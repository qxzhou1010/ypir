use std::time::Instant;

use log::debug;

use spiral_rs::{arith::*, gadget::*, ntt::*, params::*, poly::*};

use crate::serialize::*;

use super::{kernel::*, util::*};

#[cfg(feature = "explicit_avx512")]
use std::arch::x86_64::*;

/// 参考 CDKS21 2.5 中对应算法即可，以及 2.4 中的 KeySwitch
/// 这里整体上是在计算 ct' = (c0, 0) + g^{-1}(c1) * K
/// 其中 c0 c1 是 经过 Sub 替换后的，也就是把 c0 c1 当作一个普通多项式，然后进行 Sub 操作即可
fn homomorphic_automorph<'a>(
    params: &'a Params,
    t: usize,
    t_exp: usize,
    ct: &PolyMatrixNTT<'a>,
    pub_param: &PolyMatrixNTT<'a>,
) -> PolyMatrixNTT<'a> {
    // 标准的 RLWE 密文，只有2个 Rq 中的多项式
    // ct = (c0, c1)
    // 这里关于一个RLWE密文中 ct = （c0, c1) \in R_q^2， CDKS21 论文中的定义和 YPIR/Spiral，以及这里代码的定义是恰好反过来的
    // CDKS21 中 一个 RLWE sample (b, a) \in R_q^2, 其中 b = <a, s> + e + \Delta m， a是一个随机数
    // 所以在 CDKS21 中 ct = (c0, c1) = (b, a) 其中 c0 是一个消息相关的部分，c1 是公共随机数，这和 BFV里的表示形式是一样的
    // 但是在 Spiral/YPIR的定义里刚好反过来了，在YPIR原文的 Definition 2.2 中我们可以看到它的 RLWE sample 是 (a, as + e)
    // 我们也可以通过代码进一步确认
    // 写了这么多，是想写清楚后文的代码和算法对应不上来的问题
    // 算法的 KeySwitch 的计算是  ct' = (c0, 0) + g^{-1}(c1) * K
    // 由于这里代码实现对 c0, c1 的定义恰好相反
    // 所以我们可以看到代码里最后用了 ct_auto 的row = 1 的多项式 去做加法，就是这个原因
    // 在代码里实际计算的是 ct' = (c1, 0) + g^{-1}(c0) * K，其中 c0 是公共随机数，c1 是消息相关的部分
    assert_eq!(ct.rows, 2);
    assert_eq!(ct.cols, 1);

    let ct_raw = ct.raw();
    // 直接把这个密文中的2个多项式的每一个未知数X替换为对应的 X^t，注意上在 mod X^N + 1 下进行的
    // 这一步本质上就是对密文多项式的操作
    // 可以理解为是在 EvalAuto 中的 \tau_d(c0), \tau_d(c1)
    let ct_auto = automorph_alloc(&ct_raw, t);
    // println!("ct_auto, rows: {}, cols: {}", ct_auto.rows, ct_auto.cols);

    // 后面的所有内容可以理解为在做一次 KeySwitch，其中 pub_param 就是 当前 t 下对应的 KeySwitchKey = KSKeyGen(\tau_d(s), s)

    let mut ginv_ct = PolyMatrixRaw::zero(params, t_exp, 1);
    // 这里就是在计算 g_z^{-1} (c0)
    // 对应 2.4 中的 g^{-1}(c0), 注意这里的 c0 等价于论文描述里的 c1，是公共随机数的部分
    // rdim = 1, 即 row dim --> [0, 1) 所以这里的计算是 g_z^{-1} (c0)
    // c0 是 (1, 1) 通过 Digit Decomposition 后，变成了 (t_exp, 1)
    gadget_invert_rdim(&mut ginv_ct, &ct_auto, 1);
    let mut ginv_ct_ntt = PolyMatrixNTT::zero(params, t_exp, 1);

    // 注意 i 的起点是 1，也就是只处理 c1 往后的行
    // 为什么不处理第 0 行呢？
    // 尝试了 i = 0 开始，最终的计算也是正确的，没太搞懂这里的细节
    // i 从1开始，那么 ginv_ct_ntt[0][0] 的值也就是 全0
    // 我大胆判断，他代码可能写错了，从算法描述来看，就是要 g^{-1}(c0) 完整的信息乘以 K
    for i in 0..t_exp {
        let pol_src = ginv_ct.get_poly(i, 0);
        let pol_dst = ginv_ct_ntt.get_poly_mut(i, 0);
        reduce_copy(params, pol_dst, pol_src);
        ntt_forward(params, pol_dst);
    }
    // println!("ginv_ct_ntt[0]: {:?}", ginv_ct_ntt.get_poly(0, 0));

    // 对应 g^{-1}(c0) * K
    // K 是 KeySwicthKey，也就是 pub_param, 它的维度是 (2, t_exp)
    // g^{-1}(c0) 维度是 (t_exp, 1)，恰好做一次 PolyMatrix 的矩阵乘法，结果是 (2, 1)
    // 恰好是一个 new RLWE sample 的格式
    let w_times_ginv_ct = pub_param * &ginv_ct_ntt;

    // println!(
    //     "w_times_ginv_ct rows: {}, cols: {}",
    //     w_times_ginv_ct.rows, w_times_ginv_ct.cols
    // );

    // 获取 c1（对应算法的 c0），是消息相关的部分
    let mut ct_auto_1 = PolyMatrixRaw::zero(params, 1, 1);
    ct_auto_1
        .data
        .as_mut_slice()
        .copy_from_slice(ct_auto.get_poly(1, 0));
    let ct_auto_1_ntt = ct_auto_1.ntt();

    // 二者再做一次加法即可
    //pad_top 是构造算法中的 (0, c1), 注意 c1 是消息相关的部分
    &ct_auto_1_ntt.pad_top(1) + &w_times_ginv_ct
}

/// 对应 CDKS21 中的 算法2的递归实现
/// 理解起来没有难度，和算法描述完全可以一一对应起来
pub fn pack_lwes_inner<'a>(
    params: &'a Params,
    ell: usize,
    start_idx: usize,
    rlwe_cts: &[PolyMatrixNTT<'a>],
    pub_params: &[PolyMatrixNTT<'a>],
    y_constants: &(Vec<PolyMatrixNTT<'a>>, Vec<PolyMatrixNTT<'a>>),
) -> PolyMatrixNTT<'a> {
    assert_eq!(pub_params.len(), params.poly_len_log2);

    // ell == 0，直接返回
    if ell == 0 {
        return rlwe_cts[start_idx].clone();
    }
    // step = N / 2^\ell
    let step = 1 << (params.poly_len_log2 - ell);
    // 左侧的偶数节点
    let even = start_idx;
    // 右侧的奇数节点
    let odd = start_idx + step;
    // 往下递归一层, 1. ell-1; 2. start_idx 需要同步更新
    let mut ct_even = pack_lwes_inner(params, ell - 1, even, rlwe_cts, pub_params, y_constants);
    let ct_odd = pack_lwes_inner(params, ell - 1, odd, rlwe_cts, pub_params, y_constants);

    // 获取当前的 X^{N / 2^\ell} 和 -X^{N / 2^\ell}， 注意 index 要和 幂指数对应起来
    let (y, neg_y) = (&y_constants.0[ell - 1], &y_constants.1[ell - 1]);

    // X^{N / 2^\ell} * ct_{odd}
    let y_times_ct_odd = scalar_multiply_alloc(&y, &ct_odd);
    // -X^{N / 2^\ell} * ct_{odd}
    let neg_y_times_ct_odd = scalar_multiply_alloc(&neg_y, &ct_odd);

    // ct_{even} - X^{N / 2^\ell} * ct_{odd}
    let mut ct_sum_1 = ct_even.clone();
    add_into(&mut ct_sum_1, &neg_y_times_ct_odd);

    // ct_{even} + X^{N / 2^\ell} * ct_{odd}
    add_into(&mut ct_even, &y_times_ct_odd);

    // let now = Instant::now();
    // 注意 t 的值是 2^\ell + 1，这一点和 算法描述完全一样
    // 同时要注意 pub_params 的 index，要对应到 Sub(*, t) 所对应的 KeySwitchKey
    // 这个就是 算法2中的 line-7 的后半部分 EvalAuto(ct_{even} - X^{N / 2^\ell} * ct_{odd}, 2^\ell +1)
    let ct_sum_1_automorphed = homomorphic_automorph(
        params,
        (1 << ell) + 1,
        params.t_exp_left,
        &ct_sum_1,
        &pub_params[params.poly_len_log2 - 1 - (ell - 1)],
    );
    // debug!("Homomorphic automorph in {} us", now.elapsed().as_micros());

    // 算法2中完整的 line-7
    &ct_even + &ct_sum_1_automorphed
}

fn pack_lwes_inner_non_recursive<'a>(
    params: &'a Params,
    ell: usize,
    _start_idx: usize,
    rlwe_cts: &[PolyMatrixNTT<'a>],
    pub_params: &[PolyMatrixNTT<'a>],
    y_constants: &(Vec<PolyMatrixNTT<'a>>, Vec<PolyMatrixNTT<'a>>),
    prepared_vals: Option<&[PolyMatrixNTT<'a>]>,
    mut output_prepared_vals: Option<&mut Vec<PolyMatrixNTT<'a>>>,
) -> PolyMatrixNTT<'a> {
    assert!(pub_params.len() == params.poly_len_log2 || pub_params.len() == 0);
    assert_eq!(params.crt_count, 2);

    // let mut working_set = Vec::with_capacity(1 << (ell - 1));
    // let num_out = 1 << (ell - 1);
    // for i in 0..num_out {
    //     let combined = combine(
    //         params,
    //         1,
    //         &rlwe_cts[i],
    //         &rlwe_cts[num_out + i],
    //         pub_params,
    //         y_constants,
    //     );
    //     working_set.push(combined);
    // }

    let mut working_set = rlwe_cts.to_vec();

    let mut y_times_ct_odd = PolyMatrixNTT::zero(params, 2, 1);
    let mut neg_y_times_ct_odd = PolyMatrixNTT::zero(params, 2, 1);
    let mut ct_sum_1 = PolyMatrixNTT::zero(params, 2, 1);

    let mut ct_raw = PolyMatrixRaw::zero(params, 1, 1);
    let mut ct_auto = PolyMatrixRaw::zero(params, 1, 1);
    let mut ginv_ct = PolyMatrixRaw::zero(params, params.t_exp_left, 1);
    let mut ginv_ct_ntt = PolyMatrixNTT::zero(params, params.t_exp_left, 1);
    let mut ct_auto_1_ntt = PolyMatrixNTT::zero(params, 1, 1);
    let mut w_times_ginv_ct = PolyMatrixNTT::zero(params, 2, 1);
    let mut scratch = PolyMatrixNTT::zero(params, 2, 1);
    let scratch_mut_slc = scratch.as_mut_slice();

    let mut total_0 = 0;
    let mut total_1 = 0;
    let mut total_2 = 0;
    let mut total_3 = 0;
    let mut total_4 = 0;

    let mut num_ntts = 0;

    let mut ct_raw_1_auto_ntt;

    for cur_ell in 1..=ell {
        let num_in = 1 << (ell - cur_ell + 1);
        let num_out = num_in >> 1;

        let (first_half, second_half) = (&mut working_set[..num_in]).split_at_mut(num_out);

        for i in 0..num_out {
            let now = Instant::now();
            let ct_even = &mut first_half[i];
            let ct_odd = &second_half[i];

            let (y, neg_y) = (&y_constants.0[cur_ell - 1], &y_constants.1[cur_ell - 1]);

            // if i == 5 {
            //     debug!("neg_y: {:?}", neg_y.as_slice());
            // }

            scalar_multiply_avx(&mut y_times_ct_odd, &y, &ct_odd);
            scalar_multiply_avx(&mut neg_y_times_ct_odd, &neg_y, &ct_odd);

            // if i == 5 && cur_ell == 1 && output_prepared_vals.is_none() {
            //     debug!(
            //         "ct_even[0]: {:?}",
            //         params.crt_compose(ct_even.get_poly(1, 0), 0)
            //     );
            //     debug!(
            //         "ct_odd[0]: {:?}",
            //         params.crt_compose(ct_odd.get_poly(1, 0), 0)
            //     );
            // }

            ct_sum_1.as_mut_slice().copy_from_slice(ct_even.as_slice());
            add_into(&mut ct_sum_1, &neg_y_times_ct_odd);
            fast_add_into_no_reduce(ct_even, &y_times_ct_odd);
            total_3 += now.elapsed().as_micros();

            {
                let ct: &PolyMatrixNTT<'_> = &ct_sum_1;
                let t = (1 << cur_ell) + 1;
                let t_exp = params.t_exp_left;
                let (cur_ginv_ct_ntt, cur_ct_auto_1_ntt) = if cur_ell == 1
                    && prepared_vals.is_some()
                {
                    let ginv_ct_ntt = &prepared_vals.unwrap()[i];

                    // In this first round, this value is always zero
                    ct_raw_1_auto_ntt = PolyMatrixNTT::zero(params, 1, 1);
                    (ginv_ct_ntt, &ct_raw_1_auto_ntt)
                } else {
                    let now = Instant::now();
                    // let ct_raw = ct.raw();
                    // nb: scratch has 2nd row of ct in uncrtd form,
                    //     ct_raw has only first row
                    from_ntt_scratch(&mut ct_raw, scratch_mut_slc, ct);
                    if cur_ell == 1 {
                        num_ntts += 2;
                    }
                    total_0 += now.elapsed().as_micros();
                    let now = Instant::now();
                    automorph(&mut ct_auto, &ct_raw, t);
                    total_1 += now.elapsed().as_micros();

                    gadget_invert_rdim(&mut ginv_ct, &ct_auto, 1);

                    let skip_first_gadget_dim = true;
                    if skip_first_gadget_dim {
                        for i in 1..t_exp {
                            let pol_src = ginv_ct.get_poly(i, 0);
                            let pol_dst = ginv_ct_ntt.get_poly_mut(i, 0);
                            pol_dst[..params.poly_len].copy_from_slice(pol_src);
                            pol_dst[params.poly_len..].copy_from_slice(pol_src);

                            ntt_forward(params, pol_dst);
                            if cur_ell == 1 {
                                num_ntts += 1;
                            }
                        }
                    } else {
                        to_ntt(&mut ginv_ct_ntt, &ginv_ct);
                        // num_ntts += ginv_ct_ntt.rows * ginv_ct_ntt.cols;
                    }

                    let now = Instant::now();
                    automorph_poly_uncrtd(params, ct_auto_1_ntt.as_mut_slice(), scratch_mut_slc, t);
                    ntt_forward(params, ct_auto_1_ntt.as_mut_slice());
                    // num_ntts += 1;

                    total_4 += now.elapsed().as_micros();

                    (&ginv_ct_ntt, &ct_auto_1_ntt)
                };

                if output_prepared_vals.is_some() {
                    let opv_mut = output_prepared_vals.as_deref_mut();
                    opv_mut.unwrap().push(cur_ginv_ct_ntt.clone());
                    continue;
                }

                let pub_param = &pub_params[params.poly_len_log2 - 1 - (cur_ell - 1)];
                // let ginv_ct_ntt = ginv_ct.ntt();
                // let w_times_ginv_ct = pub_param * &ginv_ct_ntt;
                w_times_ginv_ct.as_mut_slice().fill(0);
                multiply_no_reduce(&mut w_times_ginv_ct, &pub_param, &cur_ginv_ct_ntt, 1);

                // &ct_auto_1_ntt.pad_top(1) + &w_times_ginv_ct
                let now = Instant::now();
                add_into_at_no_reduce(ct_even, &cur_ct_auto_1_ntt, 1, 0);
                add_into(ct_even, &w_times_ginv_ct);
                total_2 += now.elapsed().as_micros();
            };
        }

        if output_prepared_vals.is_some() {
            return PolyMatrixNTT::zero(params, 2, 1);
        }
    }

    if false {
        debug!("num_ntts: {}", num_ntts);
        debug!("total_0: {} us", total_0);
        debug!("total_1: {} us", total_1);
        debug!("total_2: {} us", total_2);
        debug!("total_3: {} us", total_3);
        debug!("total_4: {} us", total_4);
    }

    // let mut res = PolyMatrixNTT::zero(params, 2, 1);
    // // let mut res = working_set[0].clone();
    // add_into(&mut res, &working_set[0]);
    // res

    working_set[0].clone()
}

pub fn precompute_pack<'a>(
    params: &'a Params,
    ell: usize,
    rlwe_cts: &[PolyMatrixNTT<'a>],
    fake_pub_params: &[PolyMatrixNTT<'a>],
    y_constants: &(Vec<PolyMatrixNTT<'a>>, Vec<PolyMatrixNTT<'a>>),
) -> (PolyMatrixNTT<'a>, Vec<PolyMatrixNTT<'a>>, Vec<Vec<usize>>) {
    assert!(fake_pub_params.len() == params.poly_len_log2);
    assert_eq!(params.crt_count, 2);

    let mut working_set = rlwe_cts.to_vec();

    let mut y_times_ct_odd = PolyMatrixNTT::zero(params, 2, 1);
    let mut neg_y_times_ct_odd = PolyMatrixNTT::zero(params, 2, 1);
    let mut ct_sum_1 = PolyMatrixNTT::zero(params, 2, 1);

    let mut ct_raw = PolyMatrixRaw::zero(params, 1, 1);
    let mut ct_auto = PolyMatrixRaw::zero(params, 1, 1);
    let mut ginv_ct = PolyMatrixRaw::zero(params, params.t_exp_left, 1);
    let mut ginv_ct_ntt = PolyMatrixNTT::zero(params, params.t_exp_left, 1);
    let mut ct_auto_1_ntt = PolyMatrixNTT::zero(params, 1, 1);
    let mut w_times_ginv_ct = PolyMatrixNTT::zero(params, 2, 1);
    let mut scratch = PolyMatrixNTT::zero(params, 2, 1);
    let scratch_mut_slc = scratch.as_mut_slice();

    let mut total_0 = 0;
    let mut total_1 = 0;
    let mut total_2 = 0;
    let mut total_3 = 0;
    let mut total_4 = 0;

    let mut num_ntts = 0;

    let mut res = Vec::new();

    for cur_ell in 1..=ell {
        let num_in = 1 << (ell - cur_ell + 1);
        let num_out = num_in >> 1;

        let (first_half, second_half) = (&mut working_set[..num_in]).split_at_mut(num_out);

        for i in 0..num_out {
            let now = Instant::now();
            let ct_even = &mut first_half[i];
            let ct_odd = &second_half[i];

            let (y, neg_y) = (&y_constants.0[cur_ell - 1], &y_constants.1[cur_ell - 1]);

            scalar_multiply_avx(&mut y_times_ct_odd, &y, &ct_odd);
            scalar_multiply_avx(&mut neg_y_times_ct_odd, &neg_y, &ct_odd);

            ct_sum_1.as_mut_slice().copy_from_slice(ct_even.as_slice());
            add_into(&mut ct_sum_1, &neg_y_times_ct_odd);
            fast_add_into_no_reduce(ct_even, &y_times_ct_odd);
            total_3 += now.elapsed().as_micros();

            {
                let ct: &PolyMatrixNTT<'_> = &ct_sum_1;
                let t = (1 << cur_ell) + 1;
                let t_exp = params.t_exp_left;
                let (cur_ginv_ct_ntt, cur_ct_auto_1_ntt) = {
                    let now = Instant::now();
                    // let ct_raw = ct.raw();

                    // nb: scratch has 2nd row of ct in uncrtd form,
                    //     ct_raw has only first row
                    from_ntt_scratch(&mut ct_raw, scratch_mut_slc, ct);
                    if cur_ell == 1 {
                        num_ntts += 2;
                    }
                    total_0 += now.elapsed().as_micros();
                    let now = Instant::now();
                    automorph(&mut ct_auto, &ct_raw, t);
                    total_1 += now.elapsed().as_micros();

                    gadget_invert_rdim(&mut ginv_ct, &ct_auto, 1);

                    let skip_first_gadget_dim = false;
                    if skip_first_gadget_dim {
                        for i in 1..t_exp {
                            let pol_src = ginv_ct.get_poly(i, 0);
                            let pol_dst = ginv_ct_ntt.get_poly_mut(i, 0);
                            pol_dst[..params.poly_len].copy_from_slice(pol_src);
                            pol_dst[params.poly_len..].copy_from_slice(pol_src);

                            ntt_forward(params, pol_dst);
                            if cur_ell == 1 {
                                num_ntts += 1;
                            }
                        }
                    } else {
                        to_ntt(&mut ginv_ct_ntt, &ginv_ct);
                        // num_ntts += ginv_ct_ntt.rows * ginv_ct_ntt.cols;
                    }

                    let now = Instant::now();
                    automorph_poly_uncrtd(params, ct_auto_1_ntt.as_mut_slice(), scratch_mut_slc, t);
                    ntt_forward(params, ct_auto_1_ntt.as_mut_slice());
                    // num_ntts += 1;

                    total_4 += now.elapsed().as_micros();

                    (&ginv_ct_ntt, &ct_auto_1_ntt)
                };

                // println!(
                //     "ct_auto_1_ntt.raw(): {:?}",
                //     &ct_auto_1_ntt.raw().as_slice()[..30]
                // );

                res.push(condense_matrix(params, cur_ginv_ct_ntt));

                let pub_param = &fake_pub_params[params.poly_len_log2 - 1 - (cur_ell - 1)];
                // let ginv_ct_ntt = ginv_ct.ntt();
                // let w_times_ginv_ct = pub_param * &ginv_ct_ntt;
                w_times_ginv_ct.as_mut_slice().fill(0);
                multiply_no_reduce(&mut w_times_ginv_ct, &pub_param, &cur_ginv_ct_ntt, 0);

                // &ct_auto_1_ntt.pad_top(1) + &w_times_ginv_ct
                let now = Instant::now();
                add_into_at_no_reduce(ct_even, &cur_ct_auto_1_ntt, 1, 0);
                add_into(ct_even, &w_times_ginv_ct);
                total_2 += now.elapsed().as_micros();
            };
        }
    }

    if false {
        debug!("num_ntts: {}", num_ntts);
        debug!("total_0: {} us", total_0);
        debug!("total_1: {} us", total_1);
        debug!("total_2: {} us", total_2);
        debug!("total_3: {} us", total_3);
        debug!("total_4: {} us", total_4);
    }

    let tables = generate_automorph_tables_brute_force(&params);

    (working_set[0].clone(), res, tables)
}

pub fn pack_using_precomp_vals<'a>(
    params: &'a Params,
    ell: usize,
    pub_params: &[PolyMatrixNTT<'a>],
    b_values: &[u64],
    precomp_res: &PolyMatrixNTT<'a>,
    precomp_vals: &[PolyMatrixNTT<'a>],
    precomp_tables: &[Vec<usize>],
    y_constants: &(Vec<PolyMatrixNTT<'a>>, Vec<PolyMatrixNTT<'a>>),
) -> PolyMatrixNTT<'a> {
    // let now = Instant::now();
    // let mut working_set = vec![PolyMatrixNTT::zero(params, 1, 1); 1 << ell];
    let mut working_set = Vec::with_capacity(1 << (ell - 1));
    for _ in 0..(1 << (ell - 1)) {
        working_set.push(PolyMatrixNTT::zero(params, 1, 1));
    }

    let mut y_times_ct_odd = PolyMatrixNTT::zero(params, 1, 1);
    let mut neg_y_times_ct_odd = PolyMatrixNTT::zero(params, 1, 1);
    let mut ct_sum_1 = PolyMatrixNTT::zero(params, 1, 1);
    let mut w_times_ginv_ct = PolyMatrixNTT::zero(params, 1, 1);

    // println!("time_-1: {} us", now.elapsed().as_micros());

    let mut time_0 = 0;
    let mut time_1 = 0;
    let mut time_2 = 0;
    let mut time_3 = 0;
    let mut time_4 = 0;

    let mut idx_precomp = 0;
    let mut num_muls = 0;
    for cur_ell in 1..=ell {
        let mut num_in = 1 << (ell - cur_ell + 1);
        let num_out = num_in >> 1;

        if num_in == params.poly_len {
            num_in = num_out;
        }

        let (first_half, second_half) = (&mut working_set[..num_in]).split_at_mut(num_out);

        for i in 0..num_out {
            let now = Instant::now();
            let ct_even = &mut first_half[i];

            let (y, neg_y) = (&y_constants.0[cur_ell - 1], &y_constants.1[cur_ell - 1]);

            if cur_ell > 1 {
                let ct_odd = &mut second_half[i];
                scalar_multiply_avx(&mut y_times_ct_odd, &y, &ct_odd);
                scalar_multiply_avx(&mut neg_y_times_ct_odd, &neg_y, &ct_odd);
            }

            time_0 += now.elapsed().as_micros();

            let now = Instant::now();
            if cur_ell > 1 {
                ct_sum_1.as_mut_slice().copy_from_slice(ct_even.as_slice());
                fast_add_into_no_reduce(&mut ct_sum_1, &neg_y_times_ct_odd);
                fast_add_into_no_reduce(ct_even, &y_times_ct_odd);
            }
            time_1 += now.elapsed().as_micros();

            // --

            let now = Instant::now();
            let ct: &PolyMatrixNTT<'_> = &ct_sum_1;
            let t = (1 << cur_ell) + 1;

            let cur_ginv_ct_ntt = &precomp_vals[idx_precomp];
            idx_precomp += 1;

            let w = &pub_params[params.poly_len_log2 - 1 - (cur_ell - 1)];
            // let w = pub_param.submatrix(1, 0, 1, pub_param.cols);
            // let w_times_ginv_ct = &w * cur_ginv_ct_ntt;
            // multiply(&mut w_times_ginv_ct, &w, &cur_ginv_ct_ntt);
            // w_times_ginv_ct.as_mut_slice().fill(0);
            fast_multiply_no_reduce(params, &mut w_times_ginv_ct, &w, &cur_ginv_ct_ntt, 0);
            num_muls += 1;
            time_2 += now.elapsed().as_micros();

            if cur_ell > 1 {
                let now = Instant::now();
                apply_automorph_ntt(params, &precomp_tables, &ct, ct_even, t);

                // fast_add_into_no_reduce(ct_even, &ct_auto_1_ntt);
                time_3 += now.elapsed().as_micros();
                let now = Instant::now();

                // second condition prevents overflow
                if i < num_out / 2 && ((cur_ell - 1) % 5 != 0) {
                    fast_add_into_no_reduce(ct_even, &w_times_ginv_ct);
                } else {
                    // reduction right before or after addition is much faster than at multiplication time
                    fast_add_into(ct_even, &w_times_ginv_ct);
                }
                time_4 += now.elapsed().as_micros();
            } else {
                let now = Instant::now();
                if i < num_out / 2 {
                    fast_add_into_no_reduce(ct_even, &w_times_ginv_ct);
                } else {
                    fast_add_into(ct_even, &w_times_ginv_ct);
                }
                time_4 += now.elapsed().as_micros();
            }
        }
    }
    // let now = Instant::now();

    if false {
        println!("time_0: {} us", time_0);
        println!("time_1: {} us", time_1);
        println!("time_2: {} us", time_2);
        println!("time_3: {} us", time_3);
        println!("time_4: {} us", time_4);
        println!("idx_precomp: {}", idx_precomp);
        println!("num_muls: {}", num_muls);
    }

    assert_eq!(idx_precomp, precomp_vals.len());

    let mut resulting_row_1 = working_set[0].clone();
    fast_reduce(&mut resulting_row_1);

    let resulting_row_1 = resulting_row_1.as_slice();

    let mut res = precomp_res.clone();
    // {
    //     let r = res.raw();
    //     println!("res row 0: {:?}", &r.get_poly(0, 0)[..30]);
    //     println!("res row 1: {:?}", &r.get_poly(1, 0)[..30]);
    // }
    res.get_poly_mut(1, 0).copy_from_slice(resulting_row_1);

    // println!(
    //     "precomp_res     row 1: {:?}",
    //     &precomp_res.raw().get_poly(1, 0)[..30]
    // );
    // println!(
    //     "resulting_row_1 row 1: {:?}",
    //     &working_set[0].raw().get_poly(1, 0)[..30]
    // );

    // let mut res = precomp_res.clone();

    let mut out_raw = res.raw();
    for z in 0..params.poly_len {
        let val = barrett_reduction_u128(params, b_values[z] as u128 * params.poly_len as u128);
        let idx = params.poly_len + z;
        out_raw.data[idx] += val;
        if out_raw.data[idx] >= params.modulus {
            out_raw.data[idx] -= params.modulus;
        }
    }
    let out = out_raw.ntt();
    // println!("time_5: {} us", now.elapsed().as_micros());

    // for z in 0..params.poly_len {
    //     let b_value = b_values[z];
    //     let val = barrett_u64(params, res.get_poly(1, 0)[z] + b_value);
    //     res.get_poly_mut(1, 0)[z] = val;
    // }

    out
}

/// 完全对应于 CDKS21  中的 Algorithm.1
pub fn pack_single_lwe<'a>(
    params: &'a Params,
    pub_params: &[PolyMatrixNTT<'a>],
    lwe_ct: &PolyMatrixNTT<'a>,
) -> PolyMatrixNTT<'a> {
    // computing:
    // r0 = f
    // r1 = r0 + automorph(r0, ts[0])
    // r2 = r1 + automorph(r1, ts[1])
    // ...
    // r_\log d = ...

    let mut cur_r = lwe_ct.clone();
    // 在算法描述中的 index k 等于这里的 i, 注意这里 i 的起点是 0, 而算法中 k 的起点是 1
    // t 的计算在算法中是 2^{log N - k + 1} + 1， 注意 k 的起点是 1
    // 而这里 i 的起点是 0，所以代码里计算 t 的时候，按上述公式需要额外 + 1
    //  2^{log N - k + 1} =  2^{logN} / 2^{k-1} ，把 k 替换为 i + 1，那就是 2^{log N} / 2^i = N / 2^i
    // 就和代码对应起来了
    for i in 0..params.poly_len_log2 {
        // 这个 t 就是 Sub 操作的 steps，注意这里 t 的顺序/值 需要和 raw_generate_expansion_params 中生成 KeySwitchKey 的时候保持一致
        let t = (params.poly_len / (1 << i)) + 1;
        // Sub(*, t) 对应的 KeySwitchKey，t 不同，对应的 key 不同
        let pub_param = &pub_params[i];
        // 这里就是执行 Sub(ct', steps) 操作
        let tau_of_r = homomorphic_automorph(params, t, params.t_exp_left, &cur_r, pub_param);
        // 求和
        add_into(&mut cur_r, &tau_of_r);
    }
    // 返回最后的结果
    cur_r
}

// pub fn fast_scalar_multiply_avx(res: &mut PolyMatrixNTT, a: &PolyMatrixNTT, b: &PolyMatrixNTT) {
//     assert_eq!(a.rows, 1);
//     assert_eq!(a.cols, 1);
//     assert_eq!(b.rows, 1);
//     assert_eq!(b.cols, 1);
//     assert_eq!(res.rows, 1);
//     assert_eq!(res.cols, 1);

//     // this is totally custom for cur_ell == 2

//     let params = res.params;
//     // let pol2 = a.get_poly(0, 0);
//     for i in 0..b.rows {
//         for j in 0..b.cols {
//             let res_slc = res.get_poly_mut(i, j);
//             let a_slc = a.get_poly(0, 0);
//             let b_slc = b.get_poly(i, j);
//             unsafe {
//                 let a_ptr = a_slc.as_ptr();
//                 let b_ptr = b_slc.as_ptr();
//                 let res_ptr = res_slc.as_mut_ptr();

//                 for m in 0..8 {
//                     // all the values in the NTT form of the scalar polynomial are the same
//                     let a_val = *a_ptr.add(m * 512);
//                     let x = _mm256_set1_epi64x(a_val as i64);
//                     for z in (0..512).step_by(4) {
//                         let p_y = b_ptr.add(m * 512 + z);
//                         let y = _mm256_load_si256(p_y as *const _);
//                         let product = _mm256_mul_epu32(x, y);

//                         let p_z = res_ptr.add(m * 512 + z);
//                         _mm256_store_si256(p_z as *mut _, product);
//                     }
//                 }
//             }
//         }
//     }
// }

pub fn fast_barrett_raw_u64(input: u64, const_ratio_1: u64, modulus: u64) -> u64 {
    let tmp = (((input as u128) * (const_ratio_1 as u128)) >> 64) as u64;

    // Barrett subtraction
    let res = input - tmp * modulus;

    res
}

pub fn fast_add_into(res: &mut PolyMatrixNTT, a: &PolyMatrixNTT) {
    assert!(res.rows == a.rows);
    assert!(res.cols == a.cols);

    let params = res.params;
    for i in 0..res.rows {
        for j in 0..res.cols {
            let res_poly = res.get_poly_mut(i, j);
            let a_poly = a.get_poly(i, j);
            for c in 0..params.crt_count {
                for i in 0..params.poly_len {
                    let idx = c * params.poly_len + i;
                    unsafe {
                        let p_res = res_poly.as_mut_ptr().add(idx);
                        let p_a = a_poly.as_ptr().add(idx);
                        let val = *p_res + *p_a;
                        let reduced =
                            fast_barrett_raw_u64(val, params.barrett_cr_1[c], params.moduli[c]);
                        *p_res = reduced;
                    }
                }
            }
        }
    }
}

#[cfg(feature = "explicit_avx512")]
pub fn fast_multiply_no_reduce(
    params: &Params,
    res: &mut PolyMatrixNTT,
    a: &PolyMatrixNTT,
    b: &PolyMatrixNTT,
    _start_inner_dim: usize,
) {
    assert_eq!(res.rows, a.rows);
    assert_eq!(res.cols, b.cols);
    assert_eq!(res.rows, 1);
    assert_eq!(res.cols, 1);

    assert_eq!(a.cols, b.rows);
    assert_eq!(params.crt_count * params.poly_len, 2 * 2048);

    unsafe {
        let a_ptr = a.as_slice().as_ptr();
        let b_ptr = b.as_slice().as_ptr();
        let res_ptr = res.as_mut_slice().as_mut_ptr();
        let pol_sz = params.poly_len;

        for idx in (0..pol_sz).step_by(8) {
            let mut sum_lo = _mm512_setzero_si512();
            let mut sum_hi = _mm512_setzero_si512();
            for k in 0..a.cols {
                let p_x = a_ptr.add(k * 2 * pol_sz + idx);
                let p_y = b_ptr.add(k * 2 * pol_sz + idx);

                let x = _mm512_load_si512(p_x as *const _);
                let x_lo = x;
                let x_hi = _mm512_srli_epi64(x, 32);
                let y = _mm512_load_si512(p_y as *const _);
                let y_lo = y;
                let y_hi = _mm512_srli_epi64(y, 32);

                let product_lo = _mm512_mul_epu32(x_lo, y_lo);
                let product_hi = _mm512_mul_epu32(x_hi, y_hi);

                sum_lo = _mm512_add_epi64(sum_lo, product_lo);
                sum_hi = _mm512_add_epi64(sum_hi, product_hi);
            }

            let p_z = res_ptr.add(idx);
            _mm512_store_si512(p_z as *mut _, sum_lo);
            let p_z = res_ptr.add(pol_sz + idx);
            _mm512_store_si512(p_z as *mut _, sum_hi);
        }
    }
}

#[cfg(not(feature = "explicit_avx512"))]
pub fn fast_multiply_no_reduce(
    params: &Params,
    res: &mut PolyMatrixNTT,
    a: &PolyMatrixNTT,
    b: &PolyMatrixNTT,
    _start_inner_dim: usize,
) {
    assert_eq!(res.rows, a.rows);
    assert_eq!(res.cols, b.cols);
    assert_eq!(res.rows, 1);
    assert_eq!(res.cols, 1);

    assert_eq!(a.cols, b.rows);
    assert_eq!(params.crt_count * params.poly_len, 2 * 2048);

    unsafe {
        let a_ptr = a.as_slice().as_ptr();
        let b_ptr = b.as_slice().as_ptr();
        let res_ptr = res.as_mut_slice().as_mut_ptr();
        let pol_sz = params.poly_len;

        for idx in 0..pol_sz {
            let mut sum_lo = 0;
            let mut sum_hi = 0;
            for k in 0..a.cols {
                let p_x = a_ptr.add(k * 2 * pol_sz + idx);
                let p_y = b_ptr.add(k * 2 * pol_sz + idx);

                let x = *p_x;
                let x_lo = (x as u32) as u64;
                let x_hi = x >> 32;
                let y = *p_y;
                let y_lo = (y as u32) as u64;
                let y_hi = y >> 32;

                let product_lo = x_lo * y_lo;
                let product_hi = x_hi * y_hi;

                sum_lo += product_lo;
                sum_hi += product_hi;
            }

            let p_z = res_ptr.add(idx);
            *p_z = sum_lo;
            let p_z = res_ptr.add(pol_sz + idx);
            *p_z = sum_hi;
        }
    }
}

#[cfg(feature = "explicit_avx512")]
pub fn multiply_add_poly_avx(_params: &Params, res: &mut [u64], a: &[u64], b: &[u64]) {
    unsafe {
        let a_ptr = a.as_ptr();
        let b_ptr = b.as_ptr();
        let res_ptr = res.as_mut_ptr();
        for i in (0..res.len()).step_by(8) {
            let p_x = a_ptr.add(i);
            let p_y = b_ptr.add(i);
            let p_z = res_ptr.add(i);

            let x = _mm512_load_si512(p_x as *const _);
            let y = _mm512_load_si512(p_y as *const _);
            let z = _mm512_load_si512(p_z as *const _);

            let product = _mm512_mul_epu32(x, y);
            let out = _mm512_add_epi64(z, product);

            _mm512_store_si512(p_z as *mut _, out);
        }
    }
}

#[cfg(not(feature = "explicit_avx512"))]
pub fn multiply_add_poly_avx(_params: &Params, res: &mut [u64], a: &[u64], b: &[u64]) {
    unsafe {
        let a_ptr = a.as_ptr();
        let b_ptr = b.as_ptr();
        let res_ptr = res.as_mut_ptr();

        for i in 0..res.len() {
            let p_x = a_ptr.add(i);
            let p_y = b_ptr.add(i);
            let p_z = res_ptr.add(i);

            let x = ((*p_x) as u32) as u64;
            let y = ((*p_y) as u32) as u64;

            let product = x * y;

            *p_z += product;
        }
    }
}

#[cfg(feature = "explicit_avx512")]
pub fn multiply_poly_avx(_params: &Params, res: &mut [u64], a: &[u64], b: &[u64]) {
    unsafe {
        let a_ptr = a.as_ptr();
        let b_ptr = b.as_ptr();
        let res_ptr = res.as_mut_ptr();

        for i in (0..res.len()).step_by(8) {
            let p_x = a_ptr.add(i);
            let p_y = b_ptr.add(i);
            let p_z = res_ptr.add(i);

            let x = _mm512_load_si512(p_x as *const _);
            let y = _mm512_load_si512(p_y as *const _);

            let product = _mm512_mul_epu32(x, y);

            _mm512_store_si512(p_z as *mut _, product);
        }
    }
}

#[cfg(not(feature = "explicit_avx512"))]
pub fn multiply_poly_avx(_params: &Params, res: &mut [u64], a: &[u64], b: &[u64]) {
    unsafe {
        let a_ptr = a.as_ptr();
        let b_ptr = b.as_ptr();
        let res_ptr = res.as_mut_ptr();

        for i in 0..res.len() {
            let p_x = a_ptr.add(i);
            let p_y = b_ptr.add(i);
            let p_z = res_ptr.add(i);

            let x = ((*p_x) as u32) as u64;
            let y = ((*p_y) as u32) as u64;

            let product = x * y;

            *p_z = product;
        }
    }
}

pub fn fast_add_into_no_reduce(res: &mut PolyMatrixNTT, a: &PolyMatrixNTT) {
    assert!(res.rows == a.rows);
    assert!(res.cols == a.cols);

    let a_slc = a.as_slice();
    let res_slc = res.as_mut_slice();
    for (res_chunk, a_chunk) in res_slc.chunks_exact_mut(8).zip(a_slc.chunks_exact(8)) {
        for i in 0..8 {
            res_chunk[i] += a_chunk[i];
        }
    }
}

pub fn fast_reduce(res: &mut PolyMatrixNTT) {
    let params = res.params;
    let res_slc = res.as_mut_slice();
    for m in 0..params.crt_count {
        for i in 0..params.poly_len {
            let idx = m * params.poly_len + i;
            // res_slc[idx] = barrett_coeff_u64(params, res_slc[idx], m);
            unsafe {
                let p = res_slc.as_mut_ptr().add(idx);
                *p = barrett_coeff_u64(params, *p, m);
            }
        }
    }
}

pub fn combine<'a>(
    params: &'a Params,
    cur_ell: usize,
    ct_even: &mut PolyMatrixNTT<'a>,
    ct_odd: &PolyMatrixNTT<'a>,
    pub_params: &[PolyMatrixNTT<'a>],
    y_constants: &(Vec<PolyMatrixNTT<'a>>, Vec<PolyMatrixNTT<'a>>),
) {
    let (y, neg_y) = (&y_constants.0[cur_ell - 1], &y_constants.1[cur_ell - 1]);

    let y_times_ct_odd = scalar_multiply_alloc(&y, &ct_odd);
    let neg_y_times_ct_odd = scalar_multiply_alloc(&neg_y, &ct_odd);

    let mut ct_sum_1 = ct_even.clone();
    add_into(&mut ct_sum_1, &neg_y_times_ct_odd);
    add_into(ct_even, &y_times_ct_odd);

    let ct_sum_1_automorphed = homomorphic_automorph(
        params,
        (1 << cur_ell) + 1,
        params.t_exp_left,
        &ct_sum_1,
        &pub_params[params.poly_len_log2 - 1 - (cur_ell - 1)],
    );

    add_into(ct_even, &ct_sum_1_automorphed);
}

pub fn prep_pack_lwes<'a>(
    params: &'a Params,
    lwe_cts: &[u64],
    cols_to_do: usize,
) -> Vec<PolyMatrixNTT<'a>> {
    let lwe_cts_size = params.poly_len * (params.poly_len + 1);
    assert_eq!(lwe_cts.len(), lwe_cts_size);

    assert!(cols_to_do == params.poly_len);

    let mut rlwe_cts = Vec::new();
    for i in 0..cols_to_do {
        let mut rlwe_ct = PolyMatrixRaw::zero(params, 2, 1);

        // 'a' vector
        // put this in negacyclic order
        let mut poly = Vec::new();
        for j in 0..params.poly_len {
            poly.push(lwe_cts[j * params.poly_len + i])
        }
        let nega = negacyclic_perm(&poly, 0, params.modulus);

        for j in 0..params.poly_len {
            rlwe_ct.get_poly_mut(0, 0)[j] = nega[j];
        }
        // 'b' scalar (skip)

        rlwe_cts.push(rlwe_ct.ntt());
    }

    rlwe_cts
}

pub fn prep_pack_many_lwes<'a>(
    params: &'a Params,
    lwe_cts: &[u64],
    num_rlwe_outputs: usize,
) -> Vec<Vec<PolyMatrixNTT<'a>>> {
    let lwe_cts_size = (params.poly_len + 1) * (num_rlwe_outputs * params.poly_len);
    assert_eq!(lwe_cts.len(), lwe_cts_size);

    let mut vecs = Vec::new();
    for i in 0..num_rlwe_outputs {
        let mut v = Vec::new();
        for j in 0..params.poly_len + 1 {
            v.extend(
                &lwe_cts[j * (num_rlwe_outputs * params.poly_len) + i * params.poly_len..]
                    [..params.poly_len],
            );
        }
        vecs.push(v);
    }

    let mut res = Vec::new();
    for i in 0..num_rlwe_outputs {
        res.push(prep_pack_lwes(params, &vecs[i], params.poly_len));
    }

    res
}

pub fn prepare_packed_vals_pack_lwes<'a>(
    params: &'a Params,
    preped_rlwe_cts: &[PolyMatrixNTT<'a>],
    _cols_to_do: usize,
    y_constants: &(Vec<PolyMatrixNTT<'a>>, Vec<PolyMatrixNTT<'a>>),
) -> Vec<PolyMatrixNTT<'a>> {
    let now = Instant::now();
    let mut output_preped_packed_vals = Vec::new();
    pack_lwes_inner_non_recursive(
        params,
        params.poly_len_log2,
        0,
        &preped_rlwe_cts,
        &[],
        y_constants,
        None,
        Some(&mut output_preped_packed_vals),
    );
    debug!("prepack: {} us", now.elapsed().as_micros());
    output_preped_packed_vals
}

/// Returns the `prep_packed_vals` value.
pub fn prep_pack_many_lwes_packed_vals<'a>(
    params: &'a Params,
    prep_rlwe_cts: &[Vec<PolyMatrixNTT<'a>>],
    num_rlwe_outputs: usize,
    y_constants: &(Vec<PolyMatrixNTT<'a>>, Vec<PolyMatrixNTT<'a>>),
) -> Vec<Vec<PolyMatrixNTT<'a>>> {
    assert_eq!(prep_rlwe_cts.len(), num_rlwe_outputs);
    assert_eq!(prep_rlwe_cts[0].len(), params.poly_len);

    let mut res = Vec::new();
    for i in 0..num_rlwe_outputs {
        res.push(prepare_packed_vals_pack_lwes(
            params,
            &prep_rlwe_cts[i],
            params.poly_len,
            y_constants,
        ));
    }

    res
}

pub fn pack_lwes<'a>(
    params: &'a Params,
    b_values: &[u64],
    preped_rlwe_cts: &[PolyMatrixNTT<'a>],
    preped_packed_vals: &[PolyMatrixNTT<'a>],
    cols_to_do: usize,
    pub_params: &[PolyMatrixNTT<'a>],
    y_constants: &(Vec<PolyMatrixNTT<'a>>, Vec<PolyMatrixNTT<'a>>),
) -> PolyMatrixNTT<'a> {
    assert_eq!(preped_rlwe_cts.len(), cols_to_do);
    assert_eq!(cols_to_do, params.poly_len);
    assert_eq!(b_values.len(), params.poly_len);

    let now = Instant::now();
    let preped_packed_val_opt = if preped_packed_vals.len() == 0 {
        None
    } else {
        Some(preped_packed_vals)
    };
    // 可以看到这里用了非递归算法来实现
    // let out = pack_lwes_inner_non_recursive(
    //     params,
    //     params.poly_len_log2,
    //     0,
    //     &preped_rlwe_cts,
    //     pub_params,
    //     y_constants,
    //     preped_packed_val_opt,
    //     None,
    // );

    // 这是递归版本的实现，更容易理解
    // 代码默认用了 非递归算法来实现，应该是更快
    let out = pack_lwes_inner(
        params,
        params.poly_len_log2,
        0,
        &preped_rlwe_cts,
        pub_params,
        y_constants,
    );

    let mut out_raw = out.raw();
    // 为什么单独处理 b_values ？算法的描述可没有单独处理这个 b_values
    // 这样做有什么好处呢？
    for z in 0..params.poly_len {
        // 等价于在 mod q 下计算  (N * b) mod q, b 是一个 value，注意可以认为这个 b 是 LWE 密文中的 b, 也就是这个 b 已经是在 mod q 的空间内了
        // 所以
        // 为什么要乘以 N 呢？是因为在外层处理的时候, 每一个 RLWE密文乘了一个 N^{-1} mod q，这里是为了抵消这个，因为这个 b 没有参与迭代/递归算法
        // 我们要手动的清零
        let val = barrett_reduction_u128(params, b_values[z] as u128 * params.poly_len as u128);
        // 把这个值 加到对应的 RLWE密文中的消息相关的多项式的对应系数位置上
        // 其实，这里可以看成同一个pk下的密文 + 一个 RLWE plaintext，注意加法是在 mod q 下的，这里的计算不会超过 q 的范围了，所以只需要 barrett_u64
        out_raw.get_poly_mut(1, 0)[z] = barrett_u64(params, out_raw.get_poly(1, 0)[z] + val);
    }
    let res = out_raw.ntt();
    println!("pack_lwes_inner_non_recursive took {:?}", now.elapsed());

    res
}

pub fn pack_many_lwes<'a>(
    params: &'a Params,
    prep_rlwe_cts: &[Vec<PolyMatrixNTT<'a>>],
    precomp: &Precomp<'a>,
    b_values: &[u64],
    num_rlwe_outputs: usize,
    pack_pub_params_row_1s: &[PolyMatrixNTT<'a>],
    y_constants: &(Vec<PolyMatrixNTT<'a>>, Vec<PolyMatrixNTT<'a>>),
) -> Vec<PolyMatrixNTT<'a>> {
    assert_eq!(prep_rlwe_cts.len(), num_rlwe_outputs);
    assert_eq!(prep_rlwe_cts[0].len(), params.poly_len);
    assert_eq!(b_values.len(), num_rlwe_outputs * params.poly_len);

    let mut res = Vec::new();
    for i in 0..num_rlwe_outputs {
        let (precomp_res, precomp_vals, precomp_tables) = &precomp[i];

        let packed = pack_using_precomp_vals(
            &params,
            params.poly_len_log2,
            &pack_pub_params_row_1s,
            &b_values[i * params.poly_len..(i + 1) * params.poly_len],
            &precomp_res,
            &precomp_vals,
            &precomp_tables,
            &y_constants,
        );

        res.push(packed);
    }

    res
}

fn rotation_poly<'a>(params: &'a Params, amount: usize) -> PolyMatrixNTT<'a> {
    let mut res = PolyMatrixRaw::zero(params, 1, 1);
    res.data[amount] = 1;
    res.ntt()
}
pub fn pack_using_single_with_offset<'a>(
    params: &'a Params,
    pub_params: &[PolyMatrixNTT<'a>],
    cts: &[PolyMatrixNTT<'a>],
    offset: usize,
) -> PolyMatrixNTT<'a> {
    let mut res = PolyMatrixNTT::zero(params, 2, 1);
    for i in 0..cts.len() {
        let packed_single = pack_single_lwe(params, pub_params, &cts[i]);
        let rotation = rotation_poly(params, offset + i);
        let rotated = scalar_multiply_alloc(&rotation, &packed_single);
        add_into(&mut res, &rotated);
    }
    res
}

fn swap_midpoint<T>(a: &mut [T]) {
    let len = a.len();
    let (a, b) = a.split_at_mut(len / 2);
    a.swap_with_slice(b);
}

pub fn produce_table(poly_len: usize, chunk_size: usize) -> Vec<usize> {
    let mut cur = (0..poly_len).collect::<Vec<_>>();

    let outer_chunk_size = poly_len / (chunk_size / 2);
    println!("outer_chunk_size {}", outer_chunk_size);

    let mut do_it = true;
    for outer_chunk in cur.chunks_mut(outer_chunk_size) {
        if !do_it {
            do_it = true;
            continue;
        }
        do_it = false;

        for chunk in outer_chunk.chunks_mut(chunk_size) {
            let mut offs = 0;
            let mut to_add_to_offs = (chunk_size / 2).min(chunk.len() / 2); // weird hack
            while to_add_to_offs > 0 {
                swap_midpoint(&mut chunk[offs..]);
                offs += to_add_to_offs;
                to_add_to_offs /= 2;
            }
        }
    }

    cur
}

pub fn automorph_ntt_tables(poly_len: usize, log2_poly_len: usize) -> Vec<Vec<usize>> {
    let mut tables = Vec::new();
    for i in 0..log2_poly_len {
        let chunk_size = 1 << i;
        println!("table {}", i);
        let table = produce_table(poly_len, 2 * chunk_size);
        println!("table {:?}", &table.as_slice()[..32]);
        tables.push(table);
    }

    tables
}

pub fn generate_automorph_tables_brute_force(params: &Params) -> Vec<Vec<usize>> {
    let mut tables = Vec::new();
    for i in (1..=params.poly_len_log2).rev() {
        let mut table_candidate = vec![0usize; params.poly_len];

        // for 2048 balls and 2^28 bins, we will have a collision ~1% of the time
        // so, we redo if necessary
        loop {
            let t = (1 << i) + 1;

            let poly = PolyMatrixRaw::random(&params, 1, 1);
            let poly_ntt = poly.ntt();

            let poly_auto = automorph_alloc(&poly, t);
            let poly_auto_ntt = poly_auto.ntt();

            let pol_orig = (&poly_ntt.get_poly(0, 0)[..params.poly_len]).to_vec();
            let pol_auto = (&poly_auto_ntt.get_poly(0, 0)[..params.poly_len]).to_vec();

            let mut must_redo = false;

            for i in 0..params.poly_len {
                let mut total = 0;
                let mut found = None;
                for j in 0..params.poly_len {
                    if pol_orig[i] == pol_auto[j] {
                        total += 1;
                        found = Some(j);
                    }
                }
                table_candidate[found.unwrap()] = i;
                if total != 1 {
                    must_redo = true;
                    break;
                }
            }

            if !must_redo {
                break;
            }
        }
        tables.push(table_candidate);
    }
    tables
}

pub fn apply_automorph_ntt_raw<'a>(
    params: &Params,
    poly: &[u64],
    out: &mut [u64],
    t: usize,
    tables: &[Vec<usize>],
) {
    let poly_len = params.poly_len;
    // table_idx = log2(poly_len / (t - 1))
    let table_idx = (poly_len / (t - 1)).trailing_zeros() as usize;
    let table = &tables[table_idx];

    for i in 0..poly_len {
        out[i] += poly[table[i]];
    }
}

pub fn apply_automorph_ntt<'a>(
    params: &'a Params,
    tables: &[Vec<usize>],
    mat: &PolyMatrixNTT<'a>,
    res: &mut PolyMatrixNTT<'a>,
    t: usize,
) {
    // run apply_automorph_ntt on each poly in the matrix
    // let mut res = PolyMatrixNTT::zero(params, mat.rows, mat.cols);
    for i in 0..mat.rows {
        for j in 0..mat.cols {
            let poly = mat.get_poly(i, j);
            let res_poly = res.get_poly_mut(i, j);
            for (chunk, res_chunk) in poly
                .chunks_exact(params.poly_len)
                .zip(res_poly.chunks_exact_mut(params.poly_len))
            {
                apply_automorph_ntt_raw(params, chunk, res_chunk, t, tables);
            }
        }
    }
    // res
}

#[cfg(test)]
mod test {
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;
    use spiral_rs::{client::Client, number_theory::invert_uint_mod, util::get_test_params};

    use crate::{
        client::{get_fresh_reg_public_key, raw_generate_expansion_params},
        params::params_for_scenario,
        server::generate_y_constants,
    };

    use super::*;

    /// cargo test test_packing --release -- --nocapture
    /// 整体逻辑很简单
    /// 1. 生成 N 个 raw pt，然后加密得到 N 个 RLWE 密文；
    /// 2. 然后把 N 个 RLWE 密文转换为 1个 RLWE 密文；
    /// 3. 最后将这1个RLWE密文解密得到 RLWE 明文
    /// 4. 一个RLWE明文有N个系数，这N个系数就是前面的 N 个 raw pt
    #[test]
    fn test_packing() {
        let params = get_test_params();
        let mut client = Client::init(&params);
        // 生成 RLWE 私钥
        client.generate_secret_keys();
        // 生成 CDKS21 算法2中的 X^{N/2^\ell}, -X^{N / 2^\ell}
        // \ell 的范围是 [1, log(N)]
        let y_constants = generate_y_constants(&params);

        let pack_seed = [1u8; 32];
        let cts_seed = [2u8; 32];
        let mut ct_pub_rng = ChaCha20Rng::from_seed(cts_seed);

        // 生成 Sub(*, t) 操作所需的 KeySwitchKey, t 的顺序是从 (N/2^i) + 1, i 的顺序和范围是 i = 0, ..., log(N) - 1
        let pack_pub_params = raw_generate_expansion_params(
            &params,
            client.get_sk_reg(),
            params.poly_len_log2,
            params.t_exp_left,
            &mut ChaCha20Rng::from_entropy(),
            &mut ChaCha20Rng::from_seed(pack_seed),
        );

        // generate poly_len ciphertexts
        // 准备好 N 个明文，以及对应的 N 个 RLWE 密文
        let mut v_ct = Vec::new();
        // b 表示一个 RLWE 密文（含有2个多项式）的 消息相关的部分
        let mut b_values = Vec::new();
        for i in 0..params.poly_len {
            let mut pt = PolyMatrixRaw::zero(&params, 1, 1);
            // 明文 i 从 0 开始
            let val = i as u64 % params.pt_modulus;
            let scale_k = params.modulus / params.pt_modulus;
            let mod_inv = invert_uint_mod(params.poly_len as u64, params.modulus).unwrap();

            // 每一个明文首先要放缩到 mod q 下，然后要乘以 (N^{-1}) mod q
            let val_to_enc = multiply_uint_mod(val * scale_k, mod_inv, params.modulus);
            if i == 0 {
                println!("val_to_enc: {}", val_to_enc);
            }
            // raw pt 放在明文多项式的常数项系数上
            pt.data[0] = val_to_enc;
            let ct = client.encrypt_matrix_reg(
                &pt.ntt(),
                &mut ChaCha20Rng::from_entropy(),
                &mut ct_pub_rng,
            );
            let mut ct_raw = ct.raw();

            // get the b value，即消息相关部分的多项式，为什么要把消息相关部分多项式独立出来呢？
            // 独立出来之后，最后可以直接放在 完成 pack 多项式的每一个系数上，效果上一样的

            // b = as + e + m, m 是明文多项式，只有常数项上才有值
            // 我们都只取第一项 b[0] = (as + e)[0] + m[0], 而 m[0] 恰好就是 raw pt
            // 所以这里的 ct_raw.get_poly(1, 0)[0] = b[0] = as + raw_pt，正是一个 LWE密文的 消息相关部分
            // 注意这里的 b_values 只保存了每一个密文的 消息相关多项式的 常数项系数
            b_values.push(ct_raw.get_poly(1, 0)[0]);

            // zero out all of the second poly
            // 为什么要把 ct_raw 的第二项置为0呢？
            // 置0以后还是一个合法的 RLWE 密文吗？后续的计算还是满足同样的等价性吗？至少从结果来看上没问题的
            // 那现在的 ct_raw 就只有一个公开随机数的部分了
            ct_raw.get_poly_mut(1, 0).fill(0);
            v_ct.push(ct_raw.ntt());
        }

        let now = Instant::now();
        // 核心的方法
        let packed = pack_lwes(
            &params,
            &b_values,
            &v_ct,
            &[],
            params.poly_len,
            &pack_pub_params,
            &y_constants,
        );
        // 一次 Pack 实测数据要 861.459515ms，感觉不是很快的样子，如果用在 PIR里，可能也不会很快啊
        println!("Packing took {:?}", now.elapsed());

        // 结果密文
        let packed_raw = packed.raw();
        println!("packed_0: {:?}", &packed_raw.get_poly(0, 0)[..10]);
        // 为什么这个位置上的值是一个固定的值呢？
        // assert_eq!(packed_raw.get_poly(0, 0)[0], 47649720264253743u64);

        // decrypt + decode
        let dec = client.decrypt_matrix_reg(&packed);
        let dec_raw = dec.raw();

        // rescale
        let mut rescaled = PolyMatrixRaw::zero(&params, 1, 1);
        for i in 0..params.poly_len {
            rescaled.data[i] = rescale(dec_raw.data[i], params.modulus, params.pt_modulus);
        }

        println!("rescaled: {:?}", &rescaled.as_slice()[..50]);
        // gold 可以理解为 ground truth
        let mut gold = PolyMatrixRaw::zero(&params, 1, 1);
        for i in 0..params.poly_len {
            gold.data[i] = i as u64 % params.pt_modulus;
        }
        // 预期应相等
        assert_eq!(rescaled.as_slice(), gold.as_slice());
    }

    /// cargo test test_precompute_packing --release -- --nocapture
    #[test]
    fn test_precompute_packing() {
        let params = params_for_scenario(1 << 30, 1);
        println!("modulus: {}", params.modulus);
        let mut client = Client::init(&params);
        client.generate_secret_keys();
        let y_constants = generate_y_constants(&params);

        let pack_seed = [1u8; 32];
        let cts_seed = [2u8; 32];
        let mut ct_pub_rng = ChaCha20Rng::from_seed(cts_seed);

        let pack_pub_params = raw_generate_expansion_params(
            &params,
            client.get_sk_reg(),
            params.poly_len_log2,
            params.t_exp_left,
            &mut ChaCha20Rng::from_entropy(),
            &mut ChaCha20Rng::from_seed(pack_seed),
        );

        let mut fake_pack_pub_params = pack_pub_params.clone();
        // zero out all of the second rows
        for i in 0..pack_pub_params.len() {
            for col in 0..pack_pub_params[i].cols {
                fake_pack_pub_params[i].get_poly_mut(1, col).fill(0);
            }
        }

        let mut pack_pub_params_row_1s = pack_pub_params.clone();
        for i in 0..pack_pub_params.len() {
            pack_pub_params_row_1s[i] =
                pack_pub_params[i].submatrix(1, 0, 1, pack_pub_params[i].cols);
            pack_pub_params_row_1s[i] = condense_matrix(&params, &pack_pub_params_row_1s[i]);
        }

        // generate poly_len ciphertexts
        let mut v_ct = Vec::new();
        let mut b_values = Vec::new();
        for i in 0..params.poly_len {
            let mut pt = PolyMatrixRaw::zero(&params, 1, 1);
            let val = i as u64 % params.pt_modulus;
            let scale_k = params.modulus / params.pt_modulus;
            let mod_inv = invert_uint_mod(params.poly_len as u64, params.modulus).unwrap();
            let val_to_enc = multiply_uint_mod(val * scale_k, mod_inv, params.modulus);
            pt.data[0] = val_to_enc;
            let ct = client.encrypt_matrix_reg(
                &pt.ntt(),
                &mut ChaCha20Rng::from_entropy(),
                &mut ct_pub_rng,
            );
            let mut ct_raw = ct.raw();

            // get the b value
            b_values.push(ct_raw.get_poly(1, 0)[0]);

            // zero out all of the second poly
            ct_raw.get_poly_mut(1, 0).fill(0);
            v_ct.push(ct_raw.ntt());
        }

        let now = Instant::now();
        let (precomp_res, precomp_vals, precomp_tables) = precompute_pack(
            &params,
            params.poly_len_log2,
            &v_ct,
            &fake_pack_pub_params,
            &y_constants,
        );
        println!("Precomputing for packing took {:?}", now.elapsed());

        println!("t_exp_left: {}", params.t_exp_left);

        let now = Instant::now();
        let packed = pack_using_precomp_vals(
            &params,
            params.poly_len_log2,
            &pack_pub_params_row_1s,
            &b_values,
            &precomp_res,
            &precomp_vals,
            &precomp_tables,
            &y_constants,
        );
        println!("Packing(pack_using_precomp_vals) took {:?}", now.elapsed());

        let packed_raw = packed.raw();
        println!("packed_0: {:?}", &packed_raw.get_poly(0, 0)[..10]);
        // assert_eq!(packed_raw.get_poly(0, 0)[0], 17210016925609510u64);

        // decrypt + decode
        let dec = client.decrypt_matrix_reg(&packed);
        let dec_raw = dec.raw();

        // rescale
        let mut rescaled = PolyMatrixRaw::zero(&params, 1, 1);
        for i in 0..params.poly_len {
            rescaled.data[i] = rescale(dec_raw.data[i], params.modulus, params.pt_modulus);
        }

        println!("rescaled: {:?}", &rescaled.as_slice()[..50]);
        let mut gold = PolyMatrixRaw::zero(&params, 1, 1);
        for i in 0..params.poly_len {
            gold.data[i] = i as u64 % params.pt_modulus;
        }
        assert_eq!(rescaled.as_slice(), gold.as_slice());
    }

    /// R_t = Z[X]/X^N + 1 下的 Sub 操作
    /// 即明文多项式的 Sub 操作
    pub fn automorph_poly_pt(params: &Params, res: &mut [u64], a: &[u64], t: usize) {
        let poly_len = params.poly_len;
        // 这里的逻辑非常简单，我们举一个具体例子，假设多项式模数是 X^4 + 1
        // 现在有这样一个多项式：f(x) = a0 + a1X + a2X^2 + a3X^3
        // 现在执行一次 Sub 操作，t是 [1, 2N] 范围内的奇数
        // 假设 t = 3, f(x) = a0 + a1X^3 + a2(X^3)^2 + a3(X^3)^3
        // 完成取模操作后可以得到：f(x) = a0 + a1 X^3 - a2 X^2 + a3 X
        // 我们按 X 的幂次从低到高来写：f(x) = a0 + a3X -a2 X^2  + a1X^3
        // 可以看到，原来的系数从 [a0, a1, a2, a3] 变成了 [a0, a3, -a2, a1]
        // 这里有2个变化，一个是系数的位置，另一个是系数的符号，二者满足的规律其实就是下面的代码体现的
        // i 是在遍历每一个位置上的系数，首先Sub操作的第一步都是会把 X^i 幂次变成 i * t
        // 然后我们根据 i*t 来决定当前这个系数的新位置和符号
        // 新的位置就是 rem = (i*t) mod N，可以看到 a0 的位置永远不变，因为 i = 0
        // i = 1, a1 的位置变到 (t) mod N 这个位置，后面的以此内推
        // 再来看符号，(i * t) / N 表示包含了多少个 N，按奇数和偶数分只有2种情况，偶数个N，奇数个N
        // 在 X^N + 1，奇数个N的幂次，符号变负数，偶数个N的幂次，符号不变，这里就是后面 if/else 的逻辑了
        //
        for i in 0..poly_len {
            let num = (i * t) / poly_len;
            let rem = (i * t) % poly_len;

            if num % 2 == 0 {
                res[rem] = a[i];
            } else {
                res[rem] = params.pt_modulus - a[i];
            }
        }
    }
    /// 拷贝自 Spiral 相关的源码
    pub fn automorph_pt<'a>(res: &mut PolyMatrixRaw<'a>, a: &PolyMatrixRaw<'a>, t: usize) {
        assert!(res.rows == a.rows);
        assert!(res.cols == a.cols);

        let params = res.params;
        for i in 0..a.rows {
            for j in 0..a.cols {
                // 精确到每一个 (i, j) 就是精确到单个 R_q

                // 这里获取到的是2个多项式
                let res_poly = res.get_poly_mut(i, j);
                let pol1 = a.get_poly(i, j);
                // 对多项式做 automorph 变换
                automorph_poly_pt(params, res_poly, pol1, t);
            }
        }
    }
    pub fn automorph_alloc_pt<'a>(a: &PolyMatrixRaw<'a>, t: usize) -> PolyMatrixRaw<'a> {
        let mut res = PolyMatrixRaw::zero(a.params, a.rows, a.cols);
        automorph_pt(&mut res, a, t);
        res
    }
    /// 自己手动添加了一个额外测试
    /// 测试 Sub/homomorphic_automorph 操作本身
    /// 还参考了文章：Efficient Homomorphic Conversion Between (Ring) LWE Ciphertexts --- CDKS21 的 2.3 和 2.4
    #[test]
    fn test_sub_op() {
        let params = params_for_scenario(1 << 30, 1);
        let mut client = Client::init(&params);
        client.generate_secret_keys();

        let pack_seed = [1u8; 32];
        let cts_seed = [2u8; 32];
        let mut ct_pub_rng = ChaCha20Rng::from_seed(cts_seed);
        let mut rng = ChaCha20Rng::from_seed(pack_seed);

        // 用于 Pack 操作的 一组公开参数
        // 为什么还需要 TExpLeft 这个参数呢？主要就是为了 Gadget Decomposition
        // 我们下面手动计算一个 KeySwitchKey 出来

        // 下面的内容基本可以对应 CDKS21 中 2.4 KeySwitch 和 2.5 的内容
        // 首先，这一部分，我们是在生成 KeySwitchKey
        // KSKeyGen(s, s') , 这里的 s = Sub(s', t)， s' 是 客户端的RLWE私钥，即 sk_reg
        // t 是 Sub 操作的 steps，那么 s 就是下面代码中的 tau_sk_reg
        // 因为我们对密文做了 Sub 操作以后，对应的密钥也变成了 Sub(s', t) ，我们要把这个密钥变换为这个密文加密时候使用的密钥
        // 所以我们要生成这样的一个 KeySwitchKey，其中当前密钥是 s，是 Sub(s', t)，目标密钥是 s'，是客户端加密时的密钥
        // 下面的 KeySwitchKey 的生成过程基本上就是按 CDKS21 中 2.4 的内容进行描述

        let m_exp = params.t_exp_left;
        // g_exp 是 (1, m_exp)，m_exp 就是这个 Gadget Vector 的长度
        // 也就是生成这样一个向量 [1, z, z^2, ..., z^{d-1}] ，注意其中每一个元素是一个 Rq
        let g_exp = build_gadget(&params, 1, m_exp);
        let sk_reg = client.get_sk_reg();
        println!("using gadget base {}", g_exp.get_poly(0, 1)[1]);
        let g_exp_ntt = g_exp.ntt();

        // sub 操作的 steps 就固定为 3
        let t = 3;
        // Sub(s), 也可以理解为 KSKeyGen(s, s') 中的第一个输入 s
        // 到这里，我们就可以理解，为什么 Sub 操作的 KeySwitchKey 和 steps 是高度相关的
        // 就是因为 Sub 操作在不同的 steps 下，Sub 操作后得到的密文对应的新密钥不同
        // 这就导致前面的 KeySwitchKey 也是不同的
        let tau_sk_reg = automorph_alloc(sk_reg, t);
        // s * g, 使用 Ntt 加速乘法

        // 注意，从算法来看，这里是一个标量Rq 乘以一个向量 Rq^d, d 是 Gadget Vector 的长度
        // 从这里的代码实现来看是两个 PolyMatrix 的乘法，当然各自的 shape 也需要满足条件
        // 更具体的就是 (1, 1) * (1, m_exp) ，结果就是 (1, m_exp)
        let prod = &tau_sk_reg.ntt() * &g_exp_ntt;
        // let w_exp_i = client.encrypt_matrix_reg(&prod, rng, rng_pub);
        let sample = get_fresh_reg_public_key(&params, &sk_reg, m_exp, &mut rng, &mut ct_pub_rng);
        println!("sample shape, rows: {}, cols: {}", sample.rows, sample.cols);
        // sample 的维度是 (2, m_exp), 2 是表示一个 RLWE 密文包含2个Rq，m_exp 是因为 Gadget Decomposition 带来的膨胀
        // 这里本质上是用 s' 对 s 进行了一次加密，也就是 old secret s 在 new secret s' 下的一个RLWE密文
        // 这里的 w_exp_i 就是 K = [k0 | k1] \in R_q^{2 \times d}，完全是一一对应的
        let w_exp_i = &sample + &prod.pad_top(1);

        // 到这里为止，我们充分理解了 KeySwitchKey(s, s') 的生成过程，下面我们尝试如何在 Sub 操作中使用这个 KeySwitchKey
        // 即完成了 2.5 中的 AutoKeyGen

        // 先生成一个随机的 Rp 下的明文多项式
        let mut pt = PolyMatrixRaw::random(&params, 1, 1);
        pt.reduce_mod(params.pt_modulus);
        // 明文下进行 Sub 操作
        let pt_sub_expected = automorph_alloc_pt(&pt, t);

        // pt 被加密前，我们需要手动为每一个元素乘以 Delta = q/p
        for val in pt.data.as_mut_slice() {
            *val *= params.modulus / params.pt_modulus;
        }

        // 加密
        let ct =
            client.encrypt_matrix_reg(&pt.ntt(), &mut ChaCha20Rng::from_entropy(), &mut ct_pub_rng);
        // 密文下进行 Sub 操作
        // homomorphic_automorph
        //    let tau_of_r = homomorphic_automorph(params, t, params.t_exp_left, &cur_r, pub_param);

        let ct_sub = homomorphic_automorph(&params, t, m_exp, &ct, &w_exp_i);
        // 解密，并 Rescale，然后和 pt_sub_expected 对比
        let dec = client.decrypt_matrix_reg(&ct_sub);
        let dec_raw = dec.raw();
        let mut rescaled = PolyMatrixRaw::zero(&params, 1, 1);
        for i in 0..params.poly_len {
            rescaled.data[i] = rescale(dec_raw.data[i], params.modulus, params.pt_modulus);
        }

        // 对比 rescaled 和 pt_sub_expected 是否相等
        assert_eq!(pt_sub_expected.data.as_slice(), rescaled.data.as_slice());

        // 到这里，我们的猜想和计算完全正确
    }

    /// cargo test test_single_packing --release -- --nocapture
    /// 1. 生成参数，Regev密钥；
    /// 2. 生成一组 pack_pub_params，本质上也就是一组 KeySwitchKey，注意因为 Sub 操作的  Steps 不同，那么对应的新的私钥也不同，所以对应的KeySwitchKey 也不同
    /// 3. 然后提前处理 LWE明文/密文，核心是乘以 (N^{-1}) mod q
    /// 4. 然后进行转换
    #[test]
    fn test_single_packing() {
        let params: Params = params_for_scenario(1 << 30, 1);
        let mut client = Client::init(&params);
        client.generate_secret_keys();

        let pack_seed = [1u8; 32];
        let cts_seed = [2u8; 32];
        let mut ct_pub_rng = ChaCha20Rng::from_seed(cts_seed);

        // 用于 Pack 操作的 一组公开参数
        // 为什么还需要 TExpLeft 这个参数呢？主要就是为了 Gadget Decomposition
        // 这个 tExpleft 可以理解为 Gadget vector 的长度，通过这个长度可以计算出 base-z
        // 生成 log(N) 个 Sub(*, t) 操作所需的 KeySwitchKey，对应的 t 依此为 {N/1 + 1, N/2 + 1, N/ 4 + 1, .... N / (N/2) + 1};
        let pack_pub_params = raw_generate_expansion_params(
            &params,
            client.get_sk_reg(),
            params.poly_len_log2,
            params.t_exp_left,
            &mut ChaCha20Rng::from_entropy(),
            &mut ChaCha20Rng::from_seed(pack_seed),
        );
        println!("pack_pub_params len: {}", pack_pub_params.len());

        // generate 1 ciphertext
        // 一个 raw 明文
        // 这个例子实际跳过了 LWE密文这个环节，而是直接把一个 raw 明文packingd到了一个 RLWE 密文上
        let sentinel_val = 99;
        let mut v_ct = Vec::new();
        for _i in 0..1 {
            // 新建一个 RLWE Plaintext
            let mut pt = PolyMatrixRaw::zero(&params, 1, 1);
            //
            let val = sentinel_val % params.pt_modulus;
            // Delta
            let scale_k = params.modulus / params.pt_modulus;
            // N^{-1} mod q, q 是 RLWE 的密文模数
            let mod_inv = invert_uint_mod(params.poly_len as u64, params.modulus).unwrap();
            // (\Delta * val) * (N^{-1} mod q)
            // 这两个值都是 mod q 下的，上面的乘法也是在 mod q 下的
            let val_to_enc = multiply_uint_mod(val * scale_k, mod_inv, params.modulus);
            // 把这个值放在 pt 的常数项系数上
            pt.data[0] = val_to_enc;
            // 然后加密得到一个 RLWE 密文
            let ct = client.encrypt_matrix_reg(
                &pt.ntt(),
                &mut ChaCha20Rng::from_entropy(),
                &mut ct_pub_rng,
            );
            v_ct.push(ct);
        }
        let now = Instant::now();
        // 为什么叫 pack_single_lwe 呢？ 这里的输入明明是一个 RLWE 密文啊
        // 这里的 RLWE 密文对应的明文只有常数项上有值
        let packed = pack_single_lwe(&params, &pack_pub_params, &v_ct[0]);
        println!("Packing took {} us", now.elapsed().as_micros());

        // Ntt 转换回 Raw
        let packed_raw = packed.raw();
        println!("packed_0: {:?}", &packed_raw.get_poly(0, 0)[..10]);

        // decrypt + decode
        let dec = client.decrypt_matrix_reg(&packed);
        let dec_raw = dec.raw();

        // rescale
        // 去除 \Delta, rescaled 可以理解为最终得到的明文多项式
        let mut rescaled = PolyMatrixRaw::zero(&params, 1, 1);
        for i in 0..params.poly_len {
            rescaled.data[i] = rescale(dec_raw.data[i], params.modulus, params.pt_modulus);
        }

        println!("rescaled: {:?}", &rescaled.as_slice()[..50]);
        // 这个明文多项式的常数项系数应该等于 最开始设置的值
        // 但是这个值需要满足一个条件，它需要是 mod t 以内的，才可以被正确的恢复
        assert_eq!(rescaled.as_slice()[0], sentinel_val);
    }

    /// 暂时没完全看懂，不过感觉也不是非常重要
    #[test]
    fn test_automorph_tables() {
        // 根据 rows 和 rows_bits 生成参数对象，这里的参数对象定义和 Spiral里的一摸一样
        let params = params_for_scenario(1 << 30, 1);

        let now = Instant::now();
        // 为什么要生成这样一个表？1）有什么用？2）这个表是如何生成的？
        // TODO: 有时间深入研究一下
        let tables = generate_automorph_tables_brute_force(&params);
        println!("Generating tables took {} us", now.elapsed().as_micros());

        let mut rng = ChaCha20Rng::from_seed([7u8; 32]);

        // 注意是逆序，注意这里的 t 都是奇数
        for t in ([3, 9, 17, 33, 65, 129, 257, 513, 1025, 2049])
            .into_iter()
            .rev()
        {
            // 随机生成 Rq 下的多项式
            let poly = PolyMatrixRaw::random_rng(&params, 1, 1, &mut rng);
            let poly_ntt = poly.ntt();

            // 在明文下完成 Sub 操作，注意输入是 t
            let poly_auto = automorph_alloc(&poly, t);
            let poly_auto_ntt = poly_auto.ntt();

            let mut poly_auto_ntt_using_tables = PolyMatrixNTT::zero(&params, 1, 1);
            // 在 Ntt 下完成 Sub 操作
            // 这里很简单啦，就是在NTT下完成对一个明文多项式的 Sub 操作
            // TODO: 有时间深入研究一下
            apply_automorph_ntt(
                &params,
                &tables,
                &poly_ntt,
                &mut poly_auto_ntt_using_tables,
                t,
            );

            println!("poly_ntt: {:?}", &poly_ntt.as_slice()[..30]);
            println!(
                "poly_auto_ntt_using_tables: {:?}",
                &poly_auto_ntt_using_tables.as_slice()[..30]
            );

            // 对比两种方式下的 Sub 操作二者结果是一致的
            // 方式1：对普通多项式 Poly 进行 automorph，得到 poly_auto，然后再对 poly_auto 执行 Ntt 变换
            // 方式2：使用 apply_automorph_ntt 直接对一个 PolyNtt 做变换得到结果
            assert_eq!(
                &poly_auto_ntt.as_slice(),
                &poly_auto_ntt_using_tables.as_slice(),
                "t: {}",
                t
            );
        }
    }
}
