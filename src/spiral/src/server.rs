use std::fs::File;
use std::io::BufReader;
use std::io::Read;
use std::io::Seek;
use std::io::SeekFrom;

// use std::fs::File;
use std::io::Write;

use crate::aligned_memory::*;
use crate::arith::*;
use crate::client::PublicParameters;
use crate::client::Query;
use crate::client::Client;
use crate::client::CLIENT_TEST;
use crate::gadget::*;
use crate::params::*;
use crate::poly::*;
use crate::util::*;

use rand::Rng;
use rayon::prelude::*;

pub fn coefficient_expansion(
    v: &mut Vec<PolyMatrixNTT>,
    g: usize,
    stop_round: usize,
    params: &Params,
    v_w_left: &Vec<PolyMatrixNTT>,
    v_w_right: &Vec<PolyMatrixNTT>,
    v_neg1: &Vec<PolyMatrixNTT>,
    max_bits_to_gen_right: usize,
) {
    let poly_len = params.poly_len;

    for r in 0..g {

        // print!("-------------------------r: {}-----------------------------", r);


        let num_in = 1 << r;
        let num_out = 2 * num_in;

        let t = (poly_len / (1 << r)) + 1;

        let neg1 = &v_neg1[r];

        // 输出 neg1 
        // println!("neg1:\n {:?}", neg1.data.as_slice());


        let action_expand = |(i, v_i): (usize, &mut PolyMatrixNTT)| {
            
            // println!("action_expand, i = {}", i);
            
            
            if (stop_round > 0 && r > stop_round && (i % 2) == 1)
                || (stop_round > 0
                    && r == stop_round
                    && (i % 2) == 1
                    && (i / 2) >= max_bits_to_gen_right)
            {
                return;
            }

            let mut ct = PolyMatrixRaw::zero(params, 2, 1);
            let mut ct_auto = PolyMatrixRaw::zero(params, 2, 1);
            let mut ct_auto_1 = PolyMatrixRaw::zero(params, 1, 1);
            let mut ct_auto_1_ntt = PolyMatrixNTT::zero(params, 1, 1);
            let mut w_times_ginv_ct = PolyMatrixNTT::zero(params, 2, 1);

            let mut ginv_ct_left = PolyMatrixRaw::zero(params, params.t_exp_left, 1);
            let mut ginv_ct_left_ntt = PolyMatrixNTT::zero(params, params.t_exp_left, 1);
            let mut ginv_ct_right = PolyMatrixRaw::zero(params, params.t_exp_right, 1);
            let mut ginv_ct_right_ntt = PolyMatrixNTT::zero(params, params.t_exp_right, 1);
            // _gadget_dim 并没有被使用，为何还要定义出来？
            let (w, _gadget_dim, gi_ct, gi_ct_ntt) = match (r != 0) && (i % 2 == 0) {
                true => (
                    &v_w_left[r],
                    params.t_exp_left,
                    &mut ginv_ct_left,
                    &mut ginv_ct_left_ntt,
                ),
                false => (
                    &v_w_right[r],
                    params.t_exp_right,
                    &mut ginv_ct_right,
                    &mut ginv_ct_right_ntt,
                ),
            };

            // println!("after match");
            // println!("w:\n {:?}", w.data.as_slice());
            // println!("_gadget_dim:\n {:?}", _gadget_dim);
            // println!("gi_ct:\n {:?}", gi_ct.data.as_slice());
            // println!("gi_ct_ntt:\n {:?}", gi_ct_ntt.data.as_slice());






            // if i < num_in {
            //     let (src, dest) = v.split_at_mut(num_in);
            //     scalar_multiply(&mut dest[i], neg1, &src[i]);
            // }

            from_ntt(&mut ct, &v_i);
            
            // println!("fromNtt, ct:\n {:?}", ct.data.as_slice());
            automorph(&mut ct_auto, &ct, t);
            // println!("automorph, ct_auto:\n {:?}", ct_auto.data.as_slice());


            gadget_invert_rdim(gi_ct, &ct_auto, 1);
            // println!("gadget_invert_rdim, gi_ct:\n {:?}", gi_ct.data.as_slice());


            to_ntt_no_reduce(gi_ct_ntt, &gi_ct);
            // println!("to_ntt_no_reduce, gi_ct_ntt:\n {:?}", gi_ct_ntt.data.as_slice());
            ct_auto_1
                .data
                .as_mut_slice()
                .copy_from_slice(ct_auto.get_poly(1, 0));

            // println!("copy_from_slice, ct_auto_1:\n {:?}", ct_auto_1.data.as_slice());

            to_ntt(&mut ct_auto_1_ntt, &ct_auto_1);
            // println!("to_ntt, ct_auto_1_ntt:\n {:?}", ct_auto_1_ntt.data.as_slice());


            multiply(&mut w_times_ginv_ct, w, &gi_ct_ntt);
            // println!("multiply, w_times_ginv_ct:\n {:?}", w_times_ginv_ct.data.as_slice());

            let mut idx = 0;
            // println!("before sum, v0:\n {:?}", (*v_i).data.as_slice());
            for j in 0..2 {
                for n in 0..params.crt_count {
                    for z in 0..poly_len {
                        let sum = (*v_i).data[idx]
                            + w_times_ginv_ct.data[idx]
                            + j * ct_auto_1_ntt.data[n * poly_len + z];
                        (*v_i).data[idx] = barrett_coeff_u64(params, sum, n);
                        // (*v_i).data[idx] = sum;
                        idx += 1;
                    }
                }
            }

            // println!("for, v_i:\n {:?}", (*v_i).data.as_slice());

        };
        //[0, num_in)  [num_in, len)
        let (src, dest) = v.split_at_mut(num_in);
        src.par_iter_mut()
            .zip(dest.par_iter_mut())
            .for_each(|(s, d)| {
                scalar_multiply(d, neg1, s);
            });

        // println!("-------after scalar_multiply-------");
        // // 输出 v 
        // for i in 0..v.len() {
        //     println!("v[{}]:\n {:?}",i,  v[i].data.as_slice());
        // }
        
        // println!("outer v[0]:\n {:?}",  v[0].data.as_slice());
        
            // 注意这里的 par_iter_mut 开了并发，利用了 rayon 的 API 来实现 
            v[0..num_in]
            .par_iter_mut()
            .enumerate()
            .for_each(action_expand);
           v[num_in..num_out]
               .par_iter_mut()
               .enumerate() // 这样传递进去的 i 是多少？ i  是从 0 开始，这里的逻辑是把 v[num_in..num_out] 这个slice 视为一个新的迭代器
               .for_each(action_expand);
   


        // // 注意这里的 par_iter_mut 开了并发，利用了 rayon 的 API 来实现 
        // v[0..num_in]
        //     .par_iter_mut()
        //     .enumerate()
        //     .for_each(action_expand);
        // v[num_in..num_out]
        //     .par_iter_mut()
        //     .enumerate() // 这样传递进去的 i 是多少？ i  是从 0 开始，这里的逻辑是把 v[num_in..num_out] 这个slice 视为一个新的迭代器
        //     .for_each(action_expand);


        // println!("-------after action_expand-------");
        // // 输出 v 
        // for i in 0..v.len() {
        //     println!("v[{}]:\n {:?}",i,  v[i].data.as_slice());
        // }



    }
}

pub fn regev_to_gsw<'a>(
    v_gsw: &mut Vec<PolyMatrixNTT<'a>>,
    v_inp: &Vec<PolyMatrixNTT<'a>>,
    v: &PolyMatrixNTT<'a>,
    params: &'a Params,
    idx_factor: usize,
    idx_offset: usize,
) {
    assert!(v.rows == 2);
    assert!(v.cols == 2 * params.t_conv);

    v_gsw.par_iter_mut().enumerate().for_each(|(i, ct)| {
        let mut ginv_c_inp = PolyMatrixRaw::zero(params, 2 * params.t_conv, 1);
        let mut ginv_c_inp_ntt = PolyMatrixNTT::zero(params, 2 * params.t_conv, 1);
        let mut tmp_ct_raw = PolyMatrixRaw::zero(params, 2, 1);
        let mut tmp_ct = PolyMatrixNTT::zero(params, 2, 1);

        for j in 0..params.t_gsw {
            let idx_ct = i * params.t_gsw + j;
            let idx_inp = idx_factor * (idx_ct) + idx_offset;
            ct.copy_into(&v_inp[idx_inp], 0, 2 * j + 1);
            from_ntt(&mut tmp_ct_raw, &v_inp[idx_inp]);
            gadget_invert(&mut ginv_c_inp, &tmp_ct_raw);
            to_ntt(&mut ginv_c_inp_ntt, &ginv_c_inp);
            multiply(&mut tmp_ct, v, &ginv_c_inp_ntt);
            ct.copy_into(&tmp_ct, 0, 2 * j);
        }
    });
}

pub const PACKED_OFFSET_2: i32 = 32;

pub fn multiply_reg_by_database(
    out: &mut Vec<PolyMatrixNTT>,
    db: &[u64],
    v_firstdim: &[u64],
    params: &Params,
    dim0: usize,
    num_per: usize,
) {
    let ct_rows = 2;
    let ct_cols = 1;
    let pt_rows = 1;
    let pt_cols = 1;

    for z in 0..params.poly_len {
        let idx_a_base = z * (ct_cols * dim0 * ct_rows);
        let mut idx_b_base = z * (num_per * pt_cols * dim0 * pt_rows);

        for i in 0..num_per {
            for c in 0..pt_cols {
                let mut sums_out_n0_0 = 0u128;
                let mut sums_out_n0_1 = 0u128;
                let mut sums_out_n1_0 = 0u128;
                let mut sums_out_n1_1 = 0u128;

                for jm in 0..(dim0 * pt_rows) {
                    let b = db[idx_b_base];
                    idx_b_base += 1;

                    let v_a0 = v_firstdim[idx_a_base + jm * ct_rows];
                    let v_a1 = v_firstdim[idx_a_base + jm * ct_rows + 1];

                    let b_lo = b as u32;
                    let b_hi = (b >> 32) as u32;

                    let v_a0_lo = v_a0 as u32;
                    let v_a0_hi = (v_a0 >> 32) as u32;

                    let v_a1_lo = v_a1 as u32;
                    let v_a1_hi = (v_a1 >> 32) as u32;

                    // do n0
                    sums_out_n0_0 += ((v_a0_lo as u64) * (b_lo as u64)) as u128;
                    sums_out_n0_1 += ((v_a1_lo as u64) * (b_lo as u64)) as u128;

                    // do n1
                    sums_out_n1_0 += ((v_a0_hi as u64) * (b_hi as u64)) as u128;
                    sums_out_n1_1 += ((v_a1_hi as u64) * (b_hi as u64)) as u128;
                }

                // output n0
                let (crt_count, poly_len) = (params.crt_count, params.poly_len);
                let mut n = 0;
                let mut idx_c = c * (crt_count * poly_len) + n * (poly_len) + z;
                // 为何不使用 barrett reduce 
                out[i].data[idx_c] = (sums_out_n0_0 % (params.moduli[0] as u128)) as u64;
                idx_c += pt_cols * crt_count * poly_len;
                out[i].data[idx_c] = (sums_out_n0_1 % (params.moduli[0] as u128)) as u64;

                // output n1
                n = 1;
                idx_c = c * (crt_count * poly_len) + n * (poly_len) + z;
                out[i].data[idx_c] = (sums_out_n1_0 % (params.moduli[1] as u128)) as u64;
                idx_c += pt_cols * crt_count * poly_len;
                out[i].data[idx_c] = (sums_out_n1_1 % (params.moduli[1] as u128)) as u64;
            }
        }
    }
}

/// database is a 2^{v1 + v2} rows , 每一行是一个 R_p^{n * n}
/// 需要重新组织为 Spiral 中的 database 的表示方式
pub fn reorient_database<'a>(
    params: &'a Params,
    database: &Vec<Vec<u64>>,
) ->  AlignedMemory64 {
    // instances 是数据库数量 T 
    let instances = params.instances;
    // mpc4j 的实现下，单次只需要处理单个 instances
    assert!(instances == 1);
    let trials = params.n * params.n;
    // 2^v1
    let dim0 = 1 << params.db_dim_1;
    // 2^v2
    let num_per = 1 << params.db_dim_2;
    // 
    let num_items = dim0 * num_per;
    // 没懂，这里难道是直接把 数据库 编码到多项式上面了吗？
    let db_size_words = instances * trials * num_items * params.poly_len;
    // ?
    let mut v = AlignedMemory64::new(db_size_words);
 
    for instance in 0..instances {
        for trial in 0..trials {
            //  遍历数据每一行
            for i in 0..num_items {
                let ii = i % num_per;
                let j = i / num_per;

                let mut db_item = PolyMatrixRaw::zero(params, 1, 1);
                // 获取当前数据库第 i 个元素 R_p^{n * n} 的 第 trail 个 R_p^{1 *1} 个部分
                let start_index = trial * params.poly_len;
                let end_index = (trial + 1) * params.poly_len;
                db_item.as_mut_slice().copy_from_slice(
                    &database[i].as_slice()[start_index..end_index]
                );
                
                for z in 0..params.poly_len {
                    db_item.data[z] =
                        recenter_mod(db_item.data[z], params.pt_modulus, params.modulus);
                }

                let db_item_ntt = db_item.ntt();
                for z in 0..params.poly_len {
                    let idx_dst = calc_index(
                        &[instance, trial, z, ii, j],
                        &[instances, trials, params.poly_len, num_per, dim0],
                    );

                    v[idx_dst] = db_item_ntt.data[z]
                        | (db_item_ntt.data[params.poly_len + z] << PACKED_OFFSET_2);
                }
            }
        }
    }
    v
}





pub fn generate_random_db_and_get_item<'a>(
    params: &'a Params,
    item_idx: usize,
) -> (PolyMatrixRaw<'a>, AlignedMemory64) {
    // PRNG 
    let mut rng = get_seeded_rng();
    
    // instances 是什么？
    let instances = params.instances;
    // ?
    let trials = params.n * params.n;
    // ?
    let dim0 = 1 << params.db_dim_1;
    // ?
    let num_per = 1 << params.db_dim_2;
    // 这不就是 1 << (params.db_dim_1 + params.db_dim_2)
    let num_items = dim0 * num_per;
    // 没懂，这里难道是直接把 数据库 编码到多项式上面了吗？
    let db_size_words = instances * trials * num_items * params.poly_len;
    // ?
    let mut v = AlignedMemory64::new(db_size_words);
    // ? item 应该就是数据库本体 
    let mut item = PolyMatrixRaw::zero(params, params.instances * params.n, params.n);

    for instance in 0..instances {
        for trial in 0..trials {
            for i in 0..num_items {
                let ii = i % num_per;
                let j = i / num_per;

                let mut db_item = PolyMatrixRaw::random_rng(params, 1, 1, &mut rng);

                // 修改 db_item 的值，将其改得稍微复杂一点
                // for cur in 0..db_item.data.len() {
                //     db_item.data[cur] = (rng.gen::<u64>()) % params.modulus;
                // }

                db_item.reduce_mod(params.pt_modulus);

                if i == item_idx {
                    item.copy_into(
                        &db_item,
                        instance * params.n + trial / params.n,
                        trial % params.n,
                    );
                }
                // 
                for z in 0..params.poly_len {
                    db_item.data[z] =
                        recenter_mod(db_item.data[z], params.pt_modulus, params.modulus);
                }

                let db_item_ntt = db_item.ntt();
                for z in 0..params.poly_len {
                    let idx_dst = calc_index(
                        &[instance, trial, z, ii, j],
                        &[instances, trials, params.poly_len, num_per, dim0],
                    );

                    v[idx_dst] = db_item_ntt.data[z]
                        | (db_item_ntt.data[params.poly_len + z] << PACKED_OFFSET_2);
                }
            }
        }
    }
    (item, v)
}

pub fn load_item_from_seek<'a, T: Seek + Read>(
    params: &'a Params,
    seekable: &mut T,
    instance: usize,
    trial: usize,
    item_idx: usize,
) -> PolyMatrixRaw<'a> {
    let db_item_size = params.db_item_size;
    let instances = params.instances;
    let trials = params.n * params.n;

    let chunks = instances * trials;
    let bytes_per_chunk = f64::ceil(db_item_size as f64 / chunks as f64) as usize;
    let logp = f64::ceil(f64::log2(params.pt_modulus as f64)) as usize;
    let modp_words_per_chunk = f64::ceil((bytes_per_chunk * 8) as f64 / logp as f64) as usize;
    assert!(modp_words_per_chunk <= params.poly_len);

    let idx_item_in_file = item_idx * db_item_size;
    let idx_chunk = instance * trials + trial;
    let idx_poly_in_file = idx_item_in_file + idx_chunk * bytes_per_chunk;

    let mut out = PolyMatrixRaw::zero(params, 1, 1);

    let seek_result = seekable.seek(SeekFrom::Start(idx_poly_in_file as u64));
    if seek_result.is_err() {
        return out;
    }
    let mut data = vec![0u8; 2 * bytes_per_chunk];
    let bytes_read = seekable
        .read(&mut data.as_mut_slice()[0..bytes_per_chunk])
        .unwrap();

    let modp_words_read = f64::ceil((bytes_read * 8) as f64 / logp as f64) as usize;
    assert!(modp_words_read <= params.poly_len);

    for i in 0..modp_words_read {
        out.data[i] = read_arbitrary_bits(&data, i * logp, logp);
        assert!(out.data[i] <= params.pt_modulus);
    }

    out
}

pub fn load_db_from_seek<T: Seek + Read>(params: &Params, seekable: &mut T) -> AlignedMemory64 {
    let instances = params.instances;
    let trials = params.n * params.n;
    let dim0 = 1 << params.db_dim_1;
    let num_per = 1 << params.db_dim_2;
    let num_items = dim0 * num_per;
    let db_size_words = instances * trials * num_items * params.poly_len;
    let mut v = AlignedMemory64::new(db_size_words);

    for instance in 0..instances {
        for trial in 0..trials {
            for i in 0..num_items {
                let ii = i % num_per;
                let j = i / num_per;

                let mut db_item = load_item_from_seek(params, seekable, instance, trial, i);
                // db_item.reduce_mod(params.pt_modulus);

                for z in 0..params.poly_len {
                    db_item.data[z] =
                        recenter_mod(db_item.data[z], params.pt_modulus, params.modulus);
                }

                let db_item_ntt = db_item.ntt();
                for z in 0..params.poly_len {
                    let idx_dst = calc_index(
                        &[instance, trial, z, ii, j],
                        &[instances, trials, params.poly_len, num_per, dim0],
                    );

                    v[idx_dst] = db_item_ntt.data[z]
                        | (db_item_ntt.data[params.poly_len + z] << PACKED_OFFSET_2);
                }
            }
        }
    }
    v
}

pub fn load_file_unsafe(data: &mut [u64], file: &mut File) {
    let data_as_u8_mut = unsafe { data.align_to_mut::<u8>().1 };
    file.read_exact(data_as_u8_mut).unwrap();
}

pub fn load_file(data: &mut [u64], file: &mut File) {
    let mut reader = BufReader::with_capacity(1 << 24, file);
    let mut buf = [0u8; 8];
    for i in 0..data.len() {
        reader.read(&mut buf).unwrap();
        data[i] = u64::from_ne_bytes(buf);
    }
}

pub fn load_preprocessed_db_from_file(params: &Params, file: &mut File) -> AlignedMemory64 {
    let instances = params.instances;
    let trials = params.n * params.n;
    let dim0 = 1 << params.db_dim_1;
    let num_per = 1 << params.db_dim_2;
    let num_items = dim0 * num_per;
    let db_size_words = instances * trials * num_items * params.poly_len;
    let mut v = AlignedMemory64::new(db_size_words);
    let v_mut_slice = v.as_mut_slice();

    load_file(v_mut_slice, file);

    v
}

pub fn fold_ciphertexts(
    params: &Params,
    v_cts: &mut Vec<PolyMatrixRaw>,
    v_folding: &Vec<PolyMatrixNTT>,
    v_folding_neg: &Vec<PolyMatrixNTT>,
) {
    if v_cts.len() == 1 {
        return;
    }

    let further_dims = log2(v_cts.len() as u64) as usize;
    let ell = v_folding[0].cols / 2;
    let mut ginv_c = PolyMatrixRaw::zero(&params, 2 * ell, 1);
    let mut ginv_c_ntt = PolyMatrixNTT::zero(&params, 2 * ell, 1);
    let mut prod = PolyMatrixNTT::zero(&params, 2, 1);
    let mut sum = PolyMatrixNTT::zero(&params, 2, 1);

    let mut num_per = v_cts.len();
    for cur_dim in 0..further_dims {
        num_per = num_per / 2;
        for i in 0..num_per {
            gadget_invert(&mut ginv_c, &v_cts[i]);
            to_ntt(&mut ginv_c_ntt, &ginv_c);
            multiply(
                &mut prod,
                &v_folding_neg[further_dims - 1 - cur_dim],
                &ginv_c_ntt,
            );
            gadget_invert(&mut ginv_c, &v_cts[num_per + i]);
            to_ntt(&mut ginv_c_ntt, &ginv_c);
            multiply(
                &mut sum,
                &v_folding[further_dims - 1 - cur_dim],
                &ginv_c_ntt,
            );
            add_into(&mut sum, &prod);
            from_ntt(&mut v_cts[i], &sum);
        }
    }
}

pub fn pack<'a>(
    params: &'a Params,
    v_ct: &Vec<PolyMatrixRaw>,
    v_w: &Vec<PolyMatrixNTT>,
) -> PolyMatrixNTT<'a> {
    assert!(v_ct.len() >= params.n * params.n);
    assert!(v_w.len() == params.n);
    assert!(v_ct[0].rows == 2);
    assert!(v_ct[0].cols == 1);
    assert!(v_w[0].rows == (params.n + 1));
    assert!(v_w[0].cols == params.t_conv);

    let mut result = PolyMatrixNTT::zero(params, params.n + 1, params.n);

    let mut ginv = PolyMatrixRaw::zero(params, params.t_conv, 1);
    let mut ginv_nttd = PolyMatrixNTT::zero(params, params.t_conv, 1);
    let mut prod = PolyMatrixNTT::zero(params, params.n + 1, 1);
    let mut ct_1 = PolyMatrixRaw::zero(params, 1, 1);
    let mut ct_2 = PolyMatrixRaw::zero(params, 1, 1);
    let mut ct_2_ntt = PolyMatrixNTT::zero(params, 1, 1);

    for c in 0..params.n {
        let mut v_int = PolyMatrixNTT::zero(&params, params.n + 1, 1);
        for r in 0..params.n {
            let w = &v_w[r];
            let ct = &v_ct[r * params.n + c];
            ct_1.get_poly_mut(0, 0).copy_from_slice(ct.get_poly(0, 0));
            ct_2.get_poly_mut(0, 0).copy_from_slice(ct.get_poly(1, 0));
            to_ntt(&mut ct_2_ntt, &ct_2);
            gadget_invert(&mut ginv, &ct_1);
            to_ntt(&mut ginv_nttd, &ginv);
            multiply(&mut prod, &w, &ginv_nttd);
            add_into_at(&mut v_int, &ct_2_ntt, 1 + r, 0);
            add_into(&mut v_int, &prod);
        }
        result.copy_into(&v_int, 0, c);
    }

    result
}

pub fn encode(params: &Params, v_packed_ct: &Vec<PolyMatrixRaw>) -> Vec<u8> {
    let q1 = 4 * params.pt_modulus;
    let q1_bits = log2_ceil(q1) as usize;
    let q2 = Q2_VALUES[params.q2_bits as usize];
    let q2_bits = params.q2_bits as usize;

    let num_bits = params.instances
        * ((q2_bits * params.n * params.poly_len)
            + (q1_bits * params.n * params.n * params.poly_len));
    let round_to = 64;
    let num_bytes_rounded_up = ((num_bits + round_to - 1) / round_to) * round_to / 8;

    let mut result = vec![0u8; num_bytes_rounded_up];
    let mut bit_offs = 0;
    for instance in 0..params.instances {
        // 其实很简单，就是不断的遍历 packed_ct 中的单个 PolyMatrixRaw，并分解为 第一行 和 剩下行 
        let packed_ct = &v_packed_ct[instance];
        
        // 这里做的事情其实是 modulus Switch 
        let mut first_row = packed_ct.submatrix(0, 0, 1, packed_ct.cols);
        let mut rest_rows = packed_ct.submatrix(1, 0, packed_ct.rows - 1, packed_ct.cols);
        first_row.apply_func(|x| rescale(x, params.modulus, q2));
        rest_rows.apply_func(|x| rescale(x, params.modulus, q1));

        let data = result.as_mut_slice();
        for i in 0..params.n * params.poly_len {
            write_arbitrary_bits(data, first_row.data[i], bit_offs, q2_bits);
            bit_offs += q2_bits;
        }
        for i in 0..params.n * params.n * params.poly_len {
            write_arbitrary_bits(data, rest_rows.data[i], bit_offs, q1_bits);
            bit_offs += q1_bits;
        }
    }
    result
}

pub fn get_v_folding_neg<'a>(
    params: &'a Params,
    v_folding: &Vec<PolyMatrixNTT<'a>>,
) -> Vec<PolyMatrixNTT<'a>> {
    let gadget_ntt = build_gadget(params, 2, 2 * params.t_gsw).ntt(); // TODO: make this better

    let v_folding_neg = (0..params.db_dim_2)
        .into_par_iter()
        .map(|i| {
            let mut ct_gsw_inv = PolyMatrixRaw::zero(params, 2, 2 * params.t_gsw);
            invert(&mut ct_gsw_inv, &v_folding[i].raw());
            let mut ct_gsw_neg = PolyMatrixNTT::zero(params, 2, 2 * params.t_gsw);
            add(&mut ct_gsw_neg, &gadget_ntt, &ct_gsw_inv.ntt());
            ct_gsw_neg
        })
        .collect();

    v_folding_neg
}


fn dec_reg_debug<'a>(
    params: &'a Params,
    ct: &PolyMatrixNTT<'a>,
    client: &mut Client<'a>,
    scale_k: u64,
) -> u64 {
    let dec = client.decrypt_matrix_reg(ct).raw();
    let mut val = dec.data[0] as i64;
    
    // println!("dec.data[0]: {}", dec.data[0]);

    if val >= (params.modulus / 2) as i64 {
        val -= params.modulus as i64;
    }
    let val_rounded = f64::round(val as f64 / scale_k as f64) as i64;

    // println!("dec.data[0]: {}, val: {}, scale_k: {} val_rounded: {}", dec.data[0], val, scale_k, val_rounded);
    if val_rounded == 0 {
        0
    } else {
        1
    }
}


fn dec_reg_debug2<'a>(
    params: &'a Params,
    ct: &PolyMatrixNTT<'a>,
    client: &mut Client<'a>,
    scale_k: u64,
) -> u64 {
    let dec = client.decrypt_matrix_reg(ct).raw();
    let mut val = dec.data[0] as i64;
    
    // println!("dec.data[0]: {}", dec.data[0]);

    if val >= (params.modulus / 2) as i64 {
        val -= params.modulus as i64;
    }
    let val_rounded = f64::round(val as f64 / scale_k as f64) as i64;

    val_rounded as u64

    // // println!("dec.data[0]: {}, val: {}, scale_k: {} val_rounded: {}", dec.data[0], val, scale_k, val_rounded);
    // if val_rounded == 0 {
    //     0
    // } else {
    //     1
    // }
}

fn dec_gsw_debug<'a>(params: &'a Params, ct: &PolyMatrixNTT<'a>, client: &mut Client<'a>) -> u64 {
    // 解密 GSW 为何调用的是 regev 的接口？
    let dec = client.decrypt_matrix_reg(ct).raw();
    // 为什么要算这样一个 idx, 这个 idx 明显是一个固定值 
    // 2 * (tGSW - 1) * d + d = d( 2*tGSW - 2 + 1 ) = d(2*tGSW -1)
    let idx: usize = 2 * (params.t_gsw - 1) * params.poly_len + params.poly_len; // this offset should encode a large value
    let mut val = dec.data[idx] as i64;
    if val >= (params.modulus / 2) as i64 {
        // println!("{} - {} = {}", val as i64, params.modulus as i64,  val - params.modulus as i64);
        val -= params.modulus as i64;
    }
    // println!("params.modulus: {}", params.modulus as i64);
    // println!("dec.data[{}]: {}, val: {}", idx, dec.data[idx], val);

    // 为何要与 2^10 比较来决定结果
    if i64::abs(val) < (1i64 << 10) {
        0
    } else {
        1
    }
}

pub fn expand_query_debug<'a>(
    params: &'a Params,
    public_params: &PublicParameters<'a>,
    query: &Query<'a>,
    client: &mut Client<'a>,
    target_idx: usize,
    idx_dim0: usize,
    idx_dim1: usize
) -> (AlignedMemory64, Vec<PolyMatrixNTT<'a>>) {
    let dim0 = 1 << params.db_dim_1;
    let further_dims = params.db_dim_2;

    let mut v_reg_reoriented;
    let mut v_folding;

    let num_bits_to_gen = params.t_gsw * further_dims + dim0;
    let g = log2_ceil_usize(num_bits_to_gen);
    let right_expanded = params.t_gsw * further_dims;
    let stop_round = log2_ceil_usize(right_expanded);

    let mut v = Vec::new();
    for _ in 0..(1 << g) {
        v.push(PolyMatrixNTT::zero(params, 2, 1));
    }
    v[0].copy_into(&query.ct.as_ref().unwrap().ntt(), 0, 0);

    let v_conversion = &public_params.v_conversion.as_ref().unwrap()[0];
    let v_w_left = public_params.v_expansion_left.as_ref().unwrap();
    let v_w_right = public_params.v_expansion_right.as_ref().unwrap_or(v_w_left);
    let v_neg1 = params.get_v_neg1();

    let mut v_reg_inp = Vec::with_capacity(dim0);
    let mut v_gsw_inp = Vec::with_capacity(right_expanded);
    if further_dims > 0 {
        coefficient_expansion(
            &mut v,
            g,
            stop_round,
            params,
            &v_w_left,
            &v_w_right,
            &v_neg1,
            params.t_gsw * params.db_dim_2,
        );

        for i in 0..dim0 {
            v_reg_inp.push(v[2 * i].clone());
        }
        for i in 0..right_expanded {
            v_gsw_inp.push(v[2 * i + 1].clone());
        }

        // 从这里开始工作, 分别验证 2^v1 个 Regev 密文 和 tGSW * v2 个 Regev 密文，  v2 个 GSW 密文

        println!("decrypt vRegev");
        let scale_k: u64 = params.modulus / params.pt_modulus;
        for i in 0..v_reg_inp.len() {
            let decrypt_val = dec_reg_debug(params, &v_reg_inp[i], client, scale_k);
            println!("i = {}, target_idx_dim0 = {}, decrypt_val = {}", i, idx_dim0, decrypt_val);
        }

        let z_gsw_log: usize =get_bits_per(params, params.t_gsw);
        let z_gsw = 1 << z_gsw_log as u64;

        println!("decrypt v_gsw");
        for l in 0..params.db_dim_2 {

            let mask = 1usize << l;
            let bit: u64 = match (idx_dim1 & mask) == mask {
                true => 1,
                false => 0,
            };
            for k in 0..params.t_gsw {

                let decrypt = dec_reg_debug2(params, &v_gsw_inp[l * params.t_gsw + k], client, scale_k);
                println!("l: {}, k: {}, bit: {}, bit * zGSW^{}: {}, decrypt: {}", 
                l, k, bit, k,  bit * u64::pow(z_gsw, k as u32),
                decrypt
            )

            }




        }





    } else {
        coefficient_expansion(&mut v, g, 0, params, &v_w_left, &v_w_left, &v_neg1, 0);
        for i in 0..dim0 {
            v_reg_inp.push(v[i].clone());
        }
    }

    let v_reg_sz = dim0 * 2 * params.poly_len;
    v_reg_reoriented = AlignedMemory64::new(v_reg_sz);
    reorient_reg_ciphertexts(params, v_reg_reoriented.as_mut_slice(), &v_reg_inp);

    v_folding = Vec::new();
    for _ in 0..params.db_dim_2 {
        v_folding.push(PolyMatrixNTT::zero(params, 2, 2 * params.t_gsw));
    }

    regev_to_gsw(&mut v_folding, &v_gsw_inp, &v_conversion, params, 1, 0);

    // 对 GSW 密文 解密
    
    println!("decrypt vFolding");
    for i in 0..v_folding.len() {
        let decrypt_val = dec_gsw_debug(params, &v_folding[i], client);
        println!("i = {}, target_idx_dim1 = {}, decrypt_val = {}", i, idx_dim1, decrypt_val);
    }



    (v_reg_reoriented, v_folding)
}






pub fn expand_query<'a>(
    params: &'a Params,
    public_params: &PublicParameters<'a>,
    query: &Query<'a>,
) -> (AlignedMemory64, Vec<PolyMatrixNTT<'a>>) {
    let dim0 = 1 << params.db_dim_1;
    let further_dims = params.db_dim_2;

    let mut v_reg_reoriented;
    let mut v_folding;

    let num_bits_to_gen = params.t_gsw * further_dims + dim0;
    let g = log2_ceil_usize(num_bits_to_gen);
    let right_expanded = params.t_gsw * further_dims;
    let stop_round = log2_ceil_usize(right_expanded);

    let mut v = Vec::new();
    for _ in 0..(1 << g) {
        v.push(PolyMatrixNTT::zero(params, 2, 1));
    }
    v[0].copy_into(&query.ct.as_ref().unwrap().ntt(), 0, 0);

    let v_conversion = &public_params.v_conversion.as_ref().unwrap()[0];
    let v_w_left = public_params.v_expansion_left.as_ref().unwrap();
    let v_w_right = public_params.v_expansion_right.as_ref().unwrap_or(v_w_left);
    let v_neg1 = params.get_v_neg1();

    let mut v_reg_inp = Vec::with_capacity(dim0);
    let mut v_gsw_inp = Vec::with_capacity(right_expanded);
    if further_dims > 0 {
        coefficient_expansion(
            &mut v,
            g,
            stop_round,
            params,
            &v_w_left,
            &v_w_right,
            &v_neg1,
            params.t_gsw * params.db_dim_2,
        );

        for i in 0..dim0 {
            v_reg_inp.push(v[2 * i].clone());
        }
        for i in 0..right_expanded {
            v_gsw_inp.push(v[2 * i + 1].clone());
        }
    } else {
        coefficient_expansion(&mut v, g, 0, params, &v_w_left, &v_w_left, &v_neg1, 0);
        for i in 0..dim0 {
            v_reg_inp.push(v[i].clone());
        }
    }

    let v_reg_sz = dim0 * 2 * params.poly_len;
    v_reg_reoriented = AlignedMemory64::new(v_reg_sz);
    reorient_reg_ciphertexts(params, v_reg_reoriented.as_mut_slice(), &v_reg_inp);

    v_folding = Vec::new();
    for _ in 0..params.db_dim_2 {
        v_folding.push(PolyMatrixNTT::zero(params, 2, 2 * params.t_gsw));
    }

    regev_to_gsw(&mut v_folding, &v_gsw_inp, &v_conversion, params, 1, 0);

    (v_reg_reoriented, v_folding)
}

pub fn variance(v: Vec<i64>) -> f64 {
    let n = v.len();
    let mean = v.iter().map(|x| *x as f64).sum::<f64>() / n as f64;
    println!("mean: {}", mean.abs().log2());
    let mut sum = 0.0;
    for i in 0..n {
        // println!(":: {}", (v[i] as f64).abs().log2());
        sum += (v[i] as f64 - mean).powi(2);
    }
    sum / n as f64
}

fn dec_to_raw<'a>(
    params: &'a Params,
    poly: &PolyMatrixRaw<'a>,
    target: &PolyMatrixRaw<'a>,
) -> PolyMatrixRaw<'a> {
    let mut out = PolyMatrixRaw::zero(params, poly.rows, poly.cols);
    let scale_k = params.modulus / params.pt_modulus;
    let mut noises = Vec::new();
    for z in 0..poly.data.len() {
        let mut val = poly.data[z] as i64;
        if val > (params.modulus / 2) as i64 {
            val -= params.modulus as i64;
        }
        let mut val_rounded = f64::round(val as f64 / scale_k as f64) as i64;

        let mut target_val = target.data[z] as i64;
        if target_val >= (params.pt_modulus / 2) as i64 {
            target_val -= params.pt_modulus as i64;
        }
        let target_val_scaled = target_val * scale_k as i64;

        let mut noise = val - target_val_scaled;
        // this seems fragile ? 这是何意？
        if noise.abs() >= (params.pt_modulus * scale_k / 2) as i64 {
            noise -= (params.pt_modulus * scale_k) as i64;
        }
        noises.push(noise);

        if val_rounded < 0 {
            val_rounded += params.pt_modulus as i64;
        }

        let result_val = (val_rounded as u64) % params.modulus;

        out.data[z] = result_val;
    }

    println!(
        "Noise width (s^2, log2): {}",
        (2.0 * std::f64::consts::PI * variance(noises)).log2()
    );

    out
}

pub fn process_query(
    params: &Params,
    public_params: &PublicParameters,
    query: &Query,
    db: &[u64],
) -> Vec<u8> {
    let dim0 = 1 << params.db_dim_1;
    let num_per = 1 << params.db_dim_2;
    let db_slice_sz = dim0 * num_per * params.poly_len;

    let v_packing = public_params.v_packing.as_ref();

    let mut v_reg_reoriented;
    let v_folding;
    if params.expand_queries {
        (v_reg_reoriented, v_folding) = expand_query(params, public_params, query);


        // let mut file = File::create("vFolding_rust.txt").unwrap();
        // writeln!(file, "vRegevReoriented: {:?}", v_reg_reoriented.as_slice());
        // for i in 0..v_folding.len() {
        //     writeln!(file, "vFolding[{}]: {:?}",i,  v_folding[i].data.as_slice());
        // }

    } else {
        v_reg_reoriented = AlignedMemory64::new(query.v_buf.as_ref().unwrap().len());
        v_reg_reoriented
            .as_mut_slice()
            .copy_from_slice(query.v_buf.as_ref().unwrap());

        v_folding = query
            .v_ct
            .as_ref()
            .unwrap()
            .iter()
            .map(|x| x.ntt())
            .collect();
    }
    let v_folding_neg = get_v_folding_neg(params, &v_folding);


    let v_packed_ct: Vec<PolyMatrixRaw> = (0..params.instances)
        .into_par_iter()
        .map(|instance| {
            let mut intermediate = Vec::with_capacity(num_per);
            let mut intermediate_raw = Vec::with_capacity(num_per);
            for _ in 0..num_per {
                intermediate.push(PolyMatrixNTT::zero(params, 2, 1));
                intermediate_raw.push(PolyMatrixRaw::zero(params, 2, 1));
            }

            let mut v_ct = Vec::new();

            for trial in 0..(params.n * params.n) {
                let idx = (instance * (params.n * params.n) + trial) * db_slice_sz;
                let cur_db = &db[idx..(idx + db_slice_sz)];

                multiply_reg_by_database(
                    &mut intermediate,
                    cur_db,
                    v_reg_reoriented.as_slice(),
                    params,
                    dim0,
                    num_per,
                );
                // 保存 intermdiate 
                // if trial == 0 {
                //     let mut file = File::create("intermediate_trial_0_rust.txt").unwrap();
                //     for i in 0..intermediate.len() {
                //         writeln!(file, "intermediate[{}]: {:?}",i,  intermediate[i].data.as_slice());
                //     }
                // }

                for i in 0..intermediate.len() {
                    from_ntt(&mut intermediate_raw[i], &intermediate[i]);
                }

                fold_ciphertexts(params, &mut intermediate_raw, &v_folding, &v_folding_neg);

            //     if trial == 0 {
            //        let mut file = File::create("intermediate_fold_trial_0_rust.txt").unwrap();
            //        for i in 0..intermediate_raw.len() {
            //            writeln!(file, "intermediateRaw[{}]: {:?}",i,  intermediate_raw[i].data.as_slice());
            //        }
            //    }


                if instance == 0 && trial == 0 {
                    unsafe {
                        // 这里是什么逻辑？CLIENT_TEST 默认为 None, 这里应该不会执行这个逻辑
                        if let Some((sk_reg, target)) = &CLIENT_TEST {

                            println!("CLIENT_TEST is NOT NONE");

                            let ct = intermediate_raw[0].ntt();
                            let ct_subset = ct.submatrix(0, 0, 2, 1);
                            let dec = (&sk_reg.ntt() * &ct_subset).raw();
                            let dec_raw = dec_to_raw(params, &dec, target);
                            for i in 0..params.poly_len {

                                // if dec_raw.data[i] != target.data[i] {
                                //     println!("dec_raw != target");
                                //     break;
                                // }
                                

                                assert_eq!(
                                    dec_raw.data[i], target.data[i],
                                    "{} != {} at {}",
                                    dec_raw.data[i], target.data[i], i
                                );
                            }

                            // println!("dec_raw:\n {:?}", dec_raw.data.as_slice());
                            // println!("target:\n {:?}", target.data.as_slice());

                        }
                    }
                }

                v_ct.push(intermediate_raw[0].clone());
            }

            // let mut file = File::create("vCt_rust.txt").unwrap();        
            // for i in 0..v_ct.len() {
            //     writeln!(file, "vCt[{}]: {:?}",i,  v_ct[i].data.as_slice());
            // }

            let packed_ct = pack(params, &v_ct, &v_packing);

            packed_ct.raw()
        })
        .collect();

    // // 保存 v_packed_ct
    // let mut file = File::create("response_rust.txt").unwrap();
    // for i in 0..v_packed_ct.len() {
    //     writeln!(file, "response[{}]: {:?}",i,  v_packed_ct[i].data.as_slice());
    // }


    encode(params, &v_packed_ct)
}

#[cfg(test)]
mod test {
    use core::num;

    use super::*;
    use crate::client::*;
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaCha20Rng;



    



    fn get_params() -> Params {
        get_fast_expansion_testing_params()
    }

    fn dec_reg<'a>(
        params: &'a Params,
        ct: &PolyMatrixNTT<'a>,
        client: &mut Client<'a>,
        scale_k: u64,
    ) -> u64 {
        let dec = client.decrypt_matrix_reg(ct).raw();
        let mut val = dec.data[0] as i64;
        
        // println!("dec.data[0]: {}", dec.data[0]);

        if val >= (params.modulus / 2) as i64 {
            val -= params.modulus as i64;
        }
        let val_rounded = f64::round(val as f64 / scale_k as f64) as i64;

        // println!("dec.data[0]: {}, val: {}, scale_k: {} val_rounded: {}", dec.data[0], val, scale_k, val_rounded);
        if val_rounded == 0 {
            0
        } else {
            1
        }
    }

    fn dec_gsw<'a>(params: &'a Params, ct: &PolyMatrixNTT<'a>, client: &mut Client<'a>) -> u64 {
        // 解密 GSW 为何调用的是 regev 的接口？
        let dec = client.decrypt_matrix_reg(ct).raw();
        // 为什么要算这样一个 idx, 这个 idx 明显是一个固定值 
        // 2 * (tGSW - 1) * d + d = d( 2*tGSW - 2 + 1 ) = d(2*tGSW -1)
        let idx: usize = 2 * (params.t_gsw - 1) * params.poly_len + params.poly_len; // this offset should encode a large value
        let mut val = dec.data[idx] as i64;
        if val >= (params.modulus / 2) as i64 {
            println!("{} - {} = {}", val as i64, params.modulus as i64,  val - params.modulus as i64);
            val -= params.modulus as i64;
        }
        // println!("params.modulus: {}", params.modulus as i64);
        // println!("dec.data[{}]: {}, val: {}", idx, dec.data[idx], val);

        // 为何要与 2^10 比较来决定结果
        if i64::abs(val) < (1i64 << 10) {
            0
        } else {
            1
        }
    }


    #[test]
    fn query_expansion_is_correct() {
        
        let params = get_params();
        
        // 返回一个可初始化随机种子的 PRNG, 跟踪进去发现使用的是 non CSPRNG
        let mut seeded_rng = get_seeded_rng();
        // 生成 PIR 的目标 index, 注意后面很有意思， 数据库总行数难道是 2^{db_dim_1 + db_dim_2}, 但是好像又对不上，
        let target_idx = seeded_rng.gen::<usize>() % (1 << (params.db_dim_1 + params.db_dim_2));
        

        let dim0 = (1 as usize) << params.db_dim_1;
        let num_per = (1 as usize) << params.db_dim_2;

        let further_dims = params.db_dim_2;
        let idx_dim0 = target_idx / num_per;
        let idx_dim1 = target_idx % num_per;



        println!("target_idx: {}, idx_dim0: {}, idx_dim1: {}", target_idx, idx_dim0, idx_dim1);
        // 初始化客户端
        let mut client = Client::init(&params);
        // 公开参数是客户端生成的 
        // let public_params = client.generate_keys();
        let pp = client.generate_keys();

        // 客户端生成 query 
        let query = client.generate_query(target_idx);

        let (_, _) = expand_query_debug(&params, &pp, &query, &mut client, target_idx, idx_dim0, idx_dim1);
        
    
        



    
    }


    #[test]
    fn coefficient_expansion_is_correct() {
        let params = get_params();
        // println!("params: {:?}", params.expand_queries);


        let v_neg1 = params.get_v_neg1();
        
        // // 为了在 debug 的时候能够看到 v_neg1 de 数据，这里讲 PolyMatrixNTT 转换为 slice 
        // let mut v_neg1_slices = Vec::new();
        // for ele in v_neg1.iter() {
        //     let mut a = vec!(0; ele.data.as_slice().len());
        //     a.as_mut_slice().copy_from_slice(ele.data.as_slice());
        //     v_neg1_slices.push(a);
        // }



        let mut rng = ChaCha20Rng::from_entropy();
        let mut rng_pub = ChaCha20Rng::from_entropy();
        let mut client = Client::init(&params);
        let public_params = client.generate_keys();
        
        // // 同样的方式，输出 public_params 这里面的内容 
        // let mut punlic_params_v_packing = &public_params.v_packing;
        // let mut v_packing_slices = Vec::new();
        // for ele in punlic_params_v_packing.iter() {
        //     let mut a = vec!(0; ele.data.as_slice().len());
        //     a.as_mut_slice().copy_from_slice(ele.data.as_slice());
        //     v_packing_slices.push(a);
        // }
        
        // let mut punlic_params_v_expansion_left = public_params.v_expansion_left.as_ref().unwrap();
        // let mut v_expansion_left_slices = Vec::new();
        // for ele in punlic_params_v_expansion_left.iter() {
        //     let mut a = vec!(0; ele.data.as_slice().len());
        //     a.as_mut_slice().copy_from_slice(ele.data.as_slice());
        //     v_expansion_left_slices.push(a);
        // }

        // let mut punlic_params_v_expansion_right = public_params.v_expansion_right.as_ref().unwrap();
        // let mut v_expansion_right_slices = Vec::new();
        // for ele in punlic_params_v_expansion_right.iter() {
        //     let mut a = vec!(0; ele.data.as_slice().len());
        //     a.as_mut_slice().copy_from_slice(ele.data.as_slice());
        //     v_expansion_right_slices.push(a);
        // }

        // let mut punlic_params_v_conversion = public_params.v_conversion.as_ref().unwrap();
        // let mut v_conversion_slices = Vec::new();
        // for ele in punlic_params_v_conversion.iter() {
        //     let mut a = vec!(0; ele.data.as_slice().len());
        //     a.as_mut_slice().copy_from_slice(ele.data.as_slice());
        //     v_conversion_slices.push(a);
        // }


        let mut v = Vec::new();
        for _ in 0..(1 << (params.db_dim_1 + 1)) {
            v.push(PolyMatrixNTT::zero(&params, 2, 1));
        }

        let target = 7;
        let scale_k = params.modulus / params.pt_modulus;
        let mut sigma = PolyMatrixRaw::zero(&params, 1, 1);
        sigma.data[target] = scale_k;
        v[0] = client.encrypt_matrix_reg(&sigma.ntt(), &mut rng, &mut rng_pub);
        let test_ct = client.encrypt_matrix_reg(&sigma.ntt(), &mut rng, &mut rng_pub);


        // let sigma_slice = sigma.data.as_slice();
        // let v0_slice = v[0].data.as_slice();
        // let test_ct_slice = test_ct.data.as_slice();




        let v_w_left = public_params.v_expansion_left.unwrap();
        let v_w_right = public_params.v_expansion_right.unwrap();
        coefficient_expansion(
            &mut v,
            params.g(),
            params.stop_round(),
            &params,
            &v_w_left,
            &v_w_right,
            &v_neg1,
            params.t_gsw * params.db_dim_2,
        );

        // // 研究 v 
        //  // 同样的方式，输出 public_params 这里面的内容 
        
        //  let mut v_slices = Vec::new();
        //  for ele in v.iter() {
        //      let mut a = vec!(0; ele.data.as_slice().len());
        //      a.as_mut_slice().copy_from_slice(ele.data.as_slice());
        //      v_slices.push(a);
        //  }



        assert_eq!(dec_reg(&params, &test_ct, &mut client, scale_k), 0);

        for i in 0..v.len() {
            // println!("i: {}", i);
            if i == target {
                assert_eq!(dec_reg(&params, &v[i], &mut client, scale_k), 1);
            } else {
                assert_eq!(dec_reg(&params, &v[i], &mut client, scale_k), 0);
            }
        }
    }

    #[test]
    fn regev_to_gsw_is_correct() {
        let mut params = get_params();
        params.db_dim_2 = 1;
        let mut rng = ChaCha20Rng::from_entropy();
        let mut rng_pub = ChaCha20Rng::from_entropy();
        let mut client = Client::init(&params);
        let public_params = client.generate_keys();

        let mut enc_constant = |val| {
            let mut sigma = PolyMatrixRaw::zero(&params, 1, 1);
            sigma.data[0] = val;
            client.encrypt_matrix_reg(&sigma.ntt(), &mut rng, &mut rng_pub)
        };

        let v = &public_params.v_conversion.unwrap()[0];

        let bits_per = get_bits_per(&params, params.t_gsw);
        println!("q: {}, tGSW: {}, zGSW: {}", params.modulus, params.t_gsw, 1 << bits_per);
        let mut v_inp_1 = Vec::new();
        let mut v_inp_0 = Vec::new();
        for i in 0..params.t_gsw {
            // z_{GSW}^{k-1}
            let val = 1u64 << (bits_per * i);
            // 每个值都放在了 常数项上 , 而不是像 pack 多项式那样，放的 
            v_inp_1.push(enc_constant(val));

            // println!("rows: {}, cols: {}", &v_inp_1[0].rows, &v_inp_1[0].cols);

            v_inp_0.push(enc_constant(0));
        }

        let mut v_gsw = Vec::new();
        v_gsw.push(PolyMatrixNTT::zero(&params, 2, 2 * params.t_gsw));

        regev_to_gsw(&mut v_gsw, &v_inp_1, v, &params, 1, 0);

        assert_eq!(dec_gsw(&params, &v_gsw[0], &mut client), 1);

        regev_to_gsw(&mut v_gsw, &v_inp_0, v, &params, 1, 0);

        assert_eq!(dec_gsw(&params, &v_gsw[0], &mut client), 0);
    }

    #[test]
    fn multiply_reg_by_database_is_correct() {
        let params = get_params();
        let mut seeded_rng = get_seeded_rng();
        let mut rng = ChaCha20Rng::from_entropy();
        let mut rng_pub = ChaCha20Rng::from_entropy();

        let dim0 = 1 << params.db_dim_1;
        let num_per = 1 << params.db_dim_2;
        let scale_k = params.modulus / params.pt_modulus;

        let target_idx = seeded_rng.gen::<usize>() % (dim0 * num_per);
        // let target_idx = 1;
        let target_idx_dim0 = target_idx / num_per;
        let target_idx_num_per = target_idx % num_per;

        let mut client = Client::init(&params);
        _ = client.generate_keys();

        let (corr_item, db) = generate_random_db_and_get_item(&params, target_idx);

        // println!("corr_item:\n {:?}", corr_item.data.as_slice());
        // println!("db:\n {:?}", db.as_slice().len());


        let mut v_reg = Vec::new();
        for i in 0..dim0 {
            let val = if i == target_idx_dim0 { scale_k } else { 0 };
            let sigma = PolyMatrixRaw::single_value(&params, val).ntt();
            v_reg.push(client.encrypt_matrix_reg(&sigma, &mut rng, &mut rng_pub));
        }

        let v_reg_sz = dim0 * 2 * params.poly_len;
        let mut v_reg_reoriented = AlignedMemory64::new(v_reg_sz);
        reorient_reg_ciphertexts(&params, v_reg_reoriented.as_mut_slice(), &v_reg);

        let mut out = Vec::with_capacity(num_per);
        for _ in 0..dim0 {
            out.push(PolyMatrixNTT::zero(&params, 2, 1));
        }
        // println!("num_per: {}, dim0:{}", num_per, dim0);


        multiply_reg_by_database(
            &mut out,
            db.as_slice(),
            v_reg_reoriented.as_slice(),
            &params,
            dim0,
            num_per,
        );

        // decrypt
        let dec = client.decrypt_matrix_reg(&out[target_idx_num_per]).raw();
        let mut dec_rescaled = PolyMatrixRaw::zero(&params, 1, 1);
        for z in 0..params.poly_len {
            dec_rescaled.data[z] = rescale(dec.data[z], params.modulus, params.pt_modulus);
        }
        // println!("modulus: {}, ptModulus: {}", params.modulus, params.pt_modulus);
        // println!("dec.data:\n {:?}", dec.data.as_slice());
        println!("dec_rescaled.data:\n {:?}", dec_rescaled.data.as_slice());



        for z in 0..params.poly_len {
            // println!("{:?} {:?}", dec_rescaled.data[z], corr_item.data[z]);
            assert_eq!(dec_rescaled.data[z], corr_item.data[z]);
        }
    }

    #[test]
    fn fold_ciphertexts_is_correct() {
        let params = get_params();
        let mut seeded_rng = get_seeded_rng();
        let mut rng = ChaCha20Rng::from_entropy();
        let mut rng_pub = ChaCha20Rng::from_entropy();

        let dim0 = 1 << params.db_dim_1;
        let num_per = 1 << params.db_dim_2;
        let scale_k = params.modulus / params.pt_modulus;

        let target_idx = seeded_rng.gen::<usize>() % (dim0 * num_per);
        // let target_idx  = 1;
        let target_idx_num_per = target_idx % num_per;

        let mut client = Client::init(&params);
        _ = client.generate_keys();

        let mut v_reg = Vec::new();
        for i in 0..num_per {
            let val = if i == target_idx_num_per { scale_k } else { 0 };
            let sigma = PolyMatrixRaw::single_value(&params, val).ntt();
            v_reg.push(client.encrypt_matrix_reg(&sigma, &mut rng, &mut rng_pub));
        }

        let mut v_reg_raw = Vec::new();
        for i in 0..num_per {
            v_reg_raw.push(v_reg[i].raw());
        }

        let bits_per = get_bits_per(&params, params.t_gsw);
        let mut v_folding = Vec::new();
        for i in 0..params.db_dim_2 {
            let bit = ((target_idx_num_per as u64) & (1 << (i as u64))) >> (i as u64);
            let mut ct_gsw = PolyMatrixNTT::zero(&params, 2, 2 * params.t_gsw);

            for j in 0..params.t_gsw {
                let value = (1u64 << (bits_per * j)) * bit;
                let sigma = PolyMatrixRaw::single_value(&params, value);
                let sigma_ntt = to_ntt_alloc(&sigma);
                let ct = client.encrypt_matrix_reg(&sigma_ntt, &mut rng, &mut rng_pub);
                ct_gsw.copy_into(&ct, 0, 2 * j + 1);
                let prod = &to_ntt_alloc(client.get_sk_reg()) * &sigma_ntt;
                let ct = &client.encrypt_matrix_reg(&prod, &mut rng, &mut rng_pub);
                ct_gsw.copy_into(&ct, 0, 2 * j);
            }

            v_folding.push(ct_gsw);
        }

        let gadget_ntt = build_gadget(&params, 2, 2 * params.t_gsw).ntt();
        let mut v_folding_neg = Vec::new();
        let mut ct_gsw_inv = PolyMatrixRaw::zero(&params, 2, 2 * params.t_gsw);
        for i in 0..params.db_dim_2 {
            invert(&mut ct_gsw_inv, &v_folding[i].raw());
            let mut ct_gsw_neg = PolyMatrixNTT::zero(&params, 2, 2 * params.t_gsw);
            add(&mut ct_gsw_neg, &gadget_ntt, &ct_gsw_inv.ntt());
            v_folding_neg.push(ct_gsw_neg);
        }

        fold_ciphertexts(&params, &mut v_reg_raw, &v_folding, &v_folding_neg);

        // decrypt
        assert_eq!(
            dec_reg(&params, &v_reg_raw[0].ntt(), &mut client, scale_k),
            1
        );
    }
    // 完整的测试流程，后续就以这个为基准学习实现。
    fn full_protocol_is_correct_for_params(params: &Params) {
        // 返回一个可初始化随机种子的 PRNG, 跟踪进去发现使用的是 non CSPRNG
        let mut seeded_rng = get_seeded_rng();
        // 生成 PIR 的目标 index, 注意后面很有意思， 数据库总行数难道是 2^{db_dim_1 + db_dim_2}, 但是好像又对不上，
        let target_idx = seeded_rng.gen::<usize>() % (1 << (params.db_dim_1 + params.db_dim_2));
        let target_idx = 118;

        println!("target_idx: {}", target_idx);
        // 初始化客户端
        let mut client = Client::init(&params);
        // 公开参数是客户端生成的 
        let public_params = client.generate_keys();
        // let pp: PublicParameters = client.generate_keys();


        // let mut file = File::create("client_rust.txt").unwrap();
        // writeln!(file, "skGsw: {:?}", client.get_sk_gsw().data.as_slice());
        // writeln!(file, "skGswFull: {:?}", client.get_sk_gsw_full().data.as_slice());
        // writeln!(file, "skRegev: {:?}", client.get_sk_reg().data.as_slice());
        // writeln!(file, "skRegevFull: {:?}",  client.get_sk_reg_full().data.as_slice());
        
       


        // let mut file = File::create("public_parameters_rust.txt").unwrap();
        // writeln!(file, "seed: {:?}", pp.seed.as_ref().unwrap());
        // writeln!(file, "vPacking[0]: {:?}", pp.v_packing[0].data.as_slice());
        // writeln!(file, "vPacking[1]: {:?}", pp.v_packing[1].data.as_slice());
        // writeln!(file, "vConversion: {:?}",  pp.v_conversion.as_ref().unwrap()[0].data.as_slice());
        // for i in 0.. pp.v_expansion_left.as_ref().unwrap().len() {

        //     writeln!(file, "vExpansionLeft[{}]: {:?}",i,  pp.v_expansion_left.as_ref().unwrap()[i].data.as_slice());
        // }
        // for i in 0.. pp.v_expansion_right.as_ref().unwrap().len() {

        //     writeln!(file, "vExpansionRight[{}]: {:?}",i,  pp.v_expansion_right.as_ref().unwrap()[i].data.as_slice());
        // }

        // 有点坑啊，这里对 PublicParameters 的序列化是错的！反序列化出来，二者不相同, 不相同为什么还能保证协议正确性呢？

        let pp_serialized = public_params.serialize();
        println!("pp size: {}", pp_serialized.len());
        println!("setup bytes: {}", params.setup_bytes());
        let pp = PublicParameters::deserialize(params, &pp_serialized);

        // 客户端生成 query 
        let query = client.generate_query(target_idx);

        // let mut file = File::create("query_rust.txt").unwrap();
        // writeln!(file, "seed: {:?}", query.seed.as_ref().unwrap());
        // writeln!(file, "ct: {:?}", query.ct.as_ref().unwrap().data.as_slice());
        // // writeln!(file, "vBuf: {:?}", query.v_buf.as_ref().unwrap().as_slice());
        // assert!(query.v_ct.is_none());
        
        // 这里才开始生成 真正的数据库 
        let (corr_item, db) = generate_random_db_and_get_item(params, target_idx);

        // let mut file = File::create("db_rust.txt").unwrap();
        // writeln!(file, "corrItem: {:?}", corr_item.data.as_slice());
        // writeln!(file, "db: {:?}", db.as_slice());
       

        unsafe {

            // clone 一个参数对象 
            let params_static = Box::leak(Box::new(params.clone()));
            // ground truth, 即想要被检索到的那一条数据 
            let mut corr_item_static =
                PolyMatrixRaw::zero(params_static, corr_item.rows, corr_item.cols);
            corr_item_static
                .data
                .as_mut_slice()
                .copy_from_slice(corr_item.data.as_slice());
            // ?
            let sk_reg_full = matrix_with_identity(client.get_sk_reg());
            // println!("sk_reg_static: \n {:?}", client.get_sk_reg().data.as_slice());
            // ?
            let mut sk_reg_static =
                PolyMatrixRaw::zero(params_static, sk_reg_full.rows, sk_reg_full.cols);
            sk_reg_static
                .data
                .as_mut_slice()
                .copy_from_slice(sk_reg_full.as_slice());

        
            // let mut file = File::create("client_test.txt").unwrap();
            // writeln!(file, "skRegevFullStatic: {:?}", sk_reg_static.data.as_slice());
            // writeln!(file, "corrItemStatic: {:?}",corr_item_static.data.as_slice());
         
            CLIENT_TEST = Some((sk_reg_static, corr_item_static));
        }
        // 服务端处理查询
    
        let response = process_query(params, &pp, &query, db.as_slice());
        println!("response size: {}", response.len());
        // 客户端处理响应，得到查询结果 
        let result = client.decode_response(response.as_slice());
        // ground truth 转成 byte数组
        let p_bits = log2_ceil(params.pt_modulus) as usize;

        // println!("corrItem:\n {:?}", corr_item.data.as_slice());

        let corr_result = corr_item.to_vec(p_bits, params.modp_words_per_chunk());
        
        // 长度和数据双向验证 
        assert_eq!(result.len(), corr_result.len());
        println!("res len: {}", result.len());

        for z in 0..corr_result.len() {
            assert_eq!(result[z], corr_result[z], "at {:?}", z);
        }
    }

    #[test]
    fn multi_time_full_protocol_is_correct() {

        for i in 0..100 {
            println!("------------------------i: {}-------------------", i);
            // full_protocol_is_correct_for_params(&get_params());
            full_protocol_is_correct()
        }

    }

    #[test]
    fn full_protocol_is_correct() {
        full_protocol_is_correct_for_params(&get_params());
    }

    #[test]
    fn multi_time_larger_full_protocol_is_correct() {

        for i in 0..10 {
            println!("------------------------i: {}-------------------", i);
            // full_protocol_is_correct_for_params(&get_params());
            larger_full_protocol_is_correct()
        }

    }

    #[test]
    fn larger_full_protocol_is_correct() {
        let cfg_expand = r#"
        {
            "n": 2,
            "nu_1": 9,
            "nu_2": 5,
            "p": 256,
            "q2_bits": 22,
            "t_gsw": 7,
            "t_conv": 3,
            "t_exp_left": 5,
            "t_exp_right": 5,
            "instances": 4,
            "db_item_size": 32768
        }
        "#;
        let cfg = cfg_expand;
        let params = params_from_json(&cfg);

        full_protocol_is_correct_for_params(&params);
    }
}
