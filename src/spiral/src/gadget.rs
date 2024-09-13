use crate::{params::*, poly::*};

pub fn get_bits_per(params: &Params, dim: usize) -> usize {
    let modulus_log2 = params.modulus_log2;
    if dim as u64 == modulus_log2 {
        return 1;
    }
    ((modulus_log2 as f64) / (dim as f64)).floor() as usize + 1
}

pub fn build_gadget(params: &Params, rows: usize, cols: usize) -> PolyMatrixRaw {
    let mut g = PolyMatrixRaw::zero(params, rows, cols);
    let nx = g.rows;
    let m = g.cols;

    assert_eq!(m % nx, 0);

    let num_elems = m / nx;
    let params = g.params;
    let bits_per = get_bits_per(params, num_elems);

    for i in 0..nx {
        for j in 0..num_elems {
            if bits_per * j >= 64 {
                continue;
            }
            let poly = g.get_poly_mut(i, i + j * nx);
            poly[0] = 1u64 << (bits_per * j);
        }
    }
    g
}

pub fn gadget_invert_rdim<'a>(out: &mut PolyMatrixRaw<'a>, inp: &PolyMatrixRaw<'a>, rdim: usize) {
    assert_eq!(out.cols, inp.cols);

    let params = inp.params;
    let mx = out.rows;
    let num_elems = mx / rdim;
    let bits_per = get_bits_per(params, num_elems);
    let mask = (1u64 << bits_per) - 1;

    for i in 0..inp.cols {
        for j in 0..rdim {
            for z in 0..params.poly_len {
                let val = inp.get_poly(j, i)[z];
                for k in 0..num_elems {
                    let bit_offs = usize::min(k * bits_per, 64) as u64;
                    let shifted = val.checked_shr(bit_offs as u32);
                    let piece = match shifted {
                        Some(x) => x & mask,
                        None => 0,
                    };

                    out.get_poly_mut(j + k * rdim, i)[z] = piece;
                }
            }
        }
    }
}

pub fn gadget_invert<'a>(out: &mut PolyMatrixRaw<'a>, inp: &PolyMatrixRaw<'a>) {
    gadget_invert_rdim(out, inp, inp.rows);
}

pub fn gadget_invert_alloc<'a>(mx: usize, inp: &PolyMatrixRaw<'a>) -> PolyMatrixRaw<'a> {
    let mut out = PolyMatrixRaw::zero(inp.params, mx, inp.cols);
    gadget_invert(&mut out, inp);
    out
}

#[cfg(test)]
mod test {
    use crate::util::get_test_params;

    use super::*;

    #[test]
    fn gadget_invert_is_correct() {
        let params = get_test_params();
        let mut mat = PolyMatrixRaw::zero(&params, 2, 1);
        mat.get_poly_mut(0, 0)[37] = 3;
        mat.get_poly_mut(1, 0)[37] = 6;
        let log_q = params.modulus_log2 as usize;
        // 这里的 mx 为什么是 2 * t， 我有一个大胆的想法，这里应该是 mat.rows * t , 这个测试用例中 恰好 mat.rows = 2
        // 如何验证这个想法的准确性呢？我把2 改成3， 然后跑测试，预期肯定是不通过的
        // 失算了，这里改成 3 ，仍然是能通过测试，猜想是因为 3t 比起 2t 更大，能够容纳更多的元素，不会影响正确性
        // 改成 1 * log_q , 这里果然就报错了
        // 我们还要进一步验证这个问题，我们把上面的 mat 矩阵改成 (3, 1), 然后下面这里改成 2 ，预期还是会报错。
        // 果然报错了！
        // 那么这里就验证了我的猜想：mx = in.rows * t 
        // 我们再根据论文来进一步验证。论文里是 G_{n, z}^{-1} M 是逐列对 M 矩阵应用 G_{n, z}^{-1} 操作
        // 而在执行了 G_{n, z}^{-1} 后一个列向量的长度 变化是这个：R_q^n ---> R_q^m , m = nt , n 是列向量的长度，在这里也就是矩阵的行数
        // 所以， G_{n, z}^{-1} M 得到的矩阵维度是 (nt, l) , 只有行数会变，列数不变
        // G_{n, z}^{-1} 对向量的扩展，本质上是对向量的每一个元素 运用 g_z^{-1}, 也就是单个元素 会扩展为 t 个元素，现在一共 n 个元素，所以结果就是 nt 个元素
        // 前面我们提到的元素是 矩阵的每一个元素，那么具体是怎么扩展的呢？
        // 假设 输入矩阵只有2行：
        //                a    ----->  a_1, ...., a_t
        //                b    ----->  b_1, ...., b_t
        
        let result = gadget_invert_alloc(2 * log_q, &mat);
        // let result = gadget_invert_alloc(2 * log_q, &mat);
        // 但是具体在放置元素的时候，是这样
        //  [a_1, b_1]^T  [a_2, b_2]^T, ...., [a_t, b_t]^T
        //  也就是下面的 assert_eq, result 访问行时候的步长，这个步长显然是 in.rows
        // 单个元素被 分解为 base-z（默认为 2） 的结果是 a1 a2 a3 ... at, 注意这里是 从低位到高位， 即 1 1 0 .. 0 
        // 低 3位，即可以表示 3 ， 总共 t 位, t 取决于 params.modulus_log2
        assert_eq!(result.get_poly(0, 0)[37], 1);
        assert_eq!(result.get_poly(2, 0)[37], 1);
        assert_eq!(result.get_poly(4, 0)[37], 0); // binary for '3'
        // 同理，低 4 位 就可以表示 6
        assert_eq!(result.get_poly(1, 0)[37], 0);
        assert_eq!(result.get_poly(3, 0)[37], 1);
        assert_eq!(result.get_poly(5, 0)[37], 1);
        assert_eq!(result.get_poly(7, 0)[37], 0); // binary for '6'


        // 我们再往下拆一层，前面我们涉及到的都是矩阵元素这个粒度，而矩阵的每一个元素 都是长度为 N 的多项式
        // 这个又怎么理解？
        // 这个很好理解，如法炮制即可，最终的 分解为base-z 下的表示是在 多项式的每一个系数上发生的，观察 前面的 assert_eq
        // 指定了这个元素（多项式）的 第 37个系数，即  a_{37} x^37 的系数 a_{37}
        // 到这里几乎完全破案了 

    }


    #[test]
    fn shifted_test() {

        let val = 4 as u64;
        let bit_offs = 2;
        // 计算 val >> bit_off , 如果 bit_offs 大于 val 的比特数，或者相等，则 返回 None
        // 反之，返回结果 

        // 4 --> 1 0 0 , 2 ---> 结果是 1 
        let shifted = val.checked_shr(bit_offs as u32);
        // 1 
        println!("{}", shifted.unwrap());

        let val = 4 as u64;
        let bit_offs = 3;
        // 100 , 3 --> 预期结果应该是 None，但是实际是 0 
        let shifted = val.checked_shr(bit_offs as u32);
        println!("{}", shifted.unwrap());

        let val = 4 as u64;
        let bit_offs = 4;
        // 100 , 4 --> 预期结果应该是 None ？ 但是实际是 0 
        let shifted = val.checked_shr(bit_offs as u32);
        println!("{}", shifted.unwrap());

        // 不对不对，是我的理解有问题，看一下原文：
        // Checked shift right. Computes self >> rhs, returning None if rhs is larger than or equal to the number of bits in self.

        // 这里的number of bits in self，应该指的是这个类型的 bits
        // 下面试一下 65
        let val = 4 as u64;
        let bit_offs = 65 as u32;
        // u64 65 -> None
        let shifted = val.checked_shr(bit_offs as u32);
        println!("{:?}", shifted);
        // 此时果然就是 None 

        let val = 4 as u64;
        let bit_offs = 64 as u32;
        // u64 64 -> None
        let shifted = val.checked_shr(bit_offs as u32);
        println!("{:?}", shifted);

        // 下面再试一下 u32 33--> None 

        let val = 0 as u32;
        let bit_offs = 33 as u32;
        // u32  33 -> None
        let shifted = val.checked_shr(bit_offs as u32);
        println!("{:?}", shifted);

    }
}
