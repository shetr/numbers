// common functions used across several number types

use std::mem;

const U64_BITS_COUNT: usize = mem::size_of::<u64>()*8;
const U64_HALF_BITS_COUNT: usize = mem::size_of::<u64>()*4;
const U64_LOWER_MASK: u64 = u64::MAX >> U64_HALF_BITS_COUNT;
//const U64_UPPER_MASK: u64 = u64::MAX << U64_HALF_BITS_COUNT;
const U64_HEX_CHAR_COUNT: usize = mem::size_of::<u64>()*2;

// shift that never rotates, overflowing bits are just removed (no std shl implements this)
pub fn not_rotating_shl(value: u64, shift: u32) -> u64 {
    if shift >= U64_BITS_COUNT as u32 {
        return 0u64;
    }
    let mask = u64::MAX >> shift;
    (value & mask).wrapping_shl(shift)
}

// shift that never rotates, overflowing bits are just removed, similar to normal shr, but it never panics
pub fn not_rotating_shr(value: u64, shift: u32) -> u64 {
    if shift >= U64_BITS_COUNT as u32 {
        return 0u64;
    }
    value >> shift
}

fn mask_lower(n: u64) -> u64 {
    n & U64_LOWER_MASK
}

fn upper_to_lower(n: u64) -> u64 {
    not_rotating_shr(n, U64_HALF_BITS_COUNT as u32)
}

fn lower_to_upper(n: u64) -> u64 {
    not_rotating_shl(n, U64_HALF_BITS_COUNT as u32)
}

fn join_upper_lower(upper: u64, lower: u64) -> u64 {
    lower_to_upper(upper) | mask_lower(lower)
}

pub fn add_out_overflow(a: u64, b: u64) -> (u64, u64) {
    let lower_sum = mask_lower(a) + mask_lower(b);
    let lower_overflow = upper_to_lower(lower_sum);
    let upper_sum = lower_overflow + upper_to_lower(a) + upper_to_lower(b);
    let out_sum = join_upper_lower(upper_sum, lower_sum);
    let out_overflow = upper_to_lower(upper_sum);
    return (out_sum, out_overflow);
}

// prev_overflow and returned overflow should be 0 or 1, returns (addition, overflow)
pub fn add_inout_overflow(a: u64, b: u64, in_overflow: u64) -> (u64, u64) {
    let lower_sum = in_overflow + mask_lower(a) + mask_lower(b);
    let lower_overflow = upper_to_lower(lower_sum);
    let upper_sum = lower_overflow + upper_to_lower(a) + upper_to_lower(b);
    let out_sum = join_upper_lower(upper_sum, lower_sum);
    let out_overflow = upper_to_lower(upper_sum);
    return (out_sum, out_overflow);
}

fn add3_out_overflow(a: u64, b: u64, c: u64) -> (u64, u64) {
    let lower_sum = mask_lower(a) + mask_lower(b) + mask_lower(c);
    let lower_overflow = upper_to_lower(lower_sum);
    let upper_sum = lower_overflow + upper_to_lower(a) + upper_to_lower(b) + upper_to_lower(c);
    let out_sum = join_upper_lower(upper_sum, lower_sum);
    let out_overflow = upper_to_lower(upper_sum);
    return (out_sum, out_overflow);
}

// a and b should be lower half bits
fn mul_upper_half_out_overflow(a: u64, b: u64) -> (u64, u64) {
    let mul = a * b;
    (lower_to_upper(mul), upper_to_lower(mul))
}

fn mul_out_overflow(a: u64, b: u64) -> (u64, u64) {
    // TODO: add description why it behaves correctly
    let a0 = mask_lower(a);
    let a1 = upper_to_lower(a);
    let b0 = mask_lower(b);
    let b1 = upper_to_lower(b);

    let a0b0 =  a0*b0;
    let (m_a0b1, o_a0b1) =  mul_upper_half_out_overflow(a0, b1);
    let (m_a1b0, o_a1b0) =  mul_upper_half_out_overflow(a1, b0);
    let a1b1 =  a1*b1;

    let (out_mul, o_a0b0_m_a0b1_m_a1b0) = add3_out_overflow(a0b0, m_a0b1, m_a1b0);
    let out_overflow = o_a0b1 + o_a1b0 + a1b1 + o_a0b0_m_a0b1_m_a1b0;

    return (out_mul, out_overflow);
}

pub fn mul_inout_overflow_acc(a: u64, b: u64, in_overflow: u64, accumulator: u64) -> (u64, u64) {
    let (mul_res, mul_overflow) = mul_out_overflow(a, b);
    let (add_res, add_overflow) = add3_out_overflow(accumulator, mul_res, in_overflow);
    let out_overflow = mul_overflow + add_overflow;
    (add_res, out_overflow)
}

// b and in_rem should have its upper half bits set to zero
// returns (div, rem)
pub fn div_inout_rem(a: u64, b: u64, in_rem: u64) -> (u64, u64) {
    // div results should be in lower half part of the bits, because all remainders are smaller than b

    // first divide the upper part using in_rem
    let a_upper = lower_to_upper(in_rem) | upper_to_lower(a);
    let div_upper = lower_to_upper(a_upper / b);
    let rem_upper = lower_to_upper(a_upper % b);

    // then divide the lower part using rem_upper
    let a_lower = rem_upper | mask_lower(a);
    let div_lower = a_lower / b;
    let rem_lower = a_lower % b;

    (div_upper | div_lower, rem_lower)
}

pub fn get_max_bit(n: u64) -> usize {
    // TODO: it would be cool do do some performance test comparing to variant which just shifts 1 64-times
    let mut max = U64_BITS_COUNT;
    let mut min = 0usize;
    while (max - min) > 1 {
        let avg = (max + min) >> 1;
        let avg_bit = 1 << avg;
        if n < avg_bit {
            max = avg;
        } else {
            min = avg;
        }
    }
    min
}

pub fn get_sign_bit(n: u64) -> bool {
    n & (1 << (mem::size_of::<u64>()*8 - 1)) > 0
}

pub fn shift_parts(shift: usize) -> (usize, usize) {
    let block_shift = shift / U64_BITS_COUNT;
    let local_shift = shift - block_shift * U64_BITS_COUNT;
    (block_shift, local_shift)
}

// TODO: maybe generalize shl_block and shr_block with same function
// TODO: tests for shl_block and shr_block

pub fn shl_block(idx: usize, data: &[u64], block_shift: usize, local_shift: usize) -> u64 {
    // TODO: some tests on edge cases
    let left_part_idx = idx as isize - block_shift as isize;
    let right_part_idx = left_part_idx - 1;
    let left_part = if left_part_idx >= 0 { not_rotating_shl(data[left_part_idx as usize], local_shift as u32) } else { 0u64 };
    let right_part = if right_part_idx >= 0 { not_rotating_shr(data[right_part_idx as usize], (U64_BITS_COUNT - local_shift) as u32) } else { 0u64 };
    left_part | right_part
}

pub fn shr_block(idx: usize, data: &[u64], block_shift: usize, local_shift: usize) -> u64 {
    // FIXME: shifts with 64 bits panic because of overflow
    // TODO: some tests on edge cases
    let right_part_idx = idx + block_shift;
    let left_part_idx = right_part_idx + 1;
    let right_part = if right_part_idx < data.len() { not_rotating_shr(data[right_part_idx], local_shift as u32) } else { 0u64 };
    let left_part = if left_part_idx < data.len() { not_rotating_shl(data[left_part_idx], (U64_BITS_COUNT - local_shift) as u32) } else { 0u64 };
    left_part | right_part
}

fn hex_to_u64(ch: u8) -> Result<u64, String> {
    let num = ch as u64;
    if num >= '0' as u64 && num <= '9' as u64 {
        return Ok(num - '0' as u64);
    }
    if num >= 'a' as u64 && num <= 'f' as u64 {
        return Ok(10u64 + num - 'a' as u64);
    }
    if num >= 'A' as u64 && num <= 'F' as u64 {
        return Ok(10u64 + num - 'A' as u64);
    }
    Err(String::from("invalid hexadecimal character"))
}

pub fn from_hex(hex: &str, out_data: &mut [u64]) -> Option<String> {
    if hex.len() > out_data.len() * U64_HEX_CHAR_COUNT {
        return Some(String::from("input number string is too big to fit in the provided buffer"));
    }
    for (i, ch) in hex.as_bytes().iter().rev().enumerate() {
        let data_offset = i / U64_HEX_CHAR_COUNT;
        let hex_offset = i % U64_HEX_CHAR_COUNT;
        let bit_offset = hex_offset * 4;
        let maybe_value = hex_to_u64(*ch);
        match maybe_value {
            Ok(value) => out_data[data_offset] |= value << bit_offset,
            Err(err) => { return Some(err); }
        }
    }
    None
}

pub fn to_hex(data: &[u64]) -> String {
    let mut hex = String::with_capacity(data.len()*U64_HEX_CHAR_COUNT);
    let mut only_zeros = true;
    for chunk in data.iter().rev() {
        let mut bit_mask: u64 = 0xF << (U64_BITS_COUNT - 4);
        for i in (0..U64_HEX_CHAR_COUNT).rev() {
            let masked = chunk & bit_mask;
            if masked != 0 {
                only_zeros = false;
            }
            if !only_zeros {
                let val = (masked >> i * 4) as u8;
                hex.push(((if val < 10 { '0' as u8 + val} else { 'a' as u8 + val - 10})) as char);
            }
            bit_mask >>= 4;
        }
    }
    if only_zeros {
        hex.push('0');
    }
    hex
}

pub fn to_binary(data: &[u64]) -> String {
    let mut bin = String::with_capacity(data.len()*U64_BITS_COUNT);
    let mut only_zeros = true;
    for chunk in data.iter().rev() {
        let mut bit_mask: u64 = 1 << (U64_BITS_COUNT - 1);
        for _ in (0..U64_BITS_COUNT).rev() {
            let is_zero = chunk & bit_mask == 0;
            if !is_zero {
                only_zeros = false;
            }
            if !only_zeros {
                bin.push(if is_zero {'0'} else {'1'});
            }
            bit_mask >>= 1;
        }
    }
    if only_zeros {
        bin.push('0');
    }
    bin
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn shl_block_wrap_left() {
        assert_eq!(shl_block(0, &[u64::MAX], 0, U64_BITS_COUNT), 0);
    }

    #[test]
    fn shl_block_wrap_right() {
        assert_eq!(shl_block(1, &[u64::MAX, 0], 0, U64_BITS_COUNT), u64::MAX);
    }
    
    #[test]
    fn shl_block_wrap_left_half() {
        assert_eq!(shl_block(0, &[u64::MAX, 0], 0, 32), 0xFFFFFFFF00000000);
        assert_eq!(shl_block(1, &[u64::MAX, 0], 0, 32), 0xFFFFFFFF);
    }

    #[test]
    fn add_out_overflow_max_max() {
        let (out, overflow) = add_out_overflow(u64::MAX, u64::MAX);
        assert_eq!(out, u64::MAX - 1);
        assert_eq!(overflow, 1);
    }
    
    #[test]
    fn add_out_overflow_1_max() {
        let (out, overflow) = add_out_overflow(1, u64::MAX);
        assert_eq!(out, 0);
        assert_eq!(overflow, 1);
    }
    #[test]
    fn add_inout_overflow_max_max_0() {
        let (out, overflow) = add_inout_overflow(u64::MAX, u64::MAX, 0);
        assert_eq!(out, u64::MAX - 1);
        assert_eq!(overflow, 1);
    }

    #[test]
    fn add_inout_overflow_max_max_1() {
        let (out, overflow) = add_inout_overflow(u64::MAX, u64::MAX, 1);
        assert_eq!(out, u64::MAX);
        assert_eq!(overflow, 1);
    }

    #[test]
    fn add3_out_overflow_max_max_max() {
        let (out, overflow) = add3_out_overflow(u64::MAX, u64::MAX, u64::MAX);
        assert_eq!(out, u64::MAX - 2);
        assert_eq!(overflow, 2);
    }

    #[test]
    fn mul_upper_half_out_overflow_lower_max_lower_max() {
        let (out, overflow) = mul_upper_half_out_overflow(U64_LOWER_MASK, U64_LOWER_MASK);
        // a = b = 2^32
        // (a - 1)^2 = a^2 - 2a + 1
        assert_eq!(out, lower_to_upper(1));
        assert_eq!(overflow, U64_LOWER_MASK - 1);
    }
    
    #[test]
    fn mul_out_overflow_max_max() {
        let (out, overflow) = mul_out_overflow(u64::MAX, u64::MAX);
        assert_eq!(out, 1);
        assert_eq!(overflow, u64::MAX - 1);
    }

    #[test]
    fn mul_inout_overflow_acc_max_max_max_max() {
        let (out, overflow) = mul_inout_overflow_acc(u64::MAX, u64::MAX, u64::MAX, u64::MAX);
        assert_eq!(out, u64::MAX);
        assert_eq!(overflow, u64::MAX);
    }

    #[test]
    fn div_inout_rem_max_lower_max_lower_max() {
        let (out, rem) = div_inout_rem(u64::MAX, U64_LOWER_MASK, U64_LOWER_MASK);
        // (a^2 - 1) / (a - 1) = ( (a - 1) * a + (a - 1) ) / (a - 1) = a + 1
        // a = 2^32, (2^64 - 1) / (2^32 - 1) = 2^32 + 1
        assert_eq!(out, U64_LOWER_MASK + 2);
        assert_eq!(rem, 0);
    }

    #[test]
    fn div_inout_rem_max_lower_max_0() {
        let (out, rem) = div_inout_rem(u64::MAX, U64_LOWER_MASK, 0);
        // (a^2 - 1) / (a - 1) = ( (a - 1) * a + (a - 1) ) / (a - 1) = a + 1
        // a = 2^32, (2^64 - 1) / (2^32 - 1) = 2^32 + 1
        assert_eq!(out, U64_LOWER_MASK + 2);
        assert_eq!(rem, 0);
    }

    #[test]
    fn div_inout_rem_max_lower_max_lower_max_m1() {
        let (out, rem) = div_inout_rem(u64::MAX, U64_LOWER_MASK, U64_LOWER_MASK - 1);
        assert_eq!(out, (0xFFFFFFFEFFFFFFFFFFFFFFFFu128 / 0xFFFFFFFFu128) as u64);
        assert_eq!(rem, (0xFFFFFFFEFFFFFFFFFFFFFFFFu128 % 0xFFFFFFFFu128) as u64);
    }
    
    #[test]
    fn get_max_bit_0() {
        assert_eq!(get_max_bit(0), 0);
    }
    
    #[test]
    fn get_max_bit_1() {
        assert_eq!(get_max_bit(1), 0);
    }

    #[test]
    fn get_max_bit_2() {
        assert_eq!(get_max_bit(2), 1);
    }
    
    #[test]
    fn get_max_bit_3() {
        assert_eq!(get_max_bit(3), 1);
    }
    
    #[test]
    fn get_max_bit_lower_max() {
        assert_eq!(get_max_bit(U64_LOWER_MASK), 31);
    }
    
    #[test]
    fn get_max_bit_2_to_30() {
        assert_eq!(get_max_bit(1 << 30), 30);
    }

    #[test]
    fn get_max_bit_2_to_31() {
        assert_eq!(get_max_bit(1 << 31), 31);
    }
    
    #[test]
    fn get_max_bit_2_to_32() {
        assert_eq!(get_max_bit(1 << 32), 32);
    }
    
    #[test]
    fn get_max_bit_2_to_33() {
        assert_eq!(get_max_bit(1 << 33), 33);
    }

    #[test]
    fn get_max_bit_2_to_63() {
        assert_eq!(get_max_bit(1 << 63), 63);
    }

    #[test]
    fn get_max_bit_max() {
        assert_eq!(get_max_bit(u64::MAX), 63);
    }

    #[test]
    fn get_sign_bit_max() {
        assert_eq!(get_sign_bit(u64::MAX), true);
    }

    #[test]
    fn get_sign_bit_nearly_max() {
        assert_eq!(get_sign_bit(u64::MAX >> 1), false);
    }

}