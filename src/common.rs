// common functions used across several number types

use std::mem;

const U64_BITS_COUNT: usize = mem::size_of::<u64>()*8;
const U64_HALF_BITS_COUNT: usize = mem::size_of::<u64>()*4;
const U64_LOWER_MASK: u64 = u64::MAX >> U64_HALF_BITS_COUNT;
//const U64_UPPER_MASK: u64 = u64::MAX << U64_HALF_BITS_COUNT;
const U64_HEX_CHAR_COUNT: usize = mem::size_of::<u64>()*2;

// overflow shloud be 0 or 1, returns (addition, overflow)
pub fn add_with_overflow(a: u64, b: u64, overflow: u64) -> (u64, u64) {
    let right_sum = overflow + (a & U64_LOWER_MASK) + (b & U64_LOWER_MASK);
    let right_overflow = right_sum >> U64_HALF_BITS_COUNT;
    let left_sum = right_overflow + (a >> U64_HALF_BITS_COUNT) + (b >> U64_HALF_BITS_COUNT);
    let out_sum = (left_sum << U64_HALF_BITS_COUNT) + (right_sum & U64_LOWER_MASK);
    let out_overflow = left_sum >> U64_HALF_BITS_COUNT;
    return (out_sum, out_overflow);
}

// maybe we can somehow generalize add and mul?

pub fn mul_with_overflow(a: u64, b: u64) -> (u64, u64) {
    // completely wrong, it must be done from 4 multiplications
    let right_mul = (a & U64_LOWER_MASK) * (b & U64_LOWER_MASK);
    let right_overflow = right_mul >> U64_HALF_BITS_COUNT; // TODO: add right overflow 
    let left_mul = (a >> U64_HALF_BITS_COUNT) * (b >> U64_HALF_BITS_COUNT);
    let out_mul = (left_mul << U64_HALF_BITS_COUNT) + right_mul & U64_LOWER_MASK;
    let out_overflow = left_mul >> U64_HALF_BITS_COUNT;
    return (out_mul, out_overflow);
}

pub fn shift_parts(shift: usize) -> (usize, usize) {
    let block_shift = shift / U64_BITS_COUNT;
    let local_shift = shift - block_shift * U64_BITS_COUNT;
    (block_shift, local_shift)
}

// TODO: maybe generalize shl_block and shr_block with same function

pub fn shl_block(idx: usize, data: &[u64], block_shift: usize, local_shift: usize) -> u64 {
    let left_part_idx = idx as isize - block_shift as isize;
    let right_part_idx = left_part_idx - 1;
    let left_part = if left_part_idx >= 0 { data[left_part_idx as usize] << local_shift } else { 0u64 };
    let right_part = if right_part_idx >= 0 { data[right_part_idx as usize] >> (U64_BITS_COUNT - local_shift) } else { 0u64 };
    left_part & right_part
}

pub fn shr_block(idx: usize, data: &[u64], block_shift: usize, local_shift: usize) -> u64 {
    let right_part_idx = idx + block_shift;
    let left_part_idx = right_part_idx + 1;
    let right_part = if right_part_idx < data.len() { data[right_part_idx] >> local_shift } else { 0u64 };
    let left_part = if left_part_idx < data.len() { data[left_part_idx] << (U64_BITS_COUNT - local_shift) } else { 0u64 };
    left_part & right_part
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