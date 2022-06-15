// common functions used across several number types

use std::mem;

// overflow shloud be 0 or 1, returns (addition, overflow)
pub fn add_with_overflow(a: u64, b: u64, overflow: u64) -> (u64, u64) {
    let half_bits = mem::size_of::<u64>()*4;
    let right_mask = u64::MAX >> half_bits;
    let right_sum = overflow + a & right_mask + b & right_mask;
    let right_overflow = right_sum >> half_bits;
    let left_sum = right_overflow + (a >> half_bits) + (b >> half_bits);
    let out_sum = (left_sum << half_bits) + right_sum & right_mask;
    let out_overflow = left_sum >> half_bits;
    return (out_sum, out_overflow);
}