use crate::common;

use std::cmp::{Ord, Eq, PartialEq, PartialOrd, Ordering};
use std::fmt;
use std::mem;
use std::ops::*;


// TODO:
// note: don't be scared of the amount of work, once I implement this once, the others will be easy, just a lot of refactor
// comparison operators
// implement shift only for primitive types - for indexing reasons
// addition
// multiplication
// division
// implement all the operators for different 
// negative variant
// negation
// subtraction
// conversion operators, both from basic types and types defined here (even different sizes of this type)
// constructor from string, base 10, 2, hex (maybe even general base)
// make general utils for some functions like binary and hex fmt
// create general number traits and use one of them for type of data inside IntStatic
// write documentation
// cover everything with unit tests
// lower/upper exp fmt
// when killing time: octal fmt
// maybe do wrapping/saturating variant
// in number traits create some trait for from_signed, to_singned, from_unsigned and to_unsigned
// also create some trait for getting 2x sized type of a primitive type and getting 1/2 primitive type
// TODO: optimize parameters on some operator trait functions
// - for example use &self instead of just self, or use mut self to reuse the variable, but check if it's even possible at all

#[derive(Debug, Copy, Clone)] // TODO: maybe implemet with Display, because normal numbers have it like that (I think)
pub struct IntStatic<const N: usize, const S: bool>
{
    data: [u64; N]
}

impl<const N: usize, const S: bool> IntStatic<{N}, {S}> {

    pub fn zero() -> Self {
        IntStatic::bit_min()
    }

    pub fn one() -> Self {
        IntStatic::from_num(1)
    }

    pub fn bit_min() -> Self {
        IntStatic::filled(0)
    }

    pub fn bit_max() -> Self {
        IntStatic::filled(u64::MAX)
    }

    pub fn min() -> Self {
        if S {
            let mut data: [u64; N] = [0; N];
            data[data.len()-1] = 1 << (mem::size_of::<u64>()*8 - 1);
            IntStatic { data }
        } else {
            IntStatic::bit_min()
        }
    }

    pub fn max() -> Self {
        if S {
            let mut data: [u64; N] = [u64::MAX; N];
            data[data.len()-1] = !(1 << (mem::size_of::<u64>()*8 - 1));
            IntStatic { data }
        } else {
            IntStatic::bit_max()
        }
    }

    pub fn from_num(num: u64) -> Self {
        let mut data: [u64; N] = [0; N];
        data[0] = num;
        IntStatic { data }
    }

    pub fn filled(num: u64) -> Self {
        let data: [u64; N] = [num; N];
        IntStatic { data }
    }

    pub fn from_data(data: [u64; N]) -> Self {
        IntStatic { data }
    }

    pub fn get_data(&self) -> &[u64; N] {
        &self.data
    }

    pub fn get_data_mut(&mut self) -> &mut [u64; N] {
        &mut self.data
    }

    fn to_hex(&self) -> String {
        common::to_hex(&self.data)
    }

    fn to_binary(&self) -> String {
        common::to_binary(&self.data)
    }

    // if the nuber is zero, the index returned is 0
    fn largest_non_zero_index(&self) -> usize {
        for i in (0..N).rev() {
            if self.data[i] != 0 {
                return i;
            }
        }
        0
    }
}

impl<const N: usize, const S: bool> fmt::Display for IntStatic<{N}, {S}> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // TODO: real implementation with division + test
        write!(f, "{}", self.data[0])
    }
}

impl<const N: usize, const S: bool> fmt::Binary for IntStatic<{N}, {S}> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.pad_integral(true, "0b", &self.to_binary())
    }
}

impl<const N: usize, const S: bool> fmt::LowerHex for IntStatic<{N}, {S}> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.pad_integral(true, "0x", &self.to_hex())
    }
}

impl<const N: usize, const S: bool> fmt::UpperHex for IntStatic<{N}, {S}> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.pad_integral(true, "0x", &self.to_hex().to_uppercase())
    }
}

impl<const N: usize, const S: bool> Ord for IntStatic<{N}, {S}> {
    fn cmp(&self, rhs: &Self) -> Ordering {
        if S {
            // FIXME: implement for signed
            return Ordering::Equal;
        } else {
            for i in (0..self.data.len()).rev() {
                if self.data[i] < rhs.data[i] {
                    return Ordering::Less;
                } else if self.data[i] > rhs.data[i] {
                    return Ordering::Greater;
                }
            }
            return Ordering::Equal;
        }
    }
}

impl<const N: usize, const S: bool> Eq for IntStatic<{N}, {S}> {}

impl<const N: usize, const S: bool> PartialOrd for IntStatic<{N}, {S}> {
    fn partial_cmp(&self, rhs: &Self) -> Option<Ordering> {
        Some(self.cmp(rhs))
    }
}

impl<const N: usize, const S: bool> PartialEq for IntStatic<{N}, {S}> {
    fn eq(&self, rhs: &Self) -> bool {
        for i in (0..self.data.len()).rev() {
            if self.data[i] != rhs.data[i] {
                return false;
            }
        }
        return true;
    }
}

impl<const N: usize, const S: bool> BitAnd for IntStatic<{N}, {S}> {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        let mut out = self;
        out &= rhs;
        out
    }
}

impl<const N: usize, const S: bool> BitAndAssign for IntStatic<{N}, {S}> {
    fn bitand_assign(&mut self, rhs: Self) {
        for i in 0..N {
            self.data[i] &= rhs.data[i];
        }
    }
}

impl<const N: usize, const S: bool> BitOr for IntStatic<{N}, {S}> {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        let mut out = self;
        out |= rhs;
        out
    }
}

impl<const N: usize, const S: bool> BitOrAssign for IntStatic<{N}, {S}> {
    fn bitor_assign(&mut self, rhs: Self) {
        for i in 0..N {
            self.data[i] |= rhs.data[i];
        }
    }
}

impl<const N: usize, const S: bool> BitXor for IntStatic<{N}, {S}> {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        let mut out = self;
        out ^= rhs;
        out
    }
}

impl<const N: usize, const S: bool> BitXorAssign for IntStatic<{N}, {S}> {
    fn bitxor_assign(&mut self, rhs: Self) {
        for i in 0..N {
            self.data[i] ^= rhs.data[i];
        }
    }
}

impl<const N: usize, const S: bool> Not for IntStatic<{N}, {S}> {
    type Output = Self;

    fn not(self) -> Self::Output {
        let mut out = self;
        for i in 0..N {
            out.data[i] = !out.data[i];
        }
        out
    }
}

impl<const N: usize, const S: bool> Shl<usize> for IntStatic<{N}, {S}> {
    type Output = Self;

    fn shl(self, rhs: usize) -> Self::Output {
        let mut out = self;
        out <<= rhs;
        out
    }
}

impl<const N: usize, const S: bool> ShlAssign<usize> for IntStatic<{N}, {S}> {
    fn shl_assign(&mut self, rhs: usize) {
        let (block_shift, local_shift) = common::shift_parts(rhs);
        for i in (0..N).rev() {
            self.data[i] = common::shl_block(i, &self.data, block_shift, local_shift);
        }
    }
}

impl<const N: usize, const S: bool> Shr<usize> for IntStatic<{N}, {S}> {
    type Output = Self;

    fn shr(self, rhs: usize) -> Self::Output {
        let mut out = self;
        out >>= rhs;
        out
    }
}

impl<const N: usize, const S: bool> ShrAssign<usize> for IntStatic<{N}, {S}> {
    fn shr_assign(&mut self, rhs: usize) {
        let (block_shift, local_shift) = common::shift_parts(rhs);
        for i in 0..N {
            self.data[i] = common::shr_block(i, &self.data, block_shift, local_shift);
        }
    }
}

impl<const N: usize, const S: bool> Add for IntStatic<{N}, {S}> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        let mut out = self;
        out += rhs;
        out
    }
}

impl<const N: usize, const S: bool> AddAssign for IntStatic<{N}, {S}> {
    fn add_assign(&mut self, rhs: Self) {
        let mut overflow = 0u64;
        for i in 0..N {
            (self.data[i], overflow) = common::add_inout_overflow(self.data[i], rhs.data[i], overflow);
        }
    }
}

impl<const N: usize, const S: bool> Mul for IntStatic<{N}, {S}> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        let mut out = IntStatic::<N,S>::zero();
        for left_idx in 0..N {
            let mut overflow = 0u64;
            // end early (N - left_idx), results after that are overflowing the static int of size N
            for right_idx in 0..(N - left_idx) {
                let out_idx = left_idx + right_idx;
                
                let accumulator = &mut out.data[out_idx];
                let left = self.data[left_idx];
                let right = rhs.data[right_idx];

                (*accumulator, overflow) = common::mul_inout_overflow_acc(left, right, overflow, *accumulator);
            }
        }
        out
    }
}

impl<const N: usize, const S: bool> MulAssign for IntStatic<{N}, {S}> {
    fn mul_assign(&mut self, rhs: Self) {
        // possible implementation with diagonals for in-place evaluation:
        // maybe move this to its own function mul_assign_inplace
        // going by the diagonals with same index sum of the inputs = out index
        // let mut overflow = 0u64;
        // the seccond overflow is enough only if N is not bigger than max number inside used primitive type (here u64, which makes it fine)
        // but it could cause problems when generalizing to arbitrary primitive integer type
        // on the rhs hand this could be also huge optimization for dynamic integers
        // let mut overflow_overflow = 0u64;
        // for out_idx in 0..N {
        //     let mut accumulator = overflow;
        //     overflow = overflow_overflow;
        //     overflow_overflow = 0u64;
        //     for left_idx in 0..(out_idx + 1) {
        //         let right_idx = out_idx - left_idx;
        //
        //         let left = self.data[left_idx];
        //         let right = rhs.data[right_idx];
        //         
        //         let mut new_overflow = 0;
        //         let mut new_overflow_overflow = 0;
        //         (accumulator, new_overflow) = common::mul_out_overflow_acc(left, right, accumulator);
        //         (overflow, new_overflow_overflow) = add_out_overflow(verflow, new_overflow);
        //         overflow_overflow += new_overflow_overflow;
        //     }
        //     self.data[out_idx] = accumulator;
        // }

        // because of complications described above using mul implementation
        *self = *self * rhs;
    }
}

impl<const N: usize, const S: bool> Div<u32> for IntStatic<{N}, {S}> {
    type Output = Self;

    fn div(self, rhs: u32) -> Self::Output {
        let mut out = self;
        out /= rhs;
        out
    }
}

impl<const N: usize, const S: bool> DivAssign<u32> for IntStatic<{N}, {S}> {
    fn div_assign(&mut self, rhs: u32) {
        // TODO: make some tests
        let rhs = rhs as u64;
        let mut rem = 0;
        for i in (0..N).rev() {
            (self.data[i], rem) = common::div_inout_rem(self.data[i], rhs, rem);
        }
    }
}

impl<const N: usize, const S: bool> Rem<u32> for IntStatic<{N}, {S}> {
    type Output = u32;

    fn rem(self, rhs: u32) -> Self::Output {
        // TODO: make some tests
        let rhs = rhs as u64;
        let mut rem = 0;
        for i in (0..N).rev() {
            (_, rem) = common::div_inout_rem(self.data[i], rhs, rem);
        }
        rem as u32
    }
}

impl<const N: usize, const S: bool> RemAssign<u32> for IntStatic<{N}, {S}> {
    fn rem_assign(&mut self, rhs: u32) {
        // TODO: make some tests
        let rem = *self % rhs;
        self.data = [0; N];
        self.data[0] = rem as u64;
    }
}

impl<const N: usize, const S: bool> Div for IntStatic<{N}, {S}> {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        const U64_BITS_COUNT: usize = mem::size_of::<u64>()*8;

        let mut out = Self::zero();
        let mut lhs_temp = self;
        let mut rhs_temp = rhs;

        let rhs_non_zero = rhs_temp.largest_non_zero_index();
        let rhs_max_bit = common::get_max_bit(rhs_temp.data[rhs_non_zero]);
        let mut rhs_shift = 0usize;
        while lhs_temp > rhs {
            let lhs_non_zero = lhs_temp.largest_non_zero_index();
            let lhs_max_bit = common::get_max_bit(lhs_temp.data[lhs_non_zero]);
            let mut new_rhs_shift = (lhs_non_zero - rhs_non_zero) * U64_BITS_COUNT + lhs_max_bit - rhs_max_bit;
            if new_rhs_shift >= rhs_shift {
                rhs_temp <<= new_rhs_shift - rhs_shift;
            } else {
                rhs_temp >>= rhs_shift - new_rhs_shift;
            }

            if lhs_temp < rhs_temp {
                // rhs_shift should be > 0
                new_rhs_shift -= 1;
                rhs_temp >>= 1;
            }
            // FIXME: need implementation of -=
            // lhs_temp -= rhs_temp;
            // now somehow shift the prev bit in out.data, probably by rhs_shift - new_rhs_shift
            out.data[0] += 1;
            rhs_shift = new_rhs_shift;
        }
        // remainder is whats left in lhs_temp
        out
    }
}

#[allow(non_camel_case_types)]
pub type u_static<const N: usize> = IntStatic<N, false>;
#[allow(non_camel_case_types)]
pub type i_static<const N: usize> = IntStatic<N, true>;

#[allow(non_camel_case_types)]
pub type u_s<const N: usize> = IntStatic<N, false>;
#[allow(non_camel_case_types)]
pub type i_s<const N: usize> = IntStatic<N, true>;

#[allow(non_camel_case_types)]
pub type u192 = IntStatic<3, false>;
#[allow(non_camel_case_types)]
pub type u256 = IntStatic<4, false>;
#[allow(non_camel_case_types)]
pub type u320 = IntStatic<5, false>;
#[allow(non_camel_case_types)]
pub type u384 = IntStatic<6, false>;
#[allow(non_camel_case_types)]
pub type u448 = IntStatic<7, false>;
#[allow(non_camel_case_types)]
pub type u512 = IntStatic<8, false>;
#[allow(non_camel_case_types)]
pub type u576 = IntStatic<9, false>;
#[allow(non_camel_case_types)]
pub type u640 = IntStatic<10, false>;
#[allow(non_camel_case_types)]
pub type u704 = IntStatic<11, false>;
#[allow(non_camel_case_types)]
pub type u768 = IntStatic<12, false>;
#[allow(non_camel_case_types)]
pub type u832 = IntStatic<13, false>;
#[allow(non_camel_case_types)]
pub type u896 = IntStatic<14, false>;
#[allow(non_camel_case_types)]
pub type u960 = IntStatic<15, false>;
#[allow(non_camel_case_types)]
pub type u1024 = IntStatic<16, false>;

#[allow(non_camel_case_types)]
pub type i192 = IntStatic<3, true>;
#[allow(non_camel_case_types)]
pub type i256 = IntStatic<4, true>;
#[allow(non_camel_case_types)]
pub type i320 = IntStatic<5, true>;
#[allow(non_camel_case_types)]
pub type i384 = IntStatic<6, true>;
#[allow(non_camel_case_types)]
pub type i448 = IntStatic<7, true>;
#[allow(non_camel_case_types)]
pub type i512 = IntStatic<8, true>;
#[allow(non_camel_case_types)]
pub type i576 = IntStatic<9, true>;
#[allow(non_camel_case_types)]
pub type i640 = IntStatic<10, true>;
#[allow(non_camel_case_types)]
pub type i704 = IntStatic<11, true>;
#[allow(non_camel_case_types)]
pub type i768 = IntStatic<12, true>;
#[allow(non_camel_case_types)]
pub type i832 = IntStatic<13, true>;
#[allow(non_camel_case_types)]
pub type i896 = IntStatic<14, true>;
#[allow(non_camel_case_types)]
pub type i960 = IntStatic<15, true>;
#[allow(non_camel_case_types)]
pub type i1024 = IntStatic<16, true>;


#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn int_static_zero() {
        let data: [u64; 3] = [0; 3];
        let num = u_s::<3>::zero();
        assert_eq!(*num.get_data(), data);
    }

    #[test]
    fn int_static_from_data() {
        let data: [u64; 4] = [1, 2, 3, 4];
        let num = u_s::<4>::from_data(data);
        assert_eq!(*num.get_data(), data);
    }

    #[test]
    fn int_static_to_string() {
        let num = u_s::<4>::from_data([1, 2, 3, 4]);
        assert_eq!(num.to_string(), "1");
    }

    #[test]
    fn int_static_to_binary_string() {
        assert_eq!(
            format!("{:b}", u_s::<2>::from_data([1, u64::MAX])),
            "11111111111111111111111111111111111111111111111111111111111111110000000000000000000000000000000000000000000000000000000000000001"
        );
        assert_eq!(
            format!("{:b}", u_s::<2>::from_data([3, 1])),
            "10000000000000000000000000000000000000000000000000000000000000011"
        );
    }

    #[test]
    fn int_static_to_binary_string_u64() {
        assert_eq!(
            format!("{:b}", u_s::<1>::from_num(1)),
            format!("{:b}", 1)
        );
        assert_eq!(
            format!("{:b}", i_s::<1>::from_num(1)),
            format!("{:b}", 1)
        );
        assert_eq!(
            format!("{:b}", u_s::<1>::from_num(165)),
            format!("{:b}", 165)
        );
        assert_eq!(
            format!("{:#b}", u_s::<1>::from_num(5)),
            format!("{:#b}", 5)
        );
        assert_eq!(
            format!("{:032b}", u_s::<1>::from_num(5)),
            format!("{:032b}", 5)
        );
        assert_eq!(
            format!("{:032b}", u_s::<1>::from_num(5)),
            format!("{:032b}", 5)
        );
        assert_eq!(
            format!("{:<5b}", u_s::<1>::from_num(2)),
            format!("{:<5b}", 2)
        );
        assert_eq!(
            format!("{:-<5b}", u_s::<1>::from_num(2)),
            format!("{:-<5b}", 2)
        );
        assert_eq!(
            format!("{:^5b}", u_s::<1>::from_num(2)),
            format!("{:^5b}", 2)
        );
        assert_eq!(
            format!("{:>5b}", u_s::<1>::from_num(2)),
            format!("{:>5b}", 2)
        );
        assert_eq!(
            format!("{:b}", u_s::<1>::from_num(u64::MAX)),
            format!("{:b}", -1i64)
        );
        assert_eq!(
            format!("{:b}", i_s::<1>::from_num(u64::MAX)),
            format!("{:b}", -1i64)
        );
        assert_eq!(
            format!("{:b}", u_s::<1>::from_num(0)),
            format!("{:b}", 0)
        );
        assert_eq!(
            format!("{:b}", i_s::<1>::from_num(0)),
            format!("{:b}", 0)
        );
    }

    #[test]
    fn int_static_to_lower_hex() {
        assert_eq!(format!("{:x}", u_s::<2>::from_data([1, u64::MAX])), "ffffffffffffffff0000000000000001");
        assert_eq!(format!("{:x}", u_s::<2>::from_data([3, 1])), "10000000000000003");
    }

    #[test]
    fn int_static_to_upper_hex() {
        assert_eq!(format!("{:X}", u_s::<2>::from_data([1, u64::MAX])), "FFFFFFFFFFFFFFFF0000000000000001");
        assert_eq!(format!("{:X}", u_s::<2>::from_data([3, 1])), "10000000000000003");
    }

    #[test]
    fn int_static_to_hex_string_u64() {
        assert_eq!(
            format!("{:x}", u_s::<1>::from_num(1)),
            format!("{:x}", 1)
        );
        assert_eq!(
            format!("{:x}", i_s::<1>::from_num(1)),
            format!("{:x}", 1)
        );
        assert_eq!(
            format!("{:x}", u_s::<1>::from_num(165)),
            format!("{:x}", 165)
        );
        assert_eq!(
            format!("{:#x}", u_s::<1>::from_num(5)),
            format!("{:#x}", 5)
        );
        assert_eq!(
            format!("{:032x}", u_s::<1>::from_num(5)),
            format!("{:032x}", 5)
        );
        assert_eq!(
            format!("{:032x}", u_s::<1>::from_num(5)),
            format!("{:032x}", 5)
        );
        assert_eq!(
            format!("{:<5x}", u_s::<1>::from_num(2)),
            format!("{:<5x}", 2)
        );
        assert_eq!(
            format!("{:-<5x}", u_s::<1>::from_num(2)),
            format!("{:-<5x}", 2)
        );
        assert_eq!(
            format!("{:^5x}", u_s::<1>::from_num(2)),
            format!("{:^5x}", 2)
        );
        assert_eq!(
            format!("{:>5x}", u_s::<1>::from_num(2)),
            format!("{:>5x}", 2)
        );
        assert_eq!(
            format!("{:x}", u_s::<1>::from_num(u64::MAX)),
            format!("{:x}", -1i64)
        );
        assert_eq!(
            format!("{:x}", i_s::<1>::from_num(u64::MAX)),
            format!("{:x}", -1i64)
        );
        assert_eq!(
            format!("{:x}", u_s::<1>::from_num(0)),
            format!("{:x}", 0)
        );
        assert_eq!(
            format!("{:x}", i_s::<1>::from_num(0)),
            format!("{:x}", 0)
        );
    }

    #[test]
    fn int_static_cmp() {
        // TODO: write better tests, more understandable, only edge cases
        assert_eq!(u_s::<2>::from_data([1, 2]), u_s::<2>::from_data([1, 2]));
        assert_eq!(u_s::<3>::from_data([3, 0, 2]), u_s::<3>::from_data([3, 0, 2]));
        assert_ne!(u_s::<2>::from_data([1, 2]), u_s::<2>::from_data([2, 1]));
        assert_ne!(u_s::<3>::from_data([1, 0, 2]), u_s::<3>::from_data([1, 0, 1]));
        assert_eq!(u_s::<2>::from_data([1, 2]).cmp(&u_s::<2>::from_data([1, 2])), Ordering::Equal);
        assert_eq!(u_s::<3>::from_data([3, 0, 2]).cmp(&u_s::<3>::from_data([3, 0, 2])), Ordering::Equal);
        assert_eq!(u_s::<3>::from_data([0, 0, 0]).cmp(&u_s::<3>::from_data([1, 0, 0])), Ordering::Less);
        assert_eq!(u_s::<3>::from_data([0, 0, 0]).cmp(&u_s::<3>::from_data([0, 1, 0])), Ordering::Less);
        assert_eq!(u_s::<3>::from_data([1, 0, 0]).cmp(&u_s::<3>::from_data([0, 1, 0])), Ordering::Less);
        assert_eq!(u_s::<3>::from_data([1, 0, 0]).cmp(&u_s::<3>::from_data([0, 0, 1])), Ordering::Less);
        assert_eq!(u_s::<3>::from_data([1, 0, 1]).cmp(&u_s::<3>::from_data([0, 1, 1])), Ordering::Less);
        assert_eq!(u_s::<3>::from_data([1, 0, 1]).cmp(&u_s::<3>::from_data([2, 0, 1])), Ordering::Less);
        assert_eq!(u_s::<3>::from_data([2, 0, 1]).cmp(&u_s::<3>::from_data([1, 0, 1])), Ordering::Greater);
        assert_eq!(u_s::<3>::from_data([1, 0, 0]).cmp(&u_s::<3>::from_data([0, 0, 0])), Ordering::Greater);
        assert_eq!(u_s::<3>::from_data([0, 1, 0]).cmp(&u_s::<3>::from_data([0, 0, 0])), Ordering::Greater);
        assert_eq!(u_s::<3>::from_data([0, 1, 0]).cmp(&u_s::<3>::from_data([1, 0, 0])), Ordering::Greater);
        assert_eq!(u_s::<3>::from_data([0, 0, 1]).cmp(&u_s::<3>::from_data([1, 0, 0])), Ordering::Greater);
        assert_eq!(u_s::<3>::from_data([0, 1, 1]).cmp(&u_s::<3>::from_data([1, 0, 1])), Ordering::Greater);
        assert_eq!(u_s::<3>::from_data([2, 0, 1]).cmp(&u_s::<3>::from_data([1, 0, 1])), Ordering::Greater);
    }
}