use crate::common;

use std::cmp::{Ord, Eq, PartialEq, PartialOrd, Ordering};
use std::fmt;
use std::mem;
use std::ops::*;


// TODO:
// note: don't be scared of the amount of work, once I implement this once, the others will be easy, just a lot of refactor
// add operator variants with references
// comparison operators
// implement shift only for primitive types - for indexing reasons
// addition
// multiplication
// division, remainder + operation returning both division and remainder
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
// maybe do wrapping, saturating, overflowing, checked and unchecked variant
// in number traits create some trait for from_signed, to_singned, from_unsigned and to_unsigned
// also create some trait for getting 2x sized type of a primitive type and getting 1/2 primitive type
// Add<i64>
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

    /*pub fn from_i64(num: i64) -> Self {
        let num = std::mem::transmute(num);
        if S {
            if common::get_sign_bit(num) {
                let mut data: [u64; N] = [u64::MAX; N];
                data[0] = num;
                return IntStatic { data }
            }
        }
        let mut data: [u64; N] = [0; N];
        data[0] = num;
        IntStatic { data }
    }*/

    // TODO: maybe change String to some custome type
    pub fn from_hex(hex: &str) -> Result<Self, String> {
        let mut out = Self::zero();
        match common::from_hex(hex, &mut out.data) {
            None => Ok(out),
            Some(message) => Err(message)
        }
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

    pub fn not_self(&mut self) {
        for i in 0..N {
            self.data[i] = !self.data[i];
        }
    }

    fn neg_self_priv(&mut self) {
        self.not_self();
        *self += 1;
    }

    fn neg_priv(&self) -> Self {
        let mut out = *self;
        out.neg_self_priv();
        out
    }

    pub fn is_negative(&self) -> bool {
        S && common::get_sign_bit(self.data[N-1])
    }

    fn cmp_raw(&self, rhs: &Self) -> Ordering {
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

impl<const N: usize> IntStatic<{N}, true> {
    pub fn neg_self(&mut self) {
        self.neg_self_priv();
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
            let lhs_neg = self.is_negative();
            let rhs_neg = rhs.is_negative();
            if lhs_neg {
                if rhs_neg {
                    self.cmp_raw(rhs).reverse()
                } else {
                    Ordering::Less
                }
            } else {
                if rhs_neg {
                    Ordering::Greater
                } else {
                    self.cmp_raw(rhs)
                }
            }
        } else {
            self.cmp_raw(rhs)
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
        out.not_self();
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

impl<const N: usize, const S: bool> Add<u64> for IntStatic<{N}, {S}> {
    type Output = Self;

    fn add(self, rhs: u64) -> Self {
        let mut out = self;
        out += rhs;
        out
    }
}

impl<const N: usize, const S: bool> AddAssign<u64> for IntStatic<{N}, {S}> {
    fn add_assign(&mut self, rhs: u64) {
        let mut overflow = rhs;
        for i in 0..N {
            (self.data[i], overflow) = common::add_out_overflow(self.data[i], overflow);
        }
    }
}

impl<const N: usize, const S: bool> Add for IntStatic<{N}, {S}> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        &self + &rhs
    }
}

impl<const N: usize, const S: bool> Add for &IntStatic<{N}, {S}> {
    type Output = IntStatic<{N}, {S}>;

    fn add(self, rhs: Self) -> Self::Output {
        let mut out = self.clone();
        out += rhs;
        out
    }
}

impl<const N: usize, const S: bool> AddAssign for IntStatic<{N}, {S}> {
    fn add_assign(&mut self, rhs: Self) {
        *self += &rhs;
    }
}

impl<const N: usize, const S: bool> AddAssign<&Self> for IntStatic<{N}, {S}> {
    fn add_assign(&mut self, rhs: &Self) {
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
        // FIXME: probably incorrect for negative numbers
        // TODO: make some tests
        let negative = self.is_negative();
        if negative { self.neg_self_priv() }
        let rhs = rhs as u64;
        let mut rem = 0;
        for i in (0..N).rev() {
            (self.data[i], rem) = common::div_inout_rem(self.data[i], rhs, rem);
        }
        if negative { self.neg_self_priv() }
    }
}

impl<const N: usize, const S: bool> Rem<u32> for IntStatic<{N}, {S}> {
    type Output = u32;

    fn rem(self, rhs: u32) -> Self::Output {
        // TODO: make some tests
        // FIXME: probably incorrect for negative numbers
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
        // FIXME: probably incorrect for negative numbers
        if rhs == Self::zero() {
            panic!("attempt to divide by zero");
        }

        const U64_BITS_COUNT: usize = mem::size_of::<u64>()*8;

        let mut out = Self::zero();
        let mut lhs_temp = self;
        let mut rhs_temp = rhs;

        let rhs_non_zero = rhs_temp.largest_non_zero_index();
        let rhs_max_bit = common::get_max_bit(rhs_temp.data[rhs_non_zero]);
        let lhs_non_zero = lhs_temp.largest_non_zero_index();
        let lhs_max_bit = common::get_max_bit(lhs_temp.data[lhs_non_zero]);
        let mut rhs_shift = (lhs_non_zero - rhs_non_zero) * U64_BITS_COUNT + lhs_max_bit - rhs_max_bit;
        while lhs_temp > rhs {
            let lhs_non_zero = lhs_temp.largest_non_zero_index();
            let lhs_max_bit = common::get_max_bit(lhs_temp.data[lhs_non_zero]);
            let mut new_rhs_shift = (lhs_non_zero - rhs_non_zero) * U64_BITS_COUNT + lhs_max_bit - rhs_max_bit;

            rhs_temp >>= rhs_shift - new_rhs_shift;

            if lhs_temp < rhs_temp {
                // rhs_shift should be > 0
                new_rhs_shift -= 1;
                rhs_temp >>= 1;
            }
            lhs_temp -= rhs_temp;
            // now somehow shift the prev bit in out.data, probably by rhs_shift - new_rhs_shift
            let shift_diff = rhs_shift - new_rhs_shift;
            out <<= shift_diff;
            out.data[0] += 1;
            rhs_shift = new_rhs_shift;
        }
        // remainder is whats left in lhs_temp
        out
    }
}

impl<const N: usize, const S: bool> DivAssign for IntStatic<{N}, {S}> {
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs;
    }
}

impl<const N: usize> Neg for IntStatic<{N}, true> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        let mut out = self;
        out.neg_self();
        out
    }
}

impl<const N: usize, const S: bool> Sub for IntStatic<{N}, {S}> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        let mut out = self;
        out -= rhs;
        out
    }
}

impl<const N: usize, const S: bool> SubAssign for IntStatic<{N}, {S}> {
    fn sub_assign(&mut self, rhs: Self) {
        *self += rhs.neg_priv();
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
    fn zero() {
        let data: [u64; 3] = [0; 3];
        let num = u_s::<3>::zero();
        assert_eq!(*num.get_data(), data);
    }

    #[test]
    fn from_data() {
        let data: [u64; 4] = [1, 2, 3, 4];
        let num = u_s::<4>::from_data(data);
        assert_eq!(*num.get_data(), data);
    }

    mod from_hex {
        use super::*;

        #[test]
        fn u_s1_empty_string() {
            assert_eq!(u_s::<1>::from_hex("").unwrap(), u_s::<1>::zero());
        }
        #[test]
        fn u_s2_empty_string() {
            assert_eq!(u_s::<2>::from_hex("").unwrap(), u_s::<2>::zero());
        }
        #[test]
        fn u_s1_zero() {
            assert_eq!(u_s::<1>::from_hex("0").unwrap(), u_s::<1>::zero());
        }
        #[test]
        fn i_s1_zero() {
            assert_eq!(i_s::<1>::from_hex("0").unwrap(), i_s::<1>::zero());
        }
        #[test]
        fn u_s2_zero() {
            assert_eq!(u_s::<2>::from_hex("0").unwrap(), u_s::<2>::zero());
        }
        #[test]
        fn i_s2_zero() {
            assert_eq!(i_s::<2>::from_hex("0").unwrap(), i_s::<2>::zero());
        }

        #[test]
        fn u_s1_invalid_char() {
            assert_eq!(u_s::<1>::from_hex("!k2j0").unwrap_err(), String::from("invalid hexadecimal character"));
        }
        #[test]
        fn u_s2_invalid_char() {
            assert_eq!(u_s::<2>::from_hex("!k2j0").unwrap_err(), String::from("invalid hexadecimal character"));
        }

        #[test]
        fn u_s1_input_fit_tight() {
            assert_eq!(u_s::<1>::from_hex("0000000000000000").unwrap(), u_s::<1>::zero());
        }
        #[test]
        fn u_s1_input_too_big() {
            assert_eq!(u_s::<1>::from_hex("00000000000000000").unwrap_err(), String::from("input number string is too big to fit in the provided buffer"));
        }

        #[test]
        #[allow(non_snake_case)]
        fn u_s1_FFFFFFFFFFFFFFFF() {
            assert_eq!(u_s::<1>::from_hex("FFFFFFFFFFFFFFFF").unwrap(), u_s::<1>::from_num(u64::MAX));
        }
        #[test]
        #[allow(non_snake_case)]
        fn u_s1_FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF() {
            assert_eq!(u_s::<2>::from_hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF").unwrap(), u_s::<2>::from_data([u64::MAX, u64::MAX]));
        }
        
        #[test]
        fn u_s1_ffffffffffffffff() {
            assert_eq!(u_s::<1>::from_hex("ffffffffffffffff").unwrap(), u_s::<1>::from_num(u64::MAX));
        }
        #[test]
        fn u_s1_ffffffffffffffffffffffffffffffff() {
            assert_eq!(u_s::<2>::from_hex("ffffffffffffffffffffffffffffffff").unwrap(), u_s::<2>::from_data([u64::MAX, u64::MAX]));
        }

        #[test]
        fn u_s1_fdb97531() {
            assert_eq!(u_s::<1>::from_hex("fdb97531").unwrap(), u_s::<1>::from_num(0xfdb97531u64));
        }
        #[test]
        fn u_s1_fdb97531fedcba9876543210() {
            assert_eq!(u_s::<2>::from_hex("fdb97531fedcba9876543210").unwrap(), u_s::<2>::from_data([0xfedcba9876543210u64, 0xfdb97531u64]));
        }

        #[test]
        fn u_s1_fedcba9876543210() {
            assert_eq!(u_s::<1>::from_hex("fedcba9876543210").unwrap(), u_s::<1>::from_num(0xfedcba9876543210u64));
        }
        #[test]
        fn u_s1_fedcba9876543210fedcba9876543210() {
            assert_eq!(u_s::<2>::from_hex("fedcba9876543210fedcba9876543210").unwrap(), u_s::<2>::from_data([0xfedcba9876543210u64, 0xfedcba9876543210u64]));
        }
        #[test]
        #[allow(non_snake_case)]
        fn u_s1_FEDCBA9876543210() {
            assert_eq!(u_s::<1>::from_hex("FEDCBA9876543210").unwrap(), u_s::<1>::from_num(0xFEDCBA9876543210u64));
        }
        #[test]
        #[allow(non_snake_case)]
        fn u_s1_FEDCBA9876543210FEDCBA9876543210() {
            assert_eq!(u_s::<2>::from_hex("FEDCBA9876543210FEDCBA9876543210").unwrap(), u_s::<2>::from_data([0xFEDCBA9876543210u64, 0xFEDCBA9876543210u64]));
        }
        
        #[test]
        #[allow(non_snake_case)]
        fn u_s1_ABCDEFabcdefAaBb() {
            assert_eq!(u_s::<1>::from_hex("ABCDEFabcdefAaBb").unwrap(), u_s::<1>::from_num(0xABCDEFabcdefAaBbu64));
        }
    }

    mod add {
        use super::*;

        #[test]
        fn u_s2_1_max() {
            let a = u_s::<2>::one();
            let b = u_s::<2>::max();
            assert_eq!(a + b, u_s::<2>::zero());
        }

        #[test]
        fn u_s4_1_max() {
            let a = u_s::<4>::one();
            let b = u_s::<4>::max();
            assert_eq!(a + b, u_s::<4>::zero());
        }

        #[test]
        fn u_s2_max_max() {
            let a = u_s::<2>::max();
            let b = u_s::<2>::max();
            assert_eq!(a + b, u_s::<2>::from_hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE").unwrap());
        }

        #[test]
        fn u_s2_1_half_max_m1() {
            let a = u_s::<2>::one();
            let b = u_s::<2>::from_data([u64::MAX, 0]);
            assert_eq!(a + b, u_s::<2>::from_data([0, 1]));
        }

        #[test]
        fn u_s4_1_nearly_max() {
            let a = u_s::<4>::one();
            let b = u_s::<4>::from_data([u64::MAX, u64::MAX, u64::MAX, u64::MAX >> 1]);
            assert_eq!(a + b, u_s::<4>::from_data([0, 0, 0, 1 << 63]));
        }

        #[test]
        fn i_s2_1_m1() {
            let a = i_s::<2>::one();
            let b = -i_s::<2>::one();
            assert_eq!(a + b, i_s::<2>::zero());
        }

        #[test]
        fn i_s4_pos_max_mpos_max() {
            let a = i_s::<4>::from_data([u64::MAX, u64::MAX, u64::MAX, u64::MAX >> 1]);
            let b = -a;
            assert_eq!(a + b, i_s::<4>::zero());
        }

        #[test]
        fn i_s4_pos_half_max_m1() {
            let a = i_s::<4>::from_data([0, 0, 0, 1 << 63]);
            let b = -i_s::<4>::one();
            assert_eq!(a + b, i_s::<4>::from_data([u64::MAX, u64::MAX, u64::MAX, u64::MAX >> 1]));
        }
    }

    mod mul {
        use super::*;

        #[test]
        fn u_s2_1_max() {
            let a = u_s::<2>::one();
            let b = u_s::<2>::max();
            assert_eq!(a * b, u_s::<2>::max());
        }

        #[test]
        fn u_s2_max_1() {
            let a = u_s::<2>::max();
            let b = u_s::<2>::one();
            assert_eq!(a * b, u_s::<2>::max());
        }

        #[test]
        fn u_s2_1_0() {
            let a = u_s::<2>::one();
            let b = u_s::<2>::zero();
            assert_eq!(a * b, u_s::<2>::zero());
        }

        #[test]
        fn u_s2_max_0() {
            let a = u_s::<2>::max();
            let b = u_s::<2>::zero();
            assert_eq!(a * b, u_s::<2>::zero());
        }

        #[test]
        fn u_s2_0_max() {
            let a = u_s::<2>::zero();
            let b = u_s::<2>::max();
            assert_eq!(a * b, u_s::<2>::zero());
        }

        #[test]
        fn u_s3_2_to_64_m1_2_to_64() {
            let a = u_s::<3>::from_data([u64::MAX, 0, 0]);
            let b = u_s::<3>::from_data([0, 1, 0]);
            assert_eq!(a * b, u_s::<3>::from_data([0, u64::MAX, 0]));
        }

        #[test]
        fn u_s4_2_to_128_m1_2_to_64() {
            let a = u_s::<4>::from_data([u64::MAX, u64::MAX, 0, 0]);
            let b = u_s::<4>::from_data([0, 1, 0, 0]);
            assert_eq!(a * b, u_s::<4>::from_data([0, u64::MAX, u64::MAX, 0]));
        }

        #[test]
        fn u_s4_2_to_128_m1_2_to_128_m1() {
            let a = u_s::<4>::from_data([u64::MAX, u64::MAX, 0, 0]);
            let b = u_s::<4>::from_data([u64::MAX, u64::MAX, 0, 0]);
            assert_eq!(a * b, u_s::<4>::from_data([1, 0, u64::MAX - 1, u64::MAX]));
        }

        #[test]
        fn i_s4_1_m1() {
            let a = i_s::<4>::one();
            let b = -i_s::<4>::one();
            assert_eq!(a * b, -i_s::<4>::one());
        }

        #[test]
        fn i_s4_m1_max() {
            let a = -i_s::<4>::one();
            let b = i_s::<4>::max();
            assert_eq!(a * b, -i_s::<4>::max());
        }
        
        #[test]
        fn i_s4_1_mmax() {
            let a = i_s::<4>::one();
            let b = -i_s::<4>::max();
            assert_eq!(a * b, -i_s::<4>::max());
        }

        #[test]
        fn i_s4_m1_m1() {
            let a = -i_s::<4>::one();
            let b = -i_s::<4>::one();
            assert_eq!(a * b, i_s::<4>::one());
        }

        #[test]
        fn i_s4_m1_mmax() {
            let a = -i_s::<4>::one();
            let b = -i_s::<4>::max();
            assert_eq!(a * b, i_s::<4>::max());
        }

        #[test]
        fn i_s4_mmax_m1() {
            let a = -i_s::<4>::max();
            let b = -i_s::<4>::one();
            assert_eq!(a * b, i_s::<4>::max());
        }

        #[test]
        fn i_s4_0_m1() {
            let a = i_s::<4>::zero();
            let b = -i_s::<4>::one();
            assert_eq!(a * b, i_s::<4>::zero());
        }
        
        #[test]
        fn i_s4_m2_to_128_m1_m2_to_128_m1() {
            let a = -i_s::<4>::from_data([u64::MAX, u64::MAX, 0, 0]);
            let b = -i_s::<4>::from_data([u64::MAX, u64::MAX, 0, 0]);
            assert_eq!(a * b, i_s::<4>::from_data([1, 0, u64::MAX - 1, u64::MAX]));
        }

        #[test]
        fn i_s4_m2_to_128_m1_2_to_128_m1() {
            let a = -i_s::<4>::from_data([u64::MAX, u64::MAX, 0, 0]);
            let b = i_s::<4>::from_data([u64::MAX, u64::MAX, 0, 0]);
            assert_eq!(a * b, -i_s::<4>::from_data([1, 0, u64::MAX - 1, u64::MAX]));
        }

        #[test]
        fn i_s4_2_to_128_m1_m2_to_128_m1() {
            let a = i_s::<4>::from_data([u64::MAX, u64::MAX, 0, 0]);
            let b = -i_s::<4>::from_data([u64::MAX, u64::MAX, 0, 0]);
            assert_eq!(a * b, -i_s::<4>::from_data([1, 0, u64::MAX - 1, u64::MAX]));
        }
    }

    mod div_u32 {
        use super::*;

        #[test]
        fn u_s2_32_bits_in_half_max() {
            let a = u_s::<2>::from_data([u64::MAX << 48, u64::MAX >> 48]);
            let b = u32::MAX;
            assert_eq!(a / b, u_s::<2>::from_data([1 << 48, 0]));
        }

        #[test]
        fn i_s2_m32_bits_in_half_max() {
            let a = -i_s::<2>::from_data([u64::MAX << 48, u64::MAX >> 48]);
            let b = u32::MAX;
            assert_eq!(a / b, -i_s::<2>::from_data([1 << 48, 0]));
        }
    }

    mod div {
        use super::*;

        #[test]
        fn u_s2_32_bits_in_half_max() {
            let a = u_s::<2>::from_data([u64::MAX << 48, u64::MAX >> 48]);
            let b = u_s::<2>::from_data([u64::MAX >> 32, 0]);
            assert_eq!(a / b, u_s::<2>::from_data([1 << 48, 0]));
        }

        #[test]
        fn i_s2_m32_bits_in_half_max() {
            let a = -i_s::<2>::from_data([u64::MAX << 48, u64::MAX >> 48]);
            let b = i_s::<2>::from_data([u64::MAX >> 32, 0]);
            assert_eq!(a / b, -i_s::<2>::from_data([1 << 48, 0]));
        }
    }

    #[test]
    fn to_string() {
        let num = u_s::<4>::from_data([1, 2, 3, 4]);
        assert_eq!(num.to_string(), "1");
    }

    #[test]
    fn to_binary_string() {
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
    fn to_binary_string_u64() {
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
    fn to_lower_hex() {
        assert_eq!(format!("{:x}", u_s::<2>::from_data([1, u64::MAX])), "ffffffffffffffff0000000000000001");
        assert_eq!(format!("{:x}", u_s::<2>::from_data([3, 1])), "10000000000000003");
    }

    #[test]
    fn to_upper_hex() {
        assert_eq!(format!("{:X}", u_s::<2>::from_data([1, u64::MAX])), "FFFFFFFFFFFFFFFF0000000000000001");
        assert_eq!(format!("{:X}", u_s::<2>::from_data([3, 1])), "10000000000000003");
    }

    #[test]
    fn hex_string_u64() {
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
    fn cmp() {
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

    #[test]
    fn neg() {
        assert_eq!(-i_s::<2>::from_data([1, 2]), i_s::<2>::from_data([u64::MAX, !2]));
        assert_eq!(-i_s::<2>::from_data([u64::MAX, !2]), i_s::<2>::from_data([1, 2]));
    }

    #[test]
    fn neg_zero() {
        assert_eq!(-i_s::<2>::zero(), i_s::<2>::zero());
    }

    #[test]
    #[should_panic]
    fn div_by_zero_u32() {
        let _ = u_s::<2>::from_data([1, 2]) / 0;
    }

    #[test]
    #[should_panic]
    fn div_by_zero() {
        let _ = u_s::<2>::from_data([1, 2]) / u_s::<2>::from_data([0, 0]);
    }

}