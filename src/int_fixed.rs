use crate::common;

use std::cmp::{Ord, Eq, PartialEq, PartialOrd, Ordering};
use std::fmt;
use std::mem;
use std::ops::*;


// TODO:
// note: don't be scared of the amount of work, once I implement this once, the others will be easy, just a lot of refactor
// comparison operators
// binary operators
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
// create general number traits and use one of them for type of data inside IntFixed
// write documentation
// cover everything with unit tests
// lower/upper exp fmt
// when killing time: octal fmt
// maybe do wrapping/saturating variant

#[derive(Debug, Copy, Clone)] // TODO: maybe implemet with Display, because normal numbers have it like that (I think)
pub struct IntFixed<const N: usize, const S: bool>
{
    data: [u64; N]
}

impl<const N: usize, const S: bool> IntFixed<{N}, {S}> {

    pub fn zero() -> Self {
        IntFixed::bit_min()
    }

    pub fn one() -> Self {
        IntFixed::from_num(1)
    }

    pub fn bit_min() -> Self {
        IntFixed::filled(0)
    }

    pub fn bit_max() -> Self {
        IntFixed::filled(u64::MAX)
    }

    pub fn min() -> Self {
        if S {
            let mut data: [u64; N] = [0; N];
            data[data.len()-1] = 1 << (mem::size_of::<u64>()*8 - 1);
            IntFixed { data }
        } else {
            IntFixed::bit_min()
        }
    }

    pub fn max() -> Self {
        if S {
            let mut data: [u64; N] = [u64::MAX; N];
            data[data.len()-1] = !(1 << (mem::size_of::<u64>()*8 - 1));
            IntFixed { data }
        } else {
            IntFixed::bit_max()
        }
    }

    pub fn from_num(num: u64) -> Self {
        let mut data: [u64; N] = [0; N];
        data[0] = num;
        IntFixed { data }
    }

    pub fn filled(num: u64) -> Self {
        let data: [u64; N] = [num; N];
        IntFixed { data }
    }

    pub fn from_data(data: [u64; N]) -> Self {
        IntFixed { data }
    }

    pub fn get_data(&self) -> &[u64; N] {
        &self.data
    }

    pub fn get_data_mut(&mut self) -> &mut [u64; N] {
        &mut self.data
    }

    fn to_hex(&self) -> String {
        // TODO: abstract the implementation away
        let bit_size = mem::size_of::<u64>()*8;
        let chunk_size = mem::size_of::<u64>()*2;
        let mut hex = String::with_capacity(N*chunk_size);
        let mut only_zeros = true;
        for chunk in self.data.iter().rev() {
            let mut bit_mask: u64 = 0xF << (bit_size - 4);
            for i in (0..chunk_size).rev() {
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
}

impl<const N: usize, const S: bool> fmt::Display for IntFixed<{N}, {S}> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // TODO: real implementation with division + test
        write!(f, "{}", self.data[0])
    }
}

impl<const N: usize, const S: bool> fmt::Binary for IntFixed<{N}, {S}> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // TODO: abstract the implementation away
        let chunk_size = mem::size_of::<u64>()*8;
        let mut bin = String::with_capacity(N*chunk_size);
        let mut only_zeros = true;
        for chunk in self.data.iter().rev() {
            let mut bit_mask: u64 = 1 << (chunk_size - 1);
            for _ in (0..chunk_size).rev() {
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
        f.pad_integral(true, "0b", &bin)
    }
}

impl<const N: usize, const S: bool> fmt::LowerHex for IntFixed<{N}, {S}> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.pad_integral(true, "0x", &self.to_hex())
    }
}

impl<const N: usize, const S: bool> fmt::UpperHex for IntFixed<{N}, {S}> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.pad_integral(true, "0x", &self.to_hex().to_uppercase())
    }
}

impl<const N: usize, const S: bool> fmt::LowerExp for IntFixed<{N}, {S}> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // TODO: implement + test, needs similar implementation as fmt::Display
        write!(f, "{}", "")
    }
}

impl<const N: usize, const S: bool> fmt::UpperExp for IntFixed<{N}, {S}> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // TODO: implement + test, use fmt::LowerExp
        write!(f, "{}", "")
    }
}

impl<const N: usize, const S: bool> Ord for IntFixed<{N}, {S}> {
    fn cmp(&self, other: &Self) -> Ordering {
        if S {
            // FIXME: implement for signed
            return Ordering::Equal;
        } else {
            for i in (0..self.data.len()).rev() {
                if self.data[i] < other.data[i] {
                    return Ordering::Less;
                } else if self.data[i] > other.data[i] {
                    return Ordering::Greater;
                }
            }
            return Ordering::Equal;
        }
    }
}

impl<const N: usize, const S: bool> Eq for IntFixed<{N}, {S}> {}

impl<const N: usize, const S: bool> PartialOrd for IntFixed<{N}, {S}> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<const N: usize, const S: bool> PartialEq for IntFixed<{N}, {S}> {
    fn eq(&self, other: &Self) -> bool {
        for i in (0..self.data.len()).rev() {
            if self.data[i] != other.data[i] {
                return false;
            }
        }
        return true;
    }
}

impl<const N: usize, const S: bool> BitAnd for IntFixed<{N}, {S}> {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        let mut out = self;
        out &= rhs;
        out
    }
}

impl<const N: usize, const S: bool> BitAndAssign for IntFixed<{N}, {S}> {
    fn bitand_assign(&mut self, rhs: Self) {
        for i in 0..N {
            self.data[i] &= rhs.data[i];
        }
    }
}

impl<const N: usize, const S: bool> BitOr for IntFixed<{N}, {S}> {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        let mut out = self;
        out |= rhs;
        out
    }
}

impl<const N: usize, const S: bool> BitOrAssign for IntFixed<{N}, {S}> {
    fn bitor_assign(&mut self, rhs: Self) {
        for i in 0..N {
            self.data[i] |= rhs.data[i];
        }
    }
}

impl<const N: usize, const S: bool> BitXor for IntFixed<{N}, {S}> {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        let mut out = self;
        out ^= rhs;
        out
    }
}

impl<const N: usize, const S: bool> BitXorAssign for IntFixed<{N}, {S}> {
    fn bitxor_assign(&mut self, rhs: Self) {
        for i in 0..N {
            self.data[i] ^= rhs.data[i];
        }
    }
}

impl<const N: usize, const S: bool> Not for IntFixed<{N}, {S}> {
    type Output = Self;

    fn not(self) -> Self::Output {
        let mut out = self;
        for i in 0..N {
            out.data[i] = !out.data[i];
        }
        out
    }
}

// TODO: replace usize with generic unsigned int
impl<const N: usize, const S: bool> Shl<usize> for IntFixed<{N}, {S}> {
    type Output = Self;

    fn shl(self, rhs: usize) -> Self::Output {
        let mut out = self;
        out <<= rhs;
        out
    }
}

// TODO: replace usize with generic unsigned int, move implementation to some common place
impl<const N: usize, const S: bool> ShlAssign<usize> for IntFixed<{N}, {S}> {
    fn shl_assign(&mut self, rhs: usize) {
        let block_bits = mem::size_of::<u64>()*8;
        let block_shift = rhs / block_bits;
        let local_shift = rhs - block_shift * block_bits;
        for i in (0..N).rev() {
            let left_part_idx = i as isize - block_shift as isize;
            let right_part_idx = left_part_idx - 1;
            let left_part = if left_part_idx >= 0 { self.data[left_part_idx as usize] << local_shift } else { 0u64 };
            let right_part = if right_part_idx >= 0 { self.data[right_part_idx as usize] >> (block_bits - local_shift) } else { 0u64 };
            self.data[i] = left_part & right_part;
        }
    }
}

// TODO: replace usize with generic unsigned int
impl<const N: usize, const S: bool> Shr<usize> for IntFixed<{N}, {S}> {
    type Output = Self;

    fn shr(self, rhs: usize) -> Self::Output {
        let mut out = self;
        out >>= rhs;
        out
    }
}

// TODO: replace usize with generic unsigned int
// move implementation to some common place, or maybe << and >> can be generalized with same function (inversing index order)
impl<const N: usize, const S: bool> ShrAssign<usize> for IntFixed<{N}, {S}> {
    fn shr_assign(&mut self, rhs: usize) {
        let block_bits = mem::size_of::<u64>()*8;
        let block_shift = rhs / block_bits;
        let local_shift = rhs - block_shift * block_bits;
        for i in 0..N {
            let right_part_idx = i + block_shift;
            let left_part_idx = right_part_idx + 1;
            let right_part = if right_part_idx < N { self.data[right_part_idx] >> local_shift } else { 0u64 };
            let left_part = if left_part_idx < N { self.data[left_part_idx] << (block_bits - local_shift) } else { 0u64 };
            self.data[i] = left_part & right_part;
        }
    }
}

impl<const N: usize, const S: bool> Add for IntFixed<{N}, {S}> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        let mut out = self;
        out += other;
        out
    }
}

impl<const N: usize, const S: bool> AddAssign for IntFixed<{N}, {S}> {
    fn add_assign(&mut self, other: Self) {
        let mut overflow = 0u64;
        let half_bits = mem::size_of::<u64>()*4;
        let right_mask = u64::MAX >> half_bits;
        for i in 0..N {
            let a = self.data[i];
            let b = other.data[i];
            let right_sum = overflow + a & right_mask + b & right_mask;
            let right_overflow = right_sum >> half_bits;
            let left_sum = right_overflow + (a >> half_bits) + (b >> half_bits);
            self.data[i] = (left_sum << half_bits) + right_sum & right_mask;
            overflow = left_sum >> half_bits;
        }
    }
}

// replace with u_f and i_f
#[allow(non_camel_case_types)]
pub type u_fixed<const N: usize> = IntFixed<N, false>;
#[allow(non_camel_case_types)]
pub type i_fixed<const N: usize> = IntFixed<N, true>;

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn int_fixed_zero() {
        let data: [u64; 3] = [0; 3];
        let num = u_fixed::<3>::zero();
        assert_eq!(*num.get_data(), data);
    }

    #[test]
    fn int_fixed_from_data() {
        let data: [u64; 4] = [1, 2, 3, 4];
        let num = u_fixed::<4>::from_data(data);
        assert_eq!(*num.get_data(), data);
    }

    #[test]
    fn int_fixed_to_string() {
        let num = u_fixed::<4>::from_data([1, 2, 3, 4]);
        assert_eq!(num.to_string(), "1");
    }

    #[test]
    fn int_fixed_to_binary_string() {
        assert_eq!(
            format!("{:b}", u_fixed::<2>::from_data([1, u64::MAX])),
            "11111111111111111111111111111111111111111111111111111111111111110000000000000000000000000000000000000000000000000000000000000001"
        );
        assert_eq!(
            format!("{:b}", u_fixed::<2>::from_data([3, 1])),
            "10000000000000000000000000000000000000000000000000000000000000011"
        );
    }

    #[test]
    fn int_fixed_to_binary_string_u64() {
        assert_eq!(
            format!("{:b}", u_fixed::<1>::from_num(1)),
            format!("{:b}", 1)
        );
        assert_eq!(
            format!("{:b}", i_fixed::<1>::from_num(1)),
            format!("{:b}", 1)
        );
        assert_eq!(
            format!("{:b}", u_fixed::<1>::from_num(165)),
            format!("{:b}", 165)
        );
        assert_eq!(
            format!("{:#b}", u_fixed::<1>::from_num(5)),
            format!("{:#b}", 5)
        );
        assert_eq!(
            format!("{:032b}", u_fixed::<1>::from_num(5)),
            format!("{:032b}", 5)
        );
        assert_eq!(
            format!("{:032b}", u_fixed::<1>::from_num(5)),
            format!("{:032b}", 5)
        );
        assert_eq!(
            format!("{:<5b}", u_fixed::<1>::from_num(2)),
            format!("{:<5b}", 2)
        );
        assert_eq!(
            format!("{:-<5b}", u_fixed::<1>::from_num(2)),
            format!("{:-<5b}", 2)
        );
        assert_eq!(
            format!("{:^5b}", u_fixed::<1>::from_num(2)),
            format!("{:^5b}", 2)
        );
        assert_eq!(
            format!("{:>5b}", u_fixed::<1>::from_num(2)),
            format!("{:>5b}", 2)
        );
        assert_eq!(
            format!("{:b}", u_fixed::<1>::from_num(u64::MAX)),
            format!("{:b}", -1i64)
        );
        assert_eq!(
            format!("{:b}", i_fixed::<1>::from_num(u64::MAX)),
            format!("{:b}", -1i64)
        );
        assert_eq!(
            format!("{:b}", u_fixed::<1>::from_num(0)),
            format!("{:b}", 0)
        );
        assert_eq!(
            format!("{:b}", i_fixed::<1>::from_num(0)),
            format!("{:b}", 0)
        );
    }

    #[test]
    fn int_fixed_to_lower_hex() {
        assert_eq!(format!("{:x}", u_fixed::<2>::from_data([1, u64::MAX])), "ffffffffffffffff0000000000000001");
        assert_eq!(format!("{:x}", u_fixed::<2>::from_data([3, 1])), "10000000000000003");
    }

    #[test]
    fn int_fixed_to_upper_hex() {
        assert_eq!(format!("{:X}", u_fixed::<2>::from_data([1, u64::MAX])), "FFFFFFFFFFFFFFFF0000000000000001");
        assert_eq!(format!("{:X}", u_fixed::<2>::from_data([3, 1])), "10000000000000003");
    }

    #[test]
    fn int_fixed_to_hex_string_u64() {
        assert_eq!(
            format!("{:x}", u_fixed::<1>::from_num(1)),
            format!("{:x}", 1)
        );
        assert_eq!(
            format!("{:x}", i_fixed::<1>::from_num(1)),
            format!("{:x}", 1)
        );
        assert_eq!(
            format!("{:x}", u_fixed::<1>::from_num(165)),
            format!("{:x}", 165)
        );
        assert_eq!(
            format!("{:#x}", u_fixed::<1>::from_num(5)),
            format!("{:#x}", 5)
        );
        assert_eq!(
            format!("{:032x}", u_fixed::<1>::from_num(5)),
            format!("{:032x}", 5)
        );
        assert_eq!(
            format!("{:032x}", u_fixed::<1>::from_num(5)),
            format!("{:032x}", 5)
        );
        assert_eq!(
            format!("{:<5x}", u_fixed::<1>::from_num(2)),
            format!("{:<5x}", 2)
        );
        assert_eq!(
            format!("{:-<5x}", u_fixed::<1>::from_num(2)),
            format!("{:-<5x}", 2)
        );
        assert_eq!(
            format!("{:^5x}", u_fixed::<1>::from_num(2)),
            format!("{:^5x}", 2)
        );
        assert_eq!(
            format!("{:>5x}", u_fixed::<1>::from_num(2)),
            format!("{:>5x}", 2)
        );
        assert_eq!(
            format!("{:x}", u_fixed::<1>::from_num(u64::MAX)),
            format!("{:x}", -1i64)
        );
        assert_eq!(
            format!("{:x}", i_fixed::<1>::from_num(u64::MAX)),
            format!("{:x}", -1i64)
        );
        assert_eq!(
            format!("{:x}", u_fixed::<1>::from_num(0)),
            format!("{:x}", 0)
        );
        assert_eq!(
            format!("{:x}", i_fixed::<1>::from_num(0)),
            format!("{:x}", 0)
        );
    }

    #[test]
    fn int_fixed_cmp() {
        // TODO: write better tests, more understandable, only edge cases
        assert_eq!(u_fixed::<2>::from_data([1, 2]), u_fixed::<2>::from_data([1, 2]));
        assert_eq!(u_fixed::<3>::from_data([3, 0, 2]), u_fixed::<3>::from_data([3, 0, 2]));
        assert_ne!(u_fixed::<2>::from_data([1, 2]), u_fixed::<2>::from_data([2, 1]));
        assert_ne!(u_fixed::<3>::from_data([1, 0, 2]), u_fixed::<3>::from_data([1, 0, 1]));
        assert_eq!(u_fixed::<2>::from_data([1, 2]).cmp(&u_fixed::<2>::from_data([1, 2])), Ordering::Equal);
        assert_eq!(u_fixed::<3>::from_data([3, 0, 2]).cmp(&u_fixed::<3>::from_data([3, 0, 2])), Ordering::Equal);
        assert_eq!(u_fixed::<3>::from_data([0, 0, 0]).cmp(&u_fixed::<3>::from_data([1, 0, 0])), Ordering::Less);
        assert_eq!(u_fixed::<3>::from_data([0, 0, 0]).cmp(&u_fixed::<3>::from_data([0, 1, 0])), Ordering::Less);
        assert_eq!(u_fixed::<3>::from_data([1, 0, 0]).cmp(&u_fixed::<3>::from_data([0, 1, 0])), Ordering::Less);
        assert_eq!(u_fixed::<3>::from_data([1, 0, 0]).cmp(&u_fixed::<3>::from_data([0, 0, 1])), Ordering::Less);
        assert_eq!(u_fixed::<3>::from_data([1, 0, 1]).cmp(&u_fixed::<3>::from_data([0, 1, 1])), Ordering::Less);
        assert_eq!(u_fixed::<3>::from_data([1, 0, 1]).cmp(&u_fixed::<3>::from_data([2, 0, 1])), Ordering::Less);
        assert_eq!(u_fixed::<3>::from_data([2, 0, 1]).cmp(&u_fixed::<3>::from_data([1, 0, 1])), Ordering::Greater);
        assert_eq!(u_fixed::<3>::from_data([1, 0, 0]).cmp(&u_fixed::<3>::from_data([0, 0, 0])), Ordering::Greater);
        assert_eq!(u_fixed::<3>::from_data([0, 1, 0]).cmp(&u_fixed::<3>::from_data([0, 0, 0])), Ordering::Greater);
        assert_eq!(u_fixed::<3>::from_data([0, 1, 0]).cmp(&u_fixed::<3>::from_data([1, 0, 0])), Ordering::Greater);
        assert_eq!(u_fixed::<3>::from_data([0, 0, 1]).cmp(&u_fixed::<3>::from_data([1, 0, 0])), Ordering::Greater);
        assert_eq!(u_fixed::<3>::from_data([0, 1, 1]).cmp(&u_fixed::<3>::from_data([1, 0, 1])), Ordering::Greater);
        assert_eq!(u_fixed::<3>::from_data([2, 0, 1]).cmp(&u_fixed::<3>::from_data([1, 0, 1])), Ordering::Greater);
    }
}