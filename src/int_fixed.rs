use std::cmp::{Ord, Eq, PartialEq, PartialOrd, Ordering};
use std::fmt;
use std::mem;

// TODO:
// note: don't be scared of the amount of work, once I implement this once, the others will be easy
// comparison operators
// binary operators
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

// used before for int_fixed: #[allow(non_camel_case_types)]
#[derive(Debug)] // TODO: maybe implemet with Display, because normal numbers have it like that (I think)
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
        // FIXME: implement for signed
        for i in (0..self.data.len()).rev() {
            if self.data[i] < other.data[i] {
                return Ordering::Less;
            } else if self.data[i] < other.data[i] {
                return Ordering::Greater;
            }
        }
        return Ordering::Equal;
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


#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn int_fixed_zero() {
        let data: [u64; 3] = [0; 3];
        let num = IntFixed::<3, false>::zero();
        assert_eq!(*num.get_data(), data);
    }

    #[test]
    fn int_fixed_from_data() {
        let data: [u64; 4] = [1, 2, 3, 4];
        let num = IntFixed::<4, false>::from_data(data);
        assert_eq!(*num.get_data(), data);
    }

    #[test]
    fn int_fixed_to_string() {
        let num = IntFixed::<4, false>::from_data([1, 2, 3, 4]);
        assert_eq!(num.to_string(), "1");
    }

    #[test]
    fn int_fixed_to_binary_string() {
        assert_eq!(
            format!("{:b}", IntFixed::<2, false>::from_data([1, u64::MAX])),
            "11111111111111111111111111111111111111111111111111111111111111110000000000000000000000000000000000000000000000000000000000000001"
        );
        assert_eq!(
            format!("{:b}", IntFixed::<2, false>::from_data([3, 1])),
            "10000000000000000000000000000000000000000000000000000000000000011"
        );
    }

    #[test]
    fn int_fixed_to_binary_string_u64() {
        assert_eq!(
            format!("{:b}", IntFixed::<1, false>::from_num(1)),
            format!("{:b}", 1)
        );
        assert_eq!(
            format!("{:b}", IntFixed::<1, true>::from_num(1)),
            format!("{:b}", 1)
        );
        assert_eq!(
            format!("{:b}", IntFixed::<1, false>::from_num(165)),
            format!("{:b}", 165)
        );
        assert_eq!(
            format!("{:#b}", IntFixed::<1, false>::from_num(5)),
            format!("{:#b}", 5)
        );
        assert_eq!(
            format!("{:032b}", IntFixed::<1, false>::from_num(5)),
            format!("{:032b}", 5)
        );
        assert_eq!(
            format!("{:032b}", IntFixed::<1, false>::from_num(5)),
            format!("{:032b}", 5)
        );
        assert_eq!(
            format!("{:<5b}", IntFixed::<1, false>::from_num(2)),
            format!("{:<5b}", 2)
        );
        assert_eq!(
            format!("{:-<5b}", IntFixed::<1, false>::from_num(2)),
            format!("{:-<5b}", 2)
        );
        assert_eq!(
            format!("{:^5b}", IntFixed::<1, false>::from_num(2)),
            format!("{:^5b}", 2)
        );
        assert_eq!(
            format!("{:>5b}", IntFixed::<1, false>::from_num(2)),
            format!("{:>5b}", 2)
        );
        assert_eq!(
            format!("{:b}", IntFixed::<1, false>::from_num(u64::MAX)),
            format!("{:b}", -1i64)
        );
        assert_eq!(
            format!("{:b}", IntFixed::<1, true>::from_num(u64::MAX)),
            format!("{:b}", -1i64)
        );
        assert_eq!(
            format!("{:b}", IntFixed::<1, false>::from_num(0)),
            format!("{:b}", 0)
        );
        assert_eq!(
            format!("{:b}", IntFixed::<1, true>::from_num(0)),
            format!("{:b}", 0)
        );
    }

    #[test]
    fn int_fixed_to_lower_hex() {
        assert_eq!(format!("{:x}", IntFixed::<2, false>::from_data([1, u64::MAX])), "ffffffffffffffff0000000000000001");
        assert_eq!(format!("{:x}", IntFixed::<2, false>::from_data([3, 1])), "10000000000000003");
    }

    #[test]
    fn int_fixed_to_upper_hex() {
        assert_eq!(format!("{:X}", IntFixed::<2, false>::from_data([1, u64::MAX])), "FFFFFFFFFFFFFFFF0000000000000001");
        assert_eq!(format!("{:X}", IntFixed::<2, false>::from_data([3, 1])), "10000000000000003");
    }

    #[test]
    fn int_fixed_to_hex_string_u64() {
        assert_eq!(
            format!("{:x}", IntFixed::<1, false>::from_num(1)),
            format!("{:x}", 1)
        );
        assert_eq!(
            format!("{:x}", IntFixed::<1, true>::from_num(1)),
            format!("{:x}", 1)
        );
        assert_eq!(
            format!("{:x}", IntFixed::<1, false>::from_num(165)),
            format!("{:x}", 165)
        );
        assert_eq!(
            format!("{:#x}", IntFixed::<1, false>::from_num(5)),
            format!("{:#x}", 5)
        );
        assert_eq!(
            format!("{:032x}", IntFixed::<1, false>::from_num(5)),
            format!("{:032x}", 5)
        );
        assert_eq!(
            format!("{:032x}", IntFixed::<1, false>::from_num(5)),
            format!("{:032x}", 5)
        );
        assert_eq!(
            format!("{:<5x}", IntFixed::<1, false>::from_num(2)),
            format!("{:<5x}", 2)
        );
        assert_eq!(
            format!("{:-<5x}", IntFixed::<1, false>::from_num(2)),
            format!("{:-<5x}", 2)
        );
        assert_eq!(
            format!("{:^5x}", IntFixed::<1, false>::from_num(2)),
            format!("{:^5x}", 2)
        );
        assert_eq!(
            format!("{:>5x}", IntFixed::<1, false>::from_num(2)),
            format!("{:>5x}", 2)
        );
        assert_eq!(
            format!("{:x}", IntFixed::<1, false>::from_num(u64::MAX)),
            format!("{:x}", -1i64)
        );
        assert_eq!(
            format!("{:x}", IntFixed::<1, true>::from_num(u64::MAX)),
            format!("{:x}", -1i64)
        );
        assert_eq!(
            format!("{:x}", IntFixed::<1, false>::from_num(0)),
            format!("{:x}", 0)
        );
        assert_eq!(
            format!("{:x}", IntFixed::<1, true>::from_num(0)),
            format!("{:x}", 0)
        );
    }
}