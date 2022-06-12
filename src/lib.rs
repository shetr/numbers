use std::cmp;
use std::fmt;
use std::mem;

#[allow(non_camel_case_types)]
#[derive(Debug)] // TODO: maybe implemet with Display, because normal numbers have it like that (I think)
pub struct int_fixed<const N: usize, const S: bool>
{
    data: [u64; N]
}

impl<const N: usize, const S: bool> int_fixed<{N}, {S}> {

    // TODO: constructor from number literal of bigger size than 64bit

    pub fn zero() -> Self {
        int_fixed::bit_min()
    }

    pub fn one() -> Self {
        int_fixed::from_num(1)
    }

    pub fn bit_min() -> Self {
        int_fixed::filled(0)
    }

    pub fn bit_max() -> Self {
        int_fixed::filled(u64::MAX)
    }

    pub fn min() -> Self {
        if S {
            let mut data: [u64; N] = [0; N];
            data[data.len()-1] = 1 << (mem::size_of::<u64>()*8 - 1);
            int_fixed { data }
        } else {
            int_fixed::bit_min()
        }
    }

    pub fn max() -> Self {
        if S {
            let mut data: [u64; N] = [u64::MAX; N];
            data[data.len()-1] = !(1 << (mem::size_of::<u64>()*8 - 1));
            int_fixed { data }
        } else {
            int_fixed::bit_max()
        }
    }

    pub fn from_num(num: u64) -> Self {
        let mut data: [u64; N] = [0; N];
        data[0] = num;
        int_fixed { data }
    }

    pub fn filled(num: u64) -> Self {
        let data: [u64; N] = [num; N];
        int_fixed { data }
    }

    pub fn from_data(data: [u64; N]) -> Self {
        int_fixed { data }
    }

    pub fn get_data(&self) -> &[u64; N] {
        &self.data
    }

    pub fn get_data_mut(&mut self) -> &mut [u64; N] {
        &mut self.data
    }
}

impl<const N: usize, const S: bool> fmt::Display for int_fixed<{N}, {S}> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // TODO: real implementation with division + test
        write!(f, "{}", self.data[0])
    }
}

impl<const N: usize, const S: bool> fmt::Binary for int_fixed<{N}, {S}> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let chunk_size = mem::size_of::<u64>()*8;
        let mut bin = String::with_capacity(cmp::max(N*chunk_size, f.width().unwrap_or(0)));
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
        let is_nonnegative = if S { false } else { true }; // FIXME: change false to *self >= 0
        f.pad_integral(is_nonnegative, "0b", &bin)
    }
}

impl<const N: usize, const S: bool> fmt::LowerHex for int_fixed<{N}, {S}> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let chunk_size = mem::size_of::<u64>()*2;
        let mut hex = String::with_capacity(N*chunk_size);
        for chunk in self.data.iter().rev() {
            hex.push_str(&format!("{:x}", chunk));
        }
        // TODO: implement + test
        write!(f, "{}", hex)
    }
}

impl<const N: usize, const S: bool> fmt::UpperHex for int_fixed<{N}, {S}> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut hex = String::with_capacity(N*mem::size_of::<u64>()*2);
        // TODO: implement + test
        write!(f, "{}", hex)
    }
}

impl<const N: usize, const S: bool> fmt::LowerExp for int_fixed<{N}, {S}> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // TODO: implement + test
        write!(f, "{}", "")
    }
}

impl<const N: usize, const S: bool> fmt::UpperExp for int_fixed<{N}, {S}> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // TODO: implement + test
        write!(f, "{}", "")
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn int_fixed_zero() {
        let data: [u64; 3] = [0; 3];
        let num = int_fixed::<3, false>::zero();
        assert_eq!(*num.get_data(), data);
    }

    #[test]
    fn int_fixed_from_data() {
        let data: [u64; 4] = [1, 2, 3, 4];
        let num = int_fixed::<4, false>::from_data(data);
        assert_eq!(*num.get_data(), data);
    }

    #[test]
    fn int_fixed_to_string() {
        let num = int_fixed::<4, false>::from_data([1, 2, 3, 4]);
        assert_eq!(num.to_string(), "1");
    }

    #[test]
    fn int_fixed_to_binary_string() {
        assert_eq!(
            format!("{:b}", int_fixed::<2, false>::from_data([1, u64::MAX])),
            "11111111111111111111111111111111111111111111111111111111111111110000000000000000000000000000000000000000000000000000000000000001"
        );
        assert_eq!(
            format!("{:b}", int_fixed::<2, false>::from_data([3, 1])),
            "10000000000000000000000000000000000000000000000000000000000000011"
        );
    }

    #[test]
    fn int_fixed_to_binary_string_u64() {
        assert_eq!(
            format!("{:b}", int_fixed::<1, false>::from_num(1)),
            format!("{:b}", 1)
        );
        assert_eq!(
            format!("{:b}", int_fixed::<1, false>::from_num(165)),
            format!("{:b}", 165)
        );
        assert_eq!(
            format!("{:#b}", int_fixed::<1, false>::from_num(5)),
            format!("{:#b}", 5)
        );
        assert_eq!(
            format!("{:032b}", int_fixed::<1, false>::from_num(5)),
            format!("{:032b}", 5)
        );
        assert_eq!(
            format!("{:032b}", int_fixed::<1, false>::from_num(5)),
            format!("{:032b}", 5)
        );
        assert_eq!(
            format!("{:<5b}", int_fixed::<1, false>::from_num(2)),
            format!("{:<5b}", 2)
        );
        assert_eq!(
            format!("{:-<5b}", int_fixed::<1, false>::from_num(2)),
            format!("{:-<5b}", 2)
        );
        assert_eq!(
            format!("{:^5b}", int_fixed::<1, false>::from_num(2)),
            format!("{:^5b}", 2)
        );
        assert_eq!(
            format!("{:>5b}", int_fixed::<1, false>::from_num(2)),
            format!("{:>5b}", 2)
        );
    }

    #[test]
    fn int_fixed_to_lower_hex() {
        let num = int_fixed::<2, false>::from_data([1, u64::MAX]);
        assert_eq!(
            format!("{:x}", num),
            ""
        );
    }

    #[test]
    fn int_fixed_to_upper_hex() {
        let num = int_fixed::<2, false>::from_data([1, u64::MAX]);
        assert_eq!(
            format!("{:X}", num),
            ""
        );
    }
}