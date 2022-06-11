use std::fmt;
use std::mem;

#[allow(non_camel_case_types)]
#[derive(Debug)]
pub struct int_fixed<const N: usize, const S: bool>
{
    data: [u64; N]
}

impl<const N: usize, const S: bool> int_fixed<{N}, {S}> {

    pub fn zero() -> Self {
        int_fixed { data: [0; N] }
    }

    pub fn from_data(data: [u64; N]) -> Self {
        int_fixed { data }
    }

    pub fn get_data(&self) -> &[u64; N] {
        &self.data
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
        let mut bin = String::with_capacity(N*chunk_size);
        for chunk in self.data.iter().rev() {
            let mut bit_mask: u64 = 1 << (chunk_size - 1);
            for _ in (0..chunk_size).rev() {
                bin.push(if chunk & bit_mask == 0 {'0'} else {'1'});
                bit_mask = bit_mask >> 1;
            }
        }
        write!(f, "{}", bin)
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