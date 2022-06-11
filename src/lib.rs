
#[allow(non_camel_case_types)]
pub struct int_fixed<const N: usize, const S: bool>
{
    data: [u64; N]
}

impl<const N: usize, const S: bool> int_fixed<{N}, {S}> {
    pub fn from_data(data: [u64; N]) -> Self {
        int_fixed { data }
    }

    pub fn get_data(&self) -> &[u64; N] {
        &self.data
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn from_data_test() {
        let data: [u64; 4] = [1, 2, 3, 4];
        let i: int_fixed<4, false> = int_fixed::from_data(data);
        assert_eq!(*i.get_data(), data);
    }
}