use std::convert::identity;

use bitvec::{bitbox, bitvec};
use bitvec::boxed::BitBox;
use bitvec::field::BitField;
use bitvec::index::{BitEnd, BitIdx};
use bitvec::macros::internal::funty::{Fundamental, Integral};
use bitvec::order::Lsb0;
use bitvec::prelude::BitStore;
use bitvec::vec::BitVec;

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Hamming {
    pub code: BitBox<u8>,
    n: u8,
    parity_n: u8,
    all_n: u8,
}

impl Hamming {
    pub fn new(n: u8) -> Self {
        let parity_n = Hamming::calculate_parity_n(n);
        let all_n = parity_n + n;
        Hamming {
            code: bitbox![u8, Lsb0; 0; all_n as usize],
            n,
            parity_n,
            all_n,
        }
    }

    pub fn from_buffer(buf: &[bool]) -> Self {
        let mut hamming = Hamming::new(buf.len() as u8);
        for (i, bit) in buf.iter().enumerate() {
            hamming.write(i as u8, *bit);
        }
        hamming
    }


    pub fn read_all(&self) -> BitBox<u8> {
        let mut bv = bitvec![u8, Lsb0; 0; self.n as usize];
        let mut j: usize = 0;
        for i in 1..=self.all_n {
            if !i.is_power_of_two() {
                bv.set(j, *self.code.get((i - 1) as usize).unwrap());
                j += 1;
            }
        }
        return BitBox::from_bitslice(bv.as_bitslice());
    }

    pub fn read_all_with_ec(&mut self) -> BitBox<u8> {
        self.correct_if_needed();
        self.read_all()
    }


    pub fn read(&self, index: u8) -> bool {
        assert!(index < self.n);

        let mut j = 1;
        for i in 1..=self.all_n {
            if !i.is_power_of_two() {
                if j == index + 1 {
                    return self.code[(i - 1) as usize];
                }
                j += 1;
            }
        }

        unreachable!()
    }

    pub fn read_with_ec(&mut self, index: u8) -> bool {
        assert!(index < self.n);
        self.correct_if_needed();
        self.read(index)
    }

    pub fn write(&mut self, index: u8, value: bool) {
        assert!(index < self.n);

        let mut j = 1;
        for i in 1..=self.all_n {
            if !i.is_power_of_two() {
                if j == index + 1 {
                    self.code.set((i - 1) as usize, value);
                    break;
                }
                j += 1;
            }
        }

        self.rewrite_syndromes();
    }

    pub fn clean(&mut self) { self.code.fill(false) }


    pub fn check(&self) -> bool {
        !self.calculate_syndromes().into_iter().any(identity)
    }


    fn correct_if_needed(&mut self) {
        let syndromes_bits: BitVec<u8> =
            BitVec::from_iter(self.calculate_syndromes().into_iter());

        if syndromes_bits.any() {
            let index: usize = syndromes_bits.load_le();
            let bit = self.code.get(index - 1).unwrap().as_bool();
            self.code.set(index - 1, bit);
        }
    }


    fn rewrite_syndromes(&mut self) {
        for k in 0..self.parity_n {
            self.code.set(2usize.pow(k as u32) - 1, false);
        }

        let syndromes = self.calculate_syndromes();
        let syndromes_slice = syndromes.as_slice();

        for k in 0..self.parity_n {
            self.code.set(2usize.pow(k as u32) - 1, syndromes_slice[k as usize]);
        }
    }

    fn calculate_syndromes(&self) -> Vec<bool> {
        BitIdx::MIN.range(BitEnd::new(self.parity_n).unwrap())
            .map(|i| {
                let row: BitVec<u8> = BitVec::from_iter(
                    (1..=self.all_n).map(|x| x.get_bit::<Lsb0>(i))
                );
                let sum = self.code.iter().zip(row.iter())
                    .fold(0u32, |sum, (a, b)| {
                        sum + (a.as_u32() & b.as_u32())
                    });

                sum % 2u32 == 1
            })
            .collect()
    }


    fn calculate_parity_n(m: u8) -> u8 {
        let mut k: u8 = 0;
        loop {
            if 2.pow(k as u32) >= k + m + 1 {
                break k;
            } else {
                k += 1;
            }
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let hamming = Hamming::new(4);

        assert_eq!(hamming.n, 4);
        assert_eq!(hamming.parity_n, 3);
        assert_eq!(hamming.all_n, 7);
        assert_eq!(hamming.code, bitbox![u8, Lsb0; 0; 7])
    }

    #[test]
    fn test_from_buffer() {
        let hamming = Hamming::from_buffer(&[true, false, true, true]);

        assert_eq!(hamming.n, 4);
        assert_eq!(hamming.parity_n, 3);
        assert_eq!(hamming.all_n, 7);
        assert_eq!(hamming.code, bitbox![u8, Lsb0; 0, 1, 1, 0, 0, 1, 1])
    }


    #[test]
    fn test_zeroed_check_true() {
        let hamming = Hamming::new(4);

        assert!(hamming.check());
    }

    #[test]
    fn test_zeroed_check_false() {
        let mut hamming = Hamming::new(4);

        let index: usize = 2;
        let bit = hamming.code.get(index).unwrap().as_bool();
        hamming.code.set(index, bit);

        assert!(!hamming.check());
    }

    #[test]
    fn test_check_true() {
        let hamming = Hamming::from_buffer(&[true, false, true, true]);

        assert!(hamming.check());
    }

    #[test]
    fn test_check_false() {
        let mut hamming = Hamming::from_buffer(&[true, false, true, true]);

        let index: usize = 3;
        let bit = hamming.code.get(index).unwrap().as_bool();
        hamming.code.set(index, bit);

        assert!(!hamming.check());
    }


    #[test]
    fn test_zeroed_read_all() {
        let hamming = Hamming::new(4);

        assert_eq!(hamming.read_all(), bitbox![u8, Lsb0; 0; 4])
    }

    #[test]
    fn test_read_all() {
        let hamming = Hamming::from_buffer(&[true, false, true, true]);

        assert_eq!(hamming.read_all(), bitbox![u8, Lsb0; 1, 0, 1, 1])
    }


    #[test]
    fn test_zeroed_read_all_with_ec() {
        let mut hamming = Hamming::new(4);

        let index: usize = 3;
        let bit = hamming.code.get(index).unwrap().as_bool();
        hamming.code.set(index, bit);

        assert_eq!(hamming.read_all_with_ec(), bitbox![u8, Lsb0; 0; 4]);
        assert_eq!(hamming.code, bitbox![u8, Lsb0; 0; 7])
    }

    #[test]
    fn test_read_all_with_ec() {
        let mut hamming = Hamming::from_buffer(&[true, false, true, true]);

        let index: usize = 3;
        let bit = hamming.code.get(index).unwrap().as_bool();
        hamming.code.set(index, bit);

        assert_eq!(hamming.read_all_with_ec(), bitbox![u8, Lsb0; 1, 0, 1, 1]);
        assert_eq!(hamming.code, bitbox![u8, Lsb0; 0, 1, 1, 0, 0, 1, 1]);
    }


    #[test]
    fn test_zeroed_read() {
        let hamming = Hamming::new(4);

        assert_eq!(hamming.read(0), false);
        assert_eq!(hamming.read(1), false);
        assert_eq!(hamming.read(3), false);
    }

    #[test]
    fn test_read() {
        let hamming = Hamming::from_buffer(&[true, false, true, true]);

        assert_eq!(hamming.read(0), true);
        assert_eq!(hamming.read(1), false);
        assert_eq!(hamming.read(3), true);
    }

    #[test]
    #[should_panic]
    fn test_panic_on_read() {
        let hamming = Hamming::new(4);
        hamming.read(100);
    }


    #[test]
    fn test_zeroed_read_with_ec() {
        let mut hamming = Hamming::new(4);

        let index: usize = 4;
        let bit = hamming.code.get(index).unwrap().as_bool();
        hamming.code.set(index, bit);

        assert_eq!(hamming.read_with_ec(0), false);
        assert_eq!(hamming.read_with_ec(1), false);
        assert_eq!(hamming.read_with_ec(3), false);
        assert_eq!(hamming.code, bitbox![u8, Lsb0; 0; 7]);
    }

    #[test]
    fn test_read_with_ec() {
        let mut hamming = Hamming::from_buffer(&[true, false, true, true]);

        let index: usize = 4;
        let bit = hamming.code.get(index).unwrap().as_bool();
        hamming.code.set(index, bit);

        assert_eq!(hamming.read_with_ec(0), true);
        assert_eq!(hamming.read_with_ec(1), false);
        assert_eq!(hamming.read_with_ec(3), true);
        assert_eq!(hamming.code, bitbox![u8, Lsb0; 0, 1, 1, 0, 0, 1, 1]);
    }

    #[test]
    #[should_panic]
    fn test_panic_on_read_with_ec() {
        let mut hamming = Hamming::new(4);
        hamming.read_with_ec(100);
    }


    #[test]
    fn test_zeroed_write() {
        let mut hamming = Hamming::new(4);

        hamming.write(2, true);

        assert_eq!(hamming.code, bitbox![u8, Lsb0; 0, 1, 0, 1, 0, 1, 0]);
    }

    #[test]
    fn test_write() {
        let mut hamming = Hamming::from_buffer(&[true, false, true, true]);

        hamming.write(2, false);

        assert_eq!(hamming.code, bitbox![u8, Lsb0; 0, 0, 1, 1, 0, 0, 1]);
    }

    #[test]
    #[should_panic]
    fn test_panic_on_write() {
        let mut hamming = Hamming::new(4);
        hamming.write(100, true);
    }


    #[test]
    fn test_clean() {
        let mut hamming = Hamming::from_buffer(&[true, false, true, true]);

        hamming.clean();

        assert_eq!(hamming.code, bitbox![u8, Lsb0; 0; 7]);
    }
}
