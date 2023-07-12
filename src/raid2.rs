use std::fmt::{Debug, Formatter};

use bitvec::bitvec;
use bitvec::macros::internal::funty::Fundamental;
use bitvec::order::Lsb0;
use bitvec::vec::BitVec;

use crate::hamming::Hamming;

pub struct Raid2 {
    strips: Vec<Hamming>,
    disk_cnt: u8,
    disk_size: usize,
}

impl Raid2 {
    pub fn new(disk_cnt: u8, disk_size: usize) -> Self {
        Raid2 {
            strips: vec![Hamming::new(disk_cnt); disk_size],
            disk_cnt,
            disk_size,
        }
    }


    pub fn get_disks(&self) -> Vec<BitVec<u8>> {
        let mut data = vec![bitvec![u8, Lsb0; 0; self.disk_size]; self.disk_cnt as usize];
        for (i, strip) in self.strips.iter().enumerate() {
            for (j, bit) in strip.read_all().iter().enumerate() {
                data[j].set(i, !bit.as_bool());
            }
        }
        data
    }

    pub fn get_disks_with_ec(&mut self) -> Vec<BitVec<u8>> {
        let mut data = vec![bitvec![u8, Lsb0; 0; self.disk_size]; self.disk_cnt as usize];
        for (i, strip) in self.strips.iter_mut().enumerate() {
            for (j, bit) in strip.read_all_with_ec().iter().enumerate() {
                data[j].set(i, !bit.as_bool());
            }
        }
        data
    }


    pub fn read(&self, disk_index: u8, local_address: usize) -> bool {
        (&self.strips[local_address]).read(disk_index)
    }

    pub fn read_with_ec(&mut self, disk_index: u8, local_address: usize) -> bool {
        (&mut self.strips[local_address]).read_with_ec(disk_index)
    }

    pub fn write(&mut self, disk_index: u8, local_address: usize, value: bool) {
        (&mut self.strips[local_address]).write(disk_index, value)
    }

    pub fn delete(&mut self, disk_index: u8, local_address: usize) {
        self.write(disk_index, local_address, false)
    }


    pub fn check(&self) -> bool { self.strips.iter().all(Hamming::check) }
}


impl Debug for Raid2 {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.strips.iter().map(|h| write!(f, "{}\n", h.read_all())).collect()
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let raid2 = Raid2::new(4, 128);

        assert_eq!(raid2.disk_cnt, 4);
        assert_eq!(raid2.disk_size, 128);
        assert_eq!(raid2.strips, vec![Hamming::new(4); 128]);
    }


    #[test]
    fn test_check_true() {
        let raid2 = Raid2::new(4, 128);

        assert!(raid2.check());
    }

    #[test]
    fn test_check_false() {
        let mut raid2 = Raid2::new(4, 128);

        raid2.strips[0].code.set(2, true);

        assert!(!raid2.check());
    }


    #[test]
    fn test_get_disks() {
        let raid2 = Raid2::new(4, 128);

        assert_eq!(raid2.get_disks(), vec![bitvec![u8, Lsb0; 0; 128]; 4]);
    }

    #[test]
    fn test_read_all_with_ec() {
        let mut raid2 = Raid2::new(4, 128);

        raid2.strips[0].code.set(2, true);

        assert_eq!(raid2.get_disks_with_ec(), vec![bitvec![u8, Lsb0; 0; 128]; 4]);
        assert_eq!(raid2.strips, vec![Hamming::new(4); 128]);
    }


    #[test]
    fn test_read() {
        let raid2 = Raid2::new(4, 128);

        assert_eq!(raid2.read(0, 0), false);
        assert_eq!(raid2.read(0, 1), false);
        assert_eq!(raid2.read(2, 3), false);
    }

    #[test]
    #[should_panic]
    fn test_panic_on_read() {
        let raid2 = Raid2::new(4, 128);
        raid2.read(100, 100);
    }

    #[test]
    fn test_read_with_ec() {
        let mut raid2 = Raid2::new(4, 128);

        raid2.strips[0].code.set(2, true);

        assert_eq!(raid2.read_with_ec(0, 0), false);
        assert_eq!(raid2.read_with_ec(0, 1), false);
        assert_eq!(raid2.read_with_ec(2, 3), false);
        assert_eq!(raid2.strips, vec![Hamming::new(4); 128]);
    }

    #[test]
    #[should_panic]
    fn test_panic_on_read_with_ec() {
        let mut raid2 = Raid2::new(4, 128);
        raid2.read_with_ec(100, 100);
    }


    #[test]
    fn test_write() {
        let mut raid2 = Raid2::new(4, 8);

        raid2.write(0, 2, true);

        assert_eq!(
            raid2.strips,
            vec![
                Hamming::new(4),
                Hamming::new(4),
                Hamming::from_buffer(&[true, false, false, false]),
                Hamming::new(4),
                Hamming::new(4),
                Hamming::new(4),
                Hamming::new(4),
                Hamming::new(4),
            ]
        );
    }

    #[test]
    #[should_panic]
    fn test_panic_on_write() {
        let mut raid2 = Raid2::new(4, 128);
        raid2.write(100, 100, true);
    }

    #[test]
    fn test_delete() {
        let mut raid2 = Raid2::new(4, 128);

        raid2.write(0, 2, true);
        raid2.delete(0, 2);

        assert_eq!(raid2.strips, vec![Hamming::new(4); 128]);
    }

    #[test]
    #[should_panic]
    fn test_panic_on_delete() {
        let mut raid2 = Raid2::new(4, 128);
        raid2.delete(100, 100);
    }
}
