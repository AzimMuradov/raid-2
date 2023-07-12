use std::fmt::{Debug, Display, Formatter};

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


    pub fn read(&self, disk_index: u8, local_address: usize) -> bool {
        (&self.strips[local_address]).read(disk_index)
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
