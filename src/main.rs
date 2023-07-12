use crate::raid2::Raid2;

mod raid2;
mod hamming;

fn main() {
    let mut raid2 = Raid2::new(4, 8);
    println!("zero:\n{}", raid2);
    raid2.write(0, 0, true);
    raid2.write(0, 2, true);
    raid2.write(0, 3, true);
    println!("after:\n{}", raid2);
}
