#![feature(trait_alias)]
#![feature(try_blocks)]
#![deny(unused_must_use)]

pub mod scalar;
pub mod number;
pub mod ops;
pub mod expr;
pub mod eval;
pub mod once_cell_map;
pub mod functional;
pub mod ordinary;
pub mod laurent;
pub mod puiseux;
pub mod print;
pub mod term;

pub fn add(left: usize, right: usize) -> usize {
    left + right
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result, 4);
    }
}
