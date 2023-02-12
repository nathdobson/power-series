#![feature(trait_alias)]

pub mod scalar;
pub mod number;
pub mod ops;
pub mod expr;
pub mod eval;
pub mod once_cell_map;
pub mod functional;

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
