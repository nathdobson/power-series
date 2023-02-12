use crate::field::Field;

pub trait Series<T>: Field {
    fn con(x: T) -> Self;
    fn var() -> Self;
}