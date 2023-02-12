use crate::scalar::Scalar;

pub trait Functional<T>: Scalar {
    fn con(x: T) -> Self;
    fn var() -> Self;
}