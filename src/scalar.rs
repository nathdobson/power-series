use std::fmt::{Debug, Display};
use std::iter::Sum;
use std::ops::{Add, Div, Mul, Neg, Sub};

use num::traits::{NumCast, One, ToPrimitive, Zero};

pub trait Scalar : ScalarOps {
    fn sqrt(self) -> Self;
    fn exp(self) -> Self;
    fn recip(self) -> Self;
    fn powi(self, rhs: isize) -> Self;
    fn from_num<T: ToPrimitive>(x: T) -> Self;
}

pub trait ScalarOps = 'static
+ Sized
+ Clone
+ Sum
+ Debug
+ Display
+ Add<Output=Self>
+ Mul<Output=Self>
+ Sub<Output=Self>
+ Div<Output=Self>
+ Neg<Output=Self>
+ One
+ Zero
    where
            for<'a> &'a Self: Sized
    + Add<Output=Self> //
    + Add<&'a Self, Output=Self> //
    + Mul<Output=Self>
    + Mul<&'a Self, Output=Self>
    + Sub<Output=Self> //
    + Sub<&'a Self, Output=Self> //
    + Div<Output=Self> //
    + Div<&'a Self, Output=Self> //
    + Neg<Output=Self>,
            for<'a> Self: Sized //
            + Add<&'a Self, Output=Self>
            + Mul<&'a Self, Output=Self>
            + Sub<&'a Self, Output=Self>
            + Div<&'a Self, Output=Self>;

impl Scalar for f64 {
    fn sqrt(self) -> Self { f64::sqrt(self) }
    fn exp(self) -> Self { f64::exp(self) }
    fn recip(self) -> Self { f64::recip(self) }
    fn powi(self, x: isize) -> Self { f64::powi(self, x.try_into().unwrap()) }
    fn from_num<T: ToPrimitive>(x: T) -> Self { NumCast::from(x).unwrap() }
}

pub fn simple_pow<T: Scalar>(x: T, p: isize) -> T {
    let mut result = T::one();
    for _ in 0..p.abs() {
        result = result * &x;
    }
    if p < 0 {
        result.recip()
    } else {
        result
    }
}
