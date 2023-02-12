use std::fmt::{Debug, Display};
use std::iter::Sum;
use std::ops::{Add, Div, Mul, Neg, Sub};

use inari::Interval;

pub trait ScalarMethods {
    fn sqrt(self) -> Self;
    fn exp(self) -> Self;
    fn from_isize(x: isize) -> Self;
    fn from_usize(x: usize) -> Self;
    fn one() -> Self;
    fn zero() -> Self;
    fn powi(self, x: isize) -> Self;
    fn is_zero(&self) -> bool { true }
}

pub trait Scalar = 'static
    + Sized
    + Clone
    + ScalarMethods
    + Sum
    + Debug
    + Display
    + Add<Output = Self>
    + Mul<Output = Self>
    + Sub<Output = Self>
    + Div<Output = Self>
    + Neg<Output = Self>
where
    for<'a> &'a Self: Sized
        + Add<Output = Self> //
        + Add<&'a Self, Output = Self> //
        + Mul<Output = Self>
        + Mul<&'a Self, Output = Self>
        + Sub<Output = Self> //
        + Sub<&'a Self, Output = Self> //
        + Div<Output = Self> //
        + Div<&'a Self, Output = Self> //
        + Neg<Output = Self>,
    for<'a> Self: Sized //
        + Add<&'a Self, Output = Self>
        + Mul<&'a Self, Output = Self>
        + Sub<&'a Self, Output = Self>
        + Div<&'a Self, Output = Self>;

impl ScalarMethods for f64 {
    fn sqrt(self) -> Self { f64::sqrt(self) }
    fn exp(self) -> Self { f64::exp(self) }
    fn from_isize(x: isize) -> Self { x as f64 }
    fn from_usize(x: usize) -> Self { x as f64 }
    fn one() -> Self { 1.0 }
    fn zero() -> Self { 0.0 }
    fn powi(self, x: isize) -> Self { f64::powi(self, i32::try_from(x).unwrap()) }
}

impl ScalarMethods for Interval {
    fn sqrt(self) -> Self { Interval::sqrt(self) }
    fn exp(self) -> Self { Interval::exp(self) }
    fn from_isize(x: isize) -> Self { Interval::try_from((x as f64, x as f64)).unwrap() }
    fn from_usize(x: usize) -> Self { Interval::try_from((x as f64, x as f64)).unwrap() }
    fn one() -> Self { Self::from_usize(1) }
    fn zero() -> Self { Self::from_isize(0) }
    fn powi(self, x: isize) -> Self { Self::powi(self, i32::try_from(x).unwrap()) }
}

// impl<T: Scalar + Float> ScalarMethods for NotNan<T> {
//     fn sqrt(self) -> Self { NotNan::new(<T as ScalarMethods>::sqrt(self.into_inner())).unwrap() }
//     fn exp(self) -> Self { NotNan::new(<T as ScalarMethods>::exp(self.into_inner())).unwrap() }
//     fn from_isize(x: isize) -> Self { NotNan::new(T::from_isize(x)).unwrap() }
//     fn from_usize(x: usize) -> Self { NotNan::new(T::from_usize(x)).unwrap() }
//     fn one() -> Self { NotNan::new(<T as ScalarMethods>::one()).unwrap() }
//     fn zero() -> Self { NotNan::new(<T as ScalarMethods>::zero()).unwrap() }
//     fn powi(self, x: isize) -> Self { todo!() }
// }
