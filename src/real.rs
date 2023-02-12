use std::fmt::{Debug, Display, Formatter, Write};
use std::iter::Sum;
use std::ops::{Add, Div, Mul, Neg, Sub};

use inari::Interval;
use num::{One, ToPrimitive, Zero};

use crate::ops::impl_ops_by_value;
use crate::field::Field;

#[derive(Copy, Clone)]
pub struct Number(Interval);

impl Number {
    pub fn from_f64(x: f64) -> Self { Self::new(Interval::try_from((x, x)).unwrap()) }
    pub fn into_f64(self) -> f64 { self.0.mid() }
    #[track_caller]
    pub fn new(x: Interval) -> Self {
        if x.is_empty() {
            panic!("empty");
        }
        if x.is_entire() {
            panic!("entire");
        }
        assert!(x.is_common_interval());
        Number(x)
    }
}

impl Add for Number {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output { Self::new(self.0 + rhs.0) }
}

impl Mul for Number {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output { Self::new(self.0 * rhs.0) }
}

impl Sub for Number {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output { Self::new(self.0 - rhs.0) }
}

impl Div for Number {
    type Output = Self;
    fn div(self, rhs: Self) -> Self::Output {
        if rhs.0.contains(0.0) {
            if rhs.0.is_singleton() {
                panic!("division by zero");
            } else {
                panic!("division contains zero");
            }
        }
        Self::new(self.0 / rhs.0)
    }
}

impl Neg for Number {
    type Output = Self;
    fn neg(self) -> Self::Output { Self::new(-self.0) }
}

impl Field for Number {
    fn sqrt(self) -> Self { Number::new(self.0.sqrt()) }
    fn exp(self) -> Self { Number::new(self.0.exp()) }

    fn recip(self) -> Self {
        Number::new(self.0.recip())
    }
    fn powi(self, rhs: isize) -> Self {
        Number::new(self.0.powi(rhs.try_into().unwrap()))
    }
    fn from_num<T: ToPrimitive>(x: T) -> Self {
        let x = x.to_f64().unwrap();
        Number::new(Interval::try_from((x, x)).unwrap())
    }
}

impl Sum for Number {
    fn sum<I: Iterator<Item=Self>>(iter: I) -> Self { iter.fold(Self::zero(), Self::add) }
}

impl Zero for Number {
    fn zero() -> Self { Self::from_num(0) }
    fn is_zero(&self) -> bool { self.0.contains(0.0) }
}

impl One for Number {
    fn one() -> Self { Self::from_num(1) }
}

impl Display for Number {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result { <Self as Debug>::fmt(self, f) }
}

impl_ops_by_value!(
    impl <[]>  [Number];
);

impl Debug for Number {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut mid = String::new();
        write!(&mut mid, "{}", self.0.mid())?;
        if mid.len() > 7 {
            mid.clear();
            write!(&mut mid, "{:.5}", self.0.mid())?;
        }
        let err = self.0.wid();
        if self.0.is_singleton() || err < 0.00001 {
            write!(f, "{}", mid)
        } else {
            write!(f, "{}(±{:.000})", mid, err)
        }
    }
}

#[test]
fn test() {
    fn f<T: Field>() {}
    fn g() { f::<Number>() }
    g()
}