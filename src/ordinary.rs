use std::collections::BTreeMap;
use std::fmt::{Debug, Display, Formatter};
use std::iter::Sum;
use std::ops::{Add, Div, Mul, Neg, Sub};
use std::rc::Rc;

use itertools::{Either};
use num::traits::{One, Pow, ToPrimitive, Zero};

use crate::functional::Functional;
use crate::once_cell_map::OnceCellMap;
use crate::ops::impl_ops_by_value;
use crate::scalar::{Scalar, simple_pow};
use crate::term::Term;

struct Inner<T: 'static> {
    imp: Box<dyn Fn(usize, &OrdinaryGen<T>) -> T>,
    cache: OnceCellMap<usize, T>,
    max: Option<usize>,
}

pub struct OrdinaryGen<T: 'static>(Rc<Inner<T>>);

impl<T: Scalar> OrdinaryGen<T> {
    pub fn new<I: Fn(usize, &OrdinaryGen<T>) -> T + 'static>(max: Option<usize>, imp: I) -> Self {
        let result = OrdinaryGen(Rc::new(Inner {
            max,
            imp: Box::new(imp),
            cache: OnceCellMap::new(),
        }));
        result
    }
    pub fn max_power(&self) -> Option<usize> { self.0.max }
    pub fn powers(&self) -> impl Iterator<Item=usize> {
        self.max_power()
            .map_or(Either::Right(0..), |max_power| Either::Left(0..=max_power))
    }
    pub fn terms(&self) -> impl Iterator<Item=Term<T, usize>> {
        let this = self.clone();
        this.powers().map(move |p| Term { co: this.gen(p), power: p })
    }
    #[track_caller]
    pub fn gen(&self, index: usize) -> T {
        self.0
            .cache
            .get_or_init(index, || (self.0.imp)(index, &self))
            .clone()
    }
    pub fn multiply_by_power(self, power: usize) -> Self {
        OrdinaryGen::new(try { self.max_power()? + power }, move |x, _| {
            if x < power {
                T::zero()
            } else {
                self.gen(x - power)
            }
        })
    }
    pub fn divide_by_power(self, power: usize) -> Self {
        for i in 0..power {
            assert!(self.gen(i).is_zero());
        }
        OrdinaryGen::new(try { self.max_power()? - power }, move |x, _| {
            self.gen(x + power)
        })
    }
    pub fn compose_with_power(self, power: usize) -> Self {
        OrdinaryGen::new(try { self.max_power()? * power }, move |x, _| {
            if x % power == 0 {
                self.gen(x / power)
            } else {
                T::zero()
            }
        })
    }
}

impl<T: Scalar> Add for OrdinaryGen<T> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        OrdinaryGen::new(
            //
            try { self.max_power()?.max(rhs.max_power()?) },
            move |x, _| self.gen(x) + rhs.gen(x),
        )
    }
}

impl<T: Scalar> Sub for OrdinaryGen<T> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        OrdinaryGen::new(
            try { self.max_power()?.max(rhs.max_power()?) },
            move |x, _| self.gen(x) - rhs.gen(x),
        )
    }
}

impl<T: Scalar> Mul for OrdinaryGen<T> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        OrdinaryGen::new(
            try { self.max_power()? + rhs.max_power()? }, //
            move |x, _| {
                let min: Option<usize> = try { x.checked_sub(rhs.max_power()?)? };
                let min = min.unwrap_or(0);
                (min..=x).map(|i| self.gen(i) * rhs.gen(x - i)).sum()
            },
        )
    }
}

impl<T: Scalar> Div for OrdinaryGen<T> {
    type Output = OrdinaryGen<T>;
    fn div(self, rhs: Self) -> Self::Output { self * rhs.recip() }
}

impl<T: Scalar> Neg for OrdinaryGen<T> {
    type Output = OrdinaryGen<T>;
    fn neg(self) -> Self::Output {
        OrdinaryGen::new(
            self.max_power(), //
            move |x, _| -self.gen(x),
        )
    }
}

impl<T: Scalar> OrdinaryGen<T> {
    pub fn poly(iter: impl IntoIterator<Item=(T, usize)>) -> Self {
        let map: BTreeMap<usize, T> = iter.into_iter().map(|(x, y)| (y, x)).collect();
        OrdinaryGen::new(
            //
            Some(map.last_key_value().map_or(0, |(&m, _)| m)), //
            move |n, _| map.get(&n).cloned().unwrap_or(T::zero()),
        )
    }
    pub fn poly_f64(iter: impl IntoIterator<Item=(f64, usize)>) -> Self {
        Self::poly(iter.into_iter().map(|(x, y)| (T::from_num(x), y)))
    }
}

impl<T: Scalar> Debug for OrdinaryGen<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(self, f)
    }
}

impl<T: Scalar> Scalar for OrdinaryGen<T> {
    fn sqrt(self) -> Self {
        OrdinaryGen::new(None, move |n, cache| {
            if n == 0 {
                self.gen(0).sqrt()
            } else {
                ((T::from_num(n) / T::from_num(2)) * self.gen(n)
                    - (1..n)
                    .map(|k| T::from_num(k) * cache.gen(k) * cache.gen(n - k))
                    .sum::<T>())
                    / (T::from_num(n) * cache.gen(0))
            }
        })
    }
    fn exp(self) -> Self {
        OrdinaryGen::new(None, move |n, cache| {
            if n == 0 {
                return self.gen(0).exp();
            } else {
                T::one() / T::from_num(n)
                    * (1..=n)
                    .map(|k| T::from_num(k) * self.gen(k) * cache.gen(n - k))
                    .sum::<T>()
            }
        })
    }

    fn recip(self) -> Self {
        let max_power = if self.max_power() == Some(0) { Some(0) } else { None };
        let result = OrdinaryGen::new(max_power, move |n, cache| {
            if n == 0 {
                T::one() / self.gen(0)
            } else {
                -T::one() / self.gen(0)
                    * (1..=n).map(|i| self.gen(i) * cache.gen(n - i)).sum::<T>()
            }
        });
        result.gen(0);
        result
    }

    fn powi(self, rhs: isize) -> Self { simple_pow(self, rhs) }

    fn from_num<P: ToPrimitive>(x: P) -> Self {
        Self::con(T::from_num(x))
    }
}

impl<T: Scalar> Zero for OrdinaryGen<T> {
    fn zero() -> Self { Self::con(T::zero()) }
    fn is_zero(&self) -> bool { self.gen(0).is_zero() }
}

impl<T: Scalar> One for OrdinaryGen<T> {
    fn one() -> Self {
        Self::con(T::one())
    }
}

impl<T: Scalar> Pow<isize> for OrdinaryGen<T> {
    type Output = Self;
    fn pow(self, rhs: isize) -> Self::Output { simple_pow(self, rhs) }
}

impl<T: Scalar> Functional<T> for OrdinaryGen<T> {
    fn con(x: T) -> Self { OrdinaryGen::poly([(x, 0)]) }
    fn var() -> Self { OrdinaryGen::poly([(T::one(), 1)]) }
}

impl<T: Scalar> Display for OrdinaryGen<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result { Term::print_series(f, self.terms()) }
}

impl<T> Clone for OrdinaryGen<T> {
    fn clone(&self) -> Self { Self(self.0.clone()) }
}

impl<T: Scalar> Sum for OrdinaryGen<T> {
    fn sum<I: Iterator<Item=Self>>(iter: I) -> Self { iter.fold(Self::zero(), Self::add) }
}

impl_ops_by_value! {
    impl <[T:Scalar]> [OrdinaryGen<T>];
}

#[test]
fn test_con() {
    let f = OrdinaryGen::<f64>::con(123.0);
    assert_eq!(f.max_power(), Some(0));
    assert_eq!(f.gen(0), 123.0);
    assert_eq!(f.gen(1), 0.0);
    assert_eq!(f.gen(2), 0.0);
    assert_eq!("123.0", format!("{}", f));
}

#[test]
fn test_var() {
    let f = OrdinaryGen::<f64>::var();
    assert_eq!(f.max_power(), Some(1));
    assert_eq!(f.gen(0), 0.0);
    assert_eq!(f.gen(1), 1.0);
    assert_eq!(f.gen(2), 0.0);
    assert_eq!("1.0x", format!("{}", f));
}

#[test]
fn test_poly() {
    let f = OrdinaryGen::<f64>::poly([(2.0, 1), (4.0, 3)]);
    assert_eq!(f.max_power(), Some(3));
    assert_eq!(f.gen(0), 0.0);
    assert_eq!(f.gen(1), 2.0);
    assert_eq!(f.gen(2), 0.0);
    assert_eq!(f.gen(3), 4.0);
    assert_eq!(f.gen(4), 0.0);
    assert_eq!("2.0x + 4.0x³", format!("{}", f));
}

#[test]
fn test_add() {
    let f = OrdinaryGen::<f64>::poly([(2.0, 1), (3.0, 2), (4.0, 3)])
        + OrdinaryGen::<f64>::poly([(3.0, 2), (5.0, 4)]);
    assert_eq!(f.max_power(), Some(4));
    assert_eq!(f.gen(0), 0.0);
    assert_eq!(f.gen(1), 2.0);
    assert_eq!(f.gen(2), 6.0);
    assert_eq!(f.gen(3), 4.0);
    assert_eq!(f.gen(4), 5.0);
    assert_eq!(f.gen(5), 0.0);
    assert_eq!("2.0x + 6.0x² + 4.0x³ + 5.0x⁴", format!("{}", f));
}

#[test]
fn test_sub() {
    let f = OrdinaryGen::<f64>::poly([(2.0, 1), (3.0, 2), (4.0, 3)])
        - OrdinaryGen::<f64>::poly([(3.0, 2), (5.0, 4)]);
    assert_eq!(f.max_power(), Some(4));
    assert_eq!(f.gen(0), 0.0);
    assert_eq!(f.gen(1), 2.0);
    assert_eq!(f.gen(2), 0.0);
    assert_eq!(f.gen(3), 4.0);
    assert_eq!(f.gen(4), -5.0);
    assert_eq!(f.gen(5), 0.0);
    assert_eq!("2.0x + 4.0x³ + -5.0x⁴", format!("{}", f));
}

#[test]
fn test_mul_fin() {
    let f = OrdinaryGen::<f64>::poly([(2.0, 1), (3.0, 2)])
        * OrdinaryGen::<f64>::poly([(3.0, 2), (5.0, 4)]);
    assert_eq!(f.max_power(), Some(6));
    assert_eq!(f.gen(0), 0.0);
    assert_eq!(f.gen(1), 0.0);
    assert_eq!(f.gen(2), 0.0);
    assert_eq!(f.gen(3), 6.0);
    assert_eq!(f.gen(4), 9.0);
    assert_eq!(f.gen(5), 10.0);
    assert_eq!(f.gen(6), 15.0);
    assert_eq!(f.gen(7), 0.0);
    assert_eq!("6.0x³ + 9.0x⁴ + 10.0x⁵ + 15.0x⁶", format!("{}", f));
}

#[test]
fn test_recip1() {
    let f = OrdinaryGen::<f64>::poly([(1.0, 0), (-1.0, 1)]).recip();
    assert_eq!(f.gen(0), 1.0);
    assert_eq!(f.gen(1), 1.0);
    assert_eq!(f.gen(2), 1.0);
    assert_eq!("1.0 + 1.0x + 1.0x² + 1.0x³ + 1.0x⁴ + ...", format!("{}", f));
}

#[test]
fn test_recip2() {
    let f = OrdinaryGen::<f64>::poly([(0.5, 0), (3.0, 1)]).recip();
    assert_eq!("2.0 + -12.0x + 72.0x² + -432.0x³ + 2592.0x⁴ + ...", format!("{}", f));
}

#[test]
fn test_recip3() {
    let f = OrdinaryGen::<f64>::poly([(2.0, 0)]).recip();
    assert_eq!("0.5", format!("{}", f));
}


#[test]
fn test_exp() {
    use crate::number::Number;
    let f = OrdinaryGen::<Number>::poly_f64([(2.0, 0), (3.0, 1)]).exp() /
        OrdinaryGen::<Number>::poly_f64([(std::f64::consts::E.powi(2), 0)]);
    assert_eq!("1.00000 + 3.00000x + 4.5x² + 4.5x³ + 3.375x⁴ + ...", format!("{}", f));
}

#[test]
fn test_sqrt() {
    use crate::number::Number;
    let f = OrdinaryGen::<Number>::poly_f64([(0.25, 0), (3.0, 1)]).sqrt();
    assert_eq!("0.5 + 3x + -9x² + 54x³ + -405x⁴ + ...", format!("{}", f));
}
