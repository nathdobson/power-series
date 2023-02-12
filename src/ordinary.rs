use cache_map::OnceCellMap;
use itertools::{Either, max};
use ndarray::ScalarOperand;
use std::collections::BTreeMap;
use std::fmt::{Debug, Display, Formatter};
use std::iter::Sum;
use std::ops::{Add, Bound, Div, Mul, Neg, Sub};
use std::rc::Rc;

use crate::model::expr::Expr;
use crate::model::Functional;
use crate::util::number::Number;
use crate::util::ops::impl_ops_by_value;
use crate::util::scalar::{Scalar, ScalarMethods};

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
    pub fn powers(&self) -> impl Iterator<Item = usize> {
        self.max_power()
            .map_or(Either::Right(0..), |max_power| Either::Left(0..=max_power))
    }
    #[track_caller]
    pub fn gen(&self, index: usize) -> T {
        self.0
            .cache
            .get_or_init(&index, || (self.0.imp)(index, &self))
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
    pub fn poly(x: BTreeMap<usize, T>) -> Self {
        OrdinaryGen::new(
            //
            Some(x.last_key_value().map_or(0, |(&m, _)| m)), //
            move |n, _| x.get(&n).cloned().unwrap_or(T::from_isize(0)),
        )
    }
}

impl<T: Scalar> OrdinaryGen<T> {
    pub fn recip(self) -> Self {
        let result = OrdinaryGen::new(None, move |n, cache| {
            if n == 0 {
                T::from_isize(1) / self.gen(0)
            } else {
                -T::from_isize(1) / self.gen(0)
                    * (1..=n).map(|i| self.gen(i) * cache.gen(n - i)).sum::<T>()
            }
        });
        result.gen(0);
        result
    }
}

impl<T: Scalar> Debug for OrdinaryGen<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let max = self.max_power().unwrap_or(4);
        for i in 0..=max {
            write!(f, "{:.5}x^{}", self.gen(i), i)?;
            if i != max {
                write!(f, "+")?;
            }
        }
        if self.max_power() > Some(max) {
            write!(f, "+...")?;
        }
        Ok(())
    }
}

impl<T: Scalar> ScalarMethods for OrdinaryGen<T> {
    fn sqrt(self) -> Self {
        OrdinaryGen::new(None, move |n, cache| {
            if n == 0 {
                self.gen(0).sqrt()
            } else {
                ((T::from_usize(n) / T::from_isize(2)) * self.gen(n)
                    - (1..n)
                        .map(|k| T::from_usize(k) * cache.gen(k) * cache.gen(n - k))
                        .sum::<T>())
                    / (T::from_usize(n) * cache.gen(0))
            }
        })
    }
    fn exp(self) -> Self {
        OrdinaryGen::new(None, move |n, cache| {
            if n == 0 {
                return self.gen(0).exp();
            } else {
                T::one() / T::from_usize(n)
                    * (1..=n)
                        .map(|k| T::from_usize(k) * self.gen(k) * cache.gen(n - k))
                        .sum::<T>()
            }
        })
    }
    fn from_isize(x: isize) -> Self { todo!() }
    fn from_usize(x: usize) -> Self { todo!() }
    fn one() -> Self { Self::con(T::one()) }
    fn zero() -> Self { Self::con(T::zero()) }
    fn powi(self, x: isize) -> Self {
        let mut result = Self::one();
        for _ in 0..x {
            result = result * &self;
        }
        result
    }
}

impl<T: Scalar> Functional<T> for OrdinaryGen<T> {
    fn con(x: T) -> Self { OrdinaryGen::poly([(0, x)].into_iter().collect()) }
    fn var() -> Self { OrdinaryGen::poly([(1, T::one())].into_iter().collect()) }
}

impl<T: Scalar> Display for OrdinaryGen<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result { Debug::fmt(self, f) }
}

impl<T: Scalar> ScalarOperand for OrdinaryGen<T> {}

impl<T> Clone for OrdinaryGen<T> {
    fn clone(&self) -> Self { Self(self.0.clone()) }
}

impl<T: Scalar> Sum for OrdinaryGen<T> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self { iter.fold(Self::zero(), Self::add) }
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
}

#[test]
fn test_var() {
    let f = OrdinaryGen::<f64>::var();
    assert_eq!(f.max_power(), Some(1));
    assert_eq!(f.gen(0), 0.0);
    assert_eq!(f.gen(1), 1.0);
    assert_eq!(f.gen(2), 0.0);
}

#[test]
fn test_poly() {
    let f = OrdinaryGen::<f64>::poly([(1, 2.0), (3, 4.0)].into_iter().collect());
    assert_eq!(f.max_power(), Some(3));
    assert_eq!(f.gen(0), 0.0);
    assert_eq!(f.gen(1), 2.0);
    assert_eq!(f.gen(2), 0.0);
    assert_eq!(f.gen(3), 4.0);
    assert_eq!(f.gen(4), 0.0);
}

#[test]
fn test_add() {
    let f = OrdinaryGen::<f64>::poly([(1, 2.0), (2, 3.0), (3, 4.0)].into_iter().collect())
        + OrdinaryGen::<f64>::poly([(2, 3.0), (4, 5.0)].into_iter().collect());
    assert_eq!(f.max_power(), Some(4));
    assert_eq!(f.gen(0), 0.0);
    assert_eq!(f.gen(1), 2.0);
    assert_eq!(f.gen(2), 6.0);
    assert_eq!(f.gen(3), 4.0);
    assert_eq!(f.gen(4), 5.0);
    assert_eq!(f.gen(5), 0.0);
}

#[test]
fn test_sub() {
    let f = OrdinaryGen::<f64>::poly([(1, 2.0), (2, 3.0), (3, 4.0)].into_iter().collect())
        - OrdinaryGen::<f64>::poly([(2, 3.0), (4, 5.0)].into_iter().collect());
    assert_eq!(f.max_power(), Some(4));
    assert_eq!(f.gen(0), 0.0);
    assert_eq!(f.gen(1), 2.0);
    assert_eq!(f.gen(2), 0.0);
    assert_eq!(f.gen(3), 4.0);
    assert_eq!(f.gen(4), -5.0);
    assert_eq!(f.gen(5), 0.0);
}

#[test]
fn test_mul_fin() {
    let f = OrdinaryGen::<f64>::poly([(1, 2.0), (2, 3.0)].into_iter().collect())
        * OrdinaryGen::<f64>::poly([(2, 3.0), (4, 5.0)].into_iter().collect());
    assert_eq!(f.max_power(), Some(6));
    assert_eq!(f.gen(0), 0.0);
    assert_eq!(f.gen(1), 0.0);
    assert_eq!(f.gen(2), 0.0);
    assert_eq!(f.gen(3), 6.0);
    assert_eq!(f.gen(4), 9.0);
    assert_eq!(f.gen(5), 10.0);
    assert_eq!(f.gen(6), 15.0);
    assert_eq!(f.gen(7), 0.0);
}

#[test]
fn test_ordinary() {
    println!("{:?}", OrdinaryGen::<f64>::con(1.0));
    println!(
        "{:?}",
        OrdinaryGen::<f64>::con(1.0) * OrdinaryGen::<f64>::con(1.0)
    );
    println!("{:?}", Expr::con(1.0).into_functional::<OrdinaryGen<f64>>());
    let foo = (Expr::var() + Expr::con(1.0))
        .powi(2)
        .into_functional::<OrdinaryGen<f64>>();
    println!("{:?}", foo);
    println!(
        "{:?}",
        (Expr::one() / (Expr::one() - Expr::var())).into_functional::<OrdinaryGen<f64>>()
    );
    println!(
        "{:?}",
        ((Expr::one() + Expr::var()).sqrt()).into_functional::<OrdinaryGen<f64>>()
    );
    println!(
        "{:?}",
        ((Expr::from_isize(2) + Expr::from_isize(3) * Expr::var()).exp())
            .into_functional::<OrdinaryGen<Number>>()
    );
    println!(
        "{:?}",
        ((Expr::one() / (Expr::from_isize(2) + Expr::from_isize(3) * Expr::var())).powi(2))
            .exp()
            .sqrt()
            .into_functional::<OrdinaryGen<Number>>()
    );
}
