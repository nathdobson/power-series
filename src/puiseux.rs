use num::integer::lcm;
use num::rational::Ratio;
use std::collections::BTreeMap;
use std::fmt::{Debug, Display, Formatter};
use std::iter::Sum;
use std::ops::{Add, Div, Mul, Neg, Sub};

use crate::model::{Functional, Scalar};
use crate::model::laurent::LaurentGen;
use crate::util::ops::impl_ops_by_value;
use crate::util::scalar::ScalarMethods;

pub struct PuiseuxGen<T: 'static> {
    frac: usize,
    laur: LaurentGen<T>,
}

impl<T: Scalar> PuiseuxGen<T> {
    pub fn new(frac: usize, laur: LaurentGen<T>) -> Self {
        assert!(frac > 0);
        PuiseuxGen { frac, laur }
    }
    pub fn min_power(&self) -> Ratio<isize> {
        Ratio::new(self.laur.min_power(), self.frac as isize)
    }
    pub fn max_power(&self) -> Option<Ratio<isize>> {
        Some(Ratio::new(self.laur.max_power()?, self.frac as isize))
    }
    pub fn frac(&self) -> usize { self.frac }
    pub fn powers(&self) -> impl Iterator<Item = Ratio<isize>> {
        let frac = self.frac;
        self.laur
            .powers()
            .map(move |x| Ratio::new(x, frac as isize))
    }
    pub fn with_frac(&self, frac: usize) -> Self {
        assert_eq!(frac % self.frac, 0);
        PuiseuxGen::new(frac, self.laur.clone().compose_with_power(frac / self.frac))
    }
    pub fn gen(&self, power: Ratio<isize>) -> T {
        let index = power * self.frac as isize;
        if index.is_integer() {
            self.laur.gen(index.to_integer())
        } else {
            T::zero()
        }
    }
    pub fn poly(map: BTreeMap<Ratio<isize>, T>) -> Self {
        let mut frac = 1;
        for (p, c) in map.iter() {
            frac = lcm(frac, *p.denom());
        }
        Self::new(
            frac.try_into().unwrap(),
            LaurentGen::poly(
                map.into_iter()
                    .map(|(p, c)| ((p * frac).to_integer(), c))
                    .collect(),
            ),
        )
    }
    pub fn recip(self) -> Self { PuiseuxGen::new(self.frac, self.laur.recip()) }
    pub fn normalize(&self) -> Self { PuiseuxGen::new(self.frac, self.laur.normalize()) }
    pub fn sqrt_raw(self) -> Self {
        if self.laur.min_power() % 2 == 0 {
            PuiseuxGen::new(self.frac, self.laur.sqrt_raw())
        } else {
            PuiseuxGen::new(
                self.frac * 2,
                LaurentGen::new(
                    self.laur.min_power(),
                    self.laur.ord().clone().sqrt().compose_with_power(2),
                ),
            )
        }
    }
}

impl<T: Scalar> Add for PuiseuxGen<T> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        let new_frac = lcm(self.frac, rhs.frac);
        PuiseuxGen::new(
            new_frac,
            self.with_frac(new_frac).laur + rhs.with_frac(new_frac).laur,
        )
    }
}

impl<T: Scalar> Mul for PuiseuxGen<T> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        let new_frac = lcm(self.frac, rhs.frac);
        PuiseuxGen::new(
            new_frac,
            self.with_frac(new_frac).laur * rhs.with_frac(new_frac).laur,
        )
    }
}

impl<T: Scalar> Sub for PuiseuxGen<T> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        let new_frac = lcm(self.frac, rhs.frac);
        PuiseuxGen::new(
            new_frac,
            self.with_frac(new_frac).laur - rhs.with_frac(new_frac).laur,
        )
    }
}

impl<T: Scalar> Div for PuiseuxGen<T> {
    type Output = Self;
    fn div(self, rhs: Self) -> Self::Output { self * rhs.recip() }
}

impl<T: Scalar> Neg for PuiseuxGen<T> {
    type Output = Self;
    fn neg(self) -> Self::Output { Self::new(self.frac, -self.laur) }
}

impl<T: Scalar> Sum for PuiseuxGen<T> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.into_iter().fold(Self::zero(), Self::add)
    }
}

impl<T: Scalar> Functional<T> for PuiseuxGen<T> {
    fn con(x: T) -> Self { PuiseuxGen::poly([(Ratio::new(0, 1), x)].into_iter().collect()) }
    fn var() -> Self { PuiseuxGen::poly([(Ratio::new(1, 1), T::one())].into_iter().collect()) }
}
//
// fn f<T:F>(){}
// fn g(){Func

impl<T: Scalar> ScalarMethods for PuiseuxGen<T> {
    fn sqrt(self) -> Self { self.normalize().sqrt_raw() }
    fn exp(self) -> Self { PuiseuxGen::new(self.frac, self.laur.exp()) }
    fn from_isize(x: isize) -> Self { Self::con(T::from_isize(x)) }
    fn from_usize(x: usize) -> Self { Self::con(T::from_usize(x)) }
    fn one() -> Self { Self::from_isize(1) }
    fn zero() -> Self { Self::from_isize(0) }
    fn powi(self, x: isize) -> Self {
        let mut result = Self::one();
        for _ in 0..x {
            result = result * &self;
        }
        result
    }
}

impl_ops_by_value! {
    impl <[T:Scalar]> [PuiseuxGen<T>];
}

impl<T: Scalar> Display for PuiseuxGen<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut iter = self.powers();
        let mut take = (&mut iter)
            .take(100)
            .filter(|&x| !self.gen(x).is_zero())
            .take(5)
            .peekable();
        while let Some(next) = take.next() {
            write!(f, "{}", self.gen(next))?;
            write!(f, "x")?;
            let power = format!("{}", next);
            for c in power.chars() {
                let cp = match c {
                    '0' => '⁰',
                    '1' => '¹',
                    '2' => '²',
                    '3' => '³',
                    '4' => '⁴',
                    '5' => '⁵',
                    '6' => '⁶',
                    '7' => '⁷',
                    '8' => '⁸',
                    '9' => '⁹',
                    '/' => 'ᐟ',
                    '-' => '⁻',
                    _ => panic!(),
                };
                write!(f, "{}", cp)?;
            }
            if take.peek().is_some() {
                write!(f, " + ")?;
            }
        }
        if let Some(next) = iter.next() {
            write!(f, " + ...")?;
        }
        Ok(())
    }
}

impl<T: Scalar> Debug for PuiseuxGen<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result { Display::fmt(self, f) }
}

impl<T: Scalar> Clone for PuiseuxGen<T> {
    fn clone(&self) -> Self {
        PuiseuxGen {
            frac: self.frac,
            laur: self.laur.clone(),
        }
    }
}

// impl<T:Scalar> Functional<T> for PuiseuxGen<T>{
//     fn con(x: T) -> Self {
//         Self::poly()
//     }
//
//     fn var() -> Self {
//         todo!()
//     }
// }

#[test]
fn test_add() {
    let first = PuiseuxGen::poly([(Ratio::new(-1, 2), 1.0)].into_iter().collect());
    assert_eq!(first.gen(Ratio::new(-1, 2)), 1.0);
    let second = PuiseuxGen::poly([(Ratio::new(1, 2), 2.0)].into_iter().collect());
    let f = first + second;
    assert_eq!(f.min_power(), Ratio::new(-1, 2));
    assert_eq!(f.max_power(), Some(Ratio::new(1, 2)));
    assert_eq!(f.frac(), 2);
    assert_eq!(f.gen(Ratio::new(-2, 2)), 0.0);
    assert_eq!(f.gen(Ratio::new(-1, 2)), 1.0);
    assert_eq!(f.gen(Ratio::new(0, 2)), 0.0);
    assert_eq!(f.gen(Ratio::new(1, 2)), 2.0);
    assert_eq!(f.gen(Ratio::new(2, 2)), 0.0);
}
