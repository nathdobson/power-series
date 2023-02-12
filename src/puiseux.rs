use num::integer::lcm;
use num::rational::Ratio;
use std::collections::BTreeMap;
use std::fmt::{Debug, Display, Formatter};
use std::iter::Sum;
use std::ops::{Add, Div, Mul, Neg, Sub};
use num::{One, ToPrimitive, Zero};
use crate::functional::Functional;

use crate::laurent::LaurentGen;
use crate::ops::impl_ops_by_value;
use crate::scalar::{simple_pow};
use crate::scalar::Scalar;
use crate::term::Term;

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
    pub fn powers(&self) -> impl Iterator<Item=Ratio<isize>> {
        let frac = self.frac;
        self.laur
            .powers()
            .map(move |x| Ratio::new(x, frac as isize))
    }
    pub fn terms(&self) -> impl Iterator<Item=Term<T, Ratio<isize>>> {
        let this = self.clone();
        this.powers().map(move |p| Term { co: this.gen(p), power: p })
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
    pub fn poly(iter: impl IntoIterator<Item=(T, isize, usize)>) -> Self {
        let map: BTreeMap<Ratio<isize>, T> = iter.into_iter().map(|(c, p, d)| (Ratio::new(p, d as isize), c)).collect();
        let mut frac = 1;
        for (p, _) in map.iter() {
            frac = lcm(frac, *p.denom());
        }
        Self::new(
            frac.try_into().unwrap(),
            LaurentGen::poly(
                map.into_iter()
                    .map(|(p, c)| (c, (p * frac).to_integer())),
            ),
        )
    }
    pub fn poly_f64(iter: impl IntoIterator<Item=(f64, isize, usize)>) -> Self {
        Self::poly(iter.into_iter().map(|(x, n, d)| (T::from_num(x), n, d)))
    }
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
    fn sum<I: Iterator<Item=Self>>(iter: I) -> Self {
        iter.into_iter().fold(Self::zero(), Self::add)
    }
}

impl<T: Scalar> Zero for PuiseuxGen<T> {
    fn zero() -> Self { PuiseuxGen::con(T::zero()) }
    fn is_zero(&self) -> bool { false }
}

impl<T: Scalar> One for PuiseuxGen<T> {
    fn one() -> Self { PuiseuxGen::con(T::one()) }
}

impl<T: Scalar> Functional<T> for PuiseuxGen<T> {
    fn con(x: T) -> Self { PuiseuxGen::poly([(x, 0, 1)]) }
    fn var() -> Self { PuiseuxGen::poly([(T::one(), 1, 1)]) }
}

impl<T: Scalar> Scalar for PuiseuxGen<T> {
    fn sqrt(self) -> Self { self.normalize().sqrt_raw() }
    fn exp(self) -> Self { PuiseuxGen::new(self.frac, self.laur.exp()) }
    fn recip(self) -> Self { PuiseuxGen::new(self.frac, self.laur.recip()) }
    fn powi(self, rhs: isize) -> Self { simple_pow(self, rhs) }
    fn from_num<P: ToPrimitive>(x: P) -> Self { Self::con(T::from_num(x)) }
}

impl_ops_by_value! {
    impl <[T:Scalar]> [PuiseuxGen<T>];
}

impl<T: Scalar> Display for PuiseuxGen<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result { Term::print_series(f, self.terms()) }
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
    let first = PuiseuxGen::poly([(1.0, -1, 2)]);
    assert_eq!(first.gen(Ratio::new(-1, 2)), 1.0);
    let second = PuiseuxGen::poly([(2.0, 1, 2)]);
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


#[test]
fn test_var() {
    let f = PuiseuxGen::<f64>::var();
    assert_eq!("1.0x", format!("{}", f));
}

#[test]
fn test_poly() {
    let f = PuiseuxGen::<f64>::poly([(-1.0, -1, 2), (2.0, 1, 2), (4.0, 4, 2)]);
    assert_eq!("-1.0x⁻¹ᐟ² + 2.0x¹ᐟ² + 4.0x²", format!("{}", f));
}

#[test]
fn test_mul() {
    let f = PuiseuxGen::<f64>::poly([(2.0, -1, 2), (3.0, 1, 2)])
        * PuiseuxGen::<f64>::poly([(3.0, -2, 3), (5.0, 2, 3)]);
    assert_eq!("6.0x⁻⁷ᐟ⁶ + 9.0x⁻¹ᐟ⁶ + 10.0x¹ᐟ⁶ + 15.0x⁷ᐟ⁶", format!("{}", f));
}


#[test]
fn test_recip1() {
    let f = PuiseuxGen::<f64>::poly([(0.5, -1, 2), (3.0, 1, 2)]).recip();
    assert_eq!("2.0x¹ᐟ² + -12.0x³ᐟ² + 72.0x⁵ᐟ² + -432.0x⁷ᐟ² + 2592.0x⁹ᐟ² + ...", format!("{}", f));
}

#[test]
fn test_recip2() {
    let f = PuiseuxGen::<f64>::poly([(2.0, 1, 2)]).recip();
    assert_eq!("0.5x⁻¹ᐟ²", format!("{}", f));
}

#[test]
fn test_exp() {
    use crate::number::Number;
    let f = PuiseuxGen::<Number>::poly_f64([(2.0, 0, 2), (3.0, 1, 2)]).exp() /
        PuiseuxGen::<Number>::poly_f64([(std::f64::consts::E.powi(2), 0, 2)]);
    assert_eq!("1.00000 + 3.00000x¹ᐟ² + 4.5x + 4.5x³ᐟ² + 3.375x² + ...", format!("{}", f));
}

#[test]
fn test_sqrt1() {
    use crate::number::Number;
    let f = PuiseuxGen::<Number>::poly_f64([(1.0, -2, 1), (1.0, 1, 1)]).sqrt();
    assert_eq!("1x⁻¹ + 0.5x² + -0.125x⁵ + 0.0625x⁸ + -0.03906x¹¹ + ...", format!("{}", f));
}

#[test]
fn test_sqrt2() {
    use crate::number::Number;
    let f = PuiseuxGen::<Number>::poly_f64([(1.0, -1, 1), (1.0, 1, 1)]).sqrt();
    assert_eq!("1x⁻¹ᐟ² + 0.5x³ᐟ² + -0.125x⁷ᐟ² + 0.0625x¹¹ᐟ² + -0.03906x¹⁵ᐟ² + ...", format!("{}", f));
}
