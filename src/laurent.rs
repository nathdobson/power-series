use std::collections::BTreeMap;
use std::fmt::{Debug, Display, Formatter};
use std::iter::Sum;
use std::ops::{Add, Div, Mul, Neg, Sub};
use num::traits::{One, ToPrimitive, Zero};
use crate::functional::Functional;

use crate::ordinary::OrdinaryGen;
use crate::scalar::{Scalar, simple_pow};
use crate::ops::impl_ops_by_value;
use crate::term::Term;

pub struct LaurentGen<T: 'static> {
    init: isize,
    ord: OrdinaryGen<T>,
}

impl<T: Scalar> LaurentGen<T> {
    pub fn new(init: isize, ord: OrdinaryGen<T>) -> Self { LaurentGen { init, ord } }
    pub fn gen(&self, x: isize) -> T {
        if x < self.init {
            T::zero()
        } else {
            self.ord.gen((x - self.init).try_into().unwrap())
        }
    }
    pub fn ord(&self) -> &OrdinaryGen<T> { &self.ord }
    pub fn min_power(&self) -> isize { self.init }
    pub fn max_power(&self) -> Option<isize> { Some(self.ord.max_power()? as isize + self.init) }
    pub fn powers(&self) -> impl Iterator<Item=isize> {
        let init = self.init;
        self.ord.powers().map(move |x| x as isize + init)
    }
    pub fn terms(&self) -> impl Iterator<Item=Term<T, isize>> {
        let this = self.clone();
        this.powers().map(move |p| Term { co: this.gen(p), power: p })
    }
    fn with_init(&self, new_init: isize) -> Self {
        LaurentGen::new(
            new_init,
            self.ord
                .clone()
                .multiply_by_power((self.init - new_init).try_into().unwrap()),
        )
    }
    pub fn compose_with_power(self, power: usize) -> Self {
        LaurentGen::new(
            self.init * power as isize,
            self.ord.compose_with_power(power),
        )
    }
    pub fn poly(poly: impl IntoIterator<Item=(T, isize)>) -> Self {
        let map = poly.into_iter().map(|(x, y)| (y, x)).collect::<BTreeMap<isize, T>>();
        let init = *map.first_key_value().unwrap().0;
        LaurentGen::new(
            init,
            OrdinaryGen::poly(
                map.iter()
                    .map(|(&i, x)| (x.clone(), (i - init) as usize)),
            ),
        )
    }
    pub fn poly_f64(iter: impl IntoIterator<Item=(f64, isize)>) -> Self {
        Self::poly(iter.into_iter().map(|(x, y)| (T::from_num(x), y)))
    }
    pub fn recip_raw(self) -> Self { LaurentGen::new(-self.init, self.ord.recip()) }
    pub fn normalize(&self) -> Self {
        let index = self
            .ord
            .powers()
            .take(10)
            .find(|&x| !self.ord.gen(x).is_zero())
            .expect("Failed to normalize.");
        LaurentGen::new(
            index as isize + self.init,
            self.ord.clone().divide_by_power(index),
        )
    }
    pub fn sqrt_raw(self) -> Self {
        assert_eq!(self.init % 2, 0);
        LaurentGen::new(self.init / 2, self.ord.sqrt())
    }
}

impl<T: Scalar> Add for LaurentGen<T> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        let new_init = self.init.min(rhs.init);
        LaurentGen::new(
            new_init,
            self.with_init(new_init).ord + rhs.with_init(new_init).ord,
        )
    }
}

impl<T: Scalar> Sub for LaurentGen<T> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        let new_init = self.init.min(rhs.init);
        LaurentGen::new(
            new_init,
            self.with_init(new_init).ord - rhs.with_init(new_init).ord,
        )
    }
}

impl<T: Scalar> Mul for LaurentGen<T> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        LaurentGen::new(self.init + rhs.init, self.ord * rhs.ord)
    }
}

impl<T: Scalar> Div for LaurentGen<T> {
    type Output = Self;
    fn div(self, rhs: Self) -> Self::Output {
        LaurentGen::new(self.init - rhs.init, self.ord / rhs.ord)
    }
}

impl<T: Scalar> Neg for LaurentGen<T> {
    type Output = Self;
    fn neg(self) -> Self::Output { LaurentGen::new(self.init, -self.ord) }
}

impl<T: Scalar> Sum for LaurentGen<T> {
    fn sum<I: Iterator<Item=Self>>(iter: I) -> Self {
        iter.into_iter().fold(Self::zero(), Self::add)
    }
}

impl<T: Scalar> Zero for LaurentGen<T> {
    fn zero() -> Self { Self::con(T::zero()) }
    fn is_zero(&self) -> bool { false }
}

impl<T: Scalar> One for LaurentGen<T> {
    fn one() -> Self { Self::con(T::one()) }
}

impl<T: Scalar> Functional<T> for LaurentGen<T> {
    fn con(x: T) -> Self { Self::new(0, OrdinaryGen::con(x)) }
    fn var() -> Self { Self::new(1, OrdinaryGen::con(T::one())) }
}

impl<T: Scalar> Scalar for LaurentGen<T> {
    fn sqrt(self) -> Self { self.normalize().sqrt_raw() }
    fn exp(self) -> Self { OrdinaryGen::try_from(self).unwrap().exp().into() }
    fn recip(self) -> Self { self.normalize().recip_raw() }
    fn powi(self, x: isize) -> Self { simple_pow(self, x) }
    fn from_num<P: ToPrimitive>(x: P) -> Self { Self::con(T::from_num(x)) }
}

impl<T> Clone for LaurentGen<T> {
    fn clone(&self) -> Self {
        LaurentGen {
            init: self.init,
            ord: self.ord.clone(),
        }
    }
}

impl<T: Scalar> TryFrom<LaurentGen<T>> for OrdinaryGen<T> {
    type Error = ();
    fn try_from(value: LaurentGen<T>) -> Result<Self, Self::Error> {
        if value.init >= 0 {
            Ok(value.ord.multiply_by_power(value.init as usize))
        } else {
            Err(())
        }
    }
}

impl<T: Scalar> From<OrdinaryGen<T>> for LaurentGen<T> {
    fn from(value: OrdinaryGen<T>) -> Self { Self::new(0, value) }
}

impl<T: Scalar> Debug for LaurentGen<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(self, f)
    }
}

impl<T: Scalar> Display for LaurentGen<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Term::print_series(f, self.terms())
    }
}

impl_ops_by_value! {
    impl <[T:Scalar]> [LaurentGen<T>];
}

#[test]
fn test_var() {
    let f = LaurentGen::<f64>::var();
    assert_eq!("1.0x", format!("{}", f));
}

#[test]
fn test_poly() {
    let f = LaurentGen::<f64>::poly([(-1.0, -1), (2.0, 1), (4.0, 3)]);
    assert_eq!("-1.0x⁻¹ + 2.0x + 4.0x³", format!("{}", f));
}

#[test]
fn test_add() {
    let f = LaurentGen::<f64>::poly([(2.0, -1), (3.0, 1)])
        + LaurentGen::<f64>::poly([(3.0, -2), (5.0, 2)]);
    assert_eq!(f.min_power(), -2);
    assert_eq!(f.max_power(), Some(2));
    assert_eq!(f.gen(-2), 3.0);
    assert_eq!(f.gen(-1), 2.0);
    assert_eq!(f.gen(0), 0.0);
    assert_eq!(f.gen(1), 3.0);
    assert_eq!(f.gen(2), 5.0);
}

#[test]
fn test_mul() {
    let f = LaurentGen::<f64>::poly([(2.0, -1), (3.0, 1)])
        * LaurentGen::<f64>::poly([(3.0, -2), (5.0, 2)]);
    assert_eq!(f.min_power(), -3);
    assert_eq!(f.max_power(), Some(3));
    assert_eq!(f.gen(-3), 6.0);
    assert_eq!(f.gen(-2), 0.0);
    assert_eq!(f.gen(-1), 9.0);
    assert_eq!(f.gen(0), 0.0);
    assert_eq!(f.gen(1), 10.0);
    assert_eq!(f.gen(2), 0.0);
    assert_eq!(f.gen(3), 15.0);
}


#[test]
fn test_recip1() {
    let f = LaurentGen::<f64>::poly([(0.5, -1), (3.0, 1)]).recip();
    assert_eq!("2.0x + -12.0x³ + 72.0x⁵ + -432.0x⁷ + 2592.0x⁹ + ...", format!("{}", f));
}

#[test]
fn test_recip2() {
    let f = LaurentGen::<f64>::poly([(2.0, 1)]).recip();
    assert_eq!("0.5x⁻¹", format!("{}", f));
}

#[test]
fn test_exp() {
    use crate::number::Number;
    let f = LaurentGen::<Number>::poly_f64([(2.0, 0), (3.0, 1)]).exp() /
        LaurentGen::<Number>::poly_f64([(std::f64::consts::E.powi(2), 0)]);
    assert_eq!("1.00000 + 3.00000x + 4.5x² + 4.5x³ + 3.375x⁴ + ...", format!("{}", f));
}

#[test]
fn test_sqrt() {
    use crate::number::Number;
    let f = LaurentGen::<Number>::poly_f64([(1.0, -2), (1.0, 1)]).sqrt();
    assert_eq!("1x⁻¹ + 0.5x² + -0.125x⁵ + 0.0625x⁸ + -0.03906x¹¹ + ...", format!("{}", f));
}
