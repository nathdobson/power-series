use std::collections::BTreeMap;
use std::fmt::{Debug, Display, Formatter};
use std::ops::{Add, Div, Mul, Neg, Sub};

use crate::model::ordinary::OrdinaryGen;
use crate::model::Scalar;
use crate::util::ops::impl_ops_by_value;
use crate::util::scalar::ScalarMethods;

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
    pub fn powers(&self) -> impl Iterator<Item = isize> {
        let init = self.init;
        self.ord.powers().map(move |x| x as isize + init)
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
    pub fn poly(poly: BTreeMap<isize, T>) -> Self {
        let init = *poly.first_key_value().unwrap().0;
        LaurentGen::new(
            init,
            OrdinaryGen::poly(
                poly.iter()
                    .map(|(&i, x)| ((i - init) as usize, x.clone()))
                    .collect(),
            ),
        )
    }
    pub fn recip(self) -> Self { self.normalize().recip_raw() }
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
    pub fn sqrt_raw(self)->Self{
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

impl<T: Scalar> ScalarMethods for LaurentGen<T> {
    fn sqrt(self) -> Self {
        self.normalize().sqrt_raw()
    }
    fn exp(self) -> Self { OrdinaryGen::try_from(self).unwrap().exp().into() }
    fn from_isize(x: isize) -> Self { Self::from(OrdinaryGen::from_isize(x)) }
    fn from_usize(x: usize) -> Self { Self::from(OrdinaryGen::from_usize(x)) }
    fn one() -> Self { Self::from(OrdinaryGen::one()) }
    fn zero() -> Self { Self::from(OrdinaryGen::zero()) }
    fn powi(self, x: isize) -> Self {
        let mut result = Self::one();
        for _ in 0..x {
            result = result * &self;
        }
        result
    }
}

impl<T> Clone for LaurentGen<T> {
    fn clone(&self) -> Self {
        LaurentGen {
            init: self.init,
            ord: self.ord.clone(),
        }
    }
}

#[derive(Debug)]
pub struct NegativePowerError;
impl Display for NegativePowerError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result { todo!() }
}

impl<T: Scalar> TryFrom<LaurentGen<T>> for OrdinaryGen<T> {
    type Error = NegativePowerError;
    fn try_from(value: LaurentGen<T>) -> Result<Self, Self::Error> {
        if value.init >= 0 {
            Ok(value.ord.multiply_by_power(value.init as usize))
        } else {
            Err(NegativePowerError)
        }
    }
}

impl<T: Scalar> From<OrdinaryGen<T>> for LaurentGen<T> {
    fn from(value: OrdinaryGen<T>) -> Self { Self::new(0, value) }
}

impl<T: Scalar> Debug for LaurentGen<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "x^{}({})", self.init, self.ord)
    }
}

impl_ops_by_value! {
    impl <[T:Scalar]> [LaurentGen<T>];
}

#[test]
fn test_add() {
    let f = LaurentGen::<f64>::poly([(-1, 2.0), (1, 3.0)].into_iter().collect())
        + LaurentGen::<f64>::poly([(-2, 3.0), (2, 5.0)].into_iter().collect());
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
    let f = LaurentGen::<f64>::poly([(-1, 2.0), (1, 3.0)].into_iter().collect())
        * LaurentGen::<f64>::poly([(-2, 3.0), (2, 5.0)].into_iter().collect());
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
