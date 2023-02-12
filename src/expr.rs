use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::fmt::{Debug, Display, Formatter};
use std::hash::{Hash, Hasher};
use std::iter::Sum;
use std::ops::{Add, Div, Mul, Neg, Sub};
use std::rc::Rc;

use by_address::ByAddress;
use num::{One, ToPrimitive, Zero};
use safe_once::unsync::OnceCell;

use crate::eval::Eval;
use crate::functional::Functional;
use crate::ops::impl_ops_by_value;
use crate::scalar::{Scalar,};

pub enum ExprImpl<T: 'static> {
    Add(Expr<T>, Expr<T>),
    Mul(Expr<T>, Expr<T>),
    Sub(Expr<T>, Expr<T>),
    Div(Expr<T>, Expr<T>),
    Exp(Expr<T>),
    Neg(Expr<T>),
    Sqrt(Expr<T>),
    Poly(BTreeMap<isize, T>),
    Powi(Expr<T>, isize),
    Recip(Expr<T>),
}

struct Inner<T: 'static> {
    imp: ExprImpl<T>,
    deriv: OnceCell<Expr<T>>,
}

#[derive(Clone)]
pub struct Expr<T: 'static>(Rc<Inner<T>>);

pub struct ExprId<T: 'static>(ByAddress<Rc<Inner<T>>>);

impl<T: Scalar> Expr<T> {
    pub fn new(x: ExprImpl<T>) -> Self {
        Expr(Rc::new(Inner {
            imp: x,
            deriv: OnceCell::new(),
        }))
    }
    pub fn id(&self) -> ExprId<T> { ExprId(ByAddress(self.0.clone())) }
    pub fn imp(&self) -> &ExprImpl<T> { &self.0.imp }
    pub fn deriv(&self) -> Expr<T> {
        self.0
            .deriv
            .get_or_init(|| match &self.0.imp {
                ExprImpl::Add(x, y) => x.deriv() + y.deriv(),
                ExprImpl::Mul(x, y) => x.deriv() * y + y.deriv() * x,
                ExprImpl::Poly(x) => Expr::<T>::new(ExprImpl::Poly(
                    x.into_iter()
                        .flat_map(|(&i, x)| {
                            if i == 0 {
                                None
                            } else {
                                Some((i - 1, T::from_num(i) * x))
                            }
                        })
                        .collect(),
                )),
                ExprImpl::Exp(x) => x.deriv() * self,
                ExprImpl::Sub(x, y) => x.deriv() - y.deriv(),
                ExprImpl::Div(x, y) => (x.deriv() * y - x * y.deriv()) / (y * y),
                ExprImpl::Neg(x) => -x.deriv(),
                ExprImpl::Sqrt(x) => x.deriv() / (Expr::from(T::from_num(2)) * self),
                ExprImpl::Powi(x, n) => todo!("{:?}{:?}", x, n),
                ExprImpl::Recip(x) => todo!("{:?}", x),
            })
            .clone()
    }

    pub fn eval(&self, x: T) -> T { Eval::<T, T, _>::new(x, |y: T| y).eval(self).clone() }
    pub fn into_functional<T2: Functional<T>>(&self) -> T2 {
        Eval::<T, T2, _>::new(T2::var(), |x: T| T2::con(x))
            .eval(self)
            .clone()
    }
    pub fn map<T2: Scalar>(&self, f: impl Fn(T) -> T2) -> Expr<T2> {
        Eval::<T, Expr<T2>, _>::new(Expr::var(), |y| Expr::con(f(y)))
            .eval(self)
            .clone()
    }
    pub fn expected(&self) -> T { self.deriv().eval(T::one()) }
    pub fn variance(&self) -> T {
        let expected = self.expected();
        self.deriv().deriv().eval(T::one()) + &expected - &expected * &expected
    }
    pub fn poly(poly: BTreeMap<isize, T>) -> Self { Expr::new(ExprImpl::Poly(poly)) }
    pub fn proportion(x: T) -> Self { Self::poly([(1, x)].into_iter().collect()) }
}

impl_ops_by_value! {
    impl<[T:Scalar]> [Expr<T>];
}

impl<T: Scalar> Add for Expr<T> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output { Expr::new(ExprImpl::Add(self, rhs)) }
}

impl<T: Scalar> Mul for Expr<T> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output { Expr::new(ExprImpl::Mul(self, rhs)) }
}

impl<T: Scalar> Sub for Expr<T> {
    type Output = Expr<T>;
    fn sub(self, rhs: Self) -> Self::Output { Expr::new(ExprImpl::Sub(self, rhs)) }
}

impl<T: Scalar> Div for Expr<T> {
    type Output = Expr<T>;
    fn div(self, rhs: Self) -> Self::Output { Expr::new(ExprImpl::Div(self, rhs)) }
}

impl<T: Scalar> Neg for Expr<T> {
    type Output = Self;
    fn neg(self) -> Self::Output { Expr::new(ExprImpl::Neg(self)) }
}

impl<T: Scalar> From<T> for Expr<T> {
    fn from(value: T) -> Self { Expr::con(value) }
}

impl<T: Scalar> Scalar for Expr<T> {
    fn sqrt(self) -> Self { Expr::new(ExprImpl::Sqrt(self.clone())) }
    fn exp(self) -> Self { Self::new(ExprImpl::Exp(self.clone())) }
    fn recip(self) -> Self { Self::new(ExprImpl::Recip(self)) }
    fn powi(self, rhs: isize) -> Self { Expr::new(ExprImpl::Powi(self, rhs)) }
    fn from_num<P: ToPrimitive>(x: P) -> Self {
        Expr::con(T::from_num(x))
    }
}

impl<T: Scalar> Sum for Expr<T> {
    fn sum<I: Iterator<Item=Self>>(iter: I) -> Self {
        let mut total = Expr::con(T::zero());
        for x in iter {
            total = total + &x;
        }
        total
    }
}

impl<T: Scalar> Display for Expr<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self.0.imp {
            ExprImpl::Add(x, y) => write!(f, "({x} + {y})"),
            ExprImpl::Mul(x, y) => write!(f, "({x} * {y})"),
            ExprImpl::Exp(x) => write!(f, "(e^{x})"),
            ExprImpl::Poly(p) => {
                if p.len() != 1 {
                    write!(f, "(")?;
                }
                for (&i, x) in p {
                    if i == 0 {
                        write!(f, "{:.5}", x)?;
                    }
                    if i == 0 {
                        write!(f, "")?;
                    } else if i == 1 {
                        write!(f, "x")?;
                    } else {
                        write!(f, "x^{}", i)?;
                    }
                    if i != *p.last_key_value().unwrap().0 {
                        write!(f, " + ")?;
                    }
                }
                if p.len() != 1 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            ExprImpl::Sub(x, y) => write!(f, "({x} - {y})"),
            ExprImpl::Div(x, y) => write!(f, "({x} / {y})"),
            ExprImpl::Neg(x) => write!(f, "(-{x})"),
            ExprImpl::Sqrt(x) => write!(f, "sqrt{x}"),
            ExprImpl::Powi(x, n) => write!(f, "({}^{})", x, n),
            ExprImpl::Recip(x) => write!(f, "(1/{})", x),
        }
    }
}

impl<T: Scalar> Debug for Expr<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result { Display::fmt(self, f) }
}

impl<T: Scalar> Functional<T> for Expr<T> {
    fn var() -> Self { Self::poly([(1, T::one())].into_iter().collect()) }
    fn con(x: T) -> Self { Self::poly([(0, x)].into_iter().collect()) }
}

impl<T: Scalar> Zero for Expr<T> {
    fn zero() -> Self { Self::con(T::zero()) }
    fn is_zero(&self) -> bool { panic!() }
}

impl<T: Scalar> One for Expr<T> {
    fn one() -> Self { Expr::con(T::one()) }
}

impl<T> Eq for ExprId<T> {}

impl<T> PartialEq for ExprId<T> {
    fn eq(&self, other: &Self) -> bool { self.0.eq(&other.0) }
}

impl<T> Ord for ExprId<T> {
    fn cmp(&self, other: &Self) -> Ordering { self.0.cmp(&other.0) }
}

impl<T> PartialOrd for ExprId<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> { self.0.partial_cmp(&other.0) }
}

impl<T> Hash for ExprId<T> {
    fn hash<H: Hasher>(&self, state: &mut H) { self.0.hash(state) }
}

impl<T> Clone for ExprId<T> {
    fn clone(&self) -> Self { ExprId(self.0.clone()) }
}
