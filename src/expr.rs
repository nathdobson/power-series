use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::fmt::{Debug, Display, Formatter};
use std::hash::{Hash, Hasher};
use std::iter::Sum;
use std::ops::{Add, Div, Mul, Neg, Sub};
use std::rc::Rc;

use by_address::ByAddress;
use safe_once::unsync::OnceCell;

use crate::eval::Eval;
use crate::functional::Functional;
use crate::ops::impl_ops_by_value;
use crate::scalar::{Scalar, ScalarMethods};

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
                                Some((i - 1, T::from_isize(i) * x))
                            }
                        })
                        .collect(),
                )),
                ExprImpl::Exp(x) => x.deriv() * self,
                ExprImpl::Sub(x, y) => x.deriv() - y.deriv(),
                ExprImpl::Div(x, y) => (x.deriv() * y - x * y.deriv()) / (y * y),
                ExprImpl::Neg(x) => -x.deriv(),
                ExprImpl::Sqrt(x) => x.deriv() / (Expr::from(T::from_usize(2)) * self),
                ExprImpl::Powi(x, n) => todo!("{:?}{:?}", x, n),
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
    // pub fn eval_heter<T2: PartialScalar>(&self, x: T2, upcast: impl FnMut(T) -> T2) -> T2 {
    //     self.eval_with::<T2>(&x, &mut upcast, &OnceCellMap::new())
    // }
    // fn eval_with<T2: PartialScalar>(
    //     &self,
    //     x: &T2,
    //     upcast: &mut impl FnMut(T) -> T2,
    //     cache: &OnceCellMap<ByAddress<Rc<Inner<T>>>, T2>,
    // ) -> T2 {
    //     let result = cache
    //         .get_or_init(&ByAddress(self.0.clone()), || match &self.0.imp {
    //             ExprImpl::Add(f, g) => f.eval_with(x, cache) + g.eval_with(x, cache),
    //             ExprImpl::Mul(f, g) => f.eval_with(x, cache) * g.eval_with(x, cache),
    //             ExprImpl::Exp(f) => f.eval_with(x, cache).exp(),
    //             ExprImpl::Poly(p) => p.iter().map(|(&i, c)| c * &x.powi(i)).sum(),
    //             ExprImpl::Sub(f, g) => f.eval_with(x, cache) - g.eval_with(x, cache),
    //             ExprImpl::Div(f, g) => {
    //                 let an = f.eval_with(x, cache);
    //                 let bn = g.eval_with(x, cache);
    //                 an / bn
    //             }
    //             ExprImpl::Neg(f) => -f.eval_with(x, cache),
    //             ExprImpl::Sqrt(f) => f.eval_with(x, cache).sqrt(),
    //         })
    //         .clone();
    //     result
    // }
    pub fn expected(&self) -> T { self.deriv().eval(T::from_isize(1)) }
    pub fn variance(&self) -> T {
        let expected = self.expected();
        self.deriv().deriv().eval(T::from_isize(1)) + &expected - &expected * &expected
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

impl<T: Scalar> ScalarMethods for Expr<T> {
    fn sqrt(self) -> Self { Expr::new(ExprImpl::Sqrt(self.clone())) }
    fn exp(self) -> Self { Self::new(ExprImpl::Exp(self.clone())) }
    fn from_isize(x: isize) -> Self { Expr::con(T::from_isize(x)) }
    fn from_usize(x: usize) -> Self { Expr::con(T::from_usize(x)) }
    fn one() -> Self { Expr::con(T::from_usize(1)) }
    fn zero() -> Self { Expr::con(T::from_usize(0)) }
    fn powi(self, x: isize) -> Self { Expr::new(ExprImpl::Powi(self, x)) }
}

//impl<T: Scalar> ScalarOperand for Expr<T> {}

impl<T: Scalar> Sum for Expr<T> {
    fn sum<I: Iterator<Item=Self>>(iter: I) -> Self {
        let mut total = Expr::con(T::from_usize(0));
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
        }
    }
}

impl<T: Scalar> Debug for Expr<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result { Display::fmt(self, f) }
}

impl<T: Scalar> Functional<T> for Expr<T> {
    fn var() -> Self { Self::poly([(1, T::from_isize(1))].into_iter().collect()) }
    fn con(x: T) -> Self { Self::poly([(0, x)].into_iter().collect()) }
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
