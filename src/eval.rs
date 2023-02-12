use crate::expr::{Expr, ExprId, ExprImpl};
use crate::once_cell_map::OnceCellMap;
use crate::scalar::Scalar;

pub struct Eval<T: 'static, T2: 'static, F> {
    var: T2,
    upcast: F,
    cache: OnceCellMap<ExprId<T>, T2>,
}

impl<T: Scalar, T2: Scalar, F: Fn(T) -> T2> Eval<T, T2, F> {
    pub fn new(var: T2, upcast: F) -> Self {
        Eval {
            var,
            upcast,
            cache: OnceCellMap::new(),
        }
    }
    pub fn eval(&self, e: &Expr<T>) -> T2 {
        self.cache.get_or_init(e.id(), || match e.imp() {
            ExprImpl::Add(e1, e2) => self.eval(e1) + self.eval(e2),
            ExprImpl::Mul(e1, e2) => self.eval(e1) * self.eval(e2),
            ExprImpl::Sub(e1, e2) => self.eval(e1) - self.eval(e2),
            ExprImpl::Div(e1, e2) => self.eval(e1) / self.eval(e2),
            ExprImpl::Exp(e1) => self.eval(e1).clone().exp(),
            ExprImpl::Neg(e1) => -self.eval(e1),
            ExprImpl::Sqrt(e1) => self.eval(e1).clone().sqrt(),
            ExprImpl::Poly(p) => p
                .iter()
                .map(|(&i, c)| (self.upcast)(c.clone()) * &self.var.clone().powi(i))
                .sum(),
            ExprImpl::Powi(e1, n) => self.eval(e1).clone().powi(*n),
        })
    }
}
