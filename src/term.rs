use std::fmt;
use std::fmt::{Debug, Display, Formatter};
use num::{One, Zero};
use crate::scalar::Scalar;

pub struct Term<C, P> {
    pub co: C,
    pub power: P,
}

impl<C: Debug, P: Display + Zero + One + PartialEq> Debug for Term<C, P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.co)?;
        if self.power.is_zero() {
            return Ok(());
        }
        write!(f, "x")?;
        if self.power.is_one() {
            return Ok(());
        }
        let power = format!("{}", self.power);
        for c in power.chars() {
            let cs = match c {
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
                x => x,
            };
            write!(f, "{}", cs)?;
        }
        Ok(())
    }
}

fn print_sum<T: Debug>(f: &mut Formatter<'_>, mut iter: impl Iterator<Item=Option<T>>) -> fmt::Result {
    let mut peek = (&mut iter).take(20).flatten().take(5).peekable();
    while let Some(next) = peek.next() {
        write!(f, "{:?}", next)?;
        if peek.peek().is_some() {
            write!(f, " + ")?;
        }
    }
    if let Some(_) = iter.next() {
        write!(f, " + ...")?;
    }
    Ok(())
}

impl<C: Scalar, P: Display + Zero + One + PartialEq> Term<C, P> {
    pub fn print_series(f: &mut Formatter<'_>, iter: impl Iterator<Item=Self>) -> fmt::Result {
        print_sum(f, iter.map(|x| if x.co.is_zero() { None } else { Some(x) }))
    }
}


