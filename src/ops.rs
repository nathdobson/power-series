
macro_rules! impl_op_by_value {
    (impl < [ $($TypeArgs:tt)*  ] > $TraitName:ident for [$($TypeName:tt)*] {
        type $AssocName:ident = $AssocValue:ty;
        fn $method_name:ident($self_id:ident, $rhs:ident : Self);
    }) => {
        impl <$($TypeArgs)*> $TraitName<$($TypeName)*> for &$($TypeName)* {
            type $AssocName = $AssocValue;
            fn $method_name($self_id, $rhs: $($TypeName)*) -> $($TypeName)* {
                $TraitName::$method_name(::std::clone::Clone::clone($self_id), $rhs)
            }
        }
        impl <$($TypeArgs)*> $TraitName<&$($TypeName)*> for $($TypeName)* {
            type $AssocName = $AssocValue;
            fn $method_name($self_id, $rhs: &$($TypeName)*) -> $($TypeName)* {
                $TraitName::$method_name($self_id, ::std::clone::Clone::clone($rhs))
            }
        }
        impl <$($TypeArgs)*> $TraitName<&$($TypeName)*> for &$($TypeName)* {
            type $AssocName = $AssocValue;
            fn $method_name($self_id, $rhs: &$($TypeName)*) -> $($TypeName)* {
                $TraitName::$method_name(::std::clone::Clone::clone($self_id), ::std::clone::Clone::clone($rhs))
            }
        }
    };
    (impl < [ $($TypeArgs:tt)*  ] > $TraitName:ident for [$($TypeName:tt)*] {
        type $AssocName:ident = $AssocValue:ty;
        fn $method_name:ident($self_id:ident);
    }) => {
        impl <$($TypeArgs)*> $TraitName for &$($TypeName)* {
            type $AssocName = $AssocValue;
            fn $method_name($self_id) -> $($TypeName)* {
                $TraitName::$method_name(::std::clone::Clone::clone($self_id))
            }
        }
    };
}


macro_rules! impl_ops_by_value {
    (
        impl < [ $($TypeArgs:tt)*  ] > [$($TypeName:tt)*];
    ) => {
        $crate::ops::impl_op_by_value!{
            impl < [ $($TypeArgs)*  ] > Add for [$($TypeName)*] {
                type Output = $($TypeName)*;
                fn add(self, rhs: Self);
            }
        }
        $crate::ops::impl_op_by_value!{
            impl < [ $($TypeArgs)*  ] > Mul for [$($TypeName)*] {
                type Output = $($TypeName)*;
                fn mul(self, rhs: Self);
            }
        }
        $crate::ops::impl_op_by_value!{
            impl < [ $($TypeArgs)*  ] > Sub for [$($TypeName)*] {
                type Output = $($TypeName)*;
                fn sub(self, rhs: Self);
            }
        }
        $crate::ops::impl_op_by_value!{
            impl < [ $($TypeArgs)*  ] > Div for [$($TypeName)*] {
                type Output = $($TypeName)*;
                fn div(self, rhs: Self);
            }
        }
        $crate::ops::impl_op_by_value!{
            impl < [ $($TypeArgs)*  ] > Neg for [$($TypeName)*] {
                type Output = $($TypeName)*;
                fn neg(self);
            }
        }
        // impl < $($TypeArgs)*  > ::num_traits::pow::Pow<usize> for $($TypeName)* {
        //     type Output = $($TypeName)*;
        //     fn pow(self, rhs:usize) -> $($TypeName)*{
        //         ::num_traits::pow::Pow::<isize>::pow(self, rhs as isize)
        //     }
        // }
        // impl < $($TypeArgs)*  > ::num_traits::pow::Pow<usize> for &$($TypeName)* {
        //     type Output = $($TypeName)*;
        //     fn pow(self, rhs:usize) -> $($TypeName)*{
        //         ::num_traits::pow::Pow::<usize>::pow(::std::clone::Clone::clone(self), rhs)
        //     }
        // }
        // impl < $($TypeArgs)*  > ::num_traits::pow::Pow<isize> for &$($TypeName)* {
        //     type Output = $($TypeName)*;
        //     fn pow(self, rhs:isize) -> $($TypeName)*{
        //         ::num_traits::pow::Pow::<isize>::pow(::std::clone::Clone::clone(self), rhs)
        //     }
        // }
    }
}

pub(crate) use impl_op_by_value;
pub(crate) use impl_ops_by_value;
