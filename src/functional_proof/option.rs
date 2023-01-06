#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

verus!{

pub enum Option<T> {
    None,
    Some(T)
}

impl <T> Option<T> {
    pub open spec fn is_None(self) -> bool {
        match self {
            Option::Some(_) => false,
            Option::None => true,
        }
    }

    pub open spec fn is_Some(self) -> bool {
        ! self.is_None()
    }
}

}