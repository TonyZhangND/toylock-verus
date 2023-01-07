#[allow(unused_imports)]
use builtin::*;

use builtin_macros::*;

verus! {

pub type Id = nat;

pub struct Lock {}

pub enum Message {
    Release { src: Id, lock: Lock },
    Grant { dst: Id, lock: Lock }
}

impl Message {
    pub open spec fn is_Grant(self) -> bool {
        match self {
            Message::Release{src: _, lock: _} => false,
            Message::Grant{dst: _, lock: _} => true,
        }
    }

    pub open spec fn is_Release(self) -> bool {
        ! self.is_Grant()
    }
}

} // verus!