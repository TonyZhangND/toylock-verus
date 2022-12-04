#[allow(unused_imports)]
use builtin::*;

use builtin_macros::*;

verus! {

pub type Id = nat;

pub struct Packet {
    pub src: nat,
    pub dst: nat,
    pub epoch: nat,
    pub token: Lock,
}

pub struct Lock {}
}