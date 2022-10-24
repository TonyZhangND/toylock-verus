#[allow(unused_imports)]
use builtin::*;

use builtin_macros::*;

verus! {

pub type Id = nat;

#[is_variant]
pub enum Message {
    Grant{ epoch: nat },
    Accept{ epoch: nat },
}

pub struct Packet {
    pub src: nat,
    pub dst: nat,
    pub msg: Message
}
}