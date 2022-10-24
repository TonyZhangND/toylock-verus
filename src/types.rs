#[allow(unused_imports)]
use builtin::*;

use builtin_macros::*;

verus! {

pub type Id = int;

#[is_variant]
pub enum Message {
    Grant{ epoch: nat },
    Accept{ epoch: nat },
}

pub struct Packet {
    pub src: Id,
    pub dst: Id,
    pub msg: Message
}
}