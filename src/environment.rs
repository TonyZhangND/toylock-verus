#[allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;
#[allow(unused_imports)]
use crate::pervasive::{set::*};

use crate::option::*;
use crate::types::*;

verus! {

pub type IoOpt = Option<Packet>;

pub struct EnvStep {
    pub actor: Id,
    pub recv_io: IoOpt,
    pub send_io: IoOpt,
}

state_machine!{ Network {
    fields { 
        pub sent_packets: Set<Packet>
    }

    init!{ 
        Init() {
            init sent_packets = Set::empty();
        }
    }

    pub open spec fn valid_env_step(step: EnvStep) -> bool {
        &&& step.recv_io.is_Some() ==> step.recv_io.get_Some_0().dst == step.actor
        &&& step.send_io.is_Some() ==> step.send_io.get_Some_0().src == step.actor
    }

    transition!{
        env_next(step: EnvStep) {
            require State::valid_env_step(step);
            require step.recv_io.is_Some() ==> pre.sent_packets.contains(step.recv_io.get_Some_0());
            if step.send_io.is_Some() {
                update sent_packets = pre.sent_packets.insert(step.send_io.get_Some_0());
            }
        }
    }
}}
}