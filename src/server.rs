use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;

#[allow(unused_imports)]
use crate::option::*;
use crate::types::*;
use crate::environment::*;


verus! {
state_machine!{ Server {
    fields { 
        pub id: Id,
        pub has_lock: bool,
        pub epoch: nat,
        pub n: nat,
    }

    init!{ 
        Init(my_id: Id, size: nat) {
            init id = my_id;
            init n = size;
            if my_id == 0 {
                init has_lock = true;
                init epoch = 1;
            } else {
                init has_lock = false;
                init epoch = 0;
            }
        }
    }

    transition!{
        grant(recv_io: IoOpt, send_io: IoOpt) {
            require recv_io.is_None();
            require pre.has_lock;
            require send_io === Option::Some(Packet{
                src: pre.id,
                dst: (pre.id + 1) % (pre.n as int),
                msg: Message::Grant{ epoch: pre.epoch + 1 }
            });
            update has_lock = false;
        }
    }

    transition!{
        accept(recv_io: IoOpt, send_io: IoOpt) {
            require !pre.has_lock;
            require send_io.is_None();
            require recv_io.is_Some();
            let pkt = recv_io.get_Some_0();
            require pkt.dst == pre.id;
            require pkt.msg.is_Grant();
            require pkt.msg.get_Grant_epoch() > pre.epoch;
            update has_lock = true;
            update epoch = pkt.msg.get_Grant_epoch();
        }
    }
}}
}