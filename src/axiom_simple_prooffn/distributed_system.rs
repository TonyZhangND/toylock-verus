#![allow(unused_imports)]

use builtin::*;
use builtin_macros::*;

use crate::option::*;
use crate::types::*;
use crate::server::*;

verus! {

pub struct System {
    pub node0: Server,
    pub node1: Server,
    pub n: nat,
    pub curr_epoch: nat,
    pub in_flight_lock: Option<Lock>,
}

impl System {

    // Constructor
    pub proof fn initialize() -> System {
        System {
            node0: Server::initialize(0, 2),
            node1: Server::initialize(1, 2),
            n: 2,
            curr_epoch: 0,
            in_flight_lock: Option::None,
        }
    }

    pub proof fn next_one_node_grant(&mut self, actor: int)
        requires 0 <= actor < old(self).n
    {
        let mut sever;
        if actor == 0 {
            sever = self.node0;
        } else {
            sever = self.node1;
        }
        let lock_opt = sever.grant();
        if lock_opt.is_Some() {
            self.curr_epoch = sever.epoch + 1;
            self.in_flight_lock = lock_opt;
        }
    }

    pub proof fn next_one_node_accept(&mut self, actor: int)
        requires 0 <= actor < old(self).n
    {
        if self.in_flight_lock.is_Some() {
            let mut server;
            if actor == 0 {
                server = self.node0;
            } else {
                server = self.node1;
            }
            server.accept(self.in_flight_lock.get_Some_0(), self.curr_epoch);
        }
    }

    pub proof fn system_next(&mut self, actor: int, grant_step: bool) 
        requires 0 <= actor < old(self).n
    {
        if grant_step {
            self.next_one_node_grant(actor)
        } else {
            self.next_one_node_accept(actor)
        }
    }
} // impl System
}  // verus!