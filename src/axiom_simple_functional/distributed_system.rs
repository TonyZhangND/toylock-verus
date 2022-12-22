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
    pub proof fn initialize() -> (sys: System) 
        ensures 
            sys.inv()
    {
        System {
            node0: Server::initialize(0, 2),
            node1: Server::initialize(1, 2),
            n: 2,
            curr_epoch: 0,
            in_flight_lock: Option::None,
        }
    }

    pub proof fn next_one_node_grant(&mut self, actor: int)
        requires 
            0 <= actor < old(self).n,
            old(self).inv(),
        ensures 
            self.inv()
    {
        if actor == 0 {
            let ServerLockPair{ s: node0_next, l: lock_opt } = self.node0.grant();
            if lock_opt.is_Some() {
                self.curr_epoch = self.node0.epoch + 1;
                self.in_flight_lock = lock_opt;
                self.node0 = node0_next;
            }
        } else {
            let ServerLockPair{ s: node1_next, l: lock_opt } = self.node1.grant();
            if lock_opt.is_Some() {
                self.curr_epoch = self.node1.epoch + 1;
                self.in_flight_lock = lock_opt;
                self.node1 = node1_next;
            }
        }
    }

    pub proof fn next_one_node_accept(&mut self, actor: int)
        requires 
            0 <= actor < old(self).n,
            old(self).inv(),
        ensures 
            self.inv()
    {
        if actor == 0 {
            let ServerLockPair{ s: node0_next, l: lock_opt } = self.node0.accept(self.in_flight_lock, self.curr_epoch);
            self.node0 = node0_next;
            self.in_flight_lock = lock_opt;
        } else {
            let ServerLockPair{ s: node1_next, l: lock_opt } = self.node1.accept(self.in_flight_lock, self.curr_epoch);
            self.node1 = node1_next;
            self.in_flight_lock = lock_opt;
        }
    }

    pub proof fn system_next(&mut self, actor: int, grant_step: bool) 
        requires 
            0 <= actor < old(self).n,
            old(self).inv(),
        ensures 
            self.inv()
    {
        if grant_step {
            self.next_one_node_grant(actor)
        } else {
            self.next_one_node_accept(actor)
        }
    }

    /*************************************************************************************
    *                                    Properties                                      *
    *************************************************************************************/
    pub open spec fn wf(self) -> bool {
        &&& self.node0.n == self.n
        &&& self.node1.n == self.n
        &&& self.node0.id == 0
        &&& self.node1.id == 1
    }

    pub open spec fn inv(self) -> bool {
        &&& self.wf()
        &&& self.safety()
        &&& self.in_flight_lock_property()
    }

    pub open spec fn safety(self) -> bool {
        ! (self.node0.has_lock() && self.node1.has_lock())
    }

    pub open spec fn in_flight_lock_property(self) -> bool {
        self.somebody_has_lock() ==> self.in_flight_lock.is_None()
    }

    pub open spec fn nobody_has_lock(self) -> bool {
        ! self.somebody_has_lock()
    }
    
    pub open spec fn somebody_has_lock(self) -> bool {
        self.node0.has_lock() || self.node1.has_lock()
    }

} // impl System
}  // verus!