#![allow(unused_imports)]

use builtin::*;
use builtin_macros::*;

use crate::option::*;
use crate::types::*;
use crate::client::*;

verus! {

/* Functional style is required.
    1. Predicate style does not work, because we need to reason about mutability
    2. Imperative style does not work, because of verus constraints. E.g. need to talk about &mut
    

  General properties:
  1. Non-duplication: 
        self.somebody_has_lock() ==> self.in_flight_lock.is_None() 
        At most one server has lock (safety)
  2. Non-destruction:
        self.in_flight_lock.is_None()  ==> self.somebody_has_lock(). Note that this is not needed for this proof
*/

pub struct System {
    pub node0: Client,
    pub node1: Client,
    pub n: nat,
    pub in_flight_lock: Option<Lock>,
}

impl System {

    // Constructor
    pub proof fn initialize() -> (sys: System) 
        ensures 
            sys.inv()
    {
        System {
            node0: Client::initialize(0),
            node1: Client::initialize(1),
            n: 2,
            in_flight_lock: Option::None,
        }
    }

    pub proof fn next_one_node_grant(tracked self, actor: int) -> (system_next: System)
        requires 
            0 <= actor < self.n,
            self.inv(),
        ensures 
            system_next.inv()
    {
        if actor == 0 {
            let ClientLockPair{ s: node0_next, l: lock_opt } = 
                    tracked self.node0.grant();
            if lock_opt.is_Some() {
                let res = System {
                    node0: node0_next,
                    node1: self.node1,
                    n: self.n,
                    in_flight_lock: lock_opt,
                };
                
                assert(res.wf());
                assert(res.safety());
                assert(res.in_flight_lock_property());

                return res
            } else {
                return self;
            }
        } else {
            let tracked  ClientLockPair{ s: node1_next, l: lock_opt } = 
                    tracked self.node1.grant();
            if lock_opt.is_Some() {
                return System {
                    node0: self.node0,
                    node1: node1_next,
                    n: self.n,
                    in_flight_lock: lock_opt,
                };
            } else {
                return self;
            }
        }
    }

    pub proof fn next_one_node_accept(tracked self, actor: int) -> (system_next: System)
        requires 
            0 <= actor < self.n,
            self.inv(),
        ensures 
            system_next.inv()
    {
        if actor == 0 {
            let tracked ClientLockPair{ s: node0_next, l: lock_opt } = 
                    tracked self.node0.accept(self.in_flight_lock);
            return System {
                node0: node0_next,
                node1: self.node1,
                n: self.n,
                in_flight_lock: lock_opt,
            };
        } else {
            let tracked ClientLockPair{ s: node1_next, l: lock_opt } = 
                    tracked self.node1.accept(self.in_flight_lock);
            return System {
                node0: self.node0,
                node1: node1_next,
                n: self.n,
                in_flight_lock: lock_opt,
            };
        }
    }

    pub proof fn system_next(tracked self, actor: int, grant_step: bool) -> (system_next: System)
        requires 
            0 <= actor < self.n,
            self.inv(),
        ensures 
            system_next.inv()
    {
        if grant_step {
            tracked self.next_one_node_grant(actor)
        } else {
            tracked self.next_one_node_accept(actor)
        }
    }

    /*************************************************************************************
    *                                    Properties                                      *
    *************************************************************************************/
    pub open spec fn wf(self) -> bool {
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
        // this is actually implied by the general non-duplication property
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