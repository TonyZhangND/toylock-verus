#![allow(unused_imports)]

use builtin::*;
use builtin_macros::*;
use crate::pervasive::{seq::*};

use crate::option::*;
use crate::types::*;
use crate::server::*;

verus! {

pub struct System {
    pub nodes: Seq<Server>,
    pub n: nat,
    pub curr_epoch: nat,
    pub in_flight_lock: Option<Lock>,
}

impl System {

    // Constructor
    pub open spec fn initialize(size: nat) -> System {
        let nodes = Seq::new(size, |i: int| -> Server { Server::initialize(i as nat, size)});
        System {
            nodes: nodes,
            n: size,
            curr_epoch: 0,
            in_flight_lock: Option::None,
        }
    }

    pub open spec fn next_one_node_grant(self, actor: int) -> System
        recommends 0 <= actor < self.n
    {
        let old_server = self.nodes.index(actor);
        let (new_server, lock_opt) = old_server.grant();
        let new_nodes = self.nodes.update(actor, new_server);
        let new_system = System {
            nodes: new_nodes,
            n: self.n,
            curr_epoch: old_server.epoch + 1,
            in_flight_lock: lock_opt,
        };
        new_system
    }

    pub open spec fn next_one_node_accept(self, actor: int) -> System
        recommends 0 <= actor < self.n
    {
        if self.in_flight_lock.is_None() {
            self
        } else {
            let old_server = self.nodes.index(actor);
            let new_server = old_server.accept(self.in_flight_lock.get_Some_0(), self.curr_epoch);
            let new_nodes = self.nodes.update(actor, new_server);
            let new_system = System {
                nodes: new_nodes,
                n: self.n,
                curr_epoch: self.curr_epoch,
                in_flight_lock: Option::None,
            };
            new_system
        }
    }

    pub open spec fn system_next(self, actor: int, grant_step: bool) -> System 
        recommends 0 <= actor < self.n
    {
        if grant_step {
            self.next_one_node_grant(actor)
        } else {
            self.next_one_node_accept(actor)
        }
    }
} // impl System


/****************************************************************************************
 *                            Proof without linearity axiom                             *
*****************************************************************************************/

/*
* In the non-linear world, proving safety would require one invariant:
*   1. If a node holds the lock, then in_flight_lock is None
*/

pub open spec fn inv(sys: System) -> bool {
    &&& wf(sys)
    &&& safety(sys)
    &&& in_flight_lock_property(sys)
}

pub open spec fn wf(sys: System) -> bool {
    &&& Seq::len(sys.nodes) == sys.n
    &&& forall|i: int|#![auto] 0 <= i < sys.n ==> sys.nodes[i].n === sys.n
    &&& forall|i: int|#![auto] 0 <= i < sys.n ==> sys.nodes[i].id === i as nat
}

pub open spec fn safety(sys: System) -> bool {
    forall|i:int, j:int|  #![auto] 
        0 <= i < sys.n && 0 <= j < sys.n &&
        sys.nodes[i].has_lock() && sys.nodes[j].has_lock()
        ==> i == j
}

pub open spec fn in_flight_lock_property(sys: System) -> bool {
    somebody_has_lock(sys) ==> sys.in_flight_lock.is_None()
}

pub proof fn inv_init(size: nat)
    ensures inv(System::initialize(size))
{}

pub proof fn inv_next(sys: System, actor: int, grant_step: bool)
    requires 
        inv(sys),
        0 <= actor < sys.n,
    ensures inv(sys.system_next(actor, grant_step))
{}


/****************************************************************************************
 *                             Proof with linearity axiom                               *
*****************************************************************************************/


pub open spec fn inv_linear(sys: System) -> bool {
    &&& wf(sys)
    &&& safety(sys)
}

pub open spec fn linearity_axiom(sys: System) -> bool {
    &&& sys.in_flight_lock.is_Some() ==> nobody_has_lock(sys)
    &&& safety(sys)
}

pub proof fn inv_init_linear(size: nat)
    ensures inv_linear(System::initialize(size))
{}

pub proof fn inv_next_linear(sys: System, actor: int, grant_step: bool)
    requires 
        inv_linear(sys),
        0 <= actor < sys.n,
        linearity_axiom(sys),
        linearity_axiom(sys.system_next(actor, grant_step))
    ensures inv_linear(sys.system_next(actor, grant_step))
{}

/*************************************************************************************
*                                      Utils                                         *
*************************************************************************************/

pub open spec fn nobody_has_lock(sys: System) -> bool {
    forall |i:int|  #![auto] 0 <= i < sys.n ==> !sys.nodes[i].has_lock()
}

pub open spec fn somebody_has_lock(sys: System) -> bool {
    exists |i:int|  #![auto] 0 <= i < sys.n && sys.nodes[i].has_lock()
}

}  // verus!