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
}

impl System {

    // Constructor
    pub open spec fn initialize(self, size: nat) -> System {
        let nodes = Seq::new(size, |i: int| -> Server { Server::initialize(i as nat, size)});
        System {
            nodes: nodes,
            n: size,
            curr_epoch: 0,
        }
    }

    pub open spec fn next_one_node_grant(self, actor: int) -> (System, Option<Lock>)
        recommends 0 <= actor < self.n
    {
        let old_server = self.nodes.index(actor);
        let (new_server, lock) = old_server.grant();
        let new_nodes = self.nodes.update(actor, new_server);
        let new_system = System {
            nodes: new_nodes,
            n: self.n,
            curr_epoch: old_server.epoch + 1,
        };
        (new_system, Option::Some(lock))
    }

    pub open spec fn next_one_node_accept(self, actor: int, lock: Lock) -> (System, Option<Lock>)
        recommends 0 <= actor < self.n
    {
        let old_server = self.nodes.index(actor);
        let new_server = old_server.accept(lock, self.curr_epoch);
        let new_nodes = self.nodes.update(actor, new_server);
        let new_system = System {
            nodes: new_nodes,
            n: self.n,
            curr_epoch: self.curr_epoch
        };
        (new_system, Option::None)
    }

    pub open spec fn system_next(self, actor: int, grant_step: bool, in_flight_lock: Option<Lock>) -> (System, Option<Lock>) 
        recommends 0 <= actor < self.n
    {
        if grant_step {
            self.next_one_node_grant(actor)
        } else {
            self.next_one_node_accept(actor, in_flight_lock.get_Some_0())
        }
    }
} // impl System


}  // verus!