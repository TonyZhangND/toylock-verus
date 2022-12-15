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
            sys.wf(),
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
            old(self).wf(),
        ensures 
            self.wf()
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
        requires 
            0 <= actor < old(self).n,
            old(self).wf(),
        ensures 
            self.wf()
    {
        let mut server;
        if actor == 0 {
            server = self.node0;
        } else {
            server = self.node1;
        }
        server.accept(self.in_flight_lock, self.curr_epoch);
    }

    pub proof fn system_next(&mut self, actor: int, grant_step: bool) 
        requires 
            0 <= actor < old(self).n,
            old(self).wf(),
        ensures 
            self.wf()
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

} // impl System

pub open spec fn safety(sys: &System) -> bool {
    ! (sys.node0.has_lock() && sys.node1.has_lock())
}

pub open spec fn in_flight_lock_property(sys: &System) -> bool {
    somebody_has_lock(sys) ==> sys.in_flight_lock.is_None()
}

// pub proof fn inv_init(size: nat)
//     ensures inv(System::initialize(size))
// {}

// pub proof fn inv_next(sys: System, actor: int, grant_step: bool)
//     requires 
//         inv(sys),
//         0 <= actor < sys.n,
//     ensures inv(sys.system_next(actor, grant_step))
// {}


/*****************************************************************************************
*                                        Utils                                           *
*****************************************************************************************/

pub open spec fn nobody_has_lock(sys: &System) -> bool {
    ! somebody_has_lock(sys)
}

pub open spec fn somebody_has_lock(sys: &System) -> bool {
    sys.node0.has_lock() || !sys.node1.has_lock()
}


}  // verus!