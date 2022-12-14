use builtin::*;

use builtin_macros::*;

#[allow(unused_imports)]
use crate::option::*;
use crate::types::*;


verus! {

pub struct Server {
    pub id: Id,
    pub token: Option<Lock>,
    pub epoch: nat,
    pub n: nat,
}

impl Server {

    // Constructor
    pub proof fn initialize(my_id: Id, size: nat) -> (s: Server) 
        // ensures wf()
    {
        let lock = Lock{};
        Server {
            id: my_id,
            token: if my_id == 0 {Option::Some(lock)} else {Option::None},
            epoch: if my_id == 0 {1} else {0},
            n: size,
        }
    }

    pub proof fn new() -> Server {
        Server {
            id: 0,
            token: Option::None,
            epoch: 0,
            n: 0,
        }
    }

    pub proof fn grant(&mut self) -> Option<Lock>
    {
        if self.has_lock() {
            let mut lock = self.token.get_Some_0();
            self.token = Option::None;
            Option::Some(lock)
        } else {
            Option::None
        }
    }

    pub proof fn accept(&mut self, lock: Lock, new_epoch: nat)

    {
        if new_epoch > self.epoch && self.token.is_None() {
            self.token = Option::Some(lock);
            self.epoch = new_epoch;
        }
    } 

    pub open spec fn has_lock(self) -> bool {
        self.token.is_Some()
    }
}


/*************************************************************************************
*                                    Properties                                      *
*************************************************************************************/

pub open spec fn init_node_0_has_lock(s: Server) -> bool {
    s.has_lock() <==> s.id == 0
}


}  // verus!