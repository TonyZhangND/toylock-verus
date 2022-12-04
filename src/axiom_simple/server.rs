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

    pub open spec fn initialize(self, my_id: Id, size: nat) -> Server {
        Server {
            id: my_id,
            token: if my_id == 0 {Option::Some(Lock{})} else {Option::None},
            epoch: if my_id == 0 {1} else {0},
            n: size,
        }
    }

    pub open spec fn grant(self) -> (Server, Lock)
        recommends self.token.is_Some()
    {
        let lock = self.token.get_Some_0();
        let new_server = Server {   // creating new server because verus does not allow &mut self in spec functions
            id: self.id,
            token: Option::None,
            epoch: self.epoch,
            n: self.n,
        };
        (new_server, lock)
    }

    pub open spec fn accept(self, lock: Lock, new_epoch: nat) -> Server 
        recommends self.token.is_None()
    {
        if new_epoch <= self.epoch {
            self
        } else {
            let new_server = Server {
                id: self.id,
                token: Option::Some(lock),
                epoch: new_epoch,
                n: self.n,
            };
            new_server
        }
    } 
}

}  // verus!