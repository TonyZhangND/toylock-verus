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

pub struct ServerLockPair {
    pub s: Server,
    pub l: Option<Lock>,
}

impl Server {

    // Constructor
    pub proof fn initialize(my_id: Id, size: nat) -> (s: Server) 
        ensures init_node_0_has_lock(s),
                s.id == my_id,
                s.n == size,
    {
        let lock = Lock{};
        Server {
            id: my_id,
            token: if my_id == 0 {Option::Some(lock)} else {Option::None},
            epoch: if my_id == 0 {1} else {0},
            n: size,
        }
    }

    // TONY: I am doing this slp pair thing just so I can talk about the return value in 
    // the pre/post-conditions. Otherwise, I cannot name both items in a tuple return value
    pub proof fn grant(self) -> (slp: ServerLockPair)
        ensures 
            self.id == slp.s.id,
            self.n == slp.s.n,
            !slp.s.has_lock(),
            !self.has_lock() ==> slp.l.is_None()
    {
        if self.has_lock() {
            if let Option::Some(lock) = self.token {
                let new_server = Server {   // creating new server because verus does not allow &mut self in spec functions
                    id: self.id,
                    token: Option::None,
                    epoch: self.epoch,
                    n: self.n,
                };
                return ServerLockPair{s: new_server, l: Option::Some(lock)};
            }
            return ServerLockPair{s: self, l: Option::None};
        } else {
            return ServerLockPair{s: self, l: Option::None};
        }
    }

    pub proof fn accept(self, in_flight_lock: Option<Lock>, new_epoch: nat) -> (slp: ServerLockPair)
        ensures 
            self.id == slp.s.id,
            self.n == slp.s.n,
            self.token.is_None() && slp.s.token.is_Some() ==> slp.l.is_None(),
            in_flight_lock.is_None() ==> slp.l.is_None() && slp.s.token === self.token
    {
        if in_flight_lock.is_Some() && new_epoch > self.epoch && self.token.is_None() {
            if let Option::Some(lock) = in_flight_lock {
                let new_server = Server {
                    id: self.id,
                    token: Option::Some(lock),
                    epoch: new_epoch,
                    n: self.n,
                };
                return ServerLockPair{s: new_server, l: Option::None};
            }
            return ServerLockPair{s: self, l: Option::None};
        }
        return ServerLockPair{s: self, l: in_flight_lock};
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