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

    pub proof fn grant(&mut self) -> (opt_lock: Option<Lock>)
        ensures 
            self.id == old(self).id,
            self.n == old(self).n,
            !self.has_lock(),
            !old(self).has_lock() ==> opt_lock.is_None()
    {
        if self.has_lock() {
            let mut lock = self.token.get_Some_0();
            self.token = Option::None;
            Option::Some(lock)
        } else {
            Option::None
        }
    }

    pub proof fn accept(&mut self, in_flight_lock: Option<Lock>, new_epoch: nat) -> (opt_lock: Option<Lock>)
        ensures 
            self.id == old(self).id,
            self.n == old(self).n,
            old(self).token.is_None() && self.token.is_Some() ==> opt_lock.is_None(),
            in_flight_lock.is_None() ==> opt_lock.is_None() && self.token === old(self).token
    {
        if in_flight_lock.is_Some() && new_epoch > self.epoch && self.token.is_None() {
            self.token = Option::Some(in_flight_lock.get_Some_0());
            self.epoch = new_epoch;
            return Option::None;
        }
        return in_flight_lock;
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