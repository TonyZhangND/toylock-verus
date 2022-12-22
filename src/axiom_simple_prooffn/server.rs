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
            let token = self.token;
            if let Option::Some(lock) = token {
                self.token = Option::None;
                return Option::Some(lock);
            }
            return Option::None;
        } else {
            return Option::None;
        }
    }

    // This one should fail linearity check
    // pub proof fn grant_bogus(tracked self) -> (tracked opt_lock: Option<Lock>)
    //     // ensures 
    //     //     self.id == old(self).id,
    //     //     self.n == old(self).n,
    //     //     !self.has_lock(),
    //     //     !old(self).has_lock() ==> opt_lock.is_None()
    // {
    //     if self.has_lock() {
    //         if let Option::Some(lock) = tracked self.token {
    //             /* Note: Can't mutate self.token, so using myLock in its place */
    //             let tracked myLock = tracked Option::Some(lock);
    //             return tracked Option::Some(lock);
    //         }
    //         return Option::None;
    //     } else {
    //         return Option::None;
    //     }
    // }

    pub proof fn accept(&mut self, in_flight_lock: Option<Lock>, new_epoch: nat) -> (opt_lock: Option<Lock>)
        ensures 
            self.id == old(self).id,
            self.n == old(self).n,
            old(self).token.is_None() && self.token.is_Some() ==> opt_lock.is_None(),
            in_flight_lock.is_None() ==> opt_lock.is_None() && self.token === old(self).token
    {
        if in_flight_lock.is_Some() && new_epoch > self.epoch && self.token.is_None() {
            if let Option::Some(lock) = in_flight_lock {
                self.token = Option::Some(lock);
                self.epoch = new_epoch;
            }
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