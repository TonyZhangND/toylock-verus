#[allow(unused_imports)]
use builtin::*;

use builtin_macros::*;

#[allow(unused_imports)]
use crate::option::*;
use crate::types::*;


verus! {

pub struct Client {
    pub id: Id,
    pub token: Option<Lock>,
}

pub struct ClientLockPair {
    pub s: Client,
    pub l: Option<Lock>,
}

impl Client {

    // Constructor
    pub proof fn initialize(my_id: Id) -> (s: Client) 
        ensures 
            s.id == my_id,
            !s.has_lock(),
    {
        let lock = Lock{};
        Client {
            id: my_id,
            token: Option::None,
        }
    }

    // TONY: I am doing this clp pair thing just so I can talk about the return value in 
    // the pre/post-conditions. Otherwise, I cannot name both items in a tuple return value
    pub proof fn grant(tracked self) -> (tracked clp: ClientLockPair)
        ensures 
            clp.s.id == self.id,

            // If I don't have lock initially, I can't conjure locks
            !self.has_lock() ==> !clp.s.has_lock() && clp.l.is_None(),

            // Can't duplicate the lock. This property implies in_flight_lock_property()
            !(clp.s.has_lock() && clp.l.is_Some()),
    {
        if self.has_lock() {
            if let Option::Some(lock) = tracked self.token {
                let tracked new_client = tracked Client {
                    id: self.id,
                    // TONY: How to prevent user from creating new token? Make lock constructor private?
                    token: Option::None,
                };
                return tracked ClientLockPair{s: new_client, l: Option::Some(lock)};
            } else {
                // Note that I have to create a copy of self here, because client is partially moved in the "if-let" statement
                let tracked new_client = tracked Client {
                    id: self.id,
                    token: Option::None,
                };
                return tracked ClientLockPair{s: new_client, l: Option::None};
            }
        } else {
            return tracked ClientLockPair{s: self, l: Option::None};
        }
    }

    pub proof fn accept(tracked self, tracked in_flight_lock: Option<Lock>) 
    -> ( tracked clp: ClientLockPair)
        requires
            // this is the contrapositive of the general non-duplication property
            in_flight_lock.is_Some() ==> !self.has_lock()  
        ensures 
            clp.s.id == self.id,

            // If no lock in the sky initially, then no lock in the sky afterwards,
            // and no change to client
            in_flight_lock.is_None() ==> clp.l.is_None() && clp.s.token === self.token,

            // Can't duplicate the lock. This property implies in_flight_lock_property()
            !(clp.s.has_lock() && clp.l.is_Some()),
    {
        if in_flight_lock.is_Some() {
            if let Option::Some(lock) = tracked in_flight_lock {
                let tracked new_client = tracked Client {
                    id: self.id,
                    token: Option::Some(lock),
                };
                return tracked ClientLockPair{s: new_client, l: Option::None};
            }
            return tracked ClientLockPair{s: self, l: Option::None};
        }
        return tracked ClientLockPair{s: self, l: in_flight_lock};
    }

    pub open spec fn has_lock(self) -> bool {
        self.token.is_Some()
    }
}

}  // verus!