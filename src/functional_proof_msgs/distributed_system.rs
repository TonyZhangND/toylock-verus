#![allow(unused_imports)]

use builtin::*;
use builtin_macros::*;

use crate::option::*;
use crate::types::*;
use crate::server::*;
use crate::client::*;
use crate::pervasive::{set::*};

verus! {

pub struct System {
    pub server: Server,
    pub client0: Client, // Tony: have to do this because no support for arrays, and proof mode seqs
    pub client1: Client,
    pub num_clients: nat,
    pub network: Set<Message>,
}

impl System {

    // Constructor
    pub proof fn initialize() -> (sys: System) 
        ensures
            sys.server.has_lock(),
            !sys.client0.has_lock(),
            !sys.client1.has_lock(),
    {
        System {
            server: Server::initialize(2),
            client0: Client::initialize(0), 
            client1: Client::initialize(1),
            num_clients: 2,
            network: Set::empty(),
        }
    }

    // grant_dst and receive_msg are non-deterministic
    pub proof fn next_server(self, grant_dst: nat, release_msg: Message) -> (sys: System)
        requires 
            self.num_clients == self.server.num_clients,
            0 <= grant_dst < self.num_clients,
    {
        if self.server.has_lock() {
            // Server has lock, do grant
            let ServerMsgPair{ s: new_server, m: msg_opt } 
                        = self.server.grant_to_client(grant_dst);
            if let Option::Some(grant_msg) = msg_opt {
                let new_sys = System {
                    server: new_server,
                    network: self.network.insert(grant_msg),
                    ..self
                };
                return new_sys;
            }
            return self;  // stutter
        } else {
            // Server does not have lock, try to do receive
            if self.network.contains(release_msg) {
                let ServerMsgPair{ s: new_server, m: msg_opt } 
                            = self.server.receive_lock(release_msg);
                let new_sys = System {
                    server: new_server,
                    ..self
                };
                return new_sys;
            }
            return self;  // stutter
        }
    }

    pub proof fn next_one_client(self, cid: Id, client: Client, grant_msg: Message) 
    -> (sys: System) 
        requires
            0 <= cid <= self.num_clients,
            cid == 0 ==> client === self.client0,
            cid == 1 ==> client === self.client1,
    {
        if client.has_lock() {
            // Client has lock, do release 
            let ClientMsgPair{ c: new_client, m: msg_opt } = client.release();
            if let Option::Some(release_msg) = msg_opt {
                if cid == 0 {
                    return System {
                        client0: new_client,
                        network: self.network.insert(release_msg),
                        ..self
                    };
                } else {
                    return System {
                        client1: new_client,
                        network: self.network.insert(release_msg),
                        ..self
                    };
                }
            }
            return self;  // stutter
        } else {
            // Client does not have lock, try do accept
            if self.network.contains(grant_msg) {
                let ClientMsgPair{ c: new_client, m: msg_opt } = client.accept(grant_msg);
                if cid == 0 {
                    return System {
                        client0: new_client,
                        network: self.network.remove(grant_msg),
                        ..self
                    };
                } else {
                    return System {
                        client1: new_client,
                        network: self.network.remove(grant_msg),
                        ..self
                    };
                }
            }
            return self;  // stutter
        }
    }

    pub proof fn system_next(self, 
        cid: Id, server_step: bool, release_msg: Message, grant_msg: Message) 
        -> (system_next: System)
        requires
            0 <= cid < self.num_clients,
            self.num_clients == self.server.num_clients,

    {
        if server_step {
            self.next_server(cid, release_msg)
        } else {
            let mut client: Client;
            if cid == 0 {
                client = self.client0;
            } else {
                client = self.client1;
            }
            self.next_one_client(cid, client, grant_msg) 
        }
    }

    /*************************************************************************************
    *                                    Properties                                      *
    *************************************************************************************/
    // pub open spec fn wf(self) -> bool {
    //     &&& self.node0.id == 0
    //     &&& self.node1.id == 1
    // }

    // pub open spec fn inv(self) -> bool {
    //     &&& self.wf()
    //     &&& self.safety()
    //     &&& self.in_flight_lock_property()
    // }

    // pub open spec fn safety(self) -> bool {
    //     ! (self.node0.has_lock() && self.node1.has_lock())
    // }

    // pub open spec fn in_flight_lock_property(self) -> bool {  
    //     // this is actually implied by the general non-duplication property
    //     self.somebody_has_lock() ==> self.in_flight_lock.is_None()
    // }

    // pub open spec fn nobody_has_lock(self) -> bool {
    //     ! self.somebody_has_lock()
    // }
    
    // pub open spec fn somebody_has_lock(self) -> bool {
    //     self.node0.has_lock() || self.node1.has_lock()
    // }

} // impl System
}  // verus!