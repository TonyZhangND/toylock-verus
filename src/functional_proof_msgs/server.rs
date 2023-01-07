#[allow(unused_imports)]
use builtin::*;

use builtin_macros::*;

use crate::option::*;
use crate::types::*;


verus! {

pub struct Server {
    pub num_clients: nat,
    pub token: Option<Lock>,
}

pub struct ServerMsgPair {
    pub s: Server,
    pub m: Option<Message>,
}

impl Server {

    // Constructor
    pub proof fn initialize(n: nat) -> (s: Server) 
        ensures 
            s.has_lock(),
            s.num_clients == n,
    {
        let lock = Lock{};
        Server {
            num_clients: n,
            token: Option::Some(lock),
        }
    }

    pub proof fn grant_to_client(self, dst: nat) -> (smp: ServerMsgPair) 
        requires 0 <= dst < self.num_clients
    {
        if let Option::Some(lock) = self.token {
            let new_server = Server {
                num_clients: self.num_clients,
                token: Option::None,
            };
            let msg = Message::Grant{ dst: dst, lock: lock };
            return ServerMsgPair{s: new_server, m: Option::Some(msg)};
        } else {
            return ServerMsgPair{s: self, m: Option::None};
        }
    }

    pub proof fn receive_lock(self, msg: Message) -> (smp: ServerMsgPair) 
    {
        if let Message::Release{ src: _, lock: lock } = msg {
            let new_server = Server {
                num_clients: self.num_clients,
                token: Option::Some(lock),
            };
            return ServerMsgPair{s: new_server, m: Option::None};
        } else {
            return ServerMsgPair{s: self, m: Option::None};
        }
    }

    pub open spec fn has_lock(self) -> bool {
        self.token.is_Some()
    }
}  // impl Server
}  // verus!