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

pub struct ServerOpResult {
    pub x: bool,
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

    pub proof fn grant_to_client(self, dst: nat) -> (op_res: ServerOpResult) 
        requires 0 <= dst < self.num_clients
        ensures self.preserve_consts(op_res.s)
    {
        if let Option::Some(lock) = self.token {
            let new_server = Server {
                num_clients: self.num_clients,
                token: Option::None,
            };
            let msg = Message::Grant{ dst, lock };
            return ServerOpResult{x: true, s: new_server, m: Option::Some(msg)};
        } else {
            return ServerOpResult{x: false, s: self, m: Option::None};
        }
    }

    pub proof fn receive_lock(self, msg: Message) -> (op_res: ServerOpResult) 
        ensures self.preserve_consts(op_res.s)
    {
        if let Message::Release{ src: _, lock: lock } = msg {
            let new_server = Server {
                num_clients: self.num_clients,
                token: Option::Some(lock),
            };
            return ServerOpResult{x: true, s: new_server, m: Option::None};
        } else {
            return ServerOpResult{x: false, s: self, m: Option::None};
        }
    }

    pub open spec fn has_lock(self) -> bool {
        self.token.is_Some()
    }

    pub open spec fn preserve_consts(self, new_server: Server) -> bool {
        self.num_clients == new_server.num_clients
    }
}  // impl Server
}  // verus!