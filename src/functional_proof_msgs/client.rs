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

pub struct ClientMsgPair {
    pub c: Client,
    pub m: Option<Message>,
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

    pub proof fn grant(self) -> (cmp: ClientMsgPair)
    {
        if let Option::Some(lock) = self.token {
            let new_client = Client {
                id: self.id,
                token: Option::None,
            };
            let msg = Message::Release{ src: self.id, lock: lock };
            return ClientMsgPair{ c: new_client, m: Option::Some(msg) };
        } else {
            return ClientMsgPair{ c: self, m: Option::None};
        }
    }

    pub proof fn accept(self, msg: Message) -> (cmp: ClientMsgPair)
    {
        if let Message::Grant {dst: dst, lock: lock} = msg {
            if dst == self.id {
                let new_client = Client {
                    id: self.id,
                    token: Option::Some(lock),
                };
                return ClientMsgPair{c: new_client, m: Option::None};
            } 
        }
        return ClientMsgPair{c: self, m: Option::None};
    }

    pub open spec fn has_lock(self) -> bool {
        self.token.is_Some()
    }
}

}  // verus!