use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;
#[allow(unused_imports)]
use crate::pervasive::{seq::*};

use crate::environment::*;
use crate::server::*;

verus! {
state_machine!{ System {
    fields {
        pub env: Environment::State,
        pub nodes: Seq<Server::State>,
    }

    pub open spec fn init_servers(
        size: nat, init_nodes: Seq<Server::State>, node_configs: Seq<Server::Config>
    ) -> bool {
        &&& Seq::len(init_nodes) == size
        &&& Seq::len(node_configs) == size
        &&& forall|i: int|#![auto] 0 <= i < size ==> node_configs[i] === Server::Config::Init(i, size)
        &&& forall|i: int|#![auto] 0 <= i < size ==> Server::State::init_by(init_nodes[i], node_configs[i])
    }

    init!{
        Init(size: nat, 
            init_env: Environment::State, env_config: Environment::Config,
            init_nodes: Seq<Server::State>, node_configs: Seq<Server::Config>, 
        ) {
            require Environment::State::init_by(init_env, env_config);
            require State::init_servers(size, init_nodes, node_configs);
            init env = init_env;
            init nodes = init_nodes;
        }
    }
}}
}