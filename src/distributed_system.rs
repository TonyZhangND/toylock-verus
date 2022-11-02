use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;
#[allow(unused_imports)]
use crate::pervasive::{seq::*};

#[allow(unused_imports)]
use crate::types::*;
use crate::environment::*;
use crate::server::*;

verus! {
state_machine!{ System {
    fields {
        pub env: Environment::State,
        pub nodes: Seq<Server::State>,
        pub n: nat
    }

    pub open spec fn init_servers(
        size: nat, init_nodes: Seq<Server::State>, node_configs: Seq<Server::Config>
    ) -> bool {
        &&& Seq::len(init_nodes) == size
        &&& Seq::len(node_configs) == size
        &&& forall|i: int|#![auto] 0 <= i < size ==> node_configs[i] === Server::Config::initialize(i as nat, size)
        &&& forall|i: int|#![auto] 0 <= i < size ==> Server::State::init_by(init_nodes[i], node_configs[i])
    }

    init!{
        initialize(size: nat, 
            init_env: Environment::State, env_config: Environment::Config,
            init_nodes: Seq<Server::State>, node_configs: Seq<Server::Config>, 
        ) {
            require Environment::State::init_by(init_env, env_config);
            require State::init_servers(size, init_nodes, node_configs);
            init env = init_env;
            init nodes = init_nodes;
            init n = size;
        }
    }

    pub open spec fn transition_actor(nodes: Seq<Server::State>, new_nodes: Seq<Server::State>,
        actor: Id, recv_io: IoOpt, send_io: IoOpt, node_step: Server::Step,
    ) -> bool {
        let size = Seq::len(nodes);
        &&& Seq::len(new_nodes) == size
        &&& 0 <= actor < Seq::len(nodes)
        // non-actor nodes are unchanged
        &&& forall|i: int|#![auto] 0<=i<size && i!=actor ==> new_nodes[i] === nodes[i]
        // update the actor node
        &&& match node_step {
            Server::Step::grant(rcv, snd) => rcv === recv_io && snd === send_io,
            Server::Step::accept(rcv, snd) => rcv === recv_io && snd === send_io,
            Server::Step::stutter(rcv, snd) => rcv === recv_io && snd === send_io,
            _ => false,
        }
        &&& Server::State::next_by(nodes[actor as int], new_nodes[actor as int], node_step)
    }

    transition!{
        system_next(step: EnvStep, 
            new_env: Environment::State, env_step: Environment::Step,
            new_nodes: Seq<Server::State>, node_step: Server::Step
        ) {
            let actor = step.actor;
            let recv_io = step.recv_io;
            let send_io = step.send_io;
            require Environment::State::valid_env_step(step);
            // Transition the environment from env to env'
            require env_step === Environment::Step::env_next(step);
            require Environment::State::next_by(pre.env, new_env, env_step);
            
            // Transition the actor node from s to s'
            require State::transition_actor(pre.nodes, new_nodes, actor, recv_io, send_io, node_step);

            // Updates
            update env = new_env;
            update nodes = new_nodes;
        }
    }


    #[invariant]
    pub fn wf(self) -> bool {
        &&& Seq::len(self.nodes) == self.n
        &&& forall|i: nat|#![auto] 0 <= i < self.n ==> self.nodes[i as int].n === self.n
        &&& forall|i: nat|#![auto] 0 <= i < self.n ==> self.nodes[i as int].id === i
    }

    #[inductive(initialize)]
    pub fn init_wf(post: Self, 
        size: nat, init_env: Environment::State, env_config: Environment::Config, 
        init_nodes: Seq<Server::State>, node_configs: Seq<Server::Config>) 
    {
        assert forall |i: nat| 0 <= i < size ==> #[trigger] post.nodes[i as int].n == size
        by {
            if 0 <= i < size {
                let conf_i = Server::Config::initialize(i as nat, size);
                assert(node_configs[i as int] === conf_i);  // trigger

                if let Server::Config::initialize(idx, size_i) = conf_i {
                    reveal(Server::State::init_by);   // init_by is opaque
                }
            }
        }
        assert forall |i: nat| 0 <= i < size ==> #[trigger] post.nodes[i as int].id === i
        by {
            if 0 <= i < size {
                let conf_i = Server::Config::initialize(i as nat, size);
                assert(node_configs[i as int] === conf_i);  // trigger
                if let Server::Config::initialize(idx, size_i) = conf_i {
                    reveal(Server::State::init_by);   // init_by is opaque
                }
            }
        }
    }

    #[inductive(system_next)]
    fn system_next_inductive(pre: Self, post: Self, 
        step: EnvStep, new_env: Environment::State, env_step: Environment::Step, 
        new_nodes: Seq<Server::State>, node_step: Server::Step) 
    { 
        assert(pre.n == post.n);
        reveal(Server::State::next_by);
    }
}}
}