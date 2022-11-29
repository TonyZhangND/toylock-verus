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
            require Environment::State::next_by(pre.env, new_env, env_step);  // In verus, constraints on next state must be done using require clauses
            
            // Transition the actor node from s to s'
            require State::transition_actor(pre.nodes, new_nodes, actor, recv_io, send_io, node_step);

            // Updates
            update env = new_env;
            update nodes = new_nodes;
        }
    }


    /*************************************************************************************
    *                                   Invariants                                       *
    *************************************************************************************/

    #[invariant]
    pub fn wf(self) -> bool {
        &&& Seq::len(self.nodes) == self.n
        &&& forall|i: int|#![auto] 0 <= i < self.n ==> self.nodes[i].n === self.n
        &&& forall|i: int|#![auto] 0 <= i < self.n ==> self.nodes[i].id === i as nat
        &&& forall |p:Packet| self.env.sent_packets.contains(p) ==> 0 <= p.dst < self.n
    }

    #[invariant]
    pub fn safety(self) -> bool {
        forall|i:int, j:int|  #![auto] 0 <= i < self.n && 0 <= j < self.n ==> (
            self.nodes[i].has_lock && self.nodes[j].has_lock
            ==> i == j
        )
    }
    
    #[invariant]
    pub open spec fn grant_epoch_inv(self) -> bool {
        forall |p1:Packet, p2:Packet| #![auto]
            self.env.sent_packets.contains(p1) && 
            self.env.sent_packets.contains(p2) && 
            p1.epoch > self.nodes[p1.dst as int].epoch &&
            p2.epoch > self.nodes[p2.dst as int].epoch
        ==>
            p1 === p2
    }

    #[invariant]
    pub open spec fn grant_epoch_existence_inv(self) -> bool {
        (exists|p:Packet| #![auto]
            self.env.sent_packets.contains(p) && 
            0 <= p.dst < self.n && 
            p.epoch > self.nodes[p.dst as int].epoch
        )
        ==>
        self.nobody_has_lock()
    }

    /*************************************************************************************
    *                                     Proofs                                         *
    *************************************************************************************/

    #[inductive(initialize)]
    pub fn init_inv(post: Self, 
        size: nat, init_env: Environment::State, env_config: Environment::Config, 
        init_nodes: Seq<Server::State>, node_configs: Seq<Server::Config>) 
    {
        State::lemma_init_wf(post, size, init_env, env_config, init_nodes, node_configs);

        // Prove safety
        assert forall|i:int, j:int| 0 <= i < size && 0 <= j < size ==> 
            #[trigger] post.nodes[i].has_lock && #[trigger] post.nodes[j].has_lock
            ==> i == j
        by {
            if 0 <= i < size && 0 <= j < size && post.nodes[i].has_lock && post.nodes[j].has_lock {
                reveal(Server::State::init_by);
                assert(node_configs[i] === Server::Config::initialize(i as nat, size));  // trigger
            }
        }
        
        // Prove grant_epoch_inv and grant_epoch_existence_inv
        reveal(Environment::State::init_by);
    }

    // Prove that init ensures well-formed
    proof fn lemma_init_wf(post: Self, 
        size: nat, init_env: Environment::State, env_config: Environment::Config, 
        init_nodes: Seq<Server::State>, node_configs: Seq<Server::Config>)
        requires State::initialize(post, size, init_env,
            env_config, init_nodes,
            node_configs)
        ensures
            post.wf()
    {
        reveal(State::init_by);   // init_by is opaque
        assert forall |i: nat| 0 <= i < size ==> #[trigger] post.nodes[i as int].n == size
        by {
            if 0 <= i < size {
                let conf_i = Server::Config::initialize(i as nat, size);
                assert(node_configs[i as int] === conf_i);  // trigger

                if let Server::Config::initialize(idx, size_i) = conf_i {
                    reveal(Server::State::init_by);
                }
            }
        }
        assert forall |i: nat| 0 <= i < size ==> #[trigger] post.nodes[i as int].id === i
        by {
            if 0 <= i < size {
                let conf_i = Server::Config::initialize(i as nat, size);
                assert(node_configs[i as int] === conf_i);  // trigger
                if let Server::Config::initialize(idx, size_i) = conf_i {
                    reveal(Server::State::init_by);
                }
            }
        }
        assert forall |p:Packet| post.env.sent_packets.contains(p) ==> 0 <= p.dst < post.n by {
            reveal(Environment::State::init_by);
        }
    }

    #[inductive(system_next)]
    fn system_next_inductive(pre: Self, post: Self, 
        step: EnvStep, new_env: Environment::State, env_step: Environment::Step, 
        new_nodes: Seq<Server::State>, node_step: Server::Step) 
    { 
        State::lemma_next_wf(pre, post, step, new_env, env_step, new_nodes, node_step);
        State::lemma_next_safety(pre, post, step, new_env, env_step, new_nodes, node_step);
        State::lemma_next_grant_epoch_inv(pre, post, step, new_env, env_step, new_nodes, node_step);
        State::lemma_next_grant_epoch_existence_inv(pre, post, step, new_env, env_step, new_nodes, node_step);
        reveal(Server::State::next_by);
    }

    // Prove that next preserves well-formed
    proof fn lemma_next_wf(pre: Self, post: Self, 
        step: EnvStep, new_env: Environment::State, env_step: Environment::Step, 
        new_nodes: Seq<Server::State>, node_step: Server::Step) 
        requires
            pre.invariant(),
            State::system_next_strong(pre, post,
                                  step, new_env, env_step, new_nodes, node_step)
        ensures
            post.wf()
    {
        reveal(State::next_by);
        reveal(Server::State::next_by);
        reveal(Environment::State::next_by);
    }

    // Prove that next preserves grant_epoch_inv
    proof fn lemma_next_grant_epoch_inv(pre: Self, post: Self, 
        step: EnvStep, new_env: Environment::State, env_step: Environment::Step, 
        new_nodes: Seq<Server::State>, node_step: Server::Step) 
        requires
            pre.invariant(),
            State::system_next_strong(pre, post,
                                  step, new_env, env_step, new_nodes, node_step)
        ensures
            post.grant_epoch_inv()
    {
        reveal(Environment::State::next_by);
        reveal(Server::State::next_by);
    }

    // Prove that next preserves grant_epoch_inv
    proof fn lemma_next_grant_epoch_existence_inv(pre: Self, post: Self, 
        step: EnvStep, new_env: Environment::State, env_step: Environment::Step, 
        new_nodes: Seq<Server::State>, node_step: Server::Step) 
        requires
            pre.invariant(),
            State::system_next_strong(pre, post,
                                  step, new_env, env_step, new_nodes, node_step)
        ensures
            post.grant_epoch_existence_inv()
    {
        reveal(Environment::State::next_by);
        reveal(Server::State::next_by);
    }

    // Prove that next preserves safety
    proof fn lemma_next_safety(pre: Self, post: Self, 
        step: EnvStep, new_env: Environment::State, env_step: Environment::Step, 
        new_nodes: Seq<Server::State>, node_step: Server::Step) 
        requires
            pre.invariant(),
            State::system_next_strong(pre, post,
                                  step, new_env, env_step, new_nodes, node_step)
        ensures
            post.safety()
    {
        /* Two cases:
            1. No one holds lock in pre. Then we are golden
            2. Someone holds lock in pre. Then by grant_epoch_existence_inv in pre,
                no one can acquire lock in post
            But apparently, automation is so good that I don't need manual analysis...
        */
            reveal(Environment::State::next_by);
            reveal(Server::State::next_by);
    }


    /*************************************************************************************
    *                                      Utils                                         *
    *************************************************************************************/

    pub open spec fn nobody_has_lock(self) -> bool {
        forall |i:int|  #![auto] 0 <= i < self.n ==> !self.nodes[i].has_lock
    }

    pub open spec fn somebody_has_lock(self) -> bool {
        exists |i:int|  #![auto] 0 <= i < self.n && self.nodes[i].has_lock
    }
}}
}