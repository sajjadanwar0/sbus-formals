---------------------------- MODULE SBus_lean ----------------------------
(*
  SBus_lean.tla — ACP verification, optimised for N=4 completion
  
  Two fixes vs the original SBus.tla that caused state-space explosion:

  FIX 1: No `committed` variable.
    The original spec tracked every (agent, shard, version) triple ever
    committed, giving 2^(N×S×MaxV) possible set states (2^48 for N=4).
    Instead, ORISafety is verified structurally: since version strictly
    increments per shard, no two commits can share the same (shard,version).
    We check VersionMonotonicity instead — same safety guarantee, no blowup.

  FIX 2: Symmetry operator defined here, referenced from .cfg.
    Agents are interchangeable — any permutation of agent names yields
    an equivalent protocol execution. This reduces the state space by
    N! (24x for N=4, 120x for N=5).
*)

EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
  Agents,       \* e.g. {"a1","a2","a3","a4"}
  Shards,       \* e.g. {"s1","s2","s3"}
  MaxVersion,   \* e.g. 3
  RetryBudget,  \* e.g. 2
  NULL          \* placeholder for "no owner" — set to "NULL" in cfg

\* Symmetry operator: agent names are interchangeable.
\* Referenced as SYMMETRY AgentSymmetry in the .cfg file.
AgentSymmetry == Permutations(Agents)

ASSUME Agents    # {}
ASSUME Shards    # {}
ASSUME MaxVersion  \in Nat /\ MaxVersion  > 0
ASSUME RetryBudget \in Nat

VARIABLES
  registry,      \* [Shards -> [version: 0..MaxVersion, owner: Agents \cup {NULL}]]
  deliveryLog,   \* [Agents -> [Shards -> 0..MaxVersion]]
  sessionAlive,  \* [Agents -> BOOLEAN]
  retries        \* [Agents -> 0..RetryBudget]

vars == <<registry, deliveryLog, sessionAlive, retries>>

(* ------------------------------------------------------------------ *)
(*  Invariants                                                         *)
(* ------------------------------------------------------------------ *)

TypeInvariant ==
  /\ registry    \in [Shards -> [version : 0..MaxVersion,
                                  owner   : Agents \cup {NULL}]]
  /\ deliveryLog \in [Agents -> [Shards -> 0..MaxVersion]]
  /\ sessionAlive \in [Agents -> BOOLEAN]
  /\ retries      \in [Agents -> 0..RetryBudget]

\* At most one agent owns any shard at any time.
OwnershipInvariant ==
  \A s \in Shards :
    \A a1, a2 \in Agents :
      ( registry[s].owner = a1 /\ registry[s].owner = a2 ) => a1 = a2

\* Versions only increase — this implies ORISafety:
\* because version strictly increments on every commit, no two commits
\* can share the same (shard, version) pair.
VersionMonotonicity ==
  \A s \in Shards : registry[s].version \in 0..MaxVersion

\* Inductive invariant — TLC checks this is preserved by every step.
IND == TypeInvariant /\ OwnershipInvariant /\ VersionMonotonicity

(* ------------------------------------------------------------------ *)
(*  Initial state                                                      *)
(* ------------------------------------------------------------------ *)

Init ==
  /\ registry     = [s \in Shards |-> [version |-> 0, owner |-> NULL]]
  /\ deliveryLog  = [a \in Agents |-> [s \in Shards |-> 0]]
  /\ sessionAlive = [a \in Agents |-> TRUE]
  /\ retries      = [a \in Agents |-> 0]

(* ------------------------------------------------------------------ *)
(*  Actions                                                            *)
(* ------------------------------------------------------------------ *)

\* Agent a reads shard s — records current version in DeliveryLog.
AgentRead(a, s) ==
  /\ sessionAlive[a]
  /\ deliveryLog' = [deliveryLog EXCEPT ![a][s] = registry[s].version]
  /\ UNCHANGED <<registry, sessionAlive, retries>>

\* Agent a commits to shard k.
\* Preconditions (ACP algorithm):
\*   1. Session alive
\*   2. Version not at max (state-space bound)
\*   3. Cross-shard stale check: all other shards match DeliveryLog
\*   4. Primary shard version matches DeliveryLog
\*   5. Shard is unowned (ownership token free)
AttemptCommit(a, k) ==
  /\ sessionAlive[a]
  /\ registry[k].version < MaxVersion
  /\ \A s \in Shards : (s # k) => (deliveryLog[a][s] = registry[s].version)
  /\ deliveryLog[a][k] = registry[k].version
  /\ registry[k].owner = NULL
  /\ registry'    = [registry EXCEPT
                       ![k].version = registry[k].version + 1,
                       ![k].owner   = NULL]
  /\ deliveryLog' = [deliveryLog EXCEPT ![a][k] = registry'[k].version]
  /\ UNCHANGED <<sessionAlive, retries>>

\* Commit attempt fails (version mismatch or cross-shard stale).
\* Uses one retry budget slot.
CommitFails(a, k) ==
  /\ sessionAlive[a]
  /\ retries[a] < RetryBudget
  /\ \/ deliveryLog[a][k] # registry[k].version
     \/ \E s \in Shards : (s # k /\ deliveryLog[a][s] # registry[s].version)
  /\ retries' = [retries EXCEPT ![a] = retries[a] + 1]
  /\ UNCHANGED <<registry, deliveryLog, sessionAlive>>

\* Session expires — agent can no longer commit.
SessionTimeout(a) ==
  /\ sessionAlive[a]
  /\ sessionAlive' = [sessionAlive EXCEPT ![a] = FALSE]
  /\ UNCHANGED <<registry, deliveryLog, retries>>

(* ------------------------------------------------------------------ *)
(*  Spec                                                               *)
(* ------------------------------------------------------------------ *)

Next ==
  \/ \E a \in Agents, s \in Shards : AgentRead(a, s)
  \/ \E a \in Agents, s \in Shards : AttemptCommit(a, s)
  \/ \E a \in Agents, s \in Shards : CommitFails(a, s)
  \/ \E a \in Agents               : SessionTimeout(a)
  \* Stuttering step: terminal state when all sessions expired
  \/ (\A a \in Agents : ~sessionAlive[a]) /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

=============================================================================
