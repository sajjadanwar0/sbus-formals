---------------------------- MODULE SBus_lean ----------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
  Agents,
  Shards,
  MaxVersion,
  RetryBudget,
  NULL
AgentSymmetry == Permutations(Agents)

ASSUME Agents    # {}
ASSUME Shards    # {}
ASSUME MaxVersion  \in Nat /\ MaxVersion  > 0
ASSUME RetryBudget \in Nat

VARIABLES
  registry,
  deliveryLog,
  sessionAlive,
  retries

vars == <<registry, deliveryLog, sessionAlive, retries>>

TypeInvariant ==
  /\ registry    \in [Shards -> [version : 0..MaxVersion,
                                  owner   : Agents \cup {NULL}]]
  /\ deliveryLog \in [Agents -> [Shards -> 0..MaxVersion]]
  /\ sessionAlive \in [Agents -> BOOLEAN]
  /\ retries      \in [Agents -> 0..RetryBudget]

OwnershipInvariant ==
  \A s \in Shards :
    \A a1, a2 \in Agents :
      ( registry[s].owner = a1 /\ registry[s].owner = a2 ) => a1 = a2

VersionMonotonicity ==
  \A s \in Shards : registry[s].version \in 0..MaxVersion

IND == TypeInvariant /\ OwnershipInvariant /\ VersionMonotonicity

Init ==
  /\ registry     = [s \in Shards |-> [version |-> 0, owner |-> NULL]]
  /\ deliveryLog  = [a \in Agents |-> [s \in Shards |-> 0]]
  /\ sessionAlive = [a \in Agents |-> TRUE]
  /\ retries      = [a \in Agents |-> 0]


AgentRead(a, s) ==
  /\ sessionAlive[a]
  /\ deliveryLog' = [deliveryLog EXCEPT ![a][s] = registry[s].version]
  /\ UNCHANGED <<registry, sessionAlive, retries>>

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

CommitFails(a, k) ==
  /\ sessionAlive[a]
  /\ retries[a] < RetryBudget
  /\ \/ deliveryLog[a][k] # registry[k].version
     \/ \E s \in Shards : (s # k /\ deliveryLog[a][s] # registry[s].version)
  /\ retries' = [retries EXCEPT ![a] = retries[a] + 1]
  /\ UNCHANGED <<registry, deliveryLog, sessionAlive>>

SessionTimeout(a) ==
  /\ sessionAlive[a]
  /\ sessionAlive' = [sessionAlive EXCEPT ![a] = FALSE]
  /\ UNCHANGED <<registry, deliveryLog, retries>>


Next ==
  \/ \E a \in Agents, s \in Shards : AgentRead(a, s)
  \/ \E a \in Agents, s \in Shards : AttemptCommit(a, s)
  \/ \E a \in Agents, s \in Shards : CommitFails(a, s)
  \/ \E a \in Agents               : SessionTimeout(a)
  \/ (\A a \in Agents :   \* Stuttering step: terminal state when all sessions expired
~sessionAlive[a]) /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

=============================================================================