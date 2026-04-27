---------------------------- MODULE SBus_ori ----------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
  Agents, Shards, MaxVersion, RetryBudget, NULL

AgentSymmetry == Permutations(Agents)

ASSUME Agents    # {}
ASSUME Shards    # {}
ASSUME MaxVersion  \in Nat /\ MaxVersion  > 0
ASSUME RetryBudget \in Nat

VARIABLES
  registry,
  deliveryLog,
  sessionAlive,
  retries,
  committedHistory

vars == <<registry, deliveryLog, sessionAlive, retries, committedHistory>>

TypeInvariant ==
  /\ registry    \in [Shards -> [version : 0..MaxVersion,
                                  owner   : Agents \cup {NULL}]]
  /\ deliveryLog \in [Agents -> [Shards -> 0..MaxVersion]]
  /\ sessionAlive \in [Agents -> BOOLEAN]
  /\ retries      \in [Agents -> 0..RetryBudget]
  /\ committedHistory \in
       Seq([agent: Agents,
            shard: Shards,
            version: 0..MaxVersion,
            dlog_snapshot: [Shards -> 0..MaxVersion],
            registry_snapshot: [Shards -> 0..MaxVersion]])

OwnershipInvariant ==
  \A s \in Shards :
    \A a1, a2 \in Agents :
      ( registry[s].owner = a1 /\ registry[s].owner = a2 ) => a1 = a2

VersionMonotonicity ==
  \A s \in Shards : registry[s].version \in 0..MaxVersion

ReadSetSoundness ==
  \A a \in Agents : \A s \in Shards :
    deliveryLog[a][s] <= registry[s].version

NoCrossShardStaleEnabled ==
  \A a \in Agents : \A k \in Shards :
    ( sessionAlive[a]
      /\ registry[k].version < MaxVersion
      /\ registry[k].owner = NULL
      /\ deliveryLog[a][k] = registry[k].version
    ) =>
    ( \A s \in Shards : s # k => deliveryLog[a][s] = registry[s].version )
      \/ TRUE

CommittedHistoriesAreORILegal ==
  \A i \in 1..Len(committedHistory) :
    LET entry == committedHistory[i]
    IN  \A s \in Shards :
          s # entry.shard =>
            entry.dlog_snapshot[s] = entry.registry_snapshot[s]

IND == TypeInvariant
    /\ OwnershipInvariant
    /\ VersionMonotonicity
    /\ ReadSetSoundness
    /\ CommittedHistoriesAreORILegal

Init ==
  /\ registry     = [s \in Shards |-> [version |-> 0, owner |-> NULL]]
  /\ deliveryLog  = [a \in Agents |-> [s \in Shards |-> 0]]
  /\ sessionAlive = [a \in Agents |-> TRUE]
  /\ retries      = [a \in Agents |-> 0]
  /\ committedHistory = <<>>

AgentRead(a, s) ==
  /\ sessionAlive[a]
  /\ deliveryLog' = [deliveryLog EXCEPT ![a][s] = registry[s].version]
  /\ UNCHANGED <<registry, sessionAlive, retries, committedHistory>>


Commit(a, k) ==
  /\ sessionAlive[a]
  /\ registry[k].version < MaxVersion
  /\ \A s \in Shards : (s # k) => (deliveryLog[a][s] = registry[s].version)
  /\ deliveryLog[a][k] = registry[k].version
  /\ registry[k].owner = NULL
  /\ registry'    = [registry EXCEPT
                       ![k].version = registry[k].version + 1,
                       ![k].owner   = NULL]
  /\ deliveryLog' = [deliveryLog EXCEPT ![a][k] = registry'[k].version]
  /\ committedHistory' = Append(committedHistory,
         [agent |-> a,
          shard |-> k,
          version |-> registry[k].version,
          dlog_snapshot |-> deliveryLog[a],
          registry_snapshot |-> [s \in Shards |-> registry[s].version]])
  /\ UNCHANGED <<sessionAlive, retries>>

CommitFails(a, k) ==
  /\ sessionAlive[a]
  /\ retries[a] < RetryBudget
  /\ \/ deliveryLog[a][k] # registry[k].version
     \/ \E s \in Shards : (s # k /\ deliveryLog[a][s] # registry[s].version)
  /\ retries' = [retries EXCEPT ![a] = retries[a] + 1]
  /\ UNCHANGED <<registry, deliveryLog, sessionAlive, committedHistory>>

SessionTimeout(a) ==
  /\ sessionAlive[a]
  /\ sessionAlive' = [sessionAlive EXCEPT ![a] = FALSE]
  /\ UNCHANGED <<registry, deliveryLog, retries, committedHistory>>


Next ==
  \/ \E a \in Agents, s \in Shards : AgentRead(a, s)
  \/ \E a \in Agents, k \in Shards : Commit(a, k)
  \/ \E a \in Agents, k \in Shards : CommitFails(a, k)
  \/ \E a \in Agents               : SessionTimeout(a)
  \/ (\A a \in Agents : ~sessionAlive[a]) /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

=============================================================================
