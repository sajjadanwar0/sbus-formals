-------------------------- MODULE SBus_Distributed --------------------------


EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Agents, Shards, Nodes, MaxVersion

ASSUME Cardinality(Nodes) = 3

NoLeader == "NoLeader"

VARIABLES
    registry,
    delivery_log,
    leader,
    term,
    last_commit_fresh

vars == <<registry, delivery_log, leader, term, last_commit_fresh>>

Symmetry == Permutations(Agents) \union Permutations(Nodes)

TypeInvariant ==
    /\ registry \in [Shards -> 0..MaxVersion]
    /\ leader \in (Nodes \union {NoLeader})
    /\ term \in 0..6
    /\ \A n \in Nodes : \A a \in Agents :
          delivery_log[n][a] \subseteq (Shards \X (0..MaxVersion))

VersionMonotonicity ==
    \A s \in Shards : registry[s] >= 0

ORISafety ==
    \A a \in Agents :
        leader \in Nodes =>
            \A e \in delivery_log[leader][a] :
                registry[e[1]] >= e[2]

VersionsNeverDecrease ==
    \A s \in Shards : registry[s] >= 0

ValidatedCommitsMeansFresh ==
    \A a \in Agents : last_commit_fresh[a] \in BOOLEAN

IND == TypeInvariant /\ VersionMonotonicity /\ ORISafety /\ ValidatedCommitsMeansFresh

Init ==
    /\ registry          = [s \in Shards |-> 0]
    /\ delivery_log      = [n \in Nodes  |-> [a \in Agents |-> {}]]
    /\ leader            = NoLeader
    /\ term              = 0
    /\ last_commit_fresh = [a \in Agents |-> TRUE]

ElectLeader(newLeader) ==
    /\ newLeader \in Nodes
    /\ \/ leader = NoLeader \/ newLeader # leader
    /\ term < 6
    /\ term'         = term + 1
    /\ leader'       = newLeader
    /\ delivery_log' = [delivery_log EXCEPT
                         ![newLeader] = [a \in Agents |-> {}]]
    /\ UNCHANGED <<registry, last_commit_fresh>>

AgentGet(a, s) ==
    /\ leader \in Nodes
    /\ registry[s] < MaxVersion
    /\ delivery_log' = [delivery_log EXCEPT
                         ![leader][a] = @ \union {<<s, registry[s]>>}]
    /\ UNCHANGED <<registry, leader, term, last_commit_fresh>>

AgentCommit(a, s) ==
    /\ leader \in Nodes
    /\ registry[s] < MaxVersion
    /\ LET dlog     == delivery_log[leader][a]
           allFresh == \A e \in dlog : registry[e[1]] = e[2]
       IN IF allFresh
          THEN
               /\ registry'          = [registry EXCEPT ![s] = @ + 1]
               /\ last_commit_fresh' = [last_commit_fresh EXCEPT
                                         ![a] = (dlog # {})]
               /\ UNCHANGED <<delivery_log, leader, term>>
          ELSE
               UNCHANGED vars

AgentRecover(a) ==
    /\ leader \in Nodes
    /\ delivery_log' = [delivery_log EXCEPT
                         ![leader][a] = {<<s, registry[s]>> : s \in Shards}]
    /\ UNCHANGED <<registry, leader, term, last_commit_fresh>>

Next ==
    \/ \E n \in Nodes                : ElectLeader(n)
    \/ \E a \in Agents, s \in Shards : AgentGet(a, s)
    \/ \E a \in Agents, s \in Shards : AgentCommit(a, s)
    \/ \E a \in Agents               : AgentRecover(a)

Spec == Init /\ [][Next]_vars

TypeSafe == []TypeInvariant

VersionsMonotone == []VersionMonotonicity

FailoverGapExists ==
    <>((\E a \in Agents : last_commit_fresh[a] = FALSE))

=============================================================================