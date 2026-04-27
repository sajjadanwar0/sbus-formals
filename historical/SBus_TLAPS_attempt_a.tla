---- MODULE SBus_TLAPS_attempt_a ----
EXTENDS Naturals, Sequences, FiniteSets, TLAPS,
        FunctionTheorems, SequenceTheorems, Functions

CONSTANT Agents
CONSTANT Shards
CONSTANT NoOwner

ASSUME NoOwnerNotAgent == NoOwner \notin Agents

CONSTANT EmptyContent
ASSUME EmptyContentIsString == EmptyContent \in STRING

THEOREM SeqDefinition ==
  \A T : Seq(T) = UNION {[1..n -> T] : n \in Nat}
  BY SeqDef

THEOREM SeqIndexTyping ==
  \A T, s, i :
    (s \in Seq(T) /\ i \in 1..Len(s)) => s[i] \in T
  BY ElementOfSeq

THEOREM FunTypingReconstruction ==
  \A S, T, f :
    (DOMAIN f = S /\ \A x \in S : f[x] \in T) => f \in [S -> T]
<1>1. SUFFICES ASSUME NEW S, NEW T, NEW f,
                     DOMAIN f = S,
                     \A x \in S : f[x] \in T
               PROVE  f \in [S -> T]
  OBVIOUS
<1>2. Restrict(f, S) = [x \in S |-> f[x]]
  BY DEF Restrict
<1>3. [x \in S |-> f[x]] \in [S -> T]
  BY <1>1
<1>4. Restrict(f, S) \in [S -> T]
  BY <1>2, <1>3
<1>5. \A x \in S : f[x] = Restrict(f, S)[x]
  BY <1>2
<1>6. DOMAIN Restrict(f, S) = S
  BY <1>2
<1>7. f = Restrict(f, S)

  BY <1>1, <1>5, <1>6
<1>8. QED
  BY <1>4, <1>7

VARIABLE registry
VARIABLE tokens
VARIABLE delivery_log
VARIABLE committed_history

vars == <<registry, tokens, delivery_log, committed_history>>

RegistryTI == registry \in [Shards -> [version: Nat, content: STRING]]
TokensTI   == tokens   \in [Shards -> Agents \cup {NoOwner}]
DLogTI     == delivery_log \in [Agents -> Seq([k: Shards, v: Nat])]

CommittedHistoryEntry ==
  [agent: Agents, shard: Shards, version: Nat,
   read_set: Seq([k: Shards, v: Nat]),
   cross_shard_snapshot: Seq([k: Shards, snapshot_v: Nat])]

CommittedHistoryTI == committed_history \in Seq(CommittedHistoryEntry)

TypeInvariant == RegistryTI /\ TokensTI /\ DLogTI /\ CommittedHistoryTI

OwnershipInvariant ==
  \A s \in Shards :
    tokens[s] \in Agents =>
      \A a1, a2 \in Agents :
        (tokens[s] = a1 /\ tokens[s] = a2) => a1 = a2

ReadSetSoundness ==
  \A a \in Agents :
    \A i \in 1..Len(delivery_log[a]) :
      delivery_log[a][i].v <= registry[delivery_log[a][i].k].version

CommittedHistoriesAreORILegal ==
  \A i \in 1..Len(committed_history) :
    LET entry == committed_history[i]
    IN  /\ Len(entry.cross_shard_snapshot) = Len(entry.read_set)
        /\ \A j \in 1..Len(entry.read_set) :
             entry.read_set[j].k = entry.cross_shard_snapshot[j].k
        /\ \A j \in 1..Len(entry.read_set) :
             entry.read_set[j].k # entry.shard =>
               entry.read_set[j].v = entry.cross_shard_snapshot[j].snapshot_v


NoStaleCrossShard(a, primary) ==
  \A i \in 1..Len(delivery_log[a]) :
    delivery_log[a][i].k # primary =>
      registry[delivery_log[a][i].k].version = delivery_log[a][i].v

IND == TypeInvariant /\ OwnershipInvariant /\ ReadSetSoundness /\ CommittedHistoriesAreORILegal

Init ==
  /\ registry     = [s \in Shards |-> [version |-> 0, content |-> EmptyContent]]
  /\ tokens       = [s \in Shards |-> NoOwner]
  /\ delivery_log = [a \in Agents |-> <<>>]
  /\ committed_history = <<>>

Read(ag, sh) ==
  /\ delivery_log' = [delivery_log EXCEPT
        ![ag] = Append(delivery_log[ag],
                       [k |-> sh, v |-> registry[sh].version])]
  /\ UNCHANGED <<registry, tokens, committed_history>>


SnapshotAtCommit(ag) ==
  [i \in 1..Len(delivery_log[ag]) |->
     [k |-> delivery_log[ag][i].k,
      snapshot_v |-> registry[delivery_log[ag][i].k].version]]

Commit(ag, sh, ve, delta) ==
  /\ registry[sh].version = ve
  /\ tokens[sh] = NoOwner
  /\ \A i \in 1..Len(delivery_log[ag]) :
       delivery_log[ag][i].k # sh =>
         registry[delivery_log[ag][i].k].version = delivery_log[ag][i].v
  /\ registry' = [registry EXCEPT
                    ![sh] = [version |-> ve + 1, content |-> delta]]
  /\ tokens'   = [tokens EXCEPT ![sh] = NoOwner]
  /\ committed_history' = Append(committed_history,
       [agent |-> ag,
        shard |-> sh,
        version |-> ve,
        read_set |-> delivery_log[ag],
        cross_shard_snapshot |->
          [j \in 1..Len(delivery_log[ag]) |->
             [k |-> delivery_log[ag][j].k,
              snapshot_v |-> registry[delivery_log[ag][j].k].version]]])
  /\ UNCHANGED delivery_log

Timeout(ag) ==
  /\ delivery_log' = [delivery_log EXCEPT ![ag] = <<>>]
  /\ UNCHANGED <<registry, tokens, committed_history>>

Next ==
  \/ \E ag \in Agents, sh \in Shards : Read(ag, sh)
  \/ \E ag \in Agents, sh \in Shards, ve \in Nat, delta \in STRING :
       Commit(ag, sh, ve, delta)
  \/ \E ag \in Agents : Timeout(ag)

Spec == Init /\ [][Next]_vars

THEOREM InitIND == Init => IND
<1>1. ASSUME Init PROVE IND
  <2>1. registry = [s \in Shards |-> [version |-> 0, content |-> EmptyContent]]
    BY <1>1 DEF Init
  <2>2. \A s \in Shards : registry[s] = [version |-> 0, content |-> EmptyContent]
    BY <2>1
  <2>2a. 0 \in Nat
    OBVIOUS
  <2>2b. EmptyContent \in STRING
    BY EmptyContentIsString
  <2>2c. [version |-> 0, content |-> EmptyContent] \in [version: Nat, content: STRING]
    BY <2>2a, <2>2b
  <2>3. \A s \in Shards : registry[s] \in [version: Nat, content: STRING]
    BY <2>2, <2>2c
  <2>4. RegistryTI
    BY <2>1, <2>3 DEF RegistryTI
  <2>5. tokens = [s \in Shards |-> NoOwner]
    BY <1>1 DEF Init
  <2>6. NoOwner \in Agents \cup {NoOwner}
    OBVIOUS
  <2>7. \A s \in Shards : tokens[s] \in Agents \cup {NoOwner}
    BY <2>5, <2>6
  <2>8. TokensTI
    BY <2>5, <2>7 DEF TokensTI
  <2>9. delivery_log = [a \in Agents |-> <<>>]
    BY <1>1 DEF Init
  <2>10. <<>> \in Seq([k: Shards, v: Nat])
    OBVIOUS
  <2>11. \A a \in Agents : delivery_log[a] \in Seq([k: Shards, v: Nat])
    BY <2>9, <2>10
  <2>12. DLogTI
    BY <2>9, <2>11 DEF DLogTI
  <2>14. \A s \in Shards : tokens[s] = NoOwner
    BY <2>5
  <2>15. NoOwner \notin Agents
    BY NoOwnerNotAgent
  <2>16. \A s \in Shards : tokens[s] \notin Agents
    BY <2>14, <2>15
  <2>17. OwnershipInvariant
    BY <2>16 DEF OwnershipInvariant
  <2>18. \A a \in Agents : delivery_log[a] = <<>>
    BY <2>9
  <2>19. \A a \in Agents : Len(delivery_log[a]) = 0
    BY <2>18
  <2>20. \A a \in Agents : 1..Len(delivery_log[a]) = {}
    BY <2>19
  <2>21. ReadSetSoundness
    BY <2>20 DEF ReadSetSoundness
  <2>21a. committed_history = <<>>
    BY <1>1 DEF Init
  <2>21b. Len(committed_history) = 0
    BY <2>21a
  <2>21c. 1..Len(committed_history) = {}
    BY <2>21b
  <2>21d. CommittedHistoriesAreORILegal
    BY <2>21c DEF CommittedHistoriesAreORILegal
  <2>21e. committed_history \in Seq(CommittedHistoryEntry)
    BY <2>21a
  <2>21f. CommittedHistoryTI
    BY <2>21e DEF CommittedHistoryTI
  <2>13a. TypeInvariant
    BY <2>4, <2>8, <2>12, <2>21f DEF TypeInvariant
  <2>22. QED
    BY <2>13a, <2>17, <2>21, <2>21d DEF IND
<1>2. QED
  BY <1>1


LEMMA ReadPreservesIND ==
  ASSUME IND, NEW ag \in Agents, NEW sh \in Shards, Read(ag, sh)
  PROVE  IND'
<1>1. registry' = registry
  BY DEF Read
<1>2. tokens' = tokens
  BY DEF Read
<1>3. delivery_log' = [delivery_log EXCEPT
            ![ag] = Append(delivery_log[ag],
                           [k |-> sh, v |-> registry[sh].version])]
  BY DEF Read
<1>4. RegistryTI'
  BY <1>1, IND DEF IND, TypeInvariant, RegistryTI
<1>5. TokensTI'
  BY <1>2, IND DEF IND, TypeInvariant, TokensTI
<1>6. delivery_log[ag] \in Seq([k: Shards, v: Nat])
  BY IND DEF IND, TypeInvariant, DLogTI
<1>7. registry[sh].version \in Nat
  BY IND DEF IND, TypeInvariant, RegistryTI
<1>8. [k |-> sh, v |-> registry[sh].version] \in [k: Shards, v: Nat]
  BY <1>7
<1>9. Append(delivery_log[ag], [k |-> sh, v |-> registry[sh].version])
        \in Seq([k: Shards, v: Nat])
  BY <1>6, <1>8
<1>10. \A a \in Agents : delivery_log'[a] \in Seq([k: Shards, v: Nat])
  <2>1. TAKE a \in Agents
  <2>1a. delivery_log \in [Agents -> Seq([k: Shards, v: Nat])]
    BY IND DEF IND, TypeInvariant, DLogTI
  <2>1b. ag \in DOMAIN delivery_log
    BY <2>1a
  <2>2. CASE a = ag
    <3>1. delivery_log'[ag] = Append(delivery_log[ag],
                                     [k |-> sh, v |-> registry[sh].version])
      BY <1>3, <2>1b
    <3>2. QED
      BY <1>9, <2>2, <3>1
  <2>3. CASE a # ag
    <3>1. delivery_log'[a] = delivery_log[a]
      BY <1>3, <2>1b, <2>3
    <3>2. delivery_log[a] \in Seq([k: Shards, v: Nat])
      BY <2>1a
    <3>3. QED
      BY <3>1, <3>2
  <2>4. QED
    BY <2>2, <2>3
<1>11. delivery_log' \in [Agents -> Seq([k: Shards, v: Nat])]
  <2>1. delivery_log \in [Agents -> Seq([k: Shards, v: Nat])]
    BY IND DEF IND, TypeInvariant, DLogTI
  <2>2. DOMAIN delivery_log' = DOMAIN delivery_log
    BY <1>3, <2>1
  <2>3. DOMAIN delivery_log' = Agents
    BY <2>1, <2>2
  <2>4. \A a \in Agents : delivery_log'[a] \in Seq([k: Shards, v: Nat])
    BY <1>10
  <2>5. QED
    BY <2>3, <2>4, FunTypingReconstruction
<1>12. DLogTI'
  BY <1>11 DEF DLogTI
<1>12a. committed_history' = committed_history
  BY DEF Read
<1>12b. CommittedHistoryTI
  BY IND DEF IND, TypeInvariant
<1>12c. CommittedHistoryTI'
  BY <1>12a, <1>12b DEF CommittedHistoryTI
<1>13. TypeInvariant'
  BY <1>4, <1>5, <1>12, <1>12c DEF TypeInvariant
<1>14. OwnershipInvariant'
  BY <1>2, IND DEF IND, OwnershipInvariant
<1>15. \A a \in Agents :
        \A i \in 1..Len(delivery_log'[a]) :
          delivery_log'[a][i].v <=
            registry'[delivery_log'[a][i].k].version
  <2>1. TAKE a \in Agents
  <2>1a. delivery_log \in [Agents -> Seq([k: Shards, v: Nat])]
    BY IND DEF IND, TypeInvariant, DLogTI
  <2>1b. ag \in DOMAIN delivery_log
    BY <2>1a
  <2>2. TAKE i \in 1..Len(delivery_log'[a])
  <2>3. CASE a # ag
    <3>1. delivery_log'[a] = delivery_log[a]
      BY <1>3, <2>1b, <2>3
    <3>2. i \in 1..Len(delivery_log[a])
      BY <3>1
    <3>3. delivery_log[a][i].v <=
            registry[delivery_log[a][i].k].version
      BY IND, <3>2 DEF IND, ReadSetSoundness
    <3>4. delivery_log'[a][i] = delivery_log[a][i]
      BY <3>1
    <3>5. QED
      BY <1>1, <3>3, <3>4
  <2>4. CASE a = ag
    <3>1. delivery_log'[ag] = Append(delivery_log[ag],
                                     [k |-> sh, v |-> registry[sh].version])
      BY <1>3, <2>1b
    <3>2. Len(delivery_log'[ag]) = Len(delivery_log[ag]) + 1
      BY <3>1, <1>6
    <3>3. CASE i <= Len(delivery_log[ag])
      <4>1. i \in 1..Len(delivery_log[ag])
        BY <2>4, <3>3
      <4>2. delivery_log'[ag][i] = delivery_log[ag][i]
        BY <3>1, <3>3, <1>6
      <4>3. delivery_log[ag][i].v <=
              registry[delivery_log[ag][i].k].version
        BY IND, <4>1 DEF IND, ReadSetSoundness
      <4>4. QED
        BY <1>1, <2>4, <4>2, <4>3
    <3>4. CASE ~(i <= Len(delivery_log[ag]))
      <4>0. i \in 1..Len(delivery_log'[ag])
        BY <2>4
      <4>0a. i \in 1..(Len(delivery_log[ag]) + 1)
        BY <4>0, <3>2
      <4>1. i = Len(delivery_log[ag]) + 1
        BY <4>0a, <3>4
      <4>2. delivery_log'[ag][i] = [k |-> sh, v |-> registry[sh].version]
        BY <3>1, <4>1, <1>6
      <4>3. delivery_log'[ag][i].k = sh
        BY <4>2
      <4>4. delivery_log'[ag][i].v = registry[sh].version
        BY <4>2
      <4>5. registry[sh].version \in Nat
        BY <1>7
      <4>6. registry[sh].version <= registry[sh].version
        BY <4>5
      <4>7. QED
        BY <1>1, <2>4, <4>3, <4>4, <4>6
    <3>5. QED
      BY <3>3, <3>4
  <2>5. QED
    BY <2>3, <2>4
<1>16. ReadSetSoundness'
  BY <1>15 DEF ReadSetSoundness
<1>16a. committed_history' = committed_history
  BY DEF Read
<1>16b. registry' = registry
  BY DEF Read
<1>16c. CommittedHistoriesAreORILegal
  BY DEF IND
<1>16d. CommittedHistoriesAreORILegal'
  BY <1>16a, <1>16b, <1>16c DEF CommittedHistoriesAreORILegal
<1>17. QED
  BY <1>13, <1>14, <1>16, <1>16d DEF IND


LEMMA TimeoutPreservesIND ==
  ASSUME IND, NEW ag \in Agents, Timeout(ag)
  PROVE  IND'
<1>1. registry' = registry
  BY DEF Timeout
<1>2. tokens' = tokens
  BY DEF Timeout
<1>3. delivery_log' = [delivery_log EXCEPT ![ag] = <<>>]
  BY DEF Timeout
<1>4. RegistryTI'
  BY <1>1, IND DEF IND, TypeInvariant, RegistryTI
<1>5. TokensTI'
  BY <1>2, IND DEF IND, TypeInvariant, TokensTI
<1>6. <<>> \in Seq([k: Shards, v: Nat])
  OBVIOUS
<1>7. \A a \in Agents : delivery_log'[a] \in Seq([k: Shards, v: Nat])
  <2>1. TAKE a \in Agents
  <2>1a. delivery_log \in [Agents -> Seq([k: Shards, v: Nat])]
    BY IND DEF IND, TypeInvariant, DLogTI
  <2>1b. ag \in DOMAIN delivery_log
    BY <2>1a
  <2>2. CASE a = ag
    <3>1. delivery_log'[ag] = <<>>
      BY <1>3, <2>1b
    <3>2. QED
      BY <1>6, <2>2, <3>1
  <2>3. CASE a # ag
    <3>1. delivery_log'[a] = delivery_log[a]
      BY <1>3, <2>1b, <2>3
    <3>2. delivery_log[a] \in Seq([k: Shards, v: Nat])
      BY <2>1a
    <3>3. QED
      BY <3>1, <3>2
  <2>4. QED
    BY <2>2, <2>3
<1>7a. delivery_log' \in [Agents -> Seq([k: Shards, v: Nat])]
  <2>1. delivery_log \in [Agents -> Seq([k: Shards, v: Nat])]
    BY IND DEF IND, TypeInvariant, DLogTI
  <2>2. DOMAIN delivery_log' = DOMAIN delivery_log
    BY <1>3, <2>1
  <2>3. DOMAIN delivery_log' = Agents
    BY <2>1, <2>2
  <2>4. \A a \in Agents : delivery_log'[a] \in Seq([k: Shards, v: Nat])
    BY <1>7
  <2>5. QED
    BY <2>3, <2>4, FunTypingReconstruction
<1>8. DLogTI'
  BY <1>7a DEF DLogTI
<1>8a. committed_history' = committed_history
  BY DEF Timeout
<1>8b. CommittedHistoryTI
  BY IND DEF IND, TypeInvariant
<1>8c. CommittedHistoryTI'
  BY <1>8a, <1>8b DEF CommittedHistoryTI
<1>9. TypeInvariant'
  BY <1>4, <1>5, <1>8, <1>8c DEF TypeInvariant
<1>10. OwnershipInvariant'
  BY <1>2, IND DEF IND, OwnershipInvariant
<1>11. \A a \in Agents :
        \A i \in 1..Len(delivery_log'[a]) :
          delivery_log'[a][i].v <=
            registry'[delivery_log'[a][i].k].version
  <2>1. TAKE a \in Agents
  <2>1a. delivery_log \in [Agents -> Seq([k: Shards, v: Nat])]
    BY IND DEF IND, TypeInvariant, DLogTI
  <2>1b. ag \in DOMAIN delivery_log
    BY <2>1a
  <2>2. TAKE i \in 1..Len(delivery_log'[a])
  <2>3. CASE a = ag
    <3>1. delivery_log'[ag] = <<>>
      BY <1>3, <2>1b
    <3>2. Len(delivery_log'[ag]) = 0
      BY <3>1
    <3>3. 1..Len(delivery_log'[ag]) = {}
      BY <3>2
    <3>4. QED
      BY <2>3, <3>3
  <2>4. CASE a # ag
    <3>1. delivery_log'[a] = delivery_log[a]
      BY <1>3, <2>1b, <2>4
    <3>2. i \in 1..Len(delivery_log[a])
      BY <3>1
    <3>3. delivery_log[a][i].v <=
            registry[delivery_log[a][i].k].version
      BY IND, <3>2 DEF IND, ReadSetSoundness
    <3>4. delivery_log'[a][i] = delivery_log[a][i]
      BY <3>1
    <3>5. QED
      BY <1>1, <3>3, <3>4
  <2>5. QED
    BY <2>3, <2>4
<1>12. ReadSetSoundness'
  BY <1>11 DEF ReadSetSoundness
<1>12a. committed_history' = committed_history
  BY DEF Timeout
<1>12b. registry' = registry
  BY DEF Timeout
<1>12c. CommittedHistoriesAreORILegal
  BY DEF IND
<1>12d. CommittedHistoriesAreORILegal'
  BY <1>12a, <1>12b, <1>12c DEF CommittedHistoriesAreORILegal
<1>13. QED
  BY <1>9, <1>10, <1>12, <1>12d DEF IND


LEMMA CommitPreservesIND ==
  ASSUME IND,
         NEW ag \in Agents, NEW sh \in Shards,
         NEW ve \in Nat,    NEW delta \in STRING,
         Commit(ag, sh, ve, delta)
  PROVE  IND'
<1>1. registry' = [registry EXCEPT
                    ![sh] = [version |-> ve + 1, content |-> delta]]
  BY DEF Commit
<1>2. tokens'   = [tokens EXCEPT ![sh] = NoOwner]
  BY DEF Commit
<1>3. delivery_log' = delivery_log
  BY DEF Commit
<1>4. registry[sh].version = ve
  BY DEF Commit
<1>5. registry \in [Shards -> [version: Nat, content: STRING]]
  BY IND DEF IND, TypeInvariant, RegistryTI
<1>6. tokens \in [Shards -> Agents \cup {NoOwner}]
  BY IND DEF IND, TypeInvariant, TokensTI
<1>7. registry'[sh] = [version |-> ve + 1, content |-> delta]
  BY <1>1, <1>5
<1>8. registry'[sh].version = ve + 1
  BY <1>7
<1>9. \A s2 \in Shards : s2 # sh => registry'[s2] = registry[s2]
  BY <1>1, <1>5
<1>10. tokens'[sh] = NoOwner
  BY <1>2, <1>6
<1>11. \A s2 \in Shards : s2 # sh => tokens'[s2] = tokens[s2]
  BY <1>2, <1>6
<1>12. ve + 1 \in Nat
  OBVIOUS
<1>13. delta \in STRING
  OBVIOUS
<1>14. \A s2 \in Shards : registry'[s2] \in [version: Nat, content: STRING]
  <2>1. TAKE s2 \in Shards
  <2>2. CASE s2 = sh
    <3>1. registry'[sh] = [version |-> ve + 1, content |-> delta]
      BY <1>7
    <3>2. [version |-> ve + 1, content |-> delta]
            \in [version: Nat, content: STRING]
      BY <1>12, <1>13
    <3>3. QED
      BY <2>2, <3>1, <3>2
  <2>3. CASE s2 # sh
    <3>1. registry'[s2] = registry[s2]
      BY <1>9, <2>3
    <3>2. registry[s2] \in [version: Nat, content: STRING]
      BY <1>5
    <3>3. QED
      BY <3>1, <3>2
  <2>4. QED
    BY <2>2, <2>3
<1>15. registry' \in [Shards -> [version: Nat, content: STRING]]
  BY <1>1, <1>5, <1>14
<1>16. RegistryTI'
  BY <1>15 DEF RegistryTI
<1>17. \A s2 \in Shards : tokens'[s2] \in Agents \cup {NoOwner}
  <2>1. TAKE s2 \in Shards
  <2>2. CASE s2 = sh
    <3>1. tokens'[sh] = NoOwner
      BY <1>10
    <3>2. NoOwner \in Agents \cup {NoOwner}
      OBVIOUS
    <3>3. QED
      BY <2>2, <3>1, <3>2
  <2>3. CASE s2 # sh
    <3>1. tokens'[s2] = tokens[s2]
      BY <1>11, <2>3
    <3>2. tokens[s2] \in Agents \cup {NoOwner}
      BY <1>6
    <3>3. QED
      BY <3>1, <3>2
  <2>4. QED
    BY <2>2, <2>3
<1>18. tokens' \in [Shards -> Agents \cup {NoOwner}]
  BY <1>2, <1>6, <1>17
<1>19. TokensTI'
  BY <1>18 DEF TokensTI
<1>20. DLogTI'
  BY <1>3, IND DEF IND, TypeInvariant, DLogTI
(* ────────────────────────────────────────────────────────────────────
   CommittedHistoryTI preservation under Commit.  The Commit action
   appends a new entry to committed_history; we must show the
   appended entry has type CommittedHistoryEntry, then Append
   preserves Seq-membership.
   ──────────────────────────────────────────────────────────────── *)
<1>20a. committed_history' =
          Append(committed_history,
            [agent |-> ag,
             shard |-> sh,
             version |-> ve,
             read_set |-> delivery_log[ag],
             cross_shard_snapshot |->
               [j \in 1..Len(delivery_log[ag]) |->
                  [k |-> delivery_log[ag][j].k,
                   snapshot_v |-> registry[delivery_log[ag][j].k].version]]])
  BY DEF Commit
<1>20b. ag \in Agents /\ sh \in Shards /\ ve \in Nat /\ delta \in STRING
  OBVIOUS
<1>20c. delivery_log[ag] \in Seq([k: Shards, v: Nat])
  BY IND DEF IND, TypeInvariant, DLogTI
<1>20d. registry \in [Shards -> [version: Nat, content: STRING]]
  BY IND DEF IND, TypeInvariant, RegistryTI
<1>20e. \A j \in 1..Len(delivery_log[ag]) :
          delivery_log[ag][j] \in [k: Shards, v: Nat]
  BY <1>20c, SeqIndexTyping
<1>20f. \A j \in 1..Len(delivery_log[ag]) :
          delivery_log[ag][j].k \in Shards
  BY <1>20e
<1>20g. \A j \in 1..Len(delivery_log[ag]) :
          registry[delivery_log[ag][j].k].version \in Nat
  BY <1>20d, <1>20f
<1>20h. \A j \in 1..Len(delivery_log[ag]) :
          [k |-> delivery_log[ag][j].k,
           snapshot_v |-> registry[delivery_log[ag][j].k].version]
            \in [k: Shards, snapshot_v: Nat]
  BY <1>20f, <1>20g
<1>20i. [j \in 1..Len(delivery_log[ag]) |->
            [k |-> delivery_log[ag][j].k,
             snapshot_v |-> registry[delivery_log[ag][j].k].version]]
          \in Seq([k: Shards, snapshot_v: Nat])
  BY <1>20h, SeqDefinition
<1>20j. [agent |-> ag,
         shard |-> sh,
         version |-> ve,
         read_set |-> delivery_log[ag],
         cross_shard_snapshot |->
           [j \in 1..Len(delivery_log[ag]) |->
              [k |-> delivery_log[ag][j].k,
               snapshot_v |-> registry[delivery_log[ag][j].k].version]]]
          \in CommittedHistoryEntry
  BY <1>20b, <1>20c, <1>20i DEF CommittedHistoryEntry
<1>20k. committed_history \in Seq(CommittedHistoryEntry)
  BY IND DEF IND, TypeInvariant, CommittedHistoryTI
<1>20l. committed_history' \in Seq(CommittedHistoryEntry)
  BY <1>20a, <1>20j, <1>20k
<1>20m. CommittedHistoryTI'
  BY <1>20l DEF CommittedHistoryTI
<1>21. TypeInvariant'
  BY <1>16, <1>19, <1>20, <1>20m DEF TypeInvariant
<1>22. \A s2 \in Shards :
          tokens'[s2] \in Agents =>
            \A a1, a2 \in Agents :
              (tokens'[s2] = a1 /\ tokens'[s2] = a2) => a1 = a2
  <2>1. TAKE s2 \in Shards
  <2>2. CASE s2 = sh
    <3>1. tokens'[sh] = NoOwner
      BY <1>10
    <3>2. NoOwner \notin Agents
      BY NoOwnerNotAgent
    <3>3. tokens'[sh] \notin Agents
      BY <3>1, <3>2
    <3>4. QED
      BY <2>2, <3>3
  <2>3. CASE s2 # sh
    <3>1. tokens'[s2] = tokens[s2]
      BY <1>11, <2>3
    <3>2. QED
      BY <3>1, IND DEF IND, OwnershipInvariant
  <2>4. QED
    BY <2>2, <2>3
<1>23. OwnershipInvariant'
  BY <1>22 DEF OwnershipInvariant
<1>24. \A a \in Agents :
        \A i \in 1..Len(delivery_log'[a]) :
          delivery_log'[a][i].v <=
            registry'[delivery_log'[a][i].k].version
  <2>1. TAKE a \in Agents
  <2>2. TAKE i \in 1..Len(delivery_log'[a])
  <2>3. delivery_log'[a] = delivery_log[a]
    BY <1>3
  <2>4. i \in 1..Len(delivery_log[a])
    BY <2>3
  <2>5. delivery_log'[a][i] = delivery_log[a][i]
    BY <2>3
  <2>6. delivery_log[a] \in Seq([k: Shards, v: Nat])
    BY IND DEF IND, TypeInvariant, DLogTI
  <2>7. delivery_log[a][i] \in [k: Shards, v: Nat]
    BY <2>4, <2>6, SeqIndexTyping
  <2>8. delivery_log[a][i].k \in Shards
    BY <2>7
  <2>9. delivery_log[a][i].v \in Nat
    BY <2>7
  <2>10. delivery_log[a][i].v <=
            registry[delivery_log[a][i].k].version
    BY IND, <2>4 DEF IND, ReadSetSoundness
  <2>11. CASE delivery_log[a][i].k # sh
    <3>1. registry'[delivery_log[a][i].k] = registry[delivery_log[a][i].k]
      BY <1>9, <2>8, <2>11
    <3>2. QED
      BY <2>5, <2>10, <3>1
  <2>12. CASE delivery_log[a][i].k = sh
    <3>1. registry'[sh].version = ve + 1
      BY <1>8
    <3>2. registry[sh].version = ve
      BY <1>4
    <3>3. delivery_log[a][i].v <= registry[sh].version
      BY <2>10, <2>12
    <3>4. delivery_log[a][i].v <= ve
      BY <3>3, <3>2
    <3>5. ve <= ve + 1
      OBVIOUS
    <3>6. delivery_log[a][i].v <= ve + 1
      BY <3>4, <3>5, <2>9, <1>12
    <3>7. registry'[delivery_log[a][i].k].version = ve + 1
      BY <2>12, <3>1
    <3>8. QED
      BY <2>5, <3>6, <3>7
  <2>13. QED
    BY <2>11, <2>12
<1>25. ReadSetSoundness'
  BY <1>24 DEF ReadSetSoundness

<1>25a. committed_history' =
          Append(committed_history,
            [agent |-> ag,
             shard |-> sh,
             version |-> ve,
             read_set |-> delivery_log[ag],
             cross_shard_snapshot |->
               [j \in 1..Len(delivery_log[ag]) |->
                  [k |-> delivery_log[ag][j].k,
                   snapshot_v |-> registry[delivery_log[ag][j].k].version]]])
  BY DEF Commit
<1>25b. CommittedHistoriesAreORILegal
  BY DEF IND
<1>25c. \A i \in 1..Len(committed_history) :
          committed_history'[i] = committed_history[i]
  BY <1>25a
<1>25d. Len(committed_history') = Len(committed_history) + 1
  BY <1>25a
<1>25e. committed_history'[Len(committed_history) + 1] =
          [agent |-> ag,
           shard |-> sh,
           version |-> ve,
           read_set |-> delivery_log[ag],
           cross_shard_snapshot |->
             [j \in 1..Len(delivery_log[ag]) |->
                [k |-> delivery_log[ag][j].k,
                 snapshot_v |-> registry[delivery_log[ag][j].k].version]]]
  BY <1>25a
<1>25f.
        \A j \in 1..Len(delivery_log[ag]) :
          delivery_log[ag][j].k # sh =>
            registry[delivery_log[ag][j].k].version = delivery_log[ag][j].v
  BY DEF Commit
<1>25g. CommittedHistoriesAreORILegal'
  <2>1. SUFFICES ASSUME NEW i \in 1..Len(committed_history')
                 PROVE  LET entry == committed_history'[i]
                        IN  /\ Len(entry.cross_shard_snapshot) =
                                 Len(entry.read_set)
                            /\ \A j \in 1..Len(entry.read_set) :
                                 entry.read_set[j].k =
                                   entry.cross_shard_snapshot[j].k
                            /\ \A j \in 1..Len(entry.read_set) :
                                 entry.read_set[j].k # entry.shard =>
                                   entry.read_set[j].v =
                                     entry.cross_shard_snapshot[j].snapshot_v
    BY DEF CommittedHistoriesAreORILegal
  <2>2. CASE i \in 1..Len(committed_history)
    <3>1. committed_history'[i] = committed_history[i]
      BY <2>2, <1>25c
    <3>2. QED
      BY <3>1, <2>2, <1>25b DEF CommittedHistoriesAreORILegal
  <2>3. CASE i = Len(committed_history) + 1
    <3>1. committed_history'[i] =
            [agent |-> ag,
             shard |-> sh,
             version |-> ve,
             read_set |-> delivery_log[ag],
             cross_shard_snapshot |->
               [j \in 1..Len(delivery_log[ag]) |->
                  [k |-> delivery_log[ag][j].k,
                   snapshot_v |-> registry[delivery_log[ag][j].k].version]]]
      BY <2>3, <1>25e
    <3>2. committed_history'[i].read_set = delivery_log[ag]
      BY <3>1
    <3>3. Len(committed_history'[i].cross_shard_snapshot) = Len(delivery_log[ag])
      BY <3>1
    <3>4. Len(committed_history'[i].read_set) = Len(delivery_log[ag])
      BY <3>2
    <3>5. Len(committed_history'[i].cross_shard_snapshot) =
            Len(committed_history'[i].read_set)
      BY <3>3, <3>4
    <3>6. \A j \in 1..Len(delivery_log[ag]) :
            committed_history'[i].cross_shard_snapshot[j] =
              [k |-> delivery_log[ag][j].k,
               snapshot_v |-> registry[delivery_log[ag][j].k].version]
      BY <3>1
    <3>7. \A j \in 1..Len(committed_history'[i].read_set) :
            committed_history'[i].read_set[j].k =
              committed_history'[i].cross_shard_snapshot[j].k
      BY <3>2, <3>4, <3>6
    <3>8. committed_history'[i].shard = sh
      BY <3>1
    <3>9. \A j \in 1..Len(committed_history'[i].read_set) :
            committed_history'[i].read_set[j].k # committed_history'[i].shard =>
              committed_history'[i].read_set[j].v =
                committed_history'[i].cross_shard_snapshot[j].snapshot_v
      <4>1. TAKE j \in 1..Len(committed_history'[i].read_set)
      <4>2. ASSUME committed_history'[i].read_set[j].k #
                     committed_history'[i].shard
            PROVE  committed_history'[i].read_set[j].v =
                     committed_history'[i].cross_shard_snapshot[j].snapshot_v
        <5>1. j \in 1..Len(delivery_log[ag])
          BY <4>1, <3>2, <3>4
        <5>2. committed_history'[i].read_set[j] = delivery_log[ag][j]
          BY <5>1, <3>2
        <5>3. committed_history'[i].cross_shard_snapshot[j] =
                [k |-> delivery_log[ag][j].k,
                 snapshot_v |-> registry[delivery_log[ag][j].k].version]
          BY <5>1, <3>6
        <5>4. committed_history'[i].read_set[j].k = delivery_log[ag][j].k
          BY <5>2
        <5>5. delivery_log[ag][j].k # sh
          BY <4>2, <5>4, <3>8
        <5>6. registry[delivery_log[ag][j].k].version = delivery_log[ag][j].v
          BY <5>1, <5>5, <1>25f
        <5>7. committed_history'[i].read_set[j].v = delivery_log[ag][j].v
          BY <5>2
        <5>8. committed_history'[i].cross_shard_snapshot[j].snapshot_v =
                registry[delivery_log[ag][j].k].version
          BY <5>3
        <5>9. QED
          BY <5>6, <5>7, <5>8
      <4>3. QED
        BY <4>1, <4>2
    <3>10. QED
      BY <3>5, <3>7, <3>9
  <2>4. QED
    BY <2>2, <2>3, <1>25d
<1>26. QED
  BY <1>21, <1>23, <1>25, <1>25g DEF IND


THEOREM INDInductive == IND /\ [Next]_vars => IND'
<1>1. ASSUME IND, Next PROVE IND'
  <2>1. CASE \E ag \in Agents, sh \in Shards : Read(ag, sh)
    BY <2>1, <1>1, ReadPreservesIND
  <2>2. CASE \E ag \in Agents, sh \in Shards, ve \in Nat, delta \in STRING :
              Commit(ag, sh, ve, delta)
    BY <2>2, <1>1, CommitPreservesIND
  <2>3. CASE \E ag \in Agents : Timeout(ag)
    BY <2>3, <1>1, TimeoutPreservesIND
  <2>4. QED
    BY <2>1, <2>2, <2>3, <1>1 DEF Next
<1>2. ASSUME IND, UNCHANGED vars PROVE IND'
  BY <1>2 DEF vars, IND, TypeInvariant, RegistryTI, TokensTI,
                  DLogTI, CommittedHistoryTI, OwnershipInvariant,
                  ReadSetSoundness, CommittedHistoriesAreORILegal
<1>3. QED
  BY <1>1, <1>2


THEOREM SpecImpliesIND == Spec => []IND
  BY InitIND, INDInductive, PTL DEF Spec


THEOREM CommitEnablingConditionImpliesFreshness ==
  ASSUME NEW ag \in Agents, NEW sh \in Shards,
         NEW ve \in Nat,    NEW delta \in STRING,
         Commit(ag, sh, ve, delta)
  PROVE  NoStaleCrossShard(ag, sh)
<1>1. \A i \in 1..Len(delivery_log[ag]) :
        delivery_log[ag][i].k # sh =>
          registry[delivery_log[ag][i].k].version = delivery_log[ag][i].v
  BY DEF Commit
<1>2. QED
  BY <1>1 DEF NoStaleCrossShard

THEOREM ORICommitSafety ==
  ASSUME NEW ag \in Agents, NEW sh \in Shards,
         NEW ve \in Nat,    NEW delta \in STRING,
         Commit(ag, sh, ve, delta)
  PROVE  NoStaleCrossShard(ag, sh)
  BY CommitEnablingConditionImpliesFreshness

THEOREM CommittedHistoriesAreORILegalInvariant ==
  Spec => []CommittedHistoriesAreORILegal
<1>1. Spec => []IND
  BY SpecImpliesIND
<1>2. IND => CommittedHistoriesAreORILegal
  BY DEF IND
<1>3. []IND => []CommittedHistoriesAreORILegal
  BY <1>2, PTL
<1>4. QED
  BY <1>1, <1>3, PTL

CommitValidation ==
  \A ag \in Agents, sh \in Shards :
    (\E ve \in Nat, delta \in STRING : Commit(ag, sh, ve, delta))
      => NoStaleCrossShard(ag, sh)

THEOREM CommitValidationHolds == CommitValidation
<1>1. SUFFICES ASSUME NEW ag \in Agents, NEW sh \in Shards,
                     \E ve \in Nat, delta \in STRING :
                       Commit(ag, sh, ve, delta)
               PROVE  NoStaleCrossShard(ag, sh)
  BY DEF CommitValidation
<1>2. PICK ve \in Nat, delta \in STRING : Commit(ag, sh, ve, delta)
  BY <1>1
<1>3. QED
  BY <1>2, CommitEnablingConditionImpliesFreshness

====
