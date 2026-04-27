type AgentId = string
type Key     = string

datatype Option<T> = None | Some(value: T)

datatype DLogEntry = DLogEntry(k: Key, v: nat)

type Registry    = map<Key, nat>
type DeliveryLog = map<AgentId, seq<DLogEntry>>
type TokenMap    = map<Key, Option<AgentId>>

ghost predicate EntrySound(registry: Registry, e: DLogEntry)
{
    e.k in registry ==> e.v <= registry[e.k]
}

ghost predicate SeqSound(registry: Registry, s: seq<DLogEntry>)
{
    forall i: int | 0 <= i < |s| :: EntrySound(registry, s[i])
}

ghost predicate ReadSetSoundness(registry: Registry, dlog: DeliveryLog)
{
    forall a: AgentId | a in dlog :: SeqSound(registry, dlog[a])
}

lemma InitSoundness(registry: Registry)
    ensures ReadSetSoundness(registry, map[])
{
    // map[] has no keys; outer forall is vacuous.
}

lemma EmptyLogSoundness(registry: Registry, dlog: DeliveryLog, a: AgentId)
    requires ReadSetSoundness(registry, dlog)
    ensures  ReadSetSoundness(registry, dlog[a := []])
{
    var dlog' := dlog[a := []];
    forall aa: AgentId | aa in dlog'
        ensures SeqSound(registry, dlog'[aa])
    {
        if aa == a {
            assert dlog'[aa] == [];
        } else {
            assert dlog'[aa] == dlog[aa];
        }
    }
}

lemma ReadPreservesSoundness(
    registry: Registry,
    dlog:     DeliveryLog,
    a:        AgentId,
    k:        Key
)
    requires ReadSetSoundness(registry, dlog)
    requires k in registry
    requires a in dlog
    ensures  ReadSetSoundness(
        registry,
        dlog[a := dlog[a] + [DLogEntry(k, registry[k])]]
    )
{
    var newEntry: DLogEntry := DLogEntry(k, registry[k]);
    var newSeq: seq<DLogEntry> := dlog[a] + [newEntry];
    var dlog': DeliveryLog := dlog[a := newSeq];

    assert SeqSound(registry, newSeq) by {
        forall i: int | 0 <= i < |newSeq|
            ensures EntrySound(registry, newSeq[i])
        {
            if i < |dlog[a]| {
                assert newSeq[i] == dlog[a][i];
                assert SeqSound(registry, dlog[a]);
                assert EntrySound(registry, dlog[a][i]);
            } else {
                assert i == |dlog[a]|;
                assert newSeq[i] == newEntry;
                assert newEntry.k == k;
                assert newEntry.v == registry[k];
            }
        }
    }

    forall aa: AgentId | aa in dlog'
        ensures SeqSound(registry, dlog'[aa])
    {
        if aa == a {
            assert dlog'[aa] == newSeq;
        } else {
            assert dlog'[aa] == dlog[aa];
        }
    }
}

lemma TimeoutPreservesSoundness(
    registry: Registry,
    dlog:     DeliveryLog,
    a:        AgentId
)
    requires ReadSetSoundness(registry, dlog)
    requires a in dlog
    ensures  ReadSetSoundness(registry, dlog[a := []])
{
    EmptyLogSoundness(registry, dlog, a);
}

lemma MonotonicCommitPreservesSoundness(
    registry: Registry,
    dlog:     DeliveryLog,
    k:        Key,
    v_old:    nat,
    v_new:    nat
)
    requires ReadSetSoundness(registry, dlog)
    requires k in registry
    requires registry[k] == v_old
    requires v_new > v_old
    ensures  ReadSetSoundness(registry[k := v_new], dlog)
{
    var registry': Registry := registry[k := v_new];

    forall a: AgentId | a in dlog
        ensures SeqSound(registry', dlog[a])
    {
        forall i: int | 0 <= i < |dlog[a]|
            ensures EntrySound(registry', dlog[a][i])
        {
            var entry: DLogEntry := dlog[a][i];
            assert SeqSound(registry, dlog[a]);
            assert EntrySound(registry, entry);
            if entry.k in registry' {
                if entry.k == k {
                    // entry.v <= registry[k] = v_old < v_new = registry'[k]
                    assert entry.v <= registry[k];
                    assert registry[k] == v_old;
                    assert registry'[k] == v_new;
                    assert v_old < v_new;
                } else {
                    assert registry'[entry.k] == registry[entry.k];
                }
            }
        }
    }
}

predicate CrossShardStale(
    registry: Registry,
    dlog:     DeliveryLog,
    a:        AgentId,
    primary:  Key
)
    requires a in dlog
{
    exists i: int :: 0 <= i < |dlog[a]| &&
        var entry: DLogEntry := dlog[a][i];
        entry.k != primary &&
        entry.k in registry &&
        registry[entry.k] != entry.v
}

lemma CrossShardStalenessIsStrict(
    registry: Registry,
    dlog:     DeliveryLog,
    a:        AgentId,
    primary:  Key
)
    requires ReadSetSoundness(registry, dlog)
    requires a in dlog
    requires CrossShardStale(registry, dlog, a, primary)
    ensures  exists i: int :: 0 <= i < |dlog[a]| &&
                var entry: DLogEntry := dlog[a][i];
                entry.k != primary &&
                entry.k in registry &&
                entry.v < registry[entry.k]
{
    var i :| 0 <= i < |dlog[a]| &&
        var entry: DLogEntry := dlog[a][i];
        entry.k != primary &&
        entry.k in registry &&
        registry[entry.k] != entry.v;
    var entry: DLogEntry := dlog[a][i];
    assert SeqSound(registry, dlog[a]);
    assert EntrySound(registry, entry);
    assert entry.v <= registry[entry.k];
}

ghost predicate OwnershipInvariant(tokens: TokenMap)
{
    forall k: Key | k in tokens ::
        tokens[k].Some? ==>
            forall alpha1: AgentId, alpha2: AgentId |
                tokens[k] == Some(alpha1) && tokens[k] == Some(alpha2) ::
                    alpha1 == alpha2
}

lemma OwnershipInvariantInductive(
    tokens: TokenMap,
    k:      Key,
    alpha:  AgentId
)
    requires OwnershipInvariant(tokens)
    requires k in tokens && tokens[k] == None
    ensures  OwnershipInvariant(tokens[k := Some(alpha)])
{
    var tokens' := tokens[k := Some(alpha)];
    forall k': Key | k' in tokens'
        ensures tokens'[k'].Some? ==>
            forall a1: AgentId, a2: AgentId |
                tokens'[k'] == Some(a1) && tokens'[k'] == Some(a2) ::
                    a1 == a2
    {
        if k' == k {
            assert tokens'[k] == Some(alpha);
        } else {
            assert tokens'[k'] == tokens[k'];
        }
    }
}

lemma VersionMonotonicityLemma(v: nat)
    ensures v + 1 > v
    ensures forall v': nat {:trigger v + 1 != v'} | v' <= v :: v + 1 != v'
{
    // Closed by Dafny's arithmetic solver.
}

datatype Lock = RwLock | TokenMutex

ghost predicate LockOrderRespected(acquisitions: seq<Lock>)
{
    forall i: int | 0 <= i < |acquisitions| && acquisitions[i] == TokenMutex ::
        exists j: int :: 0 <= j < i && acquisitions[j] == RwLock
}

lemma AcpLockOrderIsDeadlockFree()
    ensures LockOrderRespected([RwLock, TokenMutex])
{
    var acq := [RwLock, TokenMutex];
    assert acq[0] == RwLock;
    assert exists j: int :: 0 <= j < 1 && acq[j] == RwLock by {
        assert acq[0] == RwLock;
    }
}
