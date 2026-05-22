# sbus-formals

**Mechanised proofs for the S-Bus paper.**

This repository contains the formal-methods artifacts — TLA+ specifications,
TLAPS proof scripts, and Dafny inductive lemmas — that support the safety
claims of:

> *S-Bus: Automatic Read-Set Reconstruction for Multi-Agent LLM State
> Coordination.* Sajjad Khan, 2026.
> [arXiv:2605.17076](https://arxiv.org/abs/2605.17076) [cs.LG].

**Companion repositories:**

- [`sbus`](https://github.com/sajjadanwar0/sbus) — the Rust workspace
  (`sbus-server`, `sbus-baselines`, `sbus-proxy`)
- [`sbus-experiments`](https://github.com/sajjadanwar0/sbus-experiments) —
  Python experimental harness, including the PH-3 LLM-judge validation
  against an independent human annotator (strict κ=0.93, n=93, 96.8%
  raw agreement) added in v2 of the preprint

---

## Scope of the formal evidence

The mechanised proofs cover the **abstract algorithm's** safety properties.
Refinement to the Rust implementation is empirical, not mechanised — this
matches standard industry practice short of IronFleet (Hawblitzel et al.,
SOSP 2015). Specifically:

- **TLAPS** discharges `ReadSetSoundness` and `ORICommitSafety` for
  arbitrary agent counts (687 obligations, 0 failed, modulo one retained
  typing axiom — see [Limitations](#limitations) below).
- **TLC** exhaustively explores the single-node state space at N=3
  (20,763,484 distinct states, depth 28, 0 violations), a reduced
  configuration at N=4 (2,811,301 distinct states, depth 24, 0
  violations), and an abstract 3-node Raft model (247,249 distinct
  states, 0 violations). A full N=4 exhaustive sweep is provided as
  an opt-in run via `scripts/run_formal.sh` and is not part of the
  current artifact (see [Limitations](#limitations)).
- **Dafny** machine-checks 9 inductive soundness lemmas (19
  verification obligations discharged, 0 errors) on types structurally
  equivalent to the Rust implementation (parallel specification, not
  refinement).

| Tool | What is proved | Scope | Paper section |
|---|---|---|---|
| TLAPS | `ReadSetSoundness` + `ORICommitSafety` | Arbitrary N, 687 obligations, 1 axiom | §III-D, §V |
| TLC (single-node) | Same invariants | N=3 exhaustive (20.8M states, depth 28); N=4 reduced (2.8M states, depth 24) | §III-D, §V |
| TLC (distributed) | ORI safety under Raft abstraction | 3 nodes, 2 agents, 247K states | §III-D |
| Dafny | 9 inductive soundness lemmas | 19 verification obligations, 0 errors | §III-D, §V |

---

## Repository layout

```
sbus-formals/
├── README.md                   this file
├── LICENSE                     MIT
├── proofs/                     TLAPS + Dafny mechanised proofs
│   ├── SBus_TLAPS.tla          687 obligations, 0 failed, 1 retained axiom
│   └── sbus_lemmas.dfy         9 lemmas, 19 verification obligations, 0 errors
│
├── models/                     TLC model-checking specifications
│   ├── SBus_ori.tla            ORI invariant model (single-node)
│   ├── SBus_ori_N3.cfg         N=3 exhaustive config
│   ├── SBus_ori_N4.cfg         N=4 full config (opt-in; not in current artifact)
│   ├── SBus_ori_N4_reduced.cfg N=4 reduced config (MaxVersion=2)
│   ├── SBus_lean.tla           Companion lean ACP spec
│   ├── SBus_lean_N3.cfg
│   ├── SBus_lean_N4.cfg
│   ├── SBus_Distributed.tla    Abstract 3-node Raft model
│   └── SBus_Distributed.cfg    Distributed-model TLC config
│
├── results/                    Machine-readable verification outputs
│   ├── formal_results.json     Summary (statuses + counts)
│   ├── dafny.log               Dafny verifier output
│   ├── tlapm.log               TLAPS proof-manager output
│   ├── tlc_tlc_n3.log          TLC N=3 exhaustive log
│   ├── tlc_tlc_n4_reduced.log  TLC N=4 reduced log
│   └── tlc_tlc_n4_full.log     TLC N=4 full log (in-progress / opt-in)
│
├── scripts/
│   └── run_formal.sh           One-shot reproducer for steps 1–5
│
└── historical/                 Earlier proof attempts (kept for provenance)
    ├── SBus_TLAPS_attempt_a.tla
    ├── SBus_TLAPS_attempt_b.tla
    ├── run_heavy_proof.sh
    └── tlapm_heavy_summary.txt
```

---

## Reproducing the verification

The fastest path is the bundled driver script, which runs Dafny, TLAPS,
and the two completed TLC configurations in sequence (≈ 5–15 minutes
total) and optionally launches the N=4 full sweep in the background:

```bash
./scripts/run_formal.sh
```

By default this runs steps 1–4 in the foreground and starts step 5
(N=4 full TLC) in the background under `nohup`. Use
`--skip-tlc-full` to omit the background sweep entirely, or
`--proof-only` to run only Dafny + TLAPS. See the script header for
all flags.

If you'd rather invoke each tool directly:

### TLAPS proofs

Requires [TLAPS](https://proofs.tlapl.us/) (`tlapm 1.5` or later).

```bash
cd proofs
tlapm SBus_TLAPS.tla
```

Expected: **687 / 687 obligations proved, 0 failed.** One `AXIOM`
remains undischarged (`FunTypingReconstruction`); see
[Limitations](#limitations).

Wall time: approximately 8 minutes on a recent laptop. Most of the
time is spent in the typed-function-space inductiveness lemma chain.
Pre-computed output is in `results/tlapm.log`.

### TLC model checking

Requires Java 11+. The bundled `tla2tools.jar` is sufficient.

**N=3 exhaustive (≈ 10 seconds):**

```bash
java -cp tla2tools.jar tlc2.TLC \
    -workers auto \
    -config models/SBus_ori_N3.cfg \
    models/SBus_ori.tla
```

Expected: 20,763,484 distinct states explored to depth 28, zero
invariant violations. Pre-computed output in `results/tlc_tlc_n3.log`.

**N=4 reduced (≈ 42 seconds):**

```bash
java -cp tla2tools.jar tlc2.TLC \
    -workers auto \
    -config models/SBus_ori_N4_reduced.cfg \
    models/SBus_ori.tla
```

Expected: 2,811,301 distinct states explored to depth 24, zero
invariant violations. Pre-computed output in
`results/tlc_tlc_n4_reduced.log`.

**Distributed (3-node Raft abstraction):**

```bash
java -cp tla2tools.jar tlc2.TLC \
    -workers auto \
    -config models/SBus_Distributed.cfg \
    models/SBus_Distributed.tla
```

Expected: 247,249 distinct states, depth 28, zero violations on
`ORISafety`. The companion temporal property `FailoverGapExists`
deliberately exposes the ~5 ms concurrent-failover window
(Limitation 11 in the paper).

**N=4 full (≈ 1 h – 7 h depending on workers — opt-in):**

```bash
java -cp tla2tools.jar tlc2.TLC \
    -workers 16 \
    -config models/SBus_ori_N4.cfg \
    models/SBus_ori.tla
```

This is the unbounded (`MaxVersion=3`) sweep. Wall time scales with
worker count: roughly 1 h 18 m on 16 workers, 2 h on 8 workers, 7 h
on 4 workers. **Not part of the current artifact** —
`results/tlc_tlc_n4_full.log` captures progress from a partial run
that was checkpointed mid-search; `results/formal_results.json` flags
this run as `"running"`. Reviewers who want the completed sweep
should re-run this command and update the JSON. See
[Limitations](#limitations).

### Dafny lemmas

Requires Dafny 4.0 or later.

```bash
dafny verify proofs/sbus_lemmas.dfy
```

Expected: **19 verified, 0 errors.** The 9 user-written lemmas are:
`InitSoundness`, `EmptyLogSoundness`, `ReadPreservesSoundness`,
`TimeoutPreservesSoundness`, `MonotonicCommitPreservesSoundness`,
`CrossShardStalenessIsStrict`, `OwnershipInvariantInductive`,
`VersionMonotonicityLemma`, `AcpLockOrderIsDeadlockFree`. Dafny
discharges 19 verification obligations from these lemmas (each lemma
generates well-formedness obligations alongside its main proof).
Pre-computed output in `results/dafny.log`.

---

## What the proofs do and do not establish

**Established (by the artifacts in this repo):**

- The S-Bus single-node algorithm preserves `ReadSetSoundness`
  (recorded reads never advance ahead of committed versions) for
  arbitrary N agents, conditional on the typed-function-space axiom
  below.
- The S-Bus algorithm satisfies `ORICommitSafety` (cross-shard
  recorded reads match the registry's current versions at commit time)
  for arbitrary N agents.
- The state space at N=3 (exhaustive) and N=4 (reduced) contains no
  violation of the type, ownership, version-monotonicity, or
  read-set-soundness invariants.
- Lock-acquisition order in the ACP is deadlock-free
  (`AcpLockOrderIsDeadlockFree`, Dafny).

**Not established (and explicitly out of scope):**

- **No refinement to the Rust implementation.** The Rust source is
  not formally connected to the TLA+ or Dafny specifications. The
  TLA+ spec is the ground truth for the abstract algorithm;
  correspondence to the implementation is empirical (884,110-attempt
  zero-corruption evidence in the paper).
- **No TLAPS-mechanised distributed safety proof.** The distributed
  model is TLC-checked at one configuration but not TLAPS-proven.
  Composition of the existing single-node TLAPS proof with a Raft
  TLAPS proof is open work (Limitation 18 in the paper).
- **No proof of semantic correctness.** The proofs cover *structural*
  conflict prevention (Type-I, in the paper's taxonomy). Semantic
  coherence between concurrent agent outputs is workload- and
  backbone-conditional and is established empirically, not formally.

---

## Limitations

### One retained mathematical axiom

`SBus_TLAPS.tla` retains a single undischarged `AXIOM`:

```tla
AXIOM FunTypingReconstruction ==
    \A f, S, T : (DOMAIN f = S /\ \A x \in S : f[x] \in T)
                 => f \in [S -> T]
```

This is the converse of typed-function-space introduction — a
foundational property of TLA+'s function-space construction that is
widely treated as obvious in TLA+ practice but is not a derived
theorem in the standard `FunctionTheorems.tla` library. Attempts to
discharge it within `tlapm`'s default backend have not closed. The
concrete next step is to attempt discharge via the Isabelle/TLA
backend, which encodes a deeper layer of TLA+ set theory; this is
open work.

The retained axiom is the only undischarged mathematical fact in the
proof. Two parameter `ASSUME`s on unspecified constants are also
retained (`NoOwner ∉ AGENTS`; initial shard content is a `STRING`),
but these are standard TLA+ parameterisation rather than mathematical
axioms.

### Dafny is parallel specification, not refinement

The Dafny types (`Shard`, `Delta`, `DeliveryEntry`) are structurally
equivalent to the Rust types in the implementation, but there is no
formal connection between the two. The Dafny lemmas verify that the
*algorithm expressed in Dafny* preserves the soundness invariants;
they do not verify that the Rust source code does. Full Rust
refinement via [Verus](https://github.com/verus-lang/verus) or
[Creusot](https://github.com/creusot-rs/creusot) is blocked on async
support for tokio-based code and is open work.

### TLC scope and the N=4 full sweep

The completed TLC runs cover N=3 exhaustively (20.8 M states) and N=4
under a reduced configuration (`MaxVersion=2`, 2.8 M states). A full
N=4 sweep at `MaxVersion=3` is provided in `models/SBus_ori_N4.cfg`
and the driver script supports running it as step 5 of
`scripts/run_formal.sh`, but the current artifact ships with that run
flagged as `"running"` in `results/formal_results.json` — the run
was checkpointed mid-search rather than allowed to terminate, and
`results/tlc_tlc_n4_full.log` captures the partial trace.

This means the paper's TLC claims rest on the two completed
configurations (N=3 exhaustive + N=4 reduced) rather than on a
completed N=4 full sweep. The TLAPS proof handles arbitrary N
(modulo the axiom above) and does not depend on the TLC sweep.

---

## Citation

```bibtex
@misc{khan2026sbus,
  author        = {Khan, Sajjad},
  title         = {{S-Bus}: Automatic Read-Set Reconstruction for Multi-Agent
                   {LLM} State Coordination},
  year          = {2026},
  eprint        = {2605.17076},
  archivePrefix = {arXiv},
  primaryClass  = {cs.LG},
  url           = {https://arxiv.org/abs/2605.17076},
  note          = {Preprint}
}
```

---

## License

MIT. See `LICENSE` at the repo root.