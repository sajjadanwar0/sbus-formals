# sbus-formals

**TLA+, TLAPS, and Dafny mechanized-verification artifacts for the S-Bus paper.**

> *S-Bus: Automatic Read-Set Reconstruction for Multi-Agent LLM State
> Coordination.* Sajjad Khan, 2026. [arXiv link — TBA]

This repository contains the formal evidence supporting the paper's
§III–§V safety claims, across three independent verification tools:

- **TLC** (model checking) — bounded exhaustive verification of the ORI
  invariant at *N* ≤ 4 (211,696,712 distinct states at *N* = 4)
- **TLAPS** (theorem proving) — mechanized proof of single-node ORI
  safety for arbitrary agent count (687 obligations, 0 failed; modulo
  one retained foundational typing axiom)
- **Dafny 4** — 19 machine-checked inductive soundness lemmas on the
  abstract algorithm

**Companion repositories:**

- [`sbus`](https://github.com/sajjadanwar0/sbus) — the Rust
  implementation (the measured system)
- [`sbus-experiments`](https://github.com/sajjadanwar0/sbus-experiments)
  — Python experimental harness
- [`sbus-baselines`](https://github.com/sajjadanwar0/sbus-baselines) —
  Rust-native PostgreSQL + Redis adapters for PG-Comparison
- [`sbus-proxy`](https://github.com/sajjadanwar0/sbus-proxy) — LLM-API
  proxy used in PROXY-PH2

---

## Repository structure

```
sbus-formals/
├── README.md
├── LICENSE
├── proofs/                    ← TLAPS + Dafny mechanised proofs
│   ├── SBus_TLAPS.tla       (687 obligations, 0 failed; 1 axiom)
│   └── sbus_lemmas.dfy       (19 lemmas + predicates, 0 errors)
├── models/                    ← TLC model-checking models
│   ├── SBus_ori.tla              (cross-shard ORI invariant)
│   ├── SBus_ori_N3.cfg
│   ├── SBus_ori_N4.cfg           (full N=4 check)
│   ├── SBus_ori_N4_reduced.cfg   (symmetry-reduced N=4)
│   ├── SBus_lean.tla             (ACP, no committed history)
│   ├── SBus_lean_N3.cfg
│   ├── SBus_lean_N4.cfg
│   ├── SBus_Distributed.tla      (3-node abstract Raft)
│   └── SBus_Distributed.cfg
├── results/                   ← captured run outputs (verifier logs)
│   ├── tlapm.log                  (TLAPS execution: 687/687 proved)
│   ├── dafny.log                  (Dafny: 19 verified, 0 errors)
│   ├── formal_results.json        (machine-readable summary)
│   ├── tlc_tlc_n3.log             (TLC N=3 run)
│   ├── tlc_tlc_n4_full.log        (TLC N=4 full)
│   └── tlc_tlc_n4_reduced.log     (TLC N=4 reduced)
├── scripts/
│   └── run_formal.sh              (reproducibility driver)
└── historical/                ← documented work-in-progress
    ├── SBus_TLAPS_attempt_a.tla         (attempts FunTypingReconstruction discharge)
    ├── SBus_TLAPS_attempt_b.tla         (further attempt — 22/702 still failing)
    ├── tlapm_heavy_summary.txt
    └── run_heavy_proof.sh
```

---

## Paper claim → artifact mapping

### Paper §V Table III row: TLAPS proof

| Paper cites | Artifact in this repo | Status |
|---|---|---|
| `SBus_TLAPS.tla`, 687 obligations, 0 failed, 1 retained axiom | `proofs/SBus_TLAPS.tla` | **Matches paper** |

The proof mechanises two theorems for arbitrary *N*:

- `ReadSetSoundness` — recorded-read monotonicity invariant. State
  invariant: `∀a, i : dlog[a][i].v ≤ registry[dlog[a][i].k].v`.
- `ORICommitSafety` — cross-shard equality at commit. Transition
  property capturing Definition III.4(2):
  `∀(k', v') ∈ dlog[α] : k' ≠ k ⇒ registry[k'].v = v'`.

Two sequence-theoretic facts are discharged via the standard
`SequenceTheorems` library (`SeqDef`, `ElementOfSeq`). Two parameter
`ASSUME` declarations are retained on unspecified constants —
standard TLA+ parameterisation, not mathematical axioms.

**One AXIOM is retained:** `FunTypingReconstruction`, the converse of
the typed-function-space introduction rule:
> `DOMAIN f = S ∧ ∀x ∈ S : f[x] ∈ T  ⇒  f ∈ [S → T]`

This is foundational to TLA+'s function-space construction and is
widely treated as obvious in TLA+ practice, but is not present in the
standard `FunctionTheorems.tla` library. Discharge via the Isabelle/TLA
backend is queued as future work; see `historical/` for in-progress
attempts.

To verify locally:

```bash
cd proofs
tlapm --toolbox 0 0 SBus_TLAPS.tla
# Expected:  All 687 obligations proved.
```

`results/tlapm.log` contains the captured output from a prior verification
run. The file paths inside the log record the cache directory layout used
at capture time and may not match exactly when you re-run `tlapm` today —
the workspace will write its own cache and produce a fresh log with current
paths. Re-running `scripts/run_formal.sh` regenerates `tlapm.log`,
`dafny.log`, and `formal_results.json` against the current artifacts.

What matters in the captured log is the final line:

```
[INFO]: All 687 obligations proved.
```

### Paper §V: Dafny lemmas

| Paper cites | Artifact in this repo | Status |
|---|---|---|
| `sbus_lemmas.dfy`, 19 verified | `proofs/sbus_lemmas.dfy` | **Matches paper** |

The paper lists nine named lemmas plus helper predicates. Dafny
reports `19 verified, 0 errors` — the count includes the lemmas, their
helpers, and `EmptyLogSoundness`.

To verify locally:

```bash
cd proofs
dafny verify sbus_lemmas.dfy
# Expected:  Dafny program verifier finished with 19 verified, 0 errors
```

### Paper §V + §VII: TLC model-checking

| Paper cites | Artifact | Reported states | Status |
|---|---|---|---|
| `SBus_ori.tla`, 211,696,712 states at N=4 | `models/SBus_ori.tla` + `SBus_ori_N4.cfg` | 211 M (full N=4) | **Matches paper** |
| `SBus_ori.tla`, 88,848 states at N=3 | `models/SBus_ori.tla` + `SBus_ori_N3.cfg` | 88,848 at N=3 | **Matches paper** |
| `SBus_lean.tla` | `models/SBus_lean.tla` | (predecessor of `SBus_ori`) | **Historical** |
| `SBus_Distributed.tla`, 247,249 states | `models/SBus_Distributed.tla` | 247 K | **Matches paper** |

The headline N=4 number (211 M states, depth 32, fingerprint
collision probability 4.6×10⁻⁷) came from a 16-worker parallel TLC run
of about 1h 18min. `results/tlc_tlc_n4_full.log` contains the run
output; `results/formal_results.json` contains a machine-readable
summary.

To reproduce N=3 (≈ 1 second):

```bash
cd models
java -Xmx32G -jar tla2tools.jar -workers 16 -config SBus_ori_N3.cfg SBus_ori.tla
```

For the full N=4 run, allocate ~1h 18min on 16 workers and use
`SBus_ori_N4.cfg`.

### Paper §III-D: Distributed correctness (TLC abstract)

`SBus_Distributed.tla` model-checks an abstract 3-node deployment with
five state variables (`registry`, per-node `delivery_log`, `leader`,
bounded `term`, per-agent `last_commit_fresh`) and four transitions
(`ElectLeader`, `AgentGet`, `AgentCommit`, `AgentRecover`). At
*Agents = {a1, a2}*, *Shards = {s1, s2}*, *Nodes = {n1, n2, n3}*,
*MaxVersion = 3*, with symmetry reduction over agent and node
permutations, TLC explores 247,249 distinct states to depth 28 with
0 violations.

A separate temporal property `FailoverGapExists` confirms that the
model deliberately exposes the ~5ms concurrent-failover window of
Limitation 11.

---

## Quick verification (all three tools)

```bash
./scripts/run_formal.sh
```

The driver:

1. Runs `tlapm` on `proofs/SBus_TLAPS.tla` → expects 687/687 obligations
2. Runs `dafny verify proofs/sbus_lemmas.dfy` → expects 19 verified, 0 errors
3. Runs `tlc` on `models/SBus_ori.tla` with `SBus_ori_N3.cfg` → expects 0 violations

Machine-readable results are written to `results/formal_results.json`.

### Prerequisites

| Tool | Version | Install |
|---|---|---|
| TLAPS | 1.5+ | <https://tla.msr-inria.inria.fr/tlaps/> |
| TLC | 1.8+ | bundled in `tla2tools.jar`: <https://github.com/tlaplus/tlaplus/releases> |
| Dafny | 4.0+ | `brew install dafny` or <https://github.com/dafny-lang/dafny> |
| Java | 11+ | for TLC |

---

## `historical/` — transparency about work-in-progress

The retained `FunTypingReconstruction` axiom has been the subject of
ongoing attempts to discharge it from the standard TLAPS library:

- **v17** reformulates `FunTypingReconstruction` as a `THEOREM` with a
  proof via `[x ∈ S |-> f[x]]` plus ZFC extensionality. Proof structure
  complete; full verification incomplete at time of snapshot.
- **v18** refines v17's extensionality step. Best recorded run closed
  680/702 obligations (22 still failing — see
  `historical/tlapm_heavy_summary.txt`). The failing obligations
  cluster around the inductive invariant `IND`'s preservation step,
  not around `FunTypingReconstruction` itself.

These are documented here for transparency. The paper does **not**
claim they verify. The paper's reported state is v16 (687 obligations,
1 axiom).

If you successfully close v18's remaining obligations or have insight
on the `IND` preservation step, please open an issue or PR.

---

## Why three tools?

| Tool | Scope | Strengths | Limits |
|---|---|---|---|
| TLC | Bounded *N* ≤ 4 | Exhaustive; finds counterexamples | Scale-limited |
| TLAPS | Arbitrary *N* | Proves for all *N* | Manual proof structure required |
| Dafny | Inductive soundness of state transitions | Compiles; types match implementation | Not full protocol model |

Together these cover (a) small-instance exhaustive validation (TLC),
(b) arbitrary-*N* safety theorems (TLAPS), and (c) inductive
state-invariant preservation (Dafny). The paper's §V discusses how
each tier contributes.

---

## Known limitations

From the paper's §V and §VIII:

1. **Single-node safety only.** TLAPS proves single-node ACP.
   Distributed (Raft) correctness is TLC-checked via
   `SBus_Distributed.tla` (247K states) but not TLAPS-mechanised.
   Full Raft-TLAPS estimated at 6–12 person-months (Limitation 18).
2. **Dafny verifies abstract algorithm, not Rust implementation.**
   The Dafny types are structurally equivalent to the Rust
   implementation's, but this is parallel specification, not
   refinement. Full Rust refinement via Creusot or Verus (with async
   support for tokio) is future work (Limitation 19).
3. **One retained AXIOM.** `FunTypingReconstruction` (see above).
   Distinct from Verdi's network-model assumptions (about external
   phenomena outside the formal system) and from IronFleet's
   zero-axiom discipline (Limitation 17).
4. **Two parameter ASSUMEs.** `NoOwnerNotAgent`,
   `EmptyContentIsString` — standard TLA+ parameterisation, not
   mathematical axioms.

---

## Citation

```bibtex
@techreport{khan2026sbus,
  author      = {Khan, Sajjad},
  title       = {S-Bus: Automatic Read-Set Reconstruction for Multi-Agent
                 LLM State Coordination},
  institution = {Independent},
  year        = {2026},
  note        = {arXiv preprint},
  url         = {https://arxiv.org/abs/...}
}
```

## License

MIT. See `LICENSE`.
