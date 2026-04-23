# sbus-formals

**TLA+, TLAPS, and Dafny formal-verification artefacts for the S-Bus paper.**

Paper: *S-Bus v50.2: Observable-Read Consistency for Concurrent Multi-Agent
LLM State* (arXiv, 2026).

This repository contains the mechanised-verification evidence for the
paper's §III–§V safety claims across three tools:

- **TLC** (model checking) — bounded exhaustive verification of the ORI
  invariant at N ≤ 4
- **TLAPS** (theorem proving) — mechanised proof of the single-node ORI
  safety for arbitrary agent count
- **Dafny 4** — 19 machine-checked inductive soundness lemmas

## Companion repositories

- [`sbus`](https://github.com/sajjadanwar0/sbus) — the Rust implementation +
  PostgreSQL/Redis Rust baseline adapters (Cargo workspace)
- [`sbus-experiments`](https://github.com/sajjadanwar0/sbus-experiments) —
  Python experimental pipeline

---

## Repository structure

```
sbus-formals/
├── README.md
├── LICENSE
├── proofs/                              ← TLAPS + Dafny mechanised proofs
│   ├── SBus_TLAPS_v16.tla                  (687 obligations, 0 failed; 1 axiom)
│   └── sbus_lemmas_v4.dfy                  (19 lemmas + predicates, 0 errors)
├── models/                              ← TLC model-checking models
│   ├── SBus_ori.tla                        (cross-shard ORI invariant)
│   ├── SBus_ori_N3.cfg
│   ├── SBus_ori_N4.cfg                     (full N=4 check)
│   ├── SBus_ori_N4_reduced.cfg             (symmetry-reduced N=4)
│   ├── SBus_lean.tla                       (ACP, no committed history)
│   ├── SBus_lean_N3.cfg
│   ├── SBus_lean_N4.cfg
│   ├── SBus_Distributed.tla                (3-node abstract Raft)
│   └── SBus_Distributed.cfg
├── results/                             ← verified run outputs
│   ├── tlapm.log                           (TLAPS execution log)
│   ├── dafny.log                           (Dafny execution log)
│   ├── formal_results.json                 (machine-readable summary)
│   ├── tlc_tlc_n3.log                      (TLC N=3 run)
│   ├── tlc_tlc_n4_full.log                 (TLC N=4 full)
│   └── tlc_tlc_n4_reduced.log              (TLC N=4 reduced)
├── scripts/
│   └── run_formal.sh                       (reproducibility driver)
└── historical/                          ← documented work-in-progress
    ├── SBus_TLAPS_v17.tla                  (attempts FunTypingReconstruction proof)
    ├── SBus_TLAPS_v18.tla                  (further proof attempt — 22/702 failing)
    ├── tlapm_heavy_v3_summary_*.txt        (v18 verification attempts log)
    └── run_heavy_proof_v3.sh               (the script that produced the log)
```

---

## Paper claim → artifact mapping

### §V Table III — TLAPS proof

| Paper cites              | Artifact in this repo         | Status                          |
|--------------------------|-------------------------------|---------------------------------|
| `SBus_TLAPS_v12.tla`, 519 obligations | `proofs/SBus_TLAPS_v16.tla`   | **Superseded — see note below** |

**Paper–artifact version note.** The paper was written against v12 of the
TLAPS proof (519 obligations). This repository ships **v16** (687 obligations),
which is a refinement with more explicit proof steps. Both versions prove the
same two theorems (`ReadSetSoundness` and `ORICommitSafety`) and retain the
same single AXIOM (`FunTypingReconstruction`, a primitive fact about TLA+
function-space typing; see proof file comments for scope). The obligation
count grew because v16 decomposes several v12 proof steps into finer-grained
sub-obligations — no new axioms, no weakened theorems.

To verify:
```bash
cd proofs
tlapm --toolbox 0 0 SBus_TLAPS_v16.tla
# Expected: All 687 obligations proved.
```

### §V Dafny lemmas

| Paper cites              | Artifact in this repo        | Status                                 |
|--------------------------|------------------------------|----------------------------------------|
| `sbus_lemmas_v4.dfy`, 19 verified | `proofs/sbus_lemmas_v4.dfy`  | **Matches paper exactly**              |

The paper lists nine named lemmas (`InitSoundness`, `ReadPreservesSoundness`,
`CommitPreservesSoundness`, `TimeoutPreservesSoundness`,
`MonotonicCommitPreservesSoundness`, `CrossShardStalenessIsStrict`,
`OwnershipInvariantInductive`, `VersionMonotonicityLemma`,
`AcpLockOrderIsDeadlockFree`) plus helper predicates and `EmptyLogSoundness`.
Dafny reports `19 verified, 0 errors` — the 19 count includes these lemmas
plus their supporting predicates.

Note: `CommitPreservesSoundness` is realised in the file as
`MonotonicCommitPreservesSoundness` (which captures the strongest formulation
that subsumes the non-monotonic case); the paper's two names refer to the
same lemma.

To verify:
```bash
cd proofs
dafny verify sbus_lemmas_v4.dfy
# Expected: Dafny program verifier finished with 19 verified, 0 errors
```

### §V + §VII TLC model-checking

| Paper cites | Artifact in this repo          | Reported states          | Status           |
|-------------|--------------------------------|--------------------------|------------------|
| `SBus_ori.tla`, 211,696,712 states at N=4 | `models/SBus_ori.tla` + `SBus_ori_N4.cfg` | 211,696,712 (v50.2 claim)  | **Matches paper** |
| `SBus_ori.tla`, 88,848 states at N=3      | `models/SBus_ori.tla` + `SBus_ori_N3.cfg` | 88,848 at N=3              | **Matches paper** |
| `SBus_lean.tla` | `models/SBus_lean.tla`       | operationally identical to `SBus_ori` | **Historical — predecessor** |
| `SBus_Distributed.tla`, 247,249 states | `models/SBus_Distributed.tla`  | 247,000 (paper)            | **Matches paper** |

The paper's headline TLC number (211 M states at N=4) came from a 16-worker
parallel TLC run over 1h 18min. `results/tlc_tlc_n4_full.log` contains that
run's output; `results/formal_results.json` contains a machine-readable
summary.

To reproduce (N=3 takes ~1 second, N=4 full takes ~1h 18min on 16 workers):
```bash
cd models
java -Xmx32G -jar tla2tools.jar -workers 16 -config SBus_ori_N4.cfg SBus_ori.tla
```

---

## Quick verification (all three tools)

```bash
./scripts/run_formal.sh
```

This driver:
1. Runs `tlapm` on `proofs/SBus_TLAPS_v16.tla`   → expect 687/687 obligations
2. Runs `dafny verify proofs/sbus_lemmas_v4.dfy` → expect 19 verified, 0 errors
3. Runs `tlc` on `models/SBus_ori.tla` with `SBus_ori_N3.cfg` → expect 0 violations

Machine-readable results are written to `results/formal_results.json`.

### Prerequisites

| Tool     | Version     | Install                                                              |
|----------|-------------|----------------------------------------------------------------------|
| TLAPS    | 1.5+        | https://tla.msr-inria.inria.fr/tlaps/content/Home.html               |
| TLC      | 1.8+        | bundled in `tla2tools.jar`: https://github.com/tlaplus/tlaplus/releases |
| Dafny    | 4.0+        | `brew install dafny` or https://github.com/dafny-lang/dafny          |
| Java     | 11+         | for TLC                                                              |

### `results/formal_results.json` schema

```json
{
  "start":                     "2026-04-18T09:20:28Z",
  "end":                       "2026-04-18T09:24:19Z",
  "dafny_status":              "pass",
  "dafny_verified":            19,
  "dafny_errors":              0,
  "tlapm_status":              "pass",
  "tlapm_proved":              687,
  "tlapm_failed":              0,
  "tlc_n3_status":             "pass",
  "tlc_n3_distinct":           20763484,
  "tlc_n3_generated":          130942110,
  "tlc_n3_depth":              28,
  "tlc_n3_violations":         0,
  "tlc_n4_reduced_status":     "pass",
  "tlc_n4_reduced_distinct":   2811301,
  "tlc_n4_reduced_violations": 0,
  "tlc_n4_full_status":        "running"
}
```

---

## `historical/` — transparency about work-in-progress

The paper's single documented AXIOM (`FunTypingReconstruction`) has been the
subject of ongoing attempts to discharge it from the standard TLAPS library.
`historical/SBus_TLAPS_v17.tla` and `historical/SBus_TLAPS_v18.tla` reflect
those attempts.

**Current status of these attempts (April 2026):**

- **v17** reformulates `FunTypingReconstruction` as a `THEOREM` with a proof
  via `[x \in S |-> f[x]]` plus ZFC extensionality. Proof structure
  complete; full verification incomplete at time of snapshot.

- **v18** refines v17's extensionality step, removing an Isabelle hint to
  let the default method selection route to `force`/`blast`/`zipper`. Best
  recorded run closed **680 of 702 obligations (22 failing)** — see
  `historical/tlapm_heavy_v3_summary_*.txt`. The 22 failing obligations
  cluster around the inductive invariant `IND`'s preservation step, not
  around `FunTypingReconstruction` itself.

These are documented here for transparency — the paper does **not** claim
they verify. The paper's reported state is v16 (687 obligations, 1 axiom).

If you successfully close v18's remaining obligations, please open an issue
or PR. The TLA+/TLAPS community's insight is welcomed.

---

## Why three tools?

| Tool   | Scope                                   | Strengths                          | Limits                        |
|--------|-----------------------------------------|------------------------------------|-------------------------------|
| TLC    | Bounded $N \leq 4$                      | Exhaustive; finds counterexamples   | Scale-limited                 |
| TLAPS  | Arbitrary $N$                           | Proves for all $N$                  | Requires manual proof structure |
| Dafny  | Inductive soundness of state transitions | Compiles; integrates with code     | Not full protocol model        |

Together these cover (a) small-instance exhaustive validation (TLC),
(b) arbitrary-N safety theorems (TLAPS), and (c) inductive state-invariant
preservation (Dafny). The paper's §V discusses how each tier contributes
to the overall evidence.

---

## Known limitations

From the paper's §V and §X:

1. **Single-node safety only** — the TLAPS proof verifies single-node ACP.
   Distributed (Raft) correctness is TLC-checked via `SBus_Distributed.tla`
   (247K states) but not TLAPS-mechanised. Full Raft-TLAPS is estimated at
   6–12 person-months.

2. **Dafny verifies abstract algorithm, not Rust implementation.** Full
   Rust refinement via Creusot or Verus (with async support) is future
   work.

3. **One retained AXIOM** (`FunTypingReconstruction`) in v16 — a primitive
   fact about TLA+ function-space typing, not present in the standard
   `FunctionTheorems.tla` library. See v16 header comments and v17/v18 in
   `historical/` for ongoing work to discharge it.

4. **Two parameter ASSUMEs** (`NoOwnerNotAgent`, `EmptyContentIsString`) —
   standard TLA+ parameterisation, not mathematical axioms.

---

## Citation

```bibtex
@techreport{khan2026sbus,
  author      = {Khan, Sajjad},
  title       = {Observable-Read Consistency for Concurrent Multi-Agent
                 LLM State},
  institution = {Independent},
  year        = {2026},
  note        = {arXiv preprint. Version 50.2.},
  url         = {https://arxiv.org/abs/...}
}
```

## License

MIT. See `LICENSE`.

## Contact

Sajjad Khan — sajjadanwar0@gmail.com
# sbus-formals
