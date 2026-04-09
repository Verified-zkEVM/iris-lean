# MoSeL Port to iris-lean — Implementation Plan

**Branch**: `mosel-port` (based on `measureMySpace`)
**Goal**: Port MoSeL proof mode framework to support Bluebell probabilistic logic formalization.

---

## Phase 0: Connect Bluebell Assertions to Iris BI
**Status**: IN PROGRESS

- [x] 0.1 Define missing connectives in `Assertion.lean` (`wand`, `bimp`)
- [ ] 0.2 Prove `sep_ident` (`P *' BTrue ⊣⊢ P`) — currently sorry
- [x] 0.3 Provide discrete OFE/COFE instance for `Assertion M` (via `COFE.ofDiscrete`)
- [x] 0.4 Instantiate `BIBase` for `Assertion M`
- [x] 0.5 Instantiate `BI` for `Assertion M` (compiles with sorry axioms)
- [x] 0.5a Fill in BI axiom proofs (31/36 done, 5 sorry remain for schematic quantifier NE)
- [ ] 0.6 Verify `BIAffine` instance
- [ ] 0.7 Unify notation (alias Bluebell's `*'` etc. to Iris `∗` etc.)

**Key design decisions made:**
- `OneLe M` class: requires `1 ≤ a` for all `a`, satisfied by all Bluebell models
- `persistently P := bpersistently P := {a | P 1}` (not `id` — needed for `persistently_and_l`)
- `later := id` (non-step-indexed model)
- `emp := bident := {a | 1 ≤ a}`
- `wand P Q := {a | ∀ b, P b → Q (a * b)}`
- `imp P Q := bimp P Q := {a | ∀ b ≥ a, P b → Q b}`

## Phase 1: Core MoSeL Type Classes
**Status**: DONE

- [x] 1.1 Define `Frame` class in `Classes.lean`
- [x] 1.2 Define `MaybeFrame` with progress tracking
- [x] 1.3 Define `Make*` classes (`MakeSep`, `MakeAnd`, `MakeOr`)
- [x] 1.4 Restore `FromModal` / `ElimModal` classes
- [x] 1.5 Define `AddModal` class

## Phase 2: `iFrame` Tactic
**Status**: IN PROGRESS

- [x] 2.1 Base frame instances (`frame_here`, `frame_sep_l/r`, `maybeFrame_default`)
- [x] 2.2 `tac_frame'` lemma (takes frame proof explicitly)
- [x] 2.3 `iframe` tactic implementation (uses mkAppOptM + synthInstance)
- [x] 2.4 Basic tests pass (frame_here, frame_sep_l work on Bluebell Assertions)
- [ ] 2.5 Add MakeSep instances to normalize `emp ∗ Q → Q` in frame residuals
- [ ] 2.6 Add more Frame instances (∧, ∨, ∀, ∃, modalities)

## Phase 3: Restore Modality Introduction/Elimination Tactics
**Status**: PENDING

- [ ] 3.1 `imodintro` tactic using `FromModal` + `IsModal`
- [ ] 3.2 `imod` tactic using `ElimModal`
- [ ] 3.3 Standard modality instances (`persistently`, `affinely`, `intuitionistically`)

## Phase 4: Bluebell-Specific Proof Mode Instances
**Status**: PENDING

- [ ] 4.1 `BIAffine`, `Affine`, `Persistent` instances for Bluebell connectives
- [ ] 4.2 `FromPure`/`IntoPure` for `lift φ`
- [ ] 4.3 `FromSep`/`IntoSep` for ownership decomposition
- [ ] 4.4 `Frame` instances for `ownIndexedPSpPm`, `ownPSp`
- [ ] 4.5 Permission-aware framing instances

## Phase 5: Rebuild Bluebell Logic Layer (with MoSeL from day one)
**Status**: PENDING

- [ ] 5.1 Rebuild `Ownership.lean` using Iris BI notation
- [ ] 5.2 Rebuild `WeakestPre.lean` with WP rules as proof mode instances
- [ ] 5.3 Rebuild `JointCondition.lean` with `C_μ` as MoSeL modality
- [ ] 5.4 Register `C_μ` via `FromModal`/`ElimModal`/`IsModal`
- [ ] 5.5 Rebuild Coupling and Relational Lifting

## Phase 6: Advanced Tactics and Integration Testing
**Status**: PENDING

- [ ] 6.1 `iRevert` tactic
- [ ] 6.2 `iCombine` tactic
- [ ] 6.3 Enhanced intro patterns (`#H`, `>`, etc.)
- [ ] 6.4 Bluebell compound tactics (`iCondition`, `iFuse`, `iCoupling`)
- [ ] 6.5 Port examples: One Time Pad, Markov Blankets, MPC

---

## Dependency Graph

```
Phase 0 (BI instance) ──→ Phase 1 (Frame class) ──→ Phase 2 (iFrame)
         │                        │                        │
         │                        ▼                        ▼
         │                  Phase 3 (modality tactics) ──→ Phase 5 (rebuild logic)
         │                                                   │
         └──→ Phase 4 (Bluebell instances) ─────────────────→┘
                                                              │
                                                              ▼
                                                        Phase 6 (polish)
```

## Progress Log

- **2026-04-09**: Plan created. Branch `mosel-port` created from `measureMySpace`.
- **2026-04-09**: Phase 0 structural work done — `wand`, `bimp`, `bpersistently` defined; `BIBase`, discrete COFE, and `BI` instances for `Assertion M` compile (with sorry axiom proofs). Added `OneLe` class. Pre-existing error in `isDistributed` (unknown `i`) unchanged.
- **2026-04-09**: Filled 31/36 BI axiom proofs. Remaining 5 sorries are schematic quantifier NE/encoding issues. Full build clean.
- **2026-04-09**: Phase 1 done — added Frame, MaybeFrame, FromModal, ElimModal, AddModal, Make* classes to Classes.lean.
- **2026-04-09**: Phase 2 started — added base Frame instances (frame_here, frame_sep_l/r, maybeFrame_default).
- **2026-04-09**: Phase 2 core done — `iframe` tactic works on Bluebell goals. Added BIAffine instance. Tests pass.
