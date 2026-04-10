# MoSeL Port to iris-lean — Implementation Plan

**Branch**: `mosel-port` (based on `measureMySpace`)
**Goal**: Port MoSeL proof mode framework to support Bluebell probabilistic logic formalization.

---

## Phase 0: Connect Bluebell Assertions to Iris BI
**Status**: IN PROGRESS

- [x] 0.1 Define missing connectives in `Assertion.lean` (`wand`, `bimp`)
- [x] 0.2 Prove `sep_ident` (`P *' BTrue ⊣⊢ P`)
- [x] 0.3 Provide discrete OFE/COFE instance for `Assertion M` (via `COFE.ofDiscrete`)
- [x] 0.4 Instantiate `BIBase` for `Assertion M`
- [x] 0.5 Instantiate `BI` for `Assertion M` (compiles with sorry axioms)
- [x] 0.5a Fill in ALL BI axiom proofs (36/36 done, 0 sorry in BI instance)
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
**Status**: PARTIAL

- [x] 3.1 `imodintro` tactic for `<pers>` goals (with `Persistent` instance)
- [x] 3.3 `FromModal` instances for `persistently`, `affinely`, `intuitionistically`, `id`
- [ ] 3.1a `imodintro` for `<affine>` and `□` goals
- [ ] 3.2 `imod` tactic using `ElimModal`
- [ ] 3.4 Full context transformation in `imodintro` (IsModal actions)

## Phase 4: Bluebell-Specific Proof Mode Instances
**Status**: DONE

- [x] 4.1 `BIAffine` instance for Bluebell (all propositions affine)
- [x] 4.2 `Persistent` instances for pure, emp, persistently
- [x] 4.3 `FromPure`/`IntoPure` for `lift φ`
- [x] 4.4 Scoped Bluebell notation to avoid Iris conflicts
- [x] 4.5 Comprehensive test suite (12 tests passing)
- [ ] 4.6 `Frame` instances for `ownIndexedPSpPm`, `ownPSp` (deferred)
- [ ] 4.7 Permission-aware framing instances (deferred)

## Phase 5: Rebuild Bluebell Logic Layer (with MoSeL from day one)
**Status**: STRUCTURAL DONE (semantic proofs deferred)

- [x] 5.1 Rebuild `Ownership.lean` — ownPSpPm, ownPSp', own_mono, own_sep_combine, and_to_star
- [x] 5.2 Rebuild `WeakestPre.lean` — wp, wp_cons, wp_frame, wp_seq
- [x] 5.3 Rebuild `JointCondition.lean` — jointCondition, C-CONS, C-FRAME, C-AND
- [ ] 5.4 Register `C_μ` via `FromModal`/`ElimModal`/`IsModal` (pending semantic defs)
- [ ] 5.5 Rebuild Coupling and Relational Lifting (deferred)
- [ ] 5.6 Fill semantic proofs for all sorry statements

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
- **2026-04-09**: iframe normalization: emp ∗ Q → Q and Q ∗ emp → Q in frame residuals.
- **2026-04-09**: Phase 3 partial: imodintro for <pers> goals, FromModal instances for standard modalities.
- **2026-04-10**: Phase 4 done: Bluebell instances (Persistent, IntoPure, etc.), scoped notation, 12 tests.
- **2026-04-10**: Phase 5 structural: Rebuilt Ownership, WeakestPre, JointCondition with MoSeL support.
- **2026-04-10**: All BI axiom proofs complete (0 sorry). sep_ident proved. Only 1 sorry in Assertion.lean (isDistributed).
- **2026-04-10**: imod skeleton added. Sorry count in Assertion.lean: 8 → 1.
