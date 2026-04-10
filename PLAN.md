# MoSeL Port to iris-lean — Implementation Plan & Status

**Branch**: `mosel-port` (based on `measureMySpace`)
**Goal**: Port MoSeL proof mode framework to support Bluebell probabilistic logic formalization.
**Started**: 2026-04-09

---

## Overview

This branch adds MoSeL (Modal Separation Logic) proof mode support to iris-lean,
specifically designed to enable interactive proofs for the Bluebell probabilistic
program logic. The work connects Bluebell's `Assertion M` type (upward-closed
predicates on an ordered unital resource algebra) to the Iris BI framework, adds
key missing type classes and tactics, and rebuilds the Bluebell logic layer with
MoSeL integration from day one.

### Key Design Decisions

1. **`OneLe M` class**: Requires `1 ≤ a` for all `a : M`. Satisfied by all Bluebell models (PSp, Permission, PSpPm, IndexedPSpPm). Required for affinity and the BI instance.

2. **`persistently P := bpersistently P := {a | P 1}`**: The persistence modality evaluates P at the unit element (= core). NOT identity — needed for `persistently_and_l` axiom.

3. **`later := id`**: Non-step-indexed model. All later axioms become trivial.

4. **`BIAffine` for Bluebell**: All Bluebell assertions are affine (`P ⊢ emp` for all P) since `1 ≤ a` for all a. This simplifies many proof mode operations.

5. **Bluebell notation scoped**: Custom notation (`*'`, `⊢`, `⊣⊢`, etc.) is `scoped` to avoid conflicts with Iris BI notation.

6. **`iframe` uses `mkAppOptM` + `synthInstance`**: Avoids Qq elaboration-time TC resolution issues by building Frame instance synthesis at runtime.

### Known Issues

- **BIBase instance diamond**: When writing proofs that cross between Bluebell's direct `UpperSet` membership (`P m`) and Iris's `BIBase.Entails P Q` (which unfolds to `∀ m, P m → Q m`), Lean's TC synthesis can get confused. This blocks some ownership proofs in `Logic/Ownership.lean`. Workaround: use `by intro m hm; ...` tactic mode which forces reduction.

- **`sForall`/`sExists` encoding**: Iris's schematic quantifiers use `PROP → Prop` predicates with `liftRel`-based NE conditions. Proofs involving these (like `persistently_sExists_1`) require careful witness construction with `⟨_, ⟨_, ⟨p, rfl⟩, rfl⟩, ...⟩`.

---

## Phase Status

### Phase 0: Connect Bluebell Assertions to Iris BI — COMPLETE
**Files**: `src/Bluebell/Assertion.lean`

- [x] Define `wand`, `bimp` (implication), `bpersistently` connectives
- [x] Define `OneLe` class
- [x] Prove `sep_ident` (`P *' BTrue ⊣⊢ P`)
- [x] Provide discrete `COFE` instance (via `COFE.ofDiscrete`)
- [x] Instantiate `BIBase` for `Assertion M`
- [x] Instantiate full `BI` for `Assertion M` — **all 36 axioms proved (0 sorry)**
- [x] Instantiate `BIAffine`

**Remaining sorry**: 1 (`isDistributed` definition — pre-existing, needs PSp projection work)

### Phase 1: Core MoSeL Type Classes — COMPLETE
**Files**: `src/Iris/ProofMode/Classes.lean`

- [x] `Frame p R P Q` — core class for `iframe` tactic
- [x] `MaybeFrame p R P Q progress` — with progress tracking
- [x] `FromModal φ M sel P Q` — for `imodintro`
- [x] `ElimModal φ p p' P P' Q Q'` — for `imod`
- [x] `AddModal P P' Q` — modality-aware goal transformation
- [x] `MakeSep P Q PQ`, `MakeAnd`, `MakeOr` — normalization

### Phase 2: `iframe` Tactic — COMPLETE
**Files**: `src/Iris/ProofMode/Instances.lean`, `src/Iris/ProofMode/Tactics/Frame.lean`

- [x] `frame_here` instance (R = goal, residual = emp)
- [x] `frame_sep_l` instance (frame in left of `∗`)
- [x] `frame_sep_r` instance (frame in right of `∗`)
- [x] `maybeFrame_default` fallback (no progress)
- [x] `MakeSep` instances (emp_l, emp_r, default)
- [x] `tac_frame'` lemma (explicit frame proof)
- [x] `iframe H` tactic with emp normalization
- [x] Tests: 3 frame tests passing
- [ ] Additional Frame instances (∧, ∨, ∀, ∃, modalities)

### Phase 3: Modality Tactics — PARTIAL
**Files**: `src/Iris/ProofMode/Tactics/ModIntro.lean`, `src/Iris/ProofMode/Tactics/Mod.lean`, `src/Iris/ProofMode/ModalityInstances.lean`

- [x] `imodintro` — strips `<pers>` from goal (requires `Persistent Q`)
- [x] `imod H` — strips `<pers>` from hypothesis H (requires `BIAffine`)
- [x] `FromModal` instances for `persistently`, `affinely`, `intuitionistically`, `id`
- [x] `persistently_elim_affine` lemma (`<pers> P ⊢ P` in affine logics)
- [x] `replaces_of_entails` lemma (general hypothesis weakening)
- [ ] `imodintro` for `<affine>` and `□` goals (sorry proofs)
- [ ] Full `imod` with `ElimModal` and goal transformation
- [ ] Full context transformation in `imodintro` (IsModal actions)

### Phase 4: Bluebell Proof Mode Instances — COMPLETE
**Files**: `src/Bluebell/Instances.lean`, `src/Bluebell/Tests.lean`

- [x] `Persistent` instances for pure, emp, persistently
- [x] `IntoPure`/`FromPure` for `lift φ`
- [x] `BIAffine` (all propositions affine via `OneLe`)
- [x] Scoped Bluebell notation
- [x] **14 comprehensive tests passing**:
  - Basic entailment, sep commutativity
  - Frame (simple, frame-then-finish, deep context)
  - Pure introduction, conjunction, disjunction, existential
  - Wand intro/elim, modality intro, modality elimination
- [ ] `Frame` instances for `ownIndexedPSpPm`, `ownPSp`
- [ ] Permission-aware framing

### Phase 5: Bluebell Logic Layer — STRUCTURAL (semantic proofs pending)
**Files**: `src/Bluebell/Logic/Ownership.lean`, `src/Bluebell/Logic/WeakestPre.lean`, `src/Bluebell/Logic/JointCondition.lean`

- [x] `Ownership.lean`: `ownPSpPm`, `ownPSp'`, `own_mono`, `own_sep_combine`, `and_to_star`
- [x] `WeakestPre.lean`: `wp`, `wp_cons`, `wp_frame`, `wp_seq`
- [x] `JointCondition.lean`: `jointCondition`, C-CONS, C-FRAME, C-AND
- [ ] Register `C_μ` via `FromModal`/`ElimModal`/`IsModal`
- [ ] Coupling and Relational Lifting
- [ ] Fill semantic proofs (blocked by BIBase instance diamond for ownership)

### Phase 6: Advanced Tactics & Examples — PENDING

- [ ] `iRevert` tactic
- [ ] `iCombine` tactic
- [ ] Enhanced intro patterns (`#H`, `>`)
- [ ] Bluebell compound tactics (`iCondition`, `iFuse`, `iCoupling`)
- [ ] Port examples: One Time Pad, Markov Blankets, MPC

---

## File Inventory

### New files created on this branch:

| File | Lines | Sorries | Purpose |
|------|-------|---------|---------|
| `src/Iris/ProofMode/Tactics/Frame.lean` | 82 | 0 | `iframe` tactic |
| `src/Iris/ProofMode/Tactics/ModIntro.lean` | 56 | 2 | `imodintro` tactic |
| `src/Iris/ProofMode/Tactics/Mod.lean` | 63 | 0 | `imod` tactic |
| `src/Bluebell/Instances.lean` | 53 | 0 | Proof mode instances |
| `src/Bluebell/Tests.lean` | 78 | 0 | 14 test examples |
| `src/Bluebell/Logic/Ownership.lean` | 67 | 3 | Ownership assertions |
| `src/Bluebell/Logic/WeakestPre.lean` | 57 | 4 | Weakest precondition |
| `src/Bluebell/Logic/JointCondition.lean` | 85 | 4 | Joint conditioning |

### Modified files:

| File | Key Changes |
|------|-------------|
| `src/Bluebell/Assertion.lean` | Added wand, bimp, bpersistently, OneLe, OFE/COFE/BIBase/BI/BIAffine instances, scoped notation, proved sep_ident. 1 sorry remaining (isDistributed). |
| `src/Iris/ProofMode/Classes.lean` | Added Frame, MaybeFrame, FromModal, ElimModal, AddModal, MakeSep, MakeAnd, MakeOr classes. |
| `src/Iris/ProofMode/Instances.lean` | Added Frame instances (frame_here, frame_sep_l/r, maybeFrame_default) and MakeSep instances. |
| `src/Iris/ProofMode/ModalityInstances.lean` | Added FromModal instances and import for Classes. |
| `src/Iris/ProofMode/Tactics.lean` | Added imports for Frame, ModIntro, Mod. |

---

## Sorry Summary

| File | Count | Nature |
|------|-------|--------|
| `Assertion.lean` | 1 | `isDistributed` def (pre-existing, needs PSp projection) |
| `Tactics/ModIntro.lean` | 2 | `tac_affinely_intro`, `tac_intuitionistically_intro` proofs |
| `Logic/Ownership.lean` | 3 | `and_to_star`, `own_mono`, `own_sep_combine` (diamond issue) |
| `Logic/WeakestPre.lean` | 4 | `wp` def, `wp_cons`, `wp_frame`, `wp_seq` (semantic) |
| `Logic/JointCondition.lean` | 4 | `jointCondition` def, C-CONS, C-FRAME, C-AND (semantic) |
| **Total** | **14** | |

---

## Dependency Graph

```
Phase 0 (BI instance) ──→ Phase 1 (type classes) ──→ Phase 2 (iframe) ✓
         │                        │                        │
         │                        ▼                        ▼
         │                  Phase 3 (modality)        Phase 4 (instances) ✓
         │                        │                        │
         └──→ Phase 5 (logic layer) ◄─────────────────────┘
                    │
                    ▼
              Phase 6 (polish)
```

## Progress Log

- **2026-04-09**: Plan created. Branch `mosel-port` created from `measureMySpace`.
- **2026-04-09**: Phase 0 done: BI instance for Assertion M with 31/36 axiom proofs.
- **2026-04-09**: Phase 1 done: Added all MoSeL type classes.
- **2026-04-09**: Phase 2 done: `iframe` tactic working with emp normalization.
- **2026-04-09**: Phase 3 started: `imodintro` for `<pers>` goals.
- **2026-04-10**: Phase 4 done: Bluebell instances, scoped notation, 12 tests.
- **2026-04-10**: Phase 5 structural: Rebuilt Ownership, WeakestPre, JointCondition.
- **2026-04-10**: BI instance fully proved (36/36 axioms, 0 sorry).
- **2026-04-10**: `sep_ident` proved. Assertion.lean down to 1 sorry.
- **2026-04-10**: `imod H` implemented for stripping `<pers>`. 14 tests passing.
- **2026-04-10**: Ownership proofs attempted but blocked by instance diamond.
