/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Bluebell.Instances

/-! ## Tests: Iris proof mode on Bluebell Assertions -/

section BluebellTests

open Iris.BI Iris.ProofMode

variable {M : Type*} [OrderedUnitalResourceAlgebra M] [Bluebell.OneLe M]
variable {P Q R : Bluebell.Assertion M}

-- Basic entailment
example : P ⊢ P := by
  istart; iintro HP; iexact HP

-- Separating conjunction commutativity
example : P ∗ Q ⊢ Q ∗ P := by
  istart
  iintro ⟨HP, HQ⟩
  isplitr [HP]
  · iexact HQ
  · iexact HP

-- Frame: simple
example : P ∗ Q ⊢ P := by
  istart
  iintro ⟨HP, HQ⟩
  iframe HP
  iclear HQ; iemp_intro

-- Frame then finish
example : P ∗ Q ⊢ P ∗ Q := by
  istart
  iintro ⟨HP, HQ⟩
  iframe HP
  iexact HQ

-- Frame from deeper context
example : P ∗ Q ∗ R ⊢ Q := by
  istart
  iintro ⟨HP, HQ, HR⟩
  iframe HQ
  iclear HP; iclear HR; iemp_intro

-- Pure introduction
example (h : φ) : P ⊢ ⌜φ⌝ := by
  istart; iintro HP; ipure_intro; exact h

-- Conjunction
example : P ∗ Q ⊢ P ∧ Q := by
  istart
  iintro ⟨HP, HQ⟩
  isplit
  · iframe HP; iclear HQ; iemp_intro
  · iframe HQ; iclear HP; iemp_intro

-- Disjunction
example : P ⊢ P ∨ Q := by
  istart; iintro HP; ileft; iexact HP

-- Existential
example {F : Nat → Bluebell.Assertion M} : F 42 ⊢ ∃ n, F n := by
  istart; iintro HP; iexists 42; iexact HP

-- Wand
example : P ⊢ (P -∗ Q) -∗ Q := by
  istart; iintro HP; iintro HPQ; iapply HPQ; iexact HP

-- Modality: persistently on pure
example : (iprop(⌜φ⌝) : Bluebell.Assertion M) ⊢ <pers> ⌜φ⌝ := by
  istart; iintro HP; imodintro; iexact HP

-- Modality elimination: strip <pers>
example : iprop(<pers> P) ⊢ P := by
  istart; iintro HP; imod HP; iexact HP

-- Modality elimination with frame
example : iprop(<pers> P) ∗ Q ⊢ P ∗ Q := by
  istart
  iintro ⟨HP, HQ⟩
  imod HP
  iframe HP
  iexact HQ

end BluebellTests
