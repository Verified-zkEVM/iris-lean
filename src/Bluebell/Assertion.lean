import Iris.BI.BIBase
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Bluebell.DiscreteCMRA
import Bluebell.MeasureOnSpace
import Iris.BI.BIBase
import Iris.Algebra.UPred

open MeasureTheory

namespace Bluebell

variable {I Var Val : Type*} [DecidableEq Var] [Inhabited Val]

abbrev Assertion (M : Type*) [OrderedUnitalResourceAlgebra M] :=
  UpperSet M

section Formula

/-- Allows us to write `P a` instead of `a ∈ P` -/
instance {M : Type*} [OrderedUnitalResourceAlgebra M] : FunLike (Assertion M) M Prop where
  coe := fun P => P.carrier
  coe_injective' := by intro P Q h; aesop

variable {M : Type*} [OrderedUnitalResourceAlgebra M]

-- @[simp]
def BTrue : Assertion M := {
  carrier := {x | True}
  upper' := by aesop
}

-- @[simp]
def BFalse : Assertion M := {
  carrier := {x | False}
  upper' := by aesop
}

-- @[simp]
def lift (φ : Prop) : Assertion M := {
  carrier := {x | φ}
  upper' := by aesop
}

-- @[simp]
def own (b : M) : Assertion M := {
  carrier := {a | b ≤ a}
  upper' := by
    intro x y h₁ h₂
    have : b ≤ x := by aesop
    have : b ≤ y := by grind
    aesop
}

-- @[simp]
def and (P Q : Assertion M) : Assertion M := {
  carrier := {a | P a ∧ Q a}
  upper' := by
    intro x y h₁ h₂
    have := P.upper'
    have := Q.upper'
    aesop
}

-- @[simp]
def or (P Q : Assertion M) : Assertion M := {
  carrier := {a | P a ∨ Q a}
  upper' := by
    intro x y h₁ h₂
    have := P.upper'
    have := Q.upper'
    aesop
}

-- @[simp]
def sep (P Q : Assertion M) : Assertion M := {
  carrier := {a | ∃ b₁ b₂ : M, (b₁ * b₂) ≤ a ∧ P b₁ ∧ Q b₂}
  upper' := by
    intro a b h₁ h₂
    grind
}

-- @[simp]
def bexists {A : Type*} (K : A → Assertion M) : Assertion M := {
  carrier := {a | ∃ x : A, K x a}
  upper' := by
    intro a b h₁ h₂
    have h₃ : ∃ x : A, K x a := by aesop
    obtain ⟨x, h₃⟩ := h₃
    have := (K x).upper'
    use x
    aesop
}

-- @[simp]
def bforall {A : Type*} (K : A → Assertion M) : Assertion M := {
  carrier := {a | ∀ x : A, K x a}
  upper' := by
    intro a b h₁ h₂ x
    have h₃ : ∀ x : A, K x a := by aesop
    have := (K x).upper'
    aesop
}

@[simp]
def entail (P Q : Assertion M) : Prop :=
  ∀ m, P m → Q m

@[simp]
def bientail (P Q : Assertion M) : Prop :=
  entail P Q ∧ entail Q P

notation:30 "⊢ " P => entail BTrue P
notation:30 P " ⊢ " Q => entail P Q
notation:30 P " ⊣⊢ " Q => bientail P Q
notation:40 "∀'" K => bforall K
notation:40 "∃'" K => bexists K
notation:50 "⌈" φ "⌉" => lift φ
notation:60 P:60 " ∧' " Q:60 => and P Q
notation:60 P " ∨' " Q => or P Q
notation:70 P:70 " *' " Q:71 => sep P Q

structure IxCompatiblePermission (P : I → PSp (Var → Val)) where
  perm : I → Permission Var
  comp : ∀ i, (P i).compatiblePerm (perm i)

def ownIndexedPSpPm (P : I → PSp (Var → Val)) (p : IxCompatiblePermission P)
  : Assertion (IndexedPSpPm I Var Val) :=
  own (fun i ↦ ⟨⟨P i, p.perm i⟩, p.comp i⟩) ∧' lift (∀ i : I, (P i).isSome)

def ownPSp (P : I → PSp (Var → Val)) : Assertion (IndexedPSpPm I Var Val) :=
  bexists (fun p : IxCompatiblePermission P =>
    ownIndexedPSpPm P p)

def AlmostMeasurable {A : Type*} [MeasurableSpace A]
  (E : (Var → Val) → A) (P : PSp (Var → Val)) :=
  match P with
  | none => False
  | some p => AEMeasurable E p.1.μ

def HasDistribution {A : Type*} [MeasurableSpace A]
  (E : (Var → Val) → A) (i : I) (p : Measure A)
  : Assertion (IndexedPSpPm I Var Val) :=
  bexists (fun P : I → PSp (Var → Val) =>
    ownPSp P *' lift (
      let pi := P i
      match pi with
      | none => False
      | some pi =>
        let μᵢ := pi.1.μ
        let μᵢ.push := @μᵢ.map (Var → Val) A pi.1.ms _
        AlmostMeasurable E pi
        ∧ μᵢ.push E = p
    )
  )

notation:100 E:100 "⟨" i:100 "⟩" " ~ " p:100 => HasDistribution E i p

def AlmostTrue {A : Type*} [MeasurableSpace A]
  (E : (Var → Val) → Bool) (i : I)
  : Assertion (IndexedPSpPm I Var Val) :=
  E⟨i⟩ ~ Measure.dirac True

-- Counterexample: EDistInj is false without a validity hypothesis.
-- We construct m with (m ()).1.1 = ⊤, and two witnesses P, P' with
-- different pushforward measures.
-- Counterexample: EDistInj is false without a validity hypothesis.
-- We pick I = Var = Unit, Val = A = Bool, and m with (m ()).1.1 = ⊤.
-- Two witnesses P, P' use different Dirac PSpaces, giving μ ≠ μ'.
noncomputable section Counterexample

-- Permission with value 1 at (): gives Irr = ∅, so compatiblePerm is vacuous
private def cex_perm : Permission Unit := Multiplicative.ofAdd (fun _ => (1 : ℚ≥0))

-- PSpace with ⊤ σ-algebra and Dirac measure at (fun _ => b)
private def cex_pspace (b : Bool) : PSpace (Unit → Bool) := ⟨{
  ms := ⊤
  μ := @Measure.dirac _ ⊤ (fun _ => b)
}, by constructor; simp⟩

-- State with ⊤ at PSp component; permission = cex_perm
private def cex_m : IndexedPSpPm Unit Unit Bool :=
  fun _ => ⟨(none, cex_perm), trivial⟩

-- compatiblePerm (cex_pspace b) cex_perm holds because Irr cex_perm = ∅
private lemma cex_compat (b : Bool) :
    PSpace.compatiblePerm (cex_pspace b) cex_perm := by
  intro u _ s _ x hx _
  -- hx : x ∈ Irr cex_perm, but Irr cex_perm = ∅ since cex_perm () = 1 ≠ 0
  exfalso
  simp [Irr, cex_perm, Multiplicative.ofAdd] at hx

private lemma cex_measurable :
    @Measurable (Unit → Bool) Bool ⊤ ⊤ (fun f => f ()) := by
  intro s _; exact trivial

-- Helper: build the HasDistribution witness for a given Bool
private lemma cex_hasDist (b : Bool) :
    letI : MeasurableSpace Bool := ⊤
    (HasDistribution (I := Unit) (Var := Unit) (Val := Bool)
      (fun f => f ()) ()
      (@Measure.dirac Bool ⊤ b)) cex_m := by
  -- Provide P, b₁, b₂, and all proofs
  show ∃ P, (ownPSp P *' lift _) cex_m
  use fun _ => some (cex_pspace b)
  show ∃ b₁ b₂, b₁ * b₂ ≤ cex_m ∧ ownPSp _ b₁ ∧ _
  -- b₁ = the ownership witness, b₂ = 1
  refine ⟨fun _ => ⟨(some (cex_pspace b), cex_perm), cex_compat b⟩, 1, ?_, ?_, ?_⟩
  · -- b₁ * 1 ≤ cex_m
    simp only [mul_one]
    intro i
    show (⟨(some (cex_pspace b), cex_perm), _⟩ : PSpPm Unit Bool) ≤
         (⟨(none, cex_perm), _⟩ : PSpPm Unit Bool)
    constructor
    · exact le_top
    · exact le_refl _
  · -- ownPSp
    use ⟨fun _ => cex_perm, fun _ => cex_compat b⟩
    constructor
    · -- own: v_P ≤ b₁ (they're equal)
      intro i
      exact le_refl _
    · -- lift: ∀ i, (P i).isSome
      intro _; rfl
  · -- lift: match body (AlmostMeasurable ∧ pushforward eq)
    simp only [cex_pspace, AlmostMeasurable]
    constructor
    · exact cex_measurable.aemeasurable
    · ext s hs
      rw [Measure.map_apply cex_measurable hs]
      simp only [Measure.dirac_apply' _ hs, Set.indicator]
      -- Goal: (if (fun x => b) ∈ (fun f => f ()) ⁻¹' s then 1 else 0) = (if b ∈ s then 1 else 0)
      -- These are equal because (fun x => b) ∈ (fun f => f ()) ⁻¹' s ↔ b ∈ s
      have : (fun _ : Unit => b) ∈ (fun f : Unit → Bool => f ()) ⁻¹' s ↔ b ∈ s := by
        simp [Set.mem_preimage]
      split_ifs <;> simp_all

end Counterexample

namespace Attempt2

def HasDistribution2 {A : Type*} [MeasurableSpace A]
  (E : (Var → Val) → A) (i : I) (p : Measure A)
  : Assertion (IndexedPSpPm I Var Val) :=
  bexists (fun P : I → PSpace (Var → Val) =>
    ownPSp (fun i => some (P i)) *' lift (
      let μᵢ := (P i).1.μ
      let μᵢ.push := @μᵢ.map (Var → Val) A (P i).1.ms _
      AlmostMeasurable E (P i)
      ∧ μᵢ.push E = p
    )
  )

notation:100 E:100 "⟨" i:100 "⟩₂" " ~ " p:100 => HasDistribution2 E i p

-- HasDistribution2 is still false: ownPSp gives some (P i) ≤ (m i).1.1,
-- and some x ≤ ⊤ is trivially true when (m i).1.1 = ⊤.
-- Same counterexample: cex_m with ⊤ at PSp, two different Dirac witnesses.

private lemma cex_hasDist2 (b : Bool) :
    letI : MeasurableSpace Bool := ⊤
    (HasDistribution2 (I := Unit) (Var := Unit) (Val := Bool)
      (fun f => f ()) ()
      (@Measure.dirac Bool ⊤ b)) cex_m := by
  show ∃ P : Unit → PSpace (Unit → Bool), (ownPSp (fun i => some (P i)) *' lift _) cex_m
  use fun _ => cex_pspace b
  show ∃ b₁ b₂, b₁ * b₂ ≤ cex_m ∧ ownPSp _ b₁ ∧ _
  refine ⟨fun _ => ⟨(some (cex_pspace b), cex_perm), cex_compat b⟩, 1, ?_, ?_, ?_⟩
  · simp only [mul_one]
    intro j
    show (⟨(some (cex_pspace b), cex_perm), _⟩ : PSpPm Unit Bool) ≤
         (⟨(none, cex_perm), _⟩ : PSpPm Unit Bool)
    exact ⟨le_top, le_refl _⟩
  · use ⟨fun _ => cex_perm, fun _ => cex_compat b⟩
    exact ⟨fun _ => le_refl _, fun _ => rfl⟩
  · simp only [cex_pspace, AlmostMeasurable]
    exact ⟨cex_measurable.aemeasurable, by
      ext s hs
      rw [Measure.map_apply cex_measurable hs]
      simp only [Measure.dirac_apply' _ hs, Set.indicator]
      have : (fun _ : Unit => b) ∈ (fun f : Unit → Bool => f ()) ⁻¹' s ↔ b ∈ s := by
        simp [Set.mem_preimage]
      split_ifs <;> simp_all⟩

def E : (Unit → Bool) → Bool := fun f => f ()
def i : Unit := ()

example : ∃ (m : IndexedPSpPm Unit Unit Bool) (μ μ' : @Measure Bool ⊤),
    μ ≠ μ' ∧ m ∈ (E⟨i⟩₂ ~ μ ∧' E⟨i⟩₂ ~ μ') := by
  refine ⟨cex_m, @Measure.dirac Bool ⊤ true, @Measure.dirac Bool ⊤ false, ?_, ?_, ?_⟩
  · intro h
    have : (@Measure.dirac Bool ⊤ true) {true} = (@Measure.dirac Bool ⊤ false) {true} :=
      congrFun (congrArg _ h) _
    simp at this
  · exact cex_hasDist2 true
  · exact cex_hasDist2 false

end Attempt2

theorem EDistInj
  {A : Type*} [MeasurableSpace A]
  {E : (Var → Val) → A} {i : I} {μ μ' : Measure A}
  : (E⟨i⟩ ~ μ ∧' E⟨i⟩ ~ μ') ⊢ ⌈μ = μ'⌉ := by
  intro m h
  obtain ⟨h₁, h₂⟩ := h
  obtain ⟨P, b₁, b₂, hle, ⟨p, hpown, hsome⟩, body⟩ := h₁
  obtain ⟨P', b₁', b₂', hle', ⟨p', hpown', hsome'⟩, body'⟩ := h₂
  have hPi_some : (P i).isSome := hsome i
  have hP'i_some : (P' i).isSome := hsome' i
  set x := Option.get (P i) hPi_some with hx_def
  set x' := Option.get (P' i) hP'i_some with hx'_def
  have hPi_eq : P i = some x := (Option.some_get hPi_some).symm
  have hP'i_eq : P' i = some x' := (Option.some_get hP'i_some).symm
  rw [hPi_eq] at body
  rw [hP'i_eq] at body'
  simp only [lift] at body body'
  obtain ⟨ham, hμ₁⟩ := body
  obtain ⟨ham', hμ₂⟩ := body'
  have hpown_i := hpown i
  have hpown'_i := hpown' i
  have hle_i := hle i
  have hle'_i := hle' i
  have hPi_le : P i ≤ (m i).1.1 := by
    have hPi_le_b₁ : P i ≤ (b₁ i).1.1 := hpown_i.1
    have hb₁_le_mul : (b₁ i).1.1 ≤ (b₁ i).1.1 * (b₂ i).1.1 := PSp.le_of_mul_left
    have hmul_le_m : (b₁ i).1.1 * (b₂ i).1.1 ≤ (m i).1.1 := hle_i.1
    exact le_trans hPi_le_b₁ (le_trans hb₁_le_mul hmul_le_m)
  have hP'i_le : P' i ≤ (m i).1.1 := by
    have hP'i_le_b₁ : P' i ≤ (b₁' i).1.1 := hpown'_i.1
    have hb₁'_le_mul : (b₁' i).1.1 ≤ (b₁' i).1.1 * (b₂' i).1.1 := PSp.le_of_mul_left
    have hmul_le_m : (b₁' i).1.1 * (b₂' i).1.1 ≤ (m i).1.1 := hle'_i.1
    exact le_trans hP'i_le_b₁ (le_trans hb₁'_le_mul hmul_le_m)
  rw [hPi_eq] at hPi_le
  rw [hP'i_eq] at hP'i_le
  show μ = μ'
  rw [← hμ₁, ← hμ₂]
  #check (m i)
  -- Case on (m i).1.1
  match hy : (m i).1.1 with
  | none =>
    sorry
  | some y =>
    rw [hy] at hPi_le hP'i_le
    have hxy : x ≤ y := WithTop.coe_le_coe.mp hPi_le
    have hx'y : x' ≤ y := WithTop.coe_le_coe.mp hP'i_le
    ext u hu
    rw [Measure.map_apply_of_aemeasurable ham hu,
        Measure.map_apply_of_aemeasurable ham' hu]
    set f := AEMeasurable.mk E ham with hf_def
    set f' := AEMeasurable.mk E ham' with hf'_def
    have hf_meas : @Measurable _ _ x.1.ms _ f := AEMeasurable.measurable_mk ham
    have hf'_meas : @Measurable _ _ x'.1.ms _ f' := AEMeasurable.measurable_mk ham'
    have hf_ae : f =ᵐ[x.1.μ] E := (AEMeasurable.ae_eq_mk ham).symm
    have hf'_ae : f' =ᵐ[x'.1.μ] E := (AEMeasurable.ae_eq_mk ham').symm
    have h1 : x.1.μ (E ⁻¹' u) = x.1.μ (f ⁻¹' u) :=
      MeasureTheory.measure_congr (hf_ae.symm.preimage u)
    have h3 : x'.1.μ (E ⁻¹' u) = x'.1.μ (f' ⁻¹' u) :=
      MeasureTheory.measure_congr (hf'_ae.symm.preimage u)
    have h2 : x.1.μ (f ⁻¹' u) = y.1.μ (f ⁻¹' u) :=
      MeasureOnSpace.le_preserves_measure hxy (hf_meas hu)
    have h4 : x'.1.μ (f' ⁻¹' u) = y.1.μ (f' ⁻¹' u) :=
      MeasureOnSpace.le_preserves_measure hx'y (hf'_meas hu)
    have extend_ae : ∀ {g : (Var → Val) → A} {z : PSpace (Var → Val)}
        (hzy : z ≤ y) (_ : g =ᵐ[z.1.μ] E), g =ᵐ[y.1.μ] E := by
      intro g z hzy hg_ae
      rw [Filter.EventuallyEq, MeasureTheory.ae_iff] at hg_ae ⊢
      rcases @MeasureTheory.exists_measurable_superset_of_null _ z.1.ms z.1.μ _ hg_ae
        with ⟨N, hN_sub, hN_meas, hN_null⟩
      have hN_y : y.1.μ N = 0 := by
        rw [← hN_null]
        exact (MeasureOnSpace.le_preserves_measure hzy hN_meas).symm
      exact measure_mono_null hN_sub hN_y
    have hf_ae_y : f =ᵐ[y.1.μ] E := extend_ae hxy hf_ae
    have hf'_ae_y : f' =ᵐ[y.1.μ] E := extend_ae hx'y hf'_ae
    have hff'_ae : f =ᵐ[y.1.μ] f' := hf_ae_y.trans hf'_ae_y.symm
    have h5 : y.1.μ (f ⁻¹' u) = y.1.μ (f' ⁻¹' u) :=
      MeasureTheory.measure_congr (hff'_ae.preimage u)
    rw [h1, h2, h5, ← h4, ← h3]

theorem EDiracDup
  {A : Type*} [MeasurableSpace A]
  {E : (Var → Val) → A} (i : I) (v : A)
  :   (E⟨i⟩ ~ Measure.dirac v)
    ⊢ (E⟨i⟩ ~ Measure.dirac v *' E⟨i⟩ ~ Measure.dirac v) := by
  intro m hm
  sorry

@[simp]
def bProp (I Var Val : Type*) [DecidableEq Var] [Inhabited Val] :=
  Assertion (IndexedPSpPm I Var Val)

end Formula

section Properties

theorem sep_ident {P : bProp I Var Val}
  : P *' BTrue ⊣⊢ P := by
  sorry

theorem sep_comm {P Q : bProp I Var Val}
  : P *' Q ⊣⊢ Q *' P := by
  constructor
  · intro m hm
    obtain ⟨b₁, ⟨b₂, h⟩⟩ := hm
    use b₂, b₁
    have : b₁ * b₂ = b₂ * b₁ := CommMonoid.mul_comm b₁ b₂
    aesop
  · intro m hm
    obtain ⟨b₁, ⟨b₂, h⟩⟩ := hm
    use b₂, b₁
    have : b₁ * b₂ = b₂ * b₁ := CommMonoid.mul_comm b₁ b₂
    aesop

end Properties

end Bluebell
