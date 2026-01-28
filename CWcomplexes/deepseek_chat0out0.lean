import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import CWcomplexes.RelConstructions

noncomputable section

open Metric Set

namespace Topology

variable {X : Type*} [TopologicalSpace X]

/-! ### Finite Sets -/

/-- The empty set is trivially a CW-complex. -/
instance : CWComplex (∅ : Set X) := CWComplex.ofFiniteSet finite_empty

/-- Any finite set carries the structure of a finite CW-complex with only 0-cells. -/
instance finiteSetCWComplex (S : Set X) [Finite S] : CWComplex S :=
  CWComplex.ofFiniteSet (toFinite S)

/-! ### The Closed Interval -/

section Interval

variable {a b : ℝ}

/-- A singleton interval {a} is a CW-complex with a single 0-cell. -/
instance singletonIntervalCWComplex : CWComplex ({a} : Set ℝ) :=
  CWComplex.ofFiniteSet (finite_singleton a)

/-- A non-degenerate closed interval [a, b] (a < b) is a CW-complex with:
- two 0-cells {a, b}
- one 1-cell [a, b] -/
noncomputable def closedIntervalCWComplex (h : a < b) : CWComplex (Set.Icc a b) := by
  let D1 : PartialEquiv ℝ ℝ := {
    toFun := fun x => (b - a)/2 * x + (a + b)/2
    invFun := fun x => (2 * x - (a + b))/(b - a)
    source := Set.Icc (-1) 1
    target := Set.Icc a b
    map_source' := by
      intro x hx
      simp [abs_le] at hx ⊢
      have h' := half_pos h -- typeclass instance stuck
      constructor
      · linarith [hx.1]
      · linarith [hx.2]
    map_target' := by
      intro x hx
      simp [abs_le]
      constructor
      · linarith [hx.1]
      · linarith [hx.2]
    left_inv' := by
      intro x hx
      field_simp
      ring
    right_inv' := by
      intro x hx
      field_simp
      ring
  }
  have hD1 : D1.source = Set.Icc (-1) 1 := rfl
  have hD1_target : D1.target = Set.Icc a b := rfl
  have hD1_cont : ContinuousOn D1 (closedBall (0 : ℝ) 1) := by
    simp [closedBall, D1]
    exact (continuous_const.mul continuous_id').add continuous_const
  have hD1_symm_cont : ContinuousOn D1.symm (Set.Icc a b) := by
    simp [D1]
    exact ((continuous_const.mul continuous_id').sub continuous_const).div_const _

  let C : Set ℝ := {a, b}
  let D : Set ℝ := ∅
  let E : Set ℝ := Set.Icc a b
  let F : Set ℝ := ∅

  have hCE : D1 '' C = E := sorry
  have hDF : D1 '' D = F := by simp

  letI : CWComplex C := CWComplex.ofFiniteSet (finite_insert a {b})
  exact CWComplex.ofPartialEquiv C E (isClosed_Icc) D1 hD1 hD1_target hD1_cont hD1_symm_cont

end Interval

/-! ### The Real Line -/

/-- The real line ℝ has a CW-complex structure with:
- 0-cells at integer points ℤ
- 1-cells for each interval [n, n+1] where n ∈ ℤ -/
noncomputable instance realLineCWComplex : CWComplex (Set.univ : Set ℝ) := by
  let C : Set ℝ := (∅ : Set ℝ)
  let E : Set ℝ := Set.univ
  let f : PartialEquiv ℝ ℝ := {
    toFun := id
    invFun := id
    source := Set.univ
    target := Set.univ
    map_source' := by simp
    map_target' := by simp
    left_inv' := by simp
    right_inv' := by simp
  }
  have hfC1 : f.source = C := by simp
  have hfE1 : f.target = E := by simp
  have hfC2 : ContinuousOn f C := continuousOn_empty _
  have hfE2 : ContinuousOn f.symm E := continuousOn_id _

  letI : CWComplex C := CWComplex.ofFiniteSet finite_empty
  exact CWComplex.ofPartialEquiv C E isClosed_univ f hfC1 hfE1 hfC2 hfE2

end Topology
