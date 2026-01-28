import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import CWcomplexes.RelConstructions

/-!
# Examples of CW-complexes

In this file we present some examples of CW-complexes:
## Main definitions
* `instEmpty`: The empty set is a CW-complex.
* `instFiniteSet`: Every finite set is a CW-complex.
* `instIcc`: The interval `Icc a b` in `ℝ` is a CW-complex.
* `instReal`: The real numbers are a CW-complex.
-/
noncomputable section

open Metric Set

namespace Topology.CWComplex

variable {X : Type*} [t : TopologicalSpace X] [T2Space X]

/-! # CW-complex structure on the interval -/

/-- An auxiliary bijection sending the closed unit ball in `Fin 1 → ℝ` to a desired (non-degenerate)
  closed interval. -/
@[simps! -isSimp]
def mapLT {a b : ℝ} (hab : a < b) := (IsometryEquiv.funUnique (Fin 1) ℝ).toHomeomorph.trans
    (affineHomeomorph ((b - a) / 2) ((a + b) / 2) (by linarith))

/-- `mapLT` sends the closed unit ball to the desired closed interval. -/
lemma mapLT_image_closedBall {a b : ℝ} (hab : a < b) : mapLT hab '' closedBall 0 1 = Icc a b := by
  change (((affineHomeomorph ((b - a) / 2) ((a + b) / 2) (by linarith))) ∘
    (IsometryEquiv.funUnique (Fin 1) ℝ)) '' closedBall 0 1 = Icc a b
  rw [image_comp, IsometryEquiv.image_closedBall,
    IsometryEquiv.funUnique_apply, Pi.zero_apply, Real.closedBall_eq_Icc, zero_sub, zero_add,
    affineHomeomorph_image_Icc _ _ _ _ (by linarith)]
  ring_nf

/-- `mapLT` sends the unit ball to the desired open interval. -/
lemma mapLT_image_ball {a b : ℝ} (hab : a < b) : mapLT hab '' ball 0 1 = Ioo a b := by
  change (((affineHomeomorph ((b - a) / 2) ((a + b) / 2) (by linarith))) ∘
    (IsometryEquiv.funUnique (Fin 1) ℝ)) '' ball 0 1 = Ioo a b
  rw [image_comp, IsometryEquiv.image_ball,
    IsometryEquiv.funUnique_apply, Pi.zero_apply, Real.ball_eq_Ioo, zero_sub, zero_add,
    affineHomeomorph_image_Ioo _ _ _ _ (by linarith)]
  ring_nf

/-- `mapLT` sends the unit sphere to the set of specified points. -/
lemma mapLT_image_sphere {a b : ℝ} (hab : a < b) : mapLT hab '' sphere 0 1 = {a, b} := by
  rw [← closedBall_diff_ball, image_diff (mapLT hab).injective, mapLT_image_closedBall,
    mapLT_image_ball]
  exact Icc_diff_Ioo_same (le_of_lt hab)

/-- `mapLT` as a partial bijection. -/
@[simps! -isSimp]
def mapLTPartial {a b : ℝ} (hab : a < b) :=
  (mapLT hab).toPartialEquivOfImageEq (ball 0 1) (Ioo a b) (mapLT_image_ball hab)

-- this simp never actually gets used because of the automatically generated simps above
@[simp]
lemma mapLTPartial_image {a b : ℝ} (hab : a < b) {s : Set (Fin 1 → ℝ)} :
    mapLTPartial hab '' s = mapLT hab '' s :=
  rfl

--set_option trace. in
--set_option trace.Meta.Tactic.simp.rewrite true in
/-- A helper definition for `instIccLT` where the set is presented differently. -/
protected def instIccLT' {a b : ℝ} (hab : a < b) :
    CWComplex (mapLTPartial hab '' closedBall 0 1 ∪ {a, b}) :=
  letI := CWComplex.ofFiniteSet (C := {a, b}) (toFinite {a, b})
  letI := CWComplex.finite_ofFiniteSet (C := {a, b}) (toFinite {a, b})
  attachCellFiniteType {a, b}
    (mapLTPartial hab)
    (source_eq' := rfl)
    (continuousOn' := (mapLT hab).continuous.continuousOn)
    (continuousOn_symm' := (mapLT hab).symm.continuous.continuousOn)
    (disjoint' := by
      intro m i
      simp only [mapLTPartial_image, mapLT_image_ball]
      exact match m, i with
        | 0, ⟨i, hi⟩ => by
          simp only [openCell_zero_eq_singleton, ofFiniteSet_map,
            PartialEquiv.single_apply, Function.const_apply, disjoint_singleton_right, mem_Ioo,
            not_and, not_lt]
          intro hai
          apply le_of_eq
          have : i = a ∨ i = b := by simp_all
          rcases this with hi | hi
          · subst i
            exact hai.false.elim
          · exact hi.symm
        | (_ + 1), i => i.elim)
    (mapsTo := by
      simp [closedCell_zero_eq_singleton, mapsTo_iff_image_subset, mapLT_image_sphere, subset_def,
        ofFiniteSet_map, ofFiniteSet_cell_zero])

/-- A helper lemma for `Finite_IccLT`. -/
protected lemma finite_instIccLT' {a b : ℝ} (hab : a < b) :
    letI := CWComplex.instIccLT' hab
    Finite (mapLTPartial hab '' closedBall 0 1 ∪ {a, b}) :=
  letI := CWComplex.ofFiniteSet (C := {a, b}) (toFinite {a, b})
  letI := CWComplex.finite_ofFiniteSet (C := {a, b}) (toFinite {a, b})
  finite_attachCellFiniteType ..

/-- A (non-degenerate) closed interval is a CW-complex. -/
def instIccLT {a b : ℝ} (hab : a < b) : CWComplex (Icc a b : Set ℝ) :=
  letI := CWComplex.instIccLT' hab
  ofEq (mapLTPartial hab '' closedBall 0 1 ∪ {a, b})
     (by
       rw [mapLTPartial_image, mapLT_image_closedBall, union_eq_left, pair_subset_iff,
         left_mem_Icc,
         right_mem_Icc, and_self]
       exact hab.le)

/-- The CW complex structure on a (non-degenerate) closed interval is finite. -/
lemma finite_instIccLT {a b : ℝ} (hab : a < b) :
    letI := instIccLT hab
    Finite (Icc a b) :=
  let _ := instIccLT hab
  let _ := CWComplex.instIccLT' hab
  let _ := CWComplex.finite_instIccLT' hab
  finite_ofEq (mapLTPartial hab '' closedBall 0 1 ∪ {a, b})
    (by
      rw [mapLTPartial_image, mapLT_image_closedBall, union_eq_left, pair_subset_iff, left_mem_Icc,
        right_mem_Icc, and_self]
      exact hab.le)

/- **ToDo** : Write simp lemmas about `instIcc`. -/

/-- The interval `Icc a b` in `ℝ` is a CW-complex. -/
instance instIcc {a b : ℝ} : CWComplex (Icc a b : Set ℝ) :=
  if lt1 : a < b then instIccLT lt1
    else if lt2 : b < a then Icc_eq_empty_of_lt lt2 ▸ ofFiniteSet finite_empty
      else le_antisymm (le_of_not_gt lt2) (le_of_not_gt lt1) ▸
        Icc_self a ▸ ofFiniteSet (toFinite {a})

/-! # The CW-complex structure on the real numbers -/

/- **Commment**: This reuses the auxiliary definitions and lemmas of the interval. -/

/-- The real numbers are a CW-complex. -/
@[simps (nameStem := "instReal")]
instance instReal : CWComplex (univ : Set ℝ) where
  cell n := match n with
    | 0 => ℤ
    | 1 => ℤ
    | (_ + 2) => PEmpty
  map n i := match n with
    | 0 => PartialEquiv.single ![] i
    | 1 => mapLTPartial (lt_add_one (i : ℝ))
    | (_ + 2) => i.elim
  source_eq n i := match n with
    | 0 => by simp [ball, Matrix.empty_eq, eq_univ_iff_forall]
    | 1 => rfl
    | (_ + 2) => i.elim
  continuousOn n i := match n with
    | 0 => continuousOn_const
    | 1 => (mapLT (lt_add_one (i : ℝ))).continuous.continuousOn
    | (_ + 2) => i.elim
  continuousOn_symm n i := match n with
    | 0 => continuousOn_const
    | 1 => (mapLT (lt_add_one (i : ℝ))).symm.continuous.continuousOn
    | (_ + 2) => i.elim
  pairwiseDisjoint' := by
    simp_rw [PairwiseDisjoint, Set.Pairwise, Function.onFun]
    exact fun ⟨n, j⟩ _ ⟨m, i⟩ _ ne ↦  match n with
      | 0 => match m with
        | 0 => by simp_all
        | 1 => by
          simp only [PartialEquiv.single_apply, Function.const_apply, nonempty_ball, zero_lt_one,
            Nonempty.image_const, mapLTPartial_image, mapLT_image_ball, disjoint_iff_inter_eq_empty,
            singleton_inter_eq_empty, mem_Ioo, Int.cast_lt, not_and, not_lt]
          norm_cast
          exact fun h ↦ h
        | (_ + 2) => i.elim
      | 1 => match m with
        | 0 => by
          simp only [mapLTPartial_image, mapLT_image_ball, PartialEquiv.single_apply,
            Function.const_apply, nonempty_ball, zero_lt_one, Nonempty.image_const,
            disjoint_iff_inter_eq_empty, inter_singleton_eq_empty, mem_Ioo, Int.cast_lt, not_and,
            not_lt]
          norm_cast
          exact fun h ↦ h
        | 1 => by
          simp only [mapLTPartial_image, mapLT_image_ball, disjoint_iff_inter_eq_empty ,
            Ioo_inter_Ioo, Ioo_eq_empty_iff, not_lt]
          norm_cast
          simp_all only [mem_univ, ne_eq, Sigma.mk.inj_iff, heq_eq_eq, true_and, Nat.cast_one,
            le_sup_iff, inf_le_iff, add_le_iff_nonpos_right, or_comm, Int.reduceLE, false_or]
          exact Int.lt_or_gt_of_ne ne
        | (_ +  2) => i.elim
      | (_ + 2) => j.elim
  mapsTo' n i := match n with
    | 0 => by simp [Matrix.zero_empty, sphere_eq_empty_of_subsingleton]
    | 1 => by
      use fun n ↦  match n with
        | 0 => {i, i + 1}
        | (_ + 1) => ∅
      simp only [Nat.lt_one_iff, iUnion_iUnion_eq_left, Finset.mem_insert, Finset.mem_singleton,
        PartialEquiv.single_apply, Function.const_apply, Matrix.zero_empty, nonempty_closedBall,
        zero_le_one, Nonempty.image_const, iUnion_iUnion_eq_or_left, Int.cast_add, Int.cast_one,
        union_singleton, mapsTo_iff_image_subset, mapLTPartial_image, mapLT_image_sphere, pair_comm]
      exact Subset.rfl
    | (_ + 2) => i.elim
  closed' := by
    intro A _ hA
    apply SequentialSpace.isClosed_of_seq
    intro s a hs hsa
    have : a ∈ Ioo (⌊a⌋ - 1 : ℝ) (⌈a⌉ + 1) := by
      constructor
      · refine lt_of_lt_of_le ?_ (Int.floor_le a)
        norm_num
      · apply lt_of_le_of_lt (Int.le_ceil a)
        exact lt_add_one _
    obtain ⟨N, hN⟩ := tendsto_atTop_nhds.1 hsa (Ioo (⌊a⌋ - 1 : ℝ) (⌈a⌉ + 1)) this isOpen_Ioo
    let t n := s (n + N)
    have hta : Filter.Tendsto t Filter.atTop (nhds a) :=
      (Filter.tendsto_add_atTop_iff_nat N).mpr hsa
    have ht : ∀ (n : ℕ), t n ∈ A := by
      intro n
      exact hs (n + N)
    have htA : ∀ n, t n ∈ A ∩ Icc (⌊a⌋ - 1 : ℝ) (⌈a⌉ + 1) := by
      intro n
      refine ⟨ht n, ?_⟩
      apply Ioo_subset_Icc_self
      apply hN
      exact N.le_add_left n
    have hA : IsClosed (A ∩ Icc (⌊a⌋ - 1 : ℝ) (⌈a⌉ + 1)) := by
      rw [← Icc_union_Icc_eq_Icc (b := (⌊a⌋ : ℝ)) (by linarith)
        (by norm_cast; exact (Int.floor_le_ceil a).trans (by norm_num)),
        ← Icc_union_Icc_eq_Icc (a := (⌊a⌋ : ℝ)) (b := (⌈a⌉ : ℝ))
        (by norm_cast; exact Int.floor_le_ceil a) (by norm_num),
        inter_union_distrib_left, inter_union_distrib_left]
      refine IsClosed.union ?_ (IsClosed.union ?_ ?_)
      · convert hA 1 (⌊a⌋ - 1)
        simp only [Int.cast_sub, Int.cast_one, sub_add_cancel, mapLTPartial_image,
          mapLT_image_closedBall]
      · by_cases h : ∃ (z : ℤ), z = a
        · obtain ⟨z, hz⟩ := h
          subst a
          rw [Int.ceil_intCast, Int.floor_intCast, Icc_self]
          exact isClosed_inter_singleton
        convert hA 1 ⌊a⌋
        simp only [(Int.ceil_eq_floor_add_one_iff_notMem a).2 h, mapLTPartial_image,
          mapLT_image_closedBall]
        norm_cast
      · convert hA 1 ⌈a⌉
        simp [mapLTPartial_image, mapLT_image_closedBall]
    rw [← isSeqClosed_iff_isClosed] at hA
    exact (hA htA hta).1
  union' := by
    apply subset_antisymm (subset_univ _)
    intro x _
    simp only [mem_iUnion]
    use 1, ⌊x⌋
    simp only [mapLTPartial_image, mapLT_image_closedBall, mem_Icc]
    exact ⟨Int.floor_le x, (Int.le_ceil x).trans (by norm_cast; exact Int.ceil_le_floor_add_one x)⟩

/-- The CW-structure on the reals is finite dimensional. -/
instance finiteDimensional_instReal : FiniteDimensional (univ : Set ℝ) where
  eventually_isEmpty_cell := by
    rw [Filter.eventually_atTop]
    use 2
    intro n hn
    simp only [cell_def, instReal_cell]
    split
    · contradiction
    · contradiction
    · infer_instance

end Topology.CWComplex
