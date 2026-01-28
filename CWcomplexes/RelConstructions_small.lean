import Mathlib.Topology.CWComplex.Classical.Finite
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Data.ENat.Basic

noncomputable section
open Metric Set
namespace Topology
variable {X : Type*} [t : TopologicalSpace X] {C D : Set X}
section

/-- Every finite set is a CW complex. -/
def CWComplex.ofFiniteSet {C : Set X} (h : C.Finite) : CWComplex C := mkFinite C
  (cell := fun n ↦ match n with
    | 0 => C
    | (_ + 1) => PEmpty)
  (map := fun n i ↦ match n with
    | 0 => PartialEquiv.single ![] i
    | (_ + 1) => i.elim)
  (eventually_isEmpty_cell := sorry)
  (finite_cell := fun n ↦ match n with
    | 0 => h
    | (_ + 1) => inferInstance)
  (source_eq := fun n i ↦ match n with
    | 0 => sorry
    | (_ + 1) => i.elim)
  (continuousOn := fun n i ↦ match n with
    | 0 => continuousOn_const
    | (m + 1) => i.elim)
  (continuousOn_symm := fun n i ↦ match n with
    | 0 => continuousOn_const
    | (_ + 1) => i.elim)
  (pairwiseDisjoint' := sorry)
  (mapsTo_iff_image_subset := fun n i ↦ match n with
    | 0 => sorry
    | (_ + 1) => i.elim)
  (union' := sorry)

lemma CWComplex.ofFiniteSet_cell_zero {C : Set X} (h : C.Finite) :
    letI := ofFiniteSet h
    cell C 0 =  C :=
  sorry

lemma CWComplex.ofFiniteSet_cell_of_gt_zero {C : Set X} (h : C.Finite) {n : ℕ} :
    letI := ofFiniteSet h
    cell C (n + 1) =  PEmpty :=
  sorry

lemma CWComplex.ofFiniteSet_map {C : Set X} (h : C.Finite)
    {i : C} :
    letI := ofFiniteSet h
    map (C := C) 0 i =
      PartialEquiv.single (β := X) ![] i  :=
  sorry

/-- The CW-complex on a finite set is finite. -/
lemma CWComplex.finite_ofFiniteSet {C : Set X} (h : C.Finite) :
    letI := ofFiniteSet h
    Finite C :=
  sorry

@[simps -isSimp]
def RelCWComplex.ofEq {X : Type*} [TopologicalSpace X] (C D : Set X)
    {E F : Set X} [RelCWComplex C D] (hCE : C = E) (hDF : D = F) : RelCWComplex E F where
  cell := cell C
  map := map
  source_eq := source_eq
  continuousOn := continuousOn
  continuousOn_symm := continuousOn_symm
  pairwiseDisjoint' := pairwiseDisjoint'
  disjointBase' := hDF ▸ disjointBase'
  mapsTo := hDF ▸ mapsTo
  closed' := sorry
  isClosedBase := sorry
  union' := sorry

@[simps! -isSimp]
def CWComplex.ofEq {X : Type*} [TopologicalSpace X] (C : Set X)
    {E : Set X} [CWComplex C] (hCE : C = E) : CWComplex E :=
  (RelCWComplex.ofEq C ∅ hCE rfl).toCWComplex

lemma RelCWComplex.finiteDimensional_ofEq {X : Type*} [TopologicalSpace X] (C D : Set X)
    {E F : Set X} [RelCWComplex C D] [FiniteDimensional C] (hCE : C = E) (hDF : D = F) :
    letI _ := ofEq C D hCE hDF
    FiniteDimensional E :=
  sorry

lemma CWComplex.finiteDimensional_ofEq {X : Type*} [TopologicalSpace X] (C : Set X)
    {E : Set X} [CWComplex C] [FiniteDimensional C] (hCE : C = E) :
    letI _ := ofEq C hCE
    FiniteDimensional E :=
  sorry

lemma RelCWComplex.finiteType_ofEq {X : Type*} [TopologicalSpace X] (C D : Set X)
    {E F : Set X} [RelCWComplex C D] [FiniteType C] (hCE : C = E) (hDF : D = F) :
    letI _ := ofEq C D hCE hDF
    FiniteType E :=
  sorry

lemma CWComplex.finiteType_ofEq {X : Type*} [TopologicalSpace X] (C : Set X)
    {E : Set X} [CWComplex C] [FiniteType C] (hCE : C = E) :
    letI _ := ofEq C hCE
    FiniteType E :=
  sorry

lemma RelCWComplex.finite_ofEq {X : Type*} [TopologicalSpace X] (C D : Set X)
    {E F : Set X} [RelCWComplex C D] [Finite C] (hCE : C = E) (hDF : D = F) :
    letI _ := ofEq C D hCE hDF
    Finite E :=
  sorry

lemma CWComplex.finite_ofEq {X : Type*} [TopologicalSpace X] (C : Set X)
    {E : Set X} [CWComplex C] [Finite C] (hCE : C = E) :
    letI _ := ofEq C hCE
    Finite E :=
  sorry

set_option linter.unusedVariables false in
def RelCWComplex.ofPartialEquivCell.{u} {X : Type*} {Y : Type u} [TopologicalSpace X]
    (C : Set X) {D : Set X} [RelCWComplex C D]
    (f : PartialEquiv X Y) (hfC1 : f.source = C) (n : ℕ) : Type u :=
  {x : Y // ∃ i, (f : X → Y) (map (C := C) n i 0) = x}

def RelCWComplex.ofPartialEquivCellEquiv {X Y : Type*} [TopologicalSpace X]
    [T2Space X] [TopologicalSpace Y] (C : Set X) {D : Set X} [RelCWComplex C D]
    (f : PartialEquiv X Y) (hfC1 : f.source = C) (n : ℕ) :
    cell C n ≃ ofPartialEquivCell C f hfC1 n :=
  sorry

abbrev RelCWComplex.ofPartialEquivCell.preimage {X Y : Type*} [TopologicalSpace X]
    [T2Space X] [TopologicalSpace Y] (C : Set X) {D : Set X} [RelCWComplex C D]
    {f : PartialEquiv X Y} {hfC1 : f.source = C} {n : ℕ} (i : ofPartialEquivCell C f hfC1 n) :=
  (ofPartialEquivCellEquiv C f hfC1 n).symm i

@[simp]
lemma RelCWComplex.ofPartialEquiv.preimage_ofPartialEquivCellEquiv {X Y : Type*}
    [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] (C : Set X) {D : Set X} [RelCWComplex C D]
    {f : PartialEquiv X Y} {hfC1 : f.source = C} {n : ℕ} (i : cell C n) :
    (ofPartialEquivCellEquiv C f hfC1 n i).preimage = i :=
  sorry

@[simp]
lemma RelCWComplex.ofPartialEquiv.ofPartialEquivCellEquiv_preimage {X Y : Type*}
    [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] (C : Set X) {D : Set X} [RelCWComplex C D]
    {f : PartialEquiv X Y} {hfC1 : f.source = C} {n : ℕ} (i : ofPartialEquivCell C f hfC1 n) :
    (ofPartialEquivCellEquiv C f hfC1 n i.preimage) = i :=
  sorry

lemma RelCWComplex.ofPartialEquiv.iUnion₂_eq {X Y Z : Type*}
    [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] {C : Set X} {D : Set X} [RelCWComplex C D]
    {f : PartialEquiv X Y} {hfC1 : f.source = C}
    (g : (n : ℕ) → ofPartialEquivCell C f hfC1 n → Set Z) :
    ⋃ n, ⋃ (i : ofPartialEquivCell C f hfC1 n), g n i =
      ⋃ n, ⋃ (i : cell C n), g n (ofPartialEquivCellEquiv C f hfC1 n i) :=
  sorry

@[simps -isSimp]
def RelCWComplex.ofPartialEquiv {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] (C : Set X) {D : Set X} (E : Set Y) {F : Set Y} [RelCWComplex C D]
    (hE : IsClosed E) (f : PartialEquiv X Y) (hfC1 : f.source = C) (hfE1 : f.target = E)
    (hDF : f '' D = F) (hfC2 : ContinuousOn f C) (hfE2 : ContinuousOn f.symm E) :
    RelCWComplex E F where
  cell := ofPartialEquivCell C f hfC1
  map n i := (map n i.preimage).trans' (f.restr (map n i.preimage).target) sorry
  source_eq n i := sorry
  continuousOn n i := sorry
  continuousOn_symm n i := sorry
  pairwiseDisjoint' := sorry
  disjointBase' n i := sorry
  mapsTo n i := sorry
  closed' A hA := sorry
  isClosedBase := sorry
  union' := sorry

/-- `RelCWComplex.ofPartialEquiv` preserves finite dimensionality. -/
lemma RelCWComplex.finiteDimensional_ofPartialEquiv.{u} {X Y : Type u} [TopologicalSpace X]
    [T2Space X] [TopologicalSpace Y] (C : Set X) {D : Set X} (E : Set Y) {F : Set Y}
    [RelCWComplex C D] [FiniteDimensional C] (hE : IsClosed E)
    (f : PartialEquiv X Y) (hfC1 : f.source = C) (hfE1 : f.target = E) (hDF : f '' D = F)
    (hfC2 : ContinuousOn f C) (hfE2 : ContinuousOn f.symm E) :
    letI := ofPartialEquiv C E hE f hfC1 hfE1 hDF hfC2 hfE2
    FiniteDimensional E :=
  sorry

/-- `RelCWComplex.ofPartialEquiv` preserves finite type. -/
lemma RelCWComplex.finiteType_ofPartialEquiv.{u} {X Y : Type u} [TopologicalSpace X]
    [T2Space X] [TopologicalSpace Y] (C : Set X) {D : Set X} (E : Set Y) {F : Set Y}
    [RelCWComplex C D] [FiniteType C] (hE : IsClosed E)
    (f : PartialEquiv X Y) (hfC1 : f.source = C) (hfE1 : f.target = E) (hDF : f '' D = F)
    (hfC2 : ContinuousOn f C) (hfE2 : ContinuousOn f.symm E) :
    letI := ofPartialEquiv C E hE f hfC1 hfE1 hDF hfC2 hfE2
    FiniteType E :=
  sorry

/-- `RelCWComplex.ofPartialEquiv` preserves finiteness. -/
lemma RelCWComplex.finite_ofPartialEquiv.{u} {X Y : Type u} [TopologicalSpace X]
    [T2Space X] [TopologicalSpace Y] (C : Set X) {D : Set X} (E : Set Y) {F : Set Y}
    [RelCWComplex C D] [Finite C] (hE : IsClosed E)
    (f : PartialEquiv X Y) (hfC1 : f.source = C) (hfE1 : f.target = E) (hDF : f '' D = F)
    (hfC2 : ContinuousOn f C) (hfE2 : ContinuousOn f.symm E) :
    letI := ofPartialEquiv C E hE f hfC1 hfE1 hDF hfC2 hfE2
    Finite E :=
  sorry

/-- A version of `RelCWComplex.ofPartialEquiv` for absolute CW-complexes. -/
@[simps! -isSimp]
def CWComplex.ofPartialEquiv.{u} {X Y : Type u} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] (C : Set X) (E : Set Y) [CWComplex C]
    (hE : IsClosed E) (f : PartialEquiv X Y) (hfC1 : f.source = C) (hfE1 : f.target = E)
    (hfC2 : ContinuousOn f C) (hfE2 : ContinuousOn f.symm E)  :
    CWComplex E :=
  (RelCWComplex.ofPartialEquiv C E hE f hfC1 hfE1 (image_empty f)  hfC2 hfE2).toCWComplex

/-- `CWComplex.ofPartialEquiv` preserves finite dimensionality. -/
lemma CWComplex.finiteDimensional_ofPartialEquiv .{u} {X Y : Type u} [TopologicalSpace X]
    [T2Space X] [TopologicalSpace Y] (C : Set X) (E : Set Y) [CWComplex C] [FiniteDimensional C]
    (hE : IsClosed E) (f : PartialEquiv X Y) (hfC1 : f.source = C)
    (hfE1 : f.target = E) (hfC2 : ContinuousOn f C) (hfE2 : ContinuousOn f.symm E)  :
    letI := ofPartialEquiv C E hE f hfC1 hfE1 hfC2 hfE2
    FiniteDimensional E :=
  sorry

/-- `CWComplex.ofPartialEquiv` preserves finite type. -/
lemma CWComplex.finiteType_ofPartialEquiv .{u} {X Y : Type u} [TopologicalSpace X]
    [T2Space X] [TopologicalSpace Y] (C : Set X) (E : Set Y) [CWComplex C] [FiniteType C]
    (hE : IsClosed E) (f : PartialEquiv X Y) (hfC1 : f.source = C)
    (hfE1 : f.target = E) (hfC2 : ContinuousOn f C) (hfE2 : ContinuousOn f.symm E)  :
    letI := ofPartialEquiv C E hE f hfC1 hfE1 hfC2 hfE2
    FiniteType E :=
  sorry

/-- `CWComplex.ofPartialEquiv` preserves finiteness. -/
lemma CWComplex.finite_ofPartialEquiv .{u} {X Y : Type u} [TopologicalSpace X]
    [T2Space X] [TopologicalSpace Y] (C : Set X) (E : Set Y) [CWComplex C] [Finite C]
    (hE : IsClosed E) (f : PartialEquiv X Y) (hfC1 : f.source = C)
    (hfE1 : f.target = E) (hfC2 : ContinuousOn f C) (hfE2 : ContinuousOn f.symm E)  :
    letI := ofPartialEquiv C E hE f hfC1 hfE1 hfC2 hfE2
    Finite E :=
  sorry

/-- The image of a CW-complex under a homeomorphisms is again a CW-complex. -/
@[simps! -isSimp]
def RelCWComplex.ofHomeomorph.{u} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X]
    (C : Set X) {D : Set X} (E : Set Y) {F : Set Y} [RelCWComplex C D] (f : X ≃ₜ Y)
    (hCE : f '' C = E) (hDF : f '' D = F) :
    RelCWComplex E F :=
  letI : f.toPartialEquiv.IsImage C E := sorry
  ofPartialEquiv C E (by sorry) this.restr
    (by simp) (by simp) (by simp [hDF]) f.continuous.continuousOn f.symm.continuous.continuousOn

/-- A version of `RelCWComplex.attachCell`. Assuming that the CW complex is of finite type lets us
  relax the condition `mapsTo`. -/
@[simps! -isSimp]
def RelCWComplex.attachCellFiniteType.{u} {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) {D : Set X} [RelCWComplex C D] [FiniteType C]
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = ball 0 1)
    (continuousOn' : ContinuousOn map' (closedBall 0 1))
    (continuousOn_symm' : ContinuousOn map'.symm map'.target)
    (disjoint' : ∀ m (i : cell C m), Disjoint (map' '' ball 0 1) (openCell m i))
    (disjointBase' : Disjoint (map' '' ball 0 1) D)
    (mapsTo : MapsTo map' (sphere 0 1) (D ∪ ⋃ (m < n) (j : cell C m), closedCell m j)) :
    RelCWComplex (map' '' closedBall 0 1 ∪ C) D := RelCWComplex.attachCell C map'
  (source_eq' := source_eq')
  (continuousOn' := continuousOn')
  (continuousOn_symm' := continuousOn_symm')
  (disjoint' := disjoint')
  (disjointBase' := disjointBase')
  (mapsTo := by
    have := FiniteType.finite_cell (C := C) (D := D)
    use fun m ↦ finite_univ.toFinset
    simpa)

lemma RelCWComplex.finite_attachCellFiniteType {X : Type*} [TopologicalSpace X]
    [T2Space X] (C : Set X) {D : Set X} [RelCWComplex C D] [Finite C]
    {n : ℕ} (map' : PartialEquiv (Fin n → ℝ) X) (source_eq' : map'.source = ball 0 1)
    (cont' : ContinuousOn map' (closedBall 0 1))
    (cont_symm' : ContinuousOn map'.symm map'.target)
    (disjoint' : ∀ m (i : cell C m), Disjoint (map' '' ball 0 1) (openCell m i))
    (disjointBase' : Disjoint (map' '' ball 0 1) D)
    (mapsTo : MapsTo map' (sphere 0 1) (D ∪ ⋃ (m < n) (j : cell C m), closedCell m j)) :
    letI _complex := attachCellFiniteType C map' source_eq' cont' cont_symm'
      disjoint' disjointBase' mapsTo
    Finite (map' '' closedBall 0 1 ∪ C) := sorry
