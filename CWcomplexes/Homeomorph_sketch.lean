/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Oliver Nash
-/
import Mathlib.Topology.PartialHomeomorph
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Data.Real.Sqrt

/-!
# (Local) homeomorphism between a normed space and a ball

In this file we show that a real (semi)normed vector space is homeomorphic to the unit ball.

We formalize it in two ways:

- as a `Homeomorph`, see `Homeomorph.unitBall`;
- as a `PartialHomeomorph` with `source = Set.univ` and `target = Metric.ball (0 : E) 1`.

While the former approach is more natural, the latter approach provides us
with a globally defined inverse function which makes it easier to say
that this homeomorphism is in fact a diffeomorphism.

We also show that the unit ball `Metric.ball (0 : E) 1` is homeomorphic
to a ball of positive radius in an affine space over `E`, see `PartialHomeomorph.unitBallBall`.

## Tags

homeomorphism, ball
-/

open Set Metric Pointwise
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

/-- Local homeomorphism between a real (semi)normed space and the unit ball.
See also `Homeomorph.unitBall`. -/
@[simps -isSimp]
def PartialHomeomorph.univUnitBall : PartialHomeomorph E E where
  toFun x := (√(1 + ‖x‖ ^ 2))⁻¹ • x
  invFun y := (√(1 - ‖(y : E)‖ ^ 2))⁻¹ • (y : E)
  source := univ
  target := ball 0 1
  map_source' x _ := sorry
  map_target' _ _ := sorry
  left_inv' x _ := sorry
  right_inv' y hy := sorry
  open_source := sorry
  open_target := sorry
  continuousOn_toFun := sorry
  continuousOn_invFun := sorry

@[simp]
theorem PartialHomeomorph.univUnitBall_apply_zero : univUnitBall (0 : E) = 0 := sorry

@[simp]
theorem PartialHomeomorph.univUnitBall_symm_apply_zero : univUnitBall.symm (0 : E) = 0 := sorry

/-- A (semi) normed real vector space is homeomorphic to the unit ball in the same space.
This homeomorphism sends `x : E` to `(1 + ‖x‖²)^(- ½) • x`.

In many cases the actual implementation is not important, so we don't mark the projection lemmas
`Homeomorph.unitBall_apply_coe` and `Homeomorph.unitBall_symm_apply` as `@[simp]`.

See also `Homeomorph.contDiff_unitBall` and `PartialHomeomorph.contDiffOn_unitBall_symm`
for smoothness properties that hold when `E` is an inner-product space. -/
@[simps! -isSimp]
def Homeomorph.unitBall : E ≃ₜ ball (0 : E) 1 :=
  (Homeomorph.Set.univ _).symm.trans PartialHomeomorph.univUnitBall.toHomeomorphSourceTarget

@[simp]
theorem Homeomorph.coe_unitBall_apply_zero :
    (Homeomorph.unitBall (0 : E) : E) = 0 := sorry

variable {P : Type*} [PseudoMetricSpace P] [NormedAddTorsor E P]

namespace PartialHomeomorph

/-- Affine homeomorphism `(r • · +ᵥ c)` between a normed space and an add torsor over this space,
interpreted as a `PartialHomeomorph` between `Metric.ball 0 1` and `Metric.ball c r`. -/
@[simps!]
def unitBallBall (c : P) (r : ℝ) (hr : 0 < r) : PartialHomeomorph E P :=
  ((Homeomorph.smulOfNeZero r hr.ne').trans
      (IsometryEquiv.vaddConst c).toHomeomorph).toPartialHomeomorphOfImageEq
      (ball 0 1) sorry (ball c r) sorry

/-- If `r > 0`, then `PartialHomeomorph.univBall c r` is a smooth partial homeomorphism
with `source = Set.univ` and `target = Metric.ball c r`.
Otherwise, it is the translation by `c`.
Thus in all cases, it sends `0` to `c`, see `PartialHomeomorph.univBall_apply_zero`. -/
def univBall (c : P) (r : ℝ) : PartialHomeomorph E P :=
  if h : 0 < r then univUnitBall.trans' (unitBallBall c r h) rfl
  else (IsometryEquiv.vaddConst c).toHomeomorph.toPartialHomeomorph

@[simp]
theorem univBall_source (c : P) (r : ℝ) : (univBall c r).source = univ := sorry

theorem univBall_target (c : P) {r : ℝ} (hr : 0 < r) : (univBall c r).target = ball c r := sorry

theorem ball_subset_univBall_target (c : P) (r : ℝ) : ball c r ⊆ (univBall c r).target := sorry

@[simp]
theorem univBall_apply_zero (c : P) (r : ℝ) : univBall c r 0 = c := sorry

@[simp]
theorem univBall_symm_apply_center (c : P) (r : ℝ) : (univBall c r).symm c = 0 := sorry

@[continuity]
theorem continuous_univBall (c : P) (r : ℝ) : Continuous (univBall c r) := sorry

theorem continuousOn_univBall_symm (c : P) (r : ℝ) : ContinuousOn (univBall c r).symm (ball c r) := sorry

end PartialHomeomorph
