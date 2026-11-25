module

public import C2Riemannian.MetricSource
public import C2Riemannian.MetricRank
import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false

open MeasureTheory Set TopologicalSpace

namespace C2Riemannian.WeakJet2

variable {m : ℕ} {U : Opens Plane}

/-- The almost-everywhere diagonal Gram relation for a planar coordinate chart. -/
@[expose] public def IsometryInChart (w : WeakJet2 m U) (v : Plane → ℝ) : Prop :=
  ∀ᵐ x ∂volume.restrict (U : Set Plane),
    inner ℝ (w.gradient x ex) (w.gradient x ex) = 1 + v x ∧
    inner ℝ (w.gradient x ey) (w.gradient x ey) = 1 ∧
    inner ℝ (w.gradient x ex) (w.gradient x ey) = 0

/-- The continuous representative of the gradient satisfies the metric pointwise. -/
public theorem gram_eq_of_continuous_representative
    {w : WeakJet2 m U} {v : Plane → ℝ} (hIso : w.IsometryInChart v)
    {P : Plane → Plane →L[ℝ] Target m} (hP : ContinuousOn P (U : Set Plane))
    (hRep : P =ᵐ[volume.restrict (U : Set Plane)] w.gradient)
    (hv : ContinuousOn v (U : Set Plane)) :
    ∀ x ∈ (U : Set Plane),
      inner ℝ (P x ex) (P x ex) = 1 + v x ∧
      inner ℝ (P x ey) (P x ey) = 1 ∧
      inner ℝ (P x ex) (P x ey) = 0 := by
  have hEx : ContinuousOn (fun x => P x ex) (U : Set Plane) := hP.clm_apply continuousOn_const
  have hEy : ContinuousOn (fun x => P x ey) (U : Set Plane) := hP.clm_apply continuousOn_const
  have hAe : ∀ᵐ x ∂volume.restrict (U : Set Plane),
      inner ℝ (P x ex) (P x ex) = 1 + v x ∧
      inner ℝ (P x ey) (P x ey) = 1 ∧ inner ℝ (P x ex) (P x ey) = 0 := by
    filter_upwards [hIso, hRep] with x hx h
    simpa only [h] using hx
  have hxx := Measure.eqOn_open_of_ae_eq (hAe.mono fun _ hx => hx.1) U.isOpen
    (hEx.inner hEx) (continuousOn_const.add hv)
  have hyy := Measure.eqOn_open_of_ae_eq (hAe.mono fun _ hx => hx.2.1) U.isOpen
    (hEy.inner hEy) continuousOn_const
  have hxy := Measure.eqOn_open_of_ae_eq (hAe.mono fun _ hx => hx.2.2) U.isOpen
    (hEx.inner hEy) continuousOn_const
  exact fun x hx => ⟨hxx hx, hyy hx, hxy hx⟩

private theorem norm_sq_of_gram (L : Plane →L[ℝ] Target m) {g : ℝ}
    (hxx : inner ℝ (L ex) (L ex) = g) (hyy : inner ℝ (L ey) (L ey) = 1)
    (hxy : inner ℝ (L ex) (L ey) = 0) (z : Plane) :
    ‖L z‖ ^ 2 = g * (z 0) ^ 2 + (z 1) ^ 2 := by
  have hz : z 0 • ex + z 1 • ey = z := by
    simpa only [Fin.sum_univ_two, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
      using (EuclideanSpace.basisFun (Fin 2) ℝ).sum_repr z
  have hx : ‖L ex‖ ^ 2 = g := (real_inner_self_eq_norm_sq _).symm.trans hxx
  have hy : ‖L ey‖ ^ 2 = 1 := (real_inner_self_eq_norm_sq _).symm.trans hyy
  have hOrth : inner ℝ (z 0 • L ex) (z 1 • L ey) = 0 := by
    simp [real_inner_smul_left, real_inner_smul_right, hxy]
  have hL : L z = z 0 • L ex + z 1 • L ey := by
    simpa only [map_add, map_smul] using congrArg L hz.symm
  calc
    ‖L z‖ ^ 2 = ‖z 0 • L ex + z 1 • L ey‖ ^ 2 := by
      exact congrArg (fun w => ‖w‖ ^ 2) hL
    _ = ‖z 0 • L ex‖ ^ 2 + ‖z 1 • L ey‖ ^ 2 :=
      by simpa only [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real hOrth
    _ = _ := by simp [norm_smul, mul_pow, hx, hy, Real.norm_eq_abs, sq_abs, mul_comm]

/-- Positivity of the metric gives rank two at each point of the chart. -/
public theorem injective_of_isometry_representative
    {w : WeakJet2 m U} {v : Plane → ℝ} (hIso : w.IsometryInChart v)
    {P : Plane → Plane →L[ℝ] Target m} (hP : ContinuousOn P (U : Set Plane))
    (hRep : P =ᵐ[volume.restrict (U : Set Plane)] w.gradient)
    (hv : ContinuousOn v (U : Set Plane)) (hPos : ∀ x ∈ (U : Set Plane), 0 < 1 + v x) :
    ∀ x ∈ (U : Set Plane), Function.Injective (P x) := by
  intro x hx
  obtain ⟨hxx, hyy, hxy⟩ := gram_eq_of_continuous_representative hIso hP hRep hv x hx
  exact injective_of_positive_diagonal_gram (P x) (hPos x hx) (norm_sq_of_gram (P x) hxx hyy hxy)

end C2Riemannian.WeakJet2
