module

public import C2Riemannian.DiskWeakRepresentative
public import C2Riemannian.ClassicalToWeakJet
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Affine normalization of a classical representative of a planar weak jet -/

set_option autoImplicit false

open MeasureTheory TopologicalSpace Set Filter
open scoped NNReal

namespace C2Riemannian.WeakJet2

variable {m : ℕ} {U : Opens Plane}

/-- The affine normalization of a classical representative is a weak jet
with the original second derivative field. -/
public theorem exists_normalized_weakJet (w : WeakJet2 m U) (a : Plane)
    {W : Plane → Target m} (hW : ContDiffOn ℝ 1 W (U : Set Plane))
    (hRep : W =ᵐ[volume.restrict (U : Set Plane)] w.value)
    (K : ℝ≥0)
    (hHS : ∀ x ∈ (U : Set Plane), ∀ y ∈ (U : Set Plane),
      gradHS (fderiv ℝ W x - fderiv ℝ W y) ≤ (K : ℝ) * dist x y) :
    ∃ v : WeakJet2 m U, v.value = normalize_height W a ∧
      v.gradient = fderiv ℝ (normalize_height W a) ∧
      v.second = w.second ∧ v.hessian = w.hessian ∧ ContDiffOn ℝ 1 v.value (U : Set Plane) := by
  have hd (x : Plane) (hx : x ∈ (U : Set Plane)) : DifferentiableAt ℝ W x :=
    (hW.differentiableOn_one x hx).differentiableAt (U.isOpen.mem_nhds hx)
  have hPLip : LipschitzOnWith K (fderiv ℝ W) (U : Set Plane) :=
    LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
      rw [dist_eq_norm]
      exact (opNorm_le_gradHS _).trans (hHS x hx y hy)
  let j := weakJet2_of_contDiffOn_locallyLipschitz hW (fun {_} _ => ⟨K, U, self_mem_nhdsWithin, hPLip⟩)
  have hJ : j.second =ᵐ[volume.restrict (U : Set Plane)] w.second :=
    (j.derivatives_ae_eq w hRep).2
  have hAffine : ContDiff ℝ 1 (fun x => fderiv ℝ W a (x - a)) :=
    (fderiv ℝ W a).contDiff.comp (contDiff_id.sub contDiff_const)
  have hN : ContDiffOn ℝ 1 (normalize_height W a) (U : Set Plane) :=
    (hW.sub contDiffOn_const).sub hAffine.contDiffOn
  have hNLip : LipschitzOnWith K (fderiv ℝ (normalize_height W a)) (U : Set Plane) :=
    LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
      rw [dist_eq_norm, fderiv_normalize_height (hd x hx), fderiv_normalize_height (hd y hy),
        sub_sub_sub_cancel_right]
      exact (opNorm_le_gradHS _).trans (hHS x hx y hy)
  let jN := weakJet2_of_contDiffOn_locallyLipschitz hN (fun {_} _ => ⟨K, U, self_mem_nhdsWithin, hNLip⟩)
  have hSecond : jN.second =ᵐ[volume.restrict (U : Set Plane)] w.second := by
    filter_upwards [hJ, ae_restrict_mem U.isOpen.measurableSet] with x hj hx
    exact (second_fderiv_normalize_height U.isOpen hd a hx).trans hj
  let v : WeakJet2 m U :=
    { value := jN.value
      gradient := jN.gradient
      second := w.second
      weak_value := jN.weak_value
      weak_gradient := jN.weak_gradient.congr_ae_deriv hSecond }
  exact ⟨v, rfl, rfl, rfl, rfl, hN⟩

/-- On a disk, the normalized weak jet preserves the Hessian readout and
satisfies the pointwise first-jet bounds of paper (8). -/
public theorem exists_normalized_disk_weakJet (a : Plane) (r : ℝ) (hr : 0 < r)
    (w : WeakJet2 m (⟨Metric.ball a r, Metric.isOpen_ball⟩ : Opens Plane))
    {W : Plane → Target m} {P : Plane → Plane →L[ℝ] Target m}
    (hW : ContDiffOn ℝ 1 W (Metric.ball a r))
    (hDeriv : ∀ x ∈ Metric.ball a r, HasFDerivAt W (P x) x)
    (hRep : W =ᵐ[volume.restrict (Metric.ball a r)] w.value)
    (K : ℝ≥0)
    (hHS : ∀ x ∈ Metric.ball a r, ∀ y ∈ Metric.ball a r,
      gradHS (P x - P y) ≤ (K : ℝ) * dist x y) :
    ∃ v : WeakJet2 m (⟨Metric.ball a r, Metric.isOpen_ball⟩ : Opens Plane),
      v.value = normalize_height W a ∧ v.gradient = fderiv ℝ v.value ∧
      v.second = w.second ∧ v.hessian = w.hessian ∧
      ContDiffOn ℝ 1 v.value (Metric.ball a r) ∧ v.value a = 0 ∧ v.gradient a = 0 ∧
      (∀ x ∈ Metric.ball a r, ‖v.value x‖ ≤ (K : ℝ) * dist x a ^ 2 / 2) ∧
      (∀ x ∈ Metric.ball a r, gradHS (v.gradient x) ≤ (K : ℝ) * dist x a) ∧
      (∀ x ∈ Metric.ball a r, ∀ y ∈ Metric.ball a r,
        gradHS (v.gradient x - v.gradient y) ≤ (K : ℝ) * dist x y) := by
  have ha := Metric.mem_ball_self (x := a) hr
  have hd (x : Plane) (hx : x ∈ Metric.ball a r) : DifferentiableAt ℝ W x :=
    (hDeriv x hx).differentiableAt
  have hHS' (x : Plane) (hx : x ∈ Metric.ball a r) (y : Plane) (hy : y ∈ Metric.ball a r) :
      gradHS (fderiv ℝ W x - fderiv ℝ W y) ≤ (K : ℝ) * dist x y := by
    rw [(hDeriv x hx).fderiv, (hDeriv y hy).fderiv]
    exact hHS x hx y hy
  have hCP : ContinuousOn (fderiv ℝ W) (Metric.ball a r) := by
    apply (LipschitzOnWith.of_dist_le_mul (K := K) (s := Metric.ball a r) ?_).continuousOn
    intro x hx y hy
    rw [dist_eq_norm]
    exact (opNorm_le_gradHS _).trans (hHS' x hx y hy)
  obtain ⟨v, hv, hgrad, hsecond, hhess, hvC1⟩ := w.exists_normalized_weakJet a hW hRep K hHS'
  obtain ⟨hgradLip, hgradBound⟩ := normalized_gradient_bounds ha hd hHS'
  refine ⟨v, hv, hgrad.trans (congrArg (fderiv ℝ) hv).symm, hsecond, hhess, hvC1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv, normalize_height_self]
  · rw [hgrad, fderiv_normalize_height_self (hd a ha)]
  · intro x hx
    rw [hv]
    exact normalized_bounds (convex_ball a r) ha hd hCP hHS' hx
  · simpa only [hgrad] using hgradBound
  · simpa only [hgrad] using hgradLip

end C2Riemannian.WeakJet2
