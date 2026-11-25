module

public import C2Riemannian.ClassicalToWeakJet
public import C2Riemannian.AffineNormalization
import Mathlib.Analysis.Calculus.FDeriv.Measurable

set_option autoImplicit false

open MeasureTheory Filter Set TopologicalSpace
open scoped ContDiff ENNReal NNReal

namespace C2Riemannian

variable {m : ℕ}

/-- A Hilbert–Schmidt difference bound implies the operator-norm Lipschitz estimate
with the same constant. -/
public theorem lipschitzOnWith_gradient_of_gradHS {P : Plane → Plane →L[ℝ] Target m}
    {s : Set Plane} {K : ℝ≥0}
    (hHS : ∀ x ∈ s, ∀ y ∈ s, gradHS (P x - P y) ≤ (K : ℝ) * dist x y) :
    LipschitzOnWith K P s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [dist_eq_norm]
  exact (opNorm_le_gradHS _).trans (hHS x hx y hy)

/-- The second Fréchet derivative of a classical potential inherits the gradient's
operator-norm Lipschitz bound on the open domain. -/
public theorem norm_fderiv_gradient_le {W : Plane → Target m} {U : Opens Plane}
    {K : ℝ≥0} (hLip : LipschitzOnWith K (fderiv ℝ W) (U : Set Plane))
    {x : Plane} (hx : x ∈ (U : Set Plane)) :
    ‖fderiv ℝ (fderiv ℝ W) x‖ ≤ K :=
  norm_fderiv_le_of_lipschitzOn ℝ (U.isOpen.mem_nhds hx) hLip

/-- The classical second derivative field of a potential with Lipschitz gradient is
essentially bounded with respect to the restricted planar measure. -/
public theorem classical_second_memLp_top {W : Plane → Target m} {U : Opens Plane}
    {K : ℝ≥0} (hLip : LipschitzOnWith K (fderiv ℝ W) (U : Set Plane)) :
    MemLp (fderiv ℝ (fderiv ℝ W)) ∞ (volume.restrict (U : Set Plane)) := by
  let B := Plane →L[ℝ] (Plane →L[ℝ] Target m)
  let : MeasurableSpace B := borel B
  let : BorelSpace B := ⟨rfl⟩
  apply memLp_top_of_bound (measurable_fderiv ℝ (fderiv ℝ W)).aestronglyMeasurable (K : ℝ)
  exact (ae_restrict_mem U.isOpen.measurableSet).mono fun _ hx => norm_fderiv_gradient_le hLip hx

/-- The three fields of a normalized classical jet on an open convex region of radius
at most `R` have essential bounds (KR^2/2), (KR), and (K), respectively. -/
public theorem classical_normalized_jet_bounds {W : Plane → Target m} {U : Opens Plane}
    (hConvex : Convex ℝ (U : Set Plane)) {a : Plane} (ha : a ∈ (U : Set Plane))
    (R K : ℝ≥0) (hRadius : ∀ x ∈ (U : Set Plane), dist x a ≤ R)
    (hW : ContDiffOn ℝ 1 W U) (hWa : W a = 0) (hPa : fderiv ℝ W a = 0)
    (hHS : ∀ x ∈ (U : Set Plane), ∀ y ∈ (U : Set Plane),
      gradHS (fderiv ℝ W x - fderiv ℝ W y) ≤ (K : ℝ) * dist x y) :
    MemLp W ∞ (volume.restrict (U : Set Plane)) ∧
    MemLp (fderiv ℝ W) ∞ (volume.restrict (U : Set Plane)) ∧
    MemLp (fderiv ℝ (fderiv ℝ W)) ∞ (volume.restrict (U : Set Plane)) ∧
    (∀ᵐ x ∂volume.restrict (U : Set Plane), ‖W x‖ ≤ (K : ℝ) * (R : ℝ) ^ 2 / 2) ∧
    (∀ᵐ x ∂volume.restrict (U : Set Plane), ‖fderiv ℝ W x‖ ≤ (K : ℝ) * R) ∧
    (∀ᵐ x ∂volume.restrict (U : Set Plane), ‖fderiv ℝ (fderiv ℝ W) x‖ ≤ (K : ℝ)) := by
  have hd (x : Plane) (hx : x ∈ (U : Set Plane)) : DifferentiableAt ℝ W x :=
    (hW.differentiableOn (by decide) x hx).differentiableAt (U.isOpen.mem_nhds hx)
  have hLip := lipschitzOnWith_gradient_of_gradHS hHS
  have hPcont := hLip.continuousOn
  have hmem : ∀ᵐ x ∂volume.restrict (U : Set Plane), x ∈ (U : Set Plane) :=
    ae_restrict_mem U.isOpen.measurableSet
  have hv : ∀ᵐ x ∂volume.restrict (U : Set Plane), ‖W x‖ ≤ (K : ℝ) * (R : ℝ) ^ 2 / 2 := by
    filter_upwards [hmem] with x hx
    have hb := normalized_bounds hConvex ha hd hPcont hHS hx
    have hxW : normalize_height W a x = W x := by simp [normalize_height, hWa, hPa]
    rw [hxW] at hb
    exact hb.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ dist_nonneg (hRadius x hx) 2) K.coe_nonneg)
      zero_le_two)
  have hp : ∀ᵐ x ∂volume.restrict (U : Set Plane), ‖fderiv ℝ W x‖ ≤ (K : ℝ) * R := by
    filter_upwards [hmem] with x hx
    have hh := hHS x hx a ha
    rw [hPa, sub_zero] at hh
    exact (opNorm_le_gradHS _).trans (hh.trans (mul_le_mul_of_nonneg_left
      (hRadius x hx) K.coe_nonneg))
  have hb : ∀ᵐ x ∂volume.restrict (U : Set Plane), ‖fderiv ℝ (fderiv ℝ W) x‖ ≤ (K : ℝ) :=
    hmem.mono fun _ hx => norm_fderiv_gradient_le hLip hx
  exact ⟨memLp_top_of_bound (hW.continuousOn.aestronglyMeasurable U.isOpen.measurableSet) _ hv,
    memLp_top_of_bound (hPcont.aestronglyMeasurable U.isOpen.measurableSet) _ hp,
    classical_second_memLp_top hLip, hv, hp, hb⟩

end C2Riemannian

