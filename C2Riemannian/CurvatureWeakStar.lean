module

public import C2Riemannian.MetricSource
public import C2Riemannian.WeakStarExtension
import C2Riemannian.WeakTestConvergence
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Topology Distributions ENNReal

namespace C2Riemannian.WeakJet2

variable {m : ℕ} {U : Opens Plane}

/-- Essential bounds used by the weak Gram identity and the curvature limit. -/
public structure CurvatureBounds (w : WeakJet2 m U) (P H K : ℝ) : Prop where
  value_mem : MemLp w.value ∞ (volume.restrict (U : Set Plane))
  gradient_mem : MemLp w.gradient ∞ (volume.restrict (U : Set Plane))
  second_mem : MemLp w.second ∞ (volume.restrict (U : Set Plane))
  gradient_bound : ∀ᵐ x ∂volume.restrict (U : Set Plane), ‖w.gradient x‖ ≤ P
  second_bound : ∀ᵐ x ∂volume.restrict (U : Set Plane), ‖w.second x‖ ≤ H
  frobenius_bound : ∀ᵐ x ∂volume.restrict (U : Set Plane), (w.hessian x).frobenius ≤ K

private theorem strongL2_gradient_column
    [IsFiniteMeasure (volume.restrict (U : Set Plane))]
    {W : ℕ → WeakJet2 m U} {w : WeakJet2 m U} {P H K : ℝ}
    (hW : ∀ n, CurvatureBounds (W n) P H K) (hw : CurvatureBounds w P H K)
    (hUniform : ∀ s : Set Plane, s ⊆ (U : Set Plane) → IsCompact s →
      TendstoUniformlyOn (fun n => (W n).gradient) w.gradient atTop s)
    (d : Plane) :
    StrongL2 atTop (volume.restrict (U : Set Plane))
      (fun n x => (W n).gradient x d) (fun x => w.gradient x d) := by
  let μ := volume.restrict (U : Set Plane)
  let E := ContinuousLinearMap.apply ℝ (Target m) d
  let A (n : ℕ) (x : Plane) := (W n).gradient x d
  let a (x : Plane) := w.gradient x d
  have hA (n : ℕ) : AEStronglyMeasurable (A n) μ :=
    E.continuous.comp_aestronglyMeasurable (hW n).gradient_mem.aestronglyMeasurable
  have ha : AEStronglyMeasurable a μ :=
    E.continuous.comp_aestronglyMeasurable hw.gradient_mem.aestronglyMeasurable
  have bA (n : ℕ) : ∀ᵐ x ∂μ, ‖A n x‖ ≤ P * ‖d‖ :=
    (hW n).gradient_bound.mono fun x hx => ((W n).gradient x).le_opNorm d |>.trans
      (mul_le_mul_of_nonneg_right hx (norm_nonneg d))
  have ba : ∀ᵐ x ∂μ, ‖a x‖ ≤ P * ‖d‖ :=
    hw.gradient_bound.mono fun x hx => (w.gradient x).le_opNorm d |>.trans
      (mul_le_mul_of_nonneg_right hx (norm_nonneg d))
  refine ⟨fun n => MemLp.of_bound (hA n) _ (bA n), MemLp.of_bound ha _ ba, ?_⟩
  have hTendsto : Tendsto (fun n => ∫ x, ‖A n x - a x‖ ^ (2 : ℕ) ∂μ) atTop
      (𝓝 (∫ _ : Plane, (0 : ℝ) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (P * ‖d‖ + P * ‖d‖) ^ (2 : ℕ))
    · intro n
      exact ((hA n).sub ha).norm.pow 2
    · exact integrable_const _
    · intro n
      filter_upwards [bA n, ba] with x hx hy
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _)
        ((norm_sub_le _ _).trans (add_le_add hx hy)) 2
    · filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with x hx
      have h := (hUniform {x} (singleton_subset_iff.mpr hx) isCompact_singleton).tendsto_at
        (mem_singleton x)
      have hPoint : Tendsto (fun n => A n x) atTop (𝓝 (a x)) :=
        E.continuous.continuousAt.tendsto.comp h
      simpa using ((hPoint.sub_const (a x)).norm.pow 2)
  simpa only [Real.rpow_two, integral_zero] using hTendsto

private theorem integrable_curvature
    [IsFiniteMeasure (volume.restrict (U : Set Plane))]
    {w : WeakJet2 m U} {P H K : ℝ} (hw : CurvatureBounds w P H K) :
    Integrable (fun x => (w.hessian x).q) (volume.restrict (U : Set Plane)) := by
  have hc := w.second_eval_memLp_of_bound hw.second_mem.aestronglyMeasurable hw.second_bound
  exact (integrable_weak_inner (hc ex ex) (hc ey ey)).sub
    (integrable_weak_inner (hc ex ey) (hc ex ey))

/-- On a finite-measure planar open set, compact-uniform convergence of the
weak gradient fields gives weak-star convergence of the Hessian determinant
sum. The limiting weak second jet is given, with the same Frobenius bound. -/
public theorem curvature_weakStar_of_gradient_locally_uniform
    [IsFiniteMeasure (volume.restrict (U : Set Plane))]
    {W : ℕ → WeakJet2 m U} {w : WeakJet2 m U} {P H K : ℝ}
    (hP : 0 ≤ P) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hW : ∀ n, CurvatureBounds (W n) P H K) (hw : CurvatureBounds w P H K)
    (hUniform : ∀ s : Set Plane, s ⊆ (U : Set Plane) → IsCompact s →
      TendstoUniformlyOn (fun n => (W n).gradient) w.gradient atTop s)
    {φ : Plane → ℝ} (hφ : Integrable φ (volume.restrict (U : Set Plane))) :
    Tendsto (fun n => ∫ x in ↑U, ((W n).hessian x).q * φ x) atTop
      (𝓝 (∫ x in ↑U, (w.hessian x).q * φ x)) := by
  let μ := volume.restrict (U : Set Plane)
  let qW (n : ℕ) (x : Plane) := ((W n).hessian x).q
  let qw (x : Plane) := (w.hessian x).q
  have hQ (j : WeakJet2 m U) (hj : CurvatureBounds j P H K) :
      ∀ᵐ x ∂μ, ‖(j.hessian x).q‖ ≤ K ^ 2 / 2 := by
    filter_upwards [hj.frobenius_bound] with x hx
    rw [Real.norm_eq_abs]
    exact (j.hessian x).abs_q_le.trans
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ (j.hessian x).frobenius_nonneg hx 2) (by norm_num))
  change Tendsto (fun n => ∫ x, qW n x * φ x ∂μ) atTop (𝓝 (∫ x, qw x * φ x ∂μ))
  refine weakStar_of_interior_smooth_tests U.isOpen (K ^ 2 / 2)
    (div_nonneg (pow_nonneg hK 2) (by norm_num))
    (fun n => (integrable_curvature (hW n)).aestronglyMeasurable)
    (integrable_curvature hw).aestronglyMeasurable (fun n => hQ (W n) (hW n)) (hQ w hw) ?_ hφ
  intro ψ hCompact hSmooth hSupp
  let τ : 𝓓(U, ℝ) := ⟨ψ, hSmooth, hCompact, hSupp⟩
  let ψxx := testSecond ex ex τ
  let ψxy := testSecond ey ex τ
  let ψyy := testSecond ey ey τ
  obtain ⟨B₀, hB₀⟩ := τ.hasCompactSupport.exists_bound_of_continuous τ.continuous
  obtain ⟨Bxx, hBxx⟩ := ψxx.hasCompactSupport.exists_bound_of_continuous ψxx.continuous
  obtain ⟨Bxy, hBxy⟩ := ψxy.hasCompactSupport.exists_bound_of_continuous ψxy.continuous
  obtain ⟨Byy, hByy⟩ := ψyy.hasCompactSupport.exists_bound_of_continuous ψyy.continuous
  let B := max Bxx (max Bxy Byy)
  have hGrad := tendsto_gram_quadratic_test
    ψxx.continuous.aestronglyMeasurable ψxy.continuous.aestronglyMeasurable
    ψyy.continuous.aestronglyMeasurable B
    (Eventually.of_forall fun x => (hBxx x).trans (le_max_left _ _))
    (Eventually.of_forall fun x => (hBxy x).trans ((le_max_left _ _).trans (le_max_right _ _)))
    (Eventually.of_forall fun x => (hByy x).trans ((le_max_right _ _).trans (le_max_right _ _)))
    (strongL2_gradient_column hW hw hUniform ex) (strongL2_gradient_column hW hw hUniform ey)
    (Eventually.of_forall fun n => (W n).weak_gramTest
      (hW n).value_mem (hW n).gradient_mem (hW n).second_mem hP hH
      (hW n).gradient_bound (hW n).second_bound τ)
    (w.weak_gramTest hw.value_mem hw.gradient_mem hw.second_mem hP hH
      hw.gradient_bound hw.second_bound τ)
  have hPair (j : WeakJet2 m U) (hj : CurvatureBounds j P H K) :
      (∫ x, ψ x * (j.hessian x).q ∂μ) =
        (∫ x, ψ x * inner ℝ (j.second x ex ex) (j.second x ey ey) ∂μ) -
        (∫ x, ψ x * inner ℝ (j.second x ey ex) (j.second x ey ex) ∂μ) := by
    have hc := j.second_eval_memLp_of_bound hj.second_mem.aestronglyMeasurable hj.second_bound
    exact integral_weighted_q_eq (hc ex ex) (hc ex ey) (hc ey ey)
      τ.continuous.aestronglyMeasurable (Eventually.of_forall hB₀)
  have hPair' (j : WeakJet2 m U) (hj : CurvatureBounds j P H K) :
      (∫ x, (j.hessian x).q * ψ x ∂μ) =
        (∫ x, ψ x * inner ℝ (j.second x ex ex) (j.second x ey ey) ∂μ) -
        (∫ x, ψ x * inner ℝ (j.second x ey ex) (j.second x ey ex) ∂μ) :=
    (integral_congr_ae (Eventually.of_forall fun x => mul_comm ((j.hessian x).q) (ψ x))).trans
      (hPair j hj)
  change Tendsto (fun n => ∫ x, ((W n).hessian x).q * ψ x ∂μ) atTop
    (𝓝 (∫ x, (w.hessian x).q * ψ x ∂μ))
  rw [hPair' w hw]
  exact hGrad.congr fun n => (hPair' (W n) (hW n)).symm

end C2Riemannian.WeakJet2
