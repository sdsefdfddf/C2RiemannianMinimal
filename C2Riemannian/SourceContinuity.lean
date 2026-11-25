module

public import C2Riemannian.LocalMetricSource
public import C2Riemannian.HessianTestLimit
public import C2Riemannian.CurvatureWeakStar
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions Topology

namespace C2Riemannian.WeakJet2

/-- Uniform convergence of the coefficients on compact subsets gives distributional
convergence of the corresponding scalar metric sources. -/
public theorem metric_source_tendsto_of_locally_uniform {U : Opens Plane}
    {v : ℕ → Plane → ℝ} {v₀ : Plane → ℝ}
    (hv : ∀ n, ContDiffOn ℝ 2 (v n) (U : Set Plane))
    (hv₀ : ContDiffOn ℝ 2 v₀ (U : Set Plane))
    (hUniform : ∀ s : Set Plane, s ⊆ (U : Set Plane) → IsCompact s →
      TendstoUniformlyOn v v₀ atTop s) (φ : 𝓓(U, ℝ)) :
    Tendsto (fun n => ∫ x in ↑U, φ x • (-metricYY (v n) x / 2)) atTop
      (𝓝 (∫ x in ↑U, φ x • (-metricYY v₀ x / 2))) := by
  let ψ := testSecond ey ey φ
  let S := tsupport (ψ : Plane → ℝ)
  have hU := hUniform S ψ.tsupport_subset ψ.hasCompactSupport
  obtain ⟨B₀, hB₀⟩ := ψ.hasCompactSupport.bddAbove_image
    ((hv₀.continuousOn.mono ψ.tsupport_subset).norm)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (Metric.tendstoUniformlyOn_iff.mp hU 1 zero_lt_one)
  have hTail : Tendsto (fun n => ∫ x in ↑U, ψ x • v (n + N) x) atTop
      (𝓝 (∫ x in ↑U, ψ x • v₀ x)) := by
    refine tendsto_smul_test_of_uniformOn ψ
      (fun n => (hv (n + N)).continuousOn.locallyIntegrableOn U.isOpen.measurableSet)
      (K := B₀ + 1) ?_ ?_
    · intro n x hx
      have hDist : dist (v (n + N) x) (v₀ x) < 1 := by
        rw [dist_comm]
        exact hN (n + N) (Nat.le_add_left _ _) x hx
      calc
        ‖v (n + N) x‖ ≤ ‖v₀ x‖ + dist (v (n + N) x) (v₀ x) := by simpa only [dist_eq_norm] using norm_le_insert' (v (n + N) x) (v₀ x)
        _ ≤ B₀ + 1 := add_le_add (hB₀ ⟨x, hx, rfl⟩) hDist.le
    · exact Metric.tendstoUniformlyOn_iff.mpr fun ε hε =>
        (tendsto_add_atTop_nat N).eventually
          (Metric.tendstoUniformlyOn_iff.mp hU ε hε)
  have hlim : Tendsto (fun n => ∫ x in ↑U, ψ x • v n x) atTop
      (𝓝 (∫ x in ↑U, ψ x • v₀ x)) :=
    (tendsto_add_atTop_iff_nat (f := fun n => ∫ x in ↑U, ψ x • v n x) N).mp hTail
  have hTest {f : Plane → ℝ} (hf : ContDiffOn ℝ 2 f (U : Set Plane)) :
      (∫ x in ↑U, φ x • (-metricYY f x / 2)) = (-1 / 2 : ℝ) * ∫ x in ↑U, ψ x • f x := by
    simp only [smul_eq_mul]
    have h (x : Plane) : φ x * (-metricYY f x / 2) = (-1 / 2 : ℝ) * (φ x * metricYY f x) := by ring
    simp_rw [h, integral_const_mul]
    congr 1
    simpa only [metricYY, ψ, testSecond_apply] using integral_lineDeriv₂_mul_on hf ey ey φ
  simp_rw [show ∀ n, _ from fun n => hTest (hv n), hTest hv₀]
  exact hlim.const_mul (-1 / 2)

/-- Distributional continuity of the reverse source, represented by the negative
Hessian determinant of the scalar height (a weak jet with one target coordinate). -/
public theorem reverse_source_tendsto_of_locally_uniform_gradient {U : Opens Plane}
    [IsFiniteMeasure (volume.restrict (U : Set Plane))]
    {W : ℕ → WeakJet2 1 U} {w : WeakJet2 1 U} {P H K : ℝ}
    (hP : 0 ≤ P) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hW : ∀ n, CurvatureBounds (W n) P H K) (hw : CurvatureBounds w P H K)
    (hUniform : ∀ s : Set Plane, s ⊆ (U : Set Plane) → IsCompact s →
      TendstoUniformlyOn (fun n => (W n).gradient) w.gradient atTop s)
    (φ : 𝓓(U, ℝ)) :
    Tendsto (fun n => ∫ x in ↑U, φ x • (-((W n).hessian x).q)) atTop
      (𝓝 (∫ x in ↑U, φ x • (-(w.hessian x).q))) := by
  have hφ : Integrable (φ : Plane → ℝ) (volume.restrict (U : Set Plane)) :=
    φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have h := curvature_weakStar_of_gradient_locally_uniform hP hH hK hW hw hUniform hφ
  simp only [smul_eq_mul, mul_neg, integral_neg]
  simpa only [mul_comm] using h.neg

end C2Riemannian.WeakJet2
