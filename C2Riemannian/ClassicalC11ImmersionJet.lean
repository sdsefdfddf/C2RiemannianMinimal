module

public import C2Riemannian.ClassicalC2ImmersionJet
public import C2Riemannian.ClassicalToWeakJet
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

set_option autoImplicit false
set_option maxHeartbeats 800000

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff ENNReal NNReal

namespace C2Riemannian

private theorem memLp_top_of_continuousOn_compact {E : Type*} [NormedAddCommGroup E]
    {S : Set Plane} (hS : IsCompact S) {f : Plane → E} (hf : ContinuousOn f S) :
    MemLp f ∞ (volume.restrict S) := by
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hf
  exact memLp_top_of_bound (hf.aestronglyMeasurable_of_isCompact hS hS.isClosed.measurableSet) C
    ((ae_restrict_mem hS.isClosed.measurableSet).mono hC)

private theorem hessian_frobenius_le_of_second_bound {m : ℕ} {U : Opens Plane}
    (w : WeakJet2 m U) (x : Plane) (L : ℝ≥0) (hB : ‖w.second x‖ ≤ (L : ℝ)) :
    (w.hessian x).frobenius ≤ 2 * (L : ℝ) := by
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  have hEntry (i j : Fin 2) : ‖w.second x (e i) (e j)‖ ≤ (L : ℝ) := by
    calc
      ‖w.second x (e i) (e j)‖ ≤ ‖w.second x (e i)‖ * ‖e j‖ := (w.second x (e i)).le_opNorm _
      _ = ‖w.second x (e i)‖ := by rw [e.orthonormal.norm_eq_one j, mul_one]
      _ ≤ ‖w.second x‖ * ‖e i‖ := (w.second x).le_opNorm _
      _ ≤ (L : ℝ) := by rwa [e.orthonormal.norm_eq_one i, mul_one]
  have hsq (i j : Fin 2) := pow_le_pow_left₀ (norm_nonneg _) (hEntry i j) 2
  rw [Hess3.frobenius, Hess3.frobeniusSq, ← Real.sqrt_sq (mul_nonneg zero_le_two L.coe_nonneg)]
  apply Real.sqrt_le_sqrt
  simpa only [WeakJet2.hessian, e, EuclideanSpace.basisFun_apply] using
    (show ‖w.second x (e 0) (e 0)‖ ^ 2 + 2 * ‖w.second x (e 1) (e 0)‖ ^ 2 +
      ‖w.second x (e 1) (e 1)‖ ^ 2 ≤ (2 * (L : ℝ)) ^ 2 from by
        nlinarith only [hsq 0 0, hsq 1 0, hsq 1 1])

private theorem locallyBounded_of_locallyLipschitz_gradient {m : ℕ}
    {U : Opens Plane} (w : WeakJet2 m U) (hV : ContinuousOn w.value (U : Set Plane))
    (hP : LocallyLipschitzOn (U : Set Plane) w.gradient)
    (hSecond : w.second = fderiv ℝ w.gradient) : w.LocallyBoundedOnCompacts := by
  intro S hS hSU
  obtain ⟨δ, hδ, hδU⟩ := hS.exists_cthickening_subset_open U.isOpen hSU
  obtain ⟨L, hL⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hS.cthickening
    (hP.mono hδU)
  have hbound (x : Plane) (hx : x ∈ S) : ‖w.second x‖ ≤ (L : ℝ) := by
    rw [hSecond]
    exact norm_fderiv_le_of_lipschitzOn ℝ
      (mem_of_superset (Metric.closedBall_mem_nhds x hδ) (Metric.closedBall_subset_cthickening hx δ)) hL
  have hbound_ae : ∀ᵐ x ∂volume.restrict S, ‖w.second x‖ ≤ (L : ℝ) :=
    (ae_restrict_mem (μ := volume) hS.isClosed.measurableSet).mono hbound
  have hmeasurable : AEStronglyMeasurable w.second (volume.restrict S) :=
    w.weak_gradient.locallyIntegrableOn_deriv.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono hSU le_rfl)
  have hValue : MemLp w.value ∞ (volume.restrict S) :=
    memLp_top_of_continuousOn_compact (E := Target m) (f := w.value) hS (hV.mono hSU)
  have hGradient : MemLp w.gradient ∞ (volume.restrict S) :=
    memLp_top_of_continuousOn_compact (E := Plane →L[ℝ] Target m) (f := w.gradient) hS
      (hP.continuousOn.mono hSU)
  have hBoundedSecond : MemLp w.second ∞ (volume.restrict S) := by
    apply memLp_top_of_bound (E := Plane →L[ℝ] (Plane →L[ℝ] Target m)) (f := w.second)
      hmeasurable (L : ℝ)
    exact hbound_ae
  have hFrobenius : ∀ᵐ x ∂volume.restrict S, (w.hessian x).frobenius ≤ 2 * (L : ℝ) := by
    filter_upwards [hbound_ae] with x hx
    exact hessian_frobenius_le_of_second_bound w x L hx
  have hHessian : ∃ B : ℝ, ∀ᵐ x ∂volume.restrict S, (w.hessian x).frobenius ≤ B :=
    ⟨2 * (L : ℝ), hFrobenius⟩
  exact And.intro hValue (And.intro hGradient (And.intro hBoundedSecond hHessian))

/-- The weak jet of a C¹ map with locally Lipschitz derivative is bounded on compacts. -/
public theorem weakJet2_of_contDiffOn_locallyLipschitz_locallyBounded {m : ℕ}
    {U : Opens Plane} {W : Plane → Target m} (hW : ContDiffOn ℝ 1 W U)
    (hP : LocallyLipschitzOn (U : Set Plane) (fderiv ℝ W)) :
    (weakJet2_of_contDiffOn_locallyLipschitz hW hP).LocallyBoundedOnCompacts :=
  locallyBounded_of_locallyLipschitz_gradient (weakJet2_of_contDiffOn_locallyLipschitz hW hP)
    hW.continuousOn hP rfl

end C2Riemannian
