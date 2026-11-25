module

public import C2Riemannian.WeakAnalysis
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions Topology

namespace C2Riemannian

/-- An equality tested on the exact phase passes to the conditional readout.
The equality of the input sources is required only where the test meets
the phase, and only eventually in the layer index. -/
public theorem conditional_source_eq_ae {U : Opens Plane}
    {readout source : Plane → ℝ}
    (hReadout : LocallyIntegrableOn readout (U : Set Plane) volume)
    (hSource : LocallyIntegrableOn source (U : Set Plane) volume)
    (weight curvature : ℕ → Plane → ℝ)
    (hOnPhase : ∀ φ : 𝓓(U, ℝ),
      ∀ᶠ n in atTop, ∀ᵐ x ∂volume.restrict (U : Set Plane),
        x ∈ tsupport (φ : Plane → ℝ) → weight n x ≠ 0 → curvature n x = source x)
    (hCond : ∀ φ : 𝓓(U, ℝ),
      Tendsto (fun n => ∫ x in ↑U, weight n x * curvature n x * φ x) atTop
        (𝓝 (∫ x in ↑U, φ x * readout x)))
    (hEquidist : ∀ φ : 𝓓(U, ℝ),
      Tendsto (fun n => ∫ x in ↑U, weight n x * source x * φ x) atTop
        (𝓝 (∫ x in ↑U, φ x * source x))) :
    readout =ᵐ[volume.restrict (U : Set Plane)] source := by
  apply ae_eq_of_test_integrals hReadout hSource
  intro φ
  have hEq : (fun n => ∫ x in ↑U, weight n x * curvature n x * φ x) =ᶠ[atTop]
      (fun n => ∫ x in ↑U, weight n x * source x * φ x) := by
    filter_upwards [hOnPhase φ] with n hn
    apply integral_congr_ae
    filter_upwards [hn] with x h
    by_cases hs : x ∈ tsupport (φ : Plane → ℝ)
    · by_cases hw : weight n x = 0
      · simp only [hw, zero_mul]
      · rw [h hs hw]
    · simp only [image_eq_zero_of_notMem_tsupport hs, mul_zero]
  simpa only [smul_eq_mul] using tendsto_nhds_unique (hCond φ) ((hEquidist φ).congr' hEq.symm)

end C2Riemannian
