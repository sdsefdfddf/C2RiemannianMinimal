module

public import C2Riemannian.WeakAnalysis
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions Topology

namespace C2Riemannian

/-- Bounded readouts tested against the remainder of the two phases have
vanishing pairings whenever the remainder has vanishing mass. -/
public theorem remainder_pairing_tendsto {U : Opens Plane} (φ : 𝓓(U, ℝ))
    (r u : ℕ → Plane → ℝ) (B : ℝ)
    (hMass : Tendsto (fun n => ∫ x in tsupport (φ : Plane → ℝ), r n x) atTop (𝓝 0))
    (hInt : ∀ n, IntegrableOn (r n) (tsupport (φ : Plane → ℝ)) volume)
    (hr : ∀ n, ∀ᵐ x ∂volume.restrict (tsupport (φ : Plane → ℝ)), 0 ≤ r n x)
    (hu : ∀ n, ∀ᵐ x ∂volume.restrict (U : Set Plane), ‖u n x‖ ≤ B) :
    Tendsto (fun n => ∫ x in ↑U, φ x * r n x * u n x) atTop (𝓝 0) := by
  let S := tsupport (φ : Plane → ℝ)
  have hsub : S ⊆ (U : Set Plane) := φ.tsupport_subset
  obtain ⟨C, hC⟩ := φ.hasCompactSupport.exists_bound_of_continuous φ.continuous
  have hRest (n : ℕ) : (∫ x in ↑U, φ x * r n x * u n x) =
      ∫ x in S, φ x * r n x * u n x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero U.isOpen.measurableSet hsub
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx.2, zero_mul, zero_mul]
  simp only [hRest]
  have hB : ∀ n, ∀ᵐ x ∂volume.restrict S, ‖u n x‖ ≤ B :=
    fun n => ae_mono (Measure.restrict_mono hsub le_rfl) (hu n)
  have hLim : Tendsto (fun n => (C * B) * ∫ x in S, r n x) atTop (𝓝 0) := by
    simpa only [mul_zero] using hMass.const_mul (C * B)
  refine squeeze_zero_norm (fun n => ?_) hLim
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le ((hInt n).const_mul (C * B))
  filter_upwards [hr n, hB n] with x hx hux
  rw [norm_mul, norm_mul, Real.norm_of_nonneg hx]
  calc
    ‖φ x‖ * r n x * ‖u n x‖ ≤ (C * r n x) * B :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hC x) hx) hux (norm_nonneg _)
        (mul_nonneg ((norm_nonneg _).trans (hC x)) hx)
    _ = _ := by ac_rfl

/-- The two conditional first moments average to the parent readout.
The residual contribution is tested on the same domain and same sequence. -/
public theorem conditional_barycenter_ae {U : Opens Plane}
    {parent plus minus : Plane → ℝ}
    (hp : LocallyIntegrableOn parent (U : Set Plane) volume)
    (hpm : LocallyIntegrableOn (fun x => (plus x + minus x) / 2) (U : Set Plane) volume)
    (left right rest : 𝓓(U, ℝ) → ℕ → ℝ)
    (hLeft : ∀ φ, Tendsto (left φ) atTop (𝓝 (∫ x in ↑U, φ x * plus x)))
    (hRight : ∀ φ, Tendsto (right φ) atTop (𝓝 (∫ x in ↑U, φ x * minus x)))
    (hRest : ∀ φ, Tendsto (rest φ) atTop (𝓝 0))
    (hWhole : ∀ φ, Tendsto (fun n => (left φ n + right φ n) / 2 + rest φ n) atTop
      (𝓝 (∫ x in ↑U, φ x * parent x)))
    (hi : ∀ φ : 𝓓(U, ℝ),
      IntegrableOn (fun x => φ x * plus x) (U : Set Plane) volume ∧
      IntegrableOn (fun x => φ x * minus x) (U : Set Plane) volume) :
    parent =ᵐ[volume.restrict (U : Set Plane)] (fun x => (plus x + minus x) / 2) := by
  apply ae_eq_of_test_integrals hp hpm
  intro φ
  have h := (((hLeft φ).add (hRight φ)).div_const 2).add (hRest φ)
  simp only [add_zero] at h
  simp only [smul_eq_mul]
  rw [tendsto_nhds_unique (hWhole φ) h]
  rw [← integral_add (hi φ).1 (hi φ).2, ← integral_div]
  congr 1
  funext x
  change (φ x * plus x + φ x * minus x) / 2 = φ x * ((plus x + minus x) / 2)
  rw [← mul_add, mul_div_assoc]

end C2Riemannian


