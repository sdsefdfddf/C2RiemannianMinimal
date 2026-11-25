module

public import C2Riemannian.AffineDiskPullback
public import C2Riemannian.WeakJetDimension
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped NNReal ENNReal

namespace C2Riemannian

public theorem Hess3.frobenius_scale {m : ℕ} (H : Hess3 m) (c : ℝ) :
    (H.scale c).frobenius = ‖c‖ * H.frobenius := by
  apply (sq_eq_sq₀ (H.scale c).frobenius_nonneg (mul_nonneg (norm_nonneg _) H.frobenius_nonneg)).mp
  simp only [Hess3.sq_frobenius, Hess3.frobeniusSq, Hess3.scale, norm_smul, mul_pow]
  ring

namespace WeakJet2

/-- The square-root normalization of the height cancels the amplitude in the scalar curvature source. -/
public theorem solves_unit_source_of_radial_pullback {m : ℕ}
    (a : Plane) (r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ) (K K' : ℝ≥0)
    (w : WeakJet2 m (⟨Metric.ball a r, Metric.isOpen_ball⟩ : Opens Plane))
    (hW : MemLp w.value ∞ (volume.restrict (Metric.ball a r)))
    (hP : MemLp w.gradient ∞ (volume.restrict (Metric.ball a r)))
    (hK : ∀ᵐ x ∂volume.restrict (Metric.ball a r), (w.hessian x).frobenius ≤ (K : ℝ))
    (hBound : (K : ℝ) / Real.sqrt δ ≤ (K' : ℝ))
    (F : Plane → ℝ)
    (hSource : ∀ᵐ x ∂volume.restrict (unitDisk : Set Plane),
      (w.hessian (diskDilation a r x)).q = δ * F x) :
    DiskSolvability.Solves m 0 1 K' F := by
  let c := (r ^ 2 * Real.sqrt δ)⁻¹
  have hs := Real.sqrt_pos.2 hδ
  have hc : c * r ^ 2 = (Real.sqrt δ)⁻¹ := by
    dsimp [c]
    field_simp
  obtain ⟨W, hv, hp, hh⟩ := exists_radial_pullback a r c hr K w hW hP hK
  have hb : ∀ᵐ x ∂volume.restrict (unitDisk : Set Plane), (W.hessian x).frobenius ≤ (K' : ℝ) := by
    filter_upwards [hh, (diskDilation_quasiMeasurePreserving a hr).ae hK] with x hx hxK
    rw [hx, Hess3.frobenius_scale, hc, Real.norm_of_nonneg (inv_nonneg.mpr hs.le)]
    have hh := mul_le_mul_of_nonneg_left hxK (inv_nonneg.mpr hs.le)
    exact hh.trans (by simpa only [div_eq_mul_inv, mul_comm] using hBound)
  refine ⟨W, hv, hp, W.second_memLp_top_of_frobenius_ae_le hb, hb, ?_⟩
  have hsq : ((Real.sqrt δ)⁻¹) ^ 2 = δ⁻¹ := by rw [inv_pow, Real.sq_sqrt hδ.le]
  filter_upwards [hh, hSource] with x hx hq
  change (W.hessian x).q = F x
  rw [hx, Hess3.q_scale, hc, hsq, hq, ← mul_assoc, inv_mul_cancel₀ hδ.ne', one_mul]

end WeakJet2
end C2Riemannian
