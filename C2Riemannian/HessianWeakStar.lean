module

public import C2Riemannian.HessianBoundClosure
public import C2Riemannian.WeakStarExtension

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions Topology

namespace C2Riemannian.WeakJet2

variable {m : ℕ} {U : Opens Plane}

/-- The weak Hessian converges against all scalar L¹ tests in every fixed
Frobenius direction once the second-column tests converge and the exact bound is known. -/
public theorem hessian_weakStar_of_column_tests {W : ℕ → WeakJet2 m U} {w : WeakJet2 m U}
    (hW : ∀ n, AEStronglyMeasurable (W n).second (volume.restrict (U : Set Plane)))
    (hw : AEStronglyMeasurable w.second (volume.restrict (U : Set Plane)))
    {K : ℝ} (hK : 0 ≤ K)
    (hBW : ∀ n, ∀ᵐ x ∂volume.restrict (U : Set Plane), ((W n).hessian x).frobenius ≤ K)
    (hBw : ∀ᵐ x ∂volume.restrict (U : Set Plane), (w.hessian x).frobenius ≤ K)
    (hcol : ∀ (v u : Plane) (φ : 𝓓(U, ℝ)), Tendsto
      (fun n => ∫ x in ↑U, φ x • (W n).second x v u) atTop
      (𝓝 (∫ x in ↑U, φ x • w.second x v u)))
    (e : HessSpace m) {ψ : Plane → ℝ} (hψ : IntegrableOn ψ (U : Set Plane) volume) :
    Tendsto (fun n => ∫ x in ↑U, inner ℝ ((W n).hessian x).coordinates e * ψ x) atTop
      (𝓝 (∫ x in ↑U, inner ℝ (w.hessian x).coordinates e * ψ x)) := by
  have hmeas (j : WeakJet2 m U)
      (hj : AEStronglyMeasurable j.second (volume.restrict (U : Set Plane))) :
      AEStronglyMeasurable (fun x => inner ℝ (j.hessian x).coordinates e)
        (volume.restrict (U : Set Plane)) := by
    have h : AEStronglyMeasurable (fun x => (j.hessian x).coordinates)
        (volume.restrict (U : Set Plane)) := by
      simpa only [Function.comp_def, hessianColumns_apply, hessian] using
        (hessianColumns (m := m)).continuous.comp_aestronglyMeasurable hj
    exact h.inner aestronglyMeasurable_const
  have hb (j : WeakJet2 m U)
      (hj : ∀ᵐ x ∂volume.restrict (U : Set Plane), (j.hessian x).frobenius ≤ K) :
      ∀ᵐ x ∂volume.restrict (U : Set Plane), ‖inner ℝ (j.hessian x).coordinates e‖ ≤ K * ‖e‖ :=
    hj.mono fun x hx => (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right ((j.hessian x).norm_coordinates.trans_le hx) (norm_nonneg _))
  refine weakStar_of_interior_smooth_tests U.isOpen (K * ‖e‖) (mul_nonneg hK (norm_nonneg _))
    (fun n => hmeas (W n) (hW n)) (hmeas w hw) (fun n => hb (W n) (hBW n)) (hb w hBw) ?_ hψ
  intro φ hc hd hsub
  let t : 𝓓(U, ℝ) := ⟨φ, hd, hc, hsub⟩
  have ht (x : Plane) : t x = φ x := rfl
  simpa only [ht, mul_comm] using tendsto_hessian_coordinates_test hcol e t

end C2Riemannian.WeakJet2

