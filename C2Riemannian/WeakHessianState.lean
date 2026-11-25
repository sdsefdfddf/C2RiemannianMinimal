module

public import C2Riemannian.HessianReadouts
public import C2Riemannian.HessianBoundClosure

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace

namespace C2Riemannian.WeakJet2

/-- Replace the essentially bounded Hessian by a measurable map into its compact state ball. -/
public theorem exists_measurable_hessian_state {m : ℕ} {U : Opens Plane}
    (w : WeakJet2 m U) {K : ℝ} (hK : 0 ≤ K)
    (hMeas : AEStronglyMeasurable w.second (volume.restrict (U : Set Plane)))
    (hBound : ∀ᵐ x ∂volume.restrict (U : Set Plane), (w.hessian x).frobenius ≤ K) :
    ∃ state : Plane → HessianBall m K, Measurable state ∧
      ∀ᵐ x ∂volume.restrict (U : Set Plane), (state x).val = (w.hessian x).coordinates := by
  classical
  let μ := volume.restrict (U : Set Plane)
  let H := fun x => (w.hessian x).coordinates
  have h : AEMeasurable H μ := by
    apply AEStronglyMeasurable.aemeasurable
    simpa only [H, Function.comp_def, hessianColumns_apply, hessian] using
      (hessianColumns (m := m)).continuous.comp_aestronglyMeasurable hMeas
  let B := Metric.closedBall (0 : HessSpace m) K
  let g := (h.mk H ⁻¹' B).indicator (h.mk H)
  have hm : Measurable g := h.measurable_mk.indicator (h.measurable_mk Metric.isClosed_closedBall.measurableSet)
  have hg (x : Plane) : g x ∈ B := by
    change (h.mk H ⁻¹' B).indicator (h.mk H) x ∈ B
    by_cases hx : h.mk H x ∈ B
    · rw [indicator_of_mem (show x ∈ h.mk H ⁻¹' B from hx)]
      exact hx
    · rw [indicator_of_notMem (show x ∉ h.mk H ⁻¹' B from hx)]
      exact Metric.mem_closedBall_self hK
  refine ⟨fun x => ⟨g x, hg x⟩, hm.subtype_mk, ?_⟩
  filter_upwards [h.ae_eq_mk, hBound] with x heq hx
  change (h.mk H ⁻¹' B).indicator (h.mk H) x = H x
  have hHx : H x ∈ B := by
    simpa only [B, H, Metric.mem_closedBall, dist_zero_right, Hess3.norm_coordinates] using hx
  have hmHx : x ∈ h.mk H ⁻¹' B := by
    change h.mk H x ∈ B
    rw [← heq]
    exact hHx
  rw [indicator_of_mem hmHx]
  exact heq.symm

end C2Riemannian.WeakJet2
