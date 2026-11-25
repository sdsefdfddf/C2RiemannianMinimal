module

public import C2Riemannian.GluedTorusProfile
public import C2Riemannian.FlatTorusMetric
public import C2Riemannian.C2DiskJetUniqueness
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology BoundedContinuousFunction

namespace C2Riemannian.TorusDiskGeometry

public theorem GluedTorusJet.pointwise_bounds {F : UniversalTorusInputs} {δ₀ : ℝ}
    (V : GluedTorusJet F δ₀) (hδ : 0 ≤ δ₀) (x : Plane) :
    ‖V.value x‖ ≤ 2 * δ₀ ∧ ‖fderiv ℝ V.value x‖ ≤ 2 * δ₀ ∧
      tensorHS (iteratedFDeriv ℝ 2 V.value x) ≤ 2 * δ₀ := by
  by_cases hx : x ∈ Metric.closedBall (0 : Plane) 1
  · have hEq : closedUnitDiskJet V.contDiff_two = V.jet := by
      apply C2ClosedDisk.ext_value (by norm_num)
      apply BoundedContinuousFunction.ext
      intro y
      rw [closedUnitDiskJet_value, GluedTorusJet.value, diskFieldExtension_of_mem _ y.property]
    let y : Metric.closedBall (0 : Plane) 1 := ⟨x, hx⟩
    have h := (C2ClosedDisk.norm_pointJet_le V.jet y).trans V.norm_bound
    rw [← hEq] at h
    change max ‖(closedUnitDiskJet V.contDiff_two).1.1 y‖
      (max ‖(closedUnitDiskJet V.contDiff_two).1.2.1 y‖ ‖(closedUnitDiskJet V.contDiff_two).1.2.2 y‖)
        ≤ 2 * δ₀ at h
    rw [closedUnitDiskJet_value, closedUnitDiskJet_gradient_norm, closedUnitDiskJet_hessian_norm] at h
    obtain ⟨hV, hDG⟩ := max_le_iff.mp h
    exact ⟨hV, (max_le_iff.mp hDG).1, (max_le_iff.mp hDG).2⟩
  · have hOut : x ∉ tsupport V.value := by
      intro hs
      exact hx (Metric.closedBall_subset_closedBall (by norm_num : (9 / 64 : ℝ) ≤ 1)
        (V.support_smallBall hs))
    have hNear : V.value =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hOut
    have hF : fderiv ℝ V.value x = 0 := by simpa using hNear.fderiv_eq (𝕜 := ℝ)
    have hH : iteratedFDeriv ℝ 2 V.value x = 0 := by
      simpa using (hNear.iteratedFDeriv ℝ 2).eq_of_nhds
    rw [hNear.eq_of_nhds, hF, hH, Pi.zero_apply, tensorHS, map_zero, norm_zero, norm_zero, norm_zero]
    exact ⟨by positivity, by positivity, by positivity⟩

/-- The metric assembled from the glued profiles at a distinguished point of
the flat quotient, with all C²-smallness properties in the parallel frame. -/
public theorem exists_glued_flat_torus_metric (F : UniversalTorusInputs) (o : FlatTorus)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 8 ∧ δ₀ ≤ ε / 4 ∧
      ∃ V : GluedTorusJet F δ₀,
        ContDiff ℝ 2 (torusCoefficient V.value o ∘ torusProjection) ∧
        ContDiffOn ℝ ∞ (torusCoefficient V.value o ∘ torusProjection) {x | torusProjection x ≠ o} ∧
        (∀ q X, X ≠ 0 → 0 < torusMetricForm V.value o q X X) ∧
        (∀ x, ‖torusCoefficient V.value o (torusProjection x)‖ ≤ 2 * δ₀ ∧
          ‖fderiv ℝ (torusCoefficient V.value o ∘ torusProjection) x‖ ≤ 2 * δ₀ ∧
          tensorHS (iteratedFDeriv ℝ 2 (torusCoefficient V.value o ∘ torusProjection) x) ≤ 2 * δ₀) ∧
        (∀ x, ‖torusCoefficient V.value o (torusProjection x)‖ < ε ∧
          ‖fderiv ℝ (torusCoefficient V.value o ∘ torusProjection) x‖ < ε ∧
          tensorHS (iteratedFDeriv ℝ 2 (torusCoefficient V.value o ∘ torusProjection) x) < ε) ∧
        ∀ a : Plane, torusProjection a = o →
          let c := fun x => torusCoefficient V.value o (torusProjection (a + x))
          c 0 = 0 ∧ fderiv ℝ c 0 = 0 ∧ iteratedFDeriv ℝ 2 c 0 = 0 := by
  let δ := min (1 / 8 : ℝ) (ε / 4)
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by norm_num))
  have hδ₁ : δ ≤ 1 / 8 := min_le_left _ _
  have hδ₂ : δ ≤ ε / 4 := min_le_right _ _
  obtain ⟨V⟩ := exists_glued_torus_jet F hδ.le
  have hBounds := V.pointwise_bounds hδ.le
  have hLift := torusCoefficient_lift_bounds (C := 2 * δ) (by positivity) V.support_smallBall
    (fun x => (hBounds x).1) (fun x => (hBounds x).2.1) (fun x => (hBounds x).2.2) o
  refine ⟨δ, hδ, hδ₁, hδ₂, V, torusCoefficient_contDiff_two_lift V.contDiff_two V.support_smallBall o,
    torusCoefficient_smooth_off_fiber V.smooth_off_origin V.support_smallBall o, ?_, hLift, ?_, ?_⟩
  · intro q X hX
    apply torusMetricForm_positive (C := 2 * δ) (by positivity) (by linarith only [hδ₁])
      (fun x => (hBounds x).1) o q hX
  · intro x
    have hx := hLift x
    have hSmall : 2 * δ < ε := by linarith only [hδ₂, hε]
    exact ⟨hx.1.trans_lt hSmall, hx.2.1.trans_lt hSmall, hx.2.2.trans_lt hSmall⟩
  · intro a ha
    subst o
    have hg := torusCoefficient_origin_germ V.value a
    obtain ⟨h₀, h₁, h₂⟩ := V.zero_jet_at_origin
    exact ⟨hg.eq_of_nhds.trans h₀, (hg.fderiv_eq (𝕜 := ℝ)).trans h₁,
      ((hg.iteratedFDeriv ℝ 2).eq_of_nhds).trans h₂⟩

end C2Riemannian.TorusDiskGeometry
