module

public import C2Riemannian.LocalMetricSource
public import C2Riemannian.LocalWeakCompatibility
public import C2Riemannian.OpenWeakRepresentative
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Normed.Group.Continuity

set_option autoImplicit false
set_option maxHeartbeats 850000

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Topology NNReal ENNReal

namespace C2Riemannian.WeakJet2

variable {m : ℕ} {U : Opens Plane}

private theorem chart_norm_bound {E : Type*} [NormedAddCommGroup E]
    {μ : Measure Plane} {f : Plane → E} (h : MemLp f ∞ μ) :
    ∃ C : ℝ≥0, ∀ᵐ x ∂μ, ‖f x‖ ≤ (C : ℝ) := by
  have hTop : eLpNormEssSup f μ < ⊤ := by
    simpa only [eLpNorm_exponent_top h.aestronglyMeasurable] using h.eLpNorm_lt_top
  exact eLpNormEssSup_lt_top_iff_isBoundedUnder.mp hTop

private theorem memLp_two_of_top {E : Type*} [NormedAddCommGroup E]
    {μ : Measure Plane} [IsFiniteMeasure μ] {g : Plane → E} (h : MemLp g ∞ μ) :
    MemLp g 2 μ := by
  obtain ⟨C, hC⟩ := chart_norm_bound (E := E) (μ := μ) (f := g) h
  exact MemLp.of_bound h.aestronglyMeasurable (C : ℝ) hC

private theorem second_eval_memLp_two_of_top (w : WeakJet2 m U)
    [IsFiniteMeasure (volume.restrict (U : Set Plane))]
    (hb : MemLp w.second ∞ (volume.restrict (U : Set Plane))) (a b : Plane) :
    MemLp (fun x => w.second x b a) 2 (volume.restrict (U : Set Plane)) := by
  obtain ⟨C, hC⟩ := chart_norm_bound
    (E := Plane →L[ℝ] (Plane →L[ℝ] Target m))
    (μ := volume.restrict (U : Set Plane)) (f := w.second) hb
  exact w.second_eval_memLp_of_bound hb.aestronglyMeasurable (C := (C : ℝ)) hC a b

private theorem bounded_source_of_isometry_local (w : WeakJet2 m U)
    [IsFiniteMeasure (volume.restrict (U : Set Plane))]
    {v : Plane → ℝ} (hv : ContDiffOn ℝ 2 v (U : Set Plane)) (hIso : w.IsometryInChart v)
    (hw : MemLp w.value ∞ (volume.restrict (U : Set Plane)))
    (hp : MemLp w.gradient ∞ (volume.restrict (U : Set Plane)))
    (hb : MemLp w.second ∞ (volume.restrict (U : Set Plane))) :
    ∀ᵐ x ∂volume.restrict (U : Set Plane), (w.hessian x).q = -metricYY v x / 2 := by
  let μ := volume.restrict (U : Set Plane)
  have hw₂ : MemLp w.value 2 μ :=
    memLp_two_of_top (E := Target m) (μ := μ) (g := w.value) hw
  have hp₂ : MemLp w.gradient 2 μ :=
    memLp_two_of_top (E := Plane →L[ℝ] Target m) (μ := μ) (g := w.gradient) hp
  have hb₂ : MemLp w.second 2 μ :=
    memLp_two_of_top (E := Plane →L[ℝ] (Plane →L[ℝ] Target m)) (μ := μ) (g := w.second) hb
  have hxx := second_eval_memLp_two_of_top w hb ex ex
  have hxy := second_eval_memLp_two_of_top w hb ex ey
  have hyy := second_eval_memLp_two_of_top w hb ey ey
  have hi : IntegrableOn (fun x => (w.hessian x).q) (U : Set Plane) volume :=
    (integrable_weak_inner hxx hyy).sub (integrable_weak_inner hxy hxy)
  apply w.hessian_q_eq_metric_source_on_of_tests hv hi.locallyIntegrableOn hIso
  intro φ
  obtain ⟨C, hφ⟩ := φ.hasCompactSupport.exists_bound_of_continuous φ.continuous
  rw [integral_weighted_q_eq hxx hxy hyy φ.continuous.aestronglyMeasurable
    (Eventually.of_forall hφ)]
  exact w.weak_gramTest_l2 hw₂ hp₂ hb₂ φ

/-- The curvature source equation for locally bounded coordinate isometries. -/
public theorem hessian_q_eq_metric_source_local_top (w : WeakJet2 m U) {v : Plane → ℝ}
    (hv : ContDiffOn ℝ 2 v (U : Set Plane)) (hIso : w.IsometryInChart v)
    (hlocal : ∀ s : Set Plane, IsCompact s → s ⊆ (U : Set Plane) →
      MemLp w.value ∞ (volume.restrict s) ∧ MemLp w.gradient ∞ (volume.restrict s) ∧
      MemLp w.second ∞ (volume.restrict s)) :
    ∀ᵐ x ∂volume.restrict (U : Set Plane), (w.hessian x).q = -metricYY v x / 2 := by
  classical
  have hLocal (x : U) : ∃ V : Set Plane, x.1 ∈ V ∧ IsOpen V ∧ V ⊆ (U : Set Plane) ∧
      (∀ᵐ y ∂volume.restrict V, (w.hessian y).q = -metricYY v y / 2) := by
    obtain ⟨r, hr, hBall⟩ := Metric.mem_nhds_iff.mp (U.isOpen.mem_nhds x.2)
    let s : Set Plane := Metric.closedBall (x : Plane) (r / 2)
    let V : Opens Plane := ⟨Metric.ball (x : Plane) (r / 2), Metric.isOpen_ball⟩
    have hSub : s ⊆ (U : Set Plane) :=
      (Metric.closedBall_subset_ball (half_lt_self hr)).trans hBall
    have hVs : (V : Set Plane) ⊆ s := Metric.ball_subset_closedBall
    have hs : IsCompact s := isCompact_closedBall _ _
    let _ : IsFiniteMeasure (volume.restrict (V : Set Plane)) :=
      isFiniteMeasure_restrict.mpr ((measure_mono hVs).trans_lt hs.measure_lt_top).ne
    have hμ : (volume : Measure Plane).restrict (V : Set Plane) ≤ volume.restrict s :=
      Measure.restrict_mono hVs le_rfl
    let W : WeakJet2 m V := w.restrict (hVs.trans hSub)
    have hIsoV : W.IsometryInChart v := by
      unfold IsometryInChart at hIso ⊢
      exact ae_mono (Measure.restrict_mono (hVs.trans hSub) le_rfl) hIso
    obtain ⟨hw, hp, hb⟩ := hlocal s hs hSub
    refine ⟨V, Metric.mem_ball_self (half_pos hr), V.isOpen, hVs.trans hSub, ?_⟩
    exact bounded_source_of_isometry_local (U := V) W (hv.mono (hVs.trans hSub)) hIsoV
      (hw.mono_measure hμ) (hp.mono_measure hμ) (hb.mono_measure hμ)
  choose V hMem hOpen hSub hEq using hLocal
  obtain ⟨T, hCount, hCover⟩ := isOpen_iUnion_countable V hOpen
  have hAll : (U : Set Plane) = ⋃ i ∈ T, V i := by
    rw [hCover]
    exact subset_antisymm (fun x hx => mem_iUnion_of_mem ⟨x, hx⟩ (hMem ⟨x, hx⟩))
      (iUnion_subset hSub)
  rw [hAll]
  exact (ae_restrict_biUnion_iff V hCount _).2 fun i _ => hEq i

/-- A coordinate isometry gives a classical immersed representative and the weak curvature equation. -/
public theorem classical_isometry_representative (w : WeakJet2 m U) {v : Plane → ℝ}
    (hv : ContDiffOn ℝ 2 v (U : Set Plane)) (hIso : w.IsometryInChart v)
    (hPos : ∀ x ∈ (U : Set Plane), 0 < 1 + v x)
    (hlocal : ∀ s : Set Plane, IsCompact s → s ⊆ (U : Set Plane) →
      MemLp w.value ∞ (volume.restrict s) ∧ MemLp w.gradient ∞ (volume.restrict s) ∧
      MemLp w.second ∞ (volume.restrict s)) :
    ∃ (W : Plane → Target m) (P : Plane → Plane →L[ℝ] Target m),
      ContDiffOn ℝ 1 W (U : Set Plane) ∧
      (∀ x ∈ (U : Set Plane), HasFDerivAt W (P x) x ∧ Function.Injective (P x)) ∧
      LocallyLipschitzOn (U : Set Plane) P ∧
      W =ᵐ[volume.restrict (U : Set Plane)] w.value ∧
      P =ᵐ[volume.restrict (U : Set Plane)] w.gradient ∧
      (∀ᵐ x ∂volume.restrict (U : Set Plane), (w.hessian x).q = -metricYY v x / 2) := by
  have hBall (x : U) : ∃ R : ℝ, 0 < R ∧ Metric.ball (x : Plane) R ⊆ (U : Set Plane) ∧
      MemLp w.value ∞ (volume.restrict (Metric.ball (x : Plane) R)) ∧
      MemLp w.gradient ∞ (volume.restrict (Metric.ball (x : Plane) R)) ∧
      MemLp w.second ∞ (volume.restrict (Metric.ball (x : Plane) R)) := by
    obtain ⟨r, hr, hrSubset⟩ := Metric.mem_nhds_iff.mp (U.isOpen.mem_nhds x.2)
    have hC := (Metric.closedBall_subset_ball (half_lt_self hr)).trans hrSubset
    obtain ⟨hW, hP, hB⟩ := hlocal _ (isCompact_closedBall _ _) hC
    have hMeasure : (volume : Measure Plane).restrict (Metric.ball (x : Plane) (r / 2)) ≤
        volume.restrict (Metric.closedBall (x : Plane) (r / 2)) :=
      Measure.restrict_mono Metric.ball_subset_closedBall le_rfl
    exact ⟨r / 2, half_pos hr, Metric.ball_subset_closedBall.trans hC,
      hW.mono_measure hMeasure, hP.mono_measure hMeasure, hB.mono_measure hMeasure⟩
  obtain ⟨W, P, hW, hDeriv, hLip, hWAe, hPAe⟩ :=
    w.exists_classical_representative_of_locally_memLp_top hBall
  have hInj := injective_of_isometry_representative hIso hLip.continuousOn hPAe hv.continuousOn hPos
  exact ⟨W, P, hW, fun x hx => ⟨hDeriv x hx, hInj x hx⟩, hLip, hWAe, hPAe,
    w.hessian_q_eq_metric_source_local_top hv hIso hlocal⟩

end C2Riemannian.WeakJet2
