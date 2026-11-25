module

public import C2Riemannian.PlanarCounterexampleA
public import C2Riemannian.GluedFlatTorusMetric
public import C2Riemannian.ClassicalC2ImmersionJet

set_option autoImplicit false
set_option maxHeartbeats 750000

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Topology

namespace C2Riemannian.TorusDiskGeometry

/-- A coordinate coefficient in the flat chart centered at the torus point lifted by a. -/
@[expose] public noncomputable def centeredCoefficient (f : Plane → ℝ) (o : FlatTorus) (a : Plane) :
    Plane → ℝ := fun x => torusCoefficient f o (torusProjection (a + x))

/-- Local weak isometries are expressed on an open neighborhood in a centered flat chart. -/
@[expose] public def HasLocalWeakTorusIsometry (f : Plane → ℝ) (o : FlatTorus) (m : ℕ) : Prop :=
  ∃ a : Plane, torusProjection a = o ∧
    ∃ U : Opens Plane, (0 : Plane) ∈ (U : Set Plane) ∧
      (U : Set Plane) ⊆ Metric.ball 0 (1 / 4) ∧
      ∃ w : WeakJet2 m U, w.LocallyBoundedOnCompacts ∧ w.IsometryInChart (centeredCoefficient f o a)

/-- The global chart formulation of a C² isometry on the flat quotient. -/
@[expose] public def IsGlobalC2TorusIsometry {m : ℕ} (f : Plane → ℝ) (o : FlatTorus)
    (G : FlatTorus → Target m) : Prop :=
  ContDiff ℝ 2 (G ∘ torusProjection) ∧
    ∀ a : Plane, ∀ x : Plane, x ∈ Metric.ball (0 : Plane) (1 / 4) →
      let D := fderiv ℝ (fun y => G (torusProjection (a + y))) x
      inner ℝ (D WeakJet2.ex) (D WeakJet2.ex) = 1 + centeredCoefficient f o a x ∧
      inner ℝ (D WeakJet2.ey) (D WeakJet2.ey) = 1 ∧
      inner ℝ (D WeakJet2.ex) (D WeakJet2.ey) = 0

public theorem GluedTorusJet.no_local_weak_torus_isometry {F : UniversalTorusInputs} {δ₀ : ℝ}
    (V : GluedTorusJet F δ₀) (hδ₀ : 0 < δ₀) (o : FlatTorus) (m : ℕ) :
    ¬ HasLocalWeakTorusIsometry V.value o m := by
  rintro ⟨a, ha, U, h0, _, w, hLoc, hIso⟩
  have hGerm : centeredCoefficient V.value o a =ᶠ[𝓝 (0 : Plane)] V.value := by
    rw [← ha]
    exact torusCoefficient_origin_germ V.value a
  have hEqNear : {x | centeredCoefficient V.value o a x = V.value x} ∈ 𝓝 (0 : Plane) := hGerm
  obtain ⟨r, hr, hBall⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (U.isOpen.mem_nhds h0) hEqNear)
  let W : Opens Plane := ⟨Metric.ball 0 r, Metric.isOpen_ball⟩
  have hWU : W ≤ U := fun x hx => (hBall hx).1
  let w' := w.restrict hWU
  have hLoc' : w'.LocallyBoundedOnCompacts := fun S hS hSub => hLoc S hS (hSub.trans hWU)
  have hIso' : w'.IsometryInChart V.value := by
    unfold WeakJet2.IsometryInChart at hIso ⊢
    have hi := MeasureTheory.ae_mono (Measure.restrict_mono hWU le_rfl) hIso
    filter_upwards [hi, ae_restrict_mem W.isOpen.measurableSet] with x hx hxW
    have he : centeredCoefficient V.value o a x = V.value x := (hBall hxW).2
    exact ⟨hx.1.trans (congrArg (1 + ·) he), hx.2⟩
  exact V.no_local_isometry_at_origin hδ₀ (Metric.mem_ball_self hr) w' hLoc' hIso'

public theorem globalC2TorusIsometry_yields_local {m : ℕ} {f : Plane → ℝ} {o : FlatTorus}
    {G : FlatTorus → Target m} (h : IsGlobalC2TorusIsometry f o G) :
    HasLocalWeakTorusIsometry f o m := by
  obtain ⟨a, ha⟩ := torusProjection_openQuotient.surjective o
  let U : Opens Plane := ⟨Metric.ball 0 (1 / 4), Metric.isOpen_ball⟩
  let g := fun y => G (torusProjection (a + y))
  have hg : ContDiff ℝ 2 g := h.1.comp (contDiff_const.add contDiff_id)
  let w : WeakJet2 m U := WeakJet2.classicalC2 g hg
  refine ⟨a, ha, U, Metric.mem_ball_self (by norm_num), Subset.rfl, w,
    WeakJet2.classicalC2_locallyBounded hg, ?_⟩
  unfold WeakJet2.IsometryInChart
  exact (ae_restrict_mem U.isOpen.measurableSet).mono fun x hx => h.2 a x hx

end C2Riemannian.TorusDiskGeometry

namespace C2Riemannian

open TorusDiskGeometry

/-- Theorem A on the flat quotient, with the metric and its C² distance measured in the parallel frame. -/
public theorem theorem_A (o : FlatTorus) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : Plane → ℝ, ∃ C : ℝ, C < ε ∧
      ContDiff ℝ 2 (torusCoefficient f o ∘ torusProjection) ∧
      ContDiffOn ℝ ∞ (torusCoefficient f o ∘ torusProjection) {x | torusProjection x ≠ o} ∧
      (∀ q X, X ≠ 0 → 0 < torusMetricForm f o q X X) ∧
      (∀ x, ‖torusCoefficient f o (torusProjection x)‖ ≤ C ∧
        ‖fderiv ℝ (torusCoefficient f o ∘ torusProjection) x‖ ≤ C ∧
        tensorHS (iteratedFDeriv ℝ 2 (torusCoefficient f o ∘ torusProjection) x) ≤ C) ∧
      (∀ a : Plane, torusProjection a = o →
        centeredCoefficient f o a 0 = 0 ∧ fderiv ℝ (centeredCoefficient f o a) 0 = 0 ∧
        iteratedFDeriv ℝ 2 (centeredCoefficient f o a) 0 = 0) ∧
      (∀ m : ℕ, 0 < m → ¬ HasLocalWeakTorusIsometry f o m) ∧
      (∀ (m : ℕ), 0 < m → ∀ G : FlatTorus → Target m, ¬ IsGlobalC2TorusIsometry f o G) := by
  obtain ⟨F⟩ := exists_countable_obstructing_inputs
  obtain ⟨δ, hδ, _, hδε, V, hC2, hSmooth, hPos, hBounds, _, hJet⟩ := exists_glued_flat_torus_metric F o hε
  have hSmall : 2 * δ < ε := by linarith only [hδε, hε]
  refine ⟨V.value, 2 * δ, hSmall, hC2, hSmooth, hPos, hBounds, hJet, ?_, ?_⟩
  · exact fun m _ => V.no_local_weak_torus_isometry hδ o m
  · intro m _ G hg
    exact V.no_local_weak_torus_isometry hδ o m (globalC2TorusIsometry_yields_local hg)

end C2Riemannian
