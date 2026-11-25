module

public import C2Riemannian.GluedTorusProfile
public import C2Riemannian.WeakJetRescaledSource
public import C2Riemannian.ChartCurvature
public import C2Riemannian.ClassicalC2ImmersionJet

set_option autoImplicit false
set_option maxHeartbeats 1100000

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff ENNReal NNReal Topology

namespace C2Riemannian.TorusDiskGeometry

/-- The Hessian cost of reversing the amplitude is eventually below the chosen profile's bound. -/
public theorem eventually_rescaled_bound (C : ℝ≥0) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    ∀ᶠ n : ℕ in atTop, (C : ℝ) / Real.sqrt (amplitude δ₀ n) ≤ ((n + 1 : ℕ) : ℝ) := by
  obtain ⟨j, hj⟩ := exists_nat_gt ((C : ℝ) ^ 2 / δ₀)
  filter_upwards [eventually_ge_atTop j] with n hn
  have hcast : (j : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hn.trans (Nat.le_succ n)
  have hp : (C : ℝ) ^ 2 ≤ δ₀ * ((n + 1 : ℕ) : ℝ) := by
    have h := (div_lt_iff₀ hδ₀).mp hj
    calc
      (C : ℝ) ^ 2 ≤ (j : ℝ) * δ₀ := h.le
      _ ≤ ((n + 1 : ℕ) : ℝ) * δ₀ := mul_le_mul_of_nonneg_right hcast hδ₀.le
      _ = _ := mul_comm _ _
  have hpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hδ : 0 < amplitude δ₀ n := div_pos hδ₀ (by positivity)
  apply le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0) hpos.le
  rw [div_pow, Real.sq_sqrt hδ.le]
  apply (div_le_iff₀ hδ).2
  calc
    (C : ℝ) ^ 2 ≤ δ₀ * ((n + 1 : ℕ) : ℝ) := hp
    _ = ((n + 1 : ℕ) : ℝ) ^ 2 * amplitude δ₀ n := by
      simp only [amplitude, Nat.cast_add, Nat.cast_one]
      field_simp

/-- The glued profile has no local weak scalar solution near its accumulation point. -/
public theorem GluedTorusJet.no_local_source_solution {F : UniversalTorusInputs} {δ₀ : ℝ}
    (V : GluedTorusJet F δ₀) (hδ₀ : 0 < δ₀) {U : Opens Plane}
    (h0 : (0 : Plane) ∈ (U : Set Plane)) {m : ℕ}
    (w : WeakJet2 m U) (hLoc : w.LocallyBoundedOnCompacts) :
    ¬ ((fun x => (w.hessian x).q) =ᵐ[volume.restrict (U : Set Plane)]
      fun x => -WeakJet2.metricYY V.value x / 2) := by
  intro hEq
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp (U.isOpen.mem_nhds h0)
  let D := Metric.closedBall (0 : Plane) (R / 2)
  have hDU : D ⊆ (U : Set Plane) := (Metric.closedBall_subset_ball (half_lt_self hR)).trans hRU
  obtain ⟨hV, hG, _, C, hC⟩ := hLoc D (isCompact_closedBall _ _) hDU
  let K : ℝ≥0 := Real.toNNReal C
  have hK : ∀ᵐ x ∂volume.restrict D, (w.hessian x).frobenius ≤ (K : ℝ) := by
    filter_upwards [hC] with x hx
    exact hx.trans (le_max_left _ _)
  have hn : ∀ᶠ n : ℕ in atTop, closedDisk n ⊆ Metric.ball (0 : Plane) (R / 2) ∧
      (K : ℝ) / Real.sqrt (amplitude δ₀ n) ≤ ((n + 1 : ℕ) : ℝ) ∧ m ≤ n + 1 := by
    filter_upwards [eventually_closedDisk_subset_ball (half_pos hR),
      eventually_rescaled_bound K hδ₀, eventually_ge_atTop m] with n hd hk hm
    exact ⟨hd, hk, hm.trans (Nat.le_succ n)⟩
  obtain ⟨n, hnD, hnK, hnM⟩ := hn.exists
  have hsub : disk n ⊆ D := (Metric.ball_subset_closedBall.trans hnD).trans Metric.ball_subset_closedBall
  let small : Opens Plane := ⟨disk n, Metric.isOpen_ball⟩
  let w' := w.restrict (V := small) (hsub.trans hDU)
  have hμ := Measure.restrict_mono hsub (le_rfl : (volume : Measure Plane) ≤ volume)
  have hS : ∀ᵐ x ∂volume.restrict (WeakJet2.unitDisk : Set Plane),
      (w'.hessian (WeakJet2.diskDilation (center n) (radius n) x)).q =
        amplitude δ₀ n * (-WeakJet2.metricYY (F.profile n) x / 2) := by
    let T := WeakJet2.diskDilation (center n) (radius n)
    have hPull := WeakJet2.diskDilation_quasiMeasurePreserving (center n) (radius_pos n)
    have he := ae_mono (Measure.restrict_mono (hsub.trans hDU) le_rfl) hEq
    filter_upwards [hPull.ae_eq_comp he,
      ae_restrict_mem WeakJet2.unitDisk.isOpen.measurableSet] with x hx hxU
    have hxD := WeakJet2.diskDilation_mapsTo (center n) (radius_pos n) hxU
    change (w.hessian (T x)).q = amplitude δ₀ n * (-WeakJet2.metricYY (F.profile n) x / 2)
    change (w.hessian (T x)).q = -WeakJet2.metricYY V.value (T x) / 2 at hx
    have hcoord : scaledCoordinate n (T x) = x := by
      unfold scaledCoordinate T WeakJet2.diskDilation
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (radius_pos n).ne', one_smul]
    rw [hx, V.metricYY_on_disk n hxD, hcoord]
    ring
  have hδ : 0 < amplitude δ₀ n := div_pos hδ₀ (by positivity)
  have hSol := WeakJet2.solves_unit_source_of_radial_pullback (center n) (radius n) (amplitude δ₀ n)
    (radius_pos n) hδ K ((n + 1 : ℕ) : ℝ≥0) w'
    (hV.mono_measure hμ) (hG.mono_measure hμ) (ae_mono hμ hK) hnK _ hS
  exact F.not_solvable n (WeakJet2.DiskSolvability.solves_of_le_dimension hnM hSol)

/-- The glued C² coefficient has no locally bounded coordinate isometry at the origin. -/
public theorem GluedTorusJet.no_local_isometry_at_origin {F : UniversalTorusInputs} {δ₀ : ℝ}
    (V : GluedTorusJet F δ₀) (hδ₀ : 0 < δ₀) {U : Opens Plane}
    (h0 : (0 : Plane) ∈ (U : Set Plane)) {m : ℕ}
    (w : WeakJet2 m U) (hLoc : w.LocallyBoundedOnCompacts) : ¬ w.IsometryInChart V.value := by
  intro hIso
  exact V.no_local_source_solution hδ₀ h0 w hLoc
    (w.hessian_q_eq_metric_source_local_top V.contDiff_two.contDiffOn hIso
      (fun S hS hSub => ⟨(hLoc S hS hSub).1, (hLoc S hS hSub).2.1, (hLoc S hS hSub).2.2.1⟩))

end C2Riemannian.TorusDiskGeometry
