module

public import C2Riemannian.C2DiskJetUniqueness

public import C2Riemannian.ScaledTorusInputs

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction

namespace C2Riemannian.TorusDiskGeometry

/-- The limit jet glued from the scaled disk profiles. -/
public structure GluedTorusJet (F : UniversalTorusInputs) (δ₀ : ℝ) where
  jet : C2ClosedDisk (0 : Plane) 1
  norm_bound : ‖jet‖ ≤ 2 * δ₀
  on_disk : ∀ n (x : Metric.closedBall (0 : Plane) 1), (x : Plane) ∈ disk n →
    C2ClosedDisk.pointJet x jet = C2ClosedDisk.pointJet x (amplitudeJet F δ₀ n)
  zero_off_disks : ∀ x : Metric.closedBall (0 : Plane) 1,
    (∀ n, (x : Plane) ∉ disk n) → C2ClosedDisk.pointJet x jet = 0

private theorem disjoint_disks : Pairwise (fun i j => Disjoint (disk i) (disk j)) :=
  fun _ _ h => (disjoint_closed_disks h).mono Metric.ball_subset_closedBall Metric.ball_subset_closedBall

public theorem exists_glued_torus_jet (F : UniversalTorusInputs) {δ₀ : ℝ} (hδ : 0 ≤ δ₀) :
    Nonempty (GluedTorusJet F δ₀) := by
  let u := amplitudeJet F δ₀
  let A (n : ℕ) := 2 * amplitude δ₀ n
  have hA : Tendsto A atTop (𝓝 0) := by
    simpa only [mul_zero] using (amplitude_tendsto δ₀).const_mul (2 : ℝ)
  have hZero := pointJet_amplitudeJet_zero_off_disk F δ₀
  obtain ⟨v, hv⟩ := C2ClosedDisk.exists_tendsto_disjoint_jet_sums disk u disjoint_disks hZero
    A hA (amplitudeJet_bound F hδ)
  obtain ⟨hOn, hOff⟩ := C2ClosedDisk.disjoint_jet_sum_limit_fields disk u disjoint_disks hZero hv
  refine ⟨⟨v, ?_, hOn, hOff⟩⟩
  change ‖(v.1 : C2DiskFields (0 : Plane) 1)‖ ≤ 2 * δ₀
  have hv' : Tendsto
      (fun N => ‖((∑ n ∈ Finset.range N, u n : C2ClosedDisk (0 : Plane) 1).1 :
        C2DiskFields (0 : Plane) 1)‖) atTop (𝓝 ‖v.1‖) :=
    ((continuous_subtype_val.tendsto v).comp hv).norm
  apply le_of_tendsto hv'
  filter_upwards with N
  change ‖∑ n ∈ Finset.range N, u n‖ ≤ 2 * δ₀
  apply C2ClosedDisk.norm_finset_sum_le_of_disjoint_support disk u disjoint_disks hZero
    (Finset.range N) (mul_nonneg (by norm_num) hδ)
  intro n _
  have ha : amplitude δ₀ n ≤ δ₀ :=
    div_le_self hδ (le_add_of_nonneg_left (Nat.cast_nonneg n))
  exact (amplitudeJet_bound F hδ n).trans (mul_le_mul_of_nonneg_left ha (by norm_num))

namespace GluedTorusJet

variable {F : UniversalTorusInputs} {δ₀ : ℝ}

/-- The globally defined scalar coefficient, extended by zero. -/
@[expose] public noncomputable def value (V : GluedTorusJet F δ₀) : Plane → ℝ :=
  diskFieldExtension V.jet.1.1

/-- Each small disk carries its own scaled input exactly. -/
public theorem value_eq_on_disk (V : GluedTorusJet F δ₀) (n : ℕ) {x : Plane} (hx : x ∈ disk n) :
    V.value x = amplitude δ₀ n * scaledInput F n x := by
  have hu := Metric.ball_subset_closedBall (disk_subset_unitDisk n hx)
  have h := congrArg Prod.fst (V.on_disk n ⟨x, hu⟩ hx)
  rw [value, diskFieldExtension_of_mem _ hu]
  change V.jet.1.1 ⟨x, hu⟩ = amplitude δ₀ n * (scaledUnitJet F n).1.1 ⟨x, hu⟩ at h
  rw [scaledUnitJet_value] at h
  exact h

public theorem value_zero_off_disks (V : GluedTorusJet F δ₀) {x : Plane}
    (hx : ∀ n, x ∉ disk n) : V.value x = 0 := by
  classical
  by_cases hb : x ∈ Metric.closedBall (0 : Plane) 1
  · have h := congrArg Prod.fst (V.zero_off_disks ⟨x, hb⟩ hx)
    rw [value, diskFieldExtension_of_mem _ hb]
    exact h
  · simp [value, diskFieldExtension, hb]

public theorem support_smallBall (V : GluedTorusJet F δ₀) :
    tsupport V.value ⊆ Metric.closedBall (0 : Plane) (9 / 64) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra h
  apply hx
  apply V.value_zero_off_disks
  intro n hn
  exact h (closedDisk_subset_smallBall n (Metric.ball_subset_closedBall hn))

/-- The glued profile is C² at the accumulation point and on the whole plane. -/
public theorem contDiff_two (V : GluedTorusJet F δ₀) : ContDiff ℝ 2 V.value := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ Metric.ball (0 : Plane) 1
  · exact V.jet.contDiffOn_value.contDiffAt (Metric.isOpen_ball.mem_nhds hx)
  · have hOut : x ∉ tsupport V.value := by
      intro hs
      exact hx (Metric.closedBall_subset_ball (by norm_num : (9 / 64 : ℝ) < 1) (V.support_smallBall hs))
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hOut)

/-- Off the origin a compact neighborhood meets finitely many disks, so the
profile there is a finite sum of globally smooth inputs. -/
public theorem smooth_off_origin (V : GluedTorusJet F δ₀) :
    ContDiffOn ℝ ∞ V.value ({0}ᶜ : Set Plane) := by
  intro x hx
  have h0 : x ∈ ({0}ᶜ : Set Plane) := hx
  obtain ⟨e, he, hBall⟩ := Metric.mem_nhds_iff.mp (isClosed_singleton.isOpen_compl.mem_nhds h0)
  let K := Metric.closedBall x (e / 2)
  have hK0 : (0 : Plane) ∉ K := by
    intro hz
    exact hBall (Metric.closedBall_subset_ball (half_lt_self he) hz) rfl
  let I := (disks_only_accumulate_at_origin Metric.isClosed_closedBall hK0).toFinset
  let g (z : Plane) := ∑ n ∈ I, amplitude δ₀ n * scaledInput F n z
  have hG : ContDiff ℝ ∞ g :=
    ContDiff.sum (fun n _ => contDiff_const.mul (scaledInput_smooth F n))
  have hNear : V.value =ᶠ[𝓝 x] g := by
    filter_upwards [Metric.ball_mem_nhds x (half_pos he)] with z hz
    classical
    by_cases h : ∃ n, z ∈ disk n
    · obtain ⟨n, hn⟩ := h
      have hnI : n ∈ I := by
        rw [Set.Finite.mem_toFinset]
        exact ⟨z, Metric.ball_subset_closedBall hn, Metric.ball_subset_closedBall hz⟩
      rw [V.value_eq_on_disk n hn]
      change amplitude δ₀ n * scaledInput F n z = ∑ j ∈ I, amplitude δ₀ j * scaledInput F j z
      symm
      apply Finset.sum_eq_single n _ (fun h => (h hnI).elim)
      intro j _ hjn
      have hzj : z ∉ tsupport (scaledInput F j) :=
        fun hs => Set.disjoint_left.mp (disjoint_disks hjn) (scaled_bump_support F j hs) hn
      rw [image_eq_zero_of_notMem_tsupport hzj, mul_zero]
    · rw [V.value_zero_off_disks (fun n hn => h ⟨n, hn⟩)]
      symm
      apply Finset.sum_eq_zero
      intro n _
      rw [image_eq_zero_of_notMem_tsupport (fun hn => h ⟨n, scaled_bump_support F n hn⟩), mul_zero]
  exact (hG.contDiffAt.congr_of_eventuallyEq hNear).contDiffWithinAt

/-- The value and both classical derivatives vanish at the accumulation point. -/
public theorem zero_jet_at_origin (V : GluedTorusJet F δ₀) :
    V.value 0 = 0 ∧ fderiv ℝ V.value 0 = 0 ∧ iteratedFDeriv ℝ 2 V.value 0 = 0 := by
  have h0 : (0 : Plane) ∈ Metric.ball 0 1 := Metric.mem_ball_self zero_lt_one
  have h0' : (0 : Plane) ∈ Metric.closedBall 0 1 := Metric.ball_subset_closedBall h0
  have hOff (n : ℕ) : (0 : Plane) ∉ disk n :=
    fun hn => zero_notMem_closedDisk n (Metric.ball_subset_closedBall hn)
  have hAt := V.zero_off_disks ⟨0, h0'⟩ hOff
  have hzG := congrArg (fun p : ℝ × Plane × DiskHessian => p.2.1) hAt
  have hzH := congrArg (fun p : ℝ × Plane × DiskHessian => p.2.2) hAt
  have hCompat : V.jet.1.Compatible := V.jet.2
  have hG : fderiv ℝ V.value 0 = 0 := by
    have h := ((hCompat.1 0 h0).1).fderiv
    change V.jet.1.2.1 ⟨0, h0'⟩ = 0 at hzG
    change fderiv ℝ V.value 0 = innerSL ℝ (V.jet.1.2.1 ⟨0, h0'⟩) at h
    rw [hzG, map_zero] at h
    exact h
  refine ⟨V.value_zero_off_disks hOff, hG, ?_⟩
  have hP : fderiv ℝ V.value =ᶠ[𝓝 (0 : Plane)]
      fun x => innerSL ℝ (diskFieldExtension V.jet.1.2.1 x) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds h0] with x hx
    exact ((hCompat.1 x hx).1).fderiv.trans
      (congrArg (innerSL ℝ) (diskFieldExtension_of_mem _ (Metric.ball_subset_closedBall hx))).symm
  change V.jet.1.2.2 ⟨0, h0'⟩ = 0 at hzH
  have hSecond := (hCompat.1 0 h0).2
  rw [hzH, map_zero] at hSecond
  let I : Plane →L[ℝ] Plane →L[ℝ] ℝ := innerSL ℝ
  have hSecond' := (I.hasFDerivAt.comp 0 hSecond).fderiv
  have hD : fderiv ℝ (fun x => innerSL ℝ (diskFieldExtension V.jet.1.2.1 x)) 0 = 0 := by
    change fderiv ℝ (I ∘ diskFieldExtension V.jet.1.2.1) 0 = 0
    rw [hSecond', ContinuousLinearMap.comp_zero]
  ext q
  rw [iteratedFDeriv_two_apply, hP.fderiv_eq, hD]
  simp

private theorem metricYY_eq_iteratedFDeriv {f : Plane → ℝ} (hf : ContDiff ℝ 2 f) (x : Plane) :
    WeakJet2.metricYY f x = iteratedFDeriv ℝ 2 f x (fun _ => WeakJet2.ey) := by
  have hP : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by decide)
  have hFirst : (fun y => lineDeriv ℝ f y WeakJet2.ey) =
      fun y => fderiv ℝ f y WeakJet2.ey :=
    funext fun y => (hf.differentiable (by decide) y).lineDeriv_eq_fderiv
  rw [WeakJet2.metricYY, hFirst, iteratedFDeriv_two_apply]
  exact (((ContinuousLinearMap.apply ℝ ℝ WeakJet2.ey).hasFDerivAt.comp x
    (hP.differentiable_one x).hasFDerivAt).hasLineDerivAt WeakJet2.ey).lineDeriv

/-- The yy source on a small disk has exactly the prescribed amplitude. -/
public theorem metricYY_on_disk (V : GluedTorusJet F δ₀) (n : ℕ) {x : Plane} (hx : x ∈ disk n) :
    WeakJet2.metricYY V.value x =
      amplitude δ₀ n * WeakJet2.metricYY (F.profile n) (scaledCoordinate n x) := by
  let g := fun y => amplitude δ₀ n * scaledInput F n y
  have hg : ContDiff ℝ 2 g := contDiff_const.mul ((scaledInput_smooth F n).of_le (by simp))
  have hNear : V.value =ᶠ[𝓝 x] g :=
    Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hx) (fun _ hy => V.value_eq_on_disk n hy)
  rw [metricYY_eq_iteratedFDeriv V.contDiff_two, metricYY_eq_iteratedFDeriv ((F.smooth n).of_le (by simp)),
    (hNear.iteratedFDeriv ℝ 2).eq_of_nhds]
  change iteratedFDeriv ℝ 2 ((amplitude δ₀ n : ℝ) • scaledInput F n) x (fun _ => WeakJet2.ey) = _
  rw [iteratedFDeriv_const_smul_apply (((scaledInput_smooth F n).of_le (by simp :
    (2 : ℕ∞ω) ≤ ∞)).contDiffAt), scaledInput_second]
  rfl
end GluedTorusJet
end C2Riemannian.TorusDiskGeometry
