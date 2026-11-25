module

public import C2Riemannian.SmoothCutoff
public import C2Riemannian.HessianAlgebra
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace C2Riemannian

/-- Equation (11)'s geometric scales, starting at one quarter of the fixed inner radius. -/
@[expose] public noncomputable def interiorRadius (r : ℝ) (k : ℕ) : ℝ :=
  (r / 4) * (1 / 4) ^ k

@[expose] public noncomputable def parentCore (P : Set Plane) (r : ℝ) (k : ℕ) : Set Plane :=
  {x | 3 * interiorRadius r k ≤ Metric.infDist x Pᶜ}

@[expose] public noncomputable def parentInterior (P : Set Plane) (r : ℝ) (k : ℕ) : Set Plane :=
  {x | 2 * interiorRadius r k < Metric.infDist x Pᶜ}

public theorem interiorRadius_pos {r : ℝ} (hr : 0 < r) (k : ℕ) :
    0 < interiorRadius r k := by
  unfold interiorRadius
  positivity

public theorem interiorRadius_succ (r : ℝ) (k : ℕ) :
    interiorRadius r (k + 1) = interiorRadius r k / 4 := by
  simp only [interiorRadius, pow_succ]
  ring

public theorem interiorRadius_antitone {r : ℝ} (hr : 0 < r) : Antitone (interiorRadius r) := by
  apply antitone_nat_of_succ_le
  intro k
  rw [interiorRadius_succ]
  linarith only [interiorRadius_pos hr k]

public theorem interiorRadius_tendsto (r : ℝ) : Tendsto (interiorRadius r) atTop (𝓝 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    (show (1 / 4 : ℝ) < 1 by norm_num)
  change Tendsto (fun k : ℕ => (r / 4) * (1 / 4) ^ k) atTop (𝓝 0)
  simpa only [mul_zero] using h.const_mul (r / 4)

public theorem parentInterior_open (P : Set Plane) (r : ℝ) (k : ℕ) :
    IsOpen (parentInterior P r k) :=
  isOpen_lt continuous_const (Metric.continuous_infDist_pt Pᶜ)

private theorem positive_infDist_mem {P : Set Plane} {x : Plane}
    (hx : 0 < Metric.infDist x Pᶜ) : x ∈ P := by
  by_contra h
  rw [Metric.infDist_zero_of_mem (show x ∈ Pᶜ from h)] at hx
  exact (lt_irrefl 0) hx

private theorem compact_distance_superlevel {P : Set Plane} (hBound : Bornology.IsBounded P)
    {d : ℝ} (hd : 0 < d) : IsCompact {x | d ≤ Metric.infDist x Pᶜ} := by
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_le continuous_const (Metric.continuous_infDist_pt Pᶜ)) (hBound.subset ?_)
  exact fun _ hx => positive_infDist_mem (hd.trans_le hx)

/-- Data of the interior exhaustion of a nonempty bounded planar platform. -/
public structure InteriorExhaustion (P : Set Plane) where
  center : Plane
  radius : ℝ
  radius_pos : 0 < radius
  inner_closedBall : Metric.closedBall center (4 * radius) ⊆ P
  inner_ball : ∀ k, Metric.ball center radius ⊆ parentInterior P radius k
  compact_core : ∀ k, IsCompact (parentCore P radius k)
  core_subset : ∀ k, parentCore P radius k ⊆ parentInterior P radius k
  closure_subset : ∀ k, closure (parentInterior P radius k) ⊆ parentCore P radius (k + 1)
  closure_compact : ∀ k, IsCompact (closure (parentInterior P radius k))
  inside : ∀ k, parentInterior P radius k ⊆ P
  eventually_contains_compact : ∀ C : Set Plane, C ⊆ P → IsCompact C →
    ∀ᶠ k in atTop, C ⊆ parentInterior P radius k
  iUnion_interior : (⋃ k, parentInterior P radius k) = P
  volume_pos : 0 < volume P
  volume_finite : volume P ≠ ∞
  volume_interior_tendsto : Tendsto (fun k => volume (parentInterior P radius k)) atTop (𝓝 (volume P))
  volume_remainder_tendsto : Tendsto (fun k => volume (P \ parentInterior P radius k)) atTop (𝓝 0)
  area_remainder_tendsto : Tendsto (fun k => (volume (P \ parentInterior P radius k)).toReal)
    atTop (𝓝 0)

/-- A bounded nonempty open platform has the nested distance exhaustion (11). -/
public theorem exhaust_parent {P : Set Plane} (hOpen : IsOpen P) (hP : P.Nonempty)
    (hBound : Bornology.IsBounded P) : Nonempty (InteriorExhaustion P) := by
  obtain ⟨z, hz⟩ := hP
  obtain ⟨δ, hδ, hBall⟩ := Metric.mem_nhds_iff.mp (hOpen.mem_nhds hz)
  let r := δ / 8
  have hr : 0 < r := div_pos hδ (by norm_num)
  have hInner : Metric.closedBall z (4 * r) ⊆ P :=
    (Metric.closedBall_subset_ball (by dsimp [r]; linarith only [hδ])).trans hBall
  have hCompl : Pᶜ.Nonempty := by
    by_contra h
    have hEq : P = univ := by
      rw [Set.not_nonempty_iff_eq_empty] at h
      apply eq_univ_of_forall
      intro x
      by_contra hx
      have hOutside : x ∈ Pᶜ := hx
      rw [h] at hOutside
      exact hOutside
    exact NormedSpace.unbounded_univ ℝ Plane (hEq ▸ hBound)
  have hInside (k : ℕ) : parentInterior P r k ⊆ P :=
    fun _ hx => positive_infDist_mem
      ((mul_pos (by norm_num : (0 : ℝ) < 2) (interiorRadius_pos hr k)).trans hx)
  have hCore (k : ℕ) : IsCompact (parentCore P r k) :=
    compact_distance_superlevel hBound (mul_pos (by norm_num) (interiorRadius_pos hr k))
  have hCoreSub (k : ℕ) : parentCore P r k ⊆ parentInterior P r k :=
    fun _ hx => (by linarith only [interiorRadius_pos hr k] :
      2 * interiorRadius r k < 3 * interiorRadius r k).trans_le hx
  have hClosureThreshold (k : ℕ) :
      closure (parentInterior P r k) ⊆ {x | 2 * interiorRadius r k ≤ Metric.infDist x Pᶜ} :=
    closure_minimal (fun x hx => show 2 * interiorRadius r k ≤ Metric.infDist x Pᶜ from
      (show 2 * interiorRadius r k < Metric.infDist x Pᶜ from hx).le)
      (isClosed_le continuous_const (Metric.continuous_infDist_pt Pᶜ))
  have hClosure (k : ℕ) : closure (parentInterior P r k) ⊆ parentCore P r (k + 1) := by
    intro x hx
    have hdx := hClosureThreshold k hx
    change 3 * interiorRadius r (k + 1) ≤ Metric.infDist x Pᶜ
    rw [interiorRadius_succ]
    change 2 * interiorRadius r k ≤ Metric.infDist x Pᶜ at hdx
    linarith only [hdx, interiorRadius_pos hr k]
  have hInnerBall (k : ℕ) : Metric.ball z r ⊆ parentInterior P r k := by
    intro x hx
    have hxDist : dist x z < r := Metric.mem_ball.mp hx
    have hDist : 4 * r - dist x z ≤ Metric.infDist x Pᶜ := by
      apply (Metric.le_infDist hCompl).mpr
      intro y hy
      have hyDist : 4 * r < dist y z := lt_of_not_ge fun hy' => hy (hInner hy')
      have hTriangle := dist_triangle y x z
      rw [dist_comm y x] at hTriangle
      linarith only [hTriangle, hyDist]
    have hSmall := interiorRadius_antitone hr (Nat.zero_le k)
    have hBase : interiorRadius r 0 = r / 4 := by simp [interiorRadius]
    rw [hBase] at hSmall
    change 2 * interiorRadius r k < Metric.infDist x Pᶜ
    linarith only [hSmall, hr, hxDist, hDist]
  have hEventually (C : Set Plane) (hSub : C ⊆ P) (hC : IsCompact C) :
      ∀ᶠ k in atTop, C ⊆ parentInterior P r k := by
    rcases C.eq_empty_or_nonempty with rfl | hCnonempty
    · exact Eventually.of_forall fun _ => empty_subset _
    obtain ⟨x, hx, hMin⟩ := hC.exists_isMinOn hCnonempty
      (Metric.continuous_infDist_pt Pᶜ).continuousOn
    have hdx : 0 < Metric.infDist x Pᶜ :=
      (hOpen.isClosed_compl.notMem_iff_infDist_pos hCompl).mp (by simpa using hSub hx)
    have hScales : Tendsto (fun k => 2 * interiorRadius r k) atTop (𝓝 0) := by
      simpa only [mul_zero] using (interiorRadius_tendsto r).const_mul 2
    have hEventuallySmall : ∀ᶠ k in atTop, 2 * interiorRadius r k < Metric.infDist x Pᶜ :=
      hScales (eventually_lt_nhds hdx)
    exact hEventuallySmall.mono fun k hk y hy => hk.trans_le (hMin hy)
  have hUnion : (⋃ k, parentInterior P r k) = P := by
    refine Subset.antisymm (iUnion_subset hInside) fun x hx => ?_
    have hTail := hEventually {x} (singleton_subset_iff.mpr hx) isCompact_singleton
    obtain ⟨k, hk⟩ := hTail.exists
    exact mem_iUnion.mpr ⟨k, hk (mem_singleton x)⟩
  have hMono : Monotone (parentInterior P r) := by
    intro i j hij x hx
    exact (mul_le_mul_of_nonneg_left (interiorRadius_antitone hr hij) (by norm_num : (0 : ℝ) ≤ 2)).trans_lt hx
  have hFinite : volume P ≠ ∞ := hBound.measure_lt_top.ne
  have hUp := tendsto_measure_iUnion_atTop (μ := (volume : Measure Plane)) hMono
  rw [hUnion] at hUp
  have hInter : (⋂ k, P \ parentInterior P r k) = ∅ := by
    rw [← sdiff_iUnion, hUnion, Set.sdiff_self]
  have hDown := tendsto_measure_iInter_atTop (μ := (volume : Measure Plane))
    (fun k => (hOpen.measurableSet.diff (parentInterior_open P r k).measurableSet).nullMeasurableSet)
    (show Antitone (fun k => P \ parentInterior P r k) from fun i j hij => sdiff_subset_sdiff_right (hMono hij))
    ⟨0, ne_top_of_le_ne_top hFinite (measure_mono sdiff_subset)⟩
  rw [hInter, measure_empty] at hDown
  refine ⟨⟨z, r, hr, hInner, hInnerBall, hCore, hCoreSub, hClosure,
    fun k => (hCore (k + 1)).of_isClosed_subset isClosed_closure (hClosure k),
    hInside, hEventually, hUnion, hOpen.measure_pos volume ⟨z, hz⟩, hFinite, hUp, hDown, ?_⟩⟩
  simpa only [Function.comp_def, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hDown

/-- A smooth compact cutoff for an exact interior scale. It equals one on
a neighborhood of the closed superlevel at (7r_k/4), and its support lies
inside the open superlevel at (5r_k/4). -/
public theorem cutoff_one_on_inner {P : Set Plane} (hBound : Bornology.IsBounded P)
    (E : InteriorExhaustion P) (k : ℕ) :
    ∃ (χ : Plane → ℝ) (V : Set Plane),
      ContDiff ℝ (↑(⊤ : ℕ∞)) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ {x | 5 * interiorRadius E.radius k / 4 < Metric.infDist x Pᶜ} ∧
      (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧ IsOpen V ∧
      {x | 7 * interiorRadius E.radius k / 4 ≤ Metric.infDist x Pᶜ} ⊆ V ∧
      closure (parentInterior P E.radius k) ⊆ V ∧ (∀ x ∈ V, χ x = 1) ∧
      ∃ A : ℝ, 0 ≤ A ∧ ∀ i ≤ 4, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ A := by
  let t := interiorRadius E.radius k
  have ht : 0 < t := interiorRadius_pos E.radius_pos k
  obtain ⟨χ, V, hχ, hCompact, hSupp, hRange, hOpen, hV, hOne⟩ :=
    exists_compact_inner_cutoff
      (compact_distance_superlevel hBound (show 0 < 7 * t / 4 by positivity))
      (isOpen_lt (f := fun _ : Plane => 5 * t / 4) continuous_const (Metric.continuous_infDist_pt Pᶜ))
      (show {x | 7 * t / 4 ≤ Metric.infDist x Pᶜ} ⊆ {x | 5 * t / 4 < Metric.infDist x Pᶜ}
        from fun _ hx => (by linarith only [ht] : 5 * t / 4 < 7 * t / 4).trans_le hx)
  refine ⟨χ, V, hχ, hCompact, hSupp, hRange, hOpen, hV, ?_, hOne,
    hCompact.exists_bound_iteratedFDeriv hχ 4⟩
  refine (closure_minimal ?_
    (isClosed_le (f := fun _ : Plane => 7 * t / 4) continuous_const (Metric.continuous_infDist_pt Pᶜ))).trans hV
  intro x hx
  change 2 * t < Metric.infDist x Pᶜ at hx
  change 7 * t / 4 ≤ Metric.infDist x Pᶜ
  linarith only [hx, ht]

end C2Riemannian
