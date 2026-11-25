module

public import C2Riemannian.PhaseEquidistribution
public import C2Riemannian.QuantitativeCutoff
public import C2Riemannian.OscillatoryPotential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Exact child platforms and their area estimates (M23) -/

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped ContDiff Topology BigOperators

namespace C2Riemannian

/-- A child is the intersection of the cutoff core interior with one oscillatory phase. -/
@[expose] public def childPlatform (U : Set Plane) (positive : Bool) (e L : ℝ) (n : Plane) : Set Plane :=
  U ∩ (fun x => L * inner ℝ n x) ⁻¹' periodicPhase (phaseInterval positive e)

@[expose] public def childSign (positive : Bool) : ℝ :=
  if positive then 1 else -1

public theorem childPlatform_open {U : Set Plane} (hU : IsOpen U) (positive : Bool)
    (e L : ℝ) (n : Plane) : IsOpen (childPlatform U positive e L n) :=
  hU.inter ((isOpen_periodicPhase (isOpen_phaseInterval positive e)).preimage
    (continuous_const.mul (innerSL ℝ n).continuous))

public theorem childPlatform_disjoint (U : Set Plane) {e : ℝ} (he : 0 < e) (he' : e ≤ 1 / 16)
    (L : ℝ) (n : Plane) :
    Disjoint (childPlatform U true e L n) (childPlatform U false e L n) := by
  exact Set.disjoint_left.mpr fun _ hx hy =>
    Set.disjoint_left.mp (disjoint_periodicPhases he he') hx.2 hy.2

public theorem childPlatform_closure_in_parent {P : Set Plane}
    (E : InteriorExhaustion P) (k : ℕ) (positive : Bool) (e L : ℝ) (n : Plane) :
    IsCompact (closure (childPlatform (parentInterior P E.radius k) positive e L n)) ∧
      closure (childPlatform (parentInterior P E.radius k) positive e L n) ⊆ P := by
  have hSub : closure (childPlatform (parentInterior P E.radius k) positive e L n) ⊆
      closure (parentInterior P E.radius k) := closure_mono inter_subset_left
  exact ⟨(E.closure_compact k).of_isClosed_subset isClosed_closure hSub,
    hSub.trans ((E.closure_subset k).trans ((E.core_subset (k + 1)).trans (E.inside (k + 1))))⟩

private theorem integral_phase_eq_child_area {U : Set Plane} (positive : Bool) (e L : ℝ) (n : Plane) :
    (∫ x in U, phaseIndicator (phaseInterval positive e) (L * inner ℝ n x)) =
      volume.real (childPlatform U positive e L n) := by
  let S : Set Plane := (fun x => L * inner ℝ n x) ⁻¹' periodicPhase (phaseInterval positive e)
  have hS : IsOpen S := (isOpen_periodicPhase (isOpen_phaseInterval positive e)).preimage
    (continuous_const.mul (innerSL ℝ n).continuous)
  have hEq : (fun x => phaseIndicator (phaseInterval positive e) (L * inner ℝ n x)) =
      S.indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : L * inner ℝ n x ∈ periodicPhase (phaseInterval positive e)
    · rw [phaseIndicator, indicator_of_mem hx, indicator_of_mem (show x ∈ S from hx)]
    · rw [phaseIndicator, indicator_of_notMem hx, indicator_of_notMem (show x ∉ S from hx)]
  rw [hEq, setIntegral_indicator hS.measurableSet, setIntegral_const]
  simp [childPlatform, S]

/-- The measure of either phase converges at fixed width along any diverging frequency. -/
public theorem child_area_tendsto {U : Set Plane} (hU : IsOpen U) (hFinite : volume U ≠ ⊤)
    {n : Plane} (hn : n ≠ 0) {e : ℝ} (he : 0 < e) (he' : e ≤ 1 / 16)
    (positive : Bool) (L : ℕ → ℝ) (hL₀ : ∀ j, 0 < L j) (hL : Tendsto L atTop atTop) :
    Tendsto (fun j => volume.real (childPlatform U positive e (L j) n)) atTop
      (𝓝 ((1 / 2 - 2 * e) * volume.real U)) := by
  have hγ : Integrable (fun _ : Plane => (1 : ℝ)) (volume.restrict U) := integrableOn_const hFinite
  have h := phase_centered_weakstar hU hn (fun _ => phaseInterval positive e)
    (fun _ => isOpen_phaseInterval positive e) (fun _ => phaseInterval_subset he positive)
    L hL₀ hL hγ
  have hEq (j : ℕ) :
      (∫ x in U, centeredPhase (phaseInterval positive e) (L j * inner ℝ n x) * 1) =
        2 * volume.real (childPlatform U positive e (L j) n) - 2 * ((1 / 2 - 2 * e) * volume.real U) := by
    let J (x : Plane) := phaseIndicator (phaseInterval positive e) (L j * inner ℝ n x)
    have hJ : Integrable J (volume.restrict U) := by
      apply IntegrableOn.of_bound hFinite.lt_top
        (((measurable_phaseIndicator (isOpen_phaseInterval positive e)).comp
          (measurable_const.mul (innerSL ℝ n).continuous.measurable)).aestronglyMeasurable) 1
      filter_upwards with x
      have hx := phaseIndicator_mem_Icc (phaseInterval positive e) (L j * inner ℝ n x)
      exact (Real.norm_of_nonneg hx.1).trans_le hx.2
    let _ : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hFinite
    simp only [mul_one, centeredPhase, real_volume_phaseInterval he']
    rw [integral_sub (hJ.const_mul (2 : ℝ)) (integrable_const _), integral_const_mul,
      integral_phase_eq_child_area, setIntegral_const]
    simp only [smul_eq_mul]
    ring
  simp only [hEq] at h
  have hRearranged := (h.div_const 2).add_const ((1 / 2 - 2 * e) * volume.real U)
  convert hRearranged using 1
  · ext j
    ring
  · norm_num

/-- Both children pass a fixed-width area tolerance at every sufficiently large
integer frequency. This is the eventual constraint used by frequency selection. -/
public theorem eventually_child_area_nat {U : Set Plane} (hU : IsOpen U)
    (hFinite : volume U ≠ ⊤) {n : Plane} (hn : n ≠ 0) {e η : ℝ}
    (he : 0 < e) (he' : e ≤ 1 / 16) (hη : 0 < η) :
    ∀ᶠ L : ℕ in atTop, ∀ positive : Bool,
      |volume.real (childPlatform U positive e L n) - (1 / 2 - 2 * e) * volume.real U| < η := by
  let freq (j : ℕ) := max (1 : ℝ) (j : ℝ)
  have hf : Tendsto freq atTop atTop :=
    tendsto_atTop_mono (fun j => le_max_right (1 : ℝ) (j : ℝ)) tendsto_natCast_atTop_atTop
  have hfreq (j : ℕ) : 0 < freq j := zero_lt_one.trans_le (le_max_left _ _)
  have hphase (b : Bool) : ∀ᶠ j in atTop,
      |volume.real (childPlatform U b e (freq j) n) - (1 / 2 - 2 * e) * volume.real U| < η := by
    have h := child_area_tendsto hU hFinite hn he he' b freq hfreq hf
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp h η hη
  filter_upwards [eventually_ge_atTop (1 : ℕ), hphase true, hphase false] with j hj hP hN
  have hf' : freq j = (j : ℝ) := max_eq_right (by exact_mod_cast hj)
  rw [hf'] at hP hN
  intro b
  cases b
  · exact hN
  · exact hP

/-- Above any prescribed threshold one integer frequency satisfies the
fixed-width area acceptance condition for both children. -/
public theorem exists_child_area_frequency {U : Set Plane} (hU : IsOpen U)
    (hFinite : volume U ≠ ⊤) {n : Plane} (hn : n ≠ 0) {e η : ℝ}
    (he : 0 < e) (he' : e ≤ 1 / 16) (hη : 0 < η) (threshold : ℕ) :
    ∃ L : ℕ, threshold < L ∧ ∀ positive : Bool,
      |volume.real (childPlatform U positive e L n) - (1 / 2 - 2 * e) * volume.real U| < η := by
  obtain ⟨L, hL, hPass⟩ :=
    ((eventually_ge_atTop (threshold + 1)).and
      (eventually_child_area_nat hU hFinite hn he he' hη)).exists
  exact ⟨L, hL, hPass⟩

/-- The three scalar acceptance inequalities imply both half-area estimates,
the remainder estimate, and nonemptiness. -/
public theorem child_platform_measure {P U : Set Plane} (hU : IsOpen U)
    (hUP : U ⊆ P) (hPfinite : volume P ≠ ⊤) (hPpos : 0 < volume.real P)
    {δ e L : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (he : 0 < e) (he' : e ≤ 1 / 16) (heδ : 2 * e < δ / 4) (n : Plane)
    (hInner : volume.real (P \ U) < δ * volume.real P / 4)
    (hFreq : ∀ positive : Bool,
      |volume.real (childPlatform U positive e L n) - (1 / 2 - 2 * e) * volume.real U| <
        δ * volume.real P / 4) :
    (∀ positive : Bool,
      |volume.real (childPlatform U positive e L n) - volume.real P / 2| < δ * volume.real P) ∧
    volume.real (P \ (childPlatform U true e L n ∪ childPlatform U false e L n)) ≤ 2 * δ * volume.real P ∧
    ∀ positive : Bool, (childPlatform U positive e L n).Nonempty := by
  have hUle := measureReal_mono hUP hPfinite
  have hInner' : volume.real P - volume.real U < δ * volume.real P / 4 := by
    rwa [measureReal_sdiff hUP hU.measurableSet hPfinite] at hInner
  have hm : 0 ≤ (1 / 2 : ℝ) - 2 * e := by linarith only [he']
  have hM : (1 / 2 : ℝ) - 2 * e ≤ 1 / 2 := by linarith only [he]
  have hHalf (positive : Bool) :
      |volume.real (childPlatform U positive e L n) - volume.real P / 2| < δ * volume.real P := by
    let p := volume.real P
    let u := volume.real U
    let c := volume.real (childPlatform U positive e L n)
    let m := (1 / 2 : ℝ) - 2 * e
    have hLow : 0 ≤ p - u := sub_nonneg.mpr hUle
    have hTerm : m * (p - u) ≤ δ * p / 4 := by
      calc
        _ ≤ 1 * (p - u) := mul_le_mul_of_nonneg_right (hM.trans (by norm_num)) hLow
        _ ≤ _ := by simpa only [one_mul] using hInner'.le
    have hWidth : 2 * e * p < δ * p / 4 := by
      have h := mul_lt_mul_of_pos_right heδ hPpos
      linarith only [h]
    change |c - p / 2| < δ * p
    calc
      |c - p / 2| ≤ |c - m * u| + m * (p - u) + 2 * e * p := by
        rw [show c - p / 2 = (c - m * u) + -(m * (p - u)) + -(2 * e * p) by
          dsimp [m]
          ring]
        have hmw : 0 ≤ m * (p - u) := mul_nonneg hm hLow
        have hew : 0 ≤ 2 * e * p := by positivity
        have hFirst : |(c - m * u) + -(m * (p - u))| ≤ |c - m * u| + m * (p - u) := by
          simpa only [abs_neg, abs_of_nonneg hmw] using abs_add_le (c - m * u) (-(m * (p - u)))
        have hSecond := abs_add_le ((c - m * u) + -(m * (p - u))) (-(2 * e * p))
        rw [abs_neg, abs_of_nonneg hew] at hSecond
        exact hSecond.trans (add_le_add_left hFirst _)
      _ < δ * p := by
        have hPos : 0 < δ * p := mul_pos hδ hPpos
        linarith only [hFreq positive, hTerm, hWidth, hPos]
  have hSub (positive : Bool) : childPlatform U positive e L n ⊆ P :=
    inter_subset_left.trans hUP
  have hOp (positive : Bool) : IsOpen (childPlatform U positive e L n) :=
    childPlatform_open hU positive e L n
  have hFinite (positive : Bool) : volume (childPlatform U positive e L n) ≠ ⊤ :=
    measure_ne_top_of_subset (hSub positive) hPfinite
  have hLow (positive : Bool) :
      volume.real P / 2 - δ * volume.real P < volume.real (childPlatform U positive e L n) := by
    have h := (abs_lt.mp (hHalf positive)).1
    linarith only [h]
  refine ⟨hHalf, ?_, fun positive => ?_⟩
  · rw [measureReal_sdiff (union_subset (hSub true) (hSub false))
      ((hOp true).union (hOp false)).measurableSet hPfinite,
      measureReal_union (childPlatform_disjoint U he he' L n) (hOp false).measurableSet
        (hFinite true) (hFinite false)]
    linarith only [hLow true, hLow false]
  · by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hzero := hLow positive
    rw [h, measureReal_empty] at hzero
    nlinarith only [hzero, mul_pos (sub_pos.mpr hδ') hPpos]

/-- Addition of an oscillatory potential gives the signed exact top derivative
on the child platform, at any order used for the potential. -/
public theorem exact_child_jets {P : Set Plane} (hBound : Bornology.IsBounded P)
    (E : InteriorExhaustion P) (k j : ℕ) {e L : ℝ} (he : 0 < e) (he' : e ≤ 1 / 16)
    (hL : L ≠ 0) (n : Plane) (γ : ℝ) (positive : Bool)
    {W : Plane → ℝ} (hW : ContDiff ℝ ∞ W) {x : Plane}
    (hx : x ∈ childPlatform (parentInterior P E.radius k) positive e L n) (v : Fin j → Plane) :
    iteratedFDeriv ℝ j
        (W + oscillatoryPotential j (quantitativeCutoff P E.radius k) e γ L (innerSL ℝ n)) x v =
      iteratedFDeriv ℝ j W x v + childSign positive * γ * ∏ i, inner ℝ n (v i) := by
  obtain ⟨V, hV, hVsub, hOne⟩ := quantitativeCutoff_one_near_closure hBound E k
  have hχ : ∀ᶠ y in 𝓝 x, quantitativeCutoff P E.radius k y = 1 :=
    Filter.eventually_of_mem (hV.mem_nhds (hVsub (subset_closure hx.1))) hOne
  have hχSmooth := (quantitativeCutoff_spec hBound E k).1
  have hOsc := contDiff_oscillatoryPotential j hχSmooth e γ L (innerSL ℝ n)
  have hPhase : smooth_square_wave e ((L • innerSL ℝ n) x) = childSign positive := by
    have hz : (L • innerSL ℝ n) x = L * inner ℝ n x := by simp
    rw [hz]
    cases positive
    · exact smooth_square_wave_eq_neg_one_periodicPhase he he' hx.2
    · exact smooth_square_wave_eq_one_periodicPhase he he' hx.2
  rw [iteratedFDeriv_add_apply (hW.contDiffAt.of_le (by simp)) (hOsc.contDiffAt.of_le (by simp))]
  change iteratedFDeriv ℝ j W x v +
    iteratedFDeriv ℝ j (oscillatoryPotential j (quantitativeCutoff P E.radius k) e γ L (innerSL ℝ n)) x v = _
  rw [iteratedFDeriv_oscillatoryPotential_on_plateau j e γ L hL (innerSL ℝ n) hχ v, hPhase]
  simp only [innerSL_apply_apply, mul_comm γ]

end C2Riemannian
