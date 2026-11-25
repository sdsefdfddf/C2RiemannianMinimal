module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Smooth periodic square waves and their centered primitives (M18–M19) -/

set_option autoImplicit false

open Set MeasureTheory
open scoped Interval ContDiff

namespace C2Riemannian

/-- Smooth odd truncation with exact values one and minus one outside the transition interval. -/
@[expose] public noncomputable def smoothSign (x : ℝ) : ℝ :=
  Real.smoothTransition x - Real.smoothTransition (-x)

public theorem contDiff_smoothSign : ContDiff ℝ ∞ smoothSign :=
  Real.smoothTransition.contDiff.sub (Real.smoothTransition.contDiff.comp contDiff_neg)

@[simp] public theorem smoothSign_neg (x : ℝ) : smoothSign (-x) = -smoothSign x := by
  simp only [smoothSign, neg_neg, neg_sub]

public theorem abs_smoothSign_le_one (x : ℝ) : |smoothSign x| ≤ 1 := by
  apply abs_le.mpr
  unfold smoothSign
  exact ⟨by linarith only [Real.smoothTransition.nonneg x, Real.smoothTransition.le_one (-x)],
    by linarith only [Real.smoothTransition.le_one x, Real.smoothTransition.nonneg (-x)]⟩

public theorem smoothSign_eq_one {x : ℝ} (h : 1 ≤ x) : smoothSign x = 1 := by
  rw [smoothSign, Real.smoothTransition.one_of_one_le h,
    Real.smoothTransition.zero_of_nonpos (by linarith only [h]), sub_zero]

/-- Unit-period profile with transition-width parameter `e`. -/
@[expose] public noncomputable def smooth_square_wave (e t : ℝ) : ℝ :=
  smoothSign (Real.sin (2 * Real.pi * t) / Real.sin (2 * Real.pi * e))

@[expose] public def positivePhase (e : ℝ) : Set ℝ := Ioo e (1 / 2 - e)

@[expose] public def negativePhase (e : ℝ) : Set ℝ := Ioo (1 / 2 + e) (1 - e)

/-- All integer translates of one phase interval. -/
@[expose] public def periodicPhase (I : Set ℝ) : Set ℝ :=
  {t | ∃ k : ℤ, t - (k : ℝ) ∈ I}

public theorem contDiff_smooth_square_wave (e : ℝ) : ContDiff ℝ ∞ (smooth_square_wave e) :=
  contDiff_smoothSign.comp
    ((Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).div_const _)

public theorem abs_smooth_square_wave_le_one (e t : ℝ) : |smooth_square_wave e t| ≤ 1 :=
  abs_smoothSign_le_one _

public theorem smooth_square_wave_add_half (e t : ℝ) :
    smooth_square_wave e (t + 1 / 2) = -smooth_square_wave e t := by
  unfold smooth_square_wave
  rw [show 2 * Real.pi * (t + 1 / 2) = 2 * Real.pi * t + Real.pi by ring,
    Real.sin_add_pi, neg_div, smoothSign_neg]

public theorem periodic_smooth_square_wave (e : ℝ) : Function.Periodic (smooth_square_wave e) 1 := by
  intro t
  rw [show t + (1 : ℝ) = (t + 1 / 2) + 1 / 2 by ring,
    smooth_square_wave_add_half, smooth_square_wave_add_half, neg_neg]

/-- The two half-period integrals cancel exactly. -/
public theorem integral_smooth_square_wave_eq_zero (e : ℝ) :
    (∫ t in (0 : ℝ)..1, smooth_square_wave e t) = 0 := by
  have hc := (contDiff_smooth_square_wave e).continuous
  have hShift :
      (∫ t in (0 : ℝ)..(1 / 2 : ℝ), smooth_square_wave e (t + 1 / 2)) =
        ∫ t in (1 / 2 : ℝ)..1, smooth_square_wave e t := by
    rw [intervalIntegral.integral_comp_add_right]
    norm_num
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 (1 / 2)) (hc.intervalIntegrable (1 / 2) 1),
    ← hShift]
  simp only [smooth_square_wave_add_half, intervalIntegral.integral_neg, add_neg_cancel]

public theorem smooth_square_wave_eq_one {e t : ℝ}
    (he : 0 < e) (he' : e ≤ 1 / 16) (ht : t ∈ positivePhase e) :
    smooth_square_wave e t = 1 := by
  change e < t ∧ t < 1 / 2 - e at ht
  let p := Real.pi
  have hp : 0 < p := Real.pi_pos
  have heAngle : 0 < 2 * p * e := mul_pos (mul_pos (by norm_num) hp) he
  have heUpper : 2 * p * e ≤ p / 2 := by nlinarith only [hp, he', mul_nonneg hp.le (sub_nonneg.mpr he')]
  have heSin : 0 < Real.sin (2 * p * e) :=
    Real.sin_pos_of_pos_of_lt_pi heAngle (heUpper.trans_lt (half_lt_self hp))
  have hminAngle (u : ℝ) (hu₁ : 2 * p * e ≤ u) (hu₂ : u ≤ p / 2) :
      Real.sin (2 * p * e) ≤ Real.sin u :=
    Real.strictMonoOn_sin.monotoneOn ⟨by linarith only [heAngle, hp], heUpper⟩
      ⟨by linarith only [hu₁, heAngle, hp], hu₂⟩ hu₁
  have hsin : Real.sin (2 * p * e) ≤ Real.sin (2 * p * t) := by
    by_cases ht₀ : 2 * p * t ≤ p / 2
    · exact hminAngle _ (mul_le_mul_of_nonneg_left ht.1.le (by positivity)) ht₀
    · have htu : 2 * p * e ≤ p - 2 * p * t := by
        have h := mul_le_mul_of_nonneg_left ht.2.le (show 0 ≤ 2 * p by positivity)
        linarith only [h]
      rw [← Real.sin_pi_sub (2 * p * t)]
      exact hminAngle _ htu (by linarith only [lt_of_not_ge ht₀])
  exact smoothSign_eq_one ((one_le_div heSin).mpr hsin)

public theorem smooth_square_wave_eq_neg_one {e t : ℝ}
    (he : 0 < e) (he' : e ≤ 1 / 16) (ht : t ∈ negativePhase e) :
    smooth_square_wave e t = -1 := by
  change 1 / 2 + e < t ∧ t < 1 - e at ht
  have hu : t - 1 / 2 ∈ positivePhase e := ⟨by linarith only [ht.1], by linarith only [ht.2]⟩
  have h := smooth_square_wave_add_half e (t - 1 / 2)
  rw [sub_add_cancel, smooth_square_wave_eq_one he he' hu] at h
  exact h

public theorem smooth_square_wave_eq_one_periodicPhase {e t : ℝ}
    (he : 0 < e) (he' : e ≤ 1 / 16) (ht : t ∈ periodicPhase (positivePhase e)) :
    smooth_square_wave e t = 1 := by
  obtain ⟨k, hk⟩ := ht
  have hp := (periodic_smooth_square_wave e).sub_int_mul_eq (x := t) k
  rw [mul_one] at hp
  exact hp.symm.trans (smooth_square_wave_eq_one he he' hk)

public theorem smooth_square_wave_eq_neg_one_periodicPhase {e t : ℝ}
    (he : 0 < e) (he' : e ≤ 1 / 16) (ht : t ∈ periodicPhase (negativePhase e)) :
    smooth_square_wave e t = -1 := by
  obtain ⟨k, hk⟩ := ht
  have hp := (periodic_smooth_square_wave e).sub_int_mul_eq (x := t) k
  rw [mul_one] at hp
  exact hp.symm.trans (smooth_square_wave_eq_neg_one he he' hk)

public theorem isOpen_periodicPhase {I : Set ℝ} (hI : IsOpen I) :
    IsOpen (periodicPhase I) := by
  have h : periodicPhase I = ⋃ k : ℤ, (fun t : ℝ => t - (k : ℝ)) ⁻¹' I := by
    ext t
    constructor
    · rintro ⟨k, hk⟩
      exact mem_iUnion.mpr ⟨k, hk⟩
    · intro ht
      obtain ⟨k, hk⟩ := mem_iUnion.mp ht
      exact ⟨k, hk⟩
  rw [h]
  exact isOpen_iUnion fun k => hI.preimage (continuous_id.sub continuous_const)

public theorem mem_periodicPhase_add_one_iff (I : Set ℝ) (t : ℝ) :
    t + 1 ∈ periodicPhase I ↔ t ∈ periodicPhase I := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k - 1, ?_⟩
    convert hk using 1
    push_cast
    ring
  · rintro ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    convert hk using 1
    push_cast
    ring

public theorem disjoint_periodicPhases {e : ℝ} (he : 0 < e) (he' : e ≤ 1 / 16) :
    Disjoint (periodicPhase (positivePhase e)) (periodicPhase (negativePhase e)) := by
  refine Set.disjoint_left.mpr fun t hp hm => ?_
  have h := (smooth_square_wave_eq_one_periodicPhase he he' hp).symm.trans
    (smooth_square_wave_eq_neg_one_periodicPhase he he' hm)
  norm_num at h

public theorem volume_positivePhase (e : ℝ) :
    volume (positivePhase e) = ENNReal.ofReal (1 / 2 - 2 * e) := by
  rw [positivePhase, Real.volume_Ioo]
  congr 1
  ring

public theorem volume_negativePhase (e : ℝ) :
    volume (negativePhase e) = ENNReal.ofReal (1 / 2 - 2 * e) := by
  rw [negativePhase, Real.volume_Ioo]
  congr 1
  ring

/-- The oriented integral primitive, with its average over one period subtracted. -/
@[expose] public noncomputable def meanZeroPrimitive (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..t, f u) - ∫ s in (0 : ℝ)..1, ∫ u in (0 : ℝ)..s, f u

public theorem hasDerivAt_meanZeroPrimitive {f : ℝ → ℝ} (hf : Continuous f) (t : ℝ) :
    HasDerivAt (meanZeroPrimitive f) (f t) t :=
  (intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 t)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt).sub_const _

public theorem deriv_meanZeroPrimitive {f : ℝ → ℝ} (hf : Continuous f) :
    deriv (meanZeroPrimitive f) = f :=
  funext fun t => (hasDerivAt_meanZeroPrimitive hf t).deriv

public theorem contDiff_meanZeroPrimitive {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (meanZeroPrimitive f) := by
  refine contDiff_infty_iff_deriv.mpr ⟨fun t => (hasDerivAt_meanZeroPrimitive hf.continuous t).differentiableAt, ?_⟩
  rw [deriv_meanZeroPrimitive hf.continuous]
  exact hf

public theorem periodic_meanZeroPrimitive {f : ℝ → ℝ} (hf : Continuous f)
    (hp : Function.Periodic f 1) (hzero : (∫ t in (0 : ℝ)..1, f t) = 0) :
    Function.Periodic (meanZeroPrimitive f) 1 := by
  intro t
  have h := hp.intervalIntegral_add_eq_add 0 t (fun a b => hf.intervalIntegrable a b)
  simp only [zero_add, hzero, add_zero] at h
  simp only [meanZeroPrimitive, h]

public theorem integral_meanZeroPrimitive {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ t in (0 : ℝ)..1, meanZeroPrimitive f t) = 0 := by
  have hB : Continuous (fun t : ℝ => ∫ x in (0 : ℝ)..t, f x) :=
    (intervalIntegral.differentiable_integral_of_continuous hf).continuous
  unfold meanZeroPrimitive
  rw [intervalIntegral.integral_sub (hB.intervalIntegrable 0 1) (intervalIntegrable_const),
    intervalIntegral.integral_const]
  simp

public theorem abs_meanZeroPrimitive_le {f : ℝ → ℝ} (hf : Continuous f)
    (hp : Function.Periodic f 1) (hzero : (∫ t in (0 : ℝ)..1, f t) = 0)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ t, |f t| ≤ M) (t : ℝ) :
    |meanZeroPrimitive f t| ≤ 2 * M := by
  let B (s : ℝ) := ∫ u in (0 : ℝ)..s, f u
  have hB (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : |B s| ≤ M := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := s) (C := M) (f := f) (fun u _ => by simpa only [Real.norm_eq_abs] using hb u)
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hs.1] at h
    exact h.trans (mul_le_of_le_one_right hM hs.2)
  have hMean : |∫ s in (0 : ℝ)..1, B s| ≤ M := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := 1) (C := M) (f := B) (fun s hs => by
        rw [Real.norm_eq_abs]
        rw [uIoc_of_le zero_le_one] at hs
        exact hB s ⟨hs.1.le, hs.2⟩)
    simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using h
  have ht : Int.fract t ∈ Icc (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have hp' := (periodic_meanZeroPrimitive hf hp hzero).sub_int_mul_eq (x := t) ⌊t⌋
  rw [mul_one] at hp'
  change meanZeroPrimitive f (Int.fract t) = meanZeroPrimitive f t at hp'
  rw [← hp']
  calc
    |meanZeroPrimitive f (Int.fract t)| ≤ |B (Int.fract t)| + |∫ s in (0 : ℝ)..1, B s| := abs_sub _ _
    _ ≤ M + M := add_le_add (hB _ ht) hMean
    _ = 2 * M := (two_mul M).symm

/-- The (j)-th iterated mean-zero primitive of the same profile. -/
@[expose] public noncomputable def profilePrimitive (e : ℝ) : ℕ → ℝ → ℝ
  | 0 => smooth_square_wave e
  | j + 1 => meanZeroPrimitive (profilePrimitive e j)

public theorem profilePrimitive_properties (e : ℝ) (j : ℕ) :
    ContDiff ℝ ∞ (profilePrimitive e j) ∧ Function.Periodic (profilePrimitive e j) 1 ∧
    (∫ t in (0 : ℝ)..1, profilePrimitive e j t) = 0 ∧
    ∀ t, |profilePrimitive e j t| ≤ (2 : ℝ) ^ j := by
  induction j with
  | zero =>
    exact ⟨contDiff_smooth_square_wave e, periodic_smooth_square_wave e,
      integral_smooth_square_wave_eq_zero e, fun t => by simpa only [profilePrimitive, pow_zero] using abs_smooth_square_wave_le_one e t⟩
  | succ j ih =>
    obtain ⟨hc, hp, hz, hb⟩ := ih
    refine ⟨contDiff_meanZeroPrimitive hc, periodic_meanZeroPrimitive hc.continuous hp hz,
      integral_meanZeroPrimitive hc.continuous, ?_⟩
    intro t
    simpa only [profilePrimitive, pow_succ', Nat.succ_eq_add_one] using
      abs_meanZeroPrimitive_le hc.continuous hp hz (by positivity) hb t

public theorem iteratedDeriv_profilePrimitive (e : ℝ) (i n : ℕ) :
    iteratedDeriv n (profilePrimitive e (n + i)) = profilePrimitive e i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_add, iteratedDeriv_succ', profilePrimitive,
      deriv_meanZeroPrimitive (profilePrimitive_properties e (n + i)).1.continuous]
    exact ih

/-- The second and fourth primitives both recover the same profile. -/
public theorem profile_primitives_2_4 (e : ℝ) :
    iteratedDeriv 2 (profilePrimitive e 2) = smooth_square_wave e ∧
    iteratedDeriv 4 (profilePrimitive e 4) = smooth_square_wave e :=
  ⟨iteratedDeriv_profilePrimitive e 0 2, iteratedDeriv_profilePrimitive e 0 4⟩

public theorem abs_iteratedDeriv_profilePrimitive_le (e : ℝ) {i j : ℕ}
    (h : i ≤ j) (t : ℝ) :
    |iteratedDeriv (j - i) (profilePrimitive e j) t| ≤ (2 : ℝ) ^ i := by
  have hd := iteratedDeriv_profilePrimitive e i (j - i)
  rw [Nat.sub_add_cancel h] at hd
  rw [hd]
  exact (profilePrimitive_properties e i).2.2.2 t

end C2Riemannian
