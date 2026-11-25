module

public import C2Riemannian.PeriodicProfile
public import C2Riemannian.HessianAlgebra
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import C2Riemannian.WeakStarExtension
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Quantitative pairing with periodic phases (M20) -/

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped Topology Interval ContDiff NNReal

namespace C2Riemannian

/-- Oriented primitive based at the start of a period. -/
@[expose] public noncomputable def periodicPrimitive (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, f u

private theorem locallyIntegrable_of_measurable_norm_le {f : ℝ → ℝ}
    (hf : Measurable f) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) : LocallyIntegrable f volume :=
  locallyIntegrable_iff.mpr fun _ hk =>
    IntegrableOn.of_bound hk.measure_lt_top hf.aestronglyMeasurable M (Eventually.of_forall hM)

private theorem intervalIntegrable_of_measurable_norm_le {f : ℝ → ℝ}
    (hf : Measurable f) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) (a b : ℝ) :
    IntervalIntegrable f volume a b :=
  intervalIntegrable_iff.mpr ((locallyIntegrable_of_measurable_norm_le hf hM).integrableOn_isCompact
    isCompact_uIcc |>.mono_set Ioc_subset_Icc_self)

public theorem periodic_periodicPrimitive {f : ℝ → ℝ} (hf : Measurable f)
    (hp : Function.Periodic f 1) (hz : (∫ t in (0 : ℝ)..1, f t) = 0)
    {M : ℝ} (hb : ∀ t, ‖f t‖ ≤ M) :
    Function.Periodic (periodicPrimitive f) 1 := by
  intro t
  simpa only [periodicPrimitive, zero_add, hz, add_zero] using
    hp.intervalIntegral_add_eq_add 0 t (intervalIntegrable_of_measurable_norm_le hf hb)

public theorem norm_periodicPrimitive_le {f : ℝ → ℝ} (hf : Measurable f)
    (hp : Function.Periodic f 1) (hz : (∫ t in (0 : ℝ)..1, f t) = 0)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ t, ‖f t‖ ≤ M) (t : ℝ) :
    ‖periodicPrimitive f t‖ ≤ M := by
  have ht := (periodic_periodicPrimitive hf hp hz hb).sub_int_mul_eq (x := t) ⌊t⌋
  rw [mul_one] at ht
  change periodicPrimitive f (Int.fract t) = periodicPrimitive f t at ht
  rw [← ht]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := Int.fract t) (f := f) (C := M) (fun x _ => hb x)
  rw [sub_zero, abs_of_nonneg (Int.fract_nonneg _)] at h
  exact h.trans (mul_le_of_le_one_right hM (Int.fract_lt_one _).le)

public theorem lipschitz_periodicPrimitive {f : ℝ → ℝ} (hf : Measurable f)
    {M : ℝ≥0} (hb : ∀ t, ‖f t‖ ≤ (M : ℝ)) :
    LipschitzWith M (periodicPrimitive f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, periodicPrimitive, periodicPrimitive,
    intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_of_measurable_norm_le hf hb 0 x)
      (intervalIntegrable_of_measurable_norm_le hf hb 0 y), Real.dist_eq]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := y) (b := x) (f := f) (C := (M : ℝ)) (fun t _ => hb t)
  exact h

/-- The normal-direction pairing estimate from the bounded primitive and
Lipschitz integration by parts. The scalar projection must pull back null sets to null sets. -/
public theorem periodic_directional_pairing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
    {f : ℝ → ℝ} (hf : Measurable f) (hp : Function.Periodic f 1)
    (hz : (∫ t in (0 : ℝ)..1, f t) = 0)
    (M : ℝ≥0) (hb : ∀ t, ‖f t‖ ≤ (M : ℝ))
    (A : E →L[ℝ] ℝ) (hA : QuasiMeasurePreserving A volume volume)
    (v : E) (hv : 0 < A v) {ψ : E → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) :
    |∫ x, f (A x) * ψ x| ≤ (M : ℝ) / A v * ∫ x, |fderiv ℝ ψ x v| := by
  let B := periodicPrimitive f
  have hBLip := (lipschitz_periodicPrimitive hf hb).comp A.lipschitzWith
  obtain ⟨D, hψLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hψ (by simp)
  have hparts := hBLip.integral_lineDeriv_mul_eq (μ := volume) hψLip hc v
  have hDer : ∀ᵐ x ∂(volume : Measure E), lineDeriv ℝ (B ∘ A) x v = A v * f (A x) := by
    have hae := LocallyIntegrable.ae_hasDerivAt_integral (locallyIntegrable_of_measurable_norm_le hf hb)
    filter_upwards [hA.ae hae] with x hx
    have hxB : HasDerivAt B (f (A x)) (A x) := hx 0
    have h := (hxB.hasFDerivAt.comp x A.hasFDerivAt).hasLineDerivAt v
    exact h.lineDeriv
  have hLeft :
      (∫ x, lineDeriv ℝ (B ∘ A) x v * ψ x) = A v * ∫ x, f (A x) * ψ x := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hDer] with x hx
    rw [hx, mul_assoc]
  have hRight :
      (∫ x, lineDeriv ℝ ψ x (-v) * (B ∘ A) x) = -(∫ x, B (A x) * fderiv ℝ ψ x v) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with x
    have hD := (hψ.differentiable (by simp) x).lineDeriv_eq_fderiv (v := -v)
    rw [hD, map_neg, neg_mul, Function.comp_apply, mul_comm (fderiv ℝ ψ x v)]
  rw [hLeft, hRight] at hparts
  have hDcont : Continuous (fun x => fderiv ℝ ψ x v) :=
    (ContinuousLinearMap.apply ℝ ℝ v).continuous.comp (hψ.continuous_fderiv (by simp))
  have hDint : Integrable (fun x => fderiv ℝ ψ x v) :=
    hDcont.integrable_of_hasCompactSupport (HasCompactSupport.fderiv_apply ℝ hc v)
  have hBound (x : E) : ‖B (A x)‖ ≤ (M : ℝ) :=
    norm_periodicPrimitive_le hf hp hz M.coe_nonneg hb (A x)
  have hPair : |∫ x, B (A x) * fderiv ℝ ψ x v| ≤ (M : ℝ) * ∫ x, |fderiv ℝ ψ x v| := by
    rw [← Real.norm_eq_abs, ← integral_const_mul]
    apply norm_integral_le_of_norm_le (hDint.norm.const_mul (M : ℝ))
    filter_upwards with x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hBound x) (norm_nonneg _)
  have hAbs := congrArg abs hparts
  rw [abs_mul, abs_of_pos hv, abs_neg] at hAbs
  have hScaled := hAbs.le.trans hPair
  calc
    _ ≤ ((M : ℝ) * ∫ x, |fderiv ℝ ψ x v|) / A v :=
      (le_div_iff₀ hv).mpr (by rwa [mul_comm])
    _ = _ := by rw [div_mul_eq_mul_div]

public theorem periodic_pairing_real
    {f : ℝ → ℝ} (hf : Measurable f) (hp : Function.Periodic f 1)
    (hz : (∫ t in (0 : ℝ)..1, f t) = 0)
    (M : ℝ≥0) (hb : ∀ t, ‖f t‖ ≤ (M : ℝ))
    {lam : ℝ} (hlam : 0 < lam) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    |∫ x, f (lam * x) * ψ x| ≤ (M : ℝ) / lam * ∫ x, |deriv ψ x| := by
  let A : ℝ →L[ℝ] ℝ := lam • ContinuousLinearMap.id ℝ ℝ
  have hA : QuasiMeasurePreserving A volume volume :=
    Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) hlam.ne'
  have h := periodic_directional_pairing hf hp hz M hb A hA 1 (by simpa [A] using hlam) hψ hc
  simpa only [A, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    mul_one, fderiv_apply_one_eq_deriv] using h

/-- The periodic indicator of a phase interval, taking the values zero and one. -/
@[expose] public noncomputable def phaseIndicator (I : Set ℝ) : ℝ → ℝ :=
  (periodicPhase I).indicator (fun _ => 1)

public theorem measurable_phaseIndicator {I : Set ℝ} (hI : IsOpen I) :
    Measurable (phaseIndicator I) :=
  measurable_const.indicator (isOpen_periodicPhase hI).measurableSet

public theorem phaseIndicator_mem_Icc (I : Set ℝ) (t : ℝ) :
    phaseIndicator I t ∈ Icc (0 : ℝ) 1 := by
  by_cases h : t ∈ periodicPhase I <;> simp [phaseIndicator, h]

public theorem periodic_phaseIndicator (I : Set ℝ) : Function.Periodic (phaseIndicator I) 1 := by
  intro t
  have h := mem_periodicPhase_add_one_iff I t
  by_cases ht : t ∈ periodicPhase I
  · rw [phaseIndicator, indicator_of_mem (h.mpr ht), indicator_of_mem ht]
  · rw [phaseIndicator, indicator_of_notMem (fun hn => ht (h.mp hn)), indicator_of_notMem ht]

public theorem mem_periodicPhase_iff_of_mem_Icc {I : Set ℝ} (hI : I ⊆ Ioo (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : t ∈ periodicPhase I ↔ t ∈ I := by
  constructor
  · rintro ⟨k, hk⟩
    have hs := hI hk
    have hk₁ : -1 < (k : ℝ) := by linarith only [ht.1, hs.2]
    have hk₂ : (k : ℝ) < 1 := by linarith only [ht.2, hs.1]
    have hz₁ : (-1 : ℤ) < k := by exact_mod_cast hk₁
    have hz₂ : k < 1 := by exact_mod_cast hk₂
    have hz : k = 0 := by omega
    simpa only [hz, Int.cast_zero, sub_zero] using hk
  · intro h
    exact ⟨0, by simpa only [Int.cast_zero, sub_zero] using h⟩

public theorem integral_phaseIndicator {I : Set ℝ} (hI : IsOpen I) (hsub : I ⊆ Ioo (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1, phaseIndicator I t) = volume.real I := by
  have heq : EqOn (phaseIndicator I) (I.indicator (fun _ => (1 : ℝ))) (uIcc 0 1) := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have h := mem_periodicPhase_iff_of_mem_Icc hsub ht
    by_cases hmem : t ∈ I
    · rw [phaseIndicator, indicator_of_mem (h.mpr hmem), indicator_of_mem hmem]
    · rw [phaseIndicator, indicator_of_notMem (fun hn => hmem (h.mp hn)), indicator_of_notMem hmem]
  have hIoc : I ⊆ Ioc (0 : ℝ) 1 := fun t ht => ⟨(hsub ht).1, (hsub ht).2.le⟩
  rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_of_le zero_le_one,
    setIntegral_indicator hI.measurableSet, inter_eq_right.mpr hIoc, setIntegral_const]
  simp

/-- The centered amplitude-two indicator used in the two phase estimates. -/
@[expose] public noncomputable def centeredPhase (I : Set ℝ) (t : ℝ) : ℝ :=
  2 * phaseIndicator I t - 2 * volume.real I

public theorem centeredPhase_properties {I : Set ℝ} (hI : IsOpen I)
    (hsub : I ⊆ Ioo (0 : ℝ) 1) :
    Measurable (centeredPhase I) ∧ Function.Periodic (centeredPhase I) 1 ∧
      (∫ t in (0 : ℝ)..1, centeredPhase I t) = 0 ∧
      ∀ t, ‖centeredPhase I t‖ ≤ (2 : ℝ) := by
  have hm₀ : 0 ≤ volume.real I := ENNReal.toReal_nonneg
  have hμ : (volume : Measure ℝ) I ≤ volume (Ioo (0 : ℝ) 1) := measure_mono hsub
  have hm₁ : volume.real I ≤ 1 := by
    rw [Real.volume_Ioo, sub_zero] at hμ
    simpa [Measure.real] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hμ
  have hI_meas := measurable_phaseIndicator hI
  have hI_cont t : ‖phaseIndicator I t‖ ≤ (1 : ℝ) := by
    rw [Real.norm_of_nonneg (phaseIndicator_mem_Icc I t).1]
    exact (phaseIndicator_mem_Icc I t).2
  refine ⟨(measurable_const.mul hI_meas).sub measurable_const, ?_, ?_, ?_⟩
  · intro t
    simp only [centeredPhase, periodic_phaseIndicator I t]
  · unfold centeredPhase
    rw [intervalIntegral.integral_sub
      ((intervalIntegrable_of_measurable_norm_le hI_meas hI_cont 0 1).const_mul 2)
      intervalIntegrable_const, intervalIntegral.integral_const_mul,
      integral_phaseIndicator hI hsub, intervalIntegral.integral_const]
    simp
  · intro t
    rw [Real.norm_eq_abs, centeredPhase]
    apply abs_le.mpr
    have ht := phaseIndicator_mem_Icc I t
    exact ⟨by linarith only [hm₁, ht.1], by linarith only [hm₀, ht.2]⟩

public theorem centeredPhase_pairing_real {I : Set ℝ} (hI : IsOpen I)
    (hsub : I ⊆ Ioo (0 : ℝ) 1) {lam : ℝ} (hlam : 0 < lam)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    |∫ x, centeredPhase I (lam * x) * ψ x| ≤ 2 / lam * ∫ x, |deriv ψ x| := by
  obtain ⟨hm, hp, hz, hb⟩ := centeredPhase_properties hI hsub
  exact periodic_pairing_real hm hp hz 2 hb hlam hψ hc

private theorem quasiMeasurePreserving_unit_inner {u : Plane} (hu : ‖u‖ = 1) :
    QuasiMeasurePreserving (fun x : Plane => inner ℝ u x) volume volume := by
  classical
  have horth : Orthonormal ℝ ((↑) : ({u} : Set Plane) → Plane) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : (i : Plane) = u := mem_singleton_iff.mp i.2
    have hj : (j : Plane) = u := mem_singleton_iff.mp j.2
    have hij : i = j := Subtype.ext (hi.trans hj.symm)
    simp only [hj, hij, ite_true, real_inner_self_eq_norm_sq, hu, one_pow]
  obtain ⟨s, b, hsub, hb⟩ := horth.exists_orthonormalBasis_extension
  let i : s := ⟨u, hsub (mem_singleton u)⟩
  have hi : b i = u := congrFun hb i
  have hm := (Measure.quasiMeasurePreserving_eval (fun _ : s => (volume : Measure ℝ)) i).comp
    ((PiLp.volume_preserving_ofLp (ι := s)).comp b.repr.measurePreserving).quasiMeasurePreserving
  convert hm using 1
  ext x
  change inner ℝ u x = b.repr x i
  rw [b.repr_apply_apply, hi]

/-- The centered planar phase estimate for any nonzero normal and positive frequency. -/
public theorem phase_centered_test_bound {I : Set ℝ} (hI : IsOpen I)
    (hsub : I ⊆ Ioo (0 : ℝ) 1) {n : Plane} (hn : n ≠ 0) {L : ℝ} (hL : 0 < L)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    |∫ x, centeredPhase I (L * inner ℝ n x) * ψ x| ≤
      2 / (L * ‖n‖) * ∫ x, |fderiv ℝ ψ x (‖n‖⁻¹ • n)| := by
  let u : Plane := ‖n‖⁻¹ • n
  let k : ℝ := L * ‖n‖
  have hn₀ : 0 < ‖n‖ := norm_pos_iff.mpr hn
  have hk : 0 < k := mul_pos hL hn₀
  have hu : ‖u‖ = 1 := by
    rw [show ‖u‖ = ‖‖n‖⁻¹‖ * ‖n‖ from norm_smul _ _,
      Real.norm_of_nonneg (inv_nonneg.mpr hn₀.le), inv_mul_cancel₀ hn₀.ne']
  let A : Plane →L[ℝ] ℝ := k • innerSL ℝ u
  have hAu : A u = k := by
    simp only [A, smul_apply, innerSL_apply_apply, real_inner_self_eq_norm_sq,
      hu, one_pow, smul_eq_mul, mul_one]
  have hA : QuasiMeasurePreserving A volume volume :=
    (Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) hk.ne').comp
      (quasiMeasurePreserving_unit_inner hu)
  have hscale (x : Plane) : A x = L * inner ℝ n x := by
    simp only [A, smul_apply, innerSL_apply_apply, smul_eq_mul, k, u,
      real_inner_smul_left, ← mul_assoc, mul_inv_cancel_right₀ hn₀.ne']
  obtain ⟨hm, hp, hz, hb⟩ := centeredPhase_properties hI hsub
  have h := periodic_directional_pairing hm hp hz 2 hb A hA u (by simpa only [hAu] using hk) hψ hc
  rw [hAu] at h
  simpa only [hscale, NNReal.coe_ofNat] using h

/-- Centered phase pairings converge to zero on any open test domain.
The widths may vary because the estimate uses a uniform indicator bound. -/
public theorem phase_centered_weakstar
    {Ω : Set Plane} (hΩ : IsOpen Ω) {n : Plane} (hn : n ≠ 0)
    (I : ℕ → Set ℝ) (hI : ∀ j, IsOpen (I j))
    (hsub : ∀ j, I j ⊆ Ioo (0 : ℝ) 1)
    (L : ℕ → ℝ) (hL₀ : ∀ j, 0 < L j) (hL : Tendsto L atTop atTop)
    {γ : Plane → ℝ} (hγ : Integrable γ (volume.restrict Ω)) :
    Tendsto (fun j => ∫ x in Ω, centeredPhase (I j) (L j * inner ℝ n x) * γ x) atTop (𝓝 0) := by
  let U (j : ℕ) (x : Plane) := centeredPhase (I j) (L j * inner ℝ n x)
  have hProp j := centeredPhase_properties (hI j) (hsub j)
  have hMeas j : AEStronglyMeasurable (U j) (volume.restrict Ω) :=
    ((hProp j).1.comp (measurable_const.mul (innerSL ℝ n).continuous.measurable)).aestronglyMeasurable
  have hTests (ψ : Plane → ℝ) (hc : HasCompactSupport ψ) (hψ : ContDiff ℝ ∞ ψ)
      (hSupp : tsupport ψ ⊆ Ω) :
      Tendsto (fun j => ∫ x in Ω, U j x * ψ x) atTop (𝓝 (∫ _ in Ω, (0 : ℝ))) := by
    have hFreq : Tendsto (fun j => L j * ‖n‖) atTop atTop :=
      hL.atTop_mul_const (norm_pos_iff.mpr hn) 
    have hInv : Tendsto (fun j => (2 : ℝ) / (L j * ‖n‖)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hFreq
    simp only [integral_zero]
    have hT := hInv.mul_const (∫ x, |fderiv ℝ ψ x (‖n‖⁻¹ • n)|)
    rw [zero_mul] at hT
    refine squeeze_zero_norm (fun j => ?_) hT
    rw [Real.norm_eq_abs, setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact phase_centered_test_bound (hI j) (hsub j) hn (hL₀ j) (hψ.of_le (by simp)) hc
    · intro x hx
      rw [image_eq_zero_of_notMem_tsupport fun hm => hx (hSupp hm), mul_zero]
  have h := weakStar_of_interior_smooth_tests (ν := volume) hΩ
    (U := U) (u := fun _ => (0 : ℝ)) 2 (by norm_num)
    hMeas aestronglyMeasurable_zero
    (fun j => Eventually.of_forall fun x => (hProp j).2.2.2 _) (by simp) 
    (fun ψ hc hψ hs => by simpa only [zero_mul] using hTests ψ hc hψ hs) hγ
  simpa only [U, zero_mul, integral_zero] using h

/-- The two phase intervals, indexed by a Boolean sign. -/
@[expose] public def phaseInterval (positive : Bool) (e : ℝ) : Set ℝ :=
  if positive then positivePhase e else negativePhase e

public theorem isOpen_phaseInterval (positive : Bool) (e : ℝ) :
    IsOpen (phaseInterval positive e) := by
  cases positive <;> exact isOpen_Ioo

public theorem phaseInterval_subset {e : ℝ} (he : 0 < e) (positive : Bool) :
    phaseInterval positive e ⊆ Ioo (0 : ℝ) 1 := by
  cases positive
  · intro t ht
    change 1 / 2 + e < t ∧ t < 1 - e at ht
    exact ⟨by linarith only [ht.1, he], by linarith only [ht.2, he]⟩
  · intro t ht
    change e < t ∧ t < 1 / 2 - e at ht
    exact ⟨by linarith only [ht.1, he], by linarith only [ht.2, he]⟩

public theorem real_volume_phaseInterval {e : ℝ} (he : e ≤ 1 / 16) (positive : Bool) :
    volume.real (phaseInterval positive e) = 1 / 2 - 2 * e := by
  have h : 0 ≤ (1 / 2 : ℝ) - 2 * e := by linarith only [he]
  cases positive
  · change volume.real (negativePhase e) = _
    rw [Measure.real, volume_negativePhase, ENNReal.toReal_ofReal h]
  · change volume.real (positivePhase e) = _
    rw [Measure.real, volume_positivePhase, ENNReal.toReal_ofReal h]

/-- Two times the phase indicator converges weak-star to one as the
transition width tends to zero and the frequency tends to infinity. -/
public theorem phase_weakstar_half {Ω : Set Plane} (hΩ : IsOpen Ω)
    {n : Plane} (hn : n ≠ 0) (positive : Bool)
    (e L : ℕ → ℝ) (he₀ : ∀ j, 0 < e j) (he₁ : ∀ j, e j ≤ 1 / 16)
    (he : Tendsto e atTop (𝓝 0)) (hL₀ : ∀ j, 0 < L j) (hL : Tendsto L atTop atTop)
    {γ : Plane → ℝ} (hγ : Integrable γ (volume.restrict Ω)) :
    Tendsto (fun j => ∫ x in Ω, 2 * phaseIndicator (phaseInterval positive (e j))
      (L j * inner ℝ n x) * γ x) atTop (𝓝 (∫ x in Ω, γ x)) := by
  let I (j : ℕ) := phaseInterval positive (e j)
  have hI j : IsOpen (I j) := isOpen_phaseInterval positive (e j)
  have hSub j : I j ⊆ Ioo (0 : ℝ) 1 := phaseInterval_subset (he₀ j) positive
  have hCentered := phase_centered_weakstar hΩ hn I hI hSub L hL₀ hL hγ
  have hMean : Tendsto (fun j => 2 * volume.real (I j)) atTop (𝓝 1) := by
    have he' := (he.const_mul (4 : ℝ)).const_sub 1
    convert he' using 1
    · ext j
      rw [show I j = phaseInterval positive (e j) from rfl, real_volume_phaseInterval (he₁ j)]
      ring
    · norm_num
  have hPair (j : ℕ) :
      (∫ x in Ω, 2 * phaseIndicator (I j) (L j * inner ℝ n x) * γ x) =
        (∫ x in Ω, centeredPhase (I j) (L j * inner ℝ n x) * γ x) +
          (2 * volume.real (I j)) * ∫ x in Ω, γ x := by
    have hc := centeredPhase_properties (hI j) (hSub j)
    have hm : Measurable (fun x : Plane => centeredPhase (I j) (L j * inner ℝ n x)) :=
      hc.1.comp (measurable_const.mul (innerSL ℝ n).continuous.measurable)
    rw [← integral_const_mul, ← integral_add
      (hγ.bdd_mul hm.aestronglyMeasurable (Eventually.of_forall fun x => hc.2.2.2 _))
      (hγ.const_mul _)]
    apply integral_congr_ae
    filter_upwards with x
    simp only [centeredPhase]
    ring
  convert hCentered.add (hMean.mul_const (∫ x in Ω, γ x)) using 1
  · funext j
    exact hPair j
  · simp

/-- The uncentered estimate on an open test domain, including the exact loss
from the phase mass. -/
public theorem phase_test_bound {Ω : Set Plane} {n : Plane} (hn : n ≠ 0)
    {L e : ℝ} (hL : 0 < L) (he₀ : 0 < e) (he₁ : e ≤ 1 / 16)
    (positive : Bool) {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) (hSupp : tsupport ψ ⊆ Ω) :
    |∫ x in Ω, (2 * phaseIndicator (phaseInterval positive e) (L * inner ℝ n x) - 1) * ψ x| ≤
      2 / (L * ‖n‖) * (∫ x in Ω, |fderiv ℝ ψ x (‖n‖⁻¹ • n)|) +
        4 * e * ∫ x in Ω, |ψ x| := by
  let I := phaseInterval positive e
  let z (x : Plane) := L * inner ℝ n x
  have hO := isOpen_phaseInterval positive e
  have hS := phaseInterval_subset he₀ positive
  have hCenter := phase_centered_test_bound hO hS hn hL hψ hc
  have hS₁ : ∀ x, x ∉ Ω → centeredPhase I (z x) * ψ x = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport fun h => hx (hSupp h), mul_zero]
  have hS₂ : ∀ x, x ∉ Ω → |fderiv ℝ ψ x (‖n‖⁻¹ • n)| = 0 := by
    intro x hx
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hSupp h)), zero_apply, abs_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hS₁,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hS₂] at hCenter
  have hC := centeredPhase_properties hO hS
  have hMeas : AEStronglyMeasurable (fun x => centeredPhase I (z x)) (volume.restrict Ω) :=
    (hC.1.comp (measurable_const.mul (innerSL ℝ n).continuous.measurable)).aestronglyMeasurable
  have hψInt : Integrable ψ (volume.restrict Ω) :=
    (hψ.continuous.integrable_of_hasCompactSupport hc).restrict
  have hEq :
      (∫ x in Ω, (2 * phaseIndicator I (z x) - 1) * ψ x) =
        (∫ x in Ω, centeredPhase I (z x) * ψ x) + (-4 * e) * ∫ x in Ω, ψ x := by
    rw [← integral_const_mul, ← integral_add
      (hψInt.bdd_mul hMeas (Eventually.of_forall fun x => hC.2.2.2 _)) (hψInt.const_mul _)]
    apply integral_congr_ae
    filter_upwards with x
    simp only [centeredPhase, I, real_volume_phaseInterval he₁]
    ring
  have hAbs : |(-4 * e : ℝ) * ∫ x in Ω, ψ x| ≤ 4 * e * ∫ x in Ω, |ψ x| := by
    have hcoef : |(-4 * e : ℝ)| = 4 * e := by
      rw [show -4 * e = -(4 * e) by ring, abs_neg, abs_of_nonneg (by positivity)]
    rw [abs_mul, hcoef]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := volume.restrict Ω) ψ
  change |∫ x in Ω, (2 * phaseIndicator I (z x) - 1) * ψ x| ≤ _
  rw [hEq]
  exact (abs_add_le _ _).trans (add_le_add hCenter hAbs)

/-- The unassigned phase mass tends to zero on each compact set. -/
public theorem phase_remainder_local {n : Plane} (hn : n ≠ 0)
    (e L : ℕ → ℝ) (he₀ : ∀ j, 0 < e j) (he₁ : ∀ j, e j ≤ 1 / 16)
    (he : Tendsto e atTop (𝓝 0)) (hL₀ : ∀ j, 0 < L j) (hL : Tendsto L atTop atTop)
    {C : Set Plane} (hC : IsCompact C) :
    Tendsto (fun j => ∫ x in C,
      1 - phaseIndicator (positivePhase (e j)) (L j * inner ℝ n x) -
        phaseIndicator (negativePhase (e j)) (L j * inner ℝ n x)) atTop (𝓝 0) := by
  let F (positive : Bool) (j : ℕ) (x : Plane) :=
    phaseIndicator (phaseInterval positive (e j)) (L j * inner ℝ n x)
  let γ : Plane → ℝ := C.indicator (fun _ => 1)
  have hγ : Integrable γ (volume.restrict Set.univ) := by
    rw [Measure.restrict_univ, integrable_indicator_iff hC.measurableSet]
    exact integrableOn_const hC.measure_lt_top.ne
  have hLim (positive : Bool) :
      Tendsto (fun j => ∫ x in C, F positive j x) atTop (𝓝 (volume.real C / 2)) := by
    have h := phase_weakstar_half isOpen_univ hn positive e L he₀ he₁ he hL₀ hL hγ
    have h₁ (j : ℕ) :
        (∫ x in (Set.univ : Set Plane), 2 * F positive j x * γ x) =
          2 * ∫ x in C, F positive j x := by
      rw [Measure.restrict_univ, ← integral_const_mul, ← integral_indicator hC.measurableSet]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ C <;> simp [γ, hx]
    have h₂ : (∫ x in (Set.univ : Set Plane), γ x) = volume.real C := by
      rw [Measure.restrict_univ, integral_indicator hC.measurableSet, setIntegral_const]
      simp
    change Tendsto (fun j => ∫ x in (Set.univ : Set Plane), 2 * F positive j x * γ x) atTop
      (𝓝 (∫ x in (Set.univ : Set Plane), γ x)) at h
    simp only [h₁, h₂] at h
    convert h.div_const (2 : ℝ) using 1
    ext j
    ring
  have hInt (positive : Bool) (j : ℕ) :
      Integrable (F positive j) (volume.restrict C) := by
    apply IntegrableOn.of_bound hC.measure_lt_top
      (((measurable_phaseIndicator (isOpen_phaseInterval positive (e j))).comp
        (measurable_const.mul (innerSL ℝ n).continuous.measurable)).aestronglyMeasurable) 1
    filter_upwards with x
    have hx := phaseIndicator_mem_Icc (phaseInterval positive (e j)) (L j * inner ℝ n x)
    exact (Real.norm_of_nonneg hx.1).trans_le hx.2
  have hEq (j : ℕ) :
      (∫ x in C, 1 - F true j x - F false j x) =
        volume.real C - (∫ x in C, F true j x) - (∫ x in C, F false j x) := by
    let _ : IsFiniteMeasure (volume.restrict C) := isFiniteMeasure_restrict.mpr hC.measure_lt_top.ne
    have hConst : Integrable (fun _ : Plane => (1 : ℝ)) (volume.restrict C) := integrable_const 1
    have hsub : (∫ x in C, 1 - F true j x) =
        (∫ _ in C, (1 : ℝ)) - ∫ x in C, F true j x :=
      integral_sub hConst (hInt true j)
    calc
      _ = (∫ x in C, 1 - F true j x) - ∫ x in C, F false j x :=
        integral_sub (hConst.sub (hInt true j)) (hInt false j)
      _ = _ := by rw [hsub, setIntegral_const]; simp
  have h := ((tendsto_const_nhds (x := volume.real C)).sub (hLim true)).sub (hLim false)
  change Tendsto (fun j => ∫ x in C, 1 - F true j x - F false j x) atTop (𝓝 0)
  rw [show (0 : ℝ) = volume.real C - volume.real C / 2 - volume.real C / 2 by ring]
  simpa only [hEq] using h

end C2Riemannian
