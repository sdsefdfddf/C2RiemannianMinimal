module

public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.VectorMeasure.AddContent

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped ENNReal

namespace C2Riemannian

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

/-- The (L^1) class of the indicator of a measurable set in a finite measure space. -/
@[expose] public noncomputable def pairingIndicator (μ : Measure α) [IsFiniteMeasure μ]
    {s : Set α} (hs : MeasurableSet s) : Lp ℝ 1 μ :=
  indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℝ)

private noncomputable def indicatorValue (J : Lp ℝ 1 μ →L[ℝ] ℝ) (s : Set α) : ℝ := by
  classical
  exact if hs : MeasurableSet s then J (pairingIndicator μ hs) else 0

private theorem indicatorValue_measurable (J : Lp ℝ 1 μ →L[ℝ] ℝ) {s : Set α}
    (hs : MeasurableSet s) : indicatorValue J s = J (pairingIndicator μ hs) := by
  classical
  simp [indicatorValue, hs]

private theorem indicatorValue_nonmeasurable (J : Lp ℝ 1 μ →L[ℝ] ℝ) {s : Set α}
    (hs : ¬ MeasurableSet s) : indicatorValue J s = 0 := by
  classical
  simp [indicatorValue, hs]

private theorem norm_pairingIndicator {s : Set α} (hs : MeasurableSet s) :
    ‖pairingIndicator μ hs‖ = μ.real s := by
  rw [pairingIndicator, norm_indicatorConstLp one_ne_zero ENNReal.one_ne_top]
  simp

private theorem norm_indicatorValue (J : Lp ℝ 1 μ →L[ℝ] ℝ) {s : Set α}
    (hs : MeasurableSet s) : ‖indicatorValue J s‖ ≤ ‖J‖ * μ.real s := by
  rw [indicatorValue_measurable J hs, ← norm_pairingIndicator hs]
  exact J.le_opNorm _

private theorem indicatorValue_disjoint_union (J : Lp ℝ 1 μ →L[ℝ] ℝ) {s t : Set α}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : Disjoint s t) :
    indicatorValue J (s ∪ t) = indicatorValue J s + indicatorValue J t := by
  rw [indicatorValue_measurable J (hs.union ht), indicatorValue_measurable J hs,
    indicatorValue_measurable J ht]
  unfold pairingIndicator
  rw [indicatorConstLp_disjoint_union hs ht (measure_ne_top μ s) (measure_ne_top μ t) hst, map_add]

private theorem enorm_indicatorValue_le (J : Lp ℝ 1 μ →L[ℝ] ℝ) (s : Set α) :
    ‖indicatorValue J s‖ₑ ≤ (ENNReal.ofReal ‖J‖ • μ) s := by
  by_cases hs : MeasurableSet s
  · rw [← ofReal_norm, Measure.smul_apply, smul_eq_mul,
      ← ENNReal.ofReal_toReal (measure_ne_top μ s),
      ← ENNReal.ofReal_mul (norm_nonneg J)]
    exact ENNReal.ofReal_le_ofReal (norm_indicatorValue J hs)
  · rw [indicatorValue_nonmeasurable J hs, enorm_zero]
    exact bot_le

/-- Indicator values of a bounded (L^1) functional form a signed measure.
Finite additivity comes from disjoint indicator addition, and the domination by
the finite measure (|J|mu) supplies countable additivity. -/
public noncomputable def pairingSignedMeasure (J : Lp ℝ 1 μ →L[ℝ] ℝ) : SignedMeasure α := by
  have : IsFiniteMeasure (ENNReal.ofReal ‖J‖ • μ) := μ.smul_finite ENNReal.ofReal_ne_top
  exact VectorMeasure.of_additive_of_le_measure (indicatorValue J) (enorm_indicatorValue_le J)
    (fun _ _ => indicatorValue_disjoint_union J) (fun _ => indicatorValue_nonmeasurable J)

/-- A bounded functional recovers its signed measure on each measurable set. -/
public theorem pairingSignedMeasure_apply (J : Lp ℝ 1 μ →L[ℝ] ℝ) {s : Set α}
    (hs : MeasurableSet s) :
    pairingSignedMeasure J s = J (pairingIndicator μ hs) :=
  indicatorValue_measurable J hs

/-- The signed measure is absolutely continuous with respect to the (L^1) base measure. -/
public theorem pairingSignedMeasure_ac (J : Lp ℝ 1 μ →L[ℝ] ℝ) :
    pairingSignedMeasure J ≪ᵥ μ.toENNRealVectorMeasure := by
  apply VectorMeasure.AbsolutelyContinuous.mk
  intro s hs hz
  rw [Measure.toENNRealVectorMeasure_apply_measurable hs] at hz
  have h := norm_indicatorValue J hs
  rw [measureReal_def, hz, ENNReal.toReal_zero, mul_zero] at h
  exact norm_le_zero_iff.mp h

private theorem integral_mul_pairingIndicator {g : α → ℝ} {s : Set α}
    (hs : MeasurableSet s) :
    (∫ x, pairingIndicator μ hs x * g x ∂μ) = ∫ x in s, g x ∂μ := by
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [indicatorConstLp_coeFn (p := 1) (hs := hs)
    (hμs := measure_ne_top μ s) (c := (1 : ℝ))] with x hx
  change pairingIndicator μ hs x = s.indicator (fun _ => (1 : ℝ)) x at hx
  rw [hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

private theorem indicatorConstLp_eq_smul_pairingIndicator {s : Set α}
    (hs : MeasurableSet s) (c : ℝ) :
    indicatorConstLp 1 hs (measure_ne_top μ s) c = c • pairingIndicator μ hs := by
  ext1
  filter_upwards [indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := measure_ne_top μ s) (c := c),
    Lp.coeFn_smul c (pairingIndicator μ hs),
    indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := measure_ne_top μ s) (c := (1 : ℝ))]
    with x h₁ h₂ h₃
  change pairingIndicator μ hs x = s.indicator (fun _ => (1 : ℝ)) x at h₃
  rw [h₁, h₂]
  simp only [Pi.smul_apply, h₃]
  by_cases hx : x ∈ s <;> simp [hx]

/-- A real bounded (L^1) functional on a finite measure space is integration
against a measurable signed density whose essential bound is at most its operator norm. -/
public theorem exists_l1_pairing_density (J : Lp ℝ 1 μ →L[ℝ] ℝ) :
    ∃ g : α → ℝ, Measurable g ∧ (∀ᵐ x ∂μ, |g x| ≤ ‖J‖) ∧
      ∀ γ : Lp ℝ 1 μ, J γ = ∫ x, γ x * g x ∂μ := by
  let ν := pairingSignedMeasure J
  let g := ν.rnDeriv μ
  have hg : Measurable g := ν.measurable_rnDeriv μ
  have hgi : Integrable g μ := ν.integrable_rnDeriv μ
  have hRN : μ.withDensityᵥ g = ν := ν.withDensityᵥ_rnDeriv_eq μ (pairingSignedMeasure_ac J)
  have htest (s : Set α) (hs : MeasurableSet s) :
      (∫ x in s, g x ∂μ) = J (pairingIndicator μ hs) := by
    rw [← withDensityᵥ_apply hgi hs, hRN]
    exact pairingSignedMeasure_apply J hs
  have hb (s : Set α) (hs : MeasurableSet s) :
      |∫ x in s, g x ∂μ| ≤ ‖J‖ * μ.real s := by
    rw [htest s hs, ← Real.norm_eq_abs, ← indicatorValue_measurable J hs]
    exact norm_indicatorValue J hs
  have hu : g ≤ᵐ[μ] fun _ => ‖J‖ := by
    apply ae_le_of_forall_setIntegral_le hgi (integrable_const _)
    intro s hs _
    rw [setIntegral_const, smul_eq_mul, mul_comm (μ.real s)]
    exact (le_abs_self _).trans (hb s hs)
  have hl : (fun _ => -‖J‖) ≤ᵐ[μ] g := by
    apply ae_le_of_forall_setIntegral_le (integrable_const _) hgi
    intro s hs _
    rw [setIntegral_const, smul_eq_mul, mul_neg, mul_comm (μ.real s)]
    exact (abs_le.mp (hb s hs)).1
  have hbound : ∀ᵐ x ∂μ, |g x| ≤ ‖J‖ := by
    filter_upwards [hu, hl] with x hux hlx
    exact abs_le.mpr ⟨hlx, hux⟩
  have htop : MemLp g ∞ μ :=
    memLp_top_of_bound hgi.aestronglyMeasurable ‖J‖ (by simpa only [Real.norm_eq_abs] using hbound)
  let D : Lp ℝ ∞ μ := htop.toLp g
  let T : Lp ℝ 1 μ →L[ℝ] ℝ := (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ ∞ 1 D
  have hT (γ : Lp ℝ 1 μ) : T γ = ∫ x, γ x * g x ∂μ := by
    change (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ ∞ 1 D γ = _
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [htop.coeFn_toLp] with x hx
    change D x = g x at hx
    change D x * γ x = γ x * g x
    rw [hx, mul_comm]
  have hJT (γ : Lp ℝ 1 μ) : J γ = T γ := by
    induction γ using Lp.induction (hp_ne_top := ENNReal.one_ne_top) with
    | @indicatorConst c s hs hμs =>
      rw [Lp.simpleFunc.coe_indicatorConst, indicatorConstLp_eq_smul_pairingIndicator hs,
        map_smul, map_smul, hT, integral_mul_pairingIndicator hs, htest s hs]
    | add hf hg _ hf_eq hg_eq =>
      rw [map_add, map_add, hf_eq, hg_eq]
    | isClosed => exact isClosed_eq J.continuous T.continuous
  exact ⟨g, hg, hbound, fun γ => (hJT γ).trans (hT γ)⟩

/-- Bounded pairing densities agreeing on every (L^1) test coincide almost everywhere. -/
public theorem l1_pairing_density_ae_unique {J : Lp ℝ 1 μ →L[ℝ] ℝ}
    {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (h₁ : ∀ γ : Lp ℝ 1 μ, J γ = ∫ x, γ x * f x ∂μ)
    (h₂ : ∀ γ : Lp ℝ 1 μ, J γ = ∫ x, γ x * g x ∂μ) : f =ᵐ[μ] g := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq f g hf hg
  intro s hs _
  rw [← integral_mul_pairingIndicator hs, ← integral_mul_pairingIndicator hs,
    ← h₁ (pairingIndicator μ hs), ← h₂ (pairingIndicator μ hs)]

/-- Positivity on nonnegative (L^1) classes implies positivity of their representing density. -/
public theorem l1_pairing_density_ae_nonneg {J : Lp ℝ 1 μ →L[ℝ] ℝ} {g : α → ℝ}
    (hg : Integrable g μ) (hrep : ∀ γ : Lp ℝ 1 μ, J γ = ∫ x, γ x * g x ∂μ)
    (hpos : ∀ γ : Lp ℝ 1 μ, (∀ᵐ x ∂μ, 0 ≤ γ x) → 0 ≤ J γ) : 0 ≤ᵐ[μ] g := by
  apply ae_nonneg_of_forall_setIntegral_nonneg hg
  intro s hs _
  rw [← integral_mul_pairingIndicator hs, ← hrep (pairingIndicator μ hs)]
  apply hpos
  filter_upwards [indicatorConstLp_coeFn (p := 1) (hs := hs)
    (hμs := measure_ne_top μ s) (c := (1 : ℝ))] with x hx
  change pairingIndicator μ hs x = s.indicator (fun _ => (1 : ℝ)) x at hx
  rw [hx]
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

/-- When the functional is ordinary integration, its representing density equals one
almost everywhere. -/
public theorem l1_pairing_density_ae_one {J : Lp ℝ 1 μ →L[ℝ] ℝ} {g : α → ℝ}
    (hg : Integrable g μ) (hrep : ∀ γ : Lp ℝ 1 μ, J γ = ∫ x, γ x * g x ∂μ)
    (hunit : ∀ γ : Lp ℝ 1 μ, J γ = ∫ x, γ x ∂μ) :
    g =ᵐ[μ] fun _ => 1 :=
  l1_pairing_density_ae_unique hg (integrable_const _) hrep (fun γ => by simpa using hunit γ)

end C2Riemannian


