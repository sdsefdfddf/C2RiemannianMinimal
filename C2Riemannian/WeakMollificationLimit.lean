module

public import C2Riemannian.WeakAnalysis
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

open MeasureTheory Set Filter TopologicalSpace ContinuousLinearMap
open scoped Convolution ENNReal Topology

namespace C2Riemannian
namespace WeakJet2

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable {U V : Opens Plane} {f : Plane → F}

omit [CompleteSpace F] in
/-- The normalized nonnegative bump preserves a uniform bound on the zero-extended field. -/
public theorem norm_mollify_le {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ᵐ x ∂volume.restrict (U : Set Plane), ‖f x‖ ≤ C)
    (φ : ContDiffBump (0 : Plane)) (x : Plane) : ‖mollify U φ f x‖ ≤ C := by
  have hg : ∀ᵐ y ∂(volume : Measure Plane), ‖(U : Set Plane).indicator f y‖ ≤ C := by
    rw [ae_restrict_iff' U.isOpen.measurableSet] at hf
    filter_upwards [hf] with y hy
    by_cases hyU : y ∈ (U : Set Plane)
    · simpa only [indicator_of_mem hyU] using hy hyU
    · simpa only [indicator_of_notMem hyU, norm_zero] using hC
  have hkernel : Integrable (fun y => φ.normed volume (x - y)) volume :=
    (integrable_comp_sub_left (φ.normed (volume : Measure Plane)) x).2 φ.integrable_normed
  change ‖∫ y, φ.normed volume (x - y) • (U : Set Plane).indicator f y‖ ≤ C
  calc
    _ ≤ ∫ y, φ.normed volume (x - y) * C := by
      apply norm_integral_le_of_norm_le (hkernel.mul_const C)
      filter_upwards [hg] with y hy
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed _)]
      exact mul_le_mul_of_nonneg_left hy (φ.nonneg_normed _)
    _ = C := by rw [integral_mul_const, integral_sub_left_eq_self, φ.integral_normed, one_mul]

/-- The normalized mollifiers converge almost everywhere to the field on the zero-extension
domain when the radii shrink to zero with bounded ratio. -/
public theorem mollify_ae_tendsto {p : ℝ≥0∞} (hf : MemLp f p (volume.restrict (U : Set Plane)))
    (hp : 1 ≤ p) (φ : ℕ → ContDiffBump (0 : Plane))
    (hr : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    {K : ℝ} (hK : ∀ᶠ n in atTop, (φ n).rOut ≤ K * (φ n).rIn) :
    ∀ᵐ x ∂volume.restrict (U : Set Plane), Tendsto (fun n => mollify U (φ n) f x) atTop (𝓝 (f x)) := by
  have hext : MemLp ((U : Set Plane).indicator f) p volume :=
    (memLp_indicator_iff_restrict U.isOpen.measurableSet.nullMeasurableSet).2 hf
  have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hr hK
    (hext.locallyIntegrable hp)
  rw [ae_restrict_iff' U.isOpen.measurableSet]
  filter_upwards [h] with x hx hxU
  simpa only [mollify, convolution_flip, indicator_of_mem hxU] using hx

/-- On each finite-measure subdomain the mollifications of an essentially bounded field
converge strongly in every finite positive exponent. -/
public theorem mollify_tendsto_eLpNorm_of_bound
    (hVU : V ≤ U) [IsFiniteMeasure (volume.restrict (V : Set Plane))]
    (hf : MemLp f ∞ (volume.restrict (U : Set Plane)))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ x ∂volume.restrict (U : Set Plane), ‖f x‖ ≤ C)
    (φ : ℕ → ContDiffBump (0 : Plane))
    (hr : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    {K : ℝ} (hK : ∀ᶠ n in atTop, (φ n).rOut ≤ K * (φ n).rIn)
    {p : ℝ≥0∞} (hp : p ≠ 0) (hpt : p ≠ ∞) :
    Tendsto (fun n => eLpNorm (mollify U (φ n) f - f) p (volume.restrict (V : Set Plane)))
      atTop (𝓝 0) := by
  let μ := volume.restrict (V : Set Plane)
  let err := fun n => mollify U (φ n) f - f
  have hm : μ ≤ volume.restrict (U : Set Plane) := Measure.restrict_mono hVU le_rfl
  have hmeas (n : ℕ) : AEStronglyMeasurable (err n) μ :=
    (contDiff_mollify hf (by simp) (φ n)).continuous.aestronglyMeasurable.sub
      (hf.aestronglyMeasurable.mono_measure hm)
  have hdiff : ∀ᵐ x ∂μ, Tendsto (fun n => err n x) atTop (𝓝 0) := by
    filter_upwards [ae_mono hm (mollify_ae_tendsto hf (by simp) φ hr hK)] with x hx
    simpa only [err, Pi.sub_apply, sub_self] using hx.sub (tendsto_const_nhds (x := f x))
  have hy : ∀ᵐ x ∂μ, ‖f x‖ ≤ C := ae_mono hm hbound
  let b : ℝ≥0∞ := ENNReal.ofReal (C + C) ^ p.toReal
  have hb : ∀ n, (fun x => ‖err n x‖ₑ ^ p.toReal) ≤ᵐ[μ] fun _ => b := by
    intro n
    filter_upwards [hy] with x hx
    have hnorm : ‖err n x‖ ≤ C + C :=
      (norm_sub_le _ _).trans (add_le_add (norm_mollify_le hC hbound (φ n) x) hx)
    exact ENNReal.rpow_le_rpow (by simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal hnorm)
      ENNReal.toReal_nonneg
  have hbfin : (∫⁻ _ : Plane, b ∂μ) ≠ ∞ := by
    rw [lintegral_const]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg
      ENNReal.ofReal_ne_top) (measure_ne_top _ _)
  have hc : Continuous (fun y : F => ‖y‖ₑ ^ p.toReal) :=
    ENNReal.continuous_rpow_const.comp continuous_enorm
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos hp hpt
  have hi : Tendsto (fun n => ∫⁻ x, ‖err n x‖ₑ ^ p.toReal ∂μ) atTop (𝓝 0) := by
    have ht := tendsto_lintegral_of_dominated_convergence' (fun _ => b)
      (fun n => (hc.comp_aestronglyMeasurable (hmeas n)).aemeasurable) hb hbfin
      (hdiff.mono fun x hx => (hc.tendsto 0).comp hx)
    simpa only [enorm_zero, ENNReal.zero_rpow_of_pos hp0, lintegral_zero] using ht
  change Tendsto (fun n => eLpNorm (err n) p μ) atTop (𝓝 0)
  have hEq (n : ℕ) :
      eLpNorm (err n) p μ = (∫⁻ x, ‖err n x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) :=
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp hpt (hmeas n)
  simp_rw [hEq]
  simpa only [Function.comp_def, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hp0)] using
    (ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0 |>.comp hi

/-- Continuous linear maps commute with the normalized zero-extension mollification. -/
public theorem mollify_clm {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {p : ℝ≥0∞} (hf : MemLp f p (volume.restrict (U : Set Plane))) (hp : 1 ≤ p)
    (φ : ContDiffBump (0 : Plane)) (L : F →L[ℝ] G) (x : Plane) :
    mollify U φ (fun y => L (f y)) x = L (mollify U φ f x) := by
  have hext : MemLp ((U : Set Plane).indicator f) p volume :=
    (memLp_indicator_iff_restrict U.isOpen.measurableSet.nullMeasurableSet).2 hf
  have hi : Integrable (fun y => φ.normed volume (x - y) • (U : Set Plane).indicator f y) volume :=
    φ.hasCompactSupport_normed.convolutionExists_right
      ((lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip)
      (hext.locallyIntegrable hp) ((φ.contDiff_normed (n := 0)).continuous) x
  change (∫ y, φ.normed volume (x - y) • (U : Set Plane).indicator (fun z => L (f z)) y) =
    L (∫ y, φ.normed volume (x - y) • (U : Set Plane).indicator f y)
  rw [← L.integral_comp_comm hi]
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y ∈ (U : Set Plane) <;> simp [hy]

/-- The squared (L^2) norm of the approximation error tends to zero on a finite-measure
subdomain for essentially bounded data. -/
public theorem mollify_tendsto_integral_norm_sub_sq
    (hVU : V ≤ U) [IsFiniteMeasure (volume.restrict (V : Set Plane))]
    (hf : MemLp f ∞ (volume.restrict (U : Set Plane)))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ x ∂volume.restrict (U : Set Plane), ‖f x‖ ≤ C)
    (φ : ℕ → ContDiffBump (0 : Plane))
    (hr : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    {K : ℝ} (hK : ∀ᶠ n in atTop, (φ n).rOut ≤ K * (φ n).rIn) :
    Tendsto (fun n => ∫ x in ↑V, ‖mollify U (φ n) f x - f x‖ ^ 2) atTop (𝓝 0) := by
  let μ := volume.restrict (V : Set Plane)
  let err := fun n x => ‖mollify U (φ n) f x - f x‖ ^ 2
  have hm : μ ≤ volume.restrict (U : Set Plane) := Measure.restrict_mono hVU le_rfl
  have hmeas (n : ℕ) : AEStronglyMeasurable (err n) μ :=
    (((contDiff_mollify hf (by simp) (φ n)).continuous.aestronglyMeasurable.sub
      (hf.aestronglyMeasurable.mono_measure hm)).norm).pow 2
  have hy : ∀ᵐ x ∂μ, ‖f x‖ ≤ C := ae_mono hm hbound
  have hb (n : ℕ) : ∀ᵐ x ∂μ, ‖err n x‖ ≤ (C + C) ^ 2 := by
    filter_upwards [hy] with x hx
    have hnorm : ‖mollify U (φ n) f x - f x‖ ≤ C + C :=
      (norm_sub_le _ _).trans (add_le_add (norm_mollify_le hC hbound (φ n) x) hx)
    change |‖mollify U (φ n) f x - f x‖ ^ 2| ≤ (C + C) ^ 2
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => err n x) atTop (𝓝 ((0 : ℝ))) := by
    filter_upwards [ae_mono hm (mollify_ae_tendsto hf (by simp) φ hr hK)] with x hx
    have hd := hx.sub (tendsto_const_nhds (x := f x))
    simpa [err] using hd.norm.pow 2
  simpa only [integral_zero] using
    tendsto_integral_of_dominated_convergence (fun _ => (C + C) ^ 2)
      hmeas (integrable_const _) hb hlim

omit [CompleteSpace F] in
/-- The squared (L^2) norms on a finite-measure subdomain are uniformly bounded by
the square of the original essential bound times the subdomain area. -/
public theorem integral_norm_mollify_sq_le
    [IsFiniteMeasure (volume.restrict (V : Set Plane))]
    (hf : MemLp f ∞ (volume.restrict (U : Set Plane)))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ x ∂volume.restrict (U : Set Plane), ‖f x‖ ≤ C)
    (φ : ContDiffBump (0 : Plane)) :
    (∫ x in ↑V, ‖mollify U φ f x‖ ^ 2) ≤ (volume (V : Set Plane)).toReal * C ^ 2 := by
  have hmem : MemLp (mollify U φ f) (2 : ℝ≥0∞) (volume.restrict (V : Set Plane)) :=
    MemLp.of_bound (contDiff_mollify hf (by simp) φ).continuous.aestronglyMeasurable C
      (Filter.Eventually.of_forall (norm_mollify_le hC hbound φ))
  have hi := hmem.integrable_norm_pow (p := 2) (by decide)
  have hle : (∫ x in ↑V, ‖mollify U φ f x‖ ^ 2) ≤ ∫ _ : Plane in ↑V, C ^ 2 :=
    integral_mono_ae hi (integrable_const _) <| Filter.Eventually.of_forall fun x =>
      pow_le_pow_left₀ (norm_nonneg _) (norm_mollify_le hC hbound φ x) 2
  simpa [Measure.real] using hle

end WeakJet2
end C2Riemannian





