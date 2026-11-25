module

public import C2Riemannian.WeakMollificationStrong
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open MeasureTheory Set Filter TopologicalSpace ContinuousLinearMap
open scoped Convolution ENNReal NNReal Topology

namespace C2Riemannian.WeakJet2

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Whole-plane convolution by the normalized bump. -/
@[expose] public noncomputable def bumpConvolve (φ : ContDiffBump (0 : Plane))
    (f : Plane → F) : Plane → F :=
  f ⋆[(lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip, volume] φ.normed volume

private theorem bumpConvolve_sq_le (φ : ContDiffBump (0 : Plane)) {f : Plane → F}
    (hf : MemLp f 2 volume) (x : Plane) :
    ‖bumpConvolve φ f x‖ ^ 2 ≤ bumpConvolve φ (fun y => ‖f y‖ ^ 2) x := by
  let ρ : Plane → ℝ := fun y => φ.normed volume (x - y)
  let k : Plane → ℝ≥0 := fun y => (ρ y).toNNReal
  let ν := (volume : Measure Plane).withDensity (fun y => (k y : ℝ≥0∞))
  have hρc : Continuous ρ := (φ.contDiff_normed (n := 0)).continuous.comp
    (continuous_const.sub continuous_id)
  have hk : Measurable k := (continuous_real_toNNReal.comp hρc).measurable
  have hkρ (y : Plane) : (k y : ℝ) = ρ y := Real.coe_toNNReal _ (φ.nonneg_normed _)
  have hρnn (y : Plane) : 0 ≤ ρ y := φ.nonneg_normed _
  have hρi : Integrable ρ volume :=
    (integrable_comp_sub_left _ x).2 φ.integrable_normed
  have hρmass : ∫ y, ρ y = 1 := by
    change ∫ y, φ.normed volume (x - y) = 1
    rw [integral_sub_left_eq_self, φ.integral_normed]
  let : IsProbabilityMeasure ν := ⟨by
    rw [show ν = volume.withDensity (fun y => ENNReal.ofReal (ρ y)) from rfl,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hρi (Eventually.of_forall hρnn), hρmass,
      ENNReal.ofReal_one]⟩
  have hi : Integrable f ν := by
    apply (integrable_withDensity_iff_integrable_smul hk).2
    simp only [NNReal.smul_def, hkρ]
    exact φ.hasCompactSupport_normed.convolutionExists_right
      ((lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip) (hf.locallyIntegrable (by simp))
      ((φ.contDiff_normed (n := 0)).continuous) x
  have hsq : Integrable (fun y => ‖f y‖ ^ 2) volume :=
    hf.integrable_norm_pow (p := 2) (by decide)
  have hiSq : Integrable ((fun v : F => ‖v‖ ^ 2) ∘ f) ν := by
    apply (integrable_withDensity_iff_integrable_smul hk).2
    simp only [Function.comp_apply, NNReal.smul_def, hkρ]
    exact φ.hasCompactSupport_normed.convolutionExists_right
      ((lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip) hsq.locallyIntegrable
      ((φ.contDiff_normed (n := 0)).continuous) x
  have hc : ConvexOn ℝ univ (fun v : F => ‖v‖ ^ 2) :=
    convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2
  have hj := hc.map_integral_le (continuous_norm.pow 2).continuousOn isClosed_univ
    (Eventually.of_forall fun x => mem_univ (f x)) hi hiSq
  rw [integral_withDensity_eq_integral_smul hk, integral_withDensity_eq_integral_smul hk] at hj
  simp only [NNReal.smul_def, hkρ] at hj
  exact hj

/-- Convolution by a normalized bump takes square-integrable vector fields into square-integrable
fields and contracts the square integral. -/
public theorem bumpConvolve_l2_contract (φ : ContDiffBump (0 : Plane)) {f : Plane → F}
    (hf : MemLp f 2 volume) :
    MemLp (bumpConvolve φ f) 2 volume ∧
    (∫ x, ‖bumpConvolve φ f x‖ ^ 2) ≤ ∫ x, ‖f x‖ ^ 2 := by
  let ψ : Plane → ℝ := fun x => ‖f x‖ ^ 2
  have hψ : Integrable ψ volume := hf.integrable_norm_pow (p := 2) (by decide)
  have hψc : Integrable (bumpConvolve φ ψ) volume :=
    hψ.integrable_convolution _ φ.integrable_normed
  have hfc : Continuous (bumpConvolve φ f) :=
    φ.hasCompactSupport_normed.contDiff_convolution_right _ (hf.locallyIntegrable (by simp))
      (φ.contDiff_normed (n := 0)) |>.continuous
  have hsq : Integrable (fun x => ‖bumpConvolve φ f x‖ ^ 2) volume := by
    refine hψc.mono' ((hfc.norm.pow 2).aestronglyMeasurable) ?_
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact bumpConvolve_sq_le φ hf x
  refine ⟨(memLp_two_iff_integrable_sq_norm hfc.aestronglyMeasurable).2 hsq, ?_⟩
  calc
    _ ≤ ∫ x, bumpConvolve φ ψ x := integral_mono hsq hψc (bumpConvolve_sq_le φ hf)
    _ = ∫ x, ψ x := by
      rw [bumpConvolve, integral_convolution _ hψ φ.integrable_normed, φ.integral_normed]
      exact one_smul ℝ _

/-- The L² seminorm of whole-plane bump convolution does not exceed that of the input. -/
public theorem eLpNorm_bumpConvolve_le (φ : ContDiffBump (0 : Plane)) {f : Plane → F}
    (hf : MemLp f 2 volume) :
    eLpNorm (bumpConvolve φ f) 2 volume ≤ eLpNorm f 2 volume := by
  obtain ⟨hm, hle⟩ := bumpConvolve_l2_contract φ hf
  rw [hm.eLpNorm_eq_integral_rpow_norm (by simp) (by simp),
    hf.eLpNorm_eq_integral_rpow_norm (by simp) (by simp)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow
    (integral_nonneg fun _ => sq_nonneg _) hle (inv_nonneg.mpr zero_le_two))

omit [CompleteSpace F] in
private theorem bumpConvolve_sub (φ : ContDiffBump (0 : Plane)) {f g : Plane → F}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    bumpConvolve φ (f - g) = bumpConvolve φ f - bumpConvolve φ g := by
  let L := (lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip
  have hc : Continuous (φ.normed (volume : Measure Plane)) :=
    (φ.contDiff_normed (n := 0)).continuous
  funext x
  have h₁ := φ.hasCompactSupport_normed.convolutionExists_right L
    (hf.locallyIntegrable (by simp)) hc x
  have h₂ := φ.hasCompactSupport_normed.convolutionExists_right L
    (hg.locallyIntegrable (by simp)) hc x
  simp only [bumpConvolve, convolution_def, Pi.sub_apply, flip_apply, lsmul_apply, smul_sub]
  exact integral_sub h₁ h₂

/-- Whole-plane convolution converges strongly on finite-measure subdomains for every
square-integrable input. -/
public theorem eLpNorm_bumpConvolve_sub_tendsto_zero {V : Opens Plane}
    [IsFiniteMeasure (volume.restrict (V : Set Plane))]
    {f : Plane → F} (hf : MemLp f 2 volume)
    (φ : ℕ → ContDiffBump (0 : Plane))
    (hr : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    {K : ℝ} (hK : ∀ᶠ n in atTop, (φ n).rOut ≤ K * (φ n).rIn) :
    Tendsto (fun n => eLpNorm (bumpConvolve (φ n) f - f) 2 (volume.restrict (V : Set Plane)))
      atTop (𝓝 0) := by
  let μ := volume.restrict (V : Set Plane)
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨η, hη, hηε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
  let δ : ℝ≥0 := η / 4
  have hηR : 0 < (η : ℝ) := by exact_mod_cast hη
  have hδ : 0 < (δ : ℝ) := by
    change 0 < (η : ℝ) / 4
    positivity
  have hδ' : (0 : ℝ≥0∞) < δ := by exact_mod_cast hδ
  have hsum : (δ : ℝ≥0∞) + δ + δ ≤ η := by
    have hr' : (δ : ℝ) + δ + δ ≤ η := by
      change (η : ℝ) / 4 + (η : ℝ) / 4 + (η : ℝ) / 4 ≤ η
      linarith only [η.coe_nonneg]
    exact_mod_cast hr'
  obtain ⟨g, hgc, hgs, hfg⟩ := hf.exist_eLpNorm_sub_le (by simp) (by simp) hδ
  rw [ENNReal.ofReal_coe_nnreal] at hfg
  have hg : MemLp g 2 volume := hgs.continuous.memLp_of_hasCompactSupport hgc
  obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hgs.continuous
  have hC' : 0 ≤ C := (norm_nonneg (g 0)).trans (hC 0)
  have hgtop : MemLp g ∞ (volume.restrict ((⊤ : Opens Plane) : Set Plane)) :=
    memLp_top_of_bound hgs.continuous.aestronglyMeasurable C (Eventually.of_forall hC)
  have hlim : Tendsto (fun n => eLpNorm (bumpConvolve (φ n) g - g) 2 μ) atTop (𝓝 0) := by
    simpa only [bumpConvolve, mollify, Opens.coe_top, indicator_univ, μ] using
      mollify_tendsto_eLpNorm_of_bound (V := V) le_top hgtop hC' (Eventually.of_forall hC)
        φ hr hK (p := 2) (by simp) (by simp)
  filter_upwards [ENNReal.tendsto_nhds_zero.mp hlim _ hδ'] with n hn
  have h₁ : eLpNorm (bumpConvolve (φ n) (f - g)) 2 μ ≤ δ :=
    (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
      ((eLpNorm_bumpConvolve_le _ (hf.sub hg)).trans hfg)
  have h₂ : eLpNorm (g - f) 2 μ ≤ δ := by
    rw [← neg_sub, eLpNorm_neg]
    exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans hfg
  have heq : bumpConvolve (φ n) f - f = bumpConvolve (φ n) (f - g) +
      (bumpConvolve (φ n) g - g) + (g - f) := by
    rw [bumpConvolve_sub _ hf hg]
    abel
  change eLpNorm (bumpConvolve (φ n) f - f) 2 μ ≤ ε
  rw [heq]
  refine (eLpNorm_add_le (by simp)).trans ?_
  exact (add_le_add ((eLpNorm_add_le (by simp)).trans (add_le_add h₁ hn)) h₂).trans
    (hsum.trans hηε.le)

/-- Zero-extension mollification of square-integrable data converges strongly in L²
on finite-measure open subdomains. -/
public theorem eLpNorm_mollify_sub_tendsto_zero {U V : Opens Plane} (hVU : V ≤ U)
    [IsFiniteMeasure (volume.restrict (V : Set Plane))]
    {f : Plane → F} (hf : MemLp f 2 (volume.restrict (U : Set Plane)))
    (φ : ℕ → ContDiffBump (0 : Plane))
    (hr : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    {K : ℝ} (hK : ∀ᶠ n in atTop, (φ n).rOut ≤ K * (φ n).rIn) :
    Tendsto (fun n => eLpNorm (mollify U (φ n) f - f) 2 (volume.restrict (V : Set Plane)))
      atTop (𝓝 0) := by
  let g := (U : Set Plane).indicator f
  have hg : MemLp g 2 volume :=
    (memLp_indicator_iff_restrict U.isOpen.measurableSet.nullMeasurableSet).2 hf
  have hfg : f =ᵐ[volume.restrict (V : Set Plane)] g := by
    filter_upwards [ae_restrict_mem (μ := volume) V.isOpen.measurableSet] with x hx
    exact (indicator_of_mem (hVU hx) f).symm
  have heq (n : ℕ) :
      eLpNorm (mollify U (φ n) f - f) 2 (volume.restrict (V : Set Plane)) =
        eLpNorm (bumpConvolve (φ n) g - g) 2 (volume.restrict (V : Set Plane)) :=
    eLpNorm_congr_ae (hfg.mono fun x hx => congrArg (mollify U (φ n) f x - ·) hx)
  simp_rw [heq]
  exact eLpNorm_bumpConvolve_sub_tendsto_zero hg φ hr hK

/-- On a finite-measure open subdomain, a square-integrable field and its normalized
mollifications have strong L² convergence in square-integral form. -/
public theorem mollify_strongL2 {U V : Opens Plane} (hVU : V ≤ U)
    [IsFiniteMeasure (volume.restrict (V : Set Plane))]
    {f : Plane → F} (hf : MemLp f 2 (volume.restrict (U : Set Plane)))
    (φ : ℕ → ContDiffBump (0 : Plane))
    (hr : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    {K : ℝ} (hK : ∀ᶠ n in atTop, (φ n).rOut ≤ K * (φ n).rIn) :
    StrongL2 atTop (volume.restrict (V : Set Plane)) (fun n => mollify U (φ n) f) f := by
  let μ := volume.restrict (V : Set Plane)
  let g := (U : Set Plane).indicator f
  have hg : MemLp g 2 volume :=
    (memLp_indicator_iff_restrict U.isOpen.measurableSet.nullMeasurableSet).2 hf
  have hm (n : ℕ) : MemLp (mollify U (φ n) f) 2 μ :=
    ((bumpConvolve_l2_contract (φ n) hg).1).mono_measure Measure.restrict_le_self
  have hfm : MemLp f 2 μ := hf.mono_measure (Measure.restrict_mono hVU le_rfl)
  refine ⟨hm, hfm, ?_⟩
  have hlim := eLpNorm_mollify_sub_tendsto_zero hVU hf φ hr hK
  let e (n : ℕ) := mollify U (φ n) f - f
  have heq (n : ℕ) :
      (eLpNorm (e n) 2 μ).toReal ^ 2 = ∫ x, ‖e n x‖ ^ (2 : ℝ) ∂μ := by
    rw [((hm n).sub hfm).eLpNorm_eq_integral_rpow_norm (by simp) (by simp),
      ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) _)]
    simp only [ENNReal.toReal_ofNat]
    rw [← Real.rpow_mul_natCast (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _) ]
    norm_num [e]
  have hreal := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hlim
  change Tendsto (fun n => (eLpNorm (e n) 2 μ).toReal) atTop (𝓝 (0 : ℝ)) at hreal
  have hsquare : Tendsto (fun n => (eLpNorm (e n) 2 μ).toReal ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using hreal.pow 2
  simp_rw [heq] at hsquare
  exact hsquare

/-- Continuous linear projections of a square-integrable field have strong L² convergence
for the same sequence of mollifications. -/
public theorem mollify_clm_strongL2 {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] {U V : Opens Plane} (hVU : V ≤ U)
    [IsFiniteMeasure (volume.restrict (V : Set Plane))]
    {f : Plane → F} (hf : MemLp f 2 (volume.restrict (U : Set Plane)))
    (φ : ℕ → ContDiffBump (0 : Plane))
    (hr : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    {K : ℝ} (hK : ∀ᶠ n in atTop, (φ n).rOut ≤ K * (φ n).rIn)
    (L : F →L[ℝ] G) :
    StrongL2 atTop (volume.restrict (V : Set Plane)) (fun n x => L (mollify U (φ n) f x))
      (fun x => L (f x)) := by
  have hstrong := mollify_strongL2 hVU (L.comp_memLp' hf) φ hr hK
  have heq (n : ℕ) : mollify U (φ n) (L ∘ f) = fun x => L (mollify U (φ n) f x) := by
    funext x
    exact mollify_clm hf (by simp) (φ n) L x
  simp only [Function.comp_def] at hstrong heq
  simpa only [heq] using hstrong

end C2Riemannian.WeakJet2





