module

public import C2Riemannian.WeakMollificationStrong
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Abel

set_option autoImplicit false

open MeasureTheory Set Filter TopologicalSpace
open scoped ContDiff Distributions Topology

namespace C2Riemannian

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {U : Opens Plane} {u u' : Plane → F} {τ : Plane}

/-- A scalar weight depending only on a linear normal coordinate is invariant under
translations in any direction in the kernel of that coordinate. -/
public theorem phase_invariant_of_linearForm (k : ℝ → ℝ) (a : Plane →L[ℝ] ℝ)
    (hτ : a τ = 0) (x : Plane) (t : ℝ) :
    k (a (x + t • τ)) = k (a x) := by
  simp [map_add, map_smul, hτ]

private theorem mollified_weight_invariant {a : Plane → ℝ}
    (hτ : ∀ x : Plane, ∀ t : ℝ, a (x + t • τ) = a x)
    (ρ : ContDiffBump (0 : Plane)) (x : Plane) (t : ℝ) :
    WeakJet2.mollify ⊤ ρ a (x + t • τ) = WeakJet2.mollify ⊤ ρ a x := by
  change (∫ y, ρ.normed volume (x + t • τ - y) • ((⊤ : Opens Plane) : Set Plane).indicator a y) =
      ∫ y, ρ.normed volume (x - y) • ((⊤ : Opens Plane) : Set Plane).indicator a y
  simp only [Opens.coe_top, indicator_univ]
  rw [← integral_add_right_eq_self (fun y => ρ.normed volume (x + t • τ - y) • a y) (t • τ)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  change ρ.normed volume (x + t • τ - (y + t • τ)) • a (y + t • τ) =
    ρ.normed volume (x - y) • a y
  rw [hτ y t, show x + t • τ - (y + t • τ) = x - y from by abel]

private theorem weighted_integral_tendsto {μ : Measure Plane} {g : Plane → F}
    (hg : Integrable g μ) {a : Plane → ℝ} {A : ℕ → Plane → ℝ} {C : ℝ}
    (hAm : ∀ n, AEStronglyMeasurable (A n) μ)
    (hAb : ∀ n x, ‖A n x‖ ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => A n x) atTop (𝓝 (a x))) :
    Tendsto (fun n => ∫ x, A n x • g x ∂μ) atTop (𝓝 (∫ x, a x • g x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => C * ‖g x‖)
  · intro n
    exact (hAm n).smul hg.aestronglyMeasurable
  · exact hg.norm.const_mul C
  · intro n
    exact Eventually.of_forall fun x => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hAb n x) (norm_nonneg _)
  · filter_upwards [hlim] with x hx
    exact hx.smul tendsto_const_nhds

/-- Integration by parts for a weak directional derivative with a bounded measurable
weight invariant under translations in that direction. -/
public theorem phase_tangential_ibp
    (hu : TauCeti.HasWeakLineDerivOn volume U u u' τ)
    {a : Plane → ℝ} (ha : AEStronglyMeasurable a volume)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ x ∂(volume : Measure Plane), ‖a x‖ ≤ C)
    (hinv : ∀ x : Plane, ∀ t : ℝ, a (x + t • τ) = a x) (φ : 𝓓(U, ℝ)) :
    (∫ x in ↑U, a x • (lineDeriv ℝ (φ : Plane → ℝ) x τ • u x)) =
      -∫ x in ↑U, a x • (φ x • u' x) := by
  let A (n : ℕ) := WeakJet2.mollify (⊤ : Opens Plane) (WeakJet2.shrinkingBump n) a
  have htop : MemLp a ⊤ (volume.restrict ((⊤ : Opens Plane) : Set Plane)) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using memLp_top_of_bound ha C hb
  have hA (n : ℕ) : ContDiff ℝ ∞ (A n) :=
    WeakJet2.contDiff_mollify htop (by simp) (WeakJet2.shrinkingBump n)
  have hAb (n : ℕ) (x : Plane) : ‖A n x‖ ≤ C :=
    WeakJet2.norm_mollify_le hC (by simpa only [Opens.coe_top, Measure.restrict_univ] using hb)
      (WeakJet2.shrinkingBump n) x
  have haelim : ∀ᵐ x ∂(volume : Measure Plane), Tendsto (fun n => A n x) atTop (𝓝 (a x)) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      WeakJet2.mollify_ae_tendsto htop (by simp) WeakJet2.shrinkingBump
        WeakJet2.shrinkingBump_rOut_tendsto WeakJet2.shrinkingBump_ratio
  let φn (n : ℕ) : 𝓓(U, ℝ) :=
    ⟨fun x => A n x * φ x, (hA n).mul φ.contDiff, φ.hasCompactSupport.mul_left,
      tsupport_mul_subset_right.trans φ.tsupport_subset⟩
  have hφn (n : ℕ) (x : Plane) :
      lineDeriv ℝ (φn n : Plane → ℝ) x τ = A n x * lineDeriv ℝ (φ : Plane → ℝ) x τ := by
    have hinvA : (fun t : ℝ => A n (x + t • τ)) = fun _ => A n x :=
      funext fun t => mollified_weight_invariant hinv (WeakJet2.shrinkingBump n) x t
    have hdA : HasDerivAt (fun t : ℝ => A n (x + t • τ)) 0 0 := by
      rw [hinvA]
      exact hasDerivAt_const _ _
    have hdφ : HasLineDerivAt ℝ (φ : Plane → ℝ)
        (lineDeriv ℝ (φ : Plane → ℝ) x τ) x τ :=
      (φ.contDiff.differentiable (by simp) x).lineDifferentiableAt.hasLineDerivAt
    have hprod : HasLineDerivAt ℝ (φn n : Plane → ℝ)
        (A n x * lineDeriv ℝ (φ : Plane → ℝ) x τ) x τ := by
      change HasDerivAt (fun t : ℝ => A n (x + t • τ) * φ (x + t • τ)) _ 0
      have hdφ' : HasDerivAt (fun t : ℝ => φ (x + t • τ))
          (lineDeriv ℝ (φ : Plane → ℝ) x τ) 0 := hdφ
      simpa using hdA.fun_mul hdφ'
    exact hprod.lineDeriv
  have hseq (n : ℕ) :
      (∫ x in ↑U, A n x • (lineDeriv ℝ (φ : Plane → ℝ) x τ • u x)) =
        -∫ x in ↑U, A n x • (φ x • u' x) := by
    have hi := hu.integral_lineDeriv_smul_eq_neg_integral_smul (φn n)
    rw [← TauCeti.setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul (φn n) τ,
      ← TauCeti.setIntegral_smul_eq_integral_smul (φn n)] at hi
    simp_rw [hφn] at hi
    change (∫ x in ↑U, (A n x * lineDeriv ℝ (φ : Plane → ℝ) x τ) • u x) =
      -∫ x in ↑U, (A n x * φ x) • u' x at hi
    simpa only [mul_smul] using hi
  have hL := (TauCeti.integrable_lineDeriv_smul_of_locallyIntegrableOn
    hu.locallyIntegrableOn φ τ).integrableOn (s := (U : Set Plane))
  have hR := (TauCeti.integrable_smul_of_locallyIntegrableOn
    hu.locallyIntegrableOn_deriv φ).integrableOn (s := (U : Set Plane))
  have hac := ae_mono (Measure.restrict_le_self : volume.restrict (U : Set Plane) ≤ volume) haelim
  have hm (n : ℕ) : AEStronglyMeasurable (A n) (volume.restrict (U : Set Plane)) :=
    (hA n).continuous.aestronglyMeasurable
  exact tendsto_nhds_unique_of_eventuallyEq
    (weighted_integral_tendsto hL hm hAb hac) (weighted_integral_tendsto hR hm hAb hac).neg
    (Eventually.of_forall hseq)

/-- Tangential integration by parts for a weak Hessian column and an invariant weight. -/
public theorem WeakJet2.phase_tangential_ibp_component {m : ℕ} (w : WeakJet2 m U)
    (v : Plane) {a : Plane → ℝ} (ha : AEStronglyMeasurable a volume)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ x ∂(volume : Measure Plane), ‖a x‖ ≤ C)
    (hinv : ∀ x : Plane, ∀ t : ℝ, a (x + t • τ) = a x) (φ : 𝓓(U, ℝ)) :
    (∫ x in ↑U, a x • (φ x • w.second x τ v)) =
      -∫ x in ↑U, a x • (lineDeriv ℝ (φ : Plane → ℝ) x τ • w.gradient x v) := by
  rw [phase_tangential_ibp (w.weak_component τ v) ha hC hb hinv φ, neg_neg]

/-- Limits of the weighted Hessian tests identify the tangential column whenever the
weighted gradient tests converge to those of the limiting weak jet. -/
public theorem WeakJet2.conditional_tangent_eq {m : ℕ} (w : ℕ → WeakJet2 m U)
    (w₀ : WeakJet2 m U) (v : Plane) (a : ℕ → Plane → ℝ)
    (ha : ∀ n, AEStronglyMeasurable (a n) volume) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n, ∀ᵐ x ∂(volume : Measure Plane), ‖a n x‖ ≤ C)
    (hinv : ∀ n, ∀ x : Plane, ∀ t : ℝ, a n (x + t • τ) = a n x)
    {h : Plane → Target m} (hh : LocallyIntegrableOn h U volume)
    (hsecond : ∀ φ : 𝓓(U, ℝ),
      Tendsto (fun n => ∫ x in ↑U, a n x • (φ x • (w n).second x τ v)) atTop
        (𝓝 (∫ x in ↑U, φ x • h x)))
    (hgradient : ∀ φ : 𝓓(U, ℝ),
      Tendsto (fun n => ∫ x in ↑U, a n x • (lineDeriv ℝ (φ : Plane → ℝ) x τ •
        (w n).gradient x v)) atTop
        (𝓝 (∫ x in ↑U, lineDeriv ℝ (φ : Plane → ℝ) x τ • w₀.gradient x v))) :
    h =ᵐ[volume.restrict (U : Set Plane)] fun x => w₀.second x τ v := by
  have hw₀ := w₀.weak_component τ v
  apply ae_eq_of_test_integrals hh hw₀.locallyIntegrableOn_deriv
  intro φ
  have hlim := tendsto_nhds_unique_of_eventuallyEq (hsecond φ) (hgradient φ).neg
    (Eventually.of_forall fun n => (w n).phase_tangential_ibp_component v
      (ha n) hC (hb n) (hinv n) φ)
  have hi := hw₀.integral_lineDeriv_smul_eq_neg_integral_smul φ
  rw [← TauCeti.setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul φ τ,
    ← TauCeti.setIntegral_smul_eq_integral_smul φ] at hi
  rw [hlim, hi, neg_neg]

/-- A bounded sequence of phase weights preserves the vanishing test error from
uniform convergence of gradients on the support of a derivative test. -/
public theorem phase_weighted_gradient_error {a : ℕ → Plane → ℝ}
    {g : ℕ → Plane → F} {g₀ : Plane → F} (φ : 𝓓(U, ℝ)) (τ : Plane)
    {C : ℝ} (hC : 0 ≤ C) (ha : ∀ n, ∀ᵐ x ∂volume.restrict (U : Set Plane), ‖a n x‖ ≤ C)
    {d : ℕ → ℝ} (hd : Tendsto d atTop (𝓝 0))
    (hg : ∀ n, ∀ x ∈ tsupport (φ : Plane → ℝ), ‖g n x - g₀ x‖ ≤ d n) :
    Tendsto (fun n => ∫ x in ↑U, a n x •
      (lineDeriv ℝ (φ : Plane → ℝ) x τ • (g n x - g₀ x))) atTop (𝓝 0) := by
  let S := tsupport (φ : Plane → ℝ)
  let χ : 𝓓(U, ℝ) := TestFunction.lineDerivCLM ℝ τ φ
  have hχ (x : Plane) : χ x = lineDeriv ℝ (φ : Plane → ℝ) x τ :=
    TestFunction.lineDerivCLM_apply_of_le le_top
  have hχi : Integrable (fun x : Plane => ‖χ x‖) (volume.restrict (U : Set Plane)) :=
    (χ.continuous.integrable_of_hasCompactSupport χ.hasCompactSupport).norm.integrableOn
  let c := ∫ x in ↑U, ‖χ x‖
  have hlim : Tendsto (fun n => C * d n * c) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using (hd.const_mul C).mul_const c
  apply squeeze_zero_norm _ hlim
  intro n
  have hB : ∀ᵐ x ∂volume.restrict (U : Set Plane),
      ‖a n x • (lineDeriv ℝ (φ : Plane → ℝ) x τ • (g n x - g₀ x))‖ ≤
        C * d n * ‖χ x‖ := by
    filter_upwards [ha n] with x hx
    rw [← hχ x, norm_smul, norm_smul]
    by_cases hs : x ∈ S
    · calc
        ‖a n x‖ * (‖χ x‖ * ‖g n x - g₀ x‖) =
            ‖a n x‖ * ‖g n x - g₀ x‖ * ‖χ x‖ := by ac_rfl
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul hx (hg n x hs) (norm_nonneg _) hC)
          (norm_nonneg _)
    · have hz : χ x = 0 := by
        rw [hχ x]
        exact TauCeti.lineDeriv_eq_zero_of_notMem_tsupport φ hs τ
      simp [hz]
  rw [show C * d n * c = ∫ x in ↑U, (C * d n) * ‖χ x‖ from (integral_const_mul _ _).symm]
  exact norm_integral_le_of_norm_le (hχi.const_mul _) hB

/-- Uniform gradient convergence on the test support and scalar weak-star convergence
of phase weights give the gradient test limit in tangential integration by parts. -/
public theorem phase_weighted_gradient_tendsto {a : ℕ → Plane → ℝ}
    {g : ℕ → Plane → ℝ} {g₀ : Plane → ℝ} (φ : 𝓓(U, ℝ)) (τ : Plane)
    {C : ℝ} (hC : 0 ≤ C) (ha : ∀ n, ∀ᵐ x ∂volume.restrict (U : Set Plane), ‖a n x‖ ≤ C)
    (ham : ∀ n, AEStronglyMeasurable (a n) (volume.restrict (U : Set Plane)))
    (hstar : ∀ γ : Plane → ℝ, IntegrableOn γ U volume →
      Tendsto (fun n => ∫ x in ↑U, a n x * γ x) atTop (𝓝 (∫ x in ↑U, γ x)))
    (hgi : ∀ n, LocallyIntegrableOn (g n) U volume) (hgi₀ : LocallyIntegrableOn g₀ U volume)
    {d : ℕ → ℝ} (hd : Tendsto d atTop (𝓝 0))
    (hg : ∀ n, ∀ x ∈ tsupport (φ : Plane → ℝ), ‖g n x - g₀ x‖ ≤ d n) :
    Tendsto (fun n => ∫ x in ↑U, a n x * (lineDeriv ℝ (φ : Plane → ℝ) x τ * g n x)) atTop
      (𝓝 (∫ x in ↑U, lineDeriv ℝ (φ : Plane → ℝ) x τ * g₀ x)) := by
  let l (x : Plane) := lineDeriv ℝ (φ : Plane → ℝ) x τ
  have hi : ∀ n, IntegrableOn (fun x => l x * g n x) U volume := fun n => by
    simpa only [smul_eq_mul] using
      (TauCeti.integrable_lineDeriv_smul_of_locallyIntegrableOn (hgi n) φ τ).integrableOn
  have hi₀ : IntegrableOn (fun x => l x * g₀ x) U volume := by
    simpa only [smul_eq_mul] using
      (TauCeti.integrable_lineDeriv_smul_of_locallyIntegrableOn hgi₀ φ τ).integrableOn
  have htest := hstar (fun x => l x * g₀ x) hi₀
  have herr := phase_weighted_gradient_error φ τ hC ha hd hg
  simp only [smul_eq_mul] at herr
  have heq (n : ℕ) : (∫ x in ↑U, a n x * (l x * g n x)) =
      (∫ x in ↑U, a n x * (l x * (g n x - g₀ x))) + ∫ x in ↑U, a n x * (l x * g₀ x) := by
    have hw {f : Plane → ℝ} (hf : IntegrableOn f U volume) :
        IntegrableOn (fun x => a n x * f x) U volume :=
      (hf.norm.const_mul C).mono' ((ham n).mul hf.aestronglyMeasurable) <| by
        filter_upwards [ha n] with x hx
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    simp only [mul_sub, integral_sub (hw (hi n)) (hw hi₀), sub_add_cancel]
  simpa only [l, zero_add] using (herr.add htest).congr (fun n => (heq n).symm)

end C2Riemannian

