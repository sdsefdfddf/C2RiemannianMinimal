module

public import C2Riemannian.WeakCompatibility
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open MeasureTheory Filter Set TopologicalSpace
open scoped ContDiff Distributions ENNReal

namespace C2Riemannian
namespace WeakJet2

variable {m : ℕ} {U : Opens Plane}

/-- The scalar second derivative of a metric coefficient in the second coordinate direction. -/
@[expose] public noncomputable def metricYY (v : Plane → ℝ) (x : Plane) : ℝ :=
  lineDeriv ℝ (fun y => lineDeriv ℝ v y ey) x ey

private theorem continuous_metricYY {v : Plane → ℝ} (hv : ContDiff ℝ 2 v) :
    Continuous (metricYY v) := by
  have hfirst : ContDiff ℝ 1 (fun x => lineDeriv ℝ v x ey) := by
    have heq : (fun x => lineDeriv ℝ v x ey) = fun x => fderiv ℝ v x ey :=
      funext fun x => (hv.differentiable (by decide) x).lineDeriv_eq_fderiv
    rw [heq]
    exact (hv.fderiv_right (by decide)).clm_apply contDiff_const
  have heq : metricYY v = fun x => fderiv ℝ (fun y => lineDeriv ℝ v y ey) x ey :=
    funext fun x => (hfirst.differentiable_one x).lineDeriv_eq_fderiv
  rw [heq]
  exact ((hfirst.fderiv_right (m := 0) (by decide)).clm_apply contDiff_const).continuous

private theorem integral_testSecond_zero (v u : Plane) (φ : 𝓓(U, ℝ)) :
    (∫ x in ↑U, testSecond v u φ x) = 0 := by
  let ψ : 𝓓(U, ℝ) := TestFunction.lineDerivCLM ℝ v φ
  have heq : (testSecond v u φ : Plane → ℝ) = fun x => lineDeriv ℝ (ψ : Plane → ℝ) x u := by
    funext x
    rw [testSecond_apply]
    have hψ : (ψ : Plane → ℝ) = fun y => lineDeriv ℝ (φ : Plane → ℝ) y v :=
      funext fun _ => TestFunction.lineDerivCLM_apply_of_le le_top
    rw [hψ]
  rw [heq]
  have h := TauCeti.setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul
    (μ := volume) (w := fun _ : Plane => (1 : ℝ)) ψ u
  simp only [smul_eq_mul, mul_one] at h
  exact h.trans (ψ.integral_lineDeriv_eq_zero (μ := volume) u)

/-- The diagonal Gram constraint and the curvature test identity force the scalar metric
source equation almost everywhere. -/
public theorem hessian_q_eq_metric_source_of_tests
    (w : WeakJet2 m U) {v : Plane → ℝ} (hv : ContDiff ℝ 2 v)
    (hq : LocallyIntegrableOn (fun x => (w.hessian x).q) U volume)
    (hxx : ∀ᵐ x ∂volume.restrict (U : Set Plane),
      inner ℝ (w.gradient x ex) (w.gradient x ex) = 1 + v x)
    (hyy : ∀ᵐ x ∂volume.restrict (U : Set Plane),
      inner ℝ (w.gradient x ey) (w.gradient x ey) = 1)
    (hxy : ∀ᵐ x ∂volume.restrict (U : Set Plane),
      inner ℝ (w.gradient x ex) (w.gradient x ey) = 0)
    (htest : ∀ φ : 𝓓(U, ℝ),
      -2 * (∫ x in ↑U, φ x * (w.hessian x).q) =
        (∫ x in ↑U, testSecond ey ey φ x * inner ℝ (w.gradient x ex) (w.gradient x ex)) +
        (∫ x in ↑U, testSecond ex ex φ x * inner ℝ (w.gradient x ey) (w.gradient x ey)) -
        2 * (∫ x in ↑U, testSecond ey ex φ x * inner ℝ (w.gradient x ex) (w.gradient x ey))) :
    ∀ᵐ x ∂volume.restrict (U : Set Plane), (w.hessian x).q = -metricYY v x / 2 := by
  have hg : LocallyIntegrableOn (fun x => -metricYY v x / 2) U volume :=
    ((continuous_metricYY hv).neg.div_const 2).continuousOn.locallyIntegrableOn U.isOpen.measurableSet
  apply ae_eq_of_test_integrals hq hg
  intro φ
  let ψ := testSecond ey ey φ
  have hfirst : (∫ x in ↑U, testSecond ey ey φ x * inner ℝ (w.gradient x ex) (w.gradient x ex)) =
      ∫ x in ↑U, φ x * metricYY v x := by
    have hi₁ : IntegrableOn (ψ : Plane → ℝ) (U : Set Plane) volume :=
      (ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport).integrableOn
    have hi₂ : IntegrableOn (fun x => ψ x * v x) (U : Set Plane) volume :=
      ((ψ.continuous.mul hv.continuous).integrable_of_hasCompactSupport
        ψ.hasCompactSupport.mul_right).integrableOn
    calc
      _ = ∫ x in ↑U, ψ x + ψ x * v x := by
        apply integral_congr_ae
        filter_upwards [hxx] with x hx
        rw [hx, mul_add, mul_one]
      _ = ∫ x in ↑U, ψ x * v x := by
        rw [integral_add hi₁ hi₂, integral_testSecond_zero ey ey φ, zero_add]
      _ = _ := by
        simp_rw [show ∀ x, ψ x = lineDeriv ℝ (fun y => lineDeriv ℝ (φ : Plane → ℝ) y ey) x ey
          from testSecond_apply ey ey φ]
        exact (integral_lineDeriv₂_mul hv ey ey φ).symm
  have hsecond : (∫ x in ↑U, testSecond ex ex φ x * inner ℝ (w.gradient x ey) (w.gradient x ey)) =
      0 := by
    rw [← integral_testSecond_zero ex ex φ]
    exact integral_congr_ae (hyy.mono fun x hx =>
      (congrArg (testSecond ex ex φ x * ·) hx).trans (mul_one _))
  have hthird : (∫ x in ↑U, testSecond ey ex φ x * inner ℝ (w.gradient x ex) (w.gradient x ey)) =
      0 := by
    rw [← integral_zero (α := Plane) (G := ℝ)]
    exact integral_congr_ae (hxy.mono fun x hx =>
      (congrArg (testSecond ey ex φ x * ·) hx).trans (mul_zero _))
  have h := htest φ
  rw [hfirst, hsecond, hthird, add_zero, mul_zero, sub_zero] at h
  change (∫ x in ↑U, φ x * (w.hessian x).q) = ∫ x in ↑U, φ x * (-metricYY v x / 2)
  have heq (x : Plane) : φ x * (-metricYY v x / 2) = (-1 / 2 : ℝ) * (φ x * metricYY v x) := by
    ring
  simp_rw [heq, integral_const_mul]
  linarith

/-- A weak second jet with square-integrable projected fields satisfies the metric
source equation whenever its Gram test identity and diagonal metric constraint hold. -/
public theorem hessian_q_eq_metric_source_of_gramTest
    (w : WeakJet2 m U) {v : Plane → ℝ} (hv : ContDiff ℝ 2 v)
    (hc : ∀ a b : Plane, MemLp (fun x => w.second x b a) 2 (volume.restrict (U : Set Plane)))
    (hxx : ∀ᵐ x ∂volume.restrict (U : Set Plane),
      inner ℝ (w.gradient x ex) (w.gradient x ex) = 1 + v x)
    (hyy : ∀ᵐ x ∂volume.restrict (U : Set Plane),
      inner ℝ (w.gradient x ey) (w.gradient x ey) = 1)
    (hxy : ∀ᵐ x ∂volume.restrict (U : Set Plane),
      inner ℝ (w.gradient x ex) (w.gradient x ey) = 0)
    (htest : ∀ φ : 𝓓(U, ℝ), gramTest (volume.restrict (U : Set Plane)) φ
      (testSecond ex ex φ) (testSecond ey ex φ) (testSecond ey ey φ)
      (fun x => w.gradient x ex) (fun x => w.gradient x ey)
      (fun x => w.second x ex ex) (fun x => w.second x ey ex) (fun x => w.second x ey ey)) :
    ∀ᵐ x ∂volume.restrict (U : Set Plane), (w.hessian x).q = -metricYY v x / 2 := by
  have hi : IntegrableOn (fun x => (w.hessian x).q) (U : Set Plane) volume :=
    (integrable_weak_inner (hc ex ex) (hc ey ey)).sub
      (integrable_weak_inner (hc ex ey) (hc ex ey))
  apply w.hessian_q_eq_metric_source_of_tests hv hi.locallyIntegrableOn hxx hyy hxy
  intro φ
  obtain ⟨C, hφ⟩ := φ.hasCompactSupport.exists_bound_of_continuous φ.continuous
  rw [integral_weighted_q_eq (hc ex ex) (hc ex ey) (hc ey ey)
    φ.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hφ)]
  exact htest φ

/-- Each coordinate evaluation of a bounded second derivative field has finite square integral
on a finite-measure domain. -/
public theorem second_eval_memLp_of_bound
    [IsFiniteMeasure (volume.restrict (U : Set Plane))] (w : WeakJet2 m U)
    (hB : AEStronglyMeasurable w.second (volume.restrict (U : Set Plane)))
    {C : ℝ} (hC : ∀ᵐ x ∂volume.restrict (U : Set Plane), ‖w.second x‖ ≤ C)
    (a b : Plane) : MemLp (fun x => w.second x b a) 2 (volume.restrict (U : Set Plane)) := by
  let L₁ : (Plane →L[ℝ] (Plane →L[ℝ] Target m)) →L[ℝ] (Plane →L[ℝ] Target m) :=
    ContinuousLinearMap.apply ℝ (Plane →L[ℝ] Target m) b
  let L₂ : (Plane →L[ℝ] Target m) →L[ℝ] Target m :=
    ContinuousLinearMap.apply ℝ (Target m) a
  have h₁ : AEStronglyMeasurable (fun x => L₁ (w.second x)) (volume.restrict (U : Set Plane)) :=
    L₁.continuous.comp_aestronglyMeasurable hB
  have h₂ : AEStronglyMeasurable (fun x => L₂ (L₁ (w.second x))) (volume.restrict (U : Set Plane)) :=
    L₂.continuous.comp_aestronglyMeasurable h₁
  refine MemLp.of_bound h₂ (C * ‖b‖ * ‖a‖) ?_
  filter_upwards [hC] with x hx
  change ‖w.second x b a‖ ≤ C * ‖b‖ * ‖a‖
  exact ((w.second x b).le_opNorm a).trans
    (mul_le_mul_of_nonneg_right (((w.second x).le_opNorm b).trans
      (mul_le_mul_of_nonneg_right hx (norm_nonneg b))) (norm_nonneg a))

/-- The scalar source equation for a bounded weak second jet with prescribed diagonal Gram
matrix. -/
public theorem hessian_q_eq_metric_source [IsFiniteMeasure (volume.restrict (U : Set Plane))]
    (w : WeakJet2 m U) {v : Plane → ℝ} (hv : ContDiff ℝ 2 v)
    (hw : MemLp w.value ∞ (volume.restrict (U : Set Plane)))
    (hP : MemLp w.gradient ∞ (volume.restrict (U : Set Plane)))
    (hB : MemLp w.second ∞ (volume.restrict (U : Set Plane)))
    {Cp Cb : ℝ} (hCp : 0 ≤ Cp) (hCb : 0 ≤ Cb)
    (bP : ∀ᵐ x ∂volume.restrict (U : Set Plane), ‖w.gradient x‖ ≤ Cp)
    (bB : ∀ᵐ x ∂volume.restrict (U : Set Plane), ‖w.second x‖ ≤ Cb)
    (hxx : ∀ᵐ x ∂volume.restrict (U : Set Plane),
      inner ℝ (w.gradient x ex) (w.gradient x ex) = 1 + v x)
    (hyy : ∀ᵐ x ∂volume.restrict (U : Set Plane),
      inner ℝ (w.gradient x ey) (w.gradient x ey) = 1)
    (hxy : ∀ᵐ x ∂volume.restrict (U : Set Plane),
      inner ℝ (w.gradient x ex) (w.gradient x ey) = 0) :
    ∀ᵐ x ∂volume.restrict (U : Set Plane), (w.hessian x).q = -metricYY v x / 2 := by
  exact w.hessian_q_eq_metric_source_of_gramTest hv
    (w.second_eval_memLp_of_bound hB.aestronglyMeasurable bB) hxx hyy hxy
    (w.weak_gramTest hw hP hB hCp hCb bP bB)


end WeakJet2
end C2Riemannian
