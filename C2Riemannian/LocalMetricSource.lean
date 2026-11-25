module

public import C2Riemannian.IsometryInChart
public import C2Riemannian.LocalSmoothCompatibility
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open MeasureTheory Filter Set TopologicalSpace
open scoped ContDiff Distributions

namespace C2Riemannian.WeakJet2

variable {m : ℕ} {U : Opens Plane}

private theorem continuousOn_metricYY {v : Plane → ℝ} (hv : ContDiffOn ℝ 2 v (U : Set Plane)) :
    ContinuousOn (metricYY v) (U : Set Plane) := by
  have hfirst : ContDiffOn ℝ 1 (fun x => lineDeriv ℝ v x ey) (U : Set Plane) := by
    refine ((hv.fderiv_of_isOpen U.isOpen (by decide : (1 : ℕ∞ω) + 1 ≤ 2)).clm_apply
      (contDiffOn_const (c := ey))).congr ?_
    intro x hx
    exact ((hv.differentiableOn (by decide) x hx).differentiableAt
      (U.isOpen.mem_nhds hx)).lineDeriv_eq_fderiv
  refine (((hfirst.fderiv_of_isOpen U.isOpen (by decide : (0 : ℕ∞ω) + 1 ≤ 1)).clm_apply
    (contDiffOn_const (c := ey))).continuousOn).congr ?_
  intro x hx
  exact ((hfirst.differentiableOn (by decide) x hx).differentiableAt
    (U.isOpen.mem_nhds hx)).lineDeriv_eq_fderiv

/-- The second directional derivative of a C² metric coefficient is continuous
on its domain. -/
public theorem metricYY_continuousOn {v : Plane → ℝ} (hv : ContDiffOn ℝ 2 v (U : Set Plane)) :
    ContinuousOn (metricYY v) (U : Set Plane) :=
  continuousOn_metricYY hv

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

/-- The scalar source equation for a coefficient of class C² on the chart. -/
public theorem hessian_q_eq_metric_source_on_of_tests
    (w : WeakJet2 m U) {v : Plane → ℝ} (hv : ContDiffOn ℝ 2 v (U : Set Plane))
    (hq : LocallyIntegrableOn (fun x => (w.hessian x).q) U volume)
    (hIso : w.IsometryInChart v)
    (htest : ∀ φ : 𝓓(U, ℝ),
      -2 * (∫ x in ↑U, φ x * (w.hessian x).q) =
        (∫ x in ↑U, testSecond ey ey φ x * inner ℝ (w.gradient x ex) (w.gradient x ex)) +
        (∫ x in ↑U, testSecond ex ex φ x * inner ℝ (w.gradient x ey) (w.gradient x ey)) -
        2 * (∫ x in ↑U, testSecond ey ex φ x * inner ℝ (w.gradient x ex) (w.gradient x ey))) :
    ∀ᵐ x ∂volume.restrict (U : Set Plane), (w.hessian x).q = -metricYY v x / 2 := by
  have hg : LocallyIntegrableOn (fun x => -metricYY v x / 2) U volume :=
    ((continuousOn_metricYY hv).neg.div_const 2).locallyIntegrableOn U.isOpen.measurableSet
  have hxx := hIso.mono fun _ h => h.1
  have hyy := hIso.mono fun _ h => h.2.1
  have hxy := hIso.mono fun _ h => h.2.2
  apply ae_eq_of_test_integrals hq hg
  intro φ
  let ψ := testSecond ey ey φ
  have hfirst : (∫ x in ↑U, testSecond ey ey φ x * inner ℝ (w.gradient x ex) (w.gradient x ex)) =
      ∫ x in ↑U, φ x * metricYY v x := by
    have hi₁ : IntegrableOn (ψ : Plane → ℝ) (U : Set Plane) volume :=
      (ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport).integrableOn
    have hi₂ : IntegrableOn (fun x => ψ x * v x) (U : Set Plane) volume :=
      (TauCeti.integrable_smul_of_locallyIntegrableOn
        (hv.continuousOn.locallyIntegrableOn U.isOpen.measurableSet) ψ).integrableOn
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
        exact (integral_lineDeriv₂_mul_on hv ey ey φ).symm
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

end C2Riemannian.WeakJet2

