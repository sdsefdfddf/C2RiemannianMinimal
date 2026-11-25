module

public import C2Riemannian.WeakCompatibilityLimit
public import C2Riemannian.WeakMollificationBridge
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false

open MeasureTheory Set Filter TopologicalSpace
open scoped ContDiff Distributions Topology

namespace C2Riemannian
namespace WeakJet2

public noncomputable abbrev ex : Plane := EuclideanSpace.single 0 1
public noncomputable abbrev ey : Plane := EuclideanSpace.single 1 1

variable {m : ℕ} {U : Opens Plane}

private noncomputable def testFirst (v : Plane) (φ : 𝓓(U, ℝ)) : 𝓓(U, ℝ) :=
  TestFunction.lineDerivCLM ℝ v φ

/-- The derivative of a test first in direction `v`, then in direction `u`. -/
public noncomputable def testSecond (v u : Plane) (φ : 𝓓(U, ℝ)) : 𝓓(U, ℝ) :=
  testFirst u (testFirst v φ)

private theorem testFirst_apply (v : Plane) (φ : 𝓓(U, ℝ)) (x : Plane) :
    testFirst v φ x = lineDeriv ℝ (φ : Plane → ℝ) x v :=
  TestFunction.lineDerivCLM_apply_of_le le_top

public theorem testSecond_apply (v u : Plane) (φ : 𝓓(U, ℝ)) (x : Plane) :
    testSecond v u φ x = lineDeriv ℝ (fun y => lineDeriv ℝ (φ : Plane → ℝ) y v) x u := by
  unfold testSecond
  rw [testFirst_apply]
  congr 3
  exact funext (testFirst_apply v φ)

private theorem tsupport_testFirst_subset (v : Plane) (φ : 𝓓(U, ℝ)) :
    tsupport (testFirst v φ : Plane → ℝ) ⊆ tsupport (φ : Plane → ℝ) := by
  have h : (testFirst v φ : Plane → ℝ) = fun x => fderiv ℝ (φ : Plane → ℝ) x v :=
    funext fun x => (testFirst_apply v φ x).trans
      ((φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv)
  rw [h]
  exact tsupport_fderiv_apply_subset ℝ v

/-- Both derivatives of a test remain supported in the support of the original test. -/
public theorem tsupport_testSecond_subset (v u : Plane) (φ : 𝓓(U, ℝ)) :
    tsupport (testSecond v u φ : Plane → ℝ) ⊆ tsupport (φ : Plane → ℝ) :=
  (tsupport_testFirst_subset u (testFirst v φ)).trans (tsupport_testFirst_subset v φ)

private theorem integral_mul_eq_of_tsupport {ψ f g : Plane → ℝ}
    (h : EqOn f g (tsupport ψ)) :
    (∫ x in ↑U, ψ x * f x) = ∫ x in ↑U, ψ x * g x := by
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ tsupport ψ
  · rw [h hx]
  · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]

private theorem gramTest_of_support_fields
    (W : Plane → Target m) (P : Plane → Plane →L[ℝ] Target m)
    (B : Plane → Plane →L[ℝ] (Plane →L[ℝ] Target m))
    (φ : 𝓓(U, ℝ)) (hW : ContDiff ℝ 3 W) (hBc : Continuous B)
    (hPfit : ∀ v : Plane, EqOn (fun x => lineDeriv ℝ W x v) (fun x => P x v)
      (tsupport (φ : Plane → ℝ)))
    (hBfit : EqOn (classicalHessian W)
      (fun x => (⟨B x ex ex, B x ey ex, B x ey ey⟩ : Hess3 m)) (tsupport (φ : Plane → ℝ))) :
    gramTest (volume.restrict (U : Set Plane)) φ
      (testSecond ex ex φ) (testSecond ey ex φ) (testSecond ey ey φ)
      (fun x => P x ex) (fun x => P x ey)
      (fun x => B x ex ex) (fun x => B x ey ex) (fun x => B x ey ey) := by
  have hs := smooth_compatibility_test hW φ
  have hq_eq : (∫ x in ↑U, φ x * (classicalHessian W x).q) =
      ∫ x in ↑U, φ x * (inner ℝ (B x ex ex) (B x ey ey) - inner ℝ (B x ey ex) (B x ey ex)) :=
    integral_mul_eq_of_tsupport fun x hx => by rw [hBfit hx]; rfl
  have hG (v u : Plane) : EqOn (fun x => inner ℝ (lineDeriv ℝ W x v) (lineDeriv ℝ W x u))
      (fun x => inner ℝ (P x v) (P x u)) (tsupport (φ : Plane → ℝ)) :=
    fun x hx => congrArg₂ (inner ℝ) (hPfit v hx) (hPfit u hx)
  have htest (v u a b : Plane) :
      (∫ x in ↑U, testSecond v u φ x * inner ℝ (lineDeriv ℝ W x a) (lineDeriv ℝ W x b)) =
      ∫ x in ↑U, testSecond v u φ x * inner ℝ (P x a) (P x b) :=
    integral_mul_eq_of_tsupport ((hG a b).mono (tsupport_testSecond_subset v u φ))
  have hBc' (a b : Plane) : Continuous (fun x => B x a b) :=
    (hBc.clm_apply continuous_const).clm_apply continuous_const
  have hInt (v₁ u₁ v₂ u₂ : Plane) :
      IntegrableOn (fun x => φ x * inner ℝ (B x v₁ u₁) (B x v₂ u₂)) (U : Set Plane) volume :=
    (φ.contDiff.continuous.mul ((hBc' v₁ u₁).inner (hBc' v₂ u₂))).integrable_of_hasCompactSupport
      φ.hasCompactSupport.mul_right |>.integrableOn
  change -2 * (∫ x in ↑U, φ x * (classicalHessian W x).q) =
    (∫ x in ↑U, lineDeriv ℝ (fun z => lineDeriv ℝ (φ : Plane → ℝ) z ey) x ey *
      inner ℝ (lineDeriv ℝ W x ex) (lineDeriv ℝ W x ex)) +
    (∫ x in ↑U, lineDeriv ℝ (fun z => lineDeriv ℝ (φ : Plane → ℝ) z ex) x ex *
      inner ℝ (lineDeriv ℝ W x ey) (lineDeriv ℝ W x ey)) -
    2 * (∫ x in ↑U, lineDeriv ℝ (fun z => lineDeriv ℝ (φ : Plane → ℝ) z ey) x ex *
      inner ℝ (lineDeriv ℝ W x ex) (lineDeriv ℝ W x ey)) at hs
  have hTestEq (v u a b : Plane) :
      (∫ x in ↑U, lineDeriv ℝ (fun z => lineDeriv ℝ (φ : Plane → ℝ) z v) x u *
        inner ℝ (lineDeriv ℝ W x a) (lineDeriv ℝ W x b)) =
      ∫ x in ↑U, testSecond v u φ x * inner ℝ (P x a) (P x b) := by
    refine (integral_congr_ae ?_).trans (htest v u a b)
    exact Eventually.of_forall fun x =>
      congrArg (· * inner ℝ (lineDeriv ℝ W x a) (lineDeriv ℝ W x b))
        (testSecond_apply v u φ x).symm
  rw [hq_eq, hTestEq ey ey ex ex, hTestEq ex ex ey ey, hTestEq ey ex ex ey] at hs
  have hsplit :
      (∫ x in ↑U, φ x * (inner ℝ (B x ex ex) (B x ey ey) - inner ℝ (B x ey ex) (B x ey ex))) =
        (∫ x in ↑U, φ x * inner ℝ (B x ex ex) (B x ey ey)) -
          (∫ x in ↑U, φ x * inner ℝ (B x ey ex) (B x ey ex)) := by
    simpa only [mul_sub] using integral_sub (hInt ex ex ey ey) (hInt ey ex ey ex)
  rw [hsplit] at hs
  exact hs

/-- The Gram test identity holds for a common mollified potential and its projected
weak derivative fields once the kernel fits around the support of the test. -/
public theorem gramTest_mollify_eventually {ι : Type*} {l : Filter ι}
    (w : WeakJet2 m U) {p q r : ENNReal}
    (hw : MemLp w.value p (volume.restrict (U : Set Plane)))
    (hP : MemLp w.gradient q (volume.restrict (U : Set Plane)))
    (hB : MemLp w.second r (volume.restrict (U : Set Plane)))
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (ρ : ι → ContDiffBump (0 : Plane))
    (hρ : Tendsto (fun i => (ρ i).rOut) l (𝓝 0)) (φ : 𝓓(U, ℝ)) :
    ∀ᶠ i in l, gramTest (volume.restrict (U : Set Plane)) φ
      (testSecond ex ex φ) (testSecond ey ex φ) (testSecond ey ey φ)
      (fun x => mollify U (ρ i) w.gradient x ex) (fun x => mollify U (ρ i) w.gradient x ey)
      (fun x => mollify U (ρ i) w.second x ex ex) (fun x => mollify U (ρ i) w.second x ey ex)
      (fun x => mollify U (ρ i) w.second x ey ey) := by
  obtain ⟨δ, hδ, hthick⟩ := φ.hasCompactSupport.exists_cthickening_subset_open
    U.isOpen φ.tsupport_subset
  have hsmall : ∀ᶠ i in l, (ρ i).rOut < δ := hρ.eventually (gt_mem_nhds hδ)
  filter_upwards [hsmall] with i hi
  let W := mollify U (ρ i) w.value
  let P := mollify U (ρ i) w.gradient
  let B := mollify U (ρ i) w.second
  have hFit {x : Plane} (hx : x ∈ tsupport (φ : Plane → ℝ)) :
      Metric.closedBall x (ρ i).rOut ⊆ (U : Set Plane) :=
    (Metric.closedBall_subset_closedBall hi.le).trans
      ((Metric.closedBall_subset_cthickening hx δ).trans hthick)
  have hPfit (v : Plane) : EqOn (fun x => lineDeriv ℝ W x v) (fun x => P x v)
      (tsupport (φ : Plane → ℝ)) :=
    fun x hx => w.lineDeriv_mollify hw hP hB hp hq hr (ρ i) x v (hFit hx)
  have hBfit : EqOn (classicalHessian W)
      (fun x => (⟨B x ex ex, B x ey ex, B x ey ey⟩ : Hess3 m)) (tsupport (φ : Plane → ℝ)) :=
    fun x hx => w.classicalHessian_mollify hw hP hB hp hq hr (ρ i) x (hFit hx)
  exact gramTest_of_support_fields W P B φ
    ((contDiff_mollify hw hp (ρ i)).of_le (by simp)) (contDiff_mollify hB hr (ρ i)).continuous
    hPfit hBfit
end WeakJet2
end C2Riemannian




