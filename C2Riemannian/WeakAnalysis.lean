module

public import C2Riemannian.HessianAlgebra
public import TauCeti.Analysis.Sobolev.Mollification.Interior
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

set_option autoImplicit false

open MeasureTheory Set TopologicalSpace
open scoped ContDiff Convolution Distributions ENNReal Topology

namespace C2Riemannian

variable {m : ℕ}

/-- Test functions determine a locally integrable vector field on the restricted measure. -/
public theorem ae_eq_of_test_integrals {U : Opens Plane} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {f g : Plane → F}
    (hf : LocallyIntegrableOn f U volume) (hg : LocallyIntegrableOn g U volume)
    (h : ∀ φ : 𝓓(U, ℝ), (∫ x in ↑U, φ x • f x) =
      ∫ x in ↑U, φ x • g x) :
    f =ᵐ[volume.restrict (U : Set Plane)] g := by
  have hz := U.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hf.sub hg)
  rw [Filter.EventuallyEq, ae_restrict_iff' U.isOpen.measurableSet]
  refine (hz ?_).mono fun x hx hxU => sub_eq_zero.mp (hx hxU)
  intro φ hd hc hs
  let test : 𝓓(U, ℝ) := ⟨φ, hd, hc, hs⟩
  have he := h test
  rw [TauCeti.setIntegral_smul_eq_integral_smul test,
    TauCeti.setIntegral_smul_eq_integral_smul test] at he
  change (∫ x, φ x • f x) = ∫ x, φ x • g x at he
  simp only [Pi.sub_apply, smul_sub]
  have hfi : Integrable (fun x => φ x • f x) volume :=
    TauCeti.integrable_smul_of_locallyIntegrableOn hf test
  have hgi : Integrable (fun x => φ x • g x) volume :=
    TauCeti.integrable_smul_of_locallyIntegrableOn hg test
  rw [integral_sub hfi hgi, he, sub_self]

/-- A potential and two successive weak Fréchet derivative fields on an open planar set. -/
public structure WeakJet2 (m : ℕ) (U : Opens Plane) where
  value : Plane → Target m
  gradient : Plane → Plane →L[ℝ] Target m
  second : Plane → Plane →L[ℝ] (Plane →L[ℝ] Target m)
  weak_value : TauCeti.HasWeakFDerivOn volume U value gradient
  weak_gradient : TauCeti.HasWeakFDerivOn volume U gradient second

namespace WeakJet2

variable {U V : Opens Plane} (w : WeakJet2 m U)

/-- Restriction of the weak derivative relations to an open subset. -/
@[expose] public def restrict (h : V ≤ U) : WeakJet2 m V where
  value := w.value
  gradient := w.gradient
  second := w.second
  weak_value := w.weak_value.mono h
  weak_gradient := w.weak_gradient.mono h

variable (v u : Plane)

/-- Each column of the first derivative has the indicated directional weak derivative. -/
public theorem weak_component :
    TauCeti.HasWeakLineDerivOn volume U (fun x => w.gradient x u)
      (fun x => w.second x v u) v :=
  (w.weak_gradient.hasWeakLineDerivOn v).clm_comp
    (ContinuousLinearMap.apply ℝ (Target m) u)

/-- Two integrations by parts move the derivatives onto the compactly supported test. -/
public theorem integral_second_smul (φ : 𝓓(U, ℝ)) :
    (∫ x in ↑U, φ x • w.second x v u) =
      ∫ x in ↑U,
        lineDeriv ℝ (fun y => lineDeriv ℝ (φ : Plane → ℝ) y v) x u • w.value x := by
  let ψ : 𝓓(U, ℝ) := TestFunction.lineDerivCLM ℝ v φ
  have hψ : (ψ : Plane → ℝ) = fun y => lineDeriv ℝ (φ : Plane → ℝ) y v :=
    funext fun _ => TestFunction.lineDerivCLM_apply_of_le le_top
  have h₁ := (w.weak_component v u).integral_lineDeriv_smul_eq_neg_integral_smul φ
  have h₂ := (w.weak_value.hasWeakLineDerivOn u).integral_lineDeriv_smul_eq_neg_integral_smul ψ
  rw [TauCeti.setIntegral_smul_eq_integral_smul φ, ← hψ,
    TauCeti.setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul ψ u, h₂, hψ, h₁, neg_neg]

private theorem test_lineDeriv_comm (φ : 𝓓(U, ℝ)) (v u x : Plane) :
    lineDeriv ℝ (fun y => lineDeriv ℝ (φ : Plane → ℝ) y v) x u =
      lineDeriv ℝ (fun y => lineDeriv ℝ (φ : Plane → ℝ) y u) x v := by
  have hφ : ContDiff ℝ 2 (φ : Plane → ℝ) := φ.contDiff.of_le (by simp)
  have hdiff : Differentiable ℝ (φ : Plane → ℝ) := hφ.differentiable (by decide)
  have hsecond : DifferentiableAt ℝ (fderiv ℝ (φ : Plane → ℝ)) x :=
    (hφ.fderiv_right (m := 1) (by decide)).differentiable_one x
  have heq (d : Plane) : (fun y => lineDeriv ℝ (φ : Plane → ℝ) y d) =
      fun y => fderiv ℝ (φ : Plane → ℝ) y d :=
    funext fun y => (hdiff y).lineDeriv_eq_fderiv
  rw [heq v, heq u]
  have hd (a b : Plane) :
      lineDeriv ℝ (fun y => fderiv ℝ (φ : Plane → ℝ) y a) x b =
        fderiv ℝ (fderiv ℝ (φ : Plane → ℝ)) x b a :=
    (((ContinuousLinearMap.apply ℝ ℝ a).hasFDerivAt.comp x hsecond.hasFDerivAt).hasLineDerivAt b).lineDeriv
  rw [hd v u, hd u v]
  exact hφ.contDiffAt.isSymmSndFDerivAt (by simp) u v

/-- Mixed weak derivatives coincide almost everywhere on the open set. -/
public theorem second_symm_ae :
    ∀ᵐ x ∂volume.restrict (U : Set Plane), w.second x v u = w.second x u v := by
  apply ae_eq_of_test_integrals (w.weak_component v u).locallyIntegrableOn_deriv
    (w.weak_component u v).locallyIntegrableOn_deriv
  intro φ
  rw [w.integral_second_smul v u φ, w.integral_second_smul u v φ]
  exact integral_congr_ae (Filter.Eventually.of_forall
    fun x => congrArg (· • w.value x) (test_lineDeriv_comm φ v u x))

/-- The three Cartesian coefficients of the weak Hessian in the standard orthonormal basis. -/
@[expose] public noncomputable def hessian (x : Plane) : Hess3 m :=
  let ex : Plane := EuclideanSpace.single 0 1
  let ey : Plane := EuclideanSpace.single 1 1
  ⟨w.second x ex ex, w.second x ey ex, w.second x ey ey⟩

/-- The alternate mixed coefficient represents the same field almost everywhere. -/
public theorem hessian_xy_ae :
    ∀ᵐ x ∂volume.restrict (U : Set Plane),
      (w.hessian x).xy = w.second x (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1) :=
  w.second_symm_ae (EuclideanSpace.single 1 1) (EuclideanSpace.single 0 1)

/-- The weak first and second derivative fields are determined by the potential. -/
public theorem derivatives_ae_eq (w' : WeakJet2 m U)
    (h : w.value =ᵐ[volume.restrict (U : Set Plane)] w'.value) :
    w.gradient =ᵐ[volume.restrict (U : Set Plane)] w'.gradient ∧
      w.second =ᵐ[volume.restrict (U : Set Plane)] w'.second := by
  have hp := (w.weak_value.congr_ae h).ae_eq w'.weak_value
  exact ⟨hp, (w.weak_gradient.congr_ae hp).ae_eq w'.weak_gradient⟩

/-- Mollification of the zero extension by a normalized smooth bump. -/
@[expose] public noncomputable def mollify {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (U : Opens Plane) (φ : ContDiffBump (0 : Plane)) (f : Plane → F) : Plane → F :=
  ((U : Set Plane).indicator f) ⋆[
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip, volume] φ.normed volume

/-- The zero-extended field becomes smooth after mollification. -/
public theorem contDiff_mollify {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Plane → F} {p : ℝ≥0∞}
    (hf : MemLp f p (volume.restrict (U : Set Plane))) (hp : 1 ≤ p)
    (φ : ContDiffBump (0 : Plane)) : ContDiff ℝ ∞ (mollify U φ f) := by
  have hext : MemLp ((U : Set Plane).indicator f) p volume :=
    (memLp_indicator_iff_restrict U.isOpen.measurableSet.nullMeasurableSet).2 hf
  exact φ.hasCompactSupport_normed.contDiff_convolution_right _ (hext.locallyIntegrable hp)
    φ.contDiff_normed

/-- One bump and one zero-extension domain identify both successive interior derivatives. -/
public theorem mollify_derivatives {p q r : ℝ≥0∞}
    (hw : MemLp w.value p (volume.restrict (U : Set Plane)))
    (hP : MemLp w.gradient q (volume.restrict (U : Set Plane)))
    (hB : MemLp w.second r (volume.restrict (U : Set Plane)))
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (φ : ContDiffBump (0 : Plane)) (x : Plane)
    (hx : Metric.closedBall x φ.rOut ⊆ (U : Set Plane)) :
    HasFDerivAt (mollify U φ w.value) (mollify U φ w.gradient x) x ∧
      HasFDerivAt (mollify U φ w.gradient) (mollify U φ w.second x) x :=
  ⟨w.weak_value.hasFDerivAt_indicator_convolution_normed hw hP hp hq φ x hx,
    w.weak_gradient.hasFDerivAt_indicator_convolution_normed hP hB hq hr φ x hx⟩

/-- On the interior convolution domain, the second field is the derivative of
the classical derivative of the same potential. -/
public theorem mollify_second {p q r : ℝ≥0∞}
    (hw : MemLp w.value p (volume.restrict (U : Set Plane)))
    (hP : MemLp w.gradient q (volume.restrict (U : Set Plane)))
    (hB : MemLp w.second r (volume.restrict (U : Set Plane)))
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (φ : ContDiffBump (0 : Plane)) (x : Plane)
    (hx : Metric.closedBall x φ.rOut ⊆ (U : Set Plane)) :
    HasFDerivAt (fderiv ℝ (mollify U φ w.value)) (mollify U φ w.second x) x := by
  have hn : ∀ᶠ y in 𝓝 x, Metric.closedBall y φ.rOut ⊆ (U : Set Plane) := by
    have hcompact : IsCompact (Metric.closedBall (0 : Plane) φ.rOut) :=
      isCompact_closedBall _ _
    have hnear : ∀ᶠ y in 𝓝 x, ∀ z ∈ Metric.closedBall (0 : Plane) φ.rOut, y + z ∈ (U : Set Plane) := by
      apply hcompact.eventually_forall_of_forall_eventually
      intro z hz
      apply (continuous_fst.add continuous_snd).continuousAt.preimage_mem_nhds
      apply U.isOpen.mem_nhds
      change x + z ∈ (U : Set Plane)
      apply hx
      simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero] using hz
    filter_upwards [hnear] with y hy z hz
    have hsub : z - y ∈ Metric.closedBall (0 : Plane) φ.rOut := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hz
    simpa only [add_comm y, sub_add_cancel] using hy (z - y) hsub
  exact (w.mollify_derivatives hw hP hB hp hq hr φ x hx).2.congr_of_eventuallyEq
    (hn.mono fun y hy => (w.mollify_derivatives hw hP hB hp hq hr φ y hy).1.fderiv)

end WeakJet2
end C2Riemannian







