module

public import C2Riemannian.WeakAnalysis
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Ring

set_option autoImplicit false

open MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions

namespace C2Riemannian

variable {m : ℕ}

private theorem contDiff_lineDeriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Plane → F} {n k : ℕ∞ω} (h : ContDiff ℝ n f)
    (hle : k + 1 ≤ n) (hn : n ≠ 0) (d : Plane) :
    ContDiff ℝ k (fun x => lineDeriv ℝ f x d) := by
  have heq : (fun x => lineDeriv ℝ f x d) = fun x => fderiv ℝ f x d :=
    funext fun x => (h.differentiable hn x).lineDeriv_eq_fderiv
  rw [heq]
  exact (h.fderiv_right hle).clm_apply contDiff_const

private theorem lineDeriv_lineDeriv_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Plane → F} (hf : ContDiff ℝ 2 f) (a b x : Plane) :
    lineDeriv ℝ (fun y => lineDeriv ℝ f y a) x b =
      fderiv ℝ (fderiv ℝ f) x b a := by
  have hdiff := hf.differentiable (by decide)
  have hd := (hf.fderiv_right (m := 1) (by decide)).differentiable_one x
  have heq : (fun y => lineDeriv ℝ f y a) = fun y => fderiv ℝ f y a :=
    funext fun y => (hdiff y).lineDeriv_eq_fderiv
  rw [heq]
  have hcomp := (ContinuousLinearMap.apply ℝ F a).hasFDerivAt.comp x hd.hasFDerivAt
  exact (hcomp.hasLineDerivAt b).lineDeriv

private theorem lineDeriv_comm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Plane → F} (hf : ContDiff ℝ 2 f) (a b : Plane) :
    (fun x => lineDeriv ℝ (fun y => lineDeriv ℝ f y a) x b) =
      fun x => lineDeriv ℝ (fun y => lineDeriv ℝ f y b) x a := by
  funext x
  rw [lineDeriv_lineDeriv_eq hf, lineDeriv_lineDeriv_eq hf]
  exact hf.contDiffAt.isSymmSndFDerivAt (by simp) b a

private theorem lineDeriv_inner {f g : Plane → Target m} {x d : Plane}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    lineDeriv ℝ (fun y => inner ℝ (f y) (g y)) x d =
      inner ℝ (f x) (lineDeriv ℝ g x d) + inner ℝ (lineDeriv ℝ f x d) (g x) := by
  rw [hf.lineDeriv_eq_fderiv, hg.lineDeriv_eq_fderiv]
  exact ((hf.hasFDerivAt.inner ℝ hg.hasFDerivAt).hasLineDerivAt d).lineDeriv

private theorem lineDeriv₂_inner {f g : Plane → Target m}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (a b x : Plane) :
    lineDeriv ℝ (fun z => lineDeriv ℝ (fun y => inner ℝ (f y) (g y)) z a) x b =
      (inner ℝ (f x) (lineDeriv ℝ (fun y => lineDeriv ℝ g y a) x b) +
        inner ℝ (lineDeriv ℝ f x b) (lineDeriv ℝ g x a)) +
      (inner ℝ (lineDeriv ℝ f x a) (lineDeriv ℝ g x b) +
        inner ℝ (lineDeriv ℝ (fun y => lineDeriv ℝ f y a) x b) (g x)) := by
  have df := hf.differentiable (by decide)
  have dg := hg.differentiable (by decide)
  have dfa := (contDiff_lineDeriv hf (k := 1) (by decide) (by decide) a).differentiable_one
  have dga := (contDiff_lineDeriv hg (k := 1) (by decide) (by decide) a).differentiable_one
  have heq : (fun z => lineDeriv ℝ (fun y => inner ℝ (f y) (g y)) z a) =
      fun z => inner ℝ (f z) (lineDeriv ℝ g z a) + inner ℝ (lineDeriv ℝ f z a) (g z) :=
    funext fun z => lineDeriv_inner (df z) (dg z)
  rw [heq]
  have h₁ := ((df x).hasFDerivAt.inner ℝ (dga x).hasFDerivAt).hasLineDerivAt b
  have h₂ := ((dfa x).hasFDerivAt.inner ℝ (dg x).hasFDerivAt).hasLineDerivAt b
  have hsum : HasLineDerivAt ℝ
      (fun z => inner ℝ (f z) (lineDeriv ℝ g z a) + inner ℝ (lineDeriv ℝ f z a) (g z))
      _ x b := h₁.add h₂
  rw [hsum.lineDeriv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, fderivInnerCLM_apply,
    ← (df x).lineDeriv_eq_fderiv, ← (dg x).lineDeriv_eq_fderiv,
    ← (dfa x).lineDeriv_eq_fderiv, ← (dga x).lineDeriv_eq_fderiv]

/-- The classical Cartesian Hessian, with the mixed coefficient taken by differentiating
the first column in the second direction. -/
@[expose] public noncomputable def classicalHessian (W : Plane → Target m) (x : Plane) : Hess3 m :=
  let ex : Plane := EuclideanSpace.single 0 1
  let ey : Plane := EuclideanSpace.single 1 1
  ⟨lineDeriv ℝ (fun z => lineDeriv ℝ W z ex) x ex,
    lineDeriv ℝ (fun z => lineDeriv ℝ W z ex) x ey,
    lineDeriv ℝ (fun z => lineDeriv ℝ W z ey) x ey⟩

/-- The smooth Gram compatibility identity in the two Cartesian directions. -/
public theorem smooth_compatibility {W : Plane → Target m} (hW : ContDiff ℝ 3 W) (x : Plane) :
    let ex : Plane := EuclideanSpace.single 0 1
    let ey : Plane := EuclideanSpace.single 1 1
    let Px := fun z => lineDeriv ℝ W z ex
    let Py := fun z => lineDeriv ℝ W z ey
    lineDeriv ℝ (fun z => lineDeriv ℝ (fun y => inner ℝ (Px y) (Px y)) z ey) x ey +
      lineDeriv ℝ (fun z => lineDeriv ℝ (fun y => inner ℝ (Py y) (Py y)) z ex) x ex -
      2 * lineDeriv ℝ (fun z => lineDeriv ℝ (fun y => inner ℝ (Px y) (Py y)) z ey) x ex =
      -2 * (classicalHessian W x).q := by
  let ex : Plane := EuclideanSpace.single 0 1
  let ey : Plane := EuclideanSpace.single 1 1
  let Px := fun z => lineDeriv ℝ W z ex
  let Py := fun z => lineDeriv ℝ W z ey
  change lineDeriv ℝ (fun z => lineDeriv ℝ (fun y => inner ℝ (Px y) (Px y)) z ey) x ey +
      lineDeriv ℝ (fun z => lineDeriv ℝ (fun y => inner ℝ (Py y) (Py y)) z ex) x ex -
      2 * lineDeriv ℝ (fun z => lineDeriv ℝ (fun y => inner ℝ (Px y) (Py y)) z ey) x ex =
      -2 * (classicalHessian W x).q
  have hPx : ContDiff ℝ 2 Px := contDiff_lineDeriv hW (by decide) (by decide) ex
  have hPy : ContDiff ℝ 2 Py := contDiff_lineDeriv hW (by decide) (by decide) ey
  have hmix : (fun z => lineDeriv ℝ Py z ex) = fun z => lineDeriv ℝ Px z ey :=
    lineDeriv_comm (hW.of_le (by decide)) ey ex
  have hthird :
      (fun z => lineDeriv ℝ (fun y => lineDeriv ℝ Py y ey) z ex) =
        fun z => lineDeriv ℝ (fun y => lineDeriv ℝ Px y ey) z ey := by
    rw [lineDeriv_comm hPy ey ex, hmix]
  rw [lineDeriv₂_inner hPx hPx, lineDeriv₂_inner hPy hPy, lineDeriv₂_inner hPx hPy,
    congrFun hthird x, hmix, congrFun hmix x]
  change _ = -2 * (inner ℝ (lineDeriv ℝ Px x ex) (lineDeriv ℝ Py x ey) -
    inner ℝ (lineDeriv ℝ Px x ey) (lineDeriv ℝ Px x ey))
  rw [real_inner_comm (lineDeriv ℝ (fun y => lineDeriv ℝ Px y ey) x ey) (Px x),
    real_inner_comm (Py x) (lineDeriv ℝ (fun y => lineDeriv ℝ Px y ey) x ex)]
  ring

/-- Two integrations by parts against a compactly supported test on an open set. -/
public theorem integral_lineDeriv₂_mul {U : Opens Plane} {f : Plane → ℝ}
    (hf : ContDiff ℝ 2 f) (a b : Plane) (φ : 𝓓(U, ℝ)) :
    (∫ x in ↑U, φ x * lineDeriv ℝ (fun z => lineDeriv ℝ f z a) x b) =
      ∫ x in ↑U, lineDeriv ℝ (fun z => lineDeriv ℝ (φ : Plane → ℝ) z b) x a * f x := by
  let ψ : 𝓓(U, ℝ) := TestFunction.lineDerivCLM ℝ b φ
  have hψ : (ψ : Plane → ℝ) = fun z => lineDeriv ℝ (φ : Plane → ℝ) z b :=
    funext fun _ => TestFunction.lineDerivCLM_apply_of_le le_top
  have ha := contDiff_lineDeriv hf (k := 1) (by decide) (by decide) a
  have hb := contDiff_lineDeriv ha (k := 0) (by decide) (by decide) b
  have h₁ : TauCeti.HasWeakLineDerivOn volume U f (fun z => lineDeriv ℝ f z a) a :=
    TauCeti.hasWeakLineDerivOn_of_hasLineDerivAt (hf.continuous.continuousOn.locallyIntegrableOn U.isOpen.measurableSet)
      (ha.continuous.continuousOn.locallyIntegrableOn U.isOpen.measurableSet)
      (fun x _ => (hf.differentiable (by decide) x).lineDifferentiableAt.hasLineDerivAt)
  have h₂ : TauCeti.HasWeakLineDerivOn volume U (fun z => lineDeriv ℝ f z a)
      (fun z => lineDeriv ℝ (fun y => lineDeriv ℝ f y a) z b) b :=
    TauCeti.hasWeakLineDerivOn_of_hasLineDerivAt (ha.continuous.continuousOn.locallyIntegrableOn U.isOpen.measurableSet)
      (hb.continuous.continuousOn.locallyIntegrableOn U.isOpen.measurableSet)
      (fun x _ => (ha.differentiable_one x).lineDifferentiableAt.hasLineDerivAt)
  change (∫ x in ↑U, φ x • lineDeriv ℝ (fun z => lineDeriv ℝ f z a) x b) =
    ∫ x in ↑U, lineDeriv ℝ (fun z => lineDeriv ℝ (φ : Plane → ℝ) z b) x a • f x
  rw [TauCeti.setIntegral_smul_eq_integral_smul φ, ← hψ,
    TauCeti.setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul ψ a,
    h₁.integral_lineDeriv_smul_eq_neg_integral_smul ψ, hψ,
    h₂.integral_lineDeriv_smul_eq_neg_integral_smul φ, neg_neg]

/-- The Gram compatibility identity tested on an arbitrary open set against a compactly
supported smooth function. -/
public theorem smooth_compatibility_test {U : Opens Plane} {W : Plane → Target m}
    (hW : ContDiff ℝ 3 W) (φ : 𝓓(U, ℝ)) :
    let ex : Plane := EuclideanSpace.single 0 1
    let ey : Plane := EuclideanSpace.single 1 1
    let Px := fun z => lineDeriv ℝ W z ex
    let Py := fun z => lineDeriv ℝ W z ey
    (-2 * (∫ x in ↑U, φ x * (classicalHessian W x).q) =
      (∫ x in ↑U, lineDeriv ℝ (fun z => lineDeriv ℝ (φ : Plane → ℝ) z ey) x ey *
        inner ℝ (Px x) (Px x)) +
      (∫ x in ↑U, lineDeriv ℝ (fun z => lineDeriv ℝ (φ : Plane → ℝ) z ex) x ex *
        inner ℝ (Py x) (Py x)) -
      2 * (∫ x in ↑U, lineDeriv ℝ (fun z => lineDeriv ℝ (φ : Plane → ℝ) z ey) x ex *
        inner ℝ (Px x) (Py x))) := by
  let ex : Plane := EuclideanSpace.single 0 1
  let ey : Plane := EuclideanSpace.single 1 1
  let Px := fun z => lineDeriv ℝ W z ex
  let Py := fun z => lineDeriv ℝ W z ey
  let Gxx := fun z => inner ℝ (Px z) (Px z)
  let Gyy := fun z => inner ℝ (Py z) (Py z)
  let Gxy := fun z => inner ℝ (Px z) (Py z)
  change _ =
      (∫ x in ↑U, lineDeriv ℝ (fun z => lineDeriv ℝ (φ : Plane → ℝ) z ey) x ey * Gxx x) +
      (∫ x in ↑U, lineDeriv ℝ (fun z => lineDeriv ℝ (φ : Plane → ℝ) z ex) x ex * Gyy x) -
      2 * (∫ x in ↑U, lineDeriv ℝ (fun z => lineDeriv ℝ (φ : Plane → ℝ) z ey) x ex * Gxy x)
  have hPx : ContDiff ℝ 2 Px := contDiff_lineDeriv hW (by decide) (by decide) ex
  have hPy : ContDiff ℝ 2 Py := contDiff_lineDeriv hW (by decide) (by decide) ey
  have hGxx : ContDiff ℝ 2 Gxx := hPx.inner _ hPx
  have hGyy : ContDiff ℝ 2 Gyy := hPy.inner _ hPy
  have hGxy : ContDiff ℝ 2 Gxy := hPx.inner _ hPy
  have htest : ContDiff ℝ 2 (φ : Plane → ℝ) := φ.contDiff.of_le (by simp)
  simp_rw [congrFun (lineDeriv_comm htest ey ex)]
  rw [← integral_lineDeriv₂_mul hGxx ey ey φ, ← integral_lineDeriv₂_mul hGyy ex ex φ,
    ← integral_lineDeriv₂_mul hGxy ey ex φ]
  have hi {f : Plane → ℝ} (hf : ContDiff ℝ 2 f) (a b : Plane) :
      IntegrableOn (fun x => φ x * lineDeriv ℝ (fun z => lineDeriv ℝ f z a) x b)
        (U : Set Plane) volume := by
    have hfirst := contDiff_lineDeriv hf (k := 1) (by decide) (by decide) a
    have hsecond := contDiff_lineDeriv hfirst (k := 0) (by decide) (by decide) b
    exact (TauCeti.integrable_smul_of_locallyIntegrableOn
      (hsecond.continuous.continuousOn.locallyIntegrableOn U.isOpen.measurableSet) φ).integrableOn
  have hsplit := integral_sub ((hi hGxx ey ey).add (hi hGyy ex ex))
    ((hi hGxy ey ex).const_mul 2)
  simp only [Pi.add_apply] at hsplit
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hi hGxx ey ey) (hi hGyy ex ex), ← hsplit]
  apply integral_congr_ae
  filter_upwards with x
  have hpoint := smooth_compatibility hW x
  change lineDeriv ℝ (fun z => lineDeriv ℝ Gxx z ey) x ey +
    lineDeriv ℝ (fun z => lineDeriv ℝ Gyy z ex) x ex -
    2 * lineDeriv ℝ (fun z => lineDeriv ℝ Gxy z ey) x ex =
    -2 * (classicalHessian W x).q at hpoint
  calc
    _ = φ x * (-2 * (classicalHessian W x).q) := by ring
    _ = _ := by rw [← hpoint]; ring

end C2Riemannian





