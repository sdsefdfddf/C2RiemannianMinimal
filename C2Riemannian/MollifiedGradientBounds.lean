module

public import C2Riemannian.AffineNormalization
public import C2Riemannian.WeakMollificationLimit
public import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Tactic.Ring

/-! # Interior mollification with the same Frobenius gradient bound (M03) -/

set_option autoImplicit false

open Set MeasureTheory TopologicalSpace
open scoped ENNReal

namespace C2Riemannian

variable {m : ℕ}

/-- The two columns of a planar derivative, with their product ℓ² norm. -/
@[expose] public noncomputable def gradientColumns :
    (Plane →L[ℝ] Target m) →L[ℝ] WithLp 2 (Target m × Target m) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (Target m) (Target m)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.apply ℝ (Target m) (EuclideanSpace.single 0 1)).prod
      (ContinuousLinearMap.apply ℝ (Target m) (EuclideanSpace.single 1 1)))

@[simp] public theorem gradientColumns_apply (A : Plane →L[ℝ] Target m) :
    gradientColumns A = WithLp.toLp 2 (A (EuclideanSpace.single 0 1), A (EuclideanSpace.single 1 1)) :=
  rfl

public theorem norm_gradientColumns (A : Plane →L[ℝ] Target m) :
    ‖gradientColumns A‖ = gradHS A := by
  rw [gradientColumns_apply, WithLp.prod_norm_eq_of_L2, gradHS, Fin.sum_univ_two]
  simp only [EuclideanSpace.basisFun_apply]
  rfl

namespace WeakJet2

variable {U : Opens Plane} (w : WeakJet2 m U)

/-- The Hilbert–Schmidt norm of the two-column gradient derivative is the Frobenius norm of the symmetric weak Hessian almost everywhere. -/
public theorem gradHS_second_ae :
    ∀ᵐ x ∂volume.restrict (U : Set Plane),
      gradHS (gradientColumns.comp (w.second x)) = (w.hessian x).frobenius := by
  filter_upwards [w.hessian_xy_ae] with x hxy
  rw [gradHS, Hess3.frobenius, Hess3.frobeniusSq, Fin.sum_univ_two]
  simp only [EuclideanSpace.basisFun_apply, ContinuousLinearMap.comp_apply,
    gradientColumns_apply, WithLp.prod_norm_sq_eq_of_L2]
  change √(‖(w.hessian x).xx‖ ^ 2 +
      ‖w.second x (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)‖ ^ 2 +
      (‖(w.hessian x).xy‖ ^ 2 + ‖(w.hessian x).yy‖ ^ 2)) = _
  rw [← hxy]
  congr 1
  ring

/-- Mollification preserves the bound on the derivative of the Hilbert–Schmidt
gradient field. The almost-everywhere input uses the three symmetric Hessian entries. -/
public theorem norm_gradientColumns_mollify_second_le {r : ℝ≥0∞}
    (hB : MemLp w.second r (volume.restrict (U : Set Plane))) (hr : 1 ≤ r)
    {K : ℝ} (hK : 0 ≤ K)
    (hF : ∀ᵐ x ∂volume.restrict (U : Set Plane), (w.hessian x).frobenius ≤ K)
    (φ : ContDiffBump (0 : Plane)) (x : Plane) :
    ‖gradientColumns.comp (mollify U φ w.second x)‖ ≤ K := by
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro v
  let L : (Plane →L[ℝ] (Plane →L[ℝ] Target m)) →L[ℝ] WithLp 2 (Target m × Target m) :=
    gradientColumns.comp (ContinuousLinearMap.apply ℝ (Plane →L[ℝ] Target m) v)
  have hL : ∀ᵐ y ∂volume.restrict (U : Set Plane), ‖L (w.second y)‖ ≤ K * ‖v‖ := by
    filter_upwards [w.gradHS_second_ae, hF] with y heq hy
    let B := gradientColumns.comp (w.second y)
    have hBnorm : ‖B‖ ≤ K := (opNorm_le_gradHS B).trans (heq.trans_le hy)
    exact (B.le_opNorm v).trans (mul_le_mul_of_nonneg_right hBnorm (norm_nonneg _))
  change ‖L (mollify U φ w.second x)‖ ≤ K * ‖v‖
  have hcomm := mollify_clm (U := U) (f := w.second) hB hr φ L x
  calc
    ‖L (mollify U φ w.second x)‖ = ‖mollify U φ (fun y => L (w.second y)) x‖ :=
      congrArg (fun z : WithLp 2 (Target m × Target m) => ‖z‖) hcomm.symm
    _ ≤ K * ‖v‖ :=
      norm_mollify_le (U := U) (f := fun y => L (w.second y))
        (mul_nonneg hK (norm_nonneg _)) hL φ x

/-- On a convex set with room for the bump, the mollified gradient is
Hilbert–Schmidt Lipschitz with the original Hessian bound. -/
public theorem gradHS_mollify_gradient_sub_le {q r : ℝ≥0∞}
    (hP : MemLp w.gradient q (volume.restrict (U : Set Plane)))
    (hB : MemLp w.second r (volume.restrict (U : Set Plane))) (hq : 1 ≤ q) (hr : 1 ≤ r)
    {K : ℝ} (hK : 0 ≤ K)
    (hF : ∀ᵐ x ∂volume.restrict (U : Set Plane), (w.hessian x).frobenius ≤ K)
    (φ : ContDiffBump (0 : Plane)) {s : Set Plane} (hs : Convex ℝ s)
    (hi : ∀ z ∈ s, Metric.closedBall z φ.rOut ⊆ (U : Set Plane))
    {x y : Plane} (hx : x ∈ s) (hy : y ∈ s) :
    gradHS (mollify U φ w.gradient x - mollify U φ w.gradient y) ≤ K * dist x y := by
  have hd z (hz : z ∈ s) :
      HasFDerivAt (fun z => gradientColumns (mollify U φ w.gradient z))
        (gradientColumns.comp (mollify U φ w.second z)) z :=
    gradientColumns.hasFDerivAt.comp z
      (w.weak_gradient.hasFDerivAt_indicator_convolution_normed hP hB hq hr φ z (hi z hz))
  have h := hs.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hd z hz).differentiableAt)
    (fun z hz => by
      rw [(hd z hz).fderiv]
      exact w.norm_gradientColumns_mollify_second_le hB hr hK hF φ z)
    hy hx
  simpa only [← norm_gradientColumns, map_sub, dist_eq_norm] using h

/-- An essential Hilbert–Schmidt bound on the gradient gives a Lipschitz bound on
the mollified potential over every convex subset of the interior convolution domain. -/
public theorem dist_mollify_value_le {p q : ℝ≥0∞}
    (hw : MemLp w.value p (volume.restrict (U : Set Plane)))
    (hP : MemLp w.gradient q (volume.restrict (U : Set Plane))) (hp : 1 ≤ p) (hq : 1 ≤ q)
    {M : ℝ} (hM : 0 ≤ M)
    (hgrad : ∀ᵐ x ∂volume.restrict (U : Set Plane), gradHS (w.gradient x) ≤ M)
    (φ : ContDiffBump (0 : Plane)) {s : Set Plane} (hs : Convex ℝ s)
    (hi : ∀ z ∈ s, Metric.closedBall z φ.rOut ⊆ (U : Set Plane))
    {x y : Plane} (hx : x ∈ s) (hy : y ∈ s) :
    dist (mollify U φ w.value x) (mollify U φ w.value y) ≤ M * dist x y := by
  have hOp : ∀ᵐ x ∂volume.restrict (U : Set Plane), ‖w.gradient x‖ ≤ M :=
    hgrad.mono fun x hx => (opNorm_le_gradHS _).trans hx
  have hd z (hz : z ∈ s) :
      HasFDerivAt (mollify U φ w.value) (mollify U φ w.gradient z) z :=
    w.weak_value.hasFDerivAt_indicator_convolution_normed hw hP hp hq φ z (hi z hz)
  have h := hs.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hd z hz).differentiableAt)
    (fun z hz => by
      rw [(hd z hz).fderiv]
      exact norm_mollify_le hM hOp φ z)
    hy hx
  simpa only [dist_eq_norm] using h

end WeakJet2
end C2Riemannian

