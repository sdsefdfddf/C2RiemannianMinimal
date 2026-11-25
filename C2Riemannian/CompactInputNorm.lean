module

public import C2Riemannian.C2DiskBanach
public import C2Riemannian.AffineNormalization
public import C2Riemannian.QuantitativeCutoff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology BigOperators BoundedContinuousFunction

namespace C2Riemannian

private theorem scalar_gradHS_eq_norm (A : Plane →L[ℝ] ℝ) : gradHS A = ‖A‖ := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  change √(∑ i : Fin 2, ‖A (b i)‖ ^ 2) = ‖A‖
  simp only [Real.norm_eq_abs, sq_abs]
  rw [← b.norm_dual A, Real.sqrt_sq (norm_nonneg _)]

private theorem tensorHS_two_eq_gradHS_fderiv (f : Plane → ℝ) (x : Plane) :
    tensorHS (iteratedFDeriv ℝ 2 f x) = gradHS (fderiv ℝ (fderiv ℝ f) x) := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  let A := fderiv ℝ (fderiv ℝ f) x
  rw [tensorHS_eq_sqrt_sum]
  simp only [iteratedFDeriv_two_apply]
  change √(∑ w : Fin 2 → Fin 2, ‖A (b (w 0)) (b (w 1))‖ ^ 2) =
    √(∑ i : Fin 2, ‖A (b i)‖ ^ 2)
  congr 1
  calc
    _ = ∑ ij : Fin 2 × Fin 2, ‖A (b ij.1) (b ij.2)‖ ^ 2 := by
      apply Fintype.sum_equiv (finTwoArrowEquiv (Fin 2))
      intro w
      rfl
    _ = ∑ i : Fin 2, ∑ j : Fin 2, ‖A (b i) (b j)‖ ^ 2 :=
      Fintype.sum_prod_type _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Real.norm_eq_abs, sq_abs]
      exact (b.norm_dual (A (b i))).symm

/-- Compact support in the open unit disk and a unit Hessian bound imply the
pointwise bounds needed for the maximum C² norm on the closed unit disk. -/
public theorem compact_input_value_gradient_bounds {f : Plane → ℝ}
    (hf : ContDiff ℝ 2 f) (hSupp : tsupport f ⊆ Metric.ball (0 : Plane) 1)
    (hHess : ∀ x ∈ Metric.closedBall (0 : Plane) 1,
      tensorHS (iteratedFDeriv ℝ 2 f x) ≤ 1)
    (x : Plane) (hx : x ∈ Metric.closedBall (0 : Plane) 1) :
    ‖f x‖ ≤ 2 ∧ ‖fderiv ℝ f x‖ ≤ 2 := by
  let D := Metric.closedBall (0 : Plane) 1
  let p : Plane := EuclideanSpace.single 0 1
  have hpn : ‖p‖ = 1 := by simp [p]
  have hp : p ∈ D := by simp [D, Metric.mem_closedBall, dist_zero_right, hpn]
  have hp' : p ∉ tsupport f := by
    intro h
    have hball := hSupp h
    rw [Metric.mem_ball, dist_zero_right, hpn] at hball
    exact (lt_irrefl _ hball)
  have hpNear : f =ᶠ[𝓝 p] 0 := notMem_tsupport_iff_eventuallyEq.mp hp'
  have hpF : f p = 0 := hpNear.eq_of_nhds
  have hpD : fderiv ℝ f p = 0 := by simpa using hpNear.fderiv_eq (𝕜 := ℝ)
  have hd : Differentiable ℝ f := hf.differentiable (by decide)
  have hc₁ : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by decide)
  have hLip : ∀ y ∈ D, ∀ z ∈ D, gradHS (fderiv ℝ f y - fderiv ℝ f z) ≤ 1 * dist y z := by
    intro y hy z hz
    rw [scalar_gradHS_eq_norm, dist_eq_norm]
    apply (convex_closedBall (0 : Plane) (1 : ℝ)).norm_image_sub_le_of_norm_fderiv_le
      (fun u _ => hc₁.differentiable_one u) _ hz hy
    intro u hu
    apply (opNorm_le_gradHS _).trans
    rw [← tensorHS_two_eq_gradHS_fderiv]
    exact hHess u hu
  have hDist : dist x p ≤ 2 := by
    have hx' : dist x (0 : Plane) ≤ 1 := Metric.mem_closedBall.mp hx
    have hp' : dist (0 : Plane) p = 1 := by rw [dist_comm, dist_zero_right, hpn]
    linarith only [dist_triangle x (0 : Plane) p, hx', hp']
  have hVal := normalized_bounds (convex_closedBall (0 : Plane) (1 : ℝ)) hp
    (fun y _ => hd y) hc₁.continuous.continuousOn hLip hx
  rw [show normalize_height f p x = f x by simp [normalize_height, hpF, hpD]] at hVal
  have hGrad := hLip x hx p hp
  rw [hpD, sub_zero, scalar_gradHS_eq_norm] at hGrad
  constructor
  · have hSq := pow_le_pow_left₀ (dist_nonneg (x := x) (y := p)) hDist 2
    nlinarith only [hVal, hSq]
  · exact (by simpa only [one_mul] using hGrad : ‖fderiv ℝ f x‖ ≤ dist x p).trans hDist

@[expose] public noncomputable def gradientVector :
    (Plane →L[ℝ] ℝ) →L[ℝ] Plane :=
  (InnerProductSpace.toDual ℝ Plane).symm.toContinuousLinearEquiv.toContinuousLinearMap

private theorem gradientVector_norm (A : Plane →L[ℝ] ℝ) : ‖gradientVector A‖ = ‖A‖ :=
  (InnerProductSpace.toDual ℝ Plane).symm.norm_map A

public theorem gradientVector_innerSL (A : Plane →L[ℝ] ℝ) :
    innerSL ℝ (gradientVector A) = A :=
  (InnerProductSpace.toDual ℝ Plane).apply_symm_apply A

public noncomputable abbrev standardBasis := EuclideanSpace.basisFun (Fin 2) ℝ

@[expose] public noncomputable def hessianVector (B : Plane →L[ℝ] (Plane →L[ℝ] ℝ)) : DiskHessian :=
  WithLp.toLp 2 fun ij => B (standardBasis ij.2) (standardBasis ij.1)

private theorem hessianVector_norm (f : Plane → ℝ) (x : Plane) :
    ‖hessianVector (fderiv ℝ (fderiv ℝ f) x)‖ = tensorHS (iteratedFDeriv ℝ 2 f x) := by
  let B := fderiv ℝ (fderiv ℝ f) x
  rw [tensorHS_eq_sqrt_sum]
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [iteratedFDeriv_two_apply]
  change (∑ ij : Fin 2 × Fin 2, ‖B (standardBasis ij.2) (standardBasis ij.1)‖ ^ 2) =
    ∑ w : Fin 2 → Fin 2, ‖B (standardBasis (w 0)) (standardBasis (w 1))‖ ^ 2
  symm
  apply Fintype.sum_equiv ((finTwoArrowEquiv (Fin 2)).trans (Equiv.prodComm (Fin 2) (Fin 2)))
  intro w
  rfl

public theorem diskHessianAction_hessianVector (B : Plane →L[ℝ] (Plane →L[ℝ] ℝ)) :
    diskHessianAction (hessianVector B) = gradientVector.comp B := by
  let M : Matrix (Fin 2) (Fin 2) ℝ := fun i j => B (standardBasis j) (standardBasis i)
  apply ContinuousLinearMap.coe_injective
  change Matrix.toEuclideanLin M = (gradientVector.comp B).toLinearMap
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  apply standardBasis.toBasis.ext
  intro j
  apply (WithLp.ext_iff 2).mpr
  funext i
  have hM : (Matrix.toLin standardBasis.toBasis standardBasis.toBasis M (standardBasis j)) i = M i j := by
    have h := LinearMap.toMatrix_apply standardBasis.toBasis standardBasis.toBasis
      (Matrix.toLin standardBasis.toBasis standardBasis.toBasis M) i j
    simpa [standardBasis] using h.symm
  change (Matrix.toLin standardBasis.toBasis standardBasis.toBasis M (standardBasis j)) i =
    (gradientVector (B (standardBasis j))) i
  rw [hM]
  change B (standardBasis j) (standardBasis i) = (gradientVector (B (standardBasis j))) i
  have h := congrArg (fun A : Plane →L[ℝ] ℝ => A (standardBasis i))
    (gradientVector_innerSL (B (standardBasis j)))
  simpa [standardBasis, innerSL_apply_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_right] using h.symm

@[expose] public noncomputable def restrictToClosedDisk {F : Type*} [PseudoMetricSpace F]
    (f : Plane → F) (hf : Continuous f) :
    Metric.closedBall (0 : Plane) 1 →ᵇ F :=
  have : CompactSpace (Metric.closedBall (0 : Plane) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : Plane) 1)
  BoundedContinuousFunction.mkOfCompact ⟨fun x => f x, hf.comp continuous_subtype_val⟩

public theorem extension_restrictToClosedDisk {F : Type*} [PseudoMetricSpace F] [Zero F]
    (f : Plane → F) (hf : Continuous f) {x : Plane} (hx : x ∈ Metric.ball (0 : Plane) 1) :
    diskFieldExtension (restrictToClosedDisk f hf) =ᶠ[𝓝 x] f := by
  filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
  exact diskFieldExtension_of_mem _ (Metric.ball_subset_closedBall hy)

/-- The closed-unit-disk jet of a globally C² scalar function. -/
@[expose] public noncomputable def closedUnitDiskJet {f : Plane → ℝ} (hf : ContDiff ℝ 2 f) :
    C2ClosedDisk (0 : Plane) 1 := by
  let P := fderiv ℝ f
  let B := fderiv ℝ P
  let g := fun x => gradientVector (P x)
  let H := fun x => hessianVector (B x)
  have hP : ContDiff ℝ 1 P := hf.fderiv_right (by decide)
  have hB : Continuous B := (hP.fderiv_right (m := 0) (by decide)).continuous
  have hg : Continuous g := gradientVector.continuous.comp hP.continuous
  have hH : Continuous H :=
    (PiLp.continuous_toLp 2 (fun _ : Fin 2 × Fin 2 => ℝ)).comp
      (continuous_pi fun ij => (hB.clm_apply continuous_const).clm_apply continuous_const)
  refine ⟨(restrictToClosedDisk f hf.continuous, restrictToClosedDisk g hg, restrictToClosedDisk H hH), ?_⟩
  constructor
  · intro x hx
    constructor
    · have h := ((hf.differentiable (by decide)) x).hasFDerivAt
      have hD := h.congr_of_eventuallyEq (extension_restrictToClosedDisk f hf.continuous hx)
      change HasFDerivAt (diskFieldExtension (restrictToClosedDisk f hf.continuous))
        (innerSL ℝ (gradientVector (P x))) x
      rw [gradientVector_innerSL]
      exact hD
    · have h := gradientVector.hasFDerivAt.comp x (hP.differentiable_one x).hasFDerivAt
      have hD := h.congr_of_eventuallyEq (extension_restrictToClosedDisk g hg hx)
      change HasFDerivAt (diskFieldExtension (restrictToClosedDisk g hg))
        (diskHessianAction (hessianVector (B x))) x
      rw [diskHessianAction_hessianVector]
      exact hD
  · intro x i j
    change B x (standardBasis j) (standardBasis i) = B x (standardBasis i) (standardBasis j)
    exact ContDiffAt.isSymmSndFDerivAt (hf.contDiffAt (x := (x : Plane))) (by simp) _ _

public theorem closedUnitDiskJet_value {f : Plane → ℝ} (hf : ContDiff ℝ 2 f)
    (x : Metric.closedBall (0 : Plane) 1) : (closedUnitDiskJet hf).1.1 x = f x :=
  rfl

public theorem closedUnitDiskJet_gradient_norm {f : Plane → ℝ} (hf : ContDiff ℝ 2 f)
    (x : Metric.closedBall (0 : Plane) 1) :
    ‖(closedUnitDiskJet hf).1.2.1 x‖ = ‖fderiv ℝ f x‖ :=
  gradientVector_norm _

public theorem closedUnitDiskJet_hessian_norm {f : Plane → ℝ} (hf : ContDiff ℝ 2 f)
    (x : Metric.closedBall (0 : Plane) 1) :
    ‖(closedUnitDiskJet hf).1.2.2 x‖ = tensorHS (iteratedFDeriv ℝ 2 f x) :=
  hessianVector_norm f x

/-- M47's maximum-norm estimate for a compactly supported C² input. -/
public theorem support_unit_disk_hess_bound_to_C2 {f : Plane → ℝ}
    (hf : ContDiff ℝ 2 f) (hSupp : tsupport f ⊆ Metric.ball (0 : Plane) 1)
    (hHess : ∀ x ∈ Metric.closedBall (0 : Plane) 1, tensorHS (iteratedFDeriv ℝ 2 f x) ≤ 1) :
    ‖closedUnitDiskJet hf‖ ≤ 2 := by
  let u := closedUnitDiskJet hf
  change ‖u‖ ≤ 2
  rw [u.norm_eq]
  refine max_le ?_ (max_le ?_ ?_)
  all_goals apply (BoundedContinuousFunction.norm_le (by norm_num)).mpr
  · intro x
    exact (compact_input_value_gradient_bounds hf hSupp hHess x x.property).1
  · intro x
    change ‖gradientVector (fderiv ℝ f x)‖ ≤ 2
    rw [gradientVector_norm]
    exact (compact_input_value_gradient_bounds hf hSupp hHess x x.property).2
  · intro x
    change ‖hessianVector (fderiv ℝ (fderiv ℝ f) x)‖ ≤ 2
    rw [hessianVector_norm]
    exact (hHess x x.property).trans (by norm_num)

end C2Riemannian
