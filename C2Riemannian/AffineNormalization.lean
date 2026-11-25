module

public import C2Riemannian.HessianAlgebra
public import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Affine normalization and convex-domain estimates, M09 (paper (8)) -/

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators Interval

namespace C2Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Hilbert–Schmidt norm of a derivative on the plane, in its standard orthonormal basis. -/
@[expose] public noncomputable def gradHS (A : Plane →L[ℝ] E) : ℝ :=
  √(∑ i : Fin 2, ‖A (EuclideanSpace.basisFun (Fin 2) ℝ i)‖ ^ 2)

public theorem opNorm_le_gradHS (A : Plane →L[ℝ] E) : ‖A‖ ≤ gradHS A := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro v
  have h : A v = ∑ i, b.repr v i • A (b i) := by
    conv_lhs => rw [← b.sum_repr v]
    simp only [map_sum, map_smul]
  have hv : (∑ i, ‖b.repr v i‖ ^ 2) = ‖v‖ ^ 2 := by
    exact (PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ) v).symm
  calc
    ‖A v‖ ≤ ∑ i, ‖b.repr v i‖ * ‖A (b i)‖ := by
      rw [h]
      simpa only [norm_smul] using
        norm_sum_le (Finset.univ : Finset (Fin 2)) (fun i => b.repr v i • A (b i))
    _ ≤ √(∑ i, ‖b.repr v i‖ ^ 2) * √(∑ i, ‖A (b i)‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => ‖b.repr v i‖) (fun i => ‖A (b i)‖)
    _ = gradHS A * ‖v‖ := by
      rw [hv, Real.sqrt_sq (norm_nonneg _)]
      exact mul_comm _ _

/-- Remove the affine first jet of a potential at the chosen base point. -/
@[expose] public noncomputable def normalize_height (W : Plane → E) (a : Plane) (x : Plane) : E :=
  W x - W a - fderiv ℝ W a (x - a)

@[simp] public theorem normalize_height_self (W : Plane → E) (a : Plane) :
    normalize_height W a a = 0 := by
  simp [normalize_height]

public theorem hasFDerivAt_normalize_height {W : Plane → E} {a x : Plane}
    (hW : DifferentiableAt ℝ W x) :
    HasFDerivAt (normalize_height W a) (fderiv ℝ W x - fderiv ℝ W a) x := by
  have hbase : HasFDerivAt (fun z => z - a) (ContinuousLinearMap.id ℝ Plane) x :=
    (hasFDerivAt_id x).sub_const a
  have haff : HasFDerivAt (fun z => fderiv ℝ W a (z - a)) (fderiv ℝ W a) x := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using
      ((fderiv ℝ W a).hasFDerivAt.comp x hbase)
  exact (hW.hasFDerivAt.sub_const (W a)).sub haff

public theorem fderiv_normalize_height {W : Plane → E} {a x : Plane}
    (hW : DifferentiableAt ℝ W x) :
    fderiv ℝ (normalize_height W a) x = fderiv ℝ W x - fderiv ℝ W a :=
  (hasFDerivAt_normalize_height (a := a) hW).fderiv

public theorem fderiv_normalize_height_self {W : Plane → E} {a : Plane}
    (hW : DifferentiableAt ℝ W a) : fderiv ℝ (normalize_height W a) a = 0 := by
  rw [fderiv_normalize_height hW, sub_self]

/-- On an open domain the second Fréchet derivative agrees with the original one. -/
public theorem second_fderiv_normalize_height {W : Plane → E} {s : Set Plane}
    (hs : IsOpen s) (hW : ∀ x ∈ s, DifferentiableAt ℝ W x) (a : Plane)
    {x : Plane} (hx : x ∈ s) :
    fderiv ℝ (fderiv ℝ (normalize_height W a)) x = fderiv ℝ (fderiv ℝ W) x := by
  have heq : fderiv ℝ (normalize_height W a) =ᶠ[nhds x]
      fun y => fderiv ℝ W y - fderiv ℝ W a :=
    Filter.eventually_of_mem (hs.mem_nhds hx) fun _ hy => fderiv_normalize_height (hW _ hy)
  rw [heq.fderiv_eq, fderiv_sub_const]

/-- The gradient differences and the gradient at a single point after normalization. -/
public theorem normalized_gradient_bounds {W : Plane → E} {s : Set Plane} {a : Plane}
    (ha : a ∈ s) (hW : ∀ x ∈ s, DifferentiableAt ℝ W x) {K : ℝ}
    (hLip : ∀ x ∈ s, ∀ y ∈ s, gradHS (fderiv ℝ W x - fderiv ℝ W y) ≤ K * dist x y) :
    (∀ x ∈ s, ∀ y ∈ s,
      gradHS (fderiv ℝ (normalize_height W a) x - fderiv ℝ (normalize_height W a) y) ≤
        K * dist x y) ∧
    (∀ x ∈ s, gradHS (fderiv ℝ (normalize_height W a) x) ≤ K * dist x a) := by
  constructor
  · intro x hx y hy
    rw [fderiv_normalize_height (hW x hx), fderiv_normalize_height (hW y hy),
      sub_sub_sub_cancel_right]
    exact hLip x hx y hy
  · intro x hx
    rw [fderiv_normalize_height (hW x hx)]
    exact hLip x hx a ha

/-- Integration along the segment gives the factor one half in the height bound. -/
public theorem normalized_bounds [CompleteSpace E] {W : Plane → E} {s : Set Plane}
    (hs : Convex ℝ s) {a : Plane} (ha : a ∈ s)
    (hW : ∀ x ∈ s, DifferentiableAt ℝ W x) (hC : ContinuousOn (fderiv ℝ W) s)
    {K : ℝ} (hLip : ∀ x ∈ s, ∀ y ∈ s,
      gradHS (fderiv ℝ W x - fderiv ℝ W y) ≤ K * dist x y)
    {x : Plane} (hx : x ∈ s) :
    ‖normalize_height W a x‖ ≤ K * dist x a ^ 2 / 2 := by
  let p : ℝ → Plane := fun t => a + t • (x - a)
  have hp : MapsTo p (Icc 0 1) s := by
    intro t ht
    have heq : p t = AffineMap.lineMap a x t := by
      rw [AffineMap.lineMap_apply]
      exact add_comm _ _
    rw [heq]
    exact hs.segment_subset ha hx (lineMap_mem_segment ℝ a x ht)
  have hpcont : Continuous p := continuous_const.add (continuous_id.smul continuous_const)
  let g : ℝ → E := fun t => (fderiv ℝ W (p t) - fderiv ℝ W a) (x - a)
  have hg : ContinuousOn g (Icc 0 1) :=
    ((hC.comp hpcont.continuousOn hp).sub continuousOn_const).clm_apply continuousOn_const
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun u => normalize_height W a (p u)) (g t) t := by
    have hpath : HasDerivAt p (x - a) t := by
      simpa only [p, one_smul] using ((hasDerivAt_id' t).smul_const (x - a)).const_add a
    exact (hasFDerivAt_normalize_height (a := a) (hW _ (hp ht))).comp_hasDerivAt t hpath
  have hInt : (∫ t in (0 : ℝ)..1, g t) = normalize_height W a x := by
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t => normalize_height W a (p t))
      (by simpa only [uIcc_of_le zero_le_one] using hd)
      (hg.intervalIntegrable_of_Icc zero_le_one)
    simpa [p] using hFTC
  have hpoint (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖g t‖ ≤ (K * dist x a ^ 2) * t := by
    have hdista : dist (p t) a = t * dist x a := by
      rw [dist_eq_norm, show p t - a = t • (x - a) by simp [p],
        norm_smul, Real.norm_of_nonneg ht.1, ← dist_eq_norm]
    let A := fderiv ℝ W (p t) - fderiv ℝ W a
    have hA : ‖A‖ ≤ K * (t * dist x a) :=
      (opNorm_le_gradHS A).trans (hdista ▸ hLip (p t) (hp ht) a ha)
    calc
      ‖g t‖ ≤ ‖A‖ * ‖x - a‖ := A.le_opNorm _
      _ ≤ (K * (t * dist x a)) * ‖x - a‖ :=
        mul_le_mul_of_nonneg_right hA (norm_nonneg _)
      _ = (K * dist x a ^ 2) * t := by rw [← dist_eq_norm]; ring
  rw [← hInt]
  calc
    ‖∫ t in (0 : ℝ)..1, g t‖ ≤ ∫ t in (0 : ℝ)..1, ‖g t‖ :=
      intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ t in (0 : ℝ)..1, (K * dist x a ^ 2) * t :=
      intervalIntegral.integral_mono_on zero_le_one
        (hg.norm.intervalIntegrable_of_Icc zero_le_one)
        ((continuous_const.mul continuous_id).intervalIntegrable 0 1) hpoint
    _ = K * dist x a ^ 2 / 2 := by
      rw [intervalIntegral.integral_const_mul, integral_id]
      ring

/-- On a convex domain of radius at most `R` about `a`, the normalized height
has Lipschitz constant `K * R`. -/
public theorem normalized_height_dist_le {W : Plane → E} {s : Set Plane}
    (hs : Convex ℝ s) {a : Plane} (ha : a ∈ s)
    (hW : ∀ x ∈ s, DifferentiableAt ℝ W x) {K R : ℝ} (hK : 0 ≤ K)
    (hLip : ∀ x ∈ s, ∀ y ∈ s,
      gradHS (fderiv ℝ W x - fderiv ℝ W y) ≤ K * dist x y)
    (hR : ∀ x ∈ s, dist x a ≤ R) {x y : Plane} (hx : x ∈ s) (hy : y ∈ s) :
    dist (normalize_height W a x) (normalize_height W a y) ≤ K * R * dist x y := by
  have hd z (hz : z ∈ s) : DifferentiableAt ℝ (normalize_height W a) z :=
    (hasFDerivAt_normalize_height (a := a) (hW z hz)).differentiableAt
  have hgrad z (hz : z ∈ s) : ‖fderiv ℝ (normalize_height W a) z‖ ≤ K * R :=
    (opNorm_le_gradHS _).trans
      (((normalized_gradient_bounds ha hW hLip).2 z hz).trans
        (mul_le_mul_of_nonneg_left (hR z hz) hK))
  simpa only [dist_eq_norm] using hs.norm_image_sub_le_of_norm_fderiv_le hd hgrad hy hx

end C2Riemannian
