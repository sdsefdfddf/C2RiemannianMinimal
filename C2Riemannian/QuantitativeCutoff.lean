module

public import C2Riemannian.InteriorExhaustion
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped Topology NNReal ENNReal Convolution

namespace C2Riemannian

/-- Convolve a scalar function with a vector-valued kernel. -/
@[expose] public noncomputable def kernelAverage
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Plane → ℝ) (ρ : Plane → F) : Plane → F :=
  f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ

public theorem kernelAverage_apply
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Plane → ℝ) (ρ : Plane → F) (x : Plane) :
    kernelAverage f ρ x = ∫ y, f y • ρ (x - y) := rfl

set_option maxHeartbeats 650000 in
/-- Derivatives of an arbitrary order fall on the compactly supported kernel. -/
public theorem iteratedFDeriv_kernelAverage
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : Plane → ℝ} {ρ : Plane → F}
    (hf : LocallyIntegrable f volume) (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ)
    (hρc : HasCompactSupport ρ) (i : ℕ) (x : Plane) :
    iteratedFDeriv ℝ i (kernelAverage f ρ) x = kernelAverage f (iteratedFDeriv ℝ i ρ) x := by
  induction i generalizing x with
  | zero =>
    let L := (continuousMultilinearCurryFin0 ℝ Plane F).symm.toContinuousLinearEquiv
    rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply, kernelAverage_apply, kernelAverage_apply]
    change L (∫ y, f y • ρ (x - y)) = ∫ y, f y • L (ρ (x - y))
    rw [← L.integral_comp_comm]
    simp only [map_smul]
  | succ i ih =>
    let L : ℝ →L[ℝ] (Plane [×i]→L[ℝ] F) →L[ℝ] (Plane [×i]→L[ℝ] F) :=
      ContinuousLinearMap.lsmul ℝ ℝ
    have hEq : iteratedFDeriv ℝ i (kernelAverage f ρ) =
        kernelAverage f (iteratedFDeriv ℝ i ρ) := funext ih
    have hSmooth : ContDiff ℝ 1 (iteratedFDeriv ℝ i ρ) :=
      hρ.iteratedFDeriv_right (m := 1) (by simp)
    have hCont : Continuous (fderiv ℝ (iteratedFDeriv ℝ i ρ)) :=
      hSmooth.continuous_fderiv (by decide)
    have hSuppI : HasCompactSupport (iteratedFDeriv ℝ i ρ) := hρc.iteratedFDeriv i
    have hSupp : HasCompactSupport (fderiv ℝ (iteratedFDeriv ℝ i ρ)) := hSuppI.fderiv ℝ
    have hd := ((hρc.iteratedFDeriv i).hasFDerivAt_convolution_right L hf hSmooth x).fderiv
    ext v
    rw [iteratedFDeriv_succ_apply_left, hEq]
    change (fderiv ℝ (f ⋆[L, volume] iteratedFDeriv ℝ i ρ) x) (v 0) (Fin.tail v) = _
    rw [hd, convolution_precompR_apply L hf hSupp hCont]
    let M := ContinuousLinearMap.apply ℝ (Plane [×i]→L[ℝ] F) (v 0)
    have hEvalSupp : HasCompactSupport (fun y => fderiv ℝ (iteratedFDeriv ℝ i ρ) y (v 0)) :=
      hSupp.comp_left M.map_zero
    have hEvalCont : Continuous (fun y => fderiv ℝ (iteratedFDeriv ℝ i ρ) y (v 0)) :=
      M.continuous.comp hCont
    have hLeft : Integrable (fun y => f y • fderiv ℝ (iteratedFDeriv ℝ i ρ) (x - y) (v 0)) :=
      hEvalSupp.convolutionExists_right L hf hEvalCont x
    have hRight : Integrable (fun y => f y • iteratedFDeriv ℝ (i + 1) ρ (x - y)) :=
      (hρc.iteratedFDeriv (i + 1)).convolutionExists_right
        (ContinuousLinearMap.lsmul ℝ ℝ) hf (hρ.continuous_iteratedFDeriv (by simp)) x
    rw [convolution_def, kernelAverage_apply]
    change (∫ y, f y • fderiv ℝ (iteratedFDeriv ℝ i ρ) (x - y) (v 0)) (Fin.tail v) =
      (∫ y, f y • iteratedFDeriv ℝ (i + 1) ρ (x - y)) v
    rw [ContinuousMultilinearMap.integral_apply hLeft, ContinuousMultilinearMap.integral_apply hRight]
    simp only [smul_apply, iteratedFDeriv_succ_apply_left]

/-- Planar dilation of a kernel, with the normalization for area. -/
@[expose] public noncomputable def scaleKernel (a : ℝ) (ρ : Plane → ℝ) (x : Plane) : ℝ :=
  (a ^ 2)⁻¹ * ρ (a⁻¹ • x)

public theorem scaleKernel_contDiff {ρ : Plane → ℝ} (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ)
    (a : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (scaleKernel a ρ) := by
  let L : Plane →L[ℝ] Plane := a⁻¹ • ContinuousLinearMap.id ℝ Plane
  change ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (a ^ 2)⁻¹ * (ρ ∘ L) x)
  exact contDiff_const.mul (hρ.comp L.contDiff)

public theorem scaleKernel_integral {ρ : Plane → ℝ} {a : ℝ} (ha : 0 < a) :
    (∫ x, scaleKernel a ρ x) = ∫ x, ρ x := by
  unfold scaleKernel
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume ρ ha.le]
  simp only [Plane, finrank_euclideanSpace_fin, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 ha.ne'), one_mul]

/-- Dilation multiplies the (i)-th derivative by the area factor and
the (i)-th power of the reciprocal length scale. -/
public theorem iteratedFDeriv_scaleKernel {ρ : Plane → ℝ}
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (a : ℝ) (i : ℕ) (x : Plane) :
    iteratedFDeriv ℝ i (scaleKernel a ρ) x =
      ((a ^ 2)⁻¹ * (a⁻¹) ^ i) • iteratedFDeriv ℝ i ρ (a⁻¹ • x) := by
  let L : Plane →L[ℝ] Plane := a⁻¹ • ContinuousLinearMap.id ℝ Plane
  change iteratedFDeriv ℝ i ((a ^ 2)⁻¹ • (ρ ∘ L)) x = _
  rw [iteratedFDeriv_const_smul_apply ((hρ.comp L.contDiff).contDiffAt.of_le (by simp)),
    L.iteratedFDeriv_comp_right hρ x (by simp)]
  ext v
  change (a ^ 2)⁻¹ • iteratedFDeriv ℝ i ρ (a⁻¹ • x) (fun j => a⁻¹ • v j) =
    ((a ^ 2)⁻¹ * (a⁻¹) ^ i) • iteratedFDeriv ℝ i ρ (a⁻¹ • x) v
  have h := (iteratedFDeriv ℝ i ρ (a⁻¹ • x)).toMultilinearMap.map_smul_univ (fun _ => a⁻¹) v
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  change iteratedFDeriv ℝ i ρ (a⁻¹ • x) (fun j => a⁻¹ • v j) =
    (a⁻¹) ^ i • iteratedFDeriv ℝ i ρ (a⁻¹ • x) v at h
  rw [h, smul_smul]


/-- The coefficients of a scalar derivative tensor in the standard
orthonormal planar basis. The Euclidean norm is its Hilbert–Schmidt norm. -/
@[expose] public noncomputable def tensorCoordinates (i : ℕ) :
    (Plane [×i]→L[ℝ] ℝ) →L[ℝ] EuclideanSpace ℝ (Fin i → Fin 2) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin i → Fin 2 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j =>
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => Plane) ℝ
        (fun k => EuclideanSpace.basisFun (Fin 2) ℝ (j k)))

@[expose] public noncomputable def tensorHS {i : ℕ} (A : Plane [×i]→L[ℝ] ℝ) : ℝ :=
  ‖tensorCoordinates i A‖

public theorem tensorHS_eq_sqrt_sum {i : ℕ} (A : Plane [×i]→L[ℝ] ℝ) :
    tensorHS A = √(∑ j : Fin i → Fin 2,
      ‖A (fun k => EuclideanSpace.basisFun (Fin 2) ℝ (j k))‖ ^ 2) := by
  rw [tensorHS, PiLp.norm_eq_of_L2]
  rfl

/-- The planar area factor cancels when taking the L¹ norm of a scaled
derivative tensor, leaving the inverse length scale to its derivative order. -/
public theorem integral_tensorHS_scaleKernel {ρ : Plane → ℝ}
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) {a : ℝ} (ha : 0 < a) (i : ℕ) :
    (∫ x, tensorHS (iteratedFDeriv ℝ i (scaleKernel a ρ) x)) =
      (a⁻¹) ^ i * ∫ x, tensorHS (iteratedFDeriv ℝ i ρ x) := by
  simp_rw [iteratedFDeriv_scaleKernel hρ, tensorHS, map_smul, norm_smul]
  rw [Real.norm_of_nonneg (by positivity), integral_const_mul]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume (fun x => ‖tensorCoordinates i (iteratedFDeriv ℝ i ρ x)‖) ha.le]
  simp only [Plane, finrank_euclideanSpace_fin, smul_eq_mul]
  field_simp


private theorem integral_reflect_translate {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Plane → F) (x : Plane) :
    (∫ y, f (x - y)) = ∫ y, f y := by
  calc
    _ = ∫ y, (fun v => f (x + v)) ((-1 : ℝ) • y) := by simp only [sub_eq_add_neg, neg_one_smul]
    _ = ∫ y, f (x + y) := by
      have h := Measure.integral_comp_smul (volume : Measure Plane)
        (fun y : Plane => f (x + y)) (-1 : ℝ)
      simpa [Plane, finrank_euclideanSpace_fin] using h
    _ = _ := integral_add_left_eq_self f x

/-- Sharp Hilbert–Schmidt bound for the derivatives of the convolution of a
bounded function with a fixed smooth compactly supported kernel. -/
public theorem tensorHS_iteratedFDeriv_kernelAverage_le {f ρ : Plane → ℝ}
    (hf : LocallyIntegrable f volume) (hfBound : ∀ x, ‖f x‖ ≤ 1)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (i : ℕ) (x : Plane) :
    tensorHS (iteratedFDeriv ℝ i (kernelAverage f ρ) x) ≤
      ∫ y, tensorHS (iteratedFDeriv ℝ i ρ y) := by
  let D := iteratedFDeriv ℝ i ρ
  let L := tensorCoordinates i
  have hD : HasCompactSupport D := hρc.iteratedFDeriv i
  have hDc : Continuous D := hρ.continuous_iteratedFDeriv (by simp)
  have hIntegrable : Integrable (fun y => f y • D (x - y)) :=
    hD.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ) hf hDc x
  have hTranslate : Integrable (fun y => D (x - y)) := by
    have h := hD.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ)
      (locallyIntegrable_const (μ := (volume : Measure Plane)) (1 : ℝ)) hDc x
    change Integrable (fun y => (1 : ℝ) • D (x - y)) at h
    simpa only [one_smul] using h
  have hBoundIntegrable : Integrable (fun y => ‖L (D (x - y))‖) :=
    (L.integrable_comp hTranslate).norm
  rw [iteratedFDeriv_kernelAverage hf hρ hρc, kernelAverage_apply]
  change ‖L (∫ y, f y • D (x - y))‖ ≤ ∫ y, ‖L (D y)‖
  rw [← L.integral_comp_comm hIntegrable]
  calc
    _ ≤ ∫ y, ‖L (f y • D (x - y))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, ‖L (D (x - y))‖ := by
      apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
        hBoundIntegrable
      exact Eventually.of_forall fun y => by
        change ‖L (f y • D (x - y))‖ ≤ ‖L (D (x - y))‖
        rw [map_smul, norm_smul]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hfBound y) (norm_nonneg (L (D (x - y))))
    _ = _ := integral_reflect_translate (fun y => ‖L (D y)‖) x


@[expose] public noncomputable def unitBump : ContDiffBump (0 : Plane) :=
  ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- A fixed smooth nonnegative unit-integral mollifier supported in the closed unit ball. -/
@[expose] public noncomputable def unitMollifier : Plane → ℝ := unitBump.normed volume

public theorem unitMollifier_contDiff : ContDiff ℝ (↑(⊤ : ℕ∞)) unitMollifier :=
  unitBump.contDiff_normed (μ := (volume : Measure Plane))

public theorem unitMollifier_integral : (∫ x, unitMollifier x) = 1 :=
  unitBump.integral_normed (μ := (volume : Measure Plane))


public theorem unitMollifier_hasCompactSupport : HasCompactSupport unitMollifier :=
  unitBump.hasCompactSupport_normed (μ := (volume : Measure Plane))

public theorem unitMollifier_tensorHS_integrable (i : ℕ) :
    Integrable (fun x => tensorHS (iteratedFDeriv ℝ i unitMollifier x)) := by
  have hSupp : HasCompactSupport (iteratedFDeriv ℝ i unitMollifier) :=
    unitMollifier_hasCompactSupport.iteratedFDeriv i
  have hCont : Continuous (iteratedFDeriv ℝ i unitMollifier) :=
    unitMollifier_contDiff.continuous_iteratedFDeriv (by simp)
  exact ((tensorCoordinates i).continuous.comp hCont).norm.integrable_of_hasCompactSupport
    ((hSupp.comp_left (tensorCoordinates i).map_zero).comp_left norm_zero)

private theorem scale_unitMollifier_nonneg (a : ℝ) (x : Plane) : 0 ≤ scaleKernel a unitMollifier x :=
  mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) (unitBump.nonneg_normed (μ := (volume : Measure Plane)) (a⁻¹ • x))

private theorem scale_unitMollifier_zero {a : ℝ} (ha : 0 < a) {x : Plane} (hx : a < ‖x‖) :
    scaleKernel a unitMollifier x = 0 := by
  have hOutside : a⁻¹ • x ∉ Metric.closedBall (0 : Plane) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ha.le)]
    intro h
    have hDiv : ‖x‖ / a ≤ 1 := by simpa only [div_eq_mul_inv, mul_comm] using h
    exact hx.not_ge (by simpa only [one_mul] using (div_le_iff₀ ha).mp hDiv)
  have hSupp : tsupport unitMollifier = Metric.closedBall (0 : Plane) 1 := unitBump.tsupport_normed_eq (μ := (volume : Measure Plane))
  have hZero := image_eq_zero_of_notMem_tsupport (show a⁻¹ • x ∉ tsupport unitMollifier by
    rw [hSupp]; exact hOutside)
  simp only [scaleKernel, hZero, mul_zero]

private theorem scale_unitMollifier_compact {a : ℝ} (ha : 0 < a) :
    HasCompactSupport (scaleKernel a unitMollifier) := by
  apply (isCompact_closedBall (0 : Plane) a).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  exact le_of_not_gt fun h => hx (scale_unitMollifier_zero ha h)

private theorem kernelAverage_reflect (f g : Plane → ℝ) (x : Plane) :
    kernelAverage f g x = ∫ y, f (x - y) * g y := by
  rw [kernelAverage_apply]
  have h := integral_reflect_translate (fun y => f (x - y) * g y) x
  simpa only [sub_sub_cancel, smul_eq_mul] using h

/-- The cutoff obtained by convolving the indicator of
`{d_P > 3 * rₖ / 2}` with the unit mollifier at scale `rₖ / 4`. -/
@[expose] public noncomputable def quantitativeCutoff (P : Set Plane) (r : ℝ) (k : ℕ) : Plane → ℝ :=
  let t := interiorRadius r k
  let S : Set Plane := {x | 3 * t / 2 < Metric.infDist x Pᶜ}
  kernelAverage (S.indicator (fun _ => 1)) (scaleKernel (t / 4) unitMollifier)

private theorem indicator_locallyIntegrable_superlevel {P : Set Plane}
    (hP : volume P ≠ ∞) {b : ℝ} (hb : 0 < b) :
    LocallyIntegrable (({x | b < Metric.infDist x Pᶜ} : Set Plane).indicator (fun _ => (1 : ℝ))) volume := by
  let S : Set Plane := {x | b < Metric.infDist x Pᶜ}
  have hS : MeasurableSet S :=
    (isOpen_lt continuous_const (Metric.continuous_infDist_pt Pᶜ)).measurableSet
  have hSub : S ⊆ P := by
    intro x hx
    by_contra h
    have ih : b < Metric.infDist x Pᶜ := hx
    rw [Metric.infDist_zero_of_mem (show x ∈ Pᶜ from h)] at ih
    exact (lt_irrefl 0) (hb.trans ih)
  let _ : IsFiniteMeasure (volume.restrict S) :=
    isFiniteMeasure_restrict.mpr (ne_top_of_le_ne_top hP (measure_mono hSub))
  apply Integrable.locallyIntegrable
  rw [integrable_indicator_iff hS]
  exact integrable_const _

/-- Quantitative M17 cutoff: support and plateau thresholds of (11) and the
kernel L¹ Hilbert–Schmidt bound for every derivative order. -/
public theorem quantitativeCutoff_spec {P : Set Plane} (hBound : Bornology.IsBounded P)
    (E : InteriorExhaustion P) (k : ℕ) :
    let t := interiorRadius E.radius k
    let χ := quantitativeCutoff P E.radius k
    ContDiff ℝ (↑(⊤ : ℕ∞)) χ ∧ HasCompactSupport χ ∧
    tsupport χ ⊆ {x | 5 * t / 4 ≤ Metric.infDist x Pᶜ} ∧
    tsupport χ ⊆ P ∧ (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧
    (∀ x, 7 * t / 4 < Metric.infDist x Pᶜ → χ x = 1) ∧
    (∀ i x, tensorHS (iteratedFDeriv ℝ i χ x) ≤
      (4 / t) ^ i * ∫ y, tensorHS (iteratedFDeriv ℝ i unitMollifier y)) := by
  let t := interiorRadius E.radius k
  let a := t / 4
  let S : Set Plane := {x | 3 * t / 2 < Metric.infDist x Pᶜ}
  let f := S.indicator (fun _ => (1 : ℝ))
  let g := scaleKernel a unitMollifier
  let χ := quantitativeCutoff P E.radius k
  have ht : 0 < t := interiorRadius_pos E.radius_pos k
  have ha : 0 < a := div_pos ht (by norm_num)
  have hf : LocallyIntegrable f volume :=
    indicator_locallyIntegrable_superlevel E.volume_finite (show 0 < 3 * t / 2 by positivity)
  have hgSmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) g := scaleKernel_contDiff unitMollifier_contDiff a
  have hgCompact : HasCompactSupport g := scale_unitMollifier_compact ha
  have hgInt : Integrable g := hgSmooth.continuous.integrable_of_hasCompactSupport hgCompact
  have hgMass : (∫ y, g y) = 1 := (scaleKernel_integral ha).trans unitMollifier_integral
  have hgNonneg (y : Plane) : 0 ≤ g y := scale_unitMollifier_nonneg a y
  have hχ (x : Plane) : χ x = ∫ y, f (x - y) * g y := kernelAverage_reflect f g x
  have hShift (x y : Plane) : dist x (x - y) = ‖y‖ := by rw [dist_eq_norm, sub_sub_cancel]
  have hZero (x : Plane) (hx : Metric.infDist x Pᶜ < 5 * t / 4) : χ x = 0 := by
    rw [hχ, ← integral_zero]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro y
    by_cases hy : ‖y‖ ≤ a
    · have hUpper : Metric.infDist (x - y) Pᶜ ≤ Metric.infDist x Pᶜ + ‖y‖ := by
        rw [← hShift x y, dist_comm x (x - y)]
        exact Metric.infDist_le_infDist_add_dist
      have hNot : x - y ∉ S := by
        intro hm
        change 3 * t / 2 < Metric.infDist (x - y) Pᶜ at hm
        change ‖y‖ ≤ t / 4 at hy
        linarith only [hm, hUpper, hx, hy]
      simp [f, hNot]
    · have h := scale_unitMollifier_zero ha (lt_of_not_ge hy)
      simp only [g, h, mul_zero]
  have hSupp : tsupport χ ⊆ {x | 5 * t / 4 ≤ Metric.infDist x Pᶜ} := by
    apply closure_minimal _ (isClosed_le continuous_const (Metric.continuous_infDist_pt Pᶜ))
    intro x hx
    exact le_of_not_gt fun h => hx (hZero x h)
  have hSubset : tsupport χ ⊆ P := by
    intro x hx
    by_contra h
    have hh : 5 * t / 4 ≤ Metric.infDist x Pᶜ := hSupp hx
    rw [Metric.infDist_zero_of_mem (show x ∈ Pᶜ from h)] at hh
    linarith only [hh, ht]
  have hSupportCompact : HasCompactSupport χ :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport χ) (hBound.subset hSubset)
  have hSmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) χ :=
    hgCompact.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hf hgSmooth
  refine ⟨hSmooth, hSupportCompact, hSupp, hSubset, ?_, ?_, ?_⟩
  · intro x
    change χ x ∈ Icc (0 : ℝ) 1
    rw [hχ]
    have hNonneg (y : Plane) : 0 ≤ f (x - y) * g y := by
      by_cases hy : x - y ∈ S <;> simp [f, hy, hgNonneg y]
    have hLe (y : Plane) : f (x - y) * g y ≤ g y := by
      by_cases hy : x - y ∈ S <;> simp [f, hy, hgNonneg y]
    exact ⟨integral_nonneg hNonneg, hgMass ▸
      integral_mono_of_nonneg (Eventually.of_forall hNonneg) hgInt (Eventually.of_forall hLe)⟩
  · intro x hx
    change χ x = 1
    rw [hχ, ← hgMass]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro y
    by_cases hy : ‖y‖ ≤ a
    · have hLower : Metric.infDist x Pᶜ ≤ Metric.infDist (x - y) Pᶜ + ‖y‖ := by
        rw [← hShift x y]
        exact Metric.infDist_le_infDist_add_dist
      have hIn : x - y ∈ S := by
        change 3 * t / 2 < Metric.infDist (x - y) Pᶜ
        change ‖y‖ ≤ t / 4 at hy
        linarith only [hLower, hx, hy]
      simp [f, hIn]
    · have h := scale_unitMollifier_zero ha (lt_of_not_ge hy)
      simp only [g, h, mul_zero]
  · intro i x
    change tensorHS (iteratedFDeriv ℝ i (kernelAverage f g) x) ≤ _
    have hfBound (y : Plane) : ‖f y‖ ≤ 1 := by
      by_cases hy : y ∈ S <;> simp [f, hy]
    refine (tensorHS_iteratedFDeriv_kernelAverage_le hf hfBound hgSmooth hgCompact i x).trans ?_
    rw [show g = scaleKernel a unitMollifier from rfl, integral_tensorHS_scaleKernel unitMollifier_contDiff ha]
    have hScale : a⁻¹ = 4 / t := by
      dsimp [a]
      field_simp
    rw [hScale]


public theorem quantitativeCutoff_one_near_closure {P : Set Plane} (hBound : Bornology.IsBounded P)
    (E : InteriorExhaustion P) (k : ℕ) :
    ∃ V : Set Plane, IsOpen V ∧ closure (parentInterior P E.radius k) ⊆ V ∧
      ∀ x ∈ V, quantitativeCutoff P E.radius k x = 1 := by
  let t := interiorRadius E.radius k
  let V : Set Plane := {x | 7 * t / 4 < Metric.infDist x Pᶜ}
  have ht : 0 < t := interiorRadius_pos E.radius_pos k
  have hClosure : closure (parentInterior P E.radius k) ⊆
      {x | 2 * t ≤ Metric.infDist x Pᶜ} :=
    closure_minimal (fun x hx => show 2 * t ≤ Metric.infDist x Pᶜ from
      (show 2 * t < Metric.infDist x Pᶜ from hx).le)
      (isClosed_le continuous_const (Metric.continuous_infDist_pt Pᶜ))
  obtain ⟨_, _, _, _, _, hOne, _⟩ := quantitativeCutoff_spec hBound E k
  refine ⟨V, isOpen_lt continuous_const (Metric.continuous_infDist_pt Pᶜ), ?_, hOne⟩
  intro x hx
  exact (by linarith only [ht] : 7 * t / 4 < 2 * t).trans_le (hClosure hx)

end C2Riemannian
