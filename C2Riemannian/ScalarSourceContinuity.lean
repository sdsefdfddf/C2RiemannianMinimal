module

public import C2Riemannian.SourceContinuity
public import C2Riemannian.LocalSmoothCompatibility
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions Topology

namespace C2Riemannian

open WeakJet2 (ex ey testSecond)

/-- The determinant of the Cartesian Hessian of a scalar potential. -/
@[expose] public noncomputable def scalarHessianDet (f : Plane → ℝ) (x : Plane) : ℝ :=
  lineDeriv ℝ (fun y => lineDeriv ℝ f y ex) x ex *
    lineDeriv ℝ (fun y => lineDeriv ℝ f y ey) x ey -
    (lineDeriv ℝ (fun y => lineDeriv ℝ f y ex) x ey) ^ 2

public theorem continuous_scalarHessianDet {f : Plane → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (scalarHessianDet f) := by
  have h₂ (a b : Plane) :
      Continuous (fun x => lineDeriv ℝ (fun y => lineDeriv ℝ f y a) x b) := by
    have h₁ : ContDiff ℝ 1 (fun y => lineDeriv ℝ f y a) := by
      have hEq : (fun y => lineDeriv ℝ f y a) = fun y => fderiv ℝ f y a :=
        funext fun y => ((hf.differentiable (by decide)) y).lineDeriv_eq_fderiv
      rw [hEq]
      exact (hf.fderiv_right (by decide)).clm_apply contDiff_const
    have hEq : (fun x => lineDeriv ℝ (fun y => lineDeriv ℝ f y a) x b) =
        fun x => fderiv ℝ (fun y => lineDeriv ℝ f y a) x b :=
      funext fun x => (h₁.differentiable_one x).lineDeriv_eq_fderiv
    rw [hEq]
    exact (h₁.continuous_fderiv (by decide)).clm_apply continuous_const
  exact ((h₂ ex ex).mul (h₂ ey ey)).sub ((h₂ ex ey).pow 2)

private noncomputable def scalarLift : ℝ →L[ℝ] Target 1 :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single 0 1)

private theorem scalarLift_inner (a b : ℝ) :
    inner ℝ (scalarLift a) (scalarLift b) = a * b := by
  change inner ℝ (a • (EuclideanSpace.single 0 1 : Target 1))
    (b • (EuclideanSpace.single 0 1 : Target 1)) = _
  rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
  simp

private theorem scalarLift_lineDeriv {f : Plane → ℝ} {x : Plane}
    (hf : DifferentiableAt ℝ f x) (d : Plane) :
    lineDeriv ℝ (scalarLift ∘ f) x d = scalarLift (lineDeriv ℝ f x d) := by
  rw [hf.lineDeriv_eq_fderiv]
  exact ((scalarLift.hasFDerivAt.comp x hf.hasFDerivAt).hasLineDerivAt d).lineDeriv

private theorem scalarLift_lineDeriv₂ {f : Plane → ℝ} (hf : ContDiff ℝ 2 f)
    (x a b : Plane) :
    lineDeriv ℝ (fun y => lineDeriv ℝ (scalarLift ∘ f) y a) x b =
      scalarLift (lineDeriv ℝ (fun y => lineDeriv ℝ f y a) x b) := by
  have h (y : Plane) : lineDeriv ℝ (scalarLift ∘ f) y a = scalarLift (lineDeriv ℝ f y a) :=
    scalarLift_lineDeriv ((hf.differentiable (by decide)) y) a
  simp_rw [h]
  apply scalarLift_lineDeriv
  have he : (fun y => lineDeriv ℝ f y a) = fun y => fderiv ℝ f y a :=
    funext fun y => ((hf.differentiable (by decide)) y).lineDeriv_eq_fderiv
  rw [he]
  exact ((hf.fderiv_right (m := 1) (by decide)).clm_apply contDiff_const).differentiable_one x

private theorem classicalHessian_scalarLift {f : Plane → ℝ} (hf : ContDiff ℝ 2 f) (x : Plane) :
    (classicalHessian (scalarLift ∘ f) x).q = scalarHessianDet f x := by
  simp only [classicalHessian, Hess3.q, scalarLift_lineDeriv₂ hf, scalarLift_inner,
    scalarHessianDet, pow_two, ex, ey]

/-- The determinant of a smooth scalar Hessian tested through first derivatives. -/
public theorem scalar_hessian_det_test {U : Opens Plane} {f : Plane → ℝ}
    (hf : ContDiff ℝ 3 f) (φ : 𝓓(U, ℝ)) :
    -2 * (∫ x in ↑U, φ x * scalarHessianDet f x) =
      (∫ x in ↑U, testSecond ey ey φ x * (fderiv ℝ f x ex * fderiv ℝ f x ex)) +
      (∫ x in ↑U, testSecond ex ex φ x * (fderiv ℝ f x ey * fderiv ℝ f x ey)) -
      2 * (∫ x in ↑U, testSecond ey ex φ x * (fderiv ℝ f x ex * fderiv ℝ f x ey)) := by
  have h := smooth_compatibility_test (scalarLift.contDiff.comp hf) φ
  dsimp only at h
  have hd (x : Plane) : DifferentiableAt ℝ f x := hf.differentiable (by decide) x
  simp_rw [classicalHessian_scalarLift (hf.of_le (by decide)), scalarLift_lineDeriv (hd _),
    scalarLift_inner, (hd _).lineDeriv_eq_fderiv] at h
  simpa only [WeakJet2.testSecond_apply, ex, ey] using h

private theorem grad_product_test_tendsto {U : Opens Plane}
    {F : ℕ → Plane → Plane →L[ℝ] ℝ} {G : Plane → Plane →L[ℝ] ℝ}
    (hF : ∀ n, Continuous (F n)) (hG : Continuous G)
    (hPoint : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (G x)))
    (hClose : ∀ n x, ‖F n x - G x‖ ≤ 1)
    (d e : Plane) (ψ : 𝓓(U, ℝ)) :
    Tendsto (fun n => ∫ x in ↑U, ψ x * (F n x d * F n x e)) atTop
      (𝓝 (∫ x in ↑U, ψ x * (G x d * G x e))) := by
  let S := tsupport (ψ : Plane → ℝ)
  have hS : IsCompact S := ψ.hasCompactSupport
  have hsub : S ⊆ (U : Set Plane) := ψ.tsupport_subset
  have hrest (P : Plane → Plane →L[ℝ] ℝ) :
      (∫ x in ↑U, ψ x * (P x d * P x e)) = ∫ x in S, ψ x * (P x d * P x e) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero U.isOpen.measurableSet hsub
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx.2, zero_mul]
  simp only [hrest]
  let _ : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  obtain ⟨B, hB⟩ := hS.bddAbove_image hG.norm.continuousOn
  obtain ⟨C, hC⟩ := ψ.hasCompactSupport.exists_bound_of_continuous ψ.continuous
  let M := max B 0 + 1
  have hM : 0 ≤ M := add_nonneg (le_max_right _ _) zero_le_one
  have hNorm (n : ℕ) (x : Plane) (hx : x ∈ S) : ‖F n x‖ ≤ M := by
    calc
      ‖F n x‖ ≤ ‖G x‖ + ‖F n x - G x‖ := norm_le_insert' _ _
      _ ≤ max B 0 + 1 := add_le_add ((hB ⟨x, hx, rfl⟩).trans (le_max_left _ _)) (hClose n x)
  have hEvalBound (n : ℕ) (x d : Plane) (hx : x ∈ S) : ‖F n x d‖ ≤ M * ‖d‖ :=
    ((F n x).le_opNorm d).trans (mul_le_mul_of_nonneg_right (hNorm n x hx) (norm_nonneg _))
  apply tendsto_integral_of_dominated_convergence (fun _ => C * ((M * ‖d‖) * (M * ‖e‖)))
  · intro n
    exact (ψ.continuous.mul (((hF n).clm_apply continuous_const).mul
      ((hF n).clm_apply continuous_const))).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    filter_upwards [ae_restrict_mem hS.isClosed.measurableSet] with x hx
    rw [norm_mul, norm_mul]
    exact mul_le_mul (hC x)
      (mul_le_mul (hEvalBound n x d hx) (hEvalBound n x e hx) (norm_nonneg _)
        (mul_nonneg hM (norm_nonneg _))) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      ((norm_nonneg _).trans (hC x))
  · filter_upwards with x
    have hEval (d : Plane) : Tendsto (fun n => F n x d) atTop (𝓝 (G x d)) :=
      (ContinuousLinearMap.apply ℝ ℝ d).continuous.continuousAt.tendsto.comp (hPoint x)
    exact ((hEval d).mul (hEval e)).const_mul (ψ x)

/-- Distributional convergence of negative determinants follows from convergence
of the first derivatives of smooth scalar potentials. -/
public theorem reverse_scalar_source_test_limits {U : Opens Plane}
    {f : ℕ → Plane → ℝ} {g : Plane → ℝ}
    (hf : ∀ n, ContDiff ℝ 3 (f n)) (hg : ContDiff ℝ 3 g)
    (hPoint : ∀ x, Tendsto (fun n => fderiv ℝ (f n) x) atTop (𝓝 (fderiv ℝ g x)))
    (hClose : ∀ n x, ‖fderiv ℝ (f n) x - fderiv ℝ g x‖ ≤ 1)
    (φ : 𝓓(U, ℝ)) :
    Tendsto (fun n => ∫ x in ↑U, φ x • (-scalarHessianDet (f n) x)) atTop
      (𝓝 (∫ x in ↑U, φ x • (-scalarHessianDet g x))) := by
  have hf' (n : ℕ) : Continuous (fderiv ℝ (f n)) := (hf n).continuous_fderiv (by decide)
  have hg' : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by decide)
  let P (ψ : 𝓓(U, ℝ)) (d e : Plane) (v : Plane → ℝ) :=
    ∫ x in ↑U, ψ x * (fderiv ℝ v x d * fderiv ℝ v x e)
  have hP (ψ : 𝓓(U, ℝ)) (d e : Plane) :
      Tendsto (fun n => P ψ d e (f n)) atTop (𝓝 (P ψ d e g)) :=
    grad_product_test_tendsto hf' hg' hPoint hClose d e ψ
  have hEq {v : Plane → ℝ} (hv : ContDiff ℝ 3 v) :
      (∫ x in ↑U, φ x • (-scalarHessianDet v x)) =
        (1 / 2 : ℝ) * (P (testSecond ey ey φ) ex ex v + P (testSecond ex ex φ) ey ey v -
          2 * P (testSecond ey ex φ) ex ey v) := by
    simp only [smul_eq_mul, mul_neg, integral_neg]
    have h := scalar_hessian_det_test hv φ
    change -2 * (∫ x in ↑U, φ x * scalarHessianDet v x) =
      P (testSecond ey ey φ) ex ex v + P (testSecond ex ex φ) ey ey v -
        2 * P (testSecond ey ex φ) ex ey v at h
    rw [← h]
    ring
  simp_rw [show ∀ n, _ from fun n => hEq (hf n), hEq hg]
  exact (((hP _ _ _).add (hP _ _ _)).sub ((hP _ _ _).const_mul 2)).const_mul (1 / 2)

end C2Riemannian
