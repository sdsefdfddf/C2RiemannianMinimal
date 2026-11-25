module

public import C2Riemannian.HessianAlgebra
public import C2Riemannian.PeriodicProfile
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Filter Set
open scoped ContDiff Topology BigOperators

namespace C2Riemannian

/-- The cutoff oscillation of order j in a fixed planar direction. -/
@[expose] public noncomputable def oscillatoryPotential (j : ℕ) (χ : Plane → ℝ)
    (e γ L : ℝ) (d : Plane →L[ℝ] ℝ) (x : Plane) : ℝ :=
  (γ / L ^ j) * (χ x * profilePrimitive e j ((L • d) x))

public theorem contDiff_oscillatoryPotential (j : ℕ) {χ : Plane → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (e γ L : ℝ) (d : Plane →L[ℝ] ℝ) :
    ContDiff ℝ ∞ (oscillatoryPotential j χ e γ L d) :=
  contDiff_const.mul (hχ.mul ((profilePrimitive_properties e j).1.comp
    (L • d).contDiff))

public theorem tsupport_oscillatoryPotential_subset (j : ℕ) (χ : Plane → ℝ)
    (e γ L : ℝ) (d : Plane →L[ℝ] ℝ) :
    tsupport (oscillatoryPotential j χ e γ L d) ⊆ tsupport χ := by
  unfold oscillatoryPotential
  exact tsupport_mul_subset_right.trans tsupport_mul_subset_left

public theorem hasCompactSupport_oscillatoryPotential (j : ℕ) {χ : Plane → ℝ}
    (hχ : HasCompactSupport χ) (e γ L : ℝ) (d : Plane →L[ℝ] ℝ) :
    HasCompactSupport (oscillatoryPotential j χ e γ L d) :=
  hχ.of_isClosed_subset (isClosed_tsupport _) (tsupport_oscillatoryPotential_subset j χ e γ L d)

/-- The exact top derivative on any neighborhood where the cutoff is one. -/
public theorem iteratedFDeriv_oscillatoryPotential_on_plateau (j : ℕ) {χ : Plane → ℝ}
    (e γ L : ℝ) (hL : L ≠ 0) (d : Plane →L[ℝ] ℝ) {x : Plane}
    (hχ : ∀ᶠ y in 𝓝 x, χ y = 1) (v : Fin j → Plane) :
    iteratedFDeriv ℝ j (oscillatoryPotential j χ e γ L d) x v =
      γ * smooth_square_wave e ((L • d) x) * ∏ i, d (v i) := by
  let A : Plane →L[ℝ] ℝ := L • d
  have hEq : oscillatoryPotential j χ e γ L d =ᶠ[𝓝 x]
      (fun y => (γ / L ^ j) • (profilePrimitive e j ∘ A) y) := by
    filter_upwards [hχ] with y h
    simp only [oscillatoryPotential, h, one_mul, A, Function.comp_apply, smul_eq_mul]
  have hφ := (profilePrimitive_properties e j).1
  have hSmooth : ContDiffAt ℝ (↑j) (profilePrimitive e j ∘ A) x :=
    (hφ.comp A.contDiff).contDiffAt.of_le (by simp)
  have hChain := A.iteratedFDeriv_comp_right hφ x (show (j : ℕ∞ω) ≤ ∞ by simp)
  rw [(hEq.iteratedFDeriv ℝ j).eq_of_nhds, iteratedFDeriv_const_smul_apply' hSmooth, hChain]
  simp only [smul_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul]
  have hD : iteratedDeriv j (profilePrimitive e j) = smooth_square_wave e :=
    iteratedDeriv_profilePrimitive e 0 j
  rw [hD]
  simp only [A, smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  field_simp

/-- The size of the second-order potential before differentiation. -/
public theorem abs_oscillatoryPotential_two_le {χ : Plane → ℝ} (e γ L : ℝ)
    (hL : 0 < L) (d : Plane →L[ℝ] ℝ) (x : Plane) (hχ : |χ x| ≤ 1) :
    |oscillatoryPotential 2 χ e γ L d x| ≤ 4 * |γ| / L ^ (2 : ℕ) := by
  rw [oscillatoryPotential, abs_mul, abs_mul, abs_div, abs_pow, abs_of_pos hL]
  have hp := (profilePrimitive_properties e 2).2.2.2 ((L • d) x)
  calc
    _ ≤ (|γ| / L ^ (2 : ℕ)) * (1 * (2 : ℝ) ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hχ hp (abs_nonneg _) zero_le_one)
        (div_nonneg (abs_nonneg _) (sq_nonneg _))
    _ = _ := by ring

/-- The first derivative estimate for the second-order oscillation. -/
public theorem norm_fderiv_oscillatoryPotential_two_le {χ : Plane → ℝ}
    (e γ L : ℝ) (hL : 0 < L) (d : Plane →L[ℝ] ℝ) (x : Plane)
    (hχ : DifferentiableAt ℝ χ x) (hχBound : |χ x| ≤ 1) :
    ‖fderiv ℝ (oscillatoryPotential 2 χ e γ L d) x‖ ≤
      |γ| * (4 * ‖fderiv ℝ χ x‖ / L ^ (2 : ℕ) + 2 * ‖d‖ / L) := by
  let A : Plane →L[ℝ] ℝ := L • d
  let S := profilePrimitive e 2
  let T := profilePrimitive e 1
  have hPrim : HasDerivAt S (T (A x)) (A x) :=
    hasDerivAt_meanZeroPrimitive (profilePrimitive_properties e 1).1.continuous _
  have hPhase := hPrim.comp_hasFDerivAt x A.hasFDerivAt
  have hProduct := hχ.hasFDerivAt.mul hPhase
  have hDerivative :
      fderiv ℝ (oscillatoryPotential 2 χ e γ L d) x =
        (γ / L ^ (2 : ℕ)) • (S (A x) • fderiv ℝ χ x + χ x • (T (A x) • A)) := by
    change fderiv ℝ (fun y => (γ / L ^ (2 : ℕ)) * (χ y * S (A y))) x = _
    have h := (hProduct.const_mul (γ / L ^ (2 : ℕ))).fderiv
    simpa only [A, S, T, Pi.mul_apply, Function.comp_apply, add_comm] using h
  have hS : |S (A x)| ≤ 4 := by
    simpa only [S, show (2 : ℝ) ^ (2 : ℕ) = 4 by norm_num]
      using (profilePrimitive_properties e 2).2.2.2 (A x)
  have hT : |T (A x)| ≤ 2 := by
    simpa only [T, pow_one] using (profilePrimitive_properties e 1).2.2.2 (A x)
  have hA : ‖A‖ = L * ‖d‖ := by simp only [A, norm_smul, Real.norm_eq_abs, abs_of_pos hL]
  rw [hDerivative, norm_smul, Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hL]
  calc
    _ ≤ (|γ| / L ^ (2 : ℕ)) * (‖S (A x) • fderiv ℝ χ x‖ + ‖χ x • (T (A x) • A)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (div_nonneg (abs_nonneg _) (sq_nonneg _))
    _ ≤ (|γ| / L ^ (2 : ℕ)) * (4 * ‖fderiv ℝ χ x‖ + 1 * (2 * (L * ‖d‖))) := by
      simp only [norm_smul, Real.norm_eq_abs, hA]
      gcongr
    _ = _ := by field_simp

end C2Riemannian
