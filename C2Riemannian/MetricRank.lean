module

public import C2Riemannian.HessianAlgebra
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace C2Riemannian

/-- A positive planar diagonal Gram metric forces injectivity of the derivative. -/
public theorem injective_of_positive_diagonal_gram {m : ℕ} (L : Plane →L[ℝ] Target m)
    {g : ℝ} (hg : 0 < g) (hgram : ∀ v : Plane, ‖L v‖ ^ 2 = g * (v 0) ^ 2 + (v 1) ^ 2) :
    Function.Injective L := by
  intro x y heq
  let v := x - y
  have hLv : L v = 0 := by simp [v, heq]
  have hzero : g * (v 0) ^ 2 + (v 1) ^ 2 = 0 := by simpa [hLv] using (hgram v).symm
  have hnon : 0 ≤ g * (v 0) ^ 2 := mul_nonneg hg.le (sq_nonneg _)
  have h0 : (v 0) ^ 2 = 0 := by
    have hm : g * (v 0) ^ 2 = 0 := by linarith only [hzero, hnon, sq_nonneg (v 1)]
    exact (mul_eq_zero.mp hm).resolve_left hg.ne'
  have h1 : (v 1) ^ 2 = 0 := by linarith only [hzero, hnon, sq_nonneg (v 1)]
  have hn : ‖v‖ ^ 2 = 0 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, h0, h1, add_zero]
  have hz : ‖v‖ = 0 := by
    have hm : ‖v‖ * ‖v‖ = 0 := by simpa only [pow_two] using hn
    exact (mul_eq_zero.mp hm).elim id id
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

end C2Riemannian
