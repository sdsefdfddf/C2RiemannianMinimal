module

public import C2Riemannian.HessianAlgebra
import Mathlib.Tactic.Abel

set_option autoImplicit false

namespace C2Riemannian.Hess3

variable {m : ℕ}

/-- Evaluation of the two Hessian rows on the planar vector `(a,b)`. -/
@[expose] public def applyRows (H : Hess3 m) (a b : ℝ) : Target m × Target m :=
  (a • H.xx + b • H.xy, a • H.xy + b • H.yy)

public theorem oblique_mean_of_applyRows_eq (H H₀ : Hess3 m) (t : ℝ)
    (h : H.applyRows (-t) 1 = H₀.applyRows (-t) 1) :
    H.xy = H₀.xy + t • (H.xx - H₀.xx) ∧
    H.yy = H₀.yy + t ^ 2 • (H.xx - H₀.xx) := by
  have hz := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  simp only [applyRows, neg_smul, one_smul] at hz hy
  have hxy : H.xy = H₀.xy + t • (H.xx - H₀.xx) := by
    calc
      H.xy = t • H.xx + (-(t • H.xx) + H.xy) := by abel
      _ = H₀.xy + t • (H.xx - H₀.xx) := by rw [hz, smul_sub]; abel
  refine ⟨hxy, ?_⟩
  calc
    H.yy = t • H.xy + (-(t • H.xy) + H.yy) := by abel
    _ = H₀.yy + t • (H.xy - H₀.xy) := by rw [hy, smul_sub]; abel
    _ = H₀.yy + t ^ 2 • (H.xx - H₀.xx) := by
      rw [hxy, add_sub_cancel_left, smul_smul, pow_two]

public theorem vertical_mean_of_applyRows_eq (H H₀ : Hess3 m)
    (h : H.applyRows 1 0 = H₀.applyRows 1 0) : H.xx = H₀.xx ∧ H.xy = H₀.xy := by
  simpa only [applyRows, one_smul, zero_smul, add_zero, Prod.mk.injEq] using h

end C2Riemannian.Hess3
