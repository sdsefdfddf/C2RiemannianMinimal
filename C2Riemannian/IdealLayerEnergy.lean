module

public import C2Riemannian.LayerEnergyBudget
public import C2Riemannian.ConditionalTangentialReadouts
import Mathlib.Tactic.Abel

set_option autoImplicit false

namespace C2Riemannian

namespace HessianBall

variable {m : ℕ} {K : ℝ}

/-- Apply the geometric and norm inputs of the oblique comparison together. -/
private theorem oblique_inputs
    (L : PositiveFunctional (HessianBall m K)) (H : Hess3 m) (t : ℝ)
    (hK : 0 ≤ K) (hH : H.frobenius ≤ K)
    (hT : (meanHessian L).applyRows (coordinateDirection (-t) 1 0) (coordinateDirection (-t) 1 1) =
      H.applyRows (coordinateDirection (-t) 1 0) (coordinateDirection (-t) 1 1)) :
    ∃ β : Target m, L.mean xx = H.xx + β ∧ L.mean xy = H.xy + t • β ∧
      L.mean yy = H.yy + t ^ 2 • β ∧
      L (sqNormReadout xx) ≤ K ^ 2 ∧ ‖H.xx‖ ≤ K ∧ ‖H.xy‖ ≤ K ∧ ‖β‖ ≤ 2 * K := by
  let β := (meanHessian L).xx - H.xx
  have hB := Hess3.oblique_mean_of_applyRows_eq (meanHessian L) H t hT
  have hNorm := (meanHessian L).entry_norms_le_frobenius.1.trans (mean_frobenius_le L hK)
  have hxx := H.entry_norms_le_frobenius.1.trans hH
  have hxy := H.entry_norms_le_frobenius.2.1.trans hH
  refine ⟨β, ?_, hB.1, hB.2, (entry_moment_bounds L).1, hxx, hxy, ?_⟩
  · change (meanHessian L).xx = H.xx + ((meanHessian L).xx - H.xx)
    abel
  · exact (norm_sub_le _ _).trans ((add_le_add hNorm hxx).trans_eq (two_mul K).symm)

public theorem table_linear_energy
    (L : PositiveFunctional (HessianBall m K)) (H : Hess3 m) (t B : ℝ)
    (hK : 1 ≤ K) (ht : |t| ≤ 1) (hH : H.frobenius ≤ K)
    (hT : (meanHessian L).applyRows (coordinateDirection (-t) 1 0) (coordinateDirection (-t) 1 1) =
      H.applyRows (coordinateDirection (-t) 1 0) (coordinateDirection (-t) 1 1))
    (hJump : -(t ^ 2 / 10) ≤ L curvature - H.q) (hEnergy : L energy ≤ B) :
    H.energy + -(7 * K ^ 2 * |t| ^ 3) ≤ B := by
  obtain ⟨β, hx, hz, hy, hxx₂, hxx, hxy, hb⟩ := oblique_inputs L H t (zero_le_one.trans hK) hH hT
  exact L.oblique_linear_parent_energy_le xx xy yy H β t K B hK ht hx hz hy hxx₂ hxx hxy hb hJump hEnergy

public theorem table_reverse_energy
    (L : PositiveFunctional (HessianBall m K)) (H : Hess3 m) (t B Δ : ℝ)
    (hK : 0 ≤ K) (ht : |t| ≤ 1) (hH : H.frobenius ≤ K)
    (hT : (meanHessian L).applyRows (coordinateDirection (-t) 1 0) (coordinateDirection (-t) 1 1) =
      H.applyRows (coordinateDirection (-t) 1 0) (coordinateDirection (-t) 1 1))
    (hJump : t ^ 2 * (L curvature - H.q) = Δ) (hEnergy : L energy ≤ B) :
    H.energy + (Δ - 7 * K ^ 2 * |t| ^ 3) ≤ B := by
  obtain ⟨β, hx, hz, hy, hxx₂, hxx, hxy, hb⟩ := oblique_inputs L H t hK hH hT
  exact L.oblique_reverse_parent_energy_le xx xy yy H β t K B Δ hK ht hx hz hy hxx₂ hxx hxy hb hJump hEnergy

public theorem horizontal_energy_of_tangent
    (L : PositiveFunctional (HessianBall m K)) (H : Hess3 m) (B : ℝ)
    (hT : (meanHessian L).applyRows (coordinateDirection 0 1 0) (coordinateDirection 0 1 1) =
      H.applyRows (coordinateDirection 0 1 0) (coordinateDirection 0 1 1))
    (hEnergy : L energy ≤ B) : H.energy ≤ B := by
  have hT' : (meanHessian L).applyRows (coordinateDirection (-(0 : ℝ)) 1 0) (coordinateDirection (-(0 : ℝ)) 1 1) =
      H.applyRows (coordinateDirection (-(0 : ℝ)) 1 0) (coordinateDirection (-(0 : ℝ)) 1 1) := by
    rw [neg_zero]
    exact hT
  have hy := (Hess3.oblique_mean_of_applyRows_eq (meanHessian L) H 0 hT').2
  have hh : L.mean yy = H.yy := by
    change (meanHessian L).yy = H.yy
    simpa using hy
  exact L.horizontal_parent_energy_le yy H B hh hEnergy

public theorem vertical_linear_energy_of_tangent
    (Lpos Lneg : PositiveFunctional (HessianBall m K)) (H : Hess3 m)
    (θ B : ℝ) (hK : 0 < K) (hθ : 0 ≤ θ)
    (hT : (meanHessian Lneg).applyRows (coordinateDirection 1 0 0) (coordinateDirection 1 0 1) =
      H.applyRows (coordinateDirection 1 0 0) (coordinateDirection 1 0 1))
    (hY : H.yy = (1 / 2 : ℝ) • (Lpos.mean yy + Lneg.mean yy))
    (hJump : θ / 10 ≤ Lneg curvature - H.q)
    (hBpos : Lpos energy ≤ B) (hBneg : Lneg energy ≤ B) :
    H.energy + θ ^ 2 / (400 * K ^ 2) ≤ B :=
  let ht := Hess3.vertical_mean_of_applyRows_eq (meanHessian Lneg) H hT
  PositiveFunctional.vertical_linear_parent_energy_le Lpos Lneg xx xy yy H K θ B hK hθ
    ht.1 ht.2 (entry_moment_bounds Lneg).1 hY hJump hBpos hBneg

end HessianBall

end C2Riemannian
