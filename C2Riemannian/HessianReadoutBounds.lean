module

public import C2Riemannian.WeakHessianReadouts
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace C2Riemannian

namespace Hess3

/-- Individual Cartesian Hessian entries have norm at most the Frobenius norm. -/
public theorem entry_norms_le_frobenius {m : ℕ} (H : Hess3 m) :
    ‖H.xx‖ ≤ H.frobenius ∧ ‖H.xy‖ ≤ H.frobenius ∧ ‖H.yy‖ ≤ H.frobenius := by
  have h := H.sq_frobenius
  rw [Hess3.frobeniusSq] at h
  exact ⟨le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0) H.frobenius_nonneg (by nlinarith),
    le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0) H.frobenius_nonneg (by nlinarith),
    le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0) H.frobenius_nonneg (by nlinarith)⟩

end Hess3

namespace HessianBall

variable {m : ℕ} {K : ℝ}

/-- Reading the three Cartesian entries and restoring their Frobenius scaling
recovers the original point of the state space. -/
public theorem readout_coordinates (H : HessianBall m K) :
    (Hess3.mk (xx H) (xy H) (yy H)).coordinates = H.val := by
  apply (WithLp.ext_iff 2).mpr
  apply Prod.ext
  · rfl
  · apply (WithLp.ext_iff 2).mpr
    apply Prod.ext
    · change Real.sqrt 2 • ((Real.sqrt 2)⁻¹ • H.val.snd.fst) = H.val.snd.fst
      rw [smul_smul, mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (by norm_num)), one_smul]
    · rfl

public theorem readout_frobeniusSq_le (H : HessianBall m K) :
    (Hess3.mk (xx H) (xy H) (yy H)).frobeniusSq ≤ K ^ 2 := by
  rw [← Hess3.norm_coordinates_sq, readout_coordinates]
  have h := H.property
  rw [Metric.mem_closedBall, dist_zero_right] at h
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- The probability mean belongs to the same Hessian ball. -/
public theorem mean_frobenius_le (L : PositiveFunctional (HessianBall m K)) (hK : 0 ≤ K) :
    (Hess3.mk (L.mean xx) (L.mean xy) (L.mean yy)).frobenius ≤ K :=
  L.frobenius_mean_le xx xy yy K hK (fun H => readout_frobeniusSq_le H)

public theorem entry_moment_bounds (L : PositiveFunctional (HessianBall m K)) :
    L (sqNormReadout xx) ≤ K ^ 2 ∧
      L (sqNormReadout xy) ≤ K ^ 2 / 2 ∧
      L (sqNormReadout yy) ≤ K ^ 2 :=
  L.hess_entry_moment_bounds xx xy yy K (fun H => readout_frobeniusSq_le H)

end HessianBall

end C2Riemannian
