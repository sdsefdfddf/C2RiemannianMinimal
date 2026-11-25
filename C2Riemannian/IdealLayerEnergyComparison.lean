module

public import C2Riemannian.IdealLayerEnergy
public import C2Riemannian.ExactLayerJumpProfiles
public import C2Riemannian.SameDiskTangency
public import C2Riemannian.CycleGainArithmetic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace C2Riemannian.HessianBall

variable {m : ℕ} {K : ℝ} {Q : Set Plane}

/-- The signed gain in the linear-source comparison for one scheduled physical layer. -/
public theorem linear_layer_energy_comparison
    (p : PhysicalPrefix Q) (i : p.Active) (layer : IdealLayer) (s θ : ℝ)
    (hσ : (p.ideal i.1).sigma ^ 2 = 1) (hs : 0 ≤ s) (hs' : s ≤ 1)
    (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) (hK : 1 ≤ K)
    (H : Hess3 m) (L : Bool → PositiveFunctional (HessianBall m K)) (B : ℝ)
    (hH : H.frobenius ≤ K)
    (hY : H.yy = (1 / 2 : ℝ) • ((L true).mean yy + (L false).mean yy))
    (hPhase : ∀ b, (meanHessian (L b)).applyRows (layer.tangent s 0) (layer.tangent s 1) =
      H.applyRows (layer.tangent s 0) (layer.tangent s 1) ∧
      L b curvature - H.q = PhysicalLayerRow.linearJump p layer s θ i b ∧
      (layer.step.continues b = true → L b energy ≤ B)) :
    H.energy + (CycleGainArithmetic.layer_gain_schedule s K θ 0 layer.step).1 ≤ B := by
  have hpos := (hPhase true).2.2 (SplitStep.positive_continues layer.step)
  have hObl {t : ℝ} (ht : |t| = s)
      (hStep : layer.step = .first ∨ layer.step = .third)
      (hT : (meanHessian (L true)).applyRows (coordinateDirection (-t) 1 0) (coordinateDirection (-t) 1 1) =
        H.applyRows (coordinateDirection (-t) 1 0) (coordinateDirection (-t) 1 1)) :
      H.energy + -(7 * K ^ 2 * s ^ 3) ≤ B := by
    have hJump := (p.ideal i.1).oblique_positive_linear_jump layer hStep s θ hθ hθ' hσ
    have htsq : t ^ 2 = s ^ 2 := by
      rw [← ht, sq_abs]
    have hLower : -(t ^ 2 / 10) ≤ L true curvature - H.q := by
      rw [htsq, (hPhase true).2.1]
      exact hJump
    simpa only [ht] using table_linear_energy (L true) H t B hK (ht.trans_le hs') hH hT hLower hpos
  cases hstep : layer.step with
  | vertical =>
    have hneg := (hPhase false).2.2 (by simp [hstep, SplitStep.continues])
    have ht : (meanHessian (L false)).applyRows (coordinateDirection 1 0 0) (coordinateDirection 1 0 1) =
        H.applyRows (coordinateDirection 1 0 0) (coordinateDirection 1 0 1) := by
      simpa only [IdealLayer.tangent, hstep] using (hPhase false).1
    have hj : θ / 10 ≤ L false curvature - H.q := by
      rw [(hPhase false).2.1, PhysicalLayerRow.linearJump,
        (p.ideal i.1).vertical_negative_linear_jump layer hstep s θ]
    simpa only [hstep, CycleGainArithmetic.layer_gain_schedule] using
      vertical_linear_energy_of_tangent (L true) (L false) H θ B (zero_lt_one.trans_le hK) hθ
        ht hY hj hpos hneg
  | first =>
    have ht := hObl (t := s) (abs_of_nonneg hs) (Or.inl hstep) (by
      simpa only [IdealLayer.tangent, hstep] using (hPhase true).1)
    simpa only [hstep, CycleGainArithmetic.layer_gain_schedule] using ht
  | third =>
    have ht := hObl (t := -s) (by rw [abs_neg, abs_of_nonneg hs]) (Or.inr hstep) (by
      simpa only [IdealLayer.tangent, hstep, neg_neg] using (hPhase true).1)
    simpa only [hstep, CycleGainArithmetic.layer_gain_schedule] using ht
  | second =>
    simpa only [hstep, CycleGainArithmetic.layer_gain_schedule, add_zero] using
      horizontal_energy_of_tangent (L true) H B (by
        simpa only [IdealLayer.tangent, hstep] using (hPhase true).1) hpos
  | fourth =>
    simpa only [hstep, CycleGainArithmetic.layer_gain_schedule, add_zero] using
      horizontal_energy_of_tangent (L true) H B (by
        simpa only [IdealLayer.tangent, hstep] using (hPhase true).1) hpos

/-- The signed reverse-source comparison uses the actual positive-phase jump
on an oblique row. Here the gain retains its sign throughout. -/
public theorem reverse_layer_energy_comparison
    (p : PhysicalPrefix Q) (i : p.Active) (layer : IdealLayer) (s : ℝ)
    (hs : 0 ≤ s) (hs' : s ≤ 1) (hK : 0 ≤ K)
    (H : Hess3 m) (L : Bool → PositiveFunctional (HessianBall m K)) (B g : ℝ)
    (hH : H.frobenius ≤ K)
    (hY : H.yy = (1 / 2 : ℝ) • ((L true).mean yy + (L false).mean yy))
    (hPhase : ∀ b, (meanHessian (L b)).applyRows (layer.tangent s 0) (layer.tangent s 1) =
      H.applyRows (layer.tangent s 0) (layer.tangent s 1) ∧
      L b curvature - H.q = PhysicalLayerRow.reverseJump p layer s i b ∧
      (layer.step.continues b = true → L b energy ≤ B))
    (hGain : g ≤ match layer.step with
      | .first | .third => s ^ 2 * PhysicalLayerRow.reverseJump p layer s i true - 7 * K ^ 2 * s ^ 3
      | _ => 0) :
    H.energy + g ≤ B := by
  have hpos := (hPhase true).2.2 (SplitStep.positive_continues layer.step)
  have hObl {t : ℝ} (ht : |t| = s)
      (hT : (meanHessian (L true)).applyRows (coordinateDirection (-t) 1 0) (coordinateDirection (-t) 1 1) =
        H.applyRows (coordinateDirection (-t) 1 0) (coordinateDirection (-t) 1 1)) :
      H.energy + (s ^ 2 * PhysicalLayerRow.reverseJump p layer s i true - 7 * K ^ 2 * s ^ 3) ≤ B := by
    have htsq : t ^ 2 = s ^ 2 := by rw [← ht, sq_abs]
    have hJump : t ^ 2 * (L true curvature - H.q) = s ^ 2 * PhysicalLayerRow.reverseJump p layer s i true := by
      rw [htsq, (hPhase true).2.1]
    simpa only [ht] using table_reverse_energy (L true) H t B _ hK (ht.trans_le hs') hH hT hJump hpos
  cases hstep : layer.step with
  | vertical =>
    have hneg := (hPhase false).2.2 (by simp [hstep, SplitStep.continues])
    have h := PositiveFunctional.vertical_reverse_parent_energy_le (L true) (L false) yy H B hY hpos hneg
    linarith only [h, (show g ≤ 0 by simpa only [hstep] using hGain)]
  | first =>
    have h := hObl (t := s) (abs_of_nonneg hs) (by simpa only [IdealLayer.tangent, hstep] using (hPhase true).1)
    have hg : g ≤ s ^ 2 * PhysicalLayerRow.reverseJump p layer s i true - 7 * K ^ 2 * s ^ 3 := by
      simpa only [hstep] using hGain
    linarith only [h, hg]
  | third =>
    have h := hObl (t := -s) (by rw [abs_neg, abs_of_nonneg hs]) (by
      simpa only [IdealLayer.tangent, hstep, neg_neg] using (hPhase true).1)
    have hg : g ≤ s ^ 2 * PhysicalLayerRow.reverseJump p layer s i true - 7 * K ^ 2 * s ^ 3 := by
      simpa only [hstep] using hGain
    linarith only [h, hg]
  | second =>
    have h := horizontal_energy_of_tangent (L true) H B (by
      simpa only [IdealLayer.tangent, hstep] using (hPhase true).1) hpos
    linarith only [h, (show g ≤ 0 by simpa only [hstep] using hGain)]
  | fourth =>
    have h := horizontal_energy_of_tangent (L true) H B (by
      simpa only [IdealLayer.tangent, hstep] using (hPhase true).1) hpos
    linarith only [h, (show g ≤ 0 by simpa only [hstep] using hGain)]

end C2Riemannian.HessianBall
