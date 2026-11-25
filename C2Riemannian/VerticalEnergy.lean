module

public import C2Riemannian.ObliqueEnergy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Vertical step energy, M39 (paper (25)) -/

set_option autoImplicit false

namespace C2Riemannian
namespace PositiveFunctional

variable {α : Type*} [TopologicalSpace α] {m : ℕ}

/-- The energy increase averaged over both vertical phases. -/
public theorem vertical_energy_eq (Lpos Lneg : PositiveFunctional α) (Y : C(α, Target m))
    (H₀ : Hess3 m) (hmean : Lpos.mean Y + Lneg.mean Y = (2 : ℝ) • H₀.yy) :
    (Lpos (energyReadout Y) + Lneg (energyReadout Y)) / 2 - H₀.energy =
      (Lpos (sqNormReadout (Y - ContinuousMap.const α H₀.yy)) +
        Lneg (sqNormReadout (Y - ContinuousMap.const α H₀.yy))) / 4 := by
  have hinner : inner ℝ H₀.yy (Lpos.mean Y) + inner ℝ H₀.yy (Lneg.mean Y) =
      2 * ‖H₀.yy‖ ^ 2 := by
    rw [← inner_add_right, hmean, real_inner_smul_right, real_inner_self_eq_norm_sq]
  simp only [energyReadout, map_smul, smul_eq_mul, Hess3.energy, translate_sqNorm]
  linarith only [hinner]

public theorem vertical_energy_nonneg (Lpos Lneg : PositiveFunctional α) (Y : C(α, Target m))
    (H₀ : Hess3 m) (hmean : Lpos.mean Y + Lneg.mean Y = (2 : ℝ) • H₀.yy) :
    0 ≤ (Lpos (energyReadout Y) + Lneg (energyReadout Y)) / 2 - H₀.energy := by
  rw [vertical_energy_eq Lpos Lneg Y H₀ hmean]
  exact div_nonneg (add_nonneg (Lpos.map_sqNormReadout_nonneg _) (Lneg.map_sqNormReadout_nonneg _))
    (by norm_num)

/-- A positive curvature increment bounds the second moment around the parent height. -/
public theorem vertical_second_moment (L : PositiveFunctional α)
    (X Z Y : C(α, Target m)) (H₀ : Hess3 m) (K δ : ℝ)
    (hK : 0 < K) (hδ : 0 ≤ δ) (hX : L.mean X = H₀.xx) (hZ : L.mean Z = H₀.xy)
    (hX₂ : L (sqNormReadout X) ≤ K ^ 2)
    (hjump : δ ≤ L (qReadout X Z Y) - H₀.q) :
    δ ^ 2 / K ^ 2 ≤ L (sqNormReadout (Y - ContinuousMap.const α H₀.yy)) := by
  let Y₀ := Y - ContinuousMap.const α H₀.yy
  have hlin : L (innerReadout X Y₀) = L (innerReadout X Y) - inner ℝ H₀.xx H₀.yy := by
    have h : innerReadout X Y₀ = innerReadout X Y - innerReadout X (ContinuousMap.const α H₀.yy) := by
      ext x
      simp only [Y₀, innerReadout_apply, ContinuousMap.sub_apply, ContinuousMap.const_apply,
        inner_sub_right]
    rw [h, map_sub, L.map_innerReadout_const_right, hX]
  have hZvar : L.variance Z = L (sqNormReadout Z) - ‖H₀.xy‖ ^ 2 := by
    rw [L.variance_eq, hZ]
  have hq : L (qReadout X Z Y) - H₀.q = L (innerReadout X Y₀) - L.variance Z := by
    simp only [qReadout, map_sub, Hess3.q, real_inner_self_eq_norm_sq, hlin, hZvar]
    ring
  have hδ' : δ ≤ L (innerReadout X Y₀) := by
    rw [hq] at hjump
    exact hjump.trans (sub_le_self _ (L.variance_nonneg Z))
  have hδ'' : δ ≤ K * √(L (sqNormReadout Y₀)) := by
    calc
      δ ≤ L (innerReadout X Y₀) := hδ'
      _ ≤ |L (innerReadout X Y₀)| := le_abs_self _
      _ ≤ √(L (sqNormReadout X)) * √(L (sqNormReadout Y₀)) := L.abs_map_innerReadout_le _ _
      _ ≤ K * √(L (sqNormReadout Y₀)) := by
        have hXsqrt := Real.sqrt_le_sqrt hX₂
        rw [Real.sqrt_sq hK.le] at hXsqrt
        exact mul_le_mul_of_nonneg_right hXsqrt (Real.sqrt_nonneg _)
  have hsquare : δ ^ 2 ≤ (K * √(L (sqNormReadout Y₀))) ^ 2 :=
    pow_le_pow_left₀ hδ hδ'' 2
  rw [mul_pow, Real.sq_sqrt (L.map_sqNormReadout_nonneg Y₀)] at hsquare
  exact (div_le_iff₀ (pow_pos hK _)).mpr (by simpa only [mul_comm] using hsquare)

/-- The linear source supplies the gain through the negative vertical phase. -/
public theorem vertical_linear_energy_lower (Lpos Lneg : PositiveFunctional α)
    (X Z Y : C(α, Target m)) (H₀ : Hess3 m) (K θ : ℝ)
    (hK : 0 < K) (hθ : 0 ≤ θ) (hX : Lneg.mean X = H₀.xx) (hZ : Lneg.mean Z = H₀.xy)
    (hX₂ : Lneg (sqNormReadout X) ≤ K ^ 2)
    (hmean : Lpos.mean Y + Lneg.mean Y = (2 : ℝ) • H₀.yy)
    (hjump : θ / 10 ≤ Lneg (qReadout X Z Y) - H₀.q) :
    θ ^ 2 / (400 * K ^ 2) ≤ (Lpos (energyReadout Y) + Lneg (energyReadout Y)) / 2 - H₀.energy := by
  have h := Lneg.vertical_second_moment X Z Y H₀ K (θ / 10) hK
    (div_nonneg hθ (by norm_num)) hX hZ hX₂ hjump
  have hpos := Lpos.map_sqNormReadout_nonneg (Y - ContinuousMap.const α H₀.yy)
  rw [vertical_energy_eq Lpos Lneg Y H₀ hmean]
  calc
    θ ^ 2 / (400 * K ^ 2) = ((θ / 10) ^ 2 / K ^ 2) / 4 := by ring
    _ ≤ _ := by linarith only [h, hpos]

end PositiveFunctional
end C2Riemannian
