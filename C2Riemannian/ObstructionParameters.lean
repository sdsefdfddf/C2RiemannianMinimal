module

public import C2Riemannian.CycleGainArithmetic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open scoped BigOperators

namespace C2Riemannian.ObstructionParameters

/-- Number of four-row table blocks in each cycle, as chosen in Equation (30). -/
@[expose] public noncomputable def tableCount (K theta : ℝ) : ℕ :=
  max 2 ⌈(5600 * K ^ 4 / theta ^ 2) ^ 2 / 2⌉₊

/-- Number of cycles in Equation (30). -/
@[expose] public noncomputable def cycleCount (K theta : ℝ) : ℕ :=
  ⌈800 * K ^ 4 / theta ^ 2⌉₊

@[expose] public noncomputable def slope (N : ℕ) : ℝ :=
  1 / Real.sqrt (2 * (N : ℝ))

/-- The slope lies in the geometric range and satisfies the normalization in M40. -/
public theorem slope_bounds (N : ℕ) (hN : 2 ≤ N) :
    0 < slope N ∧ slope N ≤ 1 / 2 ∧ 2 * (N : ℝ) * slope N ^ 2 = 1 := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have h4 : (2 : ℝ) ^ 2 ≤ 2 * (N : ℝ) := by linarith only [hNr]
  have hrad : 0 < 2 * (N : ℝ) := by linarith only [hNr]
  have hsqrt : 0 < Real.sqrt (2 * (N : ℝ)) := Real.sqrt_pos.2 hrad
  have htwo : (2 : ℝ) ≤ Real.sqrt (2 * (N : ℝ)) := by
    calc
      (2 : ℝ) = Real.sqrt (2 ^ 2) := (Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)).symm
      _ ≤ Real.sqrt (2 * (N : ℝ)) := Real.sqrt_le_sqrt h4
  refine ⟨div_pos one_pos hsqrt, one_div_le_one_div_of_le (by norm_num) htwo, ?_⟩
  unfold slope
  rw [div_pow, one_pow, Real.sq_sqrt hrad.le]
  exact mul_one_div_cancel (ne_of_gt hrad)

/-- For the choices in Equation (30), each accumulated gain is at least `K ^ 2`. -/
public theorem parameter_bounds (K theta : ℝ) (hK : 1 ≤ K) (htheta : 0 < theta)
    (htheta1 : theta ≤ 1) :
    let N := tableCount K theta
    let J := cycleCount K theta
    2 ≤ N ∧ 1 ≤ J ∧
      K ^ 2 ≤ (J : ℝ) * (theta ^ 2 / (400 * K ^ 2) -
        7 * K ^ 2 / Real.sqrt (2 * (N : ℝ))) ∧
      K ^ 2 ≤ (J : ℝ) * ((1 / 2 - 1 / (4 * (N : ℝ))) / 25 -
        7 * K ^ 2 / Real.sqrt (2 * (N : ℝ))) := by
  let D : ℝ := 5600 * K ^ 4 / theta ^ 2
  let U : ℝ := 800 * K ^ 4 / theta ^ 2
  let N : ℕ := max 2 ⌈D ^ 2 / 2⌉₊
  let J : ℕ := ⌈U⌉₊
  change 2 ≤ N ∧ 1 ≤ J ∧
    K ^ 2 ≤ (J : ℝ) * (theta ^ 2 / (400 * K ^ 2) -
      7 * K ^ 2 / Real.sqrt (2 * (N : ℝ))) ∧
    K ^ 2 ≤ (J : ℝ) * ((1 / 2 - 1 / (4 * (N : ℝ))) / 25 -
      7 * K ^ 2 / Real.sqrt (2 * (N : ℝ)))
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hthetasq : 0 < theta ^ 2 := pow_pos htheta 2
  have hKsq : 0 < K ^ 2 := pow_pos hK0 2
  have hKfour : 0 < K ^ 4 := pow_pos hK0 4
  have hD : 0 < D := div_pos (mul_pos (by norm_num) hKfour) hthetasq
  have hU : 0 < U := div_pos (mul_pos (by norm_num) hKfour) hthetasq
  have hN : 2 ≤ N := le_max_left _ _
  have hJ : 1 ≤ J := Nat.one_le_ceil_iff.mpr hU
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNc : (⌈D ^ 2 / 2⌉₊ : ℝ) ≤ N := Nat.cast_le.mpr (le_max_right _ _)
  have hDs : D ^ 2 / 2 ≤ (N : ℝ) := (Nat.le_ceil _).trans hNc
  have hJr : U ≤ (J : ℝ) := Nat.le_ceil U
  have hsquare : D ^ 2 ≤ 2 * (N : ℝ) := by linarith only [hDs]
  have hsqrt : D ≤ Real.sqrt (2 * (N : ℝ)) := by
    rw [← Real.sqrt_sq hD.le]
    exact Real.sqrt_le_sqrt hsquare
  let v : ℝ := theta ^ 2 / (800 * K ^ 2)
  have hv : 0 < v := div_pos hthetasq (mul_pos (by norm_num) hKsq)
  have hratio : 7 * K ^ 2 / D = v := by
    dsimp [D, v]
    field_simp [ne_of_gt htheta, ne_of_gt hK0]
    ring
  have hloss : 7 * K ^ 2 / Real.sqrt (2 * (N : ℝ)) ≤ v := by
    rw [← hratio]
    exact div_le_div_of_nonneg_left (by positivity) hD hsqrt
  have hlinear : theta ^ 2 / (400 * K ^ 2) = 2 * v := by
    dsimp [v]
    field_simp [ne_of_gt hK0]
    ring
  have hideal : (3 / 200 : ℝ) ≤ (1 / 2 - 1 / (4 * (N : ℝ))) / 25 := by
    have h4 : (8 : ℝ) ≤ 4 * (N : ℝ) := by linarith only [hNr]
    have hdiv : (1 : ℝ) / (4 * (N : ℝ)) ≤ 1 / 8 :=
      one_div_le_one_div_of_le (by norm_num) h4
    linarith only [hdiv]
  have hthetasq_le : theta ^ 2 ≤ 1 := by nlinarith only [mul_nonneg htheta.le (sub_nonneg.mpr htheta1), htheta1]
  have hKsq_ge : 1 ≤ K ^ 2 := by nlinarith only [mul_nonneg hK0.le (sub_nonneg.mpr hK), hK]
  have hle : theta ^ 2 / (400 * K ^ 2) ≤ 3 / 200 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hKsq)).2
    nlinarith only [hthetasq_le, hKsq_ge]
  have hgl : v ≤ theta ^ 2 / (400 * K ^ 2) - 7 * K ^ 2 / Real.sqrt (2 * (N : ℝ)) := by
    linarith only [hloss, hlinear]
  have hgr : v ≤ (1 / 2 - 1 / (4 * (N : ℝ))) / 25 -
        7 * K ^ 2 / Real.sqrt (2 * (N : ℝ)) := by
    linarith only [hloss, hlinear, hle, hideal]
  have hUv : U * v = K ^ 2 := by
    dsimp [U, v]
    field_simp [ne_of_gt htheta, ne_of_gt hK0]
  have hprod : K ^ 2 ≤ (J : ℝ) * v := by
    rw [← hUv]
    exact mul_le_mul_of_nonneg_right hJr hv.le
  exact ⟨hN, hJ, hprod.trans (mul_le_mul_of_nonneg_left hgl (Nat.cast_nonneg J)),
    hprod.trans (mul_le_mul_of_nonneg_left hgr (Nat.cast_nonneg J))⟩


/-- The two root budgets from the terminal budget and all scheduled layers. -/
@[expose] public noncomputable def rootBudgets (N J : ℕ) (s K theta : ℝ) : ℝ × ℝ :=
  let gain := ∑ _ ∈ Finset.range J, CycleGainArithmetic.cycleGains N s K theta
  (K ^ 2 / 2 - gain.1, K ^ 2 / 2 - gain.2)

/-- Equation (30) makes both root budgets strictly negative on one schedule. -/
public theorem root_budgets_negative (K theta : ℝ) (hK : 1 ≤ K)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1) :
    let N := tableCount K theta
    let J := cycleCount K theta
    let s := slope N
    2 ≤ N ∧ 1 ≤ J ∧ 0 < s ∧ s ≤ 1 / 2 ∧
      (rootBudgets N J s K theta).1 < 0 ∧ (rootBudgets N J s K theta).2 < 0 := by
  let N := tableCount K theta
  let J := cycleCount K theta
  let s := slope N
  obtain ⟨hN, hJ, hLinear, hReverse⟩ := parameter_bounds K theta hK htheta htheta1
  obtain ⟨hs, hsHalf, hsNorm⟩ := slope_bounds N hN
  have hLoss : 7 * K ^ 2 * s = 7 * K ^ 2 / Real.sqrt (2 * (N : ℝ)) := by
    simp [s, slope, div_eq_mul_inv]
  have hKsq : 0 < K ^ 2 := pow_pos (zero_lt_one.trans_le hK) 2
  refine ⟨hN, hJ, hs, hsHalf, ?_, ?_⟩ <;>
    rw [rootBudgets, CycleGainArithmetic.cycle_total_gains N J s K theta hsNorm]
  · change K ^ 2 / 2 - (J : ℝ) * (theta ^ 2 / (400 * K ^ 2) - 7 * K ^ 2 * s) < 0
    rw [hLoss]
    linarith only [hLinear, hKsq]
  · change K ^ 2 / 2 - (J : ℝ) *
      ((1 / 2 - 1 / (4 * (N : ℝ))) / 25 - 7 * K ^ 2 * s) < 0
    rw [hLoss]
    linarith only [hReverse, hKsq]

end C2Riemannian.ObstructionParameters
