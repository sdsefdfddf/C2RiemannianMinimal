module

public import C2Riemannian.IdealSchedule
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open scoped BigOperators

namespace C2Riemannian

namespace CycleGainArithmetic

/-- The vertical coefficient at the beginning of table block `j`. -/
@[expose] public noncomputable def coefficient (s : ℝ) (j : ℕ) : ℝ :=
  1 - 2 * (j : ℝ) * s ^ 2

/-- The contributions (t^2 (F_+ - F_0)) for the two sloped rows. -/
public theorem reverse_row_signed_gain (s sigma c : ℝ) (hsigma : sigma ^ 2 = 1) :
    let A₁ : ScalarHess := ⟨0, 0, sigma * c⟩
    let A₃ : ScalarHess := ⟨0, -sigma * s, sigma * (c - s ^ 2)⟩
    s ^ 2 * ((SplitStep.first.scalarChild A₁ s sigma true).reverseSource -
      A₁.reverseSource) = s ^ 2 * c / 25 ∧
    (-s) ^ 2 * ((SplitStep.third.scalarChild A₃ s sigma true).reverseSource -
      A₃.reverseSource) = s ^ 2 * (c - 3 * s ^ 2) / 25 := by
  simp only [SplitStep.scalarChild, ite_true, one_mul, ScalarHess.reverseSource_rankOne]
  constructor
  · calc
      _ = sigma ^ 2 * (s ^ 2 * c / 25) := by ring
      _ = _ := by rw [hsigma, one_mul]
  · calc
      _ = sigma ^ 2 * (s ^ 2 * (c - 3 * s ^ 2) / 25) := by ring
      _ = _ := by rw [hsigma, one_mul]

/-- Sum of the two sloped contributions over the table, for a free parameter `s`. -/
public theorem reverse_table_sum (N : ℕ) (s : ℝ) :
    (∑ j ∈ Finset.range N, s ^ 2 * (2 * coefficient s j - 3 * s ^ 2) / 25) =
      ((1 - coefficient s N ^ 2) / 2 - (N : ℝ) * s ^ 4) / 25 := by
  induction N with
  | zero => norm_num [coefficient]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [coefficient, Nat.cast_succ]
    ring

/-- With the normalized slope, the third row of the final block contributes negatively. -/
public theorem reverse_last_third_gain (N : ℕ) (s : ℝ)
    (h : 2 * (N.succ : ℝ) * s ^ 2 = 1) :
    s ^ 2 * (coefficient s N - 3 * s ^ 2) / 25 = -s ^ 4 / 25 := by
  have hc : coefficient s N = 2 * s ^ 2 := by
    simp only [coefficient, Nat.cast_succ] at *
    linarith only [h]
  rw [hc]
  ring

public theorem reverse_cycle_sum (N : ℕ) (s : ℝ) (h : 2 * (N : ℝ) * s ^ 2 = 1) :
    (∑ j ∈ Finset.range N, s ^ 2 * (2 * coefficient s j - 3 * s ^ 2) / 25) =
      (1 / 2 - 1 / (4 * (N : ℝ))) / 25 := by
  have hN : (N : ℝ) ≠ 0 := by
    intro hz
    simp [hz] at h
  have hFourth : (N : ℝ) * s ^ 4 = 1 / (4 * (N : ℝ)) := by
    field_simp
    nlinarith only [congrArg (fun x : ℝ ↦ x ^ 2) h]
  rw [reverse_table_sum, hFourth]
  simp [coefficient, h]

/-- The linear and reverse source gains at a layer of table block `j`.
The vertical layer precedes all blocks, and its gains are independent of `j`. -/
@[expose] public noncomputable def layer_gain_schedule
    (s K theta : ℝ) (j : ℕ) (step : SplitStep) : ℝ × ℝ :=
  let loss := 7 * K ^ 2 * s ^ 3
  match step with
  | .vertical => (theta ^ 2 / (400 * K ^ 2), 0)
  | .first => (-loss, s ^ 2 * coefficient s j / 25 - loss)
  | .second => (0, 0)
  | .third => (-loss, s ^ 2 * (coefficient s j - 3 * s ^ 2) / 25 - loss)
  | .fourth => (0, 0)

/-- One cycle, including its vertical layer and the four layers in each table block. -/
@[expose] public noncomputable def cycleGains (N : ℕ) (s K theta : ℝ) : ℝ × ℝ :=
  let gain := layer_gain_schedule s K theta
  gain 0 .vertical +
    ∑ j ∈ Finset.range N, (gain j .first + gain j .second + gain j .third + gain j .fourth)

private theorem sum_fst (t : Finset ℕ) (f : ℕ → ℝ × ℝ) :
    (∑ j ∈ t, f j).1 = ∑ j ∈ t, (f j).1 :=
  map_sum (AddMonoidHom.fst ℝ ℝ) f t

private theorem sum_snd (t : Finset ℕ) (f : ℕ → ℝ × ℝ) :
    (∑ j ∈ t, f j).2 = ∑ j ∈ t, (f j).2 :=
  map_sum (AddMonoidHom.snd ℝ ℝ) f t
public theorem cycle_gains (N : ℕ) (s K theta : ℝ) (h : 2 * (N : ℝ) * s ^ 2 = 1) :
    cycleGains N s K theta =
      (theta ^ 2 / (400 * K ^ 2) - 7 * K ^ 2 * s,
        (1 / 2 - 1 / (4 * (N : ℝ))) / 25 - 7 * K ^ 2 * s) := by
  have hLoss : (N : ℝ) * (2 * (7 * K ^ 2 * s ^ 3)) = 7 * K ^ 2 * s := by
    calc
      _ = 7 * K ^ 2 * s * (2 * (N : ℝ) * s ^ 2) := by ring
      _ = _ := by rw [h, mul_one]
  have hBlock (j : ℕ) :
      s ^ 2 * coefficient s j / 25 - 7 * K ^ 2 * s ^ 3 +
        (s ^ 2 * (coefficient s j - 3 * s ^ 2) / 25 - 7 * K ^ 2 * s ^ 3) =
      s ^ 2 * (2 * coefficient s j - 3 * s ^ 2) / 25 - 2 * (7 * K ^ 2 * s ^ 3) := by ring
  apply Prod.ext
  · simp [cycleGains, layer_gain_schedule, sum_fst, ← two_mul, nsmul_eq_mul, hLoss, sub_eq_add_neg]
  · simp [cycleGains, layer_gain_schedule, sum_snd, hBlock,
      Finset.sum_sub_distrib, reverse_cycle_sum N s h, nsmul_eq_mul, hLoss]

public theorem cycle_total_gains (N J : ℕ) (s K theta : ℝ) (h : 2 * (N : ℝ) * s ^ 2 = 1) :
    (∑ _ ∈ Finset.range J, cycleGains N s K theta) =
      ((J : ℝ) * (theta ^ 2 / (400 * K ^ 2) - 7 * K ^ 2 * s),
        (J : ℝ) * ((1 / 2 - 1 / (4 * (N : ℝ))) / 25 - 7 * K ^ 2 * s)) := by
  apply Prod.ext
  · simp [cycle_gains N s K theta h, nsmul_eq_mul]
  · simp [cycle_gains N s K theta h, nsmul_eq_mul]

/-- For the two-block cycle the last third-row contribution is negative. -/
public theorem reverse_two_block_check :
    (∑ j ∈ Finset.range 2, (1 / 2 : ℝ) ^ 2 *
      (2 * coefficient (1 / 2) j - 3 * (1 / 2) ^ 2) / 25) = 3 / 200 ∧
    (1 / 2 : ℝ) ^ 2 * (coefficient (1 / 2) 1 - 3 * (1 / 2) ^ 2) / 25 = -1 / 400 := by
  constructor
  · rw [reverse_cycle_sum 2 (1 / 2) (by norm_num)]
    norm_num
  · rw [reverse_last_third_gain 1 (1 / 2) (by norm_num)]
    norm_num
end CycleGainArithmetic

end C2Riemannian
