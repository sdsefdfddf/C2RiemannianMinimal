module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open scoped BigOperators

namespace C2Riemannian

public abbrev Plane := EuclideanSpace ℝ (Fin 2)

public abbrev Target (m : ℕ) := EuclideanSpace ℝ (Fin m)

/-- The three entries of a symmetric vector-valued Hessian. -/
public structure Hess3 (m : ℕ) where
  xx : Target m
  xy : Target m
  yy : Target m

namespace Hess3

variable {m : ℕ}

/-- The square of the Frobenius norm, counting both mixed entries. -/
@[expose] public noncomputable def frobeniusSq (H : Hess3 m) : ℝ :=
  ‖H.xx‖ ^ 2 + 2 * ‖H.xy‖ ^ 2 + ‖H.yy‖ ^ 2

@[expose] public noncomputable def frobenius (H : Hess3 m) : ℝ :=
  Real.sqrt H.frobeniusSq

/-- Sum of the componentwise Hessian determinants. -/
@[expose] public noncomputable def q (H : Hess3 m) : ℝ :=
  inner ℝ H.xx H.yy - inner ℝ H.xy H.xy

@[expose] public noncomputable def energy (H : Hess3 m) : ℝ :=
  ‖H.yy‖ ^ 2 / 2

@[expose] public def scale (c : ℝ) (H : Hess3 m) : Hess3 m :=
  ⟨c • H.xx, c • H.xy, c • H.yy⟩

public theorem frobeniusSq_nonneg (H : Hess3 m) : 0 ≤ H.frobeniusSq := by
  unfold frobeniusSq
  exact add_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (sq_nonneg _)))
    (sq_nonneg _)

public theorem sq_frobenius (H : Hess3 m) : H.frobenius ^ 2 = H.frobeniusSq :=
  Real.sq_sqrt H.frobeniusSq_nonneg

public theorem frobeniusSq_eq_norm_trace_sq_sub (H : Hess3 m) :
    H.frobeniusSq = ‖H.xx + H.yy‖ ^ 2 - 2 * H.q := by
  rw [norm_add_sq_real]
  simp only [frobeniusSq, q, real_inner_self_eq_norm_sq]
  ring

public theorem q_scale (c : ℝ) (H : Hess3 m) : (H.scale c).q = c ^ 2 * H.q := by
  simp only [q, scale, real_inner_smul_left, real_inner_smul_right]
  ring

public theorem abs_q_le (H : Hess3 m) : |H.q| ≤ H.frobenius ^ 2 / 2 := by
  rw [sq_frobenius, q, real_inner_self_eq_norm_sq]
  calc
    |inner ℝ H.xx H.yy - ‖H.xy‖ ^ 2| ≤ |inner ℝ H.xx H.yy| + |‖H.xy‖ ^ 2| :=
      abs_sub _ _
    _ = |inner ℝ H.xx H.yy| + ‖H.xy‖ ^ 2 := by
      have h : 0 ≤ ‖H.xy‖ ^ 2 := sq_nonneg _
      rw [abs_of_nonneg h]
    _ ≤ ‖H.xx‖ * ‖H.yy‖ + ‖H.xy‖ ^ 2 :=
      add_le_add (abs_real_inner_le_norm H.xx H.yy) le_rfl
    _ ≤ H.frobeniusSq / 2 := by
      unfold frobeniusSq
      nlinarith only [sq_nonneg (‖H.xx‖ - ‖H.yy‖)]

public theorem q_eq_sum_det (H : Hess3 m) :
    H.q = ∑ i : Fin m, (H.xx i * H.yy i - (H.xy i) ^ 2) := by
  rw [q, PiLp.inner_apply, PiLp.inner_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp [pow_two, mul_comm]

public theorem frobenius_nonneg (H : Hess3 m) : 0 ≤ H.frobenius :=
  Real.sqrt_nonneg _

public theorem frobenius_eq_zero_iff (H : Hess3 m) :
    H.frobenius = 0 ↔ H.xx = 0 ∧ H.xy = 0 ∧ H.yy = 0 := by
  constructor
  · intro heq
    have hsq := H.sq_frobenius
    rw [heq, zero_pow (by decide)] at hsq
    unfold frobeniusSq at hsq
    have hx : ‖H.xx‖ ^ 2 = 0 := by
      linarith only [hsq, sq_nonneg ‖H.xx‖, sq_nonneg ‖H.xy‖, sq_nonneg ‖H.yy‖]
    have hz : ‖H.xy‖ ^ 2 = 0 := by
      linarith only [hsq, sq_nonneg ‖H.xx‖, sq_nonneg ‖H.xy‖, sq_nonneg ‖H.yy‖]
    have hy : ‖H.yy‖ ^ 2 = 0 := by
      linarith only [hsq, sq_nonneg ‖H.xx‖, sq_nonneg ‖H.xy‖, sq_nonneg ‖H.yy‖]
    have zero_of_sq_zero (r : ℝ) (hr : r ^ 2 = 0) : r = 0 :=
      (mul_eq_zero.mp (by simpa only [pow_two] using hr)).elim id id
    exact ⟨norm_eq_zero.mp (zero_of_sq_zero _ hx), norm_eq_zero.mp (zero_of_sq_zero _ hz),
      norm_eq_zero.mp (zero_of_sq_zero _ hy)⟩
  · rintro ⟨hx, hz, hy⟩
    simp [frobenius, frobeniusSq, hx, hz, hy]

public theorem energy_nonneg (H : Hess3 m) : 0 ≤ H.energy := by
  exact div_nonneg (sq_nonneg _) (by norm_num)

public theorem energy_le (H : Hess3 m) : H.energy ≤ H.frobeniusSq / 2 := by
  have hxx : 0 ≤ ‖H.xx‖ ^ 2 := sq_nonneg _
  have hxy : 0 ≤ ‖H.xy‖ ^ 2 := sq_nonneg _
  unfold energy frobeniusSq
  linarith only [hxx, hxy]

end Hess3
end C2Riemannian
