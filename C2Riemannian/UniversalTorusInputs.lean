module

public import C2Riemannian.QuantitativeObstruction
public import C2Riemannian.CompactInputNorm
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set
open scoped ContDiff NNReal

namespace C2Riemannian

/-- The fixed open square used in the torus input sequence. -/
@[expose] public def standardObstructionSquare : Set Plane :=
  {x | ‖x 0‖ < 1 / 4 ∧ ‖x 1‖ < 1 / 4}

public theorem standardObstructionSquare_open : IsOpen standardObstructionSquare := by
  have hc (i : Fin 2) : Continuous (fun x : Plane => ‖x i‖) :=
    (EuclideanSpace.proj i).continuous.norm
  exact (isOpen_lt (hc 0) continuous_const).inter (isOpen_lt (hc 1) continuous_const)

public theorem standardObstructionSquare_nonempty : standardObstructionSquare.Nonempty := by
  refine ⟨0, ?_⟩
  norm_num [standardObstructionSquare]

private theorem standardObstructionSquare_subset_half :
    standardObstructionSquare ⊆ Metric.ball (0 : Plane) (1 / 2) := by
  intro x hx
  obtain ⟨hx₀, hx₁⟩ := hx
  rw [Metric.mem_ball, dist_zero_right]
  by_contra! hn
  have hSq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hn 2
  have h₀ := pow_le_pow_left₀ (norm_nonneg _) hx₀.le 2
  have h₁ := pow_le_pow_left₀ (norm_nonneg _) hx₁.le 2
  have hF := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ) x
  rw [Fin.sum_univ_two] at hF
  nlinarith only [hSq, h₀, h₁, hF]

public theorem standardObstructionSquare_closure :
    closure standardObstructionSquare ⊆ Metric.ball (0 : Plane) 1 :=
  (closure_mono standardObstructionSquare_subset_half).trans
    (Metric.closure_ball_subset_closedBall.trans (Metric.closedBall_subset_ball (by norm_num)))

/-- A sequence chosen once for all dimensions and bounds. Its n-th entry
obstructs dimension n+1 and Hessian bound n+1 on the unit disk. -/
public structure UniversalTorusInputs where
  profile : ℕ → Plane → ℝ
  smooth : ∀ n, ContDiff ℝ ∞ (profile n)
  supported : ∀ n, tsupport (profile n) ⊆ standardObstructionSquare
  hessian_bound : ∀ n x, tensorHS (iteratedFDeriv ℝ 2 (profile n) x) ≤ 1
  jet_bound : ∀ n, ‖closedUnitDiskJet ((smooth n).of_le (by simp))‖ ≤ 2
  not_solvable : ∀ n,
    ¬ WeakJet2.DiskSolvability.Solves (n + 1) 0 1 ((n + 1 : ℕ) : ℝ≥0)
      (fun x => -WeakJet2.metricYY (profile n) x / 2)

private theorem exists_bad_unit_disk_input (n : ℕ) :
    ∃ f : Plane → ℝ, ContDiff ℝ ∞ f ∧ tsupport f ⊆ standardObstructionSquare ∧
      (∀ x, tensorHS (iteratedFDeriv ℝ 2 f x) ≤ 1) ∧
      ¬ WeakJet2.DiskSolvability.Solves (n + 1) 0 1 ((n + 1 : ℕ) : ℝ≥0)
        (fun x => -WeakJet2.metricYY f x / 2) := by
  let K : ℝ≥0 := ((n + 1 : ℕ) : ℝ≥0)
  have hK : (1 : ℝ) ≤ (K : ℝ) := by
    change 1 ≤ ((n + 1 : ℕ) : ℝ)
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  let N := ObstructionParameters.tableCount K 1
  let J := ObstructionParameters.cycleCount K 1
  obtain ⟨hN, hJ, _, _, hNegative, _⟩ :=
    ObstructionParameters.root_budgets_negative (K : ℝ) 1 hK zero_lt_one le_rfl
  have hInside := subset_closure.trans standardObstructionSquare_closure
  have hQ : Bornology.IsBounded standardObstructionSquare := Metric.isBounded_ball.subset hInside
  obtain ⟨T⟩ := exists_realized_parameter_tree hQ standardObstructionSquare_open
    standardObstructionSquare_nonempty N J hN hJ
  let Solves := fun z : PhysicalPrefix standardObstructionSquare =>
    WeakJet2.DiskSolvability.Solves (n + 1) 0 1 K (z.linearSource (fun _ => 0) 1)
  have hBad : ¬ ∀ path, Solves (T.toParameterTree.leafAt path) := by
    intro hAll
    have hGood := ParameterTree.good_of_everyLeaf Solves T.toParameterTree
      (ParameterTree.everyLeaf_of_solvable_paths Solves T.toParameterTree hAll)
    have hBudget := linear_root_budget_nonneg (N := N) (J := J) T hInside hQ hN
      (Nat.succ_pos n) zero_lt_one hK (v₀ := fun _ => 0) contDiffOn_const 1
      zero_le_one le_rfl hGood
    exact (not_lt_of_ge hBudget) hNegative
  obtain ⟨path, hPath⟩ := not_forall.mp hBad
  let p := T.toParameterTree.leafAt path
  have hSupp : tsupport p.input ⊆ standardObstructionSquare := by
    change tsupport ((fun _ : Plane => (1 / 5 : ℝ)) • p.secondPotential) ⊆ _
    exact (tsupport_smul_subset_right (fun _ : Plane => (1 / 5 : ℝ)) p.secondPotential).trans
      p.support_second
  have hMember : p.input ∈ T.terminalInputs := ⟨path, rfl⟩
  refine ⟨p.input, p.input_smooth, hSupp, ?_, ?_⟩
  · intro x
    have h := bounded_terminal_input_hessian T hMember x
    have hSqrt : √(11 / 2 : ℝ) ≤ 4 := by
      calc
        _ ≤ √(16 : ℝ) := Real.sqrt_le_sqrt (by norm_num)
        _ = _ := by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    exact h.trans (by linarith only [hSqrt])
  · change ¬ WeakJet2.DiskSolvability.Solves (n + 1) 0 1 K
      (p.linearSource (fun _ => 0) 1) at hPath
    have hCoeff : p.metricCoefficient (fun _ => 0) 1 = p.input := by
      funext x
      simp [PhysicalPrefix.metricCoefficient]
    unfold PhysicalPrefix.linearSource at hPath
    rwa [hCoeff] at hPath

/-- Choose the entire sequence before selecting the metric amplitude or a candidate immersion. -/
public theorem exists_countable_obstructing_inputs : Nonempty UniversalTorusInputs := by
  have hEvery := exists_bad_unit_disk_input
  choose f hf hs hH hb using hEvery
  refine ⟨⟨f, hf, hs, hH, ?_, hb⟩⟩
  intro n
  exact support_unit_disk_hess_bound_to_C2 _ ((hs n).trans
    (subset_closure.trans standardObstructionSquare_closure)) (fun x _ => hH n x)

end C2Riemannian
