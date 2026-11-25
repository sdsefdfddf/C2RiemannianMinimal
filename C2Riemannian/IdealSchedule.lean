module

public import C2Riemannian.RankOneDet
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace C2Riemannian

public inductive SplitStep where
  | vertical | first | second | third | fourth
  deriving DecidableEq

namespace SplitStep

@[expose] public def cycle (N : ℕ) : List SplitStep :=
  .vertical :: (List.replicate N [first, second, third, fourth]).flatten

@[expose] public def schedule (N J : ℕ) : List SplitStep :=
  (List.replicate J (cycle N)).flatten

@[expose] public def continues (step : SplitStep) (positive : Bool) : Bool :=
  positive || step == vertical

@[expose] public noncomputable def scalarChild (step : SplitStep) (A : ScalarHess)
    (s sigma : ℝ) (positive : Bool) : ScalarHess :=
  let e : ℝ := if positive then 1 else -1
  match step with
  | .vertical => A.rankOneUpdate e 0 1
  | .first => A.rankOneUpdate (e * -sigma) 1 s
  | .second => A.rankOneUpdate (e * sigma) 1 0
  | .third => A.rankOneUpdate (e * -sigma) 1 (-s)
  | .fourth => A.rankOneUpdate (e * sigma) 1 0

public theorem cycle_length (N : ℕ) : (cycle N).length = 4 * N + 1 := by
  simp [cycle, Nat.mul_comm, Nat.add_comm]

public theorem schedule_length (N J : ℕ) : (schedule N J).length = (4 * N + 1) * J := by
  simp [schedule, cycle_length, Nat.mul_comm]

public theorem positive_continues (step : SplitStep) : step.continues true = true := rfl

public theorem negative_continues_iff (step : SplitStep) :
    step.continues false = true ↔ step = vertical := by
  cases step <;> decide

public theorem filter_replicated_rows_length (P : SplitStep → Bool) (N : ℕ) :
    (((List.replicate N [first, second, third, fourth]).flatten).filter P).length =
      N * ([first, second, third, fourth].filter P).length := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.replicate_succ, List.flatten_cons, List.filter_append, List.length_append,
      ih, Nat.succ_mul, Nat.add_comm]

public theorem cycle_vertical_count (N : ℕ) :
    ((cycle N).filter (· == vertical)).length = 1 := by
  change (vertical :: ((List.replicate N [first, second, third, fourth]).flatten.filter
    (· == vertical))).length = 1
  rw [List.length_cons, filter_replicated_rows_length]
  change N * 0 + 1 = 1
  simp

public theorem cycle_oblique_count (N : ℕ) :
    ((cycle N).filter (fun step => step == first || step == third)).length = 2 * N := by
  change ((List.replicate N [first, second, third, fourth]).flatten.filter
    (fun step => step == first || step == third)).length = 2 * N
  rw [filter_replicated_rows_length]
  exact Nat.mul_comm N 2

public theorem cycle_horizontal_count (N : ℕ) :
    ((cycle N).filter (fun step => step == second || step == fourth)).length = 2 * N := by
  change ((List.replicate N [first, second, third, fourth]).flatten.filter
    (fun step => step == second || step == fourth)).length = 2 * N
  rw [filter_replicated_rows_length]
  exact Nat.mul_comm N 2

/-- The positive child after the four table rows, starting from `(0, 0, σ c)`. -/
public theorem scalar_four_positive (s sigma c : ℝ) :
    let A : ScalarHess := ⟨0, 0, sigma * c⟩
    let A₁ := first.scalarChild A s sigma true
    let A₂ := second.scalarChild A₁ s sigma true
    let A₃ := third.scalarChild A₂ s sigma true
    fourth.scalarChild A₃ s sigma true = ⟨0, 0, sigma * (c - 2 * s ^ 2)⟩ := by
  simp only [scalarChild, ite_true, ScalarHess.rankOneUpdate, ScalarHess.mk.injEq]
  constructor
  · ring
  constructor <;> ring

public theorem first_negative (s sigma c : ℝ) :
    first.scalarChild ⟨0, 0, sigma * c⟩ s sigma false =
      (⟨1, s, c + s ^ 2⟩ : ScalarHess).scale sigma := by
  simp [scalarChild, ScalarHess.rankOneUpdate, ScalarHess.scale]
  ring

public theorem second_negative (s sigma c : ℝ) :
    second.scalarChild ((⟨-1, -s, c - s ^ 2⟩ : ScalarHess).scale sigma) s sigma false =
      (⟨-2, -s, c - s ^ 2⟩ : ScalarHess).scale sigma := by
  simp [scalarChild, ScalarHess.rankOneUpdate, ScalarHess.scale]
  ring

public theorem third_negative (s sigma c : ℝ) :
    third.scalarChild ((⟨0, -s, c - s ^ 2⟩ : ScalarHess).scale sigma) s sigma false =
      (⟨1, -2 * s, c⟩ : ScalarHess).scale sigma := by
  simp [scalarChild, ScalarHess.rankOneUpdate, ScalarHess.scale]
  ring_nf
  trivial

public theorem fourth_negative (s sigma c : ℝ) :
    fourth.scalarChild ((⟨-1, 0, c - 2 * s ^ 2⟩ : ScalarHess).scale sigma) s sigma false =
      (⟨-2, 0, c - 2 * s ^ 2⟩ : ScalarHess).scale sigma := by
  simp [scalarChild, ScalarHess.rankOneUpdate, ScalarHess.scale]
  ring

public theorem first_positive (s sigma c : ℝ) :
    first.scalarChild ⟨0, 0, sigma * c⟩ s sigma true =
      (⟨-1, -s, c - s ^ 2⟩ : ScalarHess).scale sigma := by
  simp [scalarChild, ScalarHess.rankOneUpdate, ScalarHess.scale]
  ring

public theorem second_positive (s sigma c : ℝ) :
    second.scalarChild ((⟨-1, -s, c - s ^ 2⟩ : ScalarHess).scale sigma) s sigma true =
      (⟨0, -s, c - s ^ 2⟩ : ScalarHess).scale sigma := by
  simp [scalarChild, ScalarHess.rankOneUpdate, ScalarHess.scale]

public theorem third_positive (s sigma c : ℝ) :
    third.scalarChild ((⟨0, -s, c - s ^ 2⟩ : ScalarHess).scale sigma) s sigma true =
      (⟨-1, 0, c - 2 * s ^ 2⟩ : ScalarHess).scale sigma := by
  simp [scalarChild, ScalarHess.rankOneUpdate, ScalarHess.scale]
  ring

public theorem fourth_positive (s sigma c : ℝ) :
    fourth.scalarChild ((⟨-1, 0, c - 2 * s ^ 2⟩ : ScalarHess).scale sigma) s sigma true =
      (⟨0, 0, c - 2 * s ^ 2⟩ : ScalarHess).scale sigma := by
  simp [scalarChild, ScalarHess.rankOneUpdate, ScalarHess.scale]

public theorem stopped_row_bounds (s c : ℝ) (hs : s ^ 2 ≤ 1 / 4)
    (hc : 2 * s ^ 2 ≤ c) (hc' : c ≤ 1) :
    1 + 2 * s ^ 2 + (c + s ^ 2) ^ 2 ≤ 49 / 16 ∧
    4 + 2 * s ^ 2 + (c - s ^ 2) ^ 2 ≤ 11 / 2 ∧
    1 + 2 * (-2 * s) ^ 2 + c ^ 2 ≤ 4 ∧
    4 + (c - 2 * s ^ 2) ^ 2 ≤ 5 := by
  have hs0 : 0 ≤ s ^ 2 := sq_nonneg s
  have hsplus : (c + s ^ 2) ^ 2 ≤ (5 / 4 : ℝ) ^ 2 := by
    have h0 : 0 ≤ c + s ^ 2 := by linarith only [hc, hs0]
    have h1 : c + s ^ 2 ≤ 5 / 4 := by linarith only [hc', hs]
    exact pow_le_pow_left₀ h0 h1 2
  have hsminus : (c - s ^ 2) ^ 2 ≤ 1 ^ 2 := by
    have h0 : 0 ≤ c - s ^ 2 := by linarith only [hc, hs0]
    have h1 : c - s ^ 2 ≤ 1 := by linarith only [hc', hs0]
    exact pow_le_pow_left₀ h0 h1 2
  have hcsq : c ^ 2 ≤ 1 ^ 2 := by
    have h0 : 0 ≤ c := by linarith only [hc, hs0]
    exact pow_le_pow_left₀ h0 hc' 2
  have hlast : (c - 2 * s ^ 2) ^ 2 ≤ 1 ^ 2 := by
    have h0 : 0 ≤ c - 2 * s ^ 2 := sub_nonneg.mpr hc
    have h1 : c - 2 * s ^ 2 ≤ 1 := by linarith only [hc', hs0]
    exact pow_le_pow_left₀ h0 h1 2
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith only [hs, hsplus]
  · linarith only [hs, hsminus]
  · nlinarith only [hs, hcsq]
  · linarith only [hlast]

public theorem continuing_row_bounds (s c : ℝ) (hs : s ^ 2 ≤ 1 / 4)
    (hc : 2 * s ^ 2 ≤ c) (hc' : c ≤ 1) :
    1 + 2 * (-s) ^ 2 + (c - s ^ 2) ^ 2 ≤ 5 / 2 ∧
    2 * (-s) ^ 2 + (c - s ^ 2) ^ 2 ≤ 5 / 2 ∧
    1 + (c - 2 * s ^ 2) ^ 2 ≤ 5 / 2 ∧
    (c - 2 * s ^ 2) ^ 2 ≤ 5 / 2 := by
  have hs0 : 0 ≤ s ^ 2 := sq_nonneg s
  have hm : (c - s ^ 2) ^ 2 ≤ (1 : ℝ) ^ 2 := by
    have h0 : 0 ≤ c - s ^ 2 := by linarith only [hc, hs0]
    have h1 : c - s ^ 2 ≤ 1 := by linarith only [hc', hs0]
    exact pow_le_pow_left₀ h0 h1 2
  have hl : (c - 2 * s ^ 2) ^ 2 ≤ (1 : ℝ) ^ 2 := by
    have h0 : 0 ≤ c - 2 * s ^ 2 := sub_nonneg.mpr hc
    have h1 : c - 2 * s ^ 2 ≤ 1 := by linarith only [hc', hs0]
    exact pow_le_pow_left₀ h0 h1 2
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith only [hs, hm]
  · nlinarith only [hs, hm]
  · linarith only [hl]
  · linarith only [hl]

public theorem coefficient_bounds (N j : ℕ) (s : ℝ) (hj : j < N)
    (h : 2 * (N : ℝ) * s ^ 2 = 1) :
    2 * s ^ 2 ≤ 1 - 2 * (j : ℝ) * s ^ 2 ∧ 1 - 2 * (j : ℝ) * s ^ 2 ≤ 1 := by
  have hj' : (j : ℝ) + 1 ≤ N := by exact_mod_cast (Nat.succ_le_of_lt hj)
  have hs : 0 ≤ s ^ 2 := sq_nonneg s
  have hmul := mul_le_mul_of_nonneg_right hj' hs
  have h0 : 0 ≤ (j : ℝ) * s ^ 2 := mul_nonneg (Nat.cast_nonneg _) hs
  constructor <;> nlinarith only [hmul, h0, h]

@[expose] public noncomputable def scalarTableRun (N : ℕ) (A : ScalarHess)
    (s sigma : ℝ) : ScalarHess :=
  (List.replicate N [first, second, third, fourth]).flatten.foldl
    (fun parent step => step.scalarChild parent s sigma true) A

public theorem scalarTableRun_state (N : ℕ) (s sigma c : ℝ) :
    scalarTableRun N ⟨0, 0, sigma * c⟩ s sigma =
      ⟨0, 0, sigma * (c - 2 * (N : ℝ) * s ^ 2)⟩ := by
  induction N generalizing c with
  | zero => simp [scalarTableRun]
  | succ N ih =>
    unfold scalarTableRun
    rw [List.replicate_succ, List.flatten_cons, List.foldl_append]
    change scalarTableRun N
      (fourth.scalarChild
        (third.scalarChild (second.scalarChild (first.scalarChild ⟨0, 0, sigma * c⟩ s sigma true)
          s sigma true) s sigma true) s sigma true) s sigma = _
    rw [scalar_four_positive, ih, Nat.cast_succ]
    congr 1
    ring

public theorem scalarCycle_reset (N : ℕ) (s sigma : ℝ) (h : 2 * (N : ℝ) * s ^ 2 = 1) :
    scalarTableRun N ⟨0, 0, sigma⟩ s sigma = ⟨0, 0, 0⟩ := by
  have hstate := scalarTableRun_state N s sigma 1
  simpa [h] using hstate

end SplitStep

/-- A layer records the number of preceding nonvertical steps, which sets the fourth-order amplitude. -/
public structure IdealLayer where
  step : SplitStep
  priorTableSteps : ℕ

@[expose] public def idealLayers (prior : ℕ) : List SplitStep → List IdealLayer
  | [] => []
  | step :: steps =>
    ⟨step, prior⟩ :: idealLayers (if step == .vertical then prior else prior + 1) steps

public theorem idealLayers_steps (prior : ℕ) (steps : List SplitStep) :
    (idealLayers prior steps).map IdealLayer.step = steps := by
  induction steps generalizing prior with
  | nil => rfl
  | cons step steps ih => simp [idealLayers, ih]

/-- Physical histories use one sign per visited split. A stopped history retains its state. -/
public structure IdealNode where
  history : List Bool
  sigma : ℝ
  scalar : ScalarHess
  fourth : Fin 5 → ℝ
  active : Bool

namespace IdealNode

@[expose] public noncomputable def root : IdealNode := ⟨[], 1, ⟨0, 0, 0⟩, fun _ => 0, true⟩

@[expose] public noncomputable def child (node : IdealNode) (layer : IdealLayer)
    (s : ℝ) (positive : Bool) : IdealNode :=
  let e : ℝ := if positive then 1 else -1
  let fourth := match layer.step with
    | .vertical => node.fourth
    | .first => fun i => node.fourth i + e * 2 ^ layer.priorTableSteps * s ^ i.val
    | .second | .fourth => fun i => node.fourth i + e * 2 ^ layer.priorTableSteps * (0 : ℝ) ^ i.val
    | .third => fun i => node.fourth i + e * 2 ^ layer.priorTableSteps * (-s) ^ i.val
  ⟨node.history ++ [positive], if layer.step == .vertical then e else node.sigma,
    layer.step.scalarChild node.scalar s node.sigma positive, fourth, layer.step.continues positive⟩

@[expose] public noncomputable def split (node : IdealNode) (layer : IdealLayer)
    (s : ℝ) : List IdealNode :=
  if node.active then [node.child layer s true, node.child layer s false] else [node]

public theorem split_stopped (node : IdealNode) (layer : IdealLayer) (s : ℝ)
    (h : node.active = false) : node.split layer s = [node] := by
  simp [split, h]

@[expose] public noncomputable def run (layers : List IdealLayer) (s : ℝ) : List IdealNode :=
  layers.foldl (fun nodes layer => nodes.flatMap (fun node => node.split layer s)) [root]

public theorem split_has_active (node : IdealNode) (layer : IdealLayer) (s : ℝ)
    (h : node.active = true) :
    ∃ child ∈ node.split layer s, child.active = true := by
  exact ⟨node.child layer s true, by simp [split, h], layer.step.positive_continues⟩

private theorem fold_has_active (layers : List IdealLayer) (s : ℝ) (nodes : List IdealNode)
    (h : ∃ node ∈ nodes, node.active = true) :
    ∃ node ∈ layers.foldl (fun ns layer => ns.flatMap (fun n => n.split layer s)) nodes,
      node.active = true := by
  induction layers generalizing nodes with
  | nil => exact h
  | cons layer layers ih =>
    obtain ⟨node, hn, ha⟩ := h
    obtain ⟨child, hc, hca⟩ := node.split_has_active layer s ha
    exact ih _ ⟨child, List.mem_flatMap.mpr ⟨node, hn, hc⟩, hca⟩

public theorem run_has_active (layers : List IdealLayer) (s : ℝ) :
    ∃ node ∈ run layers s, node.active = true :=
  fold_has_active layers s [root] ⟨root, by simp, rfl⟩

end IdealNode
end C2Riemannian
