module

public import C2Riemannian.IdealFourthBounds
import C2Riemannian.CycleGainArithmetic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace C2Riemannian.IdealNode

open SplitStep

private noncomputable def advance (nodes : List IdealNode) (step : SplitStep)
    (prior : ℕ) (s : ℝ) : List IdealNode :=
  nodes.flatMap fun node => node.split ⟨step, prior⟩ s

private noncomputable def runFrom (prior : ℕ) (steps : List SplitStep)
    (s : ℝ) (nodes : List IdealNode) : List IdealNode :=
  (idealLayers prior steps).foldl (fun ns layer => ns.flatMap fun node => node.split layer s) nodes

private theorem runFrom_cons (prior : ℕ) (step : SplitStep) (steps : List SplitStep)
    (s : ℝ) (nodes : List IdealNode) :
    runFrom prior (step :: steps) s nodes = runFrom (if step == vertical then prior else prior + 1)
      steps s (advance nodes step prior s) := rfl

private theorem idealLayers_append (prior : ℕ) (xs ys : List SplitStep) :
    idealLayers prior (xs ++ ys) =
      idealLayers prior xs ++ idealLayers (prior + tableCount xs) ys := by
  induction xs generalizing prior with
  | nil => simp [idealLayers, tableCount]
  | cons x xs ih =>
    cases x <;>
      simp [idealLayers, tableCount, ih, Nat.add_comm, Nat.add_left_comm]

private theorem runFrom_append (prior : ℕ) (xs ys : List SplitStep) (s : ℝ)
    (nodes : List IdealNode) :
    runFrom prior (xs ++ ys) s nodes =
      runFrom (prior + tableCount xs) ys s (runFrom prior xs s nodes) := by
  simp only [runFrom, idealLayers_append, List.foldl_append]

private def bounded (nodes : List IdealNode) : Prop :=
  ∀ node ∈ nodes, node.scalar.frobeniusSq ≤ 11 / 2

private def phase (A : ℝ → ScalarHess) (nodes : List IdealNode) : Prop :=
  bounded nodes ∧ ∀ node ∈ nodes, node.active = true → node.sigma ^ 2 = 1 ∧ node.scalar = A node.sigma

private def prefixesBounded (prior : ℕ) (steps : List SplitStep) (s : ℝ)
    (nodes : List IdealNode) : Prop :=
  ∀ d : ℕ, bounded (runFrom prior (steps.take d) s nodes)

private theorem prefixes_append {prior : ℕ} {xs ys : List SplitStep} {s : ℝ} {nodes : List IdealNode}
    (hx : prefixesBounded prior xs s nodes)
    (hy : prefixesBounded (prior + tableCount xs) ys s (runFrom prior xs s nodes)) :
    prefixesBounded prior (xs ++ ys) s nodes := by
  intro d
  by_cases hd : d ≤ xs.length
  · rw [List.take_append_of_le_length hd]
    exact hx d
  · have hd' : xs.length ≤ d := Nat.le_of_lt (Nat.lt_of_not_ge hd)
    rw [List.take_append, List.take_of_length_le hd', runFrom_append]
    exact hy (d - xs.length)

private theorem advance_table {A B : ℝ → ScalarHess} {nodes : List IdealNode}
    (h : phase A nodes) {step : SplitStep} (hnv : step ≠ vertical)
    (prior : ℕ) (s : ℝ)
    (hpos : ∀ σ, step.scalarChild (A σ) s σ true = B σ)
    (hb : ∀ σ, σ ^ 2 = 1 → ∀ e : Bool, (step.scalarChild (A σ) s σ e).frobeniusSq ≤ 11 / 2) :
    phase B (advance nodes step prior s) := by
  have hchildren {node : IdealNode} (hn : node ∈ advance nodes step prior s) :
      (∃ parent ∈ nodes, parent.active = true ∧ ∃ e : Bool, node = parent.child ⟨step, prior⟩ s e) ∨
        (node ∈ nodes ∧ node.active = false) := by
    obtain ⟨parent, hp, hc⟩ := List.mem_flatMap.mp hn
    cases ha : parent.active
    · rw [parent.split_stopped _ _ ha, List.mem_singleton] at hc
      subst node
      exact Or.inr ⟨hp, ha⟩
    · simp [split, ha] at hc
      rcases hc with htrue | hfalse
      · exact Or.inl ⟨parent, hp, ha, true, htrue⟩
      · exact Or.inl ⟨parent, hp, ha, false, hfalse⟩
  have hstep : (step == vertical) = false := by
    cases step <;> simp_all
  constructor
  · intro node hn
    rcases hchildren hn with ⟨parent, hp, ha, e, rfl⟩ | ⟨hn', _⟩
    · obtain ⟨hσ, hA⟩ := h.2 parent hp ha
      change (step.scalarChild parent.scalar s parent.sigma e).frobeniusSq ≤ 11 / 2
      rw [hA]
      exact hb _ hσ e
    · exact h.1 node hn'
  · intro node hn hact
    rcases hchildren hn with ⟨parent, hp, ha, e, rfl⟩ | ⟨_, hstop⟩
    · obtain ⟨hσ, hA⟩ := h.2 parent hp ha
      cases e with
      | false =>
        have he : step.continues false = true := hact
        exact (hnv ((negative_continues_iff _).mp he)).elim
      | true =>
        simpa only [child, hstep, Bool.false_eq_true, ite_false, hA, hpos] using
          (show parent.sigma ^ 2 = 1 ∧ B parent.sigma = B parent.sigma from ⟨hσ, rfl⟩)
    · rw [hstop] at hact
      contradiction

private noncomputable def zeroState : ScalarHess := ⟨0, 0, 0⟩

private noncomputable def baseState (c σ : ℝ) : ScalarHess := ⟨0, 0, σ * c⟩

private theorem advance_vertical {nodes : List IdealNode}
    (h : phase (fun _ => zeroState) nodes) (prior : ℕ) (s : ℝ) :
    phase (baseState 1) (advance nodes vertical prior s) := by
  have hnode {node : IdealNode} (hn : node ∈ advance nodes vertical prior s) :
      node.scalar.frobeniusSq ≤ 11 / 2 ∧
        (node.active = true → node.sigma ^ 2 = 1 ∧ node.scalar = baseState 1 node.sigma) := by
    obtain ⟨parent, hp, hc⟩ := List.mem_flatMap.mp hn
    cases ha : parent.active
    · rw [parent.split_stopped _ _ ha, List.mem_singleton] at hc
      subst node
      exact ⟨h.1 parent hp, fun hactive => (Bool.false_ne_true (ha.symm.trans hactive)).elim⟩
    · have hA := (h.2 parent hp ha).2
      simp [split, ha] at hc
      rcases hc with rfl | rfl <;>
        norm_num [child, scalarChild, ScalarHess.rankOneUpdate, ScalarHess.frobeniusSq,
          hA, zeroState, baseState]
  exact ⟨fun node hn => (hnode hn).1, fun node hn => (hnode hn).2⟩

private def rows : List SplitStep := [first, second, third, SplitStep.fourth]

private noncomputable def A₁ (s c σ : ℝ) : ScalarHess :=
  (⟨-1, -s, c - s ^ 2⟩ : ScalarHess).scale σ

private noncomputable def A₂ (s c σ : ℝ) : ScalarHess :=
  (⟨0, -s, c - s ^ 2⟩ : ScalarHess).scale σ

private noncomputable def A₃ (s c σ : ℝ) : ScalarHess :=
  (⟨-1, 0, c - 2 * s ^ 2⟩ : ScalarHess).scale σ

private theorem one_table_with_middle {nodes : List IdealNode} (prior : ℕ) (s c : ℝ)
    (hs : s ^ 2 ≤ 1 / 4) (hc : 2 * s ^ 2 ≤ c) (hc' : c ≤ 1)
    (h₀ : phase (baseState c) nodes) :
    prefixesBounded prior rows s nodes ∧
      phase (baseState (c - 2 * s ^ 2)) (runFrom prior rows s nodes) ∧
      phase (A₂ s c) (runFrom prior [first, second] s nodes) := by
  obtain ⟨hp₁, hp₂, hp₃, hp₄⟩ := continuing_row_bounds s c hs hc hc'
  obtain ⟨hn₁, hn₂, hn₃, hn₄⟩ := stopped_row_bounds s c hs hc hc'
  let n₁ := advance nodes first prior s
  let n₂ := advance n₁ second (prior + 1) s
  let n₃ := advance n₂ third (prior + 1 + 1) s
  let n₄ := advance n₃ SplitStep.fourth (prior + 1 + 1 + 1) s
  have h₁ : phase (A₁ s c) n₁ := by
    apply advance_table h₀ (by decide)
    · exact fun σ => first_positive s σ c
    · intro σ hσ e
      cases e
      · rw [baseState, first_negative, ScalarHess.frobeniusSq_scale, hσ, one_mul]
        simp only [ScalarHess.frobeniusSq, one_pow]
        exact hn₁.trans (by norm_num)
      · rw [baseState, first_positive, ScalarHess.frobeniusSq_scale, hσ, one_mul]
        simp only [ScalarHess.frobeniusSq, neg_sq, one_pow]
        exact (by simpa only [neg_sq] using hp₁.trans (by norm_num : (5 / 2 : ℝ) ≤ 11 / 2))
  have h₂ : phase (A₂ s c) n₂ := by
    apply advance_table h₁ (by decide)
    · exact fun σ => second_positive s σ c
    · intro σ hσ e
      cases e
      · rw [A₁, second_negative, ScalarHess.frobeniusSq_scale, hσ, one_mul]
        simp only [ScalarHess.frobeniusSq, neg_sq]
        nlinarith only [hn₂]
      · rw [A₁, second_positive, ScalarHess.frobeniusSq_scale, hσ, one_mul]
        simp only [ScalarHess.frobeniusSq, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add]
        exact hp₂.trans (by norm_num)
  have h₃ : phase (A₃ s c) n₃ := by
    apply advance_table h₂ (by decide)
    · exact fun σ => third_positive s σ c
    · intro σ hσ e
      cases e
      · rw [A₂, third_negative, ScalarHess.frobeniusSq_scale, hσ, one_mul]
        simp only [ScalarHess.frobeniusSq, one_pow]
        exact hn₃.trans (by norm_num)
      · rw [A₂, third_positive, ScalarHess.frobeniusSq_scale, hσ, one_mul]
        simp only [ScalarHess.frobeniusSq, neg_sq, one_pow,
          zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, add_zero]
        exact hp₃.trans (by norm_num)
  have h₄ : phase (baseState (c - 2 * s ^ 2)) n₄ := by
    apply advance_table h₃ (by decide)
    · intro σ
      rw [A₃, fourth_positive]
      simp [baseState, ScalarHess.scale]
    · intro σ hσ e
      cases e
      · rw [A₃, fourth_negative, ScalarHess.frobeniusSq_scale, hσ, one_mul]
        simp only [ScalarHess.frobeniusSq, neg_sq, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, add_zero]
        nlinarith only [hn₄]
      · rw [A₃, fourth_positive, ScalarHess.frobeniusSq_scale, hσ, one_mul]
        simp only [ScalarHess.frobeniusSq, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, zero_add]
        exact hp₄.trans (by norm_num)
  refine ⟨?_, h₄, h₂⟩
  intro d
  rcases d with _ | ⟨_ | ⟨_ | ⟨_ | d⟩⟩⟩
  · exact h₀.1
  · exact h₁.1
  · exact h₂.1
  · exact h₃.1
  · have ht : rows.take (d + 1 + 1 + 1 + 1) = rows :=
      List.take_of_length_le (by change 4 ≤ d + 1 + 1 + 1 + 1; omega)
    rw [ht]
    exact h₄.1

private theorem one_table {nodes : List IdealNode} (prior : ℕ) (s c : ℝ)
    (hs : s ^ 2 ≤ 1 / 4) (hc : 2 * s ^ 2 ≤ c) (hc' : c ≤ 1)
    (h₀ : phase (baseState c) nodes) :
    prefixesBounded prior rows s nodes ∧
      phase (baseState (c - 2 * s ^ 2)) (runFrom prior rows s nodes) :=
  let h := one_table_with_middle prior s c hs hc hc' h₀
  ⟨h.1, h.2.1⟩

private def table (N : ℕ) : List SplitStep := (List.replicate N rows).flatten

private theorem tables {nodes : List IdealNode} (N prior : ℕ) (s c : ℝ)
    (hs : s ^ 2 ≤ 1 / 4) (hc : 2 * (N : ℝ) * s ^ 2 ≤ c) (hc' : c ≤ 1)
    (h : phase (baseState c) nodes) :
    prefixesBounded prior (table N) s nodes ∧
      phase (baseState (c - 2 * (N : ℝ) * s ^ 2)) (runFrom prior (table N) s nodes) := by
  induction N generalizing prior c nodes with
  | zero =>
    refine ⟨fun d => ?_, ?_⟩
    · simpa [table, runFrom, idealLayers] using h.1
    · simpa [table, runFrom, idealLayers] using h
  | succ N ih =>
    have hn : 0 ≤ (N : ℝ) * s ^ 2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg s)
    have hcs : 2 * s ^ 2 ≤ c := by
      push_cast at hc
      nlinarith only [hc, hn]
    have hct : 2 * (N : ℝ) * s ^ 2 ≤ c - 2 * s ^ 2 := by
      push_cast at hc
      nlinarith only [hc]
    obtain ⟨hrows, ha⟩ := one_table prior s c hs hcs hc' h
    obtain ⟨hrest, hdone⟩ := ih (prior + tableCount rows) (c - 2 * s ^ 2) hct
      (by linarith only [hc', sq_nonneg s]) ha
    change prefixesBounded prior (rows ++ table N) s nodes ∧
      phase (baseState (c - 2 * (N.succ : ℝ) * s ^ 2)) (runFrom prior (rows ++ table N) s nodes)
    refine ⟨prefixes_append hrows hrest, ?_⟩
    rw [runFrom_append, Nat.cast_succ]
    have heq : c - 2 * (↑N + 1) * s ^ 2 = c - 2 * s ^ 2 - 2 * (N : ℝ) * s ^ 2 := by ring
    rw [heq]
    exact hdone

private theorem cycle_from {nodes : List IdealNode} (N prior : ℕ) (s : ℝ)
    (hs : s ^ 2 ≤ 1 / 4) (hN : 2 * (N : ℝ) * s ^ 2 = 1)
    (h : phase (fun _ => zeroState) nodes) :
    prefixesBounded prior (cycle N) s nodes ∧
      phase (fun _ => zeroState) (runFrom prior (cycle N) s nodes) := by
  obtain ⟨ht, hz⟩ := tables N prior s 1 hs hN.le le_rfl (advance_vertical h prior s)
  constructor
  · intro d
    cases d with
    | zero => exact h.1
    | succ d =>
      change bounded (runFrom prior ((vertical :: table N).take (d + 1)) s nodes)
      rw [List.take_succ_cons, runFrom_cons]
      exact ht d
  · rw [hN, sub_self] at hz
    change phase (fun _ => zeroState) (runFrom prior (vertical :: table N) s nodes)
    rw [runFrom_cons]
    have hzero : baseState 0 = fun _ => zeroState := by
      funext σ
      simp [baseState, zeroState]
    rw [hzero] at hz
    exact hz

private theorem full_schedule_from {nodes : List IdealNode} (N J prior : ℕ) (s : ℝ)
    (hs : s ^ 2 ≤ 1 / 4) (hN : 2 * (N : ℝ) * s ^ 2 = 1)
    (h : phase (fun _ => zeroState) nodes) :
    prefixesBounded prior (schedule N J) s nodes ∧
      phase (fun _ => zeroState) (runFrom prior (schedule N J) s nodes) := by
  induction J generalizing prior nodes with
  | zero =>
    refine ⟨fun d => ?_, h⟩
    simpa [schedule, runFrom, idealLayers] using h.1
  | succ J ih =>
    obtain ⟨hc, ha⟩ := cycle_from N prior s hs hN h
    obtain ⟨hr, he⟩ := ih (prior + tableCount (cycle N)) ha
    change prefixesBounded prior (cycle N ++ schedule N J) s nodes ∧
      phase (fun _ => zeroState) (runFrom prior (cycle N ++ schedule N J) s nodes)
    refine ⟨prefixes_append hc hr, ?_⟩
    rw [runFrom_append]
    exact he

private theorem root_phase : phase (fun _ => zeroState) [root] := by
  constructor
  · intro n hn
    rw [List.mem_singleton] at hn
    subst n
    norm_num [root, ScalarHess.frobeniusSq]
  · intro n hn _
    rw [List.mem_singleton] at hn
    subst n
    norm_num [root, zeroState]

private theorem slope_sq_bound {N : ℕ} {s : ℝ} (hN : 2 ≤ N)
    (hs : 2 * (N : ℝ) * s ^ 2 = 1) : s ^ 2 ≤ 1 / 4 := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hmul := mul_le_mul_of_nonneg_right hN' (sq_nonneg s)
  nlinarith only [hmul, hs]

/-- Every ideal state at every schedule prefix, including stopped states, has squared
Frobenius norm at most (11/2). -/
public theorem all_node_A_bound (N J d : ℕ) (s : ℝ) (hN : 2 ≤ N)
    (hs : 2 * (N : ℝ) * s ^ 2 = 1)
    (node : IdealNode) (hn : node ∈ run (idealLayers 0 ((schedule N J).take d)) s) :
    node.scalar.frobeniusSq ≤ 11 / 2 :=
  (full_schedule_from N J 0 s (slope_sq_bound hN hs) hs root_phase).1 d node hn

private theorem idealLayers_take (prior d : ℕ) (steps : List SplitStep) :
    (idealLayers prior steps).take d = idealLayers prior (steps.take d) := by
  induction d generalizing prior steps with
  | zero => rfl
  | succ d ih =>
    cases steps with
    | nil => rfl
    | cons step steps => simp [idealLayers, ih]

/-- The same Frobenius bound stated for a prefix of the labelled layers themselves. -/
public theorem all_layer_node_A_bound (N J d : ℕ) (s : ℝ) (hN : 2 ≤ N)
    (hs : 2 * (N : ℝ) * s ^ 2 = 1)
    (node : IdealNode) (hn : node ∈ run ((idealLayers 0 (schedule N J)).take d) s) :
    node.scalar.frobeniusSq ≤ 11 / 2 := by
  rw [idealLayers_take] at hn
  exact all_node_A_bound N J d s hN hs node hn

/-- At the end of each number of complete cycles every continuing second-order state is zero. -/
public theorem cycle_reset (N J : ℕ) (s : ℝ) (hN : 2 ≤ N)
    (hs : 2 * (N : ℝ) * s ^ 2 = 1)
    (node : IdealNode) (hn : node ∈ run (idealLayers 0 (schedule N J)) s)
    (ha : node.active = true) :
    node.scalar = ⟨0, 0, 0⟩ :=
  ((full_schedule_from N J 0 s (slope_sq_bound hN hs) hs root_phase).2.2 node hn ha).2

/-- Attach the block number within a cycle to each of its four table rows. -/
@[expose] public def indexedTableRows (j N : ℕ) : List (SplitStep × ℕ) :=
  match N with
  | 0 => []
  | n + 1 => [(first, j), (second, j), (third, j), (SplitStep.fourth, j)] ++
      indexedTableRows (j + 1) n

/-- In each cycle the vertical step precedes the table rows and block numbering restarts. -/
@[expose] public def indexedSchedule (N J : ℕ) : List (SplitStep × ℕ) :=
  match J with
  | 0 => []
  | n + 1 => ((vertical, 0) :: indexedTableRows 0 N) ++ indexedSchedule N n

private theorem indexedTableRows_steps (N j : ℕ) :
    (indexedTableRows j N).map Prod.fst = table N := by
  induction N generalizing j with
  | zero => rfl
  | succ N ih =>
    change rows ++ (indexedTableRows (j + 1) N).map Prod.fst = rows ++ table N
    rw [ih]

public theorem indexedSchedule_steps (N J : ℕ) :
    (indexedSchedule N J).map Prod.fst = schedule N J := by
  induction J with
  | zero => rfl
  | succ J ih =>
    rw [show indexedSchedule N (J + 1) =
      ((vertical, 0) :: indexedTableRows 0 N) ++ indexedSchedule N J from rfl,
      List.map_append, List.map_cons, indexedTableRows_steps, ih]
    rfl
/-- The signed curvature contribution for the continuing oblique phase.
Horizontal and vertical steps have zero contribution in the reverse budget. -/
@[expose] public noncomputable def reverseContribution (step : SplitStep)
    (node : IdealNode) (s : ℝ) : ℝ :=
  match step with
  | first => s ^ 2 * ((step.scalarChild node.scalar s node.sigma true).reverseSource -
      node.scalar.reverseSource)
  | third => (-s) ^ 2 * ((step.scalarChild node.scalar s node.sigma true).reverseSource -
      node.scalar.reverseSource)
  | _ => 0

/-- Signed contribution at the given table block and row. -/
@[expose] public noncomputable def scheduledReverseContribution (s : ℝ) (row : SplitStep × ℕ) : ℝ :=
  let c := 1 - 2 * (row.2 : ℝ) * s ^ 2
  match row.1 with
  | first => s ^ 2 * c / 25
  | third => s ^ 2 * (c - 3 * s ^ 2) / 25
  | _ => 0

private def ReverseCertified (s : ℝ) (prior : ℕ) (nodes : List IdealNode) :
    List (SplitStep × ℕ) → Prop
  | [] => True
  | row :: rest =>
      (∀ node ∈ nodes, node.active = true →
        reverseContribution row.1 node s = scheduledReverseContribution s row) ∧
      ReverseCertified s (if row.1 == vertical then prior else prior + 1)
        (advance nodes row.1 prior s) rest

private theorem reverseCertified_append (s : ℝ) (prior : ℕ) (nodes : List IdealNode)
    (xs ys : List (SplitStep × ℕ))
    (hx : ReverseCertified s prior nodes xs)
    (hy : ReverseCertified s (prior + tableCount (xs.map Prod.fst))
      (runFrom prior (xs.map Prod.fst) s nodes) ys) :
    ReverseCertified s prior nodes (xs ++ ys) := by
  induction xs generalizing prior nodes with
  | nil => simpa [tableCount, runFrom, idealLayers] using hy
  | cons row xs ih =>
    refine ⟨hx.1, ih _ _ hx.2 ?_⟩
    have hcount : prior + tableCount ((row :: xs).map Prod.fst) =
        (if row.1 == vertical then prior else prior + 1) + tableCount (xs.map Prod.fst) := by
      rcases row with ⟨step, j⟩
      cases step <;> simp [tableCount] <;> omega
    rw [hcount] at hy
    simpa only [List.map_cons, runFrom_cons] using hy

private theorem indexed_rows_certified (s : ℝ) (j prior : ℕ) (nodes : List IdealNode)
    (h₀ : phase (baseState (1 - 2 * (j : ℝ) * s ^ 2)) nodes)
    (h₂ : phase (A₂ s (1 - 2 * (j : ℝ) * s ^ 2)) (runFrom prior [first, second] s nodes)) :
    ReverseCertified s prior nodes [(first, j), (second, j), (third, j), (SplitStep.fourth, j)] := by
  let c := 1 - 2 * (j : ℝ) * s ^ 2
  refine ⟨?_, fun _ _ _ => rfl, ?_, fun _ _ _ => rfl, trivial⟩
  · intro node hnode ha
    obtain ⟨hsigma, hscalar⟩ := h₀.2 node hnode ha
    simpa only [reverseContribution, scheduledReverseContribution, hscalar, baseState] using
      (CycleGainArithmetic.reverse_row_signed_gain s node.sigma c hsigma).1
  · intro node hnode ha
    obtain ⟨hsigma, hscalar⟩ := h₂.2 node hnode ha
    have hA : A₂ s c node.sigma = ⟨0, -node.sigma * s, node.sigma * (c - s ^ 2)⟩ := by
      simp [A₂, ScalarHess.scale, mul_neg, neg_mul]
    simpa only [reverseContribution, scheduledReverseContribution, hscalar, ← show
      c = 1 - 2 * (j : ℝ) * s ^ 2 from rfl, hA] using
      (CycleGainArithmetic.reverse_row_signed_gain s node.sigma c hsigma).2

private theorem indexed_table_certified (s : ℝ) (N j prior : ℕ) (nodes : List IdealNode)
    (hs : s ^ 2 ≤ 1 / 4) (hc : 2 * (N : ℝ) * s ^ 2 ≤ 1 - 2 * (j : ℝ) * s ^ 2)
    (h₀ : phase (baseState (1 - 2 * (j : ℝ) * s ^ 2)) nodes) :
    ReverseCertified s prior nodes (indexedTableRows j N) := by
  induction N generalizing j prior nodes with
  | zero => trivial
  | succ N ih =>
    let c := 1 - 2 * (j : ℝ) * s ^ 2
    have hcs : 2 * s ^ 2 ≤ c := by
      push_cast at hc
      nlinarith only [hc, mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (sq_nonneg s)]
    have hc' : c ≤ 1 := by
      dsimp [c]
      nlinarith only [mul_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j) (sq_nonneg s)]
    have hcnext : c - 2 * s ^ 2 = 1 - 2 * (↑(j + 1) : ℝ) * s ^ 2 := by
      push_cast
      dsimp [c]
      ring
    have hN : 2 * (N : ℝ) * s ^ 2 ≤ 1 - 2 * (↑(j + 1) : ℝ) * s ^ 2 := by
      rw [← hcnext]
      push_cast at hc
      dsimp [c]
      linarith only [hc]
    obtain ⟨_, hEnd, hMiddle⟩ := one_table_with_middle prior s c hs hcs hc' h₀
    have hrow := indexed_rows_certified s j prior nodes h₀ hMiddle
    rw [hcnext] at hEnd
    exact reverseCertified_append s prior nodes _ _ hrow (ih _ _ _ hN hEnd)

private theorem indexed_schedule_certified_from (s : ℝ) (N J prior : ℕ) (nodes : List IdealNode)
    (hs : s ^ 2 ≤ 1 / 4) (hN : 2 * (N : ℝ) * s ^ 2 = 1)
    (h₀ : phase (fun _ => zeroState) nodes) :
    ReverseCertified s prior nodes (indexedSchedule N J) := by
  induction J generalizing prior nodes with
  | zero => trivial
  | succ J ih =>
    have hv := advance_vertical h₀ prior s
    have htab : ReverseCertified s prior (advance nodes vertical prior s) (indexedTableRows 0 N) := by
      apply indexed_table_certified s N 0 prior _ hs
      · simpa using hN.le
      · simpa using hv
    have hcycle : ReverseCertified s prior nodes ((vertical, 0) :: indexedTableRows 0 N) :=
      ⟨fun _ _ _ => rfl, htab⟩
    have hEnd := (cycle_from N prior s hs hN h₀).2
    change phase (fun _ => zeroState) (runFrom prior (vertical :: table N) s nodes) at hEnd
    apply reverseCertified_append s prior nodes _ _ hcycle
    simpa only [List.map_cons, indexedTableRows_steps] using ih _ _ hEnd

private theorem reverseCertified_at (s : ℝ) (prior : ℕ) (nodes : List IdealNode)
    (xs : List (SplitStep × ℕ)) (h : ReverseCertified s prior nodes xs)
    (d : ℕ) (row : SplitStep × ℕ) (hd : xs[d]? = some row)
    (node : IdealNode) (hn : node ∈ runFrom prior ((xs.map Prod.fst).take d) s nodes)
    (ha : node.active = true) :
    reverseContribution row.1 node s = scheduledReverseContribution s row := by
  induction xs generalizing prior nodes d with
  | nil => simp at hd
  | cons head xs ih =>
    cases d with
    | zero =>
      have he : head = row := by simpa using hd
      subst row
      exact h.1 node hn ha
    | succ d =>
      apply ih _ _ h.2 d (by simpa using hd) ?_
      simpa only [List.map_cons, List.take_succ_cons, runFrom_cons] using hn

/-- Every active ideal parent at a scheduled layer has the same signed reverse
contribution, determined by the row and the block within that cycle. -/
public theorem reverse_contribution_at (N J d : ℕ) (s : ℝ) (hN : 2 ≤ N)
    (hs : 2 * (N : ℝ) * s ^ 2 = 1)
    (row : SplitStep × ℕ) (hd : (indexedSchedule N J)[d]? = some row)
    (node : IdealNode) (hn : node ∈ run ((idealLayers 0 (schedule N J)).take d) s)
    (ha : node.active = true) :
    reverseContribution row.1 node s = scheduledReverseContribution s row := by
  refine reverseCertified_at s 0 [root] (indexedSchedule N J)
    (indexed_schedule_certified_from s N J 0 [root] (slope_sq_bound hN hs) hs root_phase)
    d row hd node ?_ ha
  rw [indexedSchedule_steps]
  rw [idealLayers_take] at hn
  exact hn

private theorem idealLayers_steps (prior : ℕ) (steps : List SplitStep) :
    (idealLayers prior steps).map IdealLayer.step = steps := by
  induction steps generalizing prior with
  | nil => rfl
  | cons step steps ih => simp [idealLayers, ih]

/-- The table annotation at a layer has the same step as its physical layer label. -/
public theorem indexedSchedule_step_at (N J d : ℕ) (row : SplitStep × ℕ) (layer : IdealLayer)
    (hrow : (indexedSchedule N J)[d]? = some row)
    (hlayer : (idealLayers 0 (schedule N J))[d]? = some layer) : row.1 = layer.step := by
  have h₁ : (schedule N J)[d]? = some row.1 := by
    rw [← indexedSchedule_steps, List.getElem?_map, hrow, Option.map_some]
  have h₂ : (schedule N J)[d]? = some layer.step := by
    rw [← idealLayers_steps 0 (schedule N J), List.getElem?_map, hlayer, Option.map_some]
  exact Option.some.inj (h₁.symm.trans h₂)

/-- The exact signed contribution for the labelled ideal layer, at any of its
active parent nodes. -/
public theorem reverse_contribution_for_layer_at (N J d : ℕ) (s : ℝ) (hN : 2 ≤ N)
    (hs : 2 * (N : ℝ) * s ^ 2 = 1)
    (row : SplitStep × ℕ) (layer : IdealLayer)
    (hrow : (indexedSchedule N J)[d]? = some row)
    (hlayer : (idealLayers 0 (schedule N J))[d]? = some layer)
    (node : IdealNode) (hn : node ∈ run ((idealLayers 0 (schedule N J)).take d) s)
    (ha : node.active = true) :
    reverseContribution layer.step node s = scheduledReverseContribution s row := by
  rw [← indexedSchedule_step_at N J d row layer hrow hlayer]
  exact reverse_contribution_at N J d s hN hs row hrow node hn ha

end C2Riemannian.IdealNode
