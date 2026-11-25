module

public import C2Riemannian.IdealSchedule
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open scoped BigOperators

namespace C2Riemannian

@[expose] public def tableCount : List SplitStep → ℕ
  | [] => 0
  | .vertical :: steps => tableCount steps
  | _ :: steps => tableCount steps + 1

public theorem tableCount_append (xs ys : List SplitStep) :
    tableCount (xs ++ ys) = tableCount xs + tableCount ys := by
  induction xs with
  | nil => simp [tableCount]
  | cons x xs ih => cases x <;> simp [tableCount, ih, Nat.add_right_comm]

private theorem tableCount_replicate (xs : List SplitStep) (n : ℕ) :
    tableCount (List.replicate n xs).flatten = n * tableCount xs := by
  induction n with
  | zero => simp [tableCount]
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, tableCount_append, ih, Nat.succ_mul,
      Nat.add_comm]

public theorem tableCount_schedule (N J : ℕ) :
    tableCount (SplitStep.schedule N J) = 4 * N * J := by
  simp only [SplitStep.schedule, tableCount_replicate, SplitStep.cycle, tableCount]
  change J * (N * 4) = 4 * N * J
  ac_rfl

namespace IdealNode

private theorem abs_add_increment (v t e : ℝ) (k i : ℕ)
    (ht : |t| ≤ 1) (he : |e| = 1) :
    |v + e * 2 ^ k * t ^ i| ≤ |v| + 2 ^ k := by
  have hb : 0 ≤ (2 : ℝ) ^ k := by positivity
  have hp : |t| ^ i ≤ 1 := pow_le_one₀ (abs_nonneg _) ht
  have hi : |e * 2 ^ k * t ^ i| ≤ 2 ^ k := by
    rw [abs_mul, abs_mul, he, abs_of_nonneg hb, one_mul, abs_pow]
    exact mul_le_of_le_one_right hb hp
  exact (abs_add_le _ _).trans (add_le_add le_rfl hi)

public theorem fourth_child_bound (node : IdealNode) (layer : IdealLayer) (s : ℝ)
    (hs : |s| ≤ 1) (positive : Bool) (i : Fin 5) :
    |(node.child layer s positive).fourth i| ≤
      |node.fourth i| + if layer.step == .vertical then 0 else 2 ^ layer.priorTableSteps := by
  rcases layer with ⟨step, prior⟩
  have he : |(if positive then 1 else -1 : ℝ)| = 1 := by cases positive <;> norm_num
  cases step with
  | vertical => simp [child]
  | first => exact abs_add_increment _ s _ prior i.val hs he
  | second => exact abs_add_increment _ 0 _ prior i.val (by norm_num) he
  | third => exact abs_add_increment _ (-s) _ prior i.val (by simpa using hs) he
  | fourth => exact abs_add_increment _ 0 _ prior i.val (by norm_num) he

private theorem split_coord_bound (node next : IdealNode) (step : SplitStep)
    (prior : ℕ) (s : ℝ) (hs : |s| ≤ 1) (i : Fin 5)
    (hnode : |node.fourth i| ≤ 2 ^ prior - 1)
    (hnext : next ∈ node.split ⟨step, prior⟩ s) :
    |next.fourth i| ≤ 2 ^ (if step == .vertical then prior else prior + 1) - 1 := by
  by_cases ha : node.active = true
  · simp [split, ha] at hnext
    have bound (positive : Bool) := node.fourth_child_bound ⟨step, prior⟩ s hs positive i
    rcases hnext with rfl | rfl
    · have hb := bound true
      cases step <;> simp [pow_succ] at hb ⊢ <;> linarith only [hb, hnode]
    · have hb := bound false
      cases step <;> simp [pow_succ] at hb ⊢ <;> linarith only [hb, hnode]
  · have hfalse : node.active = false := by
      cases h : node.active with
      | false => rfl
      | true => exact (ha h).elim
    rw [node.split_stopped ⟨step, prior⟩ s hfalse, List.mem_singleton] at hnext
    subst next
    have hp : 0 ≤ (2 : ℝ) ^ prior := by positivity
    cases step <;> simp [pow_succ] <;> linarith only [hnode, hp]

private theorem fold_coord_bound (steps : List SplitStep) (prior : ℕ)
    (s : ℝ) (hs : |s| ≤ 1) (nodes : List IdealNode) (i : Fin 5)
    (hnodes : ∀ node ∈ nodes, |node.fourth i| ≤ 2 ^ prior - 1) :
    ∀ node ∈ (idealLayers prior steps).foldl
      (fun ns layer => ns.flatMap (fun n => n.split layer s)) nodes,
      |node.fourth i| ≤ 2 ^ (prior + tableCount steps) - 1 := by
  induction steps generalizing prior nodes with
  | nil => simpa [idealLayers, tableCount] using hnodes
  | cons step steps ih =>
    let prior' := if step == .vertical then prior else prior + 1
    have hcount : prior' + tableCount steps = prior + tableCount (step :: steps) := by
      cases step <;> simp [prior', tableCount, Nat.add_comm, Nat.add_left_comm]
    have h' : ∀ node ∈ nodes.flatMap (fun n => n.split ⟨step, prior⟩ s),
        |node.fourth i| ≤ 2 ^ prior' - 1 := by
      intro node hnode
      obtain ⟨parent, hp, hsplit⟩ := List.mem_flatMap.mp hnode
      exact split_coord_bound parent node step prior s hs i (hnodes parent hp) hsplit
    rw [← hcount]
    exact ih prior' _ h'

public theorem run_fourth_coord_bound (steps : List SplitStep) (s : ℝ) (hs : |s| ≤ 1)
    (node : IdealNode) (h : node ∈ run (idealLayers 0 steps) s) (i : Fin 5) :
    |node.fourth i| ≤ 2 ^ tableCount steps - 1 := by
  have hroot : ∀ parent ∈ [root], |parent.fourth i| ≤ (2 : ℝ) ^ (0 : ℕ) - 1 := by
    intro parent hp
    rw [List.mem_singleton] at hp
    subst parent
    simp [root]
  simpa only [Nat.zero_add] using fold_coord_bound steps 0 s hs [root] i hroot node h

/-- The multiplicity of a fourth derivative with `i` vertical indices is `choose 4 i`. -/
@[expose] public noncomputable def fourthNorm (T : Fin 5 → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin 5, (Nat.choose 4 i.val : ℝ) * (T i) ^ 2)

public theorem fourthNorm_le (T : Fin 5 → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ i, |T i| ≤ B) : fourthNorm T ≤ 4 * B := by
  have hsum : (∑ i : Fin 5, (Nat.choose 4 i.val : ℝ)) = 16 := by
    norm_num [Fin.sum_univ_succ, Nat.choose]
  have hsq : (∑ i : Fin 5, (Nat.choose 4 i.val : ℝ) * (T i) ^ 2) ≤ (4 * B) ^ 2 := by
    calc
      _ ≤ ∑ i : Fin 5, (Nat.choose 4 i.val : ℝ) * B ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (T i)) (h i) 2
      _ = (4 * B) ^ 2 := by
        rw [← Finset.sum_mul, hsum]
        ring
  exact (Real.sqrt_le_sqrt hsq).trans_eq (Real.sqrt_sq (by positivity))

public theorem run_fourth_norm_bound (N J : ℕ) (s : ℝ) (hs : |s| ≤ 1)
    (node : IdealNode) (h : node ∈ run (idealLayers 0 (SplitStep.schedule N J)) s) :
    fourthNorm node.fourth ≤ 4 * (2 : ℝ) ^ (4 * N * J) := by
  have hi (i : Fin 5) := run_fourth_coord_bound _ s hs node h i
  simp only [tableCount_schedule] at hi
  have h' : ∀ i, |node.fourth i| ≤ (2 : ℝ) ^ (4 * N * J) := by
    intro i
    linarith only [hi i]
  exact fourthNorm_le _ _ (by positivity) h'

end IdealNode
end C2Riemannian
