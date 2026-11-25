module

public import C2Riemannian.BoundedPhysicalTree
public import C2Riemannian.CycleGainArithmetic
public import C2Riemannian.LayerEnergyBudget
import Mathlib.Tactic.Abel

set_option autoImplicit false

open scoped BigOperators

namespace C2Riemannian

/-- Both source gains on the indexed schedule, in their physical layer order. -/
@[expose] public noncomputable def scheduledLayerGains (N J : ℕ) (s K θ : ℝ) :
    List (ℝ × ℝ) :=
  (IdealNode.indexedSchedule N J).map fun row =>
    CycleGainArithmetic.layer_gain_schedule s K θ row.2 row.1

/-- The gain at a given depth is prescribed by its indexed row. -/
public theorem scheduledLayerGains_at (N J d : ℕ) (s K θ : ℝ) (row : SplitStep × ℕ)
    (h : (IdealNode.indexedSchedule N J)[d]? = some row) :
    (scheduledLayerGains N J s K θ)[d]? =
      some (CycleGainArithmetic.layer_gain_schedule s K θ row.2 row.1) := by
  rw [scheduledLayerGains, List.getElem?_map, h, Option.map_some]

/-- The finite budget list has exactly one entry per physical layer. -/
public theorem scheduledLayerGains_length (N J : ℕ) (s K θ : ℝ) :
    (scheduledLayerGains N J s K θ).length =
      (idealLayers 0 (SplitStep.schedule N J)).length := by
  rw [scheduledLayerGains, List.length_map]
  calc
    (IdealNode.indexedSchedule N J).length =
        ((IdealNode.indexedSchedule N J).map Prod.fst).length := (List.length_map Prod.fst).symm
    _ = (SplitStep.schedule N J).length :=
      congrArg List.length (IdealNode.indexedSchedule_steps N J)
    _ = ((idealLayers 0 (SplitStep.schedule N J)).map IdealLayer.step).length :=
      congrArg List.length (idealLayers_steps 0 (SplitStep.schedule N J)).symm
    _ = _ := List.length_map IdealLayer.step

private theorem indexedTableRows_gain_sum (s K θ : ℝ) (N j : ℕ) :
    let g := CycleGainArithmetic.layer_gain_schedule s K θ
    ((IdealNode.indexedTableRows j N).map fun row => g row.2 row.1).sum =
      ∑ b ∈ Finset.range N, (g (j + b) .first + g (j + b) .second +
        g (j + b) .third + g (j + b) .fourth) := by
  let g := CycleGainArithmetic.layer_gain_schedule s K θ
  let block (b : ℕ) := g b .first + g b .second + g b .third + g b .fourth
  change ((IdealNode.indexedTableRows j N).map fun row => g row.2 row.1).sum =
    ∑ b ∈ Finset.range N, block (j + b)
  induction N generalizing j with
  | zero => simp [IdealNode.indexedTableRows]
  | succ N ih =>
    rw [show IdealNode.indexedTableRows j (N + 1) =
      [(.first, j), (.second, j), (.third, j), (.fourth, j)] ++
      IdealNode.indexedTableRows (j + 1) N from rfl,
      List.map_append, List.sum_append, ih, Finset.sum_range_succ']
    have h : (∑ b ∈ Finset.range N, block (j + 1 + b)) =
        ∑ b ∈ Finset.range N, block (j + (b + 1)) := by
      apply Finset.sum_congr rfl
      intro b _
      congr 1
      omega
    rw [h]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, block]
    abel

/-- The gain list adds one complete cycle at each outer schedule iteration. -/
public theorem scheduledLayerGains_sum_cycles (N J : ℕ) (s K θ : ℝ) :
    (scheduledLayerGains N J s K θ).sum =
      ∑ _ ∈ Finset.range J, CycleGainArithmetic.cycleGains N s K θ := by
  induction J with
  | zero => simp [scheduledLayerGains, IdealNode.indexedSchedule]
  | succ J ih =>
    unfold scheduledLayerGains
    rw [show IdealNode.indexedSchedule N (J + 1) =
      ((.vertical, 0) :: IdealNode.indexedTableRows 0 N) ++ IdealNode.indexedSchedule N J from rfl,
      List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      indexedTableRows_gain_sum, Finset.sum_range_succ]
    simp only [Nat.zero_add]
    change CycleGainArithmetic.cycleGains N s K θ + (scheduledLayerGains N J s K θ).sum = _
    rw [ih, add_comm]

/-- The exact sum of the gains along the physical layer order. -/
public theorem scheduledLayerGains_sum (N J : ℕ) (s K θ : ℝ)
    (h : 2 * (N : ℝ) * s ^ 2 = 1) :
    (scheduledLayerGains N J s K θ).sum =
      ((J : ℝ) * (θ ^ 2 / (400 * K ^ 2) - 7 * K ^ 2 * s),
        (J : ℝ) * ((1 / 2 - 1 / (4 * (N : ℝ))) / 25 - 7 * K ^ 2 * s)) := by
  rw [scheduledLayerGains_sum_cycles, CycleGainArithmetic.cycle_total_gains N J s K θ h]

/-- The gains belonging to the suffix of physical layers still to be processed. -/
@[expose] public noncomputable def suffixGains (N J : ℕ) (s K θ : ℝ)
    (tail : List IdealLayer) : List (ℝ × ℝ) :=
  (scheduledLayerGains N J s K θ).drop
    ((idealLayers 0 (SplitStep.schedule N J)).length - tail.length)

/-- Select the linear source gain on false and the reverse source gain on true. -/
@[expose] public def sourceGain (reverse : Bool) (gain : ℝ × ℝ) : ℝ :=
  if reverse then gain.2 else gain.1

/-- The remaining energy budget for the indicated source mode. -/
@[expose] public noncomputable def scheduledEnergyBudget (N J : ℕ) (s K θ : ℝ)
    (reverse : Bool) (tail : List IdealLayer) : ℝ :=
  PhysicalPrefix.energyBudget K ((suffixGains N J s K θ tail).map (sourceGain reverse))

@[simp] public theorem scheduledEnergyBudget_nil (N J : ℕ) (s K θ : ℝ) (reverse : Bool) :
    scheduledEnergyBudget N J s K θ reverse [] = K ^ 2 / 2 := by
  unfold scheduledEnergyBudget suffixGains
  rw [List.length_nil, Nat.sub_zero,
    ← scheduledLayerGains_length N J s K θ, List.drop_length, List.map_nil,
    PhysicalPrefix.energyBudget_nil]

private theorem sourceGain_sum (reverse : Bool) (xs : List (ℝ × ℝ)) :
    (xs.map (sourceGain reverse)).sum = sourceGain reverse xs.sum := by
  induction xs with
  | nil => cases reverse <;> rfl
  | cons x xs ih => cases reverse <;> simp [sourceGain] at ih ⊢ <;> rw [ih]

/-- At the full schedule, the remaining budget is the leaf bound minus the
closed formula for the total gain of the chosen source. -/
public theorem scheduledEnergyBudget_full (N J : ℕ) (s K θ : ℝ) (reverse : Bool)
    (hs : 2 * (N : ℝ) * s ^ 2 = 1) :
    scheduledEnergyBudget N J s K θ reverse (idealLayers 0 (SplitStep.schedule N J)) =
      K ^ 2 / 2 - sourceGain reverse
        ((J : ℝ) * (θ ^ 2 / (400 * K ^ 2) - 7 * K ^ 2 * s),
          (J : ℝ) * ((1 / 2 - 1 / (4 * (N : ℝ))) / 25 - 7 * K ^ 2 * s)) := by
  rw [scheduledEnergyBudget, suffixGains, Nat.sub_self, List.drop_zero,
    PhysicalPrefix.energyBudget_eq, sourceGain_sum, scheduledLayerGains_sum N J s K θ hs]

namespace ScheduledPhysicalInvariant

/-- A physical layer has the indexed row at its prefix depth. Every active
physical parent on that layer has the same signed reverse contribution. -/
public theorem exists_indexed_row_with_reverse_contribution {Q : Set Plane}
    (N J : ℕ) (s : ℝ) (hN : 2 ≤ N) (hs : 2 * (N : ℝ) * s ^ 2 = 1)
    (p : PhysicalPrefix Q) (layer : IdealLayer) (tail : List IdealLayer)
    (hp : ScheduledPhysicalInvariant N J s (layer :: tail) p) :
    ∃ row : SplitStep × ℕ,
      (IdealNode.indexedSchedule N J)[p.parameterIndices.length]? = some row ∧
      row.1 = layer.step ∧ ∀ i : p.Active,
        IdealNode.reverseContribution layer.step (p.ideal i.1) s =
          IdealNode.scheduledReverseContribution s row := by
  obtain ⟨_, _, _, pre, hSch, hDepth, hNodes⟩ := hp
  let layers := idealLayers 0 (SplitStep.schedule N J)
  let idx := IdealNode.indexedSchedule N J
  have hLayer : layers[pre.length]? = some layer := by
    rw [show layers = pre ++ layer :: tail from hSch.symm, List.getElem?_append_right le_rfl,
      Nat.sub_self]
    rfl
  have hLen : idx.length = layers.length := by
    calc
      idx.length = (idx.map Prod.fst).length := (List.length_map Prod.fst).symm
      _ = (SplitStep.schedule N J).length := congrArg List.length (IdealNode.indexedSchedule_steps N J)
      _ = (layers.map IdealLayer.step).length := congrArg List.length (idealLayers_steps 0 _).symm
      _ = layers.length := List.length_map IdealLayer.step
  have hlt : pre.length < idx.length := by
    rw [hLen, show layers = pre ++ layer :: tail from hSch.symm, List.length_append, List.length_cons]
    omega
  let row := idx[pre.length]'hlt
  have hRow : idx[pre.length]? = some row := List.getElem?_eq_getElem hlt
  have hTake : layers.take pre.length = pre := by
    rw [show layers = pre ++ layer :: tail from hSch.symm, List.take_left]
  refine ⟨row, (by simpa only [hDepth] using hRow), IdealNode.indexedSchedule_step_at N J pre.length row layer hRow hLayer, ?_⟩
  intro i
  apply IdealNode.reverse_contribution_for_layer_at N J pre.length s hN hs row layer hRow hLayer
  · rw [show (idealLayers 0 (SplitStep.schedule N J)).take pre.length = pre from hTake]
    exact hNodes i.1
  · exact i.2

/-- Remove the gain of the current physical layer from the next suffix budget. -/
public theorem scheduledEnergyBudget_cons {Q : Set Plane}
    (N J : ℕ) (s K θ : ℝ) (reverse : Bool)
    (p : PhysicalPrefix Q) (layer : IdealLayer) (tail : List IdealLayer)
    (hp : ScheduledPhysicalInvariant N J s (layer :: tail) p)
    (row : SplitStep × ℕ)
    (hRow : (IdealNode.indexedSchedule N J)[p.parameterIndices.length]? = some row) :
    scheduledEnergyBudget N J s K θ reverse (layer :: tail) =
      scheduledEnergyBudget N J s K θ reverse tail -
        sourceGain reverse (CycleGainArithmetic.layer_gain_schedule s K θ row.2 row.1) := by
  obtain ⟨_, _, _, pre, hSch, hDepth, _⟩ := hp
  let gains := scheduledLayerGains N J s K θ
  let d := p.parameterIndices.length
  let full := idealLayers 0 (SplitStep.schedule N J)
  have hcur : full.length - (layer :: tail).length = d := by
    rw [show full = pre ++ layer :: tail from hSch.symm, List.length_append]
    rw [show d = pre.length from hDepth]
    omega
  have hnext : full.length - tail.length = d + 1 := by
    rw [show full = pre ++ layer :: tail from hSch.symm, List.length_append,
      List.length_cons, show d = pre.length from hDepth]
    omega
  have hAt := scheduledLayerGains_at N J d s K θ row hRow
  have hlt : d < gains.length := by
    rw [show gains.length = full.length from scheduledLayerGains_length N J s K θ,
      show full = pre ++ layer :: tail from hSch.symm, List.length_append, List.length_cons,
      show d = pre.length from hDepth]
    omega
  have hg : gains[d] = CycleGainArithmetic.layer_gain_schedule s K θ row.2 row.1 :=
    Option.some.inj ((List.getElem?_eq_getElem hlt).symm.trans hAt)
  change PhysicalPrefix.energyBudget K
    ((gains.drop (full.length - (layer :: tail).length)).map (sourceGain reverse)) =
      PhysicalPrefix.energyBudget K ((gains.drop (full.length - tail.length)).map (sourceGain reverse)) - _
  rw [hcur, hnext, List.drop_eq_getElem_cons hlt, hg, List.map_cons,
    PhysicalPrefix.energyBudget_cons]

end ScheduledPhysicalInvariant
end C2Riemannian
