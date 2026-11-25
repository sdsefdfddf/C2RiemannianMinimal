module

public import C2Riemannian.ActualParameterTree
public import C2Riemannian.IdealLayerTensorBounds
public import C2Riemannian.IdealSecondBounds

set_option autoImplicit false

open Set Filter
open scoped ContDiff Real Topology

namespace C2Riemannian

namespace PhysicalLayerRow

public theorem child_mem_ideal_run {Q : Set Plane} {s δ : ℝ} {layer : IdealLayer}
    {p : PhysicalPrefix Q} {next : ℕ → PhysicalPrefix Q} {directions : PhysicalDirections}
    (row : PhysicalLayerRow directions s δ layer p next) (pre : List IdealLayer)
    (hp : ∀ i, p.ideal i ∈ IdealNode.run pre s) (k : ℕ) (j : (next k).Label) :
    (next k).ideal j ∈ IdealNode.run (pre ++ [layer]) s := by
  have hj : j ∈ Set.range (row.childLabel k) ∪ Set.range (row.stoppedLabel k) := by
    rw [row.covers_labels]
    exact mem_univ _
  rw [IdealNode.run, List.foldl_append]
  change (next k).ideal j ∈ (IdealNode.run pre s).flatMap (fun n => n.split layer s)
  rcases hj with ⟨⟨i, sign⟩, rfl⟩ | ⟨i, rfl⟩
  · rw [row.child_ideal]
    refine List.mem_flatMap.mpr ⟨p.ideal i.1, hp i.1, ?_⟩
    cases sign <;> simp [IdealNode.split, i.2]
  · rw [row.stopped_ideal]
    exact List.mem_flatMap.mpr ⟨p.ideal i.1, hp i.1, by simp [IdealNode.split_stopped _ _ _ i.2]⟩

end PhysicalLayerRow

/-- The invariants propagated through the scheduled physical tree. -/
@[expose] public def ScheduledPhysicalInvariant (N J : ℕ) (s : ℝ) {Q : Set Plane}
    (tail : List IdealLayer) (p : PhysicalPrefix Q) : Prop :=
  p.ExactJets ∧
  (∀ x, tensorHS (iteratedFDeriv ℝ 2 p.secondPotential x) ≤ √(11 / 2 : ℝ) + 1) ∧
  (∀ x, tensorHS (iteratedFDeriv ℝ 4 p.fourthPotential x) ≤ 4 * (2 : ℝ) ^ (4 * N * J) + 1) ∧
  ∃ pre, pre ++ tail = idealLayers 0 (SplitStep.schedule N J) ∧
    p.parameterIndices.length = pre.length ∧ ∀ i, p.ideal i ∈ IdealNode.run pre s

/-- M25 with both global M24 bounds and explicit ideal prefix membership at every node. -/
public theorem exists_bounded_scheduled_physical_tree {Q : Set Plane} (hQ : Bornology.IsBounded Q)
    (hOpen : IsOpen Q) (hNonempty : Q.Nonempty) (N J : ℕ) (s δ : ℝ)
    (hN : 2 ≤ N) (hs : 2 * (N : ℝ) * s ^ 2 = 1)
    (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    Nonempty (PhysicalParameterTree idealPhysicalDirections s δ (ScheduledPhysicalInvariant N J s)
      (idealLayers 0 (SplitStep.schedule N J)) (PhysicalPrefix.root Q hOpen hNonempty)) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hsSq : s ^ 2 ≤ 1 / 4 := by
    have h := mul_le_mul_of_nonneg_right hN' (sq_nonneg s)
    nlinarith only [hs, h]
  have hs' : |s| ≤ 1 := abs_le_of_sq_le_sq (hsSq.trans (by norm_num)) zero_le_one
  apply PhysicalParameterTree.exists_of_layer_rows
  · intro layer tail p hp
    obtain ⟨hJets, hOld₂, hOld₄, pre, hSch, hDepth, hMem⟩ := hp
    obtain ⟨next, ⟨row⟩, hExact⟩ := exists_ideal_physical_row hQ p hJets layer s δ hδ hδ'
    refine ⟨next, ⟨row⟩, ?_⟩
    intro k
    have hSch' : (pre ++ [layer]) ++ tail = idealLayers 0 (SplitStep.schedule N J) := by
      simpa [List.append_assoc] using hSch
    have hTake : (idealLayers 0 (SplitStep.schedule N J)).take (pre ++ [layer]).length =
        pre ++ [layer] := by rw [← hSch', List.take_left]
    have hRun (i : p.Active) (positive : Bool) :
        (p.ideal i.1).child layer s positive ∈
          IdealNode.run ((idealLayers 0 (SplitStep.schedule N J)).take (pre ++ [layer]).length) s := by
      rw [hTake, ← row.child_ideal k i positive]
      exact row.child_mem_ideal_run pre hMem k _
    have hBounds := realizedLayerIdeal_bounds layer (fun i : p.Active => p.ideal i.1) s
      row.frequencyContract Finset.univ p.active_pairwiseDisjoint
      (fun i _ => p.platform_open i.1) (fun i _ => hQ.subset (p.platform_subset i.1))
      k p.smooth_second p.smooth_fourth (fun i _ x hx => (hJets i.1 x hx).1)
      (fun i _ x hx => (hJets i.1 x hx).2) (4 * (2 : ℝ) ^ (4 * N * J)) hOld₂ hOld₄
      (fun i _ positive => IdealNode.all_layer_node_A_bound N J _ s hN hs _ (hRun i positive))
      (fun i _ positive => IdealNode.all_layer_node_fourth_norm_bound N J _ s hs' _ (hRun i positive))
    refine ⟨hExact k, ?_, ?_, pre ++ [layer], hSch', ?_, row.child_mem_ideal_run pre hMem k⟩
    · rw [row.extends_second k]
      exact hBounds.1
    · rw [row.extends_fourth k]
      exact hBounds.2
    · rw [row.extends_prefix k]
      simp [hDepth]
  · refine ⟨PhysicalPrefix.root_exactJets Q hOpen hNonempty, ?_, ?_, [], rfl, rfl, ?_⟩
    · intro x
      change tensorHS (iteratedFDeriv ℝ 2 (0 : Plane → ℝ) x) ≤ √(11 / 2 : ℝ) + 1
      simp only [iteratedFDeriv_zero, Pi.zero_apply, tensorHS, map_zero, norm_zero]
      positivity
    · intro x
      change tensorHS (iteratedFDeriv ℝ 4 (0 : Plane → ℝ) x) ≤ 4 * (2 : ℝ) ^ (4 * N * J) + 1
      simp only [iteratedFDeriv_zero, Pi.zero_apply, tensorHS, map_zero, norm_zero]
      positivity
    · intro i
      change IdealNode.root ∈ [IdealNode.root]
      simp

/-- Every strictly increasing sequence of successors retains the row's global
uniform convergence in values and first derivatives. -/
public theorem PhysicalLayerRow.input_c1_tendsto_subseq {Q : Set Plane}
    {s δ : ℝ} {layer : IdealLayer} {p : PhysicalPrefix Q} {next : ℕ → PhysicalPrefix Q}
    {dirs : PhysicalDirections} (row : PhysicalLayerRow dirs s δ layer p next)
    (hQ : Bornology.IsBounded Q) (σ : ℕ → ℕ) (hσ : StrictMono σ) :
    TendstoUniformly (fun k => (next (σ k)).input) p.input atTop ∧
      TendstoUniformly (fun k => fderiv ℝ (next (σ k)).input) (fderiv ℝ p.input) atTop := by
  obtain ⟨hV, hD⟩ := row.input_c1_tendsto (fun i => hQ.subset (p.platform_subset i.1))
  constructor
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    exact hσ.tendsto_atTop.eventually (Metric.tendstoUniformly_iff.mp hV ε hε)
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    exact hσ.tendsto_atTop.eventually (Metric.tendstoUniformly_iff.mp hD ε hε)

/-- A terminal input has the normalized Hessian bound of its physical leaf. -/
public theorem bounded_terminal_input_hessian {Q : Set Plane} {N J : ℕ} {s δ : ℝ}
    {layers : List IdealLayer} {p : PhysicalPrefix Q}
    (T : PhysicalParameterTree idealPhysicalDirections s δ (ScheduledPhysicalInvariant N J s) layers p)
    {f : Plane → ℝ} (hf : f ∈ T.terminalInputs) (x : Plane) :
    tensorHS (iteratedFDeriv ℝ 2 f x) ≤ (√(11 / 2 : ℝ) + 1) / 5 := by
  obtain ⟨path, rfl⟩ := hf
  let leaf := T.toParameterTree.leafAt path
  have h := (T.leaf_valid path).2.1 x
  change tensorHS (iteratedFDeriv ℝ 2 ((1 / 5 : ℝ) • leaf.secondPotential) x) ≤ _
  have hSmooth : ContDiffAt ℝ 2 leaf.secondPotential x :=
    (leaf.smooth_second.of_le (by simp)).contDiffAt
  rw [iteratedFDeriv_const_smul_apply hSmooth, tensorHS_smul_eq,
    abs_of_nonneg (show (0 : ℝ) ≤ 1 / 5 by norm_num)]
  linarith only [h]

end C2Riemannian
