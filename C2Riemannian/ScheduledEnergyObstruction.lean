module

public import C2Riemannian.PhysicalEnergyLayer
public import C2Riemannian.PhysicalLayerGains
public import C2Riemannian.ObstructionParameters
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set
open scoped ContDiff NNReal BigOperators

namespace C2Riemannian

private theorem linear_gain_independent_of_block (s K θ : ℝ) (j : ℕ) (step : SplitStep) :
    (CycleGainArithmetic.layer_gain_schedule s K θ j step).1 =
      (CycleGainArithmetic.layer_gain_schedule s K θ 0 step).1 := by
  cases step <;> rfl

private theorem reverse_gain_le_of_row {Q : Set Plane} (p : PhysicalPrefix Q) (i : p.Active)
    (layer : IdealLayer) (row : SplitStep × ℕ) (s K θ : ℝ) (hrow : row.1 = layer.step)
    (h : IdealNode.reverseContribution layer.step (p.ideal i.1) s =
      IdealNode.scheduledReverseContribution s row) :
    (CycleGainArithmetic.layer_gain_schedule s K θ row.2 row.1).2 ≤ match layer.step with
      | .first | .third => s ^ 2 * PhysicalLayerRow.reverseJump p layer s i true - 7 * K ^ 2 * s ^ 3
      | _ => 0 := by
  obtain ⟨step, j⟩ := row
  change step = layer.step at hrow
  subst step
  cases hstep : layer.step <;>
    simp only [hstep, CycleGainArithmetic.layer_gain_schedule, CycleGainArithmetic.coefficient,
      IdealNode.reverseContribution, IdealNode.scheduledReverseContribution,
      PhysicalLayerRow.reverseJump, IdealNode.child, neg_sq, le_refl] at h ⊢
  all_goals linarith only [h]

section Tree

variable {Q : Set Plane} {s δ : ℝ} {N J m : ℕ} {a : Plane} {R K : ℝ≥0}
  {p : PhysicalPrefix Q} {layers : List IdealLayer}

/-- Goodness for the linear source propagates the exact remaining linear budget. -/
public theorem linear_energy_solution_of_good
    (T : PhysicalParameterTree idealPhysicalDirections s δ (ScheduledPhysicalInvariant N J s) layers p)
    (hQ : Q ⊆ Metric.ball a R) (hBoundedQ : Bornology.IsBounded Q)
    (hN : 2 ≤ N) (hsNorm : 2 * (N : ℝ) * s ^ 2 = 1) (hs : 0 ≤ s) (hs' : s ≤ 1)
    (hm : 0 < m) (hR : 0 < R) (hK : (1 : ℝ) ≤ K)
    {v₀ : Plane → ℝ} (hv₀ : ContDiffOn ℝ 2 v₀ (Metric.ball a R))
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)
    (hGood : ParameterTree.Good
      (fun z => WeakJet2.DiskSolvability.Solves m a R K (z.linearSource v₀ θ)) T.toParameterTree) :
    p.HasEnergySolution m a R K (p.linearSource v₀ θ)
      (scheduledEnergyBudget N J s K θ false layers) := by
  refine T.physical_certificate_of_good
    (fun z => WeakJet2.DiskSolvability.Solves m a R K (z.linearSource v₀ θ))
    (fun tail z => z.HasEnergySolution m a R K (z.linearSource v₀ θ)
      (scheduledEnergyBudget N J s K θ false tail)) ?_ ?_ hGood
  · intro z _ hSol
    rw [scheduledEnergyBudget_nil]
    exact z.hasEnergySolution_of_solves hQ hSol
  · intro layer tail z next row hValid hNext k hk hChild
    obtain ⟨indexed, hIndex, hStep, _⟩ :=
      ScheduledPhysicalInvariant.exists_indexed_row_with_reverse_contribution N J s hN hsNorm z layer tail hValid
    have hσ (i : z.Active) : (z.ideal i.1).sigma ^ 2 = 1 := by
      obtain ⟨_, _, _, pre, _, _, hRun⟩ := hValid
      exact IdealNode.run_sigma_sq pre s (hRun i.1)
    rw [ScheduledPhysicalInvariant.scheduledEnergyBudget_cons N J s K θ false z layer tail hValid indexed hIndex]
    change z.HasEnergySolution m a R K (z.linearSource v₀ θ)
      (scheduledEnergyBudget N J s K θ false tail - (CycleGainArithmetic.layer_gain_schedule s K θ indexed.2 indexed.1).1)
    rw [hStep, linear_gain_independent_of_block]
    exact row.linear_energy_solution_of_children hQ hBoundedQ hValid.1 (fun n => (hNext n).1)
      hσ hs hs' hm hR hK hv₀ θ hθ hθ' k hk _ hChild

/-- Goodness for the reverse source propagates the signed remaining reverse budget. -/
public theorem reverse_energy_solution_of_good
    (T : PhysicalParameterTree idealPhysicalDirections s δ (ScheduledPhysicalInvariant N J s) layers p)
    (hQ : Q ⊆ Metric.ball a R) (hBoundedQ : Bornology.IsBounded Q)
    (hN : 2 ≤ N) (hsNorm : 2 * (N : ℝ) * s ^ 2 = 1) (hs : 0 ≤ s) (hs' : s ≤ 1)
    (hm : 0 < m) (hR : 0 < R) (θ : ℝ)
    (hGood : ParameterTree.Good
      (fun z => WeakJet2.DiskSolvability.Solves m a R K z.reverseSource) T.toParameterTree) :
    p.HasEnergySolution m a R K p.reverseSource (scheduledEnergyBudget N J s K θ true layers) := by
  refine T.physical_certificate_of_good
    (fun z => WeakJet2.DiskSolvability.Solves m a R K z.reverseSource)
    (fun tail z => z.HasEnergySolution m a R K z.reverseSource (scheduledEnergyBudget N J s K θ true tail))
    ?_ ?_ hGood
  · intro z _ hSol
    rw [scheduledEnergyBudget_nil]
    exact z.hasEnergySolution_of_solves hQ hSol
  · intro layer tail z next row hValid hNext k hk hChild
    obtain ⟨indexed, hIndex, hStep, hRev⟩ :=
      ScheduledPhysicalInvariant.exists_indexed_row_with_reverse_contribution N J s hN hsNorm z layer tail hValid
    rw [ScheduledPhysicalInvariant.scheduledEnergyBudget_cons N J s K θ true z layer tail hValid indexed hIndex]
    change z.HasEnergySolution m a R K z.reverseSource
      (scheduledEnergyBudget N J s K θ true tail - (CycleGainArithmetic.layer_gain_schedule s K θ indexed.2 indexed.1).2)
    exact row.reverse_energy_solution_of_children hQ hBoundedQ hValid.1 (fun n => (hNext n).1) hs hs'
      hm hR k hk _ _ hChild (fun i => reverse_gain_le_of_row z i layer indexed s K θ hStep (hRev i))

end Tree

namespace ParameterTree

/-- Pointwise solvability along every path is the universal leaf predicate. -/
public theorem everyLeaf_of_solvable_paths {A : Type*} (S : A → Prop) {d : ℕ}
    (T : ParameterTree A d) (h : ∀ path, S (T.leafAt path)) : EveryLeaf S T := by
  induction T with
  | leaf x => exact h .nil
  | node x children ih =>
    exact fun k => ih k (fun path => h (.cons k path))

end ParameterTree

end C2Riemannian
