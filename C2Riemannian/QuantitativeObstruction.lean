module

public import C2Riemannian.ScheduledEnergyObstruction
public import C2Riemannian.RealizedParameterTree
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set
open scoped ContDiff NNReal

namespace C2Riemannian

variable {Q : Set Plane} {δ : ℝ} {N J m : ℕ} {a : Plane} {R K : ℝ≥0} {p : PhysicalPrefix Q}

public noncomputable abbrev ScheduledTree (N J : ℕ) (δ : ℝ) (p : PhysicalPrefix Q) :=
  PhysicalParameterTree idealPhysicalDirections (splittingSlope N) δ
    (ScheduledPhysicalInvariant N J (splittingSlope N)) (idealLayers 0 (SplitStep.schedule N J)) p

/-- The full linear energy budget is nonnegative at every good root. -/
public theorem linear_root_budget_nonneg
    (T : ScheduledTree N J δ p) (hQ : Q ⊆ Metric.ball a R) (hBoundedQ : Bornology.IsBounded Q)
    (hN : 2 ≤ N) (hm : 0 < m) (hR : 0 < R) (hK : (1 : ℝ) ≤ K)
    {v₀ : Plane → ℝ} (hv₀ : ContDiffOn ℝ 2 v₀ (Metric.ball a R))
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)
    (hGood : ParameterTree.Good
      (fun z => WeakJet2.DiskSolvability.Solves m a R K (z.linearSource v₀ θ)) T.toParameterTree) :
    0 ≤ (ObstructionParameters.rootBudgets N J (splittingSlope N) K θ).1 := by
  obtain ⟨hs, hsHalf, hsNorm⟩ := ObstructionParameters.slope_bounds N hN
  change 2 * (N : ℝ) * splittingSlope N ^ 2 = 1 at hsNorm
  have hCert := linear_energy_solution_of_good T hQ hBoundedQ hN hsNorm hs.le
    (hsHalf.trans (by norm_num)) hm hR hK hv₀ θ hθ hθ' hGood
  obtain ⟨i, hi⟩ := p.has_active
  have h := p.budget_nonneg_of_hasEnergySolution ⟨i, hi⟩ hCert
  rw [scheduledEnergyBudget_full N J (splittingSlope N) K θ false hsNorm] at h
  rw [ObstructionParameters.rootBudgets, CycleGainArithmetic.cycle_total_gains N J (splittingSlope N) K θ hsNorm]
  exact h

end C2Riemannian
