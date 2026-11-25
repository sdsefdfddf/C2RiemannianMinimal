module

public import C2Riemannian.SameDiskEnergyTransfer
public import C2Riemannian.PhysicalSourceLimits

set_option autoImplicit false

open MeasureTheory Set TopologicalSpace
open scoped ContDiff NNReal

namespace C2Riemannian.PhysicalLayerRow

variable {Q : Set Plane} {s δ : ℝ} {layer : IdealLayer}
  {p : PhysicalPrefix Q} {next : ℕ → PhysicalPrefix Q}
  {m : ℕ} {a : Plane} {R K : ℝ≥0}

/-- The analytic layer implication for the linear source on an actual row. -/
public theorem linear_energy_solution_of_children
    (row : PhysicalLayerRow idealPhysicalDirections s δ layer p next)
    (hQ : Q ⊆ Metric.ball a R) (hBoundedQ : Bornology.IsBounded Q)
    (hp : p.ExactJets) (hExact : ∀ n, (next n).ExactJets)
    (hSigma : ∀ i : p.Active, (p.ideal i.1).sigma ^ 2 = 1)
    (hs : 0 ≤ s) (hs' : s ≤ 1) (hm : 0 < m) (hR : 0 < R) (hK : (1 : ℝ) ≤ K)
    {v₀ : Plane → ℝ} (hv₀ : ContDiffOn ℝ 2 v₀ (Metric.ball a R))
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)
    (base : ℕ → ℕ) (hBase : StrictMono base) (B : ℝ)
    (hChildren : ∀ j, (next (base j)).HasEnergySolution m a R K
      ((next (base j)).linearSource v₀ θ) B) :
    p.HasEnergySolution m a R K (p.linearSource v₀ θ)
      (B - (CycleGainArithmetic.layer_gain_schedule s K θ 0 layer.step).1) := by
  let U : Opens Plane := ⟨Metric.ball a R, Metric.isOpen_ball⟩
  apply row.energy_solution_of_children hQ hBoundedQ hm hR base hBase
    (fun pre => pre.linearSource v₀ θ) (linearJump p layer s θ) B _ hChildren
    (p.linearSource_locallyIntegrable (U := U) hv₀ θ)
  · exact row.linear_source_test_limits (fun i => hBoundedQ.subset (p.platform_subset i.1)) hv₀ θ
  · intro i sign n
    exact row.linear_exact_child_profile hp hExact i sign n
      (hv₀.mono ((p.platform_subset i.1).trans hQ)) θ
  · intro i H L hH hY hPhase
    exact HessianBall.linear_layer_energy_comparison p i layer s θ (hSigma i) hs hs' hθ hθ' hK
      H L B hH hY hPhase

/-- The analytic layer implication for the reverse source on an actual row. -/
public theorem reverse_energy_solution_of_children
    (row : PhysicalLayerRow idealPhysicalDirections s δ layer p next)
    (hQ : Q ⊆ Metric.ball a R) (hBoundedQ : Bornology.IsBounded Q)
    (hp : p.ExactJets) (hExact : ∀ n, (next n).ExactJets)
    (hs : 0 ≤ s) (hs' : s ≤ 1) (hm : 0 < m) (hR : 0 < R)
    (base : ℕ → ℕ) (hBase : StrictMono base) (B gain : ℝ)
    (hChildren : ∀ j, (next (base j)).HasEnergySolution m a R K (next (base j)).reverseSource B)
    (hGain : ∀ i : p.Active, gain ≤ match layer.step with
      | .first | .third => s ^ 2 * reverseJump p layer s i true - 7 * (K : ℝ) ^ 2 * s ^ 3
      | _ => 0) :
    p.HasEnergySolution m a R K p.reverseSource (B - gain) := by
  have hc : Continuous p.reverseSource :=
    (continuous_scalarHessianDet (p.input_smooth.of_le (by simp))).neg
  apply row.energy_solution_of_children hQ hBoundedQ hm hR base hBase
    (fun pre => pre.reverseSource) (reverseJump p layer s) B gain hChildren
    (hc.continuousOn.locallyIntegrableOn Metric.isOpen_ball.measurableSet)
  · exact row.reverse_source_test_limits (fun i => hBoundedQ.subset (p.platform_subset i.1))
  · exact row.reverse_exact_child_profile hp hExact
  · intro i H L hH hY hPhase
    exact HessianBall.reverse_layer_energy_comparison p i layer s hs hs' K.coe_nonneg
      H L B gain hH hY hPhase (hGain i)

end C2Riemannian.PhysicalLayerRow
