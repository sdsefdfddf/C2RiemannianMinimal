module

public import C2Riemannian.ConditionalHessianSources
public import C2Riemannian.DiskEnergyCertificate

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped NNReal Topology

namespace C2Riemannian.PhysicalLayerRow

variable {Q : Set Plane} {directions : PhysicalDirections} {s δ : ℝ}
  {layer : IdealLayer} {p : PhysicalPrefix Q} {next : ℕ → PhysicalPrefix Q}
  {m : ℕ} {a : Plane} {R K : ℝ≥0}

/-- A conditional functional inherits the energy certificate of each continuing
selected successor when its states represent the normalized weak Hessians. -/
public theorem same_disk_conditional_energy_bound
    (row : PhysicalLayerRow directions s δ layer p next)
    (i : p.Active) (sign : Bool) (hContinue : layer.step.continues sign = true)
    (hQ : Q ⊆ Metric.ball a R) (hBoundedQ : Bornology.IsBounded Q)
    (hn : directions.normal layer s ≠ 0)
    (k : ℕ → ℕ) (hk : StrictMono k)
    (w : ℕ → WeakJet2 m (⟨Metric.ball a R, Metric.isOpen_ball⟩ : Opens Plane))
    (state : ℕ → Plane → HessianBall m K)
    (L : Plane → PositiveFunctional (HessianBall m K)) (B : ℝ)
    (hState : ∀ j, Measurable (state j))
    (hStateEq : ∀ j, ∀ᵐ x ∂volume.restrict (Metric.ball a R),
      (state j x).val = ((w j).hessian x).coordinates)
    (hMeas : Measurable (fun x => L x HessianBall.energy))
    (hEnergy : ∀ j (i' : (next (k j)).Active),
      ∀ᵐ x ∂volume.restrict ((next (k j)).platform i'.1), ((w j).hessian x).energy ≤ B)
    (hPair : ∀ γ : Plane → ℝ, IntegrableOn γ (p.platform i.1) volume →
      Tendsto (fun j => ∫ x in p.platform i.1,
        row.phaseWeight i sign (k j) x * HessianBall.energy (state j x) * γ x) atTop
        (𝓝 (∫ x in p.platform i.1, L x HessianBall.energy * γ x))) :
    ∀ᵐ x ∂volume.restrict (p.platform i.1), L x HessianBall.energy ≤ B := by
  refine row.conditional_hessian_energy_bound (i := i) (sign := sign) (k := k)
    (state := state) (L := L) (hn := hn) (hk := hk)
    (hBoundedQ.subset (p.platform_subset i.1)) hState hMeas B ?_ hPair
  intro j
  let i' : (next (k j)).Active :=
    ⟨row.childLabel (k j) (i, sign), by rw [row.child_ideal]; exact hContinue⟩
  have hEnergyOn := (ae_restrict_iff' ((next (k j)).platform_open i'.1).measurableSet).mp (hEnergy j i')
  have hEnergyParent := MeasureTheory.ae_mono (Measure.restrict_le_self (s := p.platform i.1)) hEnergyOn
  have hReadout := (w j).hessian_state_readouts_ae (hStateEq j) ((p.platform_subset i.1).trans hQ)
  filter_upwards [hEnergyParent, hReadout] with x hx hRead hMem
  rw [HessianBall.energy, PositiveFunctional.energyReadout_apply, hRead.2.2.1, ← Hess3.energy]
  exact hx hMem

end C2Riemannian.PhysicalLayerRow
