module

public import C2Riemannian.SameDiskPhaseTransfers
public import C2Riemannian.IdealLayerEnergyComparison

set_option autoImplicit false
set_option maxHeartbeats 900000

open Filter MeasureTheory Set TopologicalSpace
open scoped NNReal Distributions Topology

namespace C2Riemannian.PhysicalLayerRow

variable {Q : Set Plane} {s δ : ℝ} {layer : IdealLayer}
  {p : PhysicalPrefix Q} {next : ℕ → PhysicalPrefix Q}
  {m : ℕ} {a : Plane} {R K : ℝ≥0}

/-- Transfer a common child energy budget through one actual layer, using its
scalar source jump and the pointwise comparison appropriate to that source. -/
public theorem energy_solution_of_children
    (row : PhysicalLayerRow idealPhysicalDirections s δ layer p next)
    (hQ : Q ⊆ Metric.ball a R) (hBoundedQ : Bornology.IsBounded Q)
    (hm : 0 < m) (hR : 0 < R) (base : ℕ → ℕ) (hBase : StrictMono base)
    (F : PhysicalPrefix Q → Plane → ℝ) (Δ : p.Active → Bool → ℝ) (B gain : ℝ)
    (hChildren : ∀ j, (next (base j)).HasEnergySolution m a R K (F (next (base j))) B)
    (hSourceInt : LocallyIntegrableOn (F p) (Metric.ball a R) volume)
    (hSourceTests : ∀ φ : 𝓓((⟨Metric.ball a R, Metric.isOpen_ball⟩ : Opens Plane), ℝ),
      Tendsto (fun n => ∫ x in Metric.ball a R, φ x • F (next n) x) atTop
        (𝓝 (∫ x in Metric.ball a R, φ x • F p x)))
    (hJump : ∀ i : p.Active, ∀ sign n, EqOn (F (next n)) (fun x => F p x + Δ i sign)
      ((next n).platform (row.childLabel n (i, sign))))
    (hCompare : ∀ (i : p.Active) (H : Hess3 m) (L : Bool → PositiveFunctional (HessianBall m K)),
      H.frobenius ≤ (K : ℝ) →
      H.yy = (1 / 2 : ℝ) • ((L true).mean HessianBall.yy + (L false).mean HessianBall.yy) →
      (∀ sign, (HessianBall.meanHessian (L sign)).applyRows (layer.tangent s 0) (layer.tangent s 1) =
        H.applyRows (layer.tangent s 0) (layer.tangent s 1) ∧
        L sign HessianBall.curvature - H.q = Δ i sign ∧
        (layer.step.continues sign = true → L sign HessianBall.energy ≤ B)) →
      H.energy + gain ≤ B) :
    p.HasEnergySolution m a R K (F p) (B - gain) := by
  choose W hValue hGradient hSecond hHess hEq hEn using hChildren
  have hMeasure (j : ℕ) :
      (volume : Measure Plane).restrict (WeakJet2.openDiskExhaustion a R j : Set Plane) ≤
        volume.restrict (Metric.ball a R) :=
    Measure.restrict_mono (WeakJet2.openDiskExhaustion_subset a R j) le_rfl
  obtain ⟨C, hC⟩ := WeakJet2.exists_same_disk_solution_limit hm a R K hR W
    (fun n j => (hValue n).mono_measure (hMeasure j)) (fun n j => (hGradient n).mono_measure (hMeasure j))
    hHess (fun j => F (next (base j))) (F p) hEq hSourceInt
    (fun φ => (hSourceTests φ).comp hBase.tendsto_atTop)
  obtain ⟨L, hL⟩ := row.exists_same_disk_phase_transfers hQ hBoundedQ C base hBase F Δ B
    hHess hEq hC (fun i => hSourceInt.mono_set ((p.platform_subset i.1).trans hQ)) hJump hEn
  refine ⟨C.limit, C.bounds.value_mem, C.bounds.gradient_mem, C.bounds.second_mem,
    C.bounds.frobenius_bound, hC, fun i => ?_⟩
  filter_upwards [hL i] with x hx
  exact le_sub_iff_add_le.mpr (hCompare i (C.limit.hessian x) (fun b => L (i, b) x) hx.1 hx.2.1 hx.2.2)

end C2Riemannian.PhysicalLayerRow
