module

public import C2Riemannian.PhysicalConditionalExtraction
public import C2Riemannian.SameDiskClosure
public import C2Riemannian.WeakHessianReadouts

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped NNReal Topology

namespace C2Riemannian.PhysicalLayerRow

/-- Extend the compactness subsequence by one common conditional extraction, on
the normalized weak Hessians of the same disk. -/
public theorem exists_same_disk_conditional_pairings
    {Q : Set Plane} {directions : PhysicalDirections} {s δ : ℝ} {layer : IdealLayer}
    {p : PhysicalPrefix Q} {next : ℕ → PhysicalPrefix Q}
    (row : PhysicalLayerRow directions s δ layer p next) (hQ : Bornology.IsBounded Q)
    (hn : directions.normal layer s ≠ 0)
    {m : ℕ} {a : Plane} {R K : ℝ≥0}
    {W : ℕ → WeakJet2 m (⟨Metric.ball a R, Metric.isOpen_ball⟩ : Opens Plane)}
    (C : WeakJet2.SameDiskLimit a R K W)
    (hHess : ∀ n, ∀ᵐ x ∂volume.restrict (Metric.ball a R),
      ((W n).hessian x).frobenius ≤ (K : ℝ))
    (base : ℕ → ℕ) (hBase : StrictMono base) :
    ∃ (σ : ℕ → ℕ) (state : ℕ → Plane → HessianBall m K)
      (L : p.Active × Bool → Plane → PositiveFunctional (HessianBall m K)),
      StrictMono σ ∧
      (∀ j, Measurable (state j)) ∧
      (∀ j, ∀ᵐ x ∂volume.restrict (Metric.ball a R),
        (state j x).val = ((C.normalized j).hessian x).coordinates) ∧
      (∀ i (f : C(HessianBall m K, ℝ)), Measurable (fun x => L i x f)) ∧
      ∀ (i : p.Active × Bool) (f : C(HessianBall m K, ℝ)) (γ : Plane → ℝ),
        IntegrableOn γ (p.platform i.1.1) volume →
        Tendsto
          (fun j => ∫ x in p.platform i.1.1,
            row.phaseWeight i.1 i.2 (base (C.subseq (σ j))) x *
              f (state (C.subseq (σ j)) x) * γ x)
          atTop (𝓝 (∫ x in p.platform i.1.1, L i x f * γ x)) := by
  have hState (j : ℕ) := (C.normalized j).exists_measurable_hessian_state K.coe_nonneg
    (C.normalized j).weak_gradient.locallyIntegrableOn_deriv.aestronglyMeasurable
    (by rw [(C.normalized_data j).2.1]; exact hHess j)
  choose state hMeas hEq using hState
  have hInv (j : ℕ) : Function.invFun base (base j) = j :=
    Function.leftInverse_invFun hBase.injective j
  obtain ⟨σ, L, hσ, hL, hPair⟩ := row.exists_shared_conditional_pairings hQ hn m K K.coe_nonneg
    (state ∘ Function.invFun base) (fun j => hMeas (Function.invFun base j))
    (base ∘ C.subseq) (hBase.comp C.strictMono_subseq)
  refine ⟨σ, state, L, hσ, hMeas, hEq, hL, fun i f γ hγ => ?_⟩
  simpa only [Function.comp_def, hInv, PositiveFunctional.integral_representingMeasure] using hPair i f γ hγ

end C2Riemannian.PhysicalLayerRow
