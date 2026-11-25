module

public import C2Riemannian.ConditionalTangentialReadouts
public import C2Riemannian.SameDiskConditionalPairings

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped NNReal Topology

namespace C2Riemannian.IdealLayer

/-- A tangent to the phase lines of each row in the ideal schedule. -/
@[expose] public noncomputable def tangent (layer : IdealLayer) (s : ℝ) : Plane :=
  match layer.step with
  | .vertical => coordinateDirection 1 0
  | .first => coordinateDirection (-s) 1
  | .second | .fourth => coordinateDirection 0 1
  | .third => coordinateDirection s 1

public theorem inner_normal_tangent (layer : IdealLayer) (s : ℝ) :
    inner ℝ (layer.normal s) (layer.tangent s) = 0 := by
  cases layer with
  | mk step n =>
    cases step <;> simp [normal, tangent, PiLp.inner_apply, Fin.sum_univ_two, coordinateDirection]

end C2Riemannian.IdealLayer

namespace C2Riemannian.PhysicalLayerRow

/-- On the shared conditional extraction, both phase means have the same
tangential Hessian rows as the weak-jet limit on the parent platform. -/
public theorem same_disk_conditional_phase_mean_tangent_ae
    {Q : Set Plane} {directions : PhysicalDirections} {s δ : ℝ} {layer : IdealLayer}
    {p : PhysicalPrefix Q} {next : ℕ → PhysicalPrefix Q}
    (row : PhysicalLayerRow directions s δ layer p next) (i : p.Active)
    (hn : directions.normal layer s ≠ 0) (τ : Plane) (hτ : inner ℝ (directions.normal layer s) τ = 0)
    {m : ℕ} {a : Plane} {R K : ℝ≥0}
    {W : ℕ → WeakJet2 m (⟨Metric.ball a R, Metric.isOpen_ball⟩ : Opens Plane)}
    (C : WeakJet2.SameDiskLimit a R K W) (hp : p.platform i.1 ⊆ Metric.ball a R)
    (base σ : ℕ → ℕ) (hBase : StrictMono base) (hσ : StrictMono σ)
    (state : ℕ → Plane → HessianBall m K)
    (L : p.Active × Bool → Plane → PositiveFunctional (HessianBall m K))
    (hState : ∀ j, ∀ᵐ x ∂volume.restrict (Metric.ball a R),
      (state j x).val = ((C.normalized j).hessian x).coordinates)
    (hL : ∀ j f, Measurable (fun x => L j x f))
    (hPair : ∀ j f (γ : Plane → ℝ), IntegrableOn γ (p.platform j.1.1) volume →
      Tendsto (fun n => ∫ x in p.platform j.1.1,
        row.phaseWeight j.1 j.2 (base (C.subseq (σ n))) x * f (state (C.subseq (σ n)) x) * γ x)
        atTop (𝓝 (∫ x in p.platform j.1.1, L j x f * γ x))) :
    ∀ᵐ x ∂volume.restrict (p.platform i.1), ∀ sign,
      (HessianBall.meanHessian (L (i, sign) x)).applyRows (τ 0) (τ 1) =
        (C.limit.hessian x).applyRows (τ 0) (τ 1) := by
  exact row.conditional_phase_mean_tangent_ae i hn (fun n => base (C.subseq (σ n)))
    (hBase.comp (C.strictMono_subseq.comp hσ)) τ hτ hp hp
    (fun n => C.normalized (C.subseq (σ n))) C.limit
    (fun n => (C.normalized_gradient_continuous (C.subseq (σ n))).mono hp)
    ((lipschitzOnWith_gradient_of_gradHS C.gradient_hs_le).continuousOn.mono hp)
    (fun n S hS => hσ.tendsto_atTop.eventually (C.gradient_convergence n S hS))
    (fun n => state (C.subseq (σ n))) (fun n => hState (C.subseq (σ n))) (fun sign => L (i, sign))
    (fun sign => hL (i, sign)) (fun sign => hPair (i, sign))

end C2Riemannian.PhysicalLayerRow
