module

public import C2Riemannian.WeakProducts
public import C2Riemannian.HessianAlgebra

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology

namespace C2Riemannian

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {m : ℕ}

/-- Evaluation of the Gram compatibility identity on one test and its three test derivatives.
The first term uses the two component inner products of the Hessian quadratic form. -/
@[expose] public noncomputable def gramTest (μ : Measure α) (φ ψxx ψxy ψyy : α → ℝ)
    (Px Py X Z Y : α → Target m) : Prop :=
  -2 * ((∫ x, φ x * inner ℝ (X x) (Y x) ∂μ) - (∫ x, φ x * inner ℝ (Z x) (Z x) ∂μ)) =
    (∫ x, ψyy x * inner ℝ (Px x) (Px x) ∂μ) +
    (∫ x, ψxx x * inner ℝ (Py x) (Py x) ∂μ) -
    2 * (∫ x, ψxy x * inner ℝ (Px x) (Py x) ∂μ)

/-- The test identity passes to the limit when the two gradient columns and three
Hessian columns converge strongly in L² on the domain of integration. -/
public theorem gramTest_of_strongL2 {ι : Type*} {l : Filter ι} [NeBot l]
    {φ ψxx ψxy ψyy : α → ℝ} {Px Py X Z Y : α → Target m}
    {PX PY XX ZZ YY : ι → α → Target m}
    (hφ : AEStronglyMeasurable φ μ) (hxx : AEStronglyMeasurable ψxx μ)
    (hxy : AEStronglyMeasurable ψxy μ) (hyy : AEStronglyMeasurable ψyy μ)
    (B : ℝ) (bφ : ∀ᵐ x ∂μ, ‖φ x‖ ≤ B) (bxx : ∀ᵐ x ∂μ, ‖ψxx x‖ ≤ B)
    (bxy : ∀ᵐ x ∂μ, ‖ψxy x‖ ≤ B) (byy : ∀ᵐ x ∂μ, ‖ψyy x‖ ≤ B)
    (hPx : StrongL2 l μ PX Px) (hPy : StrongL2 l μ PY Py)
    (hX : StrongL2 l μ XX X) (hZ : StrongL2 l μ ZZ Z) (hY : StrongL2 l μ YY Y)
    (htest : ∀ᶠ i in l, gramTest μ φ ψxx ψxy ψyy (PX i) (PY i) (XX i) (ZZ i) (YY i)) :
    gramTest μ φ ψxx ψxy ψyy Px Py X Z Y := by
  have hleft := ((hX.inner_test_tendsto hY hφ B bφ).sub
    (hZ.inner_test_tendsto hZ hφ B bφ)).const_mul (-2)
  have hright := ((hPx.inner_test_tendsto hPx hyy B byy).add
    (hPy.inner_test_tendsto hPy hxx B bxx)).sub
    ((hPx.inner_test_tendsto hPy hxy B bxy).const_mul 2)
  exact tendsto_nhds_unique_of_eventuallyEq hleft hright htest

/-- The split Hessian pairings agree with the pairing against the project's curvature field. -/
public theorem integral_weighted_q_eq {φ : α → ℝ} {H : α → Hess3 m}
    (hX : MemLp (fun x => (H x).xx) 2 μ) (hZ : MemLp (fun x => (H x).xy) 2 μ)
    (hY : MemLp (fun x => (H x).yy) 2 μ) (hφ : AEStronglyMeasurable φ μ)
    {B : ℝ} (hb : ∀ᵐ x ∂μ, ‖φ x‖ ≤ B) :
    (∫ x, φ x * (H x).q ∂μ) =
      (∫ x, φ x * inner ℝ (H x).xx (H x).yy ∂μ) -
      (∫ x, φ x * inner ℝ (H x).xy (H x).xy ∂μ) := by
  simp only [Hess3.q, mul_sub]
  exact integral_sub ((integrable_weak_inner hX hY).bdd_mul hφ hb)
    ((integrable_weak_inner hZ hZ).bdd_mul hφ hb)

end C2Riemannian
