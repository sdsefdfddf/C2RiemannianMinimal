module

public import C2Riemannian.WeakHessianState

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace

namespace C2Riemannian

/-- The conditional energy readout is half the squared norm of the vertical Hessian entry. -/
@[expose] public noncomputable def HessianBall.energy {m : ℕ} {K : ℝ} :
    C(HessianBall m K, ℝ) := PositiveFunctional.energyReadout HessianBall.yy

namespace WeakJet2

/-- Every Hessian readout agrees almost everywhere with its value on the original
weak Hessian, after restriction to any measurable subset of the disk. -/
public theorem hessian_state_readouts_ae {m : ℕ} {U : Opens Plane}
    (w : WeakJet2 m U) {K : ℝ} {state : Plane → HessianBall m K}
    (hState : ∀ᵐ x ∂volume.restrict (U : Set Plane),
      (state x).val = (w.hessian x).coordinates)
    {P : Set Plane} (hP : P ⊆ (U : Set Plane)) :
    ∀ᵐ x ∂volume.restrict P,
      HessianBall.xx (state x) = (w.hessian x).xx ∧
      HessianBall.xy (state x) = (w.hessian x).xy ∧
      HessianBall.yy (state x) = (w.hessian x).yy ∧
      HessianBall.curvature (state x) = (w.hessian x).q := by
  filter_upwards [MeasureTheory.ae_mono (Measure.restrict_mono hP le_rfl) hState] with x hx
  have hb : (w.hessian x).frobenius ≤ K := by
    have hm := (state x).property
    rw [hx, Metric.mem_closedBall, dist_zero_right, Hess3.norm_coordinates] at hm
    exact hm
  have hEq : state x = HessianBall.ofHessian (w.hessian x) hb := Subtype.ext hx
  simp only [hEq, HessianBall.xx_ofHessian, HessianBall.xy_ofHessian,
    HessianBall.yy_ofHessian, HessianBall.curvature_ofHessian, and_self]

end WeakJet2
end C2Riemannian
