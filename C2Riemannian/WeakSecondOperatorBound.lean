module

public import C2Riemannian.MollifiedGradientBounds

set_option autoImplicit false

open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal

namespace C2Riemannian.WeakJet2

variable {m : ℕ} {U : Opens Plane} (w : WeakJet2 m U)

/-- The operator norm of the weak second derivative is bounded almost everywhere
by the Frobenius norm of its symmetric Hessian. -/
public theorem norm_second_le_hessian_frobenius_ae :
    ∀ᵐ x ∂volume.restrict (U : Set Plane), ‖w.second x‖ ≤ (w.hessian x).frobenius := by
  filter_upwards [w.gradHS_second_ae] with x hx
  let B : Plane →L[ℝ] (Plane →L[ℝ] Target m) := w.second x
  let A : Plane →L[ℝ] WithLp 2 (Target m × Target m) := gradientColumns.comp B
  have hBA : ‖B‖ ≤ ‖A‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
    intro v
    calc
      ‖B v‖ ≤ gradHS (B v) := opNorm_le_gradHS _
      _ = ‖A v‖ := (norm_gradientColumns (B v)).symm
      _ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
  exact hBA.trans ((opNorm_le_gradHS A).trans_eq hx)

/-- A Frobenius essential bound gives the same operator-norm essential bound. -/
public theorem norm_second_ae_le {K : ℝ}
    (hK : ∀ᵐ x ∂volume.restrict (U : Set Plane), (w.hessian x).frobenius ≤ K) :
    ∀ᵐ x ∂volume.restrict (U : Set Plane), ‖w.second x‖ ≤ K := by
  filter_upwards [w.norm_second_le_hessian_frobenius_ae, hK] with x hx hF
  exact hx.trans hF

/-- An essentially Frobenius-bounded weak Hessian has an essentially bounded
second Fréchet derivative field. -/
public theorem second_memLp_top_of_frobenius_ae_le {K : ℝ}
    (hK : ∀ᵐ x ∂volume.restrict (U : Set Plane), (w.hessian x).frobenius ≤ K) :
    MemLp w.second ∞ (volume.restrict (U : Set Plane)) :=
  memLp_top_of_bound w.weak_gradient.locallyIntegrableOn_deriv.aestronglyMeasurable K
    (w.norm_second_ae_le hK)

end C2Riemannian.WeakJet2

