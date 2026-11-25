module

public import C2Riemannian.DiskSolvability
import Mathlib.Analysis.InnerProductSpace.LinearMap

set_option autoImplicit false
set_option maxHeartbeats 600000

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

namespace C2Riemannian.WeakJet2

variable {m n : ℕ} {U : Opens Plane}

/-- An output-space linear isometry commutes with extraction of the weak jet. -/
@[expose] public noncomputable def mapIsometry (w : WeakJet2 m U) (I : Target m →ₗᵢ[ℝ] Target n) :
    WeakJet2 n U where
  value := fun x => I (w.value x)
  gradient := fun x => I.toContinuousLinearMap.comp (w.gradient x)
  second := fun x => (ContinuousLinearMap.compL ℝ Plane (Target m) (Target n)
    I.toContinuousLinearMap).comp (w.second x)
  weak_value := w.weak_value.clm_comp I.toContinuousLinearMap
  weak_gradient := w.weak_gradient.clm_comp
    (ContinuousLinearMap.compL ℝ Plane (Target m) (Target n) I.toContinuousLinearMap)

/-- The norm and the curvature of the Hessian are invariant under this map. -/
public theorem mapIsometry_hessian (w : WeakJet2 m U) (I : Target m →ₗᵢ[ℝ] Target n) (x : Plane) :
    ((w.mapIsometry I).hessian x).frobenius = (w.hessian x).frobenius ∧
    ((w.mapIsometry I).hessian x).q = (w.hessian x).q := by
  have hx : (w.mapIsometry I).hessian x =
      ⟨I ((w.hessian x).xx), I ((w.hessian x).xy), I ((w.hessian x).yy)⟩ := rfl
  rw [hx]
  simp only [Hess3.frobenius, Hess3.frobeniusSq, Hess3.q, I.norm_map, I.inner_map_map, and_self]

/-- Zero padding preserves the Frobenius bound, source and weak regularity on the disk. -/
public theorem DiskSolvability.solves_of_le_dimension {a : Plane} {R K : ℝ≥0} {F : Plane → ℝ}
    (hmn : m ≤ n) (h : DiskSolvability.Solves m a R K F) : DiskSolvability.Solves n a R K F := by
  let I : Target m →ₗᵢ[ℝ] Target n := LinearIsometry.piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hmn)
  obtain ⟨w, hw, hgrad, _, hK, hq⟩ := h
  let L := I.toContinuousLinearMap
  let L₁ := ContinuousLinearMap.compL ℝ Plane (Target m) (Target n) L
  have hb : ∀ᵐ x ∂volume.restrict (Metric.ball a R), ((w.mapIsometry I).hessian x).frobenius ≤ (K : ℝ) := by
    filter_upwards [hK] with x hx
    rwa [(w.mapIsometry_hessian I x).1]
  refine ⟨w.mapIsometry I, L.comp_memLp' hw, L₁.comp_memLp' hgrad,
    (w.mapIsometry I).second_memLp_top_of_frobenius_ae_le hb, hb, ?_⟩
  filter_upwards [hq] with x hx
  exact (w.mapIsometry_hessian I x).2.trans hx

end C2Riemannian.WeakJet2
