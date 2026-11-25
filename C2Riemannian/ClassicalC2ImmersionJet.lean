module

public import C2Riemannian.HessianFrobenius
public import C2Riemannian.WeakAnalysis

set_option autoImplicit false
set_option maxHeartbeats 800000

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff ENNReal NNReal

namespace C2Riemannian.WeakJet2

/-- The weak fields and the Frobenius norm of the Hessian are essentially bounded
on each compact subset of the open domain. -/
@[expose] public def LocallyBoundedOnCompacts {m : ℕ} {U : Opens Plane}
    (w : WeakJet2 m U) : Prop :=
  ∀ S : Set Plane, IsCompact S → S ⊆ (U : Set Plane) →
    MemLp w.value ∞ (volume.restrict S) ∧ MemLp w.gradient ∞ (volume.restrict S) ∧
    MemLp w.second ∞ (volume.restrict S) ∧
    ∃ B : ℝ, ∀ᵐ x ∂volume.restrict S, (w.hessian x).frobenius ≤ B

variable {m : ℕ} {U : Opens Plane}

public theorem classical_grad_contDiff {F : Plane → Target m} (hF : ContDiff ℝ 2 F) :
    ContDiff ℝ 1 (fderiv ℝ F) :=
  hF.fderiv_right (by decide)

public theorem classical_second_continuous {F : Plane → Target m} (hF : ContDiff ℝ 2 F) :
    Continuous (fderiv ℝ (fderiv ℝ F)) :=
  ((classical_grad_contDiff hF).fderiv_right (m := 0) (by decide)).continuous

/-- A globally C² chart map induces the weak jet of its two classical derivatives. -/
@[expose] public noncomputable def classicalC2 (F : Plane → Target m) (hF : ContDiff ℝ 2 F) :
    WeakJet2 m U :=
  ⟨F, fderiv ℝ F, fderiv ℝ (fderiv ℝ F),
    TauCeti.hasWeakFDerivOn_of_differentiableOn
      (hF.continuous.continuousOn.locallyIntegrableOn U.isOpen.measurableSet)
      ((classical_grad_contDiff hF).continuous.continuousOn.locallyIntegrableOn U.isOpen.measurableSet)
      (fun x _ => hF.differentiable (by decide) x),
    TauCeti.hasWeakFDerivOn_of_differentiableOn
      ((classical_grad_contDiff hF).continuous.continuousOn.locallyIntegrableOn U.isOpen.measurableSet)
      ((classical_second_continuous hF).continuousOn.locallyIntegrableOn U.isOpen.measurableSet)
      (fun x _ => (classical_grad_contDiff hF).differentiable_one x)⟩

private theorem memLp_top_of_continuous_on_compact {E : Type*} [NormedAddCommGroup E]
    {f : Plane → E} (hf : Continuous f) {S : Set Plane} (hS : IsCompact S) :
    MemLp f ∞ (volume.restrict S) := by
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hf.continuousOn
  exact memLp_top_of_bound hf.aestronglyMeasurable C
    ((ae_restrict_mem hS.isClosed.measurableSet).mono hC)

public theorem classicalC2_locallyBounded {F : Plane → Target m} (hF : ContDiff ℝ 2 F) :
    (classicalC2 (U := U) F hF).LocallyBoundedOnCompacts := by
  let w : WeakJet2 m U := classicalC2 F hF
  have hB : Continuous w.second := classical_second_continuous hF
  have hc : Continuous (fun x => ((w.hessian x).coordinates)) := by
    simpa only [Function.comp_def, hessianColumns_apply, hessian] using
      (hessianColumns (m := m)).continuous.comp hB
  intro S hS _
  change MemLp w.value ∞ (volume.restrict S) ∧ MemLp w.gradient ∞ (volume.restrict S) ∧
    MemLp w.second ∞ (volume.restrict S) ∧ _
  refine ⟨memLp_top_of_continuous_on_compact (E := Target m) (f := F) hF.continuous hS,
    memLp_top_of_continuous_on_compact (E := Plane →L[ℝ] Target m)
      (f := fderiv ℝ F) (classical_grad_contDiff hF).continuous hS,
    memLp_top_of_continuous_on_compact (E := Plane →L[ℝ] (Plane →L[ℝ] Target m)) (f := w.second) hB hS, ?_⟩
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hc.continuousOn
  exact ⟨C, (ae_restrict_mem hS.isClosed.measurableSet).mono fun x hx =>
    (w.hessian x).norm_coordinates.ge.trans (hC x hx)⟩

end C2Riemannian.WeakJet2
