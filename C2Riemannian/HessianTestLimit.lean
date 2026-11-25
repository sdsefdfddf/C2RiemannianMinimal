module

public import C2Riemannian.WeakAnalysis
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

open MeasureTheory Filter Set TopologicalSpace
open scoped Topology Distributions

namespace C2Riemannian

/-- A compact test only needs uniform convergence of the field on its support. -/
public theorem tendsto_smul_test_of_uniformOn {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {U : Opens Plane} (ψ : 𝓓(U, ℝ))
    {f : ℕ → Plane → F} {g : Plane → F}
    (hf : ∀ n, LocallyIntegrableOn (f n) U volume)
    {K : ℝ} (hK : ∀ n x, x ∈ tsupport (ψ : Plane → ℝ) → ‖f n x‖ ≤ K)
    (hu : TendstoUniformlyOn f g atTop (tsupport (ψ : Plane → ℝ))) :
    Tendsto (fun n => ∫ x in ↑U, ψ x • f n x) atTop (𝓝 (∫ x in ↑U, ψ x • g x)) := by
  let S := tsupport (ψ : Plane → ℝ)
  have hS : IsCompact S := ψ.hasCompactSupport
  have hsub : S ⊆ (U : Set Plane) := ψ.tsupport_subset
  have hrest (p : Plane → F) : (∫ x in ↑U, ψ x • p x) = ∫ x in S, ψ x • p x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero U.isOpen.measurableSet hsub
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx.2, zero_smul]
  simp only [hrest]
  let _ : IsFiniteMeasure (volume.restrict S) :=
    isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  obtain ⟨B, hB⟩ := ψ.hasCompactSupport.exists_bound_of_continuous ψ.continuous
  apply tendsto_integral_of_dominated_convergence (fun _ => B * K)
  · intro n
    exact ψ.continuous.aestronglyMeasurable.smul
      ((hf n).integrableOn_compact_subset hsub hS).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    filter_upwards [ae_restrict_mem hS.isClosed.measurableSet] with x hx
    rw [norm_smul]
    exact mul_le_mul (hB x) (hK n x hx) (norm_nonneg _) ((norm_nonneg _).trans (hB x))
  · filter_upwards [ae_restrict_mem hS.isClosed.measurableSet] with x hx
    exact (hu.tendsto_at hx).const_smul (ψ x)

namespace WeakJet2

variable {m : ℕ} {U : Opens Plane}

/-- Weak testing of one Hessian column uses just one derivative of the test and
the corresponding column of the weak gradient. -/
public theorem test_second_column (w : WeakJet2 m U) (v u : Plane) (φ : 𝓓(U, ℝ)) :
    (∫ x in ↑U, φ x • w.second x v u) =
      -(∫ x in ↑U, (TestFunction.lineDerivCLM ℝ v φ : 𝓓(U, ℝ)) x • w.gradient x u) := by
  let ψ : 𝓓(U, ℝ) := TestFunction.lineDerivCLM ℝ v φ
  have hψ : (ψ : Plane → ℝ) = fun x => lineDeriv ℝ (φ : Plane → ℝ) x v :=
    funext fun _ => TestFunction.lineDerivCLM_apply_of_le le_top
  change (∫ x in ↑U, φ x • w.second x v u) = -(∫ x in ↑U, ψ x • w.gradient x u)
  rw [TauCeti.setIntegral_smul_eq_integral_smul φ, TauCeti.setIntegral_smul_eq_integral_smul ψ, hψ,
    (w.weak_component v u).integral_lineDeriv_smul_eq_neg_integral_smul φ, neg_neg]

/-- Compact-uniform convergence of a gradient column implies distributional
convergence of the corresponding weak Hessian column against the original test. -/
public theorem tendsto_second_column_test {W : ℕ → WeakJet2 m U} {w : WeakJet2 m U}
    (v u : Plane) (φ : 𝓓(U, ℝ)) (K : ℝ)
    (hK : ∀ n x, x ∈ tsupport ((TestFunction.lineDerivCLM ℝ v φ : 𝓓(U, ℝ)) : Plane → ℝ) →
      ‖(W n).gradient x u‖ ≤ K)
    (hu : TendstoUniformlyOn (fun n x => (W n).gradient x u) (fun x => w.gradient x u) atTop
      (tsupport ((TestFunction.lineDerivCLM ℝ v φ : 𝓓(U, ℝ)) : Plane → ℝ))) :
    Tendsto (fun n => ∫ x in ↑U, φ x • (W n).second x v u) atTop
      (𝓝 (∫ x in ↑U, φ x • w.second x v u)) := by
  simp only [test_second_column]
  exact (tendsto_smul_test_of_uniformOn (TestFunction.lineDerivCLM ℝ v φ)
    (fun n => ((W n).weak_component v u).locallyIntegrableOn) hK hu).neg

end WeakJet2
end C2Riemannian
