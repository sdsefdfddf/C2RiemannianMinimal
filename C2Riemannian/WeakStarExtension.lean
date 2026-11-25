module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace C2Riemannian

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

private theorem bounded_test_dist {u φ ψ : α → ℝ} {B : ℝ}
    (hu : AEStronglyMeasurable u μ) (hb : ∀ᵐ x ∂μ, ‖u x‖ ≤ B)
    (hφ : Integrable φ μ) (hψ : Integrable ψ μ) :
    dist (∫ x, u x * φ x ∂μ) (∫ x, u x * ψ x ∂μ) ≤ B * (∫ x, ‖φ x - ψ x‖ ∂μ) := by
  rw [dist_eq_norm, ← integral_sub (hφ.bdd_mul hu hb) (hψ.bdd_mul hu hb)]
  simp only [← mul_sub]
  calc
    _ ≤ ∫ x, ‖u x * (φ x - ψ x)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, B * ‖φ x - ψ x‖ ∂μ := by
      refine integral_mono_ae (((hφ.sub hψ).bdd_mul hu hb).norm) ((hφ.sub hψ).norm.const_mul B) ?_
      filter_upwards [hb] with x hx
      exact (norm_mul _ _).le.trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
    _ = _ := integral_const_mul _ _

/-- An L¹-dense class of tests detects weak-star convergence for a uniformly
bounded sequence and a bounded candidate limit. -/
public theorem weakStar_of_dense_tests {ι : Type*} {l : Filter ι}
    {U : ι → α → ℝ} {u : α → ℝ} (T : Set (α → ℝ)) (B : ℝ) (hB : 0 ≤ B)
    (hU : ∀ i, AEStronglyMeasurable (U i) μ) (hu : AEStronglyMeasurable u μ)
    (hBound : ∀ i, ∀ᵐ x ∂μ, ‖U i x‖ ≤ B) (hBoundLimit : ∀ᵐ x ∂μ, ‖u x‖ ≤ B)
    (hDense : ∀ φ, Integrable φ μ → ∀ ε : ℝ, 0 < ε →
      ∃ ψ ∈ T, Integrable ψ μ ∧ (∫ x, ‖φ x - ψ x‖ ∂μ) ≤ ε)
    (hTest : ∀ ψ ∈ T, Tendsto (fun i => ∫ x, U i x * ψ x ∂μ) l (𝓝 (∫ x, u x * ψ x ∂μ)))
    {φ : α → ℝ} (hφ : Integrable φ μ) :
    Tendsto (fun i => ∫ x, U i x * φ x ∂μ) l (𝓝 (∫ x, u x * φ x ∂μ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := (ε / 4) / (B + 1)
  have hC : 0 < B + 1 := by linarith only [hB]
  have hδ : 0 < δ := div_pos (by positivity) hC
  obtain ⟨ψ, hψT, hψ, hApprox⟩ := hDense φ hφ δ hδ
  have hError : B * (∫ x, ‖φ x - ψ x‖ ∂μ) ≤ ε / 4 := by
    calc
      _ ≤ B * δ := mul_le_mul_of_nonneg_left hApprox hB
      _ ≤ (B + 1) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
      _ = _ := by rw [mul_comm]; exact div_mul_cancel₀ _ hC.ne'
  filter_upwards [Metric.tendsto_nhds.mp (hTest ψ hψT) (ε / 2) (by positivity)] with i hi
  calc
    dist (∫ x, U i x * φ x ∂μ) (∫ x, u x * φ x ∂μ) ≤
        dist (∫ x, U i x * φ x ∂μ) (∫ x, U i x * ψ x ∂μ) +
        dist (∫ x, u x * φ x ∂μ) (∫ x, u x * ψ x ∂μ) +
        dist (∫ x, U i x * ψ x ∂μ) (∫ x, u x * ψ x ∂μ) :=
      dist_triangle4_right _ _ _ _
    _ < ε := by
      have h₁ := (bounded_test_dist (hU i) (hBound i) hφ hψ).trans hError
      have h₂ := (bounded_test_dist hu hBoundLimit hφ hψ).trans hError
      linarith only [h₁, h₂, hi]

/-- Compactly supported smooth tests on the ambient finite-dimensional space
are L¹-dense for any measure finite on compact sets, including a restriction. -/
public theorem exists_smooth_compact_L1_test
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ν : Measure E} [IsFiniteMeasureOnCompacts ν]
    {φ : E → ℝ} (hφ : Integrable φ ν) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : E → ℝ, HasCompactSupport ψ ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) ψ ∧ Integrable ψ ν ∧
      (∫ x, ‖φ x - ψ x‖ ∂ν) ≤ ε := by
  have hLp := memLp_one_iff_integrable.mpr hφ
  obtain ⟨ψ, hψCompact, hψSmooth, hApprox⟩ :=
    hLp.exist_eLpNorm_sub_le ENNReal.one_ne_top le_rfl hε
  have hψ : Integrable ψ ν := hψSmooth.continuous.integrable_of_hasCompactSupport hψCompact
  refine ⟨ψ, hψCompact, hψSmooth, hψ, ?_⟩
  rw [eLpNorm_one_eq_lintegral_enorm (hφ.sub hψ).aestronglyMeasurable] at hApprox
  rw [← ofReal_integral_norm_eq_lintegral_enorm (hφ.sub hψ)] at hApprox
  exact (ENNReal.ofReal_le_ofReal_iff hε.le).mp hApprox


private theorem exists_smooth_cutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {C Ω : Set E} (hC : IsCompact C) (hΩ : IsOpen Ω) (h : C ⊆ Ω) :
    ∃ χ : E → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) χ ∧
      (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧ tsupport χ ⊆ Ω ∧ ∀ x ∈ C, χ x = 1 := by
  obtain ⟨V, hV, hCV, hClosure⟩ := normal_exists_closure_subset hC.isClosed hΩ h
  obtain ⟨χ, hSmooth, hRange, hSupp, hOne⟩ :=
    exists_contDiff_support_eq_eq_one_iff hV hC.isClosed hCV
  refine ⟨χ, hSmooth, fun x => hRange (mem_range_self x), ?_, fun x hx => (hOne x).mp hx⟩
  simpa only [tsupport, hSupp] using hClosure

/-- Interior smooth compactly supported tests are L¹-dense on the restriction
to an open subset of a finite-dimensional real normed space. -/
public theorem exists_interior_smooth_compact_L1_test
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ν : Measure E} [IsFiniteMeasureOnCompacts ν]
    {Ω : Set E} (hΩ : IsOpen Ω) {φ : E → ℝ} (hφ : Integrable φ (ν.restrict Ω))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : E → ℝ, HasCompactSupport ψ ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) ψ ∧ tsupport ψ ⊆ Ω ∧
      Integrable ψ (ν.restrict Ω) ∧ (∫ x in Ω, ‖φ x - ψ x‖ ∂ν) ≤ ε := by
  obtain ⟨g, hgCompact, hgSmooth, hg, hgApprox⟩ :=
    exists_smooth_compact_L1_test hφ (show 0 < ε / 2 by positivity)
  let _ : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  let C := CompactExhaustion.choice Ω
  have hCut (n : ℕ) :=
    exists_smooth_cutoff ((C.isCompact n).image continuous_subtype_val) hΩ
      (show Subtype.val '' (C n) ⊆ Ω from fun _ ⟨x, _, hx⟩ => hx ▸ x.2)
  choose χ χSmooth χRange χSupp χOne using hCut
  let g' (n : ℕ) (x : E) := χ n x * g x
  have hg'Smooth (n : ℕ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (g' n) :=
    (χSmooth n).mul hgSmooth
  have hg'Compact (n : ℕ) : HasCompactSupport (g' n) := hgCompact.mul_left
  have hg' (n : ℕ) : Integrable (g' n) (ν.restrict Ω) :=
    (hg'Smooth n).continuous.integrable_of_hasCompactSupport (hg'Compact n)
  have hError : Tendsto (fun n => ∫ x in Ω, ‖g x - g' n x‖ ∂ν) atTop (𝓝 0) := by
    have h : Tendsto (fun n => ∫ x in Ω, ‖g x - g' n x‖ ∂ν) atTop
        (𝓝 (∫ _ : E in Ω, (0 : ℝ) ∂ν)) := by
      apply tendsto_integral_of_dominated_convergence (fun x => ‖g x‖)
      · exact fun n => (hg.aestronglyMeasurable.sub (hg' n).aestronglyMeasurable).norm
      · exact hg.norm
      · intro n
        apply Eventually.of_forall
        intro x
        rw [norm_norm, show g x - g' n x = (1 - χ n x) * g x by
          simp only [g', sub_mul, one_mul]]
        rw [norm_mul, Real.norm_of_nonneg (sub_nonneg.mpr (χRange n x).2)]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (sub_le_self 1 (χRange n x).1) (norm_nonneg (g x))
      · filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
        obtain ⟨n, hn⟩ := C.exists_mem ⟨x, hx⟩
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop n] with i hi
        have hOne := χOne i x ⟨⟨x, hx⟩, C.subset hi hn, rfl⟩
        simp [g', hOne]
    simpa only [integral_zero] using h
  have hEventually : ∀ᶠ n in atTop, (∫ x in Ω, ‖g x - g' n x‖ ∂ν) < ε / 2 :=
    hError (eventually_lt_nhds (show 0 < ε / 2 by positivity))
  obtain ⟨n, hn⟩ := hEventually.exists
  refine ⟨g' n, hg'Compact n, hg'Smooth n, tsupport_mul_subset_left.trans (χSupp n), hg' n, ?_⟩
  calc
    _ ≤ ∫ x in Ω, ‖φ x - g x‖ + ‖g x - g' n x‖ ∂ν := by
      refine integral_mono (hφ.sub (hg' n)).norm
        ((hφ.sub hg).norm.add (hg.sub (hg' n)).norm) ?_
      intro x
      simpa only [← dist_eq_norm] using dist_triangle (φ x) (g x) (g' n x)
    _ = (∫ x in Ω, ‖φ x - g x‖ ∂ν) + (∫ x in Ω, ‖g x - g' n x‖ ∂ν) :=
      integral_add (hφ.sub hg).norm (hg.sub (hg' n)).norm
    _ ≤ ε := by linarith only [hgApprox, hn]


/-- Distributional convergence against interior smooth tests extends to all
L¹ tests on the open domain, under uniform L∞ bounds. -/
public theorem weakStar_of_interior_smooth_tests
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ν : Measure E} [IsFiniteMeasureOnCompacts ν]
    {Ω : Set E} (hΩ : IsOpen Ω) {l : Filter ι}
    {U : ι → E → ℝ} {u : E → ℝ} (B : ℝ) (hB : 0 ≤ B)
    (hU : ∀ i, AEStronglyMeasurable (U i) (ν.restrict Ω))
    (hu : AEStronglyMeasurable u (ν.restrict Ω))
    (hBound : ∀ i, ∀ᵐ x ∂ν.restrict Ω, ‖U i x‖ ≤ B)
    (hBoundLimit : ∀ᵐ x ∂ν.restrict Ω, ‖u x‖ ≤ B)
    (hTest : ∀ ψ : E → ℝ, HasCompactSupport ψ → ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
      tsupport ψ ⊆ Ω →
      Tendsto (fun i => ∫ x in Ω, U i x * ψ x ∂ν) l (𝓝 (∫ x in Ω, u x * ψ x ∂ν)))
    {φ : E → ℝ} (hφ : Integrable φ (ν.restrict Ω)) :
    Tendsto (fun i => ∫ x in Ω, U i x * φ x ∂ν) l (𝓝 (∫ x in Ω, u x * φ x ∂ν)) := by
  let T := {ψ : E → ℝ | HasCompactSupport ψ ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) ψ ∧ tsupport ψ ⊆ Ω}
  refine weakStar_of_dense_tests T B hB hU hu hBound hBoundLimit ?_ ?_ hφ
  · intro φ' hφ' ε hε
    obtain ⟨ψ, hCompact, hSmooth, hSupp, hψ, hError⟩ :=
      exists_interior_smooth_compact_L1_test hΩ hφ' hε
    exact ⟨ψ, ⟨hCompact, hSmooth, hSupp⟩, hψ, hError⟩
  · intro ψ hψ
    exact hTest ψ hψ.1 hψ.2.1 hψ.2.2

end C2Riemannian
