module

public import C2Riemannian.MollifiedGradientBounds
public import C2Riemannian.WeakMollificationStrong
public import C2Riemannian.DerivativeLimit
import C2Riemannian.CompactDiskConvergence
import C2Riemannian.StrongL2Uniqueness
import C2Riemannian.WeakTestConvergence
import Mathlib.Topology.MetricSpace.Thickening

/-! # Classical representatives obtained from interior mollification (M03) -/

set_option autoImplicit false

open Filter Set MeasureTheory TopologicalSpace
open scoped Topology NNReal ENNReal

namespace C2Riemannian.WeakJet2

variable {m : ℕ} {U V : Opens Plane}

/-- The limit of uniformly convergent mollifications represents the original
essentially bounded field on the target open set. -/
private theorem ae_eq_of_uniform_mollify
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f g : Plane → E} (hVU : V ≤ U) (hV : volume (V : Set Plane) ≠ ∞)
    (hf : MemLp f ∞ (volume.restrict (U : Set Plane)))
    {C : ℝ} (hC : 0 ≤ C) (hB : ∀ᵐ x ∂volume.restrict (U : Set Plane), ‖f x‖ ≤ C)
    (φ : ℕ → ContDiffBump (0 : Plane))
    (hzero : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    (hratio : ∀ᶠ n in atTop, (φ n).rOut ≤ 2 * (φ n).rIn)
    (hg : ContinuousOn g (V : Set Plane))
    (hUnif : TendstoUniformlyOn (fun n => mollify U (φ n) f) g atTop (V : Set Plane)) :
    g =ᵐ[volume.restrict (V : Set Plane)] f := by
  let _ : IsFiniteMeasure (volume.restrict (V : Set Plane)) := isFiniteMeasure_restrict.mpr hV
  have hBound n x : ‖mollify U (φ n) f x‖ ≤ C := norm_mollify_le hC hB (φ n) x
  have hgBound (x : Plane) (hx : x ∈ (V : Set Plane)) : ‖g x‖ ≤ C :=
    le_of_tendsto ((hUnif.tendsto_at hx).norm) (Eventually.of_forall fun n => hBound n x)
  have hgStrong := strongL2_of_uniformOn (μ := volume) V.isOpen.measurableSet hV
    (fun n => (contDiff_mollify hf (by simp) (φ n)).continuous.aestronglyMeasurable)
    (hg.aestronglyMeasurable V.isOpen.measurableSet) C (fun n x _ => hBound n x) hgBound hUnif
  have hfStrong := mollify_strongL2_of_bound hVU hf hC hB φ hzero hratio
  exact hgStrong.ae_eq hfStrong

/-- A locally interior convex compact set supplies a common uniformly
converging mollification subsequence. On its open subset the limits form a
classical first jet and represent the original weak fields. -/
public theorem exists_classical_representative_on_compact (w : WeakJet2 m U)
    {s : Set Plane} (hs : IsCompact s) (hConvex : Convex ℝ s)
    (hU : s ⊆ (U : Set Plane)) (hVs : (V : Set Plane) ⊆ s)
    (hw : MemLp w.value ∞ (volume.restrict (U : Set Plane)))
    (hP : MemLp w.gradient ∞ (volume.restrict (U : Set Plane)))
    (hB : MemLp w.second ∞ (volume.restrict (U : Set Plane)))
    (M₀ M₁ K : ℝ≥0)
    (hValue : ∀ᵐ x ∂volume.restrict (U : Set Plane), ‖w.value x‖ ≤ (M₀ : ℝ))
    (hGradient : ∀ᵐ x ∂volume.restrict (U : Set Plane), gradHS (w.gradient x) ≤ (M₁ : ℝ))
    (hHessian : ∀ᵐ x ∂volume.restrict (U : Set Plane), (w.hessian x).frobenius ≤ (K : ℝ)) :
    ∃ (W : Plane → Target m) (P : Plane → Plane →L[ℝ] Target m),
      ContDiffOn ℝ 1 W (V : Set Plane) ∧
      (∀ x ∈ (V : Set Plane), HasFDerivAt W (P x) x) ∧
      (∀ x ∈ s, ∀ y ∈ s, gradHS (P x - P y) ≤ (K : ℝ) * dist x y) ∧
      W =ᵐ[volume.restrict (V : Set Plane)] w.value ∧
      P =ᵐ[volume.restrict (V : Set Plane)] w.gradient := by
  classical
  have hVU : V ≤ U := hVs.trans hU
  have hFinite : volume (V : Set Plane) ≠ ∞ :=
    ((measure_mono hVs).trans_lt hs.measure_lt_top).ne
  obtain ⟨δ, hδ, hδU⟩ := hs.exists_cthickening_subset_open U.isOpen hU
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((Metric.tendsto_nhds.mp shrinkingBump_rOut_tendsto) δ hδ)
  let φ (n : ℕ) := shrinkingBump (n + N)
  have hRoom (n : ℕ) (x : Plane) (hx : x ∈ s) :
      Metric.closedBall x (φ n).rOut ⊆ (U : Set Plane) := by
    have hNn := hN (n + N) (Nat.le_add_left N n)
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (shrinkingBump (n + N)).rOut_pos.le] at hNn
    exact (Metric.closedBall_subset_closedBall hNn.le).trans
      ((Metric.closedBall_subset_cthickening hx δ).trans hδU)
  let F (n : ℕ) (x : s) := (mollify U (φ n) w.value x.1, mollify U (φ n) w.gradient x.1)
  let L : ℝ≥0 := max M₁ K
  let R : ℝ := max (M₀ : ℝ) (M₁ : ℝ)
  have hOp : ∀ᵐ x ∂volume.restrict (U : Set Plane), ‖w.gradient x‖ ≤ (M₁ : ℝ) :=
    hGradient.mono fun x hx => (opNorm_le_gradHS _).trans hx
  have hLip (n : ℕ) : LipschitzWith L (F n) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Prod.dist_eq]
    apply max_le
    · exact (w.dist_mollify_value_le hw hP (by simp) (by simp) M₁.coe_nonneg hGradient
        (φ n) hConvex (hRoom n) x.2 y.2).trans
        (mul_le_mul_of_nonneg_right (le_max_left (M₁ : ℝ) (K : ℝ)) dist_nonneg)
    · rw [dist_eq_norm]
      exact (opNorm_le_gradHS _).trans
        ((w.gradHS_mollify_gradient_sub_le hP hB (by simp) (by simp) K.coe_nonneg hHessian
          (φ n) hConvex (hRoom n) x.2 y.2).trans
          (mul_le_mul_of_nonneg_right (le_max_right (M₁ : ℝ) (K : ℝ)) dist_nonneg))
  have hBound (n : ℕ) (x : s) : ‖F n x‖ ≤ R := by
    rw [Prod.norm_def]
    exact max_le ((norm_mollify_le M₀.coe_nonneg hValue (φ n) x).trans (le_max_left _ _))
      ((norm_mollify_le M₁.coe_nonneg hOp (φ n) x).trans (le_max_right _ _))
  obtain ⟨g, k, hk, _, _, hUniform⟩ :=
    compact_set_bounded_lipschitz_subsequence hs L R F hLip hBound
  let W (x : Plane) := if hx : x ∈ s then (g ⟨x, hx⟩).1 else 0
  let P (x : Plane) := if hx : x ∈ s then (g ⟨x, hx⟩).2 else 0
  let ψ (n : ℕ) := φ (k n)
  have hUnif :
      TendstoUniformlyOn (fun n x => (mollify U (ψ n) w.value x, mollify U (ψ n) w.gradient x))
        (fun x => (W x, P x)) atTop s := by
    intro u hu
    exact (hUniform u hu).mono fun n hn x hx => by
      simpa only [W, P, dite_eq_left hx, F, ψ] using hn ⟨x, hx⟩
  have hUnifW : TendstoUniformlyOn (fun n => mollify U (ψ n) w.value) W atTop s :=
    Metric.tendstoUniformlyOn_iff.mpr fun ε hε =>
      ((Metric.tendstoUniformlyOn_iff.mp hUnif) ε hε).mono fun _ hn x hx =>
        (le_max_left _ _).trans_lt (hn x hx)
  have hUnifP : TendstoUniformlyOn (fun n => mollify U (ψ n) w.gradient) P atTop s :=
    Metric.tendstoUniformlyOn_iff.mpr fun ε hε =>
      ((Metric.tendstoUniformlyOn_iff.mp hUnif) ε hε).mono fun _ hn x hx =>
        (le_max_right _ _).trans_lt (hn x hx)
  have hPW : ∀ n x, x ∈ (V : Set Plane) →
      HasFDerivAt (mollify U (ψ n) w.value) (mollify U (ψ n) w.gradient x) x :=
    fun n x hx => (w.mollify_derivatives hw hP hB (by simp) (by simp) (by simp)
      (ψ n) x (hRoom (k n) x (hVs hx))).1
  obtain ⟨hC1, hDerivative⟩ := contDiffOn_one_of_locally_uniform_derivatives V.isOpen hPW
    (fun n => (contDiff_mollify hP (by simp) (ψ n)).continuous.continuousOn)
    (fun _ hx => hUnifW.tendsto_at (hVs hx)) (hUnifP.mono hVs).tendstoLocallyUniformlyOn
  have hContP : ContinuousOn P (V : Set Plane) :=
    (hUnifP.mono hVs).continuousOn
      (Eventually.of_forall (fun n =>
        (contDiff_mollify hP (by simp) (ψ n)).continuous.continuousOn)).frequently
  have hψTop : Tendsto (fun n => k n + N) atTop atTop :=
    (tendsto_add_atTop_nat N).comp hk.tendsto_atTop
  have hψzero : Tendsto (fun n => (ψ n).rOut) atTop (𝓝 0) :=
    shrinkingBump_rOut_tendsto.comp hψTop
  have hψratio : ∀ᶠ n in atTop, (ψ n).rOut ≤ 2 * (ψ n).rIn :=
    hψTop.eventually shrinkingBump_ratio
  refine ⟨W, P, hC1, hDerivative, ?_, ?_, ?_⟩
  · intro x hx y hy
    rw [← norm_gradientColumns, map_sub]
    have hLim := (gradientColumns.continuous.continuousAt.tendsto.comp (hUnifP.tendsto_at hx)).sub
      (gradientColumns.continuous.continuousAt.tendsto.comp (hUnifP.tendsto_at hy))
    apply le_of_tendsto hLim.norm
    filter_upwards with n
    rw [Function.comp_apply, Function.comp_apply, ← map_sub, norm_gradientColumns]
    exact w.gradHS_mollify_gradient_sub_le hP hB (by simp) (by simp) K.coe_nonneg hHessian
      (ψ n) hConvex (hRoom (k n)) hx hy
  · exact ae_eq_of_uniform_mollify hVU hFinite hw M₀.coe_nonneg hValue ψ hψzero hψratio
      hC1.continuousOn (hUnifW.mono hVs)
  · exact ae_eq_of_uniform_mollify hVU hFinite hP M₁.coe_nonneg hOp ψ hψzero hψratio
      hContP (hUnifP.mono hVs)

/-- The first jet representative on an open ball whose closure lies in the
domain retains the underlying Hessian's Hilbert–Schmidt Lipschitz constant. -/
public theorem exists_classical_representative_on_ball (w : WeakJet2 m U)
    (a : Plane) (r : ℝ) (hU : Metric.closedBall a r ⊆ (U : Set Plane))
    (hw : MemLp w.value ∞ (volume.restrict (U : Set Plane)))
    (hP : MemLp w.gradient ∞ (volume.restrict (U : Set Plane)))
    (hB : MemLp w.second ∞ (volume.restrict (U : Set Plane)))
    (M₀ M₁ K : ℝ≥0)
    (hValue : ∀ᵐ x ∂volume.restrict (U : Set Plane), ‖w.value x‖ ≤ (M₀ : ℝ))
    (hGradient : ∀ᵐ x ∂volume.restrict (U : Set Plane), gradHS (w.gradient x) ≤ (M₁ : ℝ))
    (hHessian : ∀ᵐ x ∂volume.restrict (U : Set Plane), (w.hessian x).frobenius ≤ (K : ℝ)) :
    ∃ (W : Plane → Target m) (P : Plane → Plane →L[ℝ] Target m),
      ContDiffOn ℝ 1 W (Metric.ball a r) ∧
      (∀ x ∈ Metric.ball a r, HasFDerivAt W (P x) x) ∧
      (∀ x ∈ Metric.closedBall a r, ∀ y ∈ Metric.closedBall a r,
        gradHS (P x - P y) ≤ (K : ℝ) * dist x y) ∧
      W =ᵐ[volume.restrict (Metric.ball a r)] w.value ∧
      P =ᵐ[volume.restrict (Metric.ball a r)] w.gradient :=
  w.exists_classical_representative_on_compact
    (V := ⟨Metric.ball a r, Metric.isOpen_ball⟩)
    (isCompact_closedBall a r) (convex_closedBall a r) hU Metric.ball_subset_closedBall
    hw hP hB M₀ M₁ K hValue hGradient hHessian

end C2Riemannian.WeakJet2
