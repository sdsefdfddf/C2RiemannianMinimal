module

public import C2Riemannian.WeakMollificationLimit
public import C2Riemannian.WeakProducts

set_option autoImplicit false

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal Topology

namespace C2Riemannian.WeakJet2

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  {U V : Opens Plane} {f : Plane → F}

public theorem mollify_strongL2_of_bound (hVU : V ≤ U)
    [IsFiniteMeasure (volume.restrict (V : Set Plane))]
    (hf : MemLp f ∞ (volume.restrict (U : Set Plane)))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ x ∂volume.restrict (U : Set Plane), ‖f x‖ ≤ C)
    (φ : ℕ → ContDiffBump (0 : Plane))
    (hr : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    {K : ℝ} (hK : ∀ᶠ n in atTop, (φ n).rOut ≤ K * (φ n).rIn) :
    StrongL2 atTop (volume.restrict (V : Set Plane)) (fun n => mollify U (φ n) f) f := by
  have hm : volume.restrict (V : Set Plane) ≤ volume.restrict (U : Set Plane) :=
    Measure.restrict_mono hVU le_rfl
  refine ⟨fun n => ?_, ?_, ?_⟩
  · exact MemLp.of_bound (contDiff_mollify hf (by simp) (φ n)).continuous.aestronglyMeasurable C
      (Eventually.of_forall (norm_mollify_le hC hbound (φ n)))
  · exact MemLp.of_bound (hf.aestronglyMeasurable.mono_measure hm) C (ae_mono hm hbound)
  · simpa only [Real.rpow_two] using mollify_tendsto_integral_norm_sub_sq hVU hf hC hbound φ hr hK

/-- Every continuous linear projection of a bounded weak derivative field has
strong L² convergence for the same mollification sequence. -/
public theorem mollify_clm_strongL2_of_bound (hVU : V ≤ U)
    [IsFiniteMeasure (volume.restrict (V : Set Plane))]
    (hf : MemLp f ∞ (volume.restrict (U : Set Plane)))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ x ∂volume.restrict (U : Set Plane), ‖f x‖ ≤ C)
    (φ : ℕ → ContDiffBump (0 : Plane))
    (hr : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    {K : ℝ} (hK : ∀ᶠ n in atTop, (φ n).rOut ≤ K * (φ n).rIn)
    (L : F →L[ℝ] G) :
    StrongL2 atTop (volume.restrict (V : Set Plane)) (fun n x => L (mollify U (φ n) f x))
      (fun x => L (f x)) := by
  have h : ∀ᵐ x ∂volume.restrict (U : Set Plane), ‖L (f x)‖ ≤ ‖L‖ * C := by
    filter_upwards [hbound] with x hx
    exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
  have hstrong := mollify_strongL2_of_bound hVU (L.comp_memLp' hf)
    (mul_nonneg (norm_nonneg _) hC) h φ hr hK
  have heq (n : ℕ) : mollify U (φ n) (L ∘ f) = fun x => L (mollify U (φ n) f x) := by
    funext x
    exact mollify_clm hf (by simp) (φ n) L x
  simp only [Function.comp_def] at hstrong heq
  simpa only [heq] using hstrong

/-- A shrinking bump sequence with fixed outer-to-inner radius ratio two. -/
@[expose] public noncomputable def shrinkingBump (n : ℕ) : ContDiffBump (0 : Plane) :=
  let r : ℝ := ((n : ℝ) + 1)⁻¹
  have hr : 0 < r := inv_pos.mpr (by positivity)
  ⟨r, 2 * r, hr, by linarith only [hr]⟩

public theorem shrinkingBump_rOut_tendsto : Tendsto (fun n => (shrinkingBump n).rOut) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  simpa only [shrinkingBump, Function.comp_apply, mul_zero] using
    (tendsto_inv_atTop_zero.comp h).const_mul 2

public theorem shrinkingBump_ratio :
    ∀ᶠ n in atTop, (shrinkingBump n).rOut ≤ 2 * (shrinkingBump n).rIn :=
  Eventually.of_forall fun _ => le_rfl

end C2Riemannian.WeakJet2
