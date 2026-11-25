module

public import C2Riemannian.WeakAnalysis
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

set_option autoImplicit false

open MeasureTheory Set Filter TopologicalSpace
open scoped ContDiff Distributions Topology NNReal

namespace C2Riemannian

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace F]
variable {U : Opens Plane} {f : Plane → F}

private theorem locallyIntegrableOn_fderiv_of_locallyLipschitz
    (hf : LocallyLipschitzOn (U : Set Plane) f) :
    LocallyIntegrableOn (fderiv ℝ f) U volume := by
  let : MeasurableSpace (Plane →L[ℝ] F) := borel _
  let : BorelSpace (Plane →L[ℝ] F) := ⟨rfl⟩
  intro x hx
  obtain ⟨L, t, ht, hL⟩ := hf hx
  have ht' : t ∈ 𝓝 x := (U.isOpen.nhdsWithin_eq hx) ▸ ht
  obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.1 ht'
  let s := Metric.closedBall x (r / 2)
  have hsball : s ⊆ Metric.ball x r := Metric.closedBall_subset_ball (half_lt_self hr)
  have hsm : MeasurableSet s := Metric.isClosed_closedBall.measurableSet
  have : IsFiniteMeasure ((volume : Measure Plane).restrict s) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
        exact (isCompact_closedBall _ _).measure_lt_top⟩
  refine ⟨s, nhdsWithin_le_nhds (Metric.closedBall_mem_nhds _ (half_pos hr)), ?_⟩
  apply memLp_one_iff_integrable.mp
  apply MemLp.of_bound (measurable_fderiv ℝ f).aestronglyMeasurable (L : ℝ)
  rw [ae_restrict_iff' hsm]
  exact Eventually.of_forall fun y hy =>
    norm_fderiv_le_of_lipschitzOn ℝ (mem_of_superset (Metric.isOpen_ball.mem_nhds (hsball hy)) hrt) hL

private theorem weak_integral_of_locallyLipschitz
    (hf : LocallyLipschitzOn (U : Set Plane) f)
    (v : Plane) (φ : 𝓓(U, ℝ)) :
    (∫ x, lineDeriv ℝ (φ : Plane → ℝ) x v • f x) =
      -∫ x, φ x • fderiv ℝ f x v := by
  have hfi : LocallyIntegrableOn f U volume :=
    hf.continuousOn.locallyIntegrableOn U.isOpen.measurableSet
  have hdi : LocallyIntegrableOn (fun x => fderiv ℝ f x v) U volume :=
    (ContinuousLinearMap.apply ℝ F v).locallyIntegrableOn_comp
      (locallyIntegrableOn_fderiv_of_locallyLipschitz hf)
  have hleft := TauCeti.integrable_lineDeriv_smul_of_locallyIntegrableOn hfi φ v
  have hright := TauCeti.integrable_smul_of_locallyIntegrableOn hdi φ
  obtain ⟨δ, hδ, hsub⟩ := φ.hasCompactSupport.exists_cthickening_subset_open
    U.isOpen φ.tsupport_subset
  let K := Metric.cthickening δ (tsupport (φ : Plane → ℝ))
  have hK : IsCompact K := φ.hasCompactSupport.cthickening
  obtain ⟨L, hL⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK (hf.mono hsub)
  obtain ⟨g, hg, heq⟩ := hL.extend_finite_dimension
  have hnear {x : Plane} (hx : x ∈ tsupport (φ : Plane → ℝ)) : f =ᶠ[𝓝 x] g :=
    (show ∀ᶠ y in 𝓝 x, y ∈ Metric.closedBall x δ from Metric.closedBall_mem_nhds x hδ).mono fun y hy =>
      heq (Metric.closedBall_subset_cthickening hx δ hy)
  have hae : ∀ᵐ x ∂(volume : Measure Plane), DifferentiableAt ℝ g x := hg.ae_differentiableAt
  have hφd := φ.contDiff.differentiable (by simp)
  obtain ⟨D, hφlip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    φ.hasCompactSupport φ.contDiff (by simp)
  let A := ∫ x, lineDeriv ℝ (φ : Plane → ℝ) x v • f x
  let B := ∫ x, φ x • fderiv ℝ f x v
  have hdual (ℓ : F →L[ℝ] ℝ) : ℓ A = -ℓ B := by
    rw [← ℓ.integral_comp_comm hleft, ← ℓ.integral_comp_comm hright]
    simp only [map_smul, smul_eq_mul]
    let k : Plane → ℝ := fun x => ℓ (g x)
    have hk : LipschitzWith (‖ℓ‖₊ * _) k := ℓ.lipschitzWith.comp hg
    have hscalar := hk.integral_lineDeriv_mul_eq (μ := volume) hφlip φ.hasCompactSupport v
    have hminus (x : Plane) : lineDeriv ℝ (φ : Plane → ℝ) x (-v) =
        -lineDeriv ℝ (φ : Plane → ℝ) x v := by
      rw [(hφd x).lineDeriv_eq_fderiv, (hφd x).lineDeriv_eq_fderiv, map_neg]
    have h₁ : (∫ x, lineDeriv ℝ (φ : Plane → ℝ) x v * ℓ (f x)) =
        ∫ x, lineDeriv ℝ (φ : Plane → ℝ) x v * k x := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ tsupport (φ : Plane → ℝ)
      · exact congrArg (lineDeriv ℝ (φ : Plane → ℝ) x v * ·)
          (congrArg ℓ (hnear hx).eq_of_nhds)
      · simp only [TauCeti.lineDeriv_eq_zero_of_notMem_tsupport φ hx v, zero_mul]
    have h₂ : (∫ x, φ x * ℓ (fderiv ℝ f x v)) =
        ∫ x, lineDeriv ℝ k x v * φ x := by
      apply integral_congr_ae
      filter_upwards [hae] with x hdx
      by_cases hx : x ∈ tsupport (φ : Plane → ℝ)
      · have hd := ((ℓ.hasFDerivAt.comp x hdx.hasFDerivAt).hasLineDerivAt v).lineDeriv
        change lineDeriv ℝ k x v = ℓ (fderiv ℝ g x v) at hd
        change φ x * ℓ (fderiv ℝ f x v) = lineDeriv ℝ k x v * φ x
        rw [(hnear hx).fderiv_eq, hd, mul_comm]
      · have hz := image_eq_zero_of_notMem_tsupport hx
        change φ x * ℓ (fderiv ℝ f x v) = lineDeriv ℝ k x v * φ x
        rw [hz, zero_mul, mul_zero]
    rw [h₁, h₂]
    simp_rw [hminus, neg_mul, integral_neg] at hscalar
    rw [hscalar, neg_neg]
  have hab : A + B = 0 := by
    by_contra hn
    obtain ⟨ℓ, _, hℓ⟩ := exists_dual_vector ℝ (A + B) (norm_ne_zero_iff.mpr hn)
    rw [map_add, hdual, neg_add_cancel] at hℓ
    exact hn (norm_eq_zero.mp hℓ.symm)
  exact eq_neg_of_add_eq_zero_left hab

omit [CompleteSpace F] in
/-- Local Rademacher differentiability for finite-dimensional fields on an open set. -/
public theorem ae_differentiableAt_of_locallyLipschitzOn
    (hf : LocallyLipschitzOn (U : Set Plane) f) :
    ∀ᵐ x ∂volume.restrict (U : Set Plane), DifferentiableAt ℝ f x := by
  have hball (x : U) : ∃ r : ℝ, 0 < r ∧ Metric.ball (x : Plane) r ⊆ (U : Set Plane) ∧
      ∃ L : ℝ≥0, LipschitzOnWith L f (Metric.ball (x : Plane) r) := by
    obtain ⟨L, s, hsn, hL⟩ := hf x.property
    have hsn' : s ∈ 𝓝 (x : Plane) := (U.isOpen.nhdsWithin_eq x.property) ▸ hsn
    obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.1 (inter_mem hsn' (U.isOpen.mem_nhds x.property))
    exact ⟨r, hr, fun _ hy => (hb hy).2, L, hL.mono (fun _ hy => (hb hy).1)⟩
  choose rad hr hsub L hL using hball
  let ball (x : U) := Metric.ball (x : Plane) (rad x)
  obtain ⟨J, hJ, hunion⟩ := isOpen_iUnion_countable ball (fun _ => Metric.isOpen_ball)
  have heq : (U : Set Plane) = ⋃ x ∈ J, ball x := by
    rw [hunion]
    exact Subset.antisymm (fun x hx => mem_iUnion_of_mem ⟨x, hx⟩ (Metric.mem_ball_self (hr ⟨x, hx⟩)))
      (iUnion_subset hsub)
  rw [heq, ae_restrict_biUnion_iff ball hJ]
  intro x _
  have hdiff := (hL x).ae_differentiableWithinAt (μ := volume) Metric.isOpen_ball.measurableSet
  filter_upwards [hdiff, ae_restrict_mem (μ := volume) Metric.isOpen_ball.measurableSet] with y hy hyball
  exact hy.differentiableAt (Metric.isOpen_ball.mem_nhds hyball)

/-- A locally Lipschitz finite-dimensional field has its classical Fréchet derivative
as a weak derivative on an open set. -/
public theorem hasWeakFDerivOn_of_locallyLipschitz
    (hf : LocallyLipschitzOn (U : Set Plane) f) :
    TauCeti.HasWeakFDerivOn volume U f (fderiv ℝ f) := by
  apply TauCeti.hasWeakFDerivOn_iff.mpr
  intro v
  apply TauCeti.hasWeakLineDerivOn_iff_testFunction.mpr
  exact ⟨inferInstance, hf.continuousOn.locallyIntegrableOn U.isOpen.measurableSet,
    (ContinuousLinearMap.apply ℝ F v).locallyIntegrableOn_comp
      (locallyIntegrableOn_fderiv_of_locallyLipschitz hf),
    weak_integral_of_locallyLipschitz hf v⟩

/-- The weak second jet of a (C^1) potential with locally Lipschitz classical gradient. -/
@[expose] public noncomputable def weakJet2_of_contDiffOn_locallyLipschitz {m : ℕ}
    {W : Plane → Target m} (hW : ContDiffOn ℝ 1 W U)
    (hP : LocallyLipschitzOn (U : Set Plane) (fderiv ℝ W)) : WeakJet2 m U where
  value := W
  gradient := fderiv ℝ W
  second := fderiv ℝ (fderiv ℝ W)
  weak_value := TauCeti.hasWeakFDerivOn_of_differentiableOn
    (hW.continuousOn.locallyIntegrableOn U.isOpen.measurableSet)
    (hP.continuousOn.locallyIntegrableOn U.isOpen.measurableSet)
    (fun x hx => (hW.differentiableOn (by decide) x hx).differentiableAt (U.isOpen.mem_nhds hx))
  weak_gradient := hasWeakFDerivOn_of_locallyLipschitz hP

end C2Riemannian





