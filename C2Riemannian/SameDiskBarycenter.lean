module

public import C2Riemannian.SameDiskClosure
public import C2Riemannian.PhysicalBarycenter
public import C2Riemannian.HessianReadouts
import C2Riemannian.ConditionalRiesz
import Mathlib.Analysis.InnerProductSpace.Dual

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions NNReal Topology

namespace C2Riemannian.PhysicalLayerRow

set_option maxHeartbeats 500000 in
/-- The means of the two conditional laws recover a fixed linear projection
of the weak Hessian on the parent platform. -/
public theorem same_disk_projected_barycenter_ae
    {Q : Set Plane} {directions : PhysicalDirections} {s δ : ℝ} {layer : IdealLayer}
    {p : PhysicalPrefix Q} {next : ℕ → PhysicalPrefix Q}
    (row : PhysicalLayerRow directions s δ layer p next)
    (hn : directions.normal layer s ≠ 0)
    {m : ℕ} {a : Plane} {R K : ℝ≥0}
    {W : ℕ → WeakJet2 m (⟨Metric.ball a R, Metric.isOpen_ball⟩ : Opens Plane)}
    (C : WeakJet2.SameDiskLimit a R K W)
    (i : p.Active) (hP : p.platform i.1 ⊆ Metric.ball a R)
    (base σ : ℕ → ℕ) (hBase : StrictMono base) (hσ : StrictMono σ)
    (state : ℕ → Plane → HessianBall m K)
    (hState : ∀ j, Measurable (state j))
    (hEq : ∀ j, ∀ᵐ x ∂volume.restrict (Metric.ball a R),
      (state j x).val = ((C.normalized j).hessian x).coordinates)
    (L : Bool → Plane → PositiveFunctional (HessianBall m K))
    (hL : ∀ b (f : C(HessianBall m K, ℝ)), Measurable (fun x => L b x f))
    (hPair : ∀ b (f : C(HessianBall m K, ℝ)) (γ : Plane → ℝ),
      IntegrableOn γ (p.platform i.1) volume →
      Tendsto (fun j => ∫ x in p.platform i.1,
        row.phaseWeight i b (base (C.subseq (σ j))) x * f (state (C.subseq (σ j)) x) * γ x)
        atTop (𝓝 (∫ x in p.platform i.1, L b x f * γ x)))
    (A : HessSpace m →L[ℝ] Target m) :
    (fun x => A (C.limit.hessian x).coordinates) =ᵐ[volume.restrict (p.platform i.1)]
      (fun x => (1 / 2 : ℝ) • ((L true x).mean ⟨fun y => A y.val,
        A.continuous.comp continuous_subtype_val⟩ + (L false x).mean ⟨fun y => A y.val,
        A.continuous.comp continuous_subtype_val⟩)) := by
  classical
  let P := p.platform i.1
  let U : C(HessianBall m K, Target m) := ⟨fun y => A y.val,
    A.continuous.comp continuous_subtype_val⟩
  let _ : CompactSpace (HessianBall m K) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : HessSpace m) (K : ℝ))
  let _ : IsFiniteMeasure (volume.restrict P) :=
    isFiniteMeasure_restrict.mpr ((Metric.isBounded_ball (x := a) (r := (R : ℝ))).subset hP).measure_lt_top.ne
  have hμ := Measure.restrict_mono (μ := (volume : Measure Plane)) hP le_rfl
  have hborel : MeasurableSet P := (p.platform_open i.1).measurableSet
  have hCoord (l : Fin m) :
      (fun x => A (C.limit.hessian x).coordinates l) =ᵐ[volume.restrict P]
      (fun x => (L true x (PositiveFunctional.coord U l) +
        L false x (PositiveFunctional.coord U l)) / 2) := by
    let f := PositiveFunctional.coord U l
    let v := EuclideanSpace.single l (1 : ℝ)
    let d : HessSpace m →L[ℝ] ℝ := (innerSL ℝ v).comp A
    let e := (InnerProductSpace.toDual ℝ (HessSpace m)).symm d
    have he (H : HessSpace m) : inner ℝ H e = A H l := by
      rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
      change inner ℝ v (A H) = A H l
      simp [v, EuclideanSpace.inner_single_left]
    let u (j : ℕ) (x : Plane) := f (state (C.subseq (σ j)) x)
    let parent (x : Plane) := A (C.limit.hessian x).coordinates l
    have hpInt : LocallyIntegrableOn parent P volume := by
      have h := (d.comp (hessianColumns (m := m))).locallyIntegrableOn_comp
        C.limit.weak_gradient.locallyIntegrableOn_deriv
      have h' := h.mono_set (show P ⊆ Metric.ball a R from hP)
      have hd (H : HessSpace m) : d H = A H l := by
        change inner ℝ v (A H) = A H l
        simp [v, EuclideanSpace.inner_single_left]
      simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, hessianColumns_apply,
        WeakJet2.hessian, hd, parent] using h'
    have hLInt (b : Bool) : LocallyIntegrableOn (fun x => L b x f) P volume := by
      have h : IntegrableOn (fun x => L b x f) P volume :=
        Integrable.of_bound (hL b f).aestronglyMeasurable ‖f‖
          (Eventually.of_forall fun x => (L b x).norm_readout_le f)
      exact h.locallyIntegrableOn
    have hφint (φ : 𝓓(parentOpen p i, ℝ)) : Integrable (φ : Plane → ℝ) volume :=
      φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
    refine row.phase_barycenter_ae i hn (base ∘ C.subseq ∘ σ) (hBase.comp
      (C.strictMono_subseq.comp hσ)) u parent (fun x => L true x f) (fun x => L false x f)
      ‖f‖ hpInt (hLInt true) (hLInt false)
      (fun j => (f.continuous.measurable.comp (hState (C.subseq (σ j)))).aestronglyMeasurable)
      (fun j => Eventually.of_forall fun x => f.norm_coe_le_norm _) ?_ ?_ ?_
    · intro φ
      let γ := P.indicator (φ : Plane → ℝ)
      have hγ : IntegrableOn γ (Metric.ball a R) volume := ((hφint φ).indicator hborel).integrableOn
      have hInd (g : Plane → ℝ) : (∫ x in Metric.ball a R, g x * γ x) =
          ∫ x in P, g x * φ x := by
        rw [← inter_eq_right.mpr (show P ⊆ Metric.ball a R from hP), ← setIntegral_indicator hborel]
        apply integral_congr_ae
        filter_upwards with x
        by_cases hx : x ∈ P
        · simp only [γ, indicator_of_mem hx]
        · simp only [γ, indicator_of_notMem hx, mul_zero]
      have h := (C.hessian_weakStar e γ hγ).comp hσ.tendsto_atTop
      have h' : Tendsto (fun j => ∫ x in P, A ((C.normalized (C.subseq (σ j))).hessian x).coordinates l * φ x)
          atTop (𝓝 (∫ x in P, parent x * φ x)) := by
        simpa only [Function.comp_def, hInd, he, parent] using h
      rw [show (∫ x in P, φ x * parent x) = (∫ x in P, parent x * φ x) by simp only [mul_comm]]
      refine h'.congr' (Eventually.of_forall fun j => ?_)
      apply integral_congr_ae
      filter_upwards [MeasureTheory.ae_mono hμ (hEq (C.subseq (σ j)))] with x hx
      change A ((C.normalized (C.subseq (σ j))).hessian x).coordinates l * φ x =
        φ x * A (state (C.subseq (σ j)) x).val l
      rw [hx, mul_comm]
    · intro φ
      simpa only [u, Function.comp_def, mul_comm (L true _ f)] using
        hPair true f φ (hφint φ).integrableOn
    · intro φ
      simpa only [u, Function.comp_def, mul_comm (L false _ f)] using
        hPair false f φ (hφint φ).integrableOn
  filter_upwards [ae_all_iff.mpr hCoord] with x hx
  ext l
  change A (C.limit.hessian x).coordinates l =
    (1 / 2 : ℝ) * (L true x (PositiveFunctional.coord U l) + L false x (PositiveFunctional.coord U l))
  rw [hx l, div_eq_mul_inv, one_div, mul_comm]


/-- The weak Hessian entries equal the arithmetic average of their conditional means. -/
public theorem same_disk_hessian_barycenter_ae
    {Q : Set Plane} {directions : PhysicalDirections} {s δ : ℝ} {layer : IdealLayer}
    {p : PhysicalPrefix Q} {next : ℕ → PhysicalPrefix Q}
    (row : PhysicalLayerRow directions s δ layer p next)
    (hn : directions.normal layer s ≠ 0)
    {m : ℕ} {a : Plane} {R K : ℝ≥0}
    {W : ℕ → WeakJet2 m (⟨Metric.ball a R, Metric.isOpen_ball⟩ : Opens Plane)}
    (C : WeakJet2.SameDiskLimit a R K W)
    (i : p.Active) (hP : p.platform i.1 ⊆ Metric.ball a R)
    (base σ : ℕ → ℕ) (hBase : StrictMono base) (hσ : StrictMono σ)
    (state : ℕ → Plane → HessianBall m K)
    (hState : ∀ j, Measurable (state j))
    (hEq : ∀ j, ∀ᵐ x ∂volume.restrict (Metric.ball a R),
      (state j x).val = ((C.normalized j).hessian x).coordinates)
    (L : Bool → Plane → PositiveFunctional (HessianBall m K))
    (hL : ∀ b (f : C(HessianBall m K, ℝ)), Measurable (fun x => L b x f))
    (hPair : ∀ b (f : C(HessianBall m K, ℝ)) (γ : Plane → ℝ),
      IntegrableOn γ (p.platform i.1) volume →
      Tendsto (fun j => ∫ x in p.platform i.1,
        row.phaseWeight i b (base (C.subseq (σ j))) x * f (state (C.subseq (σ j)) x) * γ x)
        atTop (𝓝 (∫ x in p.platform i.1, L b x f * γ x))) :
    ∀ᵐ x ∂volume.restrict (p.platform i.1),
      (C.limit.hessian x).xx = (1 / 2 : ℝ) •
        ((L true x).mean HessianBall.xx + (L false x).mean HessianBall.xx) ∧
      (C.limit.hessian x).xy = (1 / 2 : ℝ) •
        ((L true x).mean HessianBall.xy + (L false x).mean HessianBall.xy) ∧
      (C.limit.hessian x).yy = (1 / 2 : ℝ) •
        ((L true x).mean HessianBall.yy + (L false x).mean HessianBall.yy) := by
  let fst := WithLp.fstL 2 ℝ (Target m) (WithLp 2 (Target m × Target m))
  let snd := WithLp.sndL 2 ℝ (Target m) (WithLp 2 (Target m × Target m))
  let mid : HessSpace m →L[ℝ] Target m :=
    (Real.sqrt 2)⁻¹ • (WithLp.fstL 2 ℝ (Target m) (Target m)).comp snd
  let last : HessSpace m →L[ℝ] Target m :=
    (WithLp.sndL 2 ℝ (Target m) (Target m)).comp snd
  have hFirst := row.same_disk_projected_barycenter_ae hn C i hP base σ hBase hσ state hState hEq L hL hPair fst
  have hMid := row.same_disk_projected_barycenter_ae hn C i hP base σ hBase hσ state hState hEq L hL hPair mid
  have hLast := row.same_disk_projected_barycenter_ae hn C i hP base σ hBase hσ state hState hEq L hL hPair last
  filter_upwards [hFirst, hMid, hLast] with x hx hy hz
  refine ⟨hx, ?_, hz⟩
  change (Real.sqrt 2)⁻¹ • (Real.sqrt 2 • (C.limit.hessian x).xy) =
    (1 / 2 : ℝ) • ((L true x).mean HessianBall.xy + (L false x).mean HessianBall.xy) at hy
  rwa [smul_smul, inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by norm_num)), one_smul] at hy

end C2Riemannian.PhysicalLayerRow
