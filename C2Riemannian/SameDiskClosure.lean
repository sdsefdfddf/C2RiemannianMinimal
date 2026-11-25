module

public import C2Riemannian.CurvatureWeakStar
public import C2Riemannian.DomainTestClosure
public import C2Riemannian.HessianTestLimit
public import C2Riemannian.NormalizedCompactness
public import C2Riemannian.BoundedDiskNormalization
public import C2Riemannian.ClassicalJetBounds
public import C2Riemannian.HessianWeakStar
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Topology Distributions NNReal ENNReal

namespace C2Riemannian.WeakJet2

variable {m : ℕ} {U : Opens Plane}

/-- The source equation is closed along compact-uniform gradient convergence
on a fixed finite-measure open domain. The limiting weak jet and its bounds are
given, and the prescribed sources converge against smooth interior tests. -/
public theorem source_eq_of_same_domain_gradient_limit
    [IsFiniteMeasure (volume.restrict (U : Set Plane))]
    {W : ℕ → WeakJet2 m U} {w : WeakJet2 m U} {F : ℕ → Plane → ℝ} {f : Plane → ℝ}
    {P H K : ℝ} (hP : 0 ≤ P) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hW : ∀ n, CurvatureBounds (W n) P H K) (hw : CurvatureBounds w P H K)
    (hUniform : ∀ s : Set Plane, s ⊆ (U : Set Plane) → IsCompact s →
      TendstoUniformlyOn (fun n => (W n).gradient) w.gradient atTop s)
    (hEq : ∀ᶠ n in atTop, (fun x => ((W n).hessian x).q) =ᵐ[volume.restrict (U : Set Plane)] F n)
    (hf : LocallyIntegrableOn f U volume)
    (hSource : ∀ φ : 𝓓(U, ℝ), Tendsto (fun n => ∫ x in ↑U, φ x • F n x) atTop
      (𝓝 (∫ x in ↑U, φ x • f x))) :
    (fun x => (w.hessian x).q) =ᵐ[volume.restrict (U : Set Plane)] f := by
  let μ := volume.restrict (U : Set Plane)
  have hc := w.second_eval_memLp_of_bound hw.second_mem.aestronglyMeasurable hw.second_bound
  have hq : Integrable (fun x => (w.hessian x).q) μ :=
    (integrable_weak_inner (hc ex ex) (hc ey ey)).sub
      (integrable_weak_inner (hc ex ey) (hc ex ey))
  have hq' : IntegrableOn (fun x => (w.hessian x).q) (U : Set Plane) volume := hq
  refine ae_eq_of_same_domain_test_limits hq'.locallyIntegrableOn hf hEq ?_ hSource
  intro φ
  have hφ : Integrable (φ : Plane → ℝ) μ :=
    φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hTest := curvature_weakStar_of_gradient_locally_uniform hP hH hK hW hw hUniform hφ
  simpa only [smul_eq_mul, mul_comm] using hTest

/-- Same-disk closure along a chosen compact-uniform gradient subsequence.
For locally uniformly convergent bounded sources, the smooth test convergence
is supplied by the compact-support test theorem. -/
public theorem source_eq_of_disk_subsequence
    {a : Plane} {R : ℝ}
    [IsFiniteMeasure (volume.restrict (Metric.ball a R))]
    {W : ℕ → WeakJet2 m ⟨Metric.ball a R, Metric.isOpen_ball⟩}
    {w : WeakJet2 m ⟨Metric.ball a R, Metric.isOpen_ball⟩}
    {F : ℕ → Plane → ℝ} {f : Plane → ℝ}
    {P H K M : ℝ} (hP : 0 ≤ P) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hW : ∀ n, CurvatureBounds (W n) P H K) (hw : CurvatureBounds w P H K)
    (k : ℕ → ℕ) (hk : StrictMono k)
    (hGradient : ∀ j, TendstoUniformlyOn (fun n => (W (k n)).gradient) w.gradient atTop
      (diskExhaustion a R j))
    (hEq : ∀ n, (fun x => ((W n).hessian x).q) =ᵐ[volume.restrict (Metric.ball a R)] F n)
    (hf : LocallyIntegrableOn f (Metric.ball a R) volume)
    (hF : ∀ n, LocallyIntegrableOn (F n) (Metric.ball a R) volume)
    (hBound : ∀ n x, x ∈ Metric.ball a R → ‖F n x‖ ≤ M)
    (hSource : ∀ j, TendstoUniformlyOn F f atTop (diskExhaustion a R j)) :
    (fun x => (w.hessian x).q) =ᵐ[volume.restrict (Metric.ball a R)] f := by
  let D : Opens Plane := ⟨Metric.ball a R, Metric.isOpen_ball⟩
  refine source_eq_of_same_domain_gradient_limit (U := D) (W := fun n => W (k n))
    hP hH hK (fun n => hW (k n)) hw ?_
    (Eventually.of_forall fun n => hEq (k n)) hf ?_
  · intro s hSub hCompact
    obtain ⟨j, hj⟩ := diskExhaustion_covers_compacts a R s hSub hCompact
    exact (hGradient j).mono hj
  · intro φ
    obtain ⟨j, hj⟩ := diskExhaustion_covers_compacts a R _ φ.tsupport_subset φ.hasCompactSupport
    exact (tendsto_smul_test_of_uniformOn φ hF
      (fun n x hx => hBound n x (φ.tsupport_subset hx)) ((hSource j).mono hj)).comp hk.tendsto_atTop


/-- A common compact-uniform limit of the normalized jets on a disk, with
the exact Hessian bound and both weak-star limits. -/
public structure SameDiskLimit (a : Plane) (R K : ℝ≥0)
    (W : ℕ → WeakJet2 m (⟨Metric.ball a R, Metric.isOpen_ball⟩ : Opens Plane)) where
  normalized : ℕ → WeakJet2 m (⟨Metric.ball a R, Metric.isOpen_ball⟩ : Opens Plane)
  limit : WeakJet2 m (⟨Metric.ball a R, Metric.isOpen_ball⟩ : Opens Plane)
  subseq : ℕ → ℕ
  strictMono_subseq : StrictMono subseq
  normalized_data : ∀ n, (normalized n).second = (W n).second ∧
    (normalized n).hessian = (W n).hessian ∧
    (normalized n).gradient = fderiv ℝ (normalized n).value ∧
    (normalized n).value a = 0 ∧ (normalized n).gradient a = 0
  normalized_gradient_continuous : ∀ n, ContinuousOn (normalized n).gradient (Metric.ball a R)
  value_center : limit.value a = 0
  gradient_center : limit.gradient a = 0
  contDiffOn_limit : ContDiffOn ℝ 1 limit.value (Metric.ball a R)
  gradient_eq_fderiv : limit.gradient = fderiv ℝ limit.value
  gradient_hs_le : ∀ x ∈ Metric.ball a R, ∀ y ∈ Metric.ball a R,
    gradHS (limit.gradient x - limit.gradient y) ≤ (K : ℝ) * dist x y
  value_convergence : ∀ j, TendstoUniformlyOn (fun n => (normalized (subseq n)).value)
    limit.value atTop (diskExhaustion a R j)
  gradient_convergence : ∀ j, TendstoUniformlyOn (fun n => (normalized (subseq n)).gradient)
    limit.gradient atTop (diskExhaustion a R j)
  bounds : CurvatureBounds limit ((K : ℝ) * R) K K
  hessian_weakStar : ∀ (e : HessSpace m) (φ : Plane → ℝ), IntegrableOn φ (Metric.ball a R) volume →
    Tendsto (fun n => ∫ x in Metric.ball a R,
      inner ℝ ((normalized (subseq n)).hessian x).coordinates e * φ x) atTop
      (𝓝 (∫ x in Metric.ball a R, inner ℝ (limit.hessian x).coordinates e * φ x))
  curvature_weakStar : ∀ φ : Plane → ℝ, IntegrableOn φ (Metric.ball a R) volume →
    Tendsto (fun n => ∫ x in Metric.ball a R, ((normalized (subseq n)).hessian x).q * φ x)
      atTop (𝓝 (∫ x in Metric.ball a R, (limit.hessian x).q * φ x))

set_option maxHeartbeats 650000 in
/-- Weak second jets with a common Frobenius bound on one disk have a common
subsequence after affine normalization, with compact-uniform and weak-star convergence. -/
public theorem exists_same_disk_compact_limit
    (hm : 0 < m) (a : Plane) (R K : ℝ≥0) (hR : 0 < R)
    (W : ℕ → WeakJet2 m (⟨Metric.ball a R, Metric.isOpen_ball⟩ : Opens Plane))
    (hValueMem : ∀ n j, MemLp (W n).value ∞ (volume.restrict (openDiskExhaustion a R j : Set Plane)))
    (hGradientMem : ∀ n j, MemLp (W n).gradient ∞
      (volume.restrict (openDiskExhaustion a R j : Set Plane)))
    (hFrobenius : ∀ n, ∀ᵐ x ∂volume.restrict (Metric.ball a R),
      ((W n).hessian x).frobenius ≤ (K : ℝ)) :
    Nonempty (SameDiskLimit a R K W) := by
  let U : Opens Plane := ⟨Metric.ball a R, Metric.isOpen_ball⟩
  let μ := volume.restrict (U : Set Plane)
  let _ : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.mpr
      (((measure_mono Metric.ball_subset_closedBall).trans_lt (isCompact_closedBall a R).measure_lt_top).ne)
  have ha : a ∈ (U : Set Plane) := Metric.mem_ball_self (by exact_mod_cast hR)
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hRadius (x : Plane) (hx : x ∈ (U : Set Plane)) : dist x a ≤ R :=
    (Metric.mem_ball.mp hx).le
  have hConvex : Convex ℝ (U : Set Plane) := convex_ball a R
  have hNormalize (n : ℕ) := exists_normalized_locally_bounded_disk_weakJet a R hR' (W n) K
    (hValueMem n) (hGradientMem n) (hFrobenius n)
  choose V hVGrad hVSecond hVHess hVC1 hVZero hVGradZero hVBound hVGradBound hVHS
    using hNormalize
  have hVDiff (n : ℕ) (x : Plane) (hx : x ∈ (U : Set Plane)) :
      DifferentiableAt ℝ (V n).value x :=
    ((hVC1 n).differentiableOn_one x hx).differentiableAt (U.isOpen.mem_nhds hx)
  have hVHS' (n : ℕ) :
      ∀ x ∈ (U : Set Plane), ∀ y ∈ (U : Set Plane),
        gradHS (fderiv ℝ (V n).value x - fderiv ℝ (V n).value y) ≤ (K : ℝ) * dist x y := by
    intro x hx y hy
    rw [← hVGrad n]
    exact hVHS n x hx y hy
  have hVCont (n : ℕ) : ContinuousOn (fderiv ℝ (V n).value) (U : Set Plane) :=
    (lipschitzOnWith_gradient_of_gradHS (hVHS' n)).continuousOn
  have hIdem (n : ℕ) : normalize_height (V n).value a = (V n).value := by
    funext x
    have hZero : fderiv ℝ (V n).value a = 0 := (congrFun (hVGrad n) a).symm.trans (hVGradZero n)
    simp [normalize_height, hVZero n, hZero]
  obtain ⟨v, p, k, hk, hvC1, hvDeriv, hvZero, hpZero, hHS, hvConv, hpConv⟩ :=
    normalized_disk_potentials_compactness a R K hR (fun n => (V n).value)
      hVDiff hVCont hVHS'
  have hDeriv (x : Plane) (hx : x ∈ (U : Set Plane)) : fderiv ℝ v x = p x :=
    (hvDeriv x hx).fderiv
  have hHS' : ∀ x ∈ (U : Set Plane), ∀ y ∈ (U : Set Plane),
      gradHS (fderiv ℝ v x - fderiv ℝ v y) ≤ (K : ℝ) * dist x y := by
    intro x hx y hy
    rw [hDeriv x hx, hDeriv y hy]
    exact hHS x hx y hy
  have hLip := lipschitzOnWith_gradient_of_gradHS hHS'
  let w := weakJet2_of_contDiffOn_locallyLipschitz (U := U) hvC1
    (fun _ _ => ⟨K, U, self_mem_nhdsWithin, hLip⟩)
  have hGradConv (j : ℕ) : TendstoUniformlyOn (fun n => (V (k n)).gradient) w.gradient atTop
      (diskExhaustion a R j) := by
    intro S hS
    exact (hpConv j S hS).mono fun n hn x hx => by
      change (fderiv ℝ v x, (V (k n)).gradient x) ∈ S
      rw [hDeriv x (diskExhaustion_subset a R j hx), hVGrad (k n), ← hIdem (k n)]
      exact hn x hx
  have hAllConv : ∀ s : Set Plane, s ⊆ (U : Set Plane) → IsCompact s →
      TendstoUniformlyOn (fun n => (V (k n)).gradient) w.gradient atTop s := by
    intro s hSub hCompact
    obtain ⟨j, hj⟩ := diskExhaustion_covers_compacts a R s hSub hCompact
    exact (hGradConv j).mono hj
  have hVGradOp (n : ℕ) (x : Plane) (hx : x ∈ (U : Set Plane)) :
      ‖(V n).gradient x‖ ≤ (K : ℝ) * R :=
    (opNorm_le_gradHS _).trans
      ((hVGradBound n x hx).trans (mul_le_mul_of_nonneg_left (hRadius x hx) K.coe_nonneg))
  have hVB (n : ℕ) : CurvatureBounds (V n) ((K : ℝ) * R) K K := by
    have hGradZero : fderiv ℝ (V n).value a = 0 := (congrFun (hVGrad n) a).symm.trans (hVGradZero n)
    obtain ⟨hv, hp, _, _, _, _⟩ := classical_normalized_jet_bounds hConvex ha R K hRadius
      (hVC1 n) (hVZero n) hGradZero (hVHS' n)
    have hMemGrad : MemLp (V n).gradient ∞ μ := (hVGrad n).symm ▸ hp
    have hFrob : ∀ᵐ x ∂μ, ((V n).hessian x).frobenius ≤ (K : ℝ) := by
      rw [hVHess n]
      exact hFrobenius n
    exact ⟨hv, hMemGrad, (V n).second_memLp_top_of_frobenius_ae_le hFrob,
      (ae_restrict_mem U.isOpen.measurableSet).mono (hVGradOp n),
      (V n).norm_second_ae_le hFrob, hFrob⟩
  have hGradZero : fderiv ℝ v a = 0 := (hDeriv a ha).trans hpZero
  obtain ⟨hv, hp, hb, _, hpBound, hbBound⟩ := classical_normalized_jet_bounds hConvex ha R K hRadius
    hvC1 hvZero hGradZero hHS'
  have hwSecondMem : MemLp w.second ∞ μ := hb
  have hwSecondBound : ∀ᵐ x ∂μ, ‖w.second x‖ ≤ (K : ℝ) := hbBound
  have hCoarse : ∀ᵐ x ∂μ, (w.hessian x).frobenius ≤ 2 * (K : ℝ) := by
    have hex : ‖ex‖ = 1 := by simp [ex, EuclideanSpace.single, PiLp.norm_single]
    have hey : ‖ey‖ = 1 := by simp [ey, EuclideanSpace.single, PiLp.norm_single]
    filter_upwards [hwSecondBound] with x hx
    have hEval (b c : Plane) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
        ‖w.second x b c‖ ≤ (K : ℝ) := by
      calc
        _ ≤ ‖w.second x b‖ * ‖c‖ := (w.second x b).le_opNorm c
        _ = ‖w.second x b‖ := by rw [hc, mul_one]
        _ ≤ ‖w.second x‖ * ‖b‖ := (w.second x).le_opNorm b
        _ ≤ _ := by rw [hb, mul_one]; exact hx
    have hxx := pow_le_pow_left₀ (norm_nonneg _) (hEval ex ex hex hex) 2
    have hxy := pow_le_pow_left₀ (norm_nonneg _) (hEval ey ex hey hex) 2
    have hyy := pow_le_pow_left₀ (norm_nonneg _) (hEval ey ey hey hey) 2
    change Real.sqrt (‖w.second x ex ex‖ ^ 2 + 2 * ‖w.second x ey ex‖ ^ 2 +
      ‖w.second x ey ey‖ ^ 2) ≤ 2 * (K : ℝ)
    exact (Real.sqrt_le_iff).2 ⟨by positivity, by nlinarith only [hxx, hxy, hyy]⟩
  have hCoord := w.hessian_coordinates_integrable hwSecondMem.aestronglyMeasurable hCoarse
  have hColumns := second_column_limits_of_gradient ((K : ℝ) * R)
    (fun n => hVGradOp (k n)) hAllConv
  have hwHS : ∀ᵐ x ∂μ, (w.hessian x).frobenius ≤ (K : ℝ) :=
    hessian_bound_of_test_limits_pos_dimension hm
      (fun n => (V (k n)).hessian_coordinates_integrable
        (hVB (k n)).second_mem.aestronglyMeasurable (hVB (k n)).frobenius_bound)
      hCoord K.coe_nonneg (fun n => (hVB (k n)).frobenius_bound) hColumns
  have hwBounds : CurvatureBounds w ((K : ℝ) * R) K K := ⟨hv, hp, hb, hpBound, hbBound, hwHS⟩
  have hP : 0 ≤ (K : ℝ) * R := mul_nonneg K.coe_nonneg R.coe_nonneg
  refine ⟨⟨V, w, k, hk, fun n => ⟨hVSecond n, hVHess n, hVGrad n, hVZero n, hVGradZero n⟩,
    (fun n => (hVGrad n).symm ▸ hVCont n),
    hvZero, hGradZero, hvC1, rfl, hHS', ?_, hGradConv, hwBounds, ?_, ?_⟩⟩
  · intro j
    change TendstoUniformlyOn (fun n => (V (k n)).value) v atTop (diskExhaustion a R j)
    simpa only [hIdem] using hvConv j
  · exact fun e φ hφ => hessian_weakStar_of_column_tests
      (fun n => (hVB (k n)).second_mem.aestronglyMeasurable) hwSecondMem.aestronglyMeasurable
      K.coe_nonneg (fun n => (hVB (k n)).frobenius_bound) hwHS hColumns e hφ
  · exact fun φ hφ => curvature_weakStar_of_gradient_locally_uniform hP K.coe_nonneg K.coe_nonneg
      (fun n => hVB (k n)) hwBounds hAllConv hφ


/-- Same-disk closure for sources converging against interior smooth tests,
with the full source-independent compactness certificate on the same subsequence. -/
public theorem exists_same_disk_solution_limit
    (hm : 0 < m) (a : Plane) (R K : ℝ≥0) (hR : 0 < R)
    (W : ℕ → WeakJet2 m (⟨Metric.ball a R, Metric.isOpen_ball⟩ : Opens Plane))
    (hValueMem : ∀ n j, MemLp (W n).value ∞ (volume.restrict (openDiskExhaustion a R j : Set Plane)))
    (hGradientMem : ∀ n j, MemLp (W n).gradient ∞
      (volume.restrict (openDiskExhaustion a R j : Set Plane)))
    (hFrobenius : ∀ n, ∀ᵐ x ∂volume.restrict (Metric.ball a R),
      ((W n).hessian x).frobenius ≤ (K : ℝ))
    (F : ℕ → Plane → ℝ) (f : Plane → ℝ)
    (hEq : ∀ n, (fun x => ((W n).hessian x).q) =ᵐ[volume.restrict (Metric.ball a R)] F n)
    (hf : LocallyIntegrableOn f (Metric.ball a R) volume)
    (hSource : ∀ ψ : 𝓓((⟨Metric.ball a R, Metric.isOpen_ball⟩ : Opens Plane), ℝ),
      Tendsto (fun n => ∫ x in Metric.ball a R, ψ x • F n x) atTop
        (𝓝 (∫ x in Metric.ball a R, ψ x • f x))) :
    ∃ C : SameDiskLimit a R K W,
      (fun x => (C.limit.hessian x).q) =ᵐ[volume.restrict (Metric.ball a R)] f := by
  let U : Opens Plane := ⟨Metric.ball a R, Metric.isOpen_ball⟩
  let μ := volume.restrict (U : Set Plane)
  let _ : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.mpr
      (((measure_mono Metric.ball_subset_closedBall).trans_lt (isCompact_closedBall a R).measure_lt_top).ne)
  obtain ⟨C⟩ := exists_same_disk_compact_limit hm a R K hR W hValueMem hGradientMem hFrobenius
  have hc := C.limit.second_eval_memLp_of_bound
    C.bounds.second_mem.aestronglyMeasurable C.bounds.second_bound
  have hq : IntegrableOn (fun x => (C.limit.hessian x).q) (U : Set Plane) volume :=
    (integrable_weak_inner (hc ex ex) (hc ey ey)).sub
      (integrable_weak_inner (hc ex ey) (hc ex ey))
  have hEq' : ∀ᶠ n in atTop, (fun x => ((C.normalized (C.subseq n)).hessian x).q) =ᵐ[μ] F (C.subseq n) := by
    apply Eventually.of_forall
    intro n
    rw [(C.normalized_data (C.subseq n)).2.1]
    exact hEq (C.subseq n)
  refine ⟨C, ae_eq_of_same_domain_test_limits hq.locallyIntegrableOn hf hEq' ?_
    (fun ψ => (hSource ψ).comp C.strictMono_subseq.tendsto_atTop)⟩
  intro ψ
  have hψ : IntegrableOn (ψ : Plane → ℝ) (U : Set Plane) volume :=
    ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  have h := C.curvature_weakStar ψ hψ
  change Tendsto (fun n => ∫ x in Metric.ball a R, ψ x • ((C.normalized (C.subseq n)).hessian x).q)
    atTop (𝓝 (∫ x in Metric.ball a R, ψ x • (C.limit.hessian x).q))
  simpa only [smul_eq_mul, mul_comm] using h

end C2Riemannian.WeakJet2
