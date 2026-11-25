module

public import C2Riemannian.WeakRepresentative
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.Linarith

/-! # Local and unique classical representatives on open planar sets (M03) -/

set_option autoImplicit false

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology

namespace C2Riemannian.WeakJet2

variable {m : ℕ} {U : Opens Plane}

/-- Any two continuous representatives of the same weak potential agree on
the open set. Their classical derivatives then agree there as well. -/
public theorem representative_unique (w : WeakJet2 m U)
    {W₁ W₂ : Plane → Target m} (hW₁ : ContinuousOn W₁ (U : Set Plane))
    (hW₂ : ContinuousOn W₂ (U : Set Plane))
    (h₁ : W₁ =ᵐ[volume.restrict (U : Set Plane)] w.value)
    (h₂ : W₂ =ᵐ[volume.restrict (U : Set Plane)] w.value) :
    EqOn W₁ W₂ (U : Set Plane) ∧
      EqOn (fderiv ℝ W₁) (fderiv ℝ W₂) (U : Set Plane) := by
  have h := Measure.eqOn_open_of_ae_eq (h₁.trans h₂.symm) U.isOpen hW₁ hW₂
  refine ⟨h, fun x hx => ?_⟩
  have heq : W₁ =ᶠ[𝓝 x] W₂ := Filter.eventually_of_mem (U.isOpen.mem_nhds hx) h
  exact heq.fderiv_eq

private theorem ae_norm_bound_top {E : Type*} [NormedAddCommGroup E] {f : Plane → E}
    {μ : Measure Plane} (hf : MemLp f ∞ μ) :
    ∃ C : ℝ≥0, ∀ᵐ x ∂μ, ‖f x‖ ≤ (C : ℝ) := by
  have h : eLpNormEssSup f μ < ∞ := by simpa only [eLpNorm_exponent_top hf.aestronglyMeasurable] using hf.eLpNorm_lt_top
  obtain ⟨C, hC⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp h
  change ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C at hC
  exact ⟨C, hC⟩

private theorem gradHS_le_twice_opNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Plane →L[ℝ] E) : gradHS A ≤ 2 * ‖A‖ := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  have h (i : Fin 2) : ‖A (b i)‖ ≤ ‖A‖ := by
    simpa only [b.orthonormal.norm_eq_one i, mul_one] using A.le_opNorm (b i)
  have h₀ := pow_le_pow_left₀ (norm_nonneg _) (h 0) 2
  have h₁ := pow_le_pow_left₀ (norm_nonneg _) (h 1) 2
  unfold gradHS
  rw [Fin.sum_univ_two, ← Real.sqrt_sq (mul_nonneg zero_le_two (norm_nonneg A))]
  apply Real.sqrt_le_sqrt
  change ‖A (b 0)‖ ^ 2 + ‖A (b 1)‖ ^ 2 ≤ (2 * ‖A‖) ^ 2
  nlinarith only [h₀, h₁, sq_nonneg ‖A‖]

/-- A local essential bound on each weak field gives a classical first jet on
an arbitrary open subset of the plane. Each prescribed local Frobenius
bound remains a Lipschitz constant for the gradient on a smaller ball. -/
public theorem exists_classical_representative_on_open (w : WeakJet2 m U)
    (hLocal : ∀ x : U, ∃ (R : ℝ) (K : ℝ≥0), 0 < R ∧ Metric.ball (x : Plane) R ⊆ (U : Set Plane) ∧
      MemLp w.value ∞ (volume.restrict (Metric.ball (x : Plane) R)) ∧
      MemLp w.gradient ∞ (volume.restrict (Metric.ball (x : Plane) R)) ∧
      MemLp w.second ∞ (volume.restrict (Metric.ball (x : Plane) R)) ∧
      (∀ᵐ y ∂volume.restrict (Metric.ball (x : Plane) R), (w.hessian y).frobenius ≤ (K : ℝ))) :
    ∃ (W : Plane → Target m) (P : Plane → Plane →L[ℝ] Target m),
      ContDiffOn ℝ 1 W (U : Set Plane) ∧
      (∀ x ∈ (U : Set Plane), HasFDerivAt W (P x) x) ∧
      LocallyLipschitzOn (U : Set Plane) P ∧
      W =ᵐ[volume.restrict (U : Set Plane)] w.value ∧
      P =ᵐ[volume.restrict (U : Set Plane)] w.gradient ∧
      (∀ x : U, ∃ (R : ℝ) (K : ℝ≥0), 0 < R ∧ Metric.ball (x : Plane) R ⊆ (U : Set Plane) ∧
        (∀ᵐ y ∂volume.restrict (Metric.ball (x : Plane) R), (w.hessian y).frobenius ≤ (K : ℝ)) ∧
        ∀ y ∈ Metric.ball (x : Plane) (R / 2), ∀ z ∈ Metric.ball (x : Plane) (R / 2),
          gradHS (P y - P z) ≤ (K : ℝ) * dist y z) := by
  classical
  choose R K hR hSub hVal hGrad hSecond hF using hLocal
  let ball (x : U) := Metric.ball (x : Plane) (R x / 2)
  have hBallSub (x : U) : ball x ⊆ (U : Set Plane) :=
    (Metric.ball_subset_ball (half_le_self (hR x).le)).trans (hSub x)
  have hBallOpen (x : U) : IsOpen (ball x) := Metric.isOpen_ball
  have hBallSelf (x : U) : (x : Plane) ∈ ball x := Metric.mem_ball_self (half_pos (hR x))
  have hCov (x : Plane) (hx : x ∈ (U : Set Plane)) : ∃ j : U, x ∈ ball j :=
    ⟨⟨x, hx⟩, hBallSelf ⟨x, hx⟩⟩
  have hLoc (x : U) :
      ∃ (W : Plane → Target m) (P : Plane → Plane →L[ℝ] Target m),
        ContDiffOn ℝ 1 W (ball x) ∧
        (∀ y ∈ ball x, HasFDerivAt W (P y) y) ∧
        (∀ y ∈ ball x, ∀ z ∈ ball x, gradHS (P y - P z) ≤ (K x : ℝ) * dist y z) ∧
        W =ᵐ[volume.restrict (ball x)] w.value ∧
        P =ᵐ[volume.restrict (ball x)] w.gradient := by
    let V : Opens Plane := ⟨Metric.ball (x : Plane) (R x), Metric.isOpen_ball⟩
    let wx := w.restrict (V := V) (hSub x)
    obtain ⟨M₀, hM₀⟩ := ae_norm_bound_top (hVal x)
    obtain ⟨M₁, hM₁⟩ := ae_norm_bound_top (hGrad x)
    have hHS : ∀ᵐ y ∂volume.restrict (V : Set Plane), gradHS (wx.gradient y) ≤ ((2 * M₁ : ℝ≥0) : ℝ) := by
      filter_upwards [hM₁] with y hy
      exact (gradHS_le_twice_opNorm _).trans (mul_le_mul_of_nonneg_left hy zero_le_two)
    obtain ⟨W, P, hW, hD, hL, hWae, hPae⟩ :=
      wx.exists_classical_representative_on_ball (x : Plane) (R x / 2)
        (Metric.closedBall_subset_ball (half_lt_self (hR x))) (hVal x) (hGrad x) (hSecond x)
        M₀ (2 * M₁) (K x) hM₀ hHS (hF x)
    refine ⟨W, P, hW, hD, ?_, hWae, hPae⟩
    intro y hy z hz
    exact hL y (Metric.ball_subset_closedBall hy) z (Metric.ball_subset_closedBall hz)
  choose Wj Pj hC hD hL hWa hPa using hLoc
  have hPL (j : U) : LipschitzOnWith (K j) (Pj j) (ball j) :=
    LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
      rw [dist_eq_norm]
      exact (opNorm_le_gradHS _).trans (hL j x hx y hy)
  have hEqW (i j : U) : EqOn (Wj i) (Wj j) (ball i ∩ ball j) := by
    have h₁ : Wj i =ᵐ[volume.restrict (ball i ∩ ball j)] w.value :=
      ae_mono (Measure.restrict_mono inter_subset_left le_rfl) (hWa i)
    have h₂ : Wj j =ᵐ[volume.restrict (ball i ∩ ball j)] w.value :=
      ae_mono (Measure.restrict_mono inter_subset_right le_rfl) (hWa j)
    exact Measure.eqOn_open_of_ae_eq (h₁.trans h₂.symm) ((hBallOpen i).inter (hBallOpen j))
      ((hC i).continuousOn.mono inter_subset_left) ((hC j).continuousOn.mono inter_subset_right)
  have hEqP (i j : U) : EqOn (Pj i) (Pj j) (ball i ∩ ball j) := by
    have h₁ : Pj i =ᵐ[volume.restrict (ball i ∩ ball j)] w.gradient :=
      ae_mono (Measure.restrict_mono inter_subset_left le_rfl) (hPa i)
    have h₂ : Pj j =ᵐ[volume.restrict (ball i ∩ ball j)] w.gradient :=
      ae_mono (Measure.restrict_mono inter_subset_right le_rfl) (hPa j)
    exact Measure.eqOn_open_of_ae_eq (h₁.trans h₂.symm) ((hBallOpen i).inter (hBallOpen j))
      ((hPL i).continuousOn.mono inter_subset_left) ((hPL j).continuousOn.mono inter_subset_right)
  let W (x : Plane) := if hx : x ∈ (U : Set Plane) then Wj (hCov x hx).choose x else 0
  let P (x : Plane) := if hx : x ∈ (U : Set Plane) then Pj (hCov x hx).choose x else 0
  have hWj (j : U) : EqOn W (Wj j) (ball j) := by
    intro x hx
    have hxU := hBallSub j hx
    change (if h : x ∈ (U : Set Plane) then Wj (hCov x h).choose x else 0) = Wj j x
    rw [dite_eq_left hxU]
    exact hEqW _ j ⟨(hCov x hxU).choose_spec, hx⟩
  have hPj (j : U) : EqOn P (Pj j) (ball j) := by
    intro x hx
    have hxU := hBallSub j hx
    change (if h : x ∈ (U : Set Plane) then Pj (hCov x h).choose x else 0) = Pj j x
    rw [dite_eq_left hxU]
    exact hEqP _ j ⟨(hCov x hxU).choose_spec, hx⟩
  obtain ⟨J, hJ, hUnion⟩ := isOpen_iUnion_countable ball hBallOpen
  have hCover : (U : Set Plane) = ⋃ j ∈ J, ball j := by
    rw [hUnion]
    exact Subset.antisymm (fun x hx => mem_iUnion_of_mem ⟨x, hx⟩ (hBallSelf ⟨x, hx⟩))
      (iUnion_subset hBallSub)
  refine ⟨W, P, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply contDiffOn_of_locally_contDiffOn
    intro x hx
    let j : U := ⟨x, hx⟩
    exact ⟨ball j, hBallOpen j, hBallSelf j, ((hC j).congr (hWj j)).mono inter_subset_right⟩
  · intro x hx
    let j : U := ⟨x, hx⟩
    rw [hPj j (hBallSelf j)]
    exact (hD j x (hBallSelf j)).congr_of_eventuallyEq
      (Filter.eventually_of_mem ((hBallOpen j).mem_nhds (hBallSelf j)) (hWj j))
  · intro x hx
    let j : U := ⟨x, hx⟩
    refine ⟨K j, ball j, mem_nhdsWithin_of_mem_nhds ((hBallOpen j).mem_nhds (hBallSelf j)), ?_⟩
    apply LipschitzOnWith.of_dist_le_mul
    intro y hy z hz
    rw [hPj j hy, hPj j hz]
    exact (hPL j).dist_le_mul y hy z hz
  · change ∀ᵐ x ∂volume.restrict (U : Set Plane), W x = w.value x
    rw [hCover, ae_restrict_biUnion_iff ball hJ]
    intro j _
    filter_upwards [hWa j, ae_restrict_mem (hBallOpen j).measurableSet] with x hx hBall
    exact (hWj j hBall).trans hx
  · change ∀ᵐ x ∂volume.restrict (U : Set Plane), P x = w.gradient x
    rw [hCover, ae_restrict_biUnion_iff ball hJ]
    intro j _
    filter_upwards [hPa j, ae_restrict_mem (hBallOpen j).measurableSet] with x hx hBall
    exact (hPj j hBall).trans hx
  · intro j
    refine ⟨R j, K j, hR j, hSub j, hF j, ?_⟩
    intro y hy z hz
    rw [hPj j hy, hPj j hz]
    exact hL j y hy z hz

private theorem frobenius_le_twice_second (w : WeakJet2 m U) (x : Plane) :
    (w.hessian x).frobenius ≤ 2 * ‖w.second x‖ := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  let B := w.second x
  have h (i j : Fin 2) : ‖B (b i) (b j)‖ ≤ ‖B‖ := by
    have hi : ‖B (b i)‖ ≤ ‖B‖ := by
      simpa only [b.orthonormal.norm_eq_one i, mul_one] using B.le_opNorm (b i)
    have hj : ‖B (b i) (b j)‖ ≤ ‖B (b i)‖ := by
      simpa only [b.orthonormal.norm_eq_one j, mul_one] using (B (b i)).le_opNorm (b j)
    exact hj.trans hi
  have h00 := pow_le_pow_left₀ (norm_nonneg _) (h 0 0) 2
  have h10 := pow_le_pow_left₀ (norm_nonneg _) (h 1 0) 2
  have h11 := pow_le_pow_left₀ (norm_nonneg _) (h 1 1) 2
  have hn : 0 ≤ 2 * ‖w.second x‖ := mul_nonneg zero_le_two (norm_nonneg (w.second x))
  rw [Hess3.frobenius, Hess3.frobeniusSq, ← Real.sqrt_sq hn]
  apply Real.sqrt_le_sqrt
  simpa only [WeakJet2.hessian, B, b, EuclideanSpace.basisFun_apply] using
    (show ‖B (b 0) (b 0)‖ ^ 2 + 2 * ‖B (b 1) (b 0)‖ ^ 2 + ‖B (b 1) (b 1)‖ ^ 2 ≤ (2 * ‖B‖) ^ 2
      from by nlinarith only [h00, h10, h11])

/-- The local (W^{2,infty}) input is sufficient for a (C^1) representative
with locally Lipschitz classical gradient. -/
public theorem exists_classical_representative_of_locally_memLp_top (w : WeakJet2 m U)
    (hLocal : ∀ x : U, ∃ R : ℝ, 0 < R ∧ Metric.ball (x : Plane) R ⊆ (U : Set Plane) ∧
      MemLp w.value ∞ (volume.restrict (Metric.ball (x : Plane) R)) ∧
      MemLp w.gradient ∞ (volume.restrict (Metric.ball (x : Plane) R)) ∧
      MemLp w.second ∞ (volume.restrict (Metric.ball (x : Plane) R))) :
    ∃ (W : Plane → Target m) (P : Plane → Plane →L[ℝ] Target m),
      ContDiffOn ℝ 1 W (U : Set Plane) ∧
      (∀ x ∈ (U : Set Plane), HasFDerivAt W (P x) x) ∧
      LocallyLipschitzOn (U : Set Plane) P ∧
      W =ᵐ[volume.restrict (U : Set Plane)] w.value ∧
      P =ᵐ[volume.restrict (U : Set Plane)] w.gradient := by
  have hChoose (x : U) : ∃ (R : ℝ) (K : ℝ≥0),
      0 < R ∧ Metric.ball (x : Plane) R ⊆ (U : Set Plane) ∧
      MemLp w.value ∞ (volume.restrict (Metric.ball (x : Plane) R)) ∧
      MemLp w.gradient ∞ (volume.restrict (Metric.ball (x : Plane) R)) ∧
      MemLp w.second ∞ (volume.restrict (Metric.ball (x : Plane) R)) ∧
      (∀ᵐ y ∂volume.restrict (Metric.ball (x : Plane) R), (w.hessian y).frobenius ≤ (K : ℝ)) := by
    obtain ⟨R, hR, hSub, hW, hP, hB⟩ := hLocal x
    obtain ⟨C, hC⟩ := ae_norm_bound_top
      (E := Plane →L[ℝ] (Plane →L[ℝ] Target m)) (f := w.second)
      (μ := volume.restrict (Metric.ball (x : Plane) R)) hB
    refine ⟨R, 2 * C, hR, hSub, hW, hP, hB, hC.mono ?_⟩
    exact fun y hy => (frobenius_le_twice_second w y).trans (mul_le_mul_of_nonneg_left hy zero_le_two)
  obtain ⟨W, P, hW, hDeriv, hLip, hWae, hPae, _⟩ :=
    w.exists_classical_representative_on_open hChoose
  exact ⟨W, P, hW, hDeriv, hLip, hWae, hPae⟩

end C2Riemannian.WeakJet2
