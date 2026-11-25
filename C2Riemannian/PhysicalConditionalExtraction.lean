module

public import C2Riemannian.ConditionalExtraction
public import C2Riemannian.PhysicalPhaseWeight
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # The shared conditional subsequence on the actual physical row (M31) -/

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped Topology

namespace C2Riemannian.PhysicalLayerRow

variable {Q : Set Plane} {directions : PhysicalDirections} {s δ : ℝ}
  {layer : IdealLayer} {p : PhysicalPrefix Q} {next : ℕ → PhysicalPrefix Q}

/-- The row weight extended by one off the corresponding parent, to keep
the same normalization in a common ambient measure. -/
@[expose] public noncomputable def ambientPhaseWeight (row : PhysicalLayerRow directions s δ layer p next)
    (i : p.Active × Bool) (k : ℕ) (x : Plane) : ℝ := by
  classical
  exact
  if x ∈ p.platform i.1.1 then row.phaseWeight i.1 i.2 k x else 1

private theorem measurable_phaseWeight (row : PhysicalLayerRow directions s δ layer p next)
    (i : p.Active × Bool) (k : ℕ) : Measurable (row.phaseWeight i.1 i.2 k) :=
  measurable_const.mul ((measurable_phaseIndicator (isOpen_phaseInterval i.2
    (row.frequencyContract.width k))).comp (measurable_const.mul
      (innerSL ℝ (directions.normal layer s)).continuous.measurable))

private theorem phaseWeight_mem_Icc (row : PhysicalLayerRow directions s δ layer p next)
    (i : p.Active × Bool) (k : ℕ) (x : Plane) : row.phaseWeight i.1 i.2 k x ∈ Icc (0 : ℝ) 2 := by
  have h := phaseIndicator_mem_Icc (phaseInterval i.2 (row.frequencyContract.width k))
    ((row.frequencyContract.frequency k : ℝ) * inner ℝ (directions.normal layer s) x)
  refine ⟨mul_nonneg (by norm_num) h.1, ?_⟩
  simpa only [phaseWeight, mul_one] using mul_le_mul_of_nonneg_left h.2 (show (0 : ℝ) ≤ 2 by norm_num)

private theorem ambientPhaseWeight_unit (row : PhysicalLayerRow directions s δ layer p next)
    (hn : directions.normal layer s ≠ 0) (i : p.Active × Bool)
    (γ : Lp ℝ 1 (volume.restrict Q)) :
    Tendsto (fun k => ∫ x in Q, row.ambientPhaseWeight i k x * γ x) atTop (𝓝 (∫ x in Q, γ x)) := by
  classical
  let P := p.platform i.1.1
  have hP : MeasurableSet P := (p.platform_open i.1.1).measurableSet
  have hPQ : P ⊆ Q := p.platform_subset i.1.1
  have hγ := L1.integrable_coeFn γ
  have hγP : IntegrableOn γ P volume := hγ.mono_measure (Measure.restrict_mono hPQ le_rfl)
  have hL := row.phaseWeight_test_limit i.1 i.2 hn id strictMono_id hγP
  change Tendsto (fun k => ∫ x in P, row.phaseWeight i.1 i.2 k x * γ x) atTop
    (𝓝 (∫ x in P, γ x)) at hL
  have hEq (k : ℕ) : (∫ x in Q, row.ambientPhaseWeight i k x * γ x) =
      (∫ x in Q, γ x) + ((∫ x in P, row.phaseWeight i.1 i.2 k x * γ x) - ∫ x in P, γ x) := by
    let g (x : Plane) := (row.phaseWeight i.1 i.2 k x - 1) * γ x
    have hg : Integrable g (volume.restrict Q) := by
      refine hγ.bdd_mul (c := 1) (((measurable_phaseWeight row i k).sub measurable_const).aestronglyMeasurable) ?_
      exact Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_le]
        have h := phaseWeight_mem_Icc row i k x
        change 0 ≤ row.phaseWeight i.1 i.2 k x ∧ row.phaseWeight i.1 i.2 k x ≤ 2 at h
        exact ⟨by linarith only [h.1], by linarith only [h.2]⟩
    have hgP : IntegrableOn g P volume := hg.mono_measure (Measure.restrict_mono hPQ le_rfl)
    have hwγ : IntegrableOn (fun x => row.phaseWeight i.1 i.2 k x * γ x) P volume :=
      hγP.bdd_mul (c := 2) (measurable_phaseWeight row i k).aestronglyMeasurable
        (Eventually.of_forall fun x => (Real.norm_of_nonneg (phaseWeight_mem_Icc row i k x).1).trans_le
          (phaseWeight_mem_Icc row i k x).2)
    have hd : (∫ x in P, g x) =
        (∫ x in P, row.phaseWeight i.1 i.2 k x * γ x) - ∫ x in P, γ x := by
      rw [← integral_sub hwγ hγP]
      apply integral_congr_ae
      filter_upwards with x
      dsimp [g]
      ring
    rw [← hd, ← inter_eq_right.mpr hPQ, ← setIntegral_indicator hP,
      ← integral_add hγ (hg.indicator hP)]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ P
    · simp only [ambientPhaseWeight, ite_eq_left (show x ∈ p.platform i.1.1 from hx),
        indicator_of_mem hx, g]
      ring
    · simp only [ambientPhaseWeight, ite_eq_right (show x ∉ p.platform i.1.1 from hx),
        indicator_of_notMem hx, one_mul, add_zero]
  simp only [hEq]
  simpa only [sub_self, add_zero] using
    (tendsto_const_nhds (x := ∫ x in Q, γ x)).add (hL.sub_const (∫ x in P, γ x))

/-- For the selected physical row, all active parents and both signs share a
single subsequence for every Hessian-ball readout and (L^1) test. -/
public theorem exists_shared_conditional_pairings
    (row : PhysicalLayerRow directions s δ layer p next) (hQ : Bornology.IsBounded Q)
    (hn : directions.normal layer s ≠ 0) (m : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (state : ℕ → Plane → HessianBall m K) (hs : ∀ k, Measurable (state k))
    (base : ℕ → ℕ) (hBase : StrictMono base) :
    ∃ (σ : ℕ → ℕ) (L : p.Active × Bool → Plane → PositiveFunctional (HessianBall m K)),
      StrictMono σ ∧ (∀ i (f : C(HessianBall m K, ℝ)), Measurable (fun x => L i x f)) ∧
      ∀ (i : p.Active × Bool) (f : C(HessianBall m K, ℝ)) (γ : Plane → ℝ),
        IntegrableOn γ (p.platform i.1.1) volume →
        Tendsto (fun k => ∫ x in p.platform i.1.1, row.phaseWeight i.1 i.2 (base (σ k)) x *
          f (state (base (σ k)) x) * γ x) atTop
          (𝓝 (∫ x in p.platform i.1.1, (∫ y, f y ∂(L i x).representingMeasure) * γ x)) := by
  classical
  let μ := volume.restrict Q
  let _ : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hQ.measure_lt_top.ne
  let _ : CompactSpace (HessianBall m K) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : HessSpace m) K)
  let x₀ : HessianBall m K := ⟨0, Metric.mem_closedBall_self hK⟩
  have hp (i : p.Active × Bool) (k : ℕ) : AEStronglyMeasurable (row.ambientPhaseWeight i k) μ :=
    (Measurable.ite (p.platform_open i.1.1).measurableSet
      (measurable_phaseWeight row i k) measurable_const).aestronglyMeasurable
  have hRange (i : p.Active × Bool) (k : ℕ) (x : Plane) :
      row.ambientPhaseWeight i k x ∈ Icc (0 : ℝ) 2 := by
    unfold ambientPhaseWeight
    split
    · exact phaseWeight_mem_Icc row i k x
    · norm_num [mem_Icc]
  obtain ⟨σ, L, hσ, hMeas, hTest⟩ := exists_conditional_pairing_subsequence_of_secondCountable
    (μ := μ) x₀ (fun (_ : p.Active × Bool) => state) row.ambientPhaseWeight (fun _ => hs) hp
    (fun i k => Eventually.of_forall fun x =>
      (Real.norm_of_nonneg (hRange i k x).1).trans_le (hRange i k x).2)
    (fun i k => Eventually.of_forall fun x => (hRange i k x).1)
    (ambientPhaseWeight_unit row hn) base hBase
  refine ⟨σ, L, hσ, hMeas, fun i f γ hγ => ?_⟩
  let P := p.platform i.1.1
  have hP : MeasurableSet P := (p.platform_open i.1.1).measurableSet
  have hPQ : P ⊆ Q := p.platform_subset i.1.1
  let g := P.indicator γ
  have hg : Integrable g μ := by
    rw [integrable_indicator_iff hP]
    change Integrable γ ((volume.restrict Q).restrict P)
    rw [Measure.restrict_restrict hP, inter_eq_left.mpr hPQ]
    exact hγ
  let gLp : Lp ℝ 1 μ := (memLp_one_iff_integrable.mpr hg).toLp g
  have hgLp : gLp =ᵐ[μ] g := (memLp_one_iff_integrable.mpr hg).coeFn_toLp
  have hLeft (k : ℕ) :
      (∫ x, row.ambientPhaseWeight i (base (σ k)) x * f (state (base (σ k)) x) * gLp x ∂μ) =
        ∫ x in P, row.phaseWeight i.1 i.2 (base (σ k)) x * f (state (base (σ k)) x) * γ x := by
    rw [← inter_eq_right.mpr hPQ, ← setIntegral_indicator hP]
    apply integral_congr_ae
    filter_upwards [hgLp] with x hx
    by_cases h : x ∈ P
    · simp only [hx, g, indicator_of_mem h, ambientPhaseWeight,
        ite_eq_left (show x ∈ p.platform i.1.1 from h)]
    · simp only [hx, g, indicator_of_notMem h, mul_zero]
  have hRight :
      (∫ x, (∫ y, f y ∂(L i x).representingMeasure) * gLp x ∂μ) =
        ∫ x in P, (∫ y, f y ∂(L i x).representingMeasure) * γ x := by
    rw [← inter_eq_right.mpr hPQ, ← setIntegral_indicator hP]
    apply integral_congr_ae
    filter_upwards [hgLp] with x hx
    by_cases h : x ∈ P
    · simp only [hx, g, indicator_of_mem h]
    · simp only [hx, g, indicator_of_notMem h, mul_zero]
  simpa only [hLeft, hRight] using hTest i f gLp

end C2Riemannian.PhysicalLayerRow
