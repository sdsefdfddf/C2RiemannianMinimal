module

public import C2Riemannian.PhysicalPhaseWeight
public import C2Riemannian.ConditionalBarycenter
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions Topology

namespace C2Riemannian.PhysicalLayerRow

variable {Q : Set Plane} {directions : PhysicalDirections} {s δ : ℝ}
  {layer : IdealLayer} {p : PhysicalPrefix Q} {next : ℕ → PhysicalPrefix Q}

private noncomputable def phaseRemainder (row : PhysicalLayerRow directions s δ layer p next)
    (i : p.Active) (n : ℕ) (x : Plane) : ℝ :=
  1 - row.phaseWeight i true n x / 2 - row.phaseWeight i false n x / 2

private theorem phaseRemainder_bounds (row : PhysicalLayerRow directions s δ layer p next)
    (i : p.Active) (n : ℕ) (x : Plane) : row.phaseRemainder i n x ∈ Icc (0 : ℝ) 1 := by
  let e := row.frequencyContract.width n
  let t := (row.frequencyContract.frequency n : ℝ) * inner ℝ (directions.normal layer s) x
  have hDis := disjoint_periodicPhases (row.frequencyContract.width_pos n)
    (row.frequencyContract.width_le_one_sixteenth n)
  have heq : row.phaseRemainder i n x =
      1 - phaseIndicator (positivePhase e) t - phaseIndicator (negativePhase e) t := by
    unfold phaseRemainder phaseWeight
    change 1 - (2 * phaseIndicator (positivePhase e) t) / 2 -
      (2 * phaseIndicator (negativePhase e) t) / 2 = _
    ring
  rw [heq, phaseIndicator, phaseIndicator]
  by_cases hp : t ∈ periodicPhase (positivePhase e)
  · have hn : t ∉ periodicPhase (negativePhase e) := fun h => Set.disjoint_left.mp hDis hp h
    simp [indicator_of_mem hp, indicator_of_notMem hn]
  · by_cases hn : t ∈ periodicPhase (negativePhase e)
    · simp [indicator_of_notMem hp, indicator_of_mem hn]
    · simp [indicator_of_notMem hp, indicator_of_notMem hn]

private theorem phaseWeight_measurable (row : PhysicalLayerRow directions s δ layer p next)
    (i : p.Active) (sign : Bool) (n : ℕ) : Measurable (row.phaseWeight i sign n) :=
  measurable_const.mul
    ((measurable_phaseIndicator (isOpen_phaseInterval sign _)).comp
      (measurable_const.mul (innerSL ℝ (directions.normal layer s)).continuous.measurable))

private theorem phaseWeight_norm_le (row : PhysicalLayerRow directions s δ layer p next)
    (i : p.Active) (sign : Bool) (n : ℕ) (x : Plane) :
    ‖row.phaseWeight i sign n x‖ ≤ 2 := by
  have h := phaseIndicator_mem_Icc (phaseInterval sign (row.frequencyContract.width n))
    (row.frequencyContract.frequency n * inner ℝ (directions.normal layer s) x)
  simpa only [phaseWeight, norm_mul, Real.norm_eq_abs, abs_of_nonneg h.1, abs_two, mul_one] using
    mul_le_mul_of_nonneg_left h.2 (by norm_num : (0 : ℝ) ≤ 2)

/-- The two phase means average to the unconditioned parent readout. The
vanishing compact remainder mass is supplied by the actual phase arithmetic. -/
public theorem phase_barycenter_ae
    (row : PhysicalLayerRow directions s δ layer p next)
    (i : p.Active) (hn : directions.normal layer s ≠ 0)
    (k : ℕ → ℕ) (hk : StrictMono k)
    (u : ℕ → Plane → ℝ) (parent plus minus : Plane → ℝ) (B : ℝ)
    (hParent : LocallyIntegrableOn parent (p.platform i.1) volume)
    (hPlus : LocallyIntegrableOn plus (p.platform i.1) volume)
    (hMinus : LocallyIntegrableOn minus (p.platform i.1) volume)
    (hu : ∀ j, AEStronglyMeasurable (u j) (volume.restrict (p.platform i.1)))
    (hB : ∀ j, ∀ᵐ x ∂volume.restrict (p.platform i.1), ‖u j x‖ ≤ B)
    (hWhole : ∀ φ : 𝓓(parentOpen p i, ℝ),
      Tendsto (fun j => ∫ x in p.platform i.1, φ x * u j x) atTop
        (𝓝 (∫ x in p.platform i.1, φ x * parent x)))
    (hPlusLimit : ∀ φ : 𝓓(parentOpen p i, ℝ),
      Tendsto (fun j => ∫ x in p.platform i.1, row.phaseWeight i true (k j) x * u j x * φ x) atTop
        (𝓝 (∫ x in p.platform i.1, φ x * plus x)))
    (hMinusLimit : ∀ φ : 𝓓(parentOpen p i, ℝ),
      Tendsto (fun j => ∫ x in p.platform i.1, row.phaseWeight i false (k j) x * u j x * φ x) atTop
        (𝓝 (∫ x in p.platform i.1, φ x * minus x))) :
    parent =ᵐ[volume.restrict (p.platform i.1)] (fun x => (plus x + minus x) / 2) := by
  let r j := row.phaseRemainder i (k j)
  let w (sign : Bool) (j : ℕ) := row.phaseWeight i sign (k j)
  let P := p.platform i.1
  have hRmeas (j : ℕ) : Measurable (r j) :=
    (measurable_const.sub ((row.phaseWeight_measurable i true (k j)).div_const _)).sub
      ((row.phaseWeight_measurable i false (k j)).div_const _)
  have hb (j : ℕ) (x : Plane) : ‖r j x‖ ≤ 1 := by
    have h := row.phaseRemainder_bounds i (k j) x
    exact (Real.norm_of_nonneg h.1).trans_le h.2
  have hR (φ : 𝓓(parentOpen p i, ℝ)) :
      Tendsto (fun j => ∫ x in P, φ x * r j x * u j x) atTop (𝓝 0) := by
    have hMass := phase_remainder_local hn row.frequencyContract.width
      (fun j => (row.frequencyContract.frequency j : ℝ)) row.frequencyContract.width_pos
      row.frequencyContract.width_le_one_sixteenth row.frequencyContract.tendsto_width
      (fun j => by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 1) (row.frequencyContract.frequency_ge_one j))
      (tendsto_natCast_atTop_atTop.comp row.frequencyContract.tendsto_frequency) φ.hasCompactSupport
    have hEq (j : ℕ) : r j = fun x =>
        1 - phaseIndicator (positivePhase (row.frequencyContract.width (k j)))
          (row.frequencyContract.frequency (k j) * inner ℝ (directions.normal layer s) x) -
        phaseIndicator (negativePhase (row.frequencyContract.width (k j)))
          (row.frequencyContract.frequency (k j) * inner ℝ (directions.normal layer s) x) := by
      funext x
      simp only [r, phaseRemainder, phaseWeight]
      change 1 - (2 * phaseIndicator (positivePhase _) _) / 2 -
        (2 * phaseIndicator (negativePhase _) _) / 2 = _
      ring
    have hMass' : Tendsto (fun j => ∫ x in tsupport (φ : Plane → ℝ), r j x) atTop (𝓝 0) := by
      simpa only [hEq, Function.comp_def] using hMass.comp hk.tendsto_atTop
    let _ : IsFiniteMeasure (volume.restrict (tsupport (φ : Plane → ℝ))) :=
      isFiniteMeasure_restrict.mpr φ.hasCompactSupport.measure_lt_top.ne
    exact remainder_pairing_tendsto φ r u B hMass'
      (fun j => Integrable.of_bound (hRmeas j).aestronglyMeasurable 1 (Eventually.of_forall (hb j)))
      (fun j => Eventually.of_forall fun x => (row.phaseRemainder_bounds i (k j) x).1) hB
  have hSum : LocallyIntegrableOn (fun x => (plus x + minus x) / 2) P volume := by
    have heq : (fun x => (plus x + minus x) / 2) = (1 / 2 : ℝ) • (plus + minus) := by
      funext x
      change (plus x + minus x) / 2 = (1 / 2) * (plus x + minus x)
      ring
    rw [heq]
    exact (hPlus.add hMinus).smul (1 / 2 : ℝ)
  refine conditional_barycenter_ae (U := parentOpen p i) hParent hSum
    (fun φ j => ∫ x in P, w true j x * u j x * φ x)
    (fun φ j => ∫ x in P, w false j x * u j x * φ x)
    (fun φ j => ∫ x in P, φ x * r j x * u j x) hPlusLimit hMinusLimit hR ?_ ?_
  · intro φ
    apply (hWhole φ).congr'
    apply Eventually.of_forall
    intro j
    have hφ : IntegrableOn (φ : Plane → ℝ) P volume :=
      (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).integrableOn
    have hW (sign : Bool) : IntegrableOn (fun x => w sign j x * u j x * φ x) P volume := by
      apply hφ.bdd_mul ((row.phaseWeight_measurable i sign (k j)).aestronglyMeasurable.mul (hu j)) (c := 2 * B)
      filter_upwards [hB j] with x hx
      rw [Pi.mul_apply, norm_mul]
      exact mul_le_mul (row.phaseWeight_norm_le i sign (k j) x) hx (norm_nonneg _) (by norm_num)
    have hRi : IntegrableOn (fun x => φ x * r j x * u j x) P volume := by
      have h := hφ.bdd_mul ((hRmeas j).aestronglyMeasurable.mul (hu j)) (c := 1 * B) ?_
      · change Integrable (fun x => φ x * r j x * u j x) (volume.restrict P)
        simpa only [Pi.mul_apply, mul_left_comm, mul_comm, mul_assoc] using h
      · filter_upwards [hB j] with x hx
        rw [Pi.mul_apply, norm_mul]
        exact mul_le_mul (hb j x) hx (norm_nonneg _) zero_le_one
    change (∫ x in P, φ x * u j x) =
      ((∫ x in P, w true j x * u j x * φ x) + (∫ x in P, w false j x * u j x * φ x)) / 2 +
      ∫ x in P, φ x * r j x * u j x
    have hAvg : IntegrableOn
        (fun x => (w true j x * u j x * φ x + w false j x * u j x * φ x) / 2) P volume :=
      ((hW true).add (hW false)).div_const 2
    rw [← integral_add (hW true) (hW false), ← integral_div, ← integral_add hAvg hRi]
    apply integral_congr_ae
    filter_upwards with x
    change φ x * u j x =
      (w true j x * u j x * φ x + w false j x * u j x * φ x) / 2 + φ x * r j x * u j x
    dsimp only [r, phaseRemainder, w]
    ring
  · intro φ
    exact ⟨by simpa only [smul_eq_mul] using (TauCeti.integrable_smul_of_locallyIntegrableOn hPlus φ).integrableOn,
      by simpa only [smul_eq_mul] using (TauCeti.integrable_smul_of_locallyIntegrableOn hMinus φ).integrableOn⟩

end C2Riemannian.PhysicalLayerRow
