module

public import C2Riemannian.PhysicalConditionalSource
public import C2Riemannian.ConditionalEnergyBound
public import C2Riemannian.PhysicalTangentialConstraint
public import C2Riemannian.WeakHessianReadouts
public import C2Riemannian.ConditionalRiesz

set_option autoImplicit false
set_option maxHeartbeats 600000

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions Topology

namespace C2Riemannian.PhysicalLayerRow

variable {Q : Set Plane} {directions : PhysicalDirections} {s δ : ℝ}
  {layer : IdealLayer} {p : PhysicalPrefix Q} {next : ℕ → PhysicalPrefix Q}
  {m : ℕ} {K : ℝ}

private theorem locallyIntegrable_functional_readout {P : Set Plane}
    (hP : Bornology.IsBounded P) (L : Plane → PositiveFunctional (HessianBall m K))
    (f : C(HessianBall m K, ℝ)) (hMeas : Measurable (fun x => L x f)) :
    LocallyIntegrableOn (fun x => L x f) P volume := by
  let _ : CompactSpace (HessianBall m K) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : HessSpace m) K)
  let _ : IsFiniteMeasure (volume.restrict P) := isFiniteMeasure_restrict.mpr hP.measure_lt_top.ne
  have hi : IntegrableOn (fun x => L x f) P volume :=
    Integrable.of_bound hMeas.aestronglyMeasurable ‖f‖
      (Eventually.of_forall fun x => (L x).norm_readout_le f)
  exact hi.locallyIntegrableOn

variable (row : PhysicalLayerRow directions s δ layer p next)
  (i : p.Active) (sign : Bool) (hn : directions.normal layer s ≠ 0)
  (k : ℕ → ℕ) (hk : StrictMono k) (state : ℕ → Plane → HessianBall m K)
  (L : Plane → PositiveFunctional (HessianBall m K))

include hn hk

/-- The reverse curvature equation passes from the exact child platforms to the conditional Hessian. -/
public theorem reverse_conditional_curvature
    (hP : Bornology.IsBounded (p.platform i.1)) (hExact : ∀ n, (next n).ExactJets)
    (hMeas : Measurable (fun x => L x HessianBall.curvature))
    (hSource : ∀ j, (fun x => HessianBall.curvature (state j x))
      =ᵐ[volume.restrict (p.platform i.1)] (next (k j)).reverseSource)
    (hPair : ∀ γ : Plane → ℝ, IntegrableOn γ (p.platform i.1) volume →
      Tendsto (fun j => ∫ x in p.platform i.1,
        row.phaseWeight i sign (k j) x * HessianBall.curvature (state j x) * γ x) atTop
        (𝓝 (∫ x in p.platform i.1, L x HessianBall.curvature * γ x))) :
    (fun x => L x HessianBall.curvature) =ᵐ[volume.restrict (p.platform i.1)]
      fun _ => -((p.ideal i.1).child layer s sign).scalar.det / 25 := by
  refine row.conditional_reverse_source_ae hExact i sign hn k hk
    (fun j x => HessianBall.curvature (state j x)) (fun x => L x HessianBall.curvature)
    (locallyIntegrable_functional_readout hP L _ hMeas) hSource ?_
  intro φ
  have h := hPair φ (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).integrableOn
  simpa only [mul_left_comm, mul_comm, mul_assoc] using h

/-- The conditional linear curvature retains the classical derivative of the background. -/
public theorem linear_conditional_curvature
    (hP : Bornology.IsBounded (p.platform i.1)) (hExact : ∀ n, (next n).ExactJets)
    {v₀ : Plane → ℝ} (hv₀ : ContDiffOn ℝ 2 v₀ (p.platform i.1)) (θ : ℝ)
    (hMeas : Measurable (fun x => L x HessianBall.curvature))
    (hSource : ∀ j, (fun x => HessianBall.curvature (state j x))
      =ᵐ[volume.restrict (p.platform i.1)] (next (k j)).linearSource v₀ θ)
    (hPair : ∀ γ : Plane → ℝ, IntegrableOn γ (p.platform i.1) volume →
      Tendsto (fun j => ∫ x in p.platform i.1,
        row.phaseWeight i sign (k j) x * HessianBall.curvature (state j x) * γ x) atTop
        (𝓝 (∫ x in p.platform i.1, L x HessianBall.curvature * γ x))) :
    (fun x => L x HessianBall.curvature) =ᵐ[volume.restrict (p.platform i.1)] fun x =>
      -WeakJet2.metricYY v₀ x / 2 - (θ / 10) * ((p.ideal i.1).child layer s sign).scalar.yy := by
  refine row.conditional_linear_source_ae hExact i sign hn hv₀ θ k hk
    (fun j x => HessianBall.curvature (state j x)) (fun x => L x HessianBall.curvature)
    (locallyIntegrable_functional_readout hP L _ hMeas) hSource ?_
  intro φ
  have h := hPair φ (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).integrableOn
  simpa only [mul_left_comm, mul_comm, mul_assoc] using h

/-- A child-platform bound on the actual energy is preserved by the conditional functional. -/
public theorem conditional_hessian_energy_bound
    (hP : Bornology.IsBounded (p.platform i.1))
    (hState : ∀ j, Measurable (state j))
    (hMeas : Measurable (fun x => L x HessianBall.energy)) (B : ℝ)
    (hChild : ∀ j, ∀ᵐ x ∂volume.restrict (p.platform i.1),
      x ∈ (next (k j)).platform (row.childLabel (k j) (i, sign)) → HessianBall.energy (state j x) ≤ B)
    (hPair : ∀ γ : Plane → ℝ, IntegrableOn γ (p.platform i.1) volume →
      Tendsto (fun j => ∫ x in p.platform i.1,
        row.phaseWeight i sign (k j) x * HessianBall.energy (state j x) * γ x) atTop
        (𝓝 (∫ x in p.platform i.1, L x HessianBall.energy * γ x))) :
    ∀ᵐ x ∂volume.restrict (p.platform i.1), L x HessianBall.energy ≤ B := by
  let _ : CompactSpace (HessianBall m K) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : HessSpace m) K)
  refine row.conditional_energy_bound_ae i sign hn k hk
    (fun j x => HessianBall.energy (state j x)) (fun x => L x HessianBall.energy) B
    (locallyIntegrable_functional_readout hP L _ hMeas) hChild ?_ ?_
  · intro j φ
    have hφ : IntegrableOn (φ : Plane → ℝ) (p.platform i.1) volume :=
      (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).integrableOn
    have hw := row.measurable_phaseWeight i sign (k j)
    have he := (HessianBall.energy (m := m) (K := K)).continuous.measurable.comp (hState j)
    constructor
    · apply hφ.bdd_mul (hw.mul he).aestronglyMeasurable (c := 2 * ‖HessianBall.energy (m := m) (K := K)‖)
      apply Eventually.of_forall
      intro x
      change ‖row.phaseWeight i sign (k j) x * HessianBall.energy (state j x)‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul (row.norm_phaseWeight_le i sign (k j) x)
        (ContinuousMap.norm_coe_le_norm _ _) (norm_nonneg _) (by norm_num)
    · apply hφ.bdd_mul (hw.mul measurable_const).aestronglyMeasurable (c := 2 * ‖B‖)
      apply Eventually.of_forall
      intro x
      change ‖row.phaseWeight i sign (k j) x * B‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (row.norm_phaseWeight_le i sign (k j) x) (norm_nonneg _)
  · intro φ
    have h := hPair φ (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).integrableOn
    simpa only [mul_left_comm, mul_comm, mul_assoc] using h

end C2Riemannian.PhysicalLayerRow
