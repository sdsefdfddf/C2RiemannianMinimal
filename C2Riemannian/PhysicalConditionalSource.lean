module

public import C2Riemannian.ConditionalSource
public import C2Riemannian.ExactPlatformSources
public import C2Riemannian.PhysicalPhaseWeight

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions Topology

namespace C2Riemannian.PhysicalLayerRow

variable {Q : Set Plane} {directions : PhysicalDirections} {s δ : ℝ}
  {layer : IdealLayer} {p : PhysicalPrefix Q} {next : ℕ → PhysicalPrefix Q}

/-- Conditional curvature on either child phase equals the corresponding exact
source readout on the whole parent, in the almost-everywhere sense. -/
public theorem conditional_phase_source_ae
    (row : PhysicalLayerRow directions s δ layer p next)
    (i : p.Active) (sign : Bool) (hn : directions.normal layer s ≠ 0)
    (k : ℕ → ℕ) (hk : StrictMono k) (F : ℕ → Plane → ℝ) (curvature : ℕ → Plane → ℝ)
    (source readout : Plane → ℝ)
    (hv : LocallyIntegrableOn source (p.platform i.1) volume)
    (hr : LocallyIntegrableOn readout (p.platform i.1) volume)
    (hField : ∀ j, curvature j =ᵐ[volume.restrict (p.platform i.1)] F (k j))
    (hPlateau : ∀ n, EqOn (F n) source ((next n).platform (row.childLabel n (i, sign))))
    (hCond : ∀ φ : 𝓓(parentOpen p i, ℝ),
      Tendsto (fun j => ∫ x in p.platform i.1, row.phaseWeight i sign (k j) x * curvature j x * φ x)
        atTop (𝓝 (∫ x in p.platform i.1, φ x * readout x))) :
    readout =ᵐ[volume.restrict (p.platform i.1)] source := by
  apply conditional_source_eq_ae (U := parentOpen p i) hr hv
    (fun j => row.phaseWeight i sign (k j)) curvature _ hCond
  · intro φ
    have hi : IntegrableOn (fun x => φ x * source x) (p.platform i.1) volume := by
      simpa only [smul_eq_mul] using
        (TauCeti.integrable_smul_of_locallyIntegrableOn hv φ).integrableOn
    have h := row.phaseWeight_test_limit i sign hn k hk hi
    have hP : (parentOpen p i : Set Plane) = p.platform i.1 := rfl
    rw [hP]
    simpa only [mul_left_comm, mul_comm, mul_assoc] using h
  · intro φ
    have hCompact := row.frequencyContract.eventually_contains_compact i
      (tsupport (φ : Plane → ℝ)) φ.tsupport_subset φ.hasCompactSupport
    filter_upwards [hk.tendsto_atTop.eventually hCompact] with j hj
    filter_upwards [hField j] with x e hx hw
    exact e.trans (hPlateau (k j) (row.mem_child_of_phaseWeight_ne_zero i sign (k j) (hj hx) hw))

/-- The normalized determinant gives the conditional reverse source on either phase. -/
public theorem conditional_reverse_source_ae
    (row : PhysicalLayerRow directions s δ layer p next)
    (hExact : ∀ n, (next n).ExactJets)
    (i : p.Active) (sign : Bool) (hn : directions.normal layer s ≠ 0)
    (k : ℕ → ℕ) (hk : StrictMono k) (curvature : ℕ → Plane → ℝ)
    (readout : Plane → ℝ)
    (hr : LocallyIntegrableOn readout (p.platform i.1) volume)
    (hField : ∀ j, curvature j =ᵐ[volume.restrict (p.platform i.1)] (next (k j)).reverseSource)
    (hCond : ∀ φ : 𝓓(parentOpen p i, ℝ),
      Tendsto (fun j => ∫ x in p.platform i.1, row.phaseWeight i sign (k j) x * curvature j x * φ x)
        atTop (𝓝 (∫ x in p.platform i.1, φ x * readout x))) :
    readout =ᵐ[volume.restrict (p.platform i.1)]
      fun _ => -((p.ideal i.1).child layer s sign).scalar.det / 25 := by
  refine row.conditional_phase_source_ae i sign hn k hk (fun n => (next n).reverseSource)
    curvature _ readout ?_ hr hField ?_ hCond
  · exact continuousOn_const.locallyIntegrableOn (p.platform_open i.1).measurableSet
  · intro n x hx
    rw [(next n).reverseSource_eq_ideal (hExact n) _ hx, row.child_ideal]

/-- The vertical scalar Hessian entry gives the conditional linear source. -/
public theorem conditional_linear_source_ae
    (row : PhysicalLayerRow directions s δ layer p next)
    (hExact : ∀ n, (next n).ExactJets)
    (i : p.Active) (sign : Bool) (hn : directions.normal layer s ≠ 0)
    {v₀ : Plane → ℝ} (hv₀ : ContDiffOn ℝ 2 v₀ (p.platform i.1)) (θ : ℝ)
    (k : ℕ → ℕ) (hk : StrictMono k) (curvature : ℕ → Plane → ℝ)
    (readout : Plane → ℝ)
    (hr : LocallyIntegrableOn readout (p.platform i.1) volume)
    (hField : ∀ j, curvature j =ᵐ[volume.restrict (p.platform i.1)] (next (k j)).linearSource v₀ θ)
    (hCond : ∀ φ : 𝓓(parentOpen p i, ℝ),
      Tendsto (fun j => ∫ x in p.platform i.1, row.phaseWeight i sign (k j) x * curvature j x * φ x)
        atTop (𝓝 (∫ x in p.platform i.1, φ x * readout x))) :
    readout =ᵐ[volume.restrict (p.platform i.1)] fun x =>
      -WeakJet2.metricYY v₀ x / 2 - (θ / 10) * ((p.ideal i.1).child layer s sign).scalar.yy := by
  refine row.conditional_phase_source_ae i sign hn k hk (fun n => (next n).linearSource v₀ θ)
    curvature _ readout ?_ hr hField ?_ hCond
  · have hcont := WeakJet2.metricYY_continuousOn (U := parentOpen p i) hv₀
    exact ((hcont.neg.div_const 2).sub continuousOn_const).locallyIntegrableOn
      (p.platform_open i.1).measurableSet
  · intro n x hx
    have hxp : x ∈ p.platform i.1 := by
      have hchild := hx
      rw [row.child_platform] at hchild
      exact row.frequencyContract.inner_subset n i hchild.1
    rw [(next n).linearSource_eq_ideal (hExact n) _ hx (p.platform_open i.1) hxp hv₀ θ,
      row.child_ideal]

end C2Riemannian.PhysicalLayerRow

