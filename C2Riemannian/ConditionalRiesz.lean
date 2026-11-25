module

public import C2Riemannian.FunctionalMoments
public import C2Riemannian.CountableReadouts
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open MeasureTheory Set Filter TopologicalSpace
open scoped CompactlySupported Topology

namespace C2Riemannian.PositiveFunctional

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

private noncomputable def onCompactSupport (L : PositiveFunctional X) : C_c(X, ℝ) →ₚ[ℝ] ℝ where
  toFun f := L f.toContinuousMap
  map_add' f g := by
    change L (f.toContinuousMap + g.toContinuousMap) = _
    exact map_add L _ _
  map_smul' r f := by
    change L (r • f.toContinuousMap) = _
    exact map_smul L _ _
  monotone' f g h :=
    L.toPositiveLinearMap.monotone' (ContinuousMap.le_def.mpr fun x => h x)

/-- Positivity and normalization bound the action on a continuous readout by its uniform norm. -/
public theorem norm_readout_le (L : PositiveFunctional X) (f : C(X, ℝ)) : ‖L f‖ ≤ ‖f‖ := by
  have hu : L f ≤ ‖f‖ :=
    L.map_le_const fun x => (le_abs_self (f x)).trans (f.norm_coe_le_norm x)
  have hl : L (-f) ≤ ‖f‖ :=
    L.map_le_const fun x => (neg_le_abs (f x)).trans (f.norm_coe_le_norm x)
  rw [map_neg] at hl
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith only [hl], hu⟩

/-- The positive normalized functional is continuous in the uniform norm. -/
public theorem continuous_readout (L : PositiveFunctional X) : Continuous (L : C(X, ℝ) → ℝ) := by
  let T : C(X, ℝ) →ₗ[ℝ] ℝ := L.toPositiveLinearMap.toLinearMap
  have ht (f : C(X, ℝ)) : ‖T f‖ ≤ ‖f‖ := by
    change ‖L f‖ ≤ ‖f‖
    exact L.norm_readout_le f
  have hT := (T.mkContinuous 1 (fun f => by simpa only [one_mul] using ht f)).continuous
  exact hT

section Representation

variable [T2Space X] [MeasurableSpace X] [BorelSpace X]

/-- The regular Borel measure representing a positive normalized continuous-readout functional. -/
public noncomputable def representingMeasure (L : PositiveFunctional X) : Measure X :=
  RealRMK.rieszMeasure (onCompactSupport L)

/-- Every continuous real readout integrates to its value under the functional. -/
public theorem integral_representingMeasure (L : PositiveFunctional X) (f : C(X, ℝ)) :
    (∫ x, f x ∂L.representingMeasure) = L f := by
  let g : C_c(X, ℝ) := ⟨f, HasCompactSupport.of_compactSpace f⟩
  exact RealRMK.integral_rieszMeasure (onCompactSupport L) g

public instance representingMeasure_regular (L : PositiveFunctional X) :
    L.representingMeasure.Regular := by
  unfold representingMeasure
  infer_instance

/-- The Riesz measure is a probability measure because the constant one has value one. -/
public instance representingMeasure_isProbability (L : PositiveFunctional X) :
    IsProbabilityMeasure L.representingMeasure := by
  have h := L.integral_representingMeasure (ContinuousMap.const X (1 : ℝ))
  rw [map_const] at h
  change (∫ _ : X, (1 : ℝ) ∂L.representingMeasure) = 1 at h
  rw [integral_const, smul_eq_mul, mul_one, measureReal_def] at h
  exact ⟨(ENNReal.toReal_eq_one_iff _).mp h⟩

/-- Riesz representation by an actual regular Borel probability measure. -/
public theorem exists_probability_representation (L : PositiveFunctional X) :
    ∃ ν : Measure X, IsProbabilityMeasure ν ∧ ν.Regular ∧
      ∀ f : C(X, ℝ), (∫ x, f x ∂ν) = L f :=
  ⟨L.representingMeasure, inferInstance, inferInstance, L.integral_representingMeasure⟩

end Representation

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Measurability on any uniformly dense family of readouts determines measurability
of every readout of a family of positive normalized functionals. -/
public theorem measurable_readout_of_dense {S : Set C(X, ℝ)} (hS : Dense S)
    (L : Ω → PositiveFunctional X)
    (hm : ∀ f ∈ S, Measurable (fun x => L x f)) (f : C(X, ℝ)) :
    Measurable (fun x => L x f) := by
  obtain ⟨g, hg, hlim⟩ := mem_closure_iff_seq_limit.mp (hS f)
  apply measurable_of_tendsto_metrizable (fun n => hm (g n) (hg n))
  apply tendsto_pi_nhds.mpr
  intro x
  exact (L x).continuous_readout.continuousAt.tendsto.comp hlim

section Representation

variable [T2Space X] [MeasurableSpace X] [BorelSpace X]

/-- Each continuous readout of the representing conditional probability measures is measurable
if this holds on a uniformly dense family of functional readouts. -/
public theorem measurable_integral_representingMeasure_of_dense
    {S : Set C(X, ℝ)} (hS : Dense S) (L : Ω → PositiveFunctional X)
    (hm : ∀ f ∈ S, Measurable (fun x => L x f)) (f : C(X, ℝ)) :
    Measurable (fun x => ∫ y, f y ∂(L x).representingMeasure) := by
  simpa only [integral_representingMeasure] using measurable_readout_of_dense hS L hm f

end Representation
end C2Riemannian.PositiveFunctional

namespace C2Riemannian

/-- The project Hessian ball carries the regular probability representing a positive normalized
functional on its continuous readouts. -/
public theorem hessianBall_probability_representation {m : ℕ} {K : ℝ}
    (L : PositiveFunctional (HessianBall m K)) :
    ∃ ν : Measure (HessianBall m K), IsProbabilityMeasure ν ∧ ν.Regular ∧
      ∀ f : C(HessianBall m K, ℝ), (∫ x, f x ∂ν) = L f := by
  let _ : CompactSpace (HessianBall m K) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : HessSpace m) K)
  exact L.exists_probability_representation

end C2Riemannian


