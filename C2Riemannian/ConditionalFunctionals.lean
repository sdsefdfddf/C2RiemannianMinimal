module

public import C2Riemannian.FunctionalMoments
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Topology.Sequences
import Mathlib.Tactic.Linarith

/-! # Common pointwise conditional functionals from the rational densities (M30) -/

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped Topology

namespace C2Riemannian

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- A bounded rational functional on a dense readout algebra extends to a
positive normalized real functional. The norm and unit fix positivity:
for a nonnegative readout (f), the readout (|f|1-f) has norm at most (|f|). -/
public theorem exists_positiveFunctional_of_rational
    (A : Subalgebra ℚ C(X, ℝ)) (hA : Dense (A : Set C(X, ℝ)))
    (l : A →ₗ[ℚ] ℝ) (hBound : ∀ a, ‖l a‖ ≤ ‖(a : C(X, ℝ))‖) (hOne : l 1 = 1) :
    ∃ L : PositiveFunctional X, Continuous (fun f : C(X, ℝ) => L f) ∧
      (∀ f : C(X, ℝ), ‖L f‖ ≤ ‖f‖) ∧ ∀ a : A, L (a : C(X, ℝ)) = l a := by
  let _ : NormedSpace ℚ C(X, ℝ) := NormedSpace.restrictScalars ℚ ℝ _
  let _ : NormedSpace ℚ ℝ := NormedSpace.restrictScalars ℚ ℝ _
  let ι : A →ₗ[ℚ] C(X, ℝ) := A.val.toLinearMap
  have hDense : DenseRange ι := by
    change Dense (range ι)
    rw [show range ι = (A : Set C(X, ℝ)) from Subtype.range_coe]
    exact hA
  have hB : ∀ a : A, ‖l a‖ ≤ (1 : ℝ) * ‖ι a‖ := fun a => by
    change ‖l a‖ ≤ (1 : ℝ) * ‖(a : C(X, ℝ))‖
    rw [one_mul]
    exact hBound a
  let g : C(X, ℝ) →L[ℚ] ℝ := l.extendOfNorm ι
  have hEq (a : A) : g (a : C(X, ℝ)) = l a :=
    LinearMap.extendOfNorm_eq hDense ⟨1, hB⟩ a
  have hgNorm (f : C(X, ℝ)) : ‖g f‖ ≤ ‖f‖ := by
    simpa only [one_mul] using LinearMap.norm_extendOfNorm_apply_le hDense 1 hB f
  let Lr : C(X, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := g
      map_add' := map_add g
      map_smul' := fun c f => by
        have hcont₁ : Continuous (fun r : ℝ => g (r • f)) :=
          g.continuous.comp (continuous_id.smul continuous_const)
        have hcont₂ : Continuous (fun r : ℝ => r • g f) :=
          continuous_id.smul continuous_const
        exact Rat.denseRange_cast.induction_on c (isClosed_eq hcont₁ hcont₂) (fun q => by
          change g ((q : ℝ) • f) = (q : ℝ) • g f
          simp only [Rat.cast_smul_eq_qsmul, map_smul]) }
  have hrOne : Lr 1 = 1 := (hEq 1).trans hOne
  have hConst (c : ℝ) : Lr (ContinuousMap.const X c) = c := by
    have h : ContinuousMap.const X c = c • (1 : C(X, ℝ)) := by ext x; simp
    rw [h, map_smul, hrOne, smul_eq_mul, mul_one]
  have hpos {f : C(X, ℝ)} (hf : 0 ≤ f) : 0 ≤ Lr f := by
    have hSup : ‖ContinuousMap.const X ‖f‖ - f‖ ≤ ‖f‖ := by
      apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
      intro x
      have hx : 0 ≤ f x := hf x
      have hx' : f x ≤ ‖f‖ := (le_abs_self _).trans (f.norm_coe_le_norm x)
      rw [ContinuousMap.sub_apply, ContinuousMap.const_apply, Real.norm_of_nonneg (sub_nonneg.mpr hx')]
      exact sub_le_self _ hx
    have hb : ‖Lr (ContinuousMap.const X ‖f‖ - f)‖ ≤ ‖f‖ :=
      (hgNorm _).trans hSup
    have hval := (le_abs_self (Lr (ContinuousMap.const X ‖f‖ - f))).trans hb
    rw [map_sub, hConst] at hval
    linarith only [hval]
  let L : PositiveFunctional X :=
    { toPositiveLinearMap :=
        { toLinearMap := Lr
          monotone' := fun f g hfg => by
            have hsub : 0 ≤ g - f := ContinuousMap.le_def.mpr fun x => by
              change 0 ≤ g x - f x
              exact sub_nonneg.mpr (hfg x)
            have h := hpos hsub
            rw [map_sub] at h
            exact sub_nonneg.mp h }
      map_one := hrOne }
  exact ⟨L, g.continuous, hgNorm, hEq⟩

variable {Z ι : Type*} [MeasurableSpace Z]

/-- Measurable densities on the rational readouts, with the separate
almost-everywhere identities delivered by the pairing representation. -/
public structure RationalReadoutDensities (μ : Measure Z) (A : Subalgebra ℚ C(X, ℝ))
    (ι : Type*) where
  density : ι → A → Z → ℝ
  measurable_density : ∀ i a, Measurable (density i a)
  norm_ae : ∀ i a, ∀ᵐ z ∂μ, ‖density i a z‖ ≤ ‖(a : C(X, ℝ))‖
  add_ae : ∀ i a b, ∀ᵐ z ∂μ, density i (a + b) z = density i a z + density i b z
  smul_ae : ∀ i (r : ℚ) a, ∀ᵐ z ∂μ, density i (r • a) z = r • density i a z
  one_ae : ∀ i, ∀ᵐ z ∂μ, density i 1 z = 1
  nonneg_ae : ∀ i (a : A), 0 ≤ (a : C(X, ℝ)) → ∀ᵐ z ∂μ, 0 ≤ density i a z

namespace RationalReadoutDensities

variable {μ : Measure Z} {A : Subalgebra ℚ C(X, ℝ)}

/-- Simultaneous pointwise contracts for all phases and all rational readouts. -/
@[expose] public def Good (D : RationalReadoutDensities μ A ι) (z : Z) : Prop :=
  (∀ i a, ‖D.density i a z‖ ≤ ‖(a : C(X, ℝ))‖) ∧
  (∀ i a b, D.density i (a + b) z = D.density i a z + D.density i b z) ∧
  (∀ i (r : ℚ) a, D.density i (r • a) z = r • D.density i a z) ∧
  (∀ i, D.density i 1 z = 1) ∧
  (∀ i (a : {a : A // 0 ≤ (a : C(X, ℝ))}), 0 ≤ D.density i a.1 z)

public theorem measurableSet_good [Countable ι] [Countable A]
    (D : RationalReadoutDensities μ A ι) : MeasurableSet {z | D.Good z} := by
  classical
  unfold Good
  simp only [ofPred_and, ofPred_forall]
  refine (MeasurableSet.iInter fun i => MeasurableSet.iInter fun a =>
    measurableSet_le (D.measurable_density i a).norm measurable_const).inter ?_
  refine (MeasurableSet.iInter fun i => MeasurableSet.iInter fun a => MeasurableSet.iInter fun b =>
    measurableSet_eq_fun (D.measurable_density i (a + b))
      ((D.measurable_density i a).add (D.measurable_density i b))).inter ?_
  refine (MeasurableSet.iInter fun i => MeasurableSet.iInter fun r => MeasurableSet.iInter fun a =>
    measurableSet_eq_fun (D.measurable_density i (r • a))
      ((D.measurable_density i a).const_smul r)).inter ?_
  refine (MeasurableSet.iInter fun i => measurableSet_eq_fun (D.measurable_density i 1)
    measurable_const).inter ?_
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun a =>
    measurableSet_le measurable_const (D.measurable_density i a.1)

/-- Countably many identities give one common full-measure set. -/
public theorem ae_good [Countable ι] [Countable A]
    (D : RationalReadoutDensities μ A ι) : ∀ᵐ z ∂μ, D.Good z := by
  have hp (i : ι) (a : {a : A // 0 ≤ (a : C(X, ℝ))}) : ∀ᵐ z ∂μ, 0 ≤ D.density i a.1 z :=
    D.nonneg_ae i a.1 a.2
  filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr (D.norm_ae i),
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun a => ae_all_iff.mpr (D.add_ae i a),
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun r => ae_all_iff.mpr (D.smul_ae i r),
    ae_all_iff.mpr D.one_ae, ae_all_iff.mpr fun i => ae_all_iff.mpr (hp i)] with _ hn ha hs h1 hpos
  exact ⟨hn, ha, hs, h1, hpos⟩

/-- On the common set the density evaluations form a rational linear functional. -/
@[expose] public def rationalFunctional (D : RationalReadoutDensities μ A ι)
    (i : ι) {z : Z} (hz : D.Good z) : A →ₗ[ℚ] ℝ where
  toFun a := D.density i a z
  map_add' := hz.2.1 i
  map_smul' := hz.2.2.1 i

/-- The common full-measure set supports positive normalized extensions.
Off that set the extension is evaluation at the fixed reference state.
For each continuous readout the resulting function of the conditioning
variable is measurable. -/
public theorem exists_conditional_functionals [Countable ι]
    (D : RationalReadoutDensities μ A ι) (hCount : (A : Set C(X, ℝ)).Countable)
    (hA : Dense (A : Set C(X, ℝ))) (x₀ : X) :
    ∃ S : Set Z, MeasurableSet S ∧ (∀ᵐ z ∂μ, z ∈ S) ∧
      ∃ L : ι → Z → PositiveFunctional X,
        (∀ i z, z ∈ S → ∀ a : A, L i z (a : C(X, ℝ)) = D.density i a z) ∧
        (∀ i z, z ∉ S → L i z = PositiveFunctional.eval x₀) ∧
        (∀ (i : ι) (f : C(X, ℝ)), Measurable (fun z => L i z f)) ∧
        (∀ i z f, ‖L i z f‖ ≤ ‖f‖) := by
  classical
  let _ : Countable A := hCount.to_subtype
  let S : Set Z := {z | D.Good z}
  have hS : MeasurableSet S := D.measurableSet_good
  have hEach (i : ι) (z : S) : ∃ L : PositiveFunctional X,
      Continuous (fun f : C(X, ℝ) => L f) ∧
      (∀ f : C(X, ℝ), ‖L f‖ ≤ ‖f‖) ∧ ∀ a : A, L (a : C(X, ℝ)) = D.density i a z :=
    exists_positiveFunctional_of_rational A hA (D.rationalFunctional i z.2)
      (fun a => z.2.1 i a) (z.2.2.2.2.1 i)
  choose localL hCont hNorm hEq using hEach
  let L (i : ι) (z : Z) := if h : z ∈ S then localL i ⟨z, h⟩ else PositiveFunctional.eval x₀
  have hOn (i : ι) (z : Z) (hz : z ∈ S) (a : A) :
      L i z (a : C(X, ℝ)) = D.density i a z := by
    simp only [L, dite_eq_left hz, hEq]
  have hOff (i : ι) (z : Z) (hz : z ∉ S) : L i z = PositiveFunctional.eval x₀ := by
    simp [L, hz]
  refine ⟨S, hS, D.ae_good, L, hOn, hOff, ?_, ?_⟩
  · intro i f
    obtain ⟨seq, hSeq, hLim⟩ := mem_closure_iff_seq_limit.mp (hA f)
    let a (k : ℕ) : A := ⟨seq k, hSeq k⟩
    let g (k : ℕ) (z : Z) := if z ∈ S then D.density i (a k) z else seq k x₀
    have hg (k : ℕ) : Measurable (g k) :=
      Measurable.ite hS (D.measurable_density i (a k)) measurable_const
    refine measurable_of_tendsto_metrizable hg ?_
    apply tendsto_pi_nhds.mpr
    intro z
    by_cases hz : z ∈ S
    · have h := (hCont i ⟨z, hz⟩).continuousAt.tendsto.comp hLim
      simpa only [g, ite_eq_left hz, L, dite_eq_left hz, ← hEq i ⟨z, hz⟩, a, Function.comp_def] using h
    · have hEval : Continuous (fun f : C(X, ℝ) => f x₀) := continuous_eval_const x₀
      have h := hEval.continuousAt.tendsto.comp hLim
      simpa only [g, ite_eq_right hz, hOff i z hz, PositiveFunctional.eval_apply, Function.comp_def] using h
  · intro i z f
    by_cases hz : z ∈ S
    · simpa only [L, dite_eq_left hz] using hNorm i ⟨z, hz⟩ f
    · rw [hOff i z hz, PositiveFunctional.eval_apply]
      exact f.norm_coe_le_norm x₀

end RationalReadoutDensities
end C2Riemannian
