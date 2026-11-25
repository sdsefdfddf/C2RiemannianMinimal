module

public import C2Riemannian.ConditionalFunctionals
public import C2Riemannian.PairingDensities
public import C2Riemannian.PairingOperators
import Mathlib.Logic.Encodable.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Simultaneous rational densities of conditional pairing limits (M28–M30) -/

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped Topology

namespace C2Riemannian

variable {X Z ι : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Z]
  {μ : Measure Z} [IsFiniteMeasure μ]

/-- Pairing limits of nonnegative phase multipliers, with constant readout
limit one, supply the rational density conditions. The sharp bound on each
density comes from comparing the prelimit pairings against constant readouts. -/
public theorem exists_rationalReadoutDensities_of_pairingLimits
    (A : Subalgebra ℚ C(X, ℝ)) (state : ι → ℕ → Z → X) (phase : ι → ℕ → Z → ℝ)
    (hs : ∀ i k, Measurable (state i k)) (hp : ∀ i k, AEStronglyMeasurable (phase i k) μ)
    (hb : ∀ i k, ∀ᵐ z ∂μ, ‖phase i k z‖ ≤ 2)
    (hNonneg : ∀ i k, ∀ᵐ z ∂μ, 0 ≤ phase i k z)
    (hUnit : ∀ i (γ : Lp ℝ 1 μ),
      Tendsto (fun k => ∫ z, phase i k z * γ z ∂μ) atTop (𝓝 (∫ z, γ z ∂μ)))
    (J : ι → A → (Lp ℝ 1 μ →L[ℝ] ℝ))
    (hSeq : ∀ i (a : A) (γ : Lp ℝ 1 μ),
      Tendsto (fun k => ∫ z, phase i k z * (a : C(X, ℝ)) (state i k z) * γ z ∂μ) atTop (𝓝 (J i a γ))) :
    ∃ D : RationalReadoutDensities μ A ι, ∀ i a (γ : Lp ℝ 1 μ),
      J i a γ = ∫ z, γ z * D.density i a z ∂μ := by
  classical
  choose g hMeas hBound hRep using fun i (a : A) => exists_l1_pairing_density (J i a)
  let B (a : A) := ‖(a : C(X, ℝ))‖
  let Raw (i : ι) (a : A) (k : ℕ) (γ : Lp ℝ 1 μ) :=
    ∫ z, phase i k z * (a : C(X, ℝ)) (state i k z) * γ z ∂μ
  have hRawInt (i : ι) (a : A) (k : ℕ) (γ : Lp ℝ 1 μ) :
      Integrable (fun z => phase i k z * (a : C(X, ℝ)) (state i k z) * γ z) μ := by
    apply (L1.integrable_coeFn γ).bdd_mul (c := 2 * B a) ((hp i k).mul
      (((a : C(X, ℝ)).continuous.measurable.comp (hs i k)).aestronglyMeasurable))
    filter_upwards [hb i k] with z hz
    change ‖phase i k z * (a : C(X, ℝ)) (state i k z)‖ ≤ 2 * B a
    rw [norm_mul]
    exact mul_le_mul hz ((a : C(X, ℝ)).norm_coe_le_norm _) (norm_nonneg _) (by norm_num)
  have hPhaseInt (i : ι) (k : ℕ) (γ : Lp ℝ 1 μ) :
      Integrable (fun z => phase i k z * γ z) μ :=
    (L1.integrable_coeFn γ).bdd_mul (hp i k) (hb i k)
  have hGInt (i : ι) (a : A) : Integrable (g i a) μ :=
    Integrable.of_bound (hMeas i a).aestronglyMeasurable ‖J i a‖
      (by simpa only [Real.norm_eq_abs] using hBound i a)
  have hTestInt (i : ι) (a : A) (γ : Lp ℝ 1 μ) :
      Integrable (fun z => γ z * g i a z) μ := by
    have h := (L1.integrable_coeFn γ).bdd_mul (hMeas i a).aestronglyMeasurable
      (c := ‖J i a‖) (by simpa only [Real.norm_eq_abs] using hBound i a)
    simpa only [mul_comm] using h
  have hOne (i : ι) (γ : Lp ℝ 1 μ) : J i 1 γ = ∫ z, γ z ∂μ :=
    tendsto_nhds_unique (hSeq i 1 γ) (by
      simpa only [Subalgebra.coe_one, ContinuousMap.one_apply, mul_one] using hUnit i γ)
  have hAdd (i : ι) (a b : A) (γ : Lp ℝ 1 μ) :
      J i (a + b) γ = J i a γ + J i b γ := by
    refine tendsto_nhds_unique (hSeq i (a + b) γ) (((hSeq i a γ).add (hSeq i b γ)).congr ?_)
    intro k
    change Raw i a k γ + Raw i b k γ = Raw i (a + b) k γ
    unfold Raw
    rw [← integral_add (hRawInt i a k γ) (hRawInt i b k γ)]
    apply integral_congr_ae
    filter_upwards with z
    simp only [Subalgebra.coe_add, ContinuousMap.add_apply]
    ring
  have hSmul (i : ι) (r : ℚ) (a : A) (γ : Lp ℝ 1 μ) :
      J i (r • a) γ = (r : ℝ) * J i a γ := by
    refine tendsto_nhds_unique (hSeq i (r • a) γ) (((hSeq i a γ).const_mul (r : ℝ)).congr ?_)
    intro k
    change (r : ℝ) * Raw i a k γ = Raw i (r • a) k γ
    unfold Raw
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with z
    simp only [Subalgebra.coe_smul, ContinuousMap.smul_apply, ← Rat.cast_smul_eq_qsmul ℝ, smul_eq_mul]
    ring
  have hPositive (i : ι) (a : A) (ha : 0 ≤ (a : C(X, ℝ))) (γ : Lp ℝ 1 μ)
      (hγ : ∀ᵐ z ∂μ, 0 ≤ γ z) : 0 ≤ J i a γ := by
    apply ge_of_tendsto (hSeq i a γ)
    exact Eventually.of_forall fun k => by
      apply integral_nonneg_of_ae
      filter_upwards [hNonneg i k, hγ] with z hz hzγ
      exact mul_nonneg (mul_nonneg hz (ha (state i k z))) hzγ
  have hUpper (i : ι) (a : A) (γ : Lp ℝ 1 μ) (hγ : ∀ᵐ z ∂μ, 0 ≤ γ z) :
      J i a γ ≤ B a * ∫ z, γ z ∂μ := by
    apply le_of_tendsto_of_tendsto' (hSeq i a γ) ((hUnit i γ).const_mul (B a))
    intro k
    rw [← integral_const_mul]
    apply integral_mono_ae (hRawInt i a k γ) ((hPhaseInt i k γ).const_mul (B a))
    filter_upwards [hNonneg i k, hγ] with z hz hzγ
    have h : (a : C(X, ℝ)) (state i k z) ≤ B a :=
      (le_abs_self _).trans ((a : C(X, ℝ)).norm_coe_le_norm _)
    calc
      _ ≤ phase i k z * B a * γ z :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hz) hzγ
      _ = _ := by ring
  have hLower (i : ι) (a : A) (γ : Lp ℝ 1 μ) (hγ : ∀ᵐ z ∂μ, 0 ≤ γ z) :
      (-B a) * (∫ z, γ z ∂μ) ≤ J i a γ := by
    apply le_of_tendsto_of_tendsto' ((hUnit i γ).const_mul (-B a)) (hSeq i a γ)
    intro k
    rw [← integral_const_mul]
    apply integral_mono_ae ((hPhaseInt i k γ).const_mul (-B a)) (hRawInt i a k γ)
    filter_upwards [hNonneg i k, hγ] with z hz hzγ
    have h : -B a ≤ (a : C(X, ℝ)) (state i k z) :=
      (abs_le.mp ((a : C(X, ℝ)).norm_coe_le_norm _)).1
    calc
      _ = phase i k z * (-B a) * γ z := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hz) hzγ
  have hSharp (i : ι) (a : A) : ∀ᵐ z ∂μ, ‖g i a z‖ ≤ B a := by
    let U := B a • J i 1 - J i a
    let V := J i a + B a • J i 1
    have hURep (γ : Lp ℝ 1 μ) : U γ = ∫ z, γ z * (B a - g i a z) ∂μ := by
      change B a * J i 1 γ - J i a γ = _
      rw [hOne i γ, hRep i a γ, ← integral_const_mul,
        ← integral_sub ((L1.integrable_coeFn γ).const_mul (B a)) (hTestInt i a γ)]
      apply integral_congr_ae
      filter_upwards with z
      ring
    have hVRep (γ : Lp ℝ 1 μ) : V γ = ∫ z, γ z * (g i a z + B a) ∂μ := by
      change J i a γ + B a * J i 1 γ = _
      rw [hOne i γ, hRep i a γ, ← integral_const_mul,
        ← integral_add (hTestInt i a γ) ((L1.integrable_coeFn γ).const_mul (B a))]
      apply integral_congr_ae
      filter_upwards with z
      ring
    have hu := l1_pairing_density_ae_nonneg ((integrable_const (B a)).sub (hGInt i a)) hURep
      (fun γ hγ => by
        change 0 ≤ B a * J i 1 γ - J i a γ
        rw [hOne i γ]
        exact sub_nonneg.mpr (hUpper i a γ hγ))
    have hv := l1_pairing_density_ae_nonneg ((hGInt i a).add (integrable_const (B a))) hVRep
      (fun γ hγ => by
        change 0 ≤ J i a γ + B a * J i 1 γ
        rw [hOne i γ]
        have h := hLower i a γ hγ
        linarith only [h])
    filter_upwards [hu, hv] with z hzu hzv
    change 0 ≤ B a - g i a z at hzu
    change 0 ≤ g i a z + B a at hzv
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith only [hzv], sub_nonneg.mp hzu⟩
  let D : RationalReadoutDensities μ A ι :=
    { density := g
      measurable_density := hMeas
      norm_ae := hSharp
      add_ae := fun i a b => by
        apply l1_pairing_density_ae_unique (hGInt i (a + b)) ((hGInt i a).add (hGInt i b)) (hRep i (a + b))
        intro γ
        rw [hAdd i a b γ, hRep i a γ, hRep i b γ, ← integral_add (hTestInt i a γ) (hTestInt i b γ)]
        apply integral_congr_ae
        filter_upwards with z
        simp [mul_add]
      smul_ae := fun i r a => by
        have hI : Integrable (fun z => (r : ℝ) * g i a z) μ := (hGInt i a).const_mul r
        have hEq : g i (r • a) =ᵐ[μ] fun z => (r : ℝ) * g i a z := by
          apply l1_pairing_density_ae_unique (hGInt i (r • a)) hI (hRep i (r • a))
          intro γ
          rw [hSmul i r a γ, hRep i a γ, ← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with z
          ring
        filter_upwards [hEq] with z hz
        simpa only [Rat.smul_def] using hz
      one_ae := fun i => l1_pairing_density_ae_one (hGInt i 1) (hRep i 1) (hOne i)
      nonneg_ae := fun i a ha => l1_pairing_density_ae_nonneg (hGInt i a) (hRep i a) (hPositive i a ha) }
  exact ⟨D, hRep⟩

/-- Extract one subsequence for all phases and rational readouts, and give its
limits measurable densities that meet the common pointwise contract. -/
public theorem exists_diagonal_rationalReadoutDensities [IsSeparable μ] [Countable ι]
    (A : Subalgebra ℚ C(X, ℝ)) (hCount : (A : Set C(X, ℝ)).Countable)
    (state : ι → ℕ → Z → X) (phase : ι → ℕ → Z → ℝ)
    (hs : ∀ i k, Measurable (state i k)) (hp : ∀ i k, AEStronglyMeasurable (phase i k) μ)
    (hb : ∀ i k, ∀ᵐ z ∂μ, ‖phase i k z‖ ≤ 2)
    (hNonneg : ∀ i k, ∀ᵐ z ∂μ, 0 ≤ phase i k z)
    (hUnit : ∀ i (γ : Lp ℝ 1 μ),
      Tendsto (fun k => ∫ z, phase i k z * γ z ∂μ) atTop (𝓝 (∫ z, γ z ∂μ)))
    (base : ℕ → ℕ) (hBase : StrictMono base) :
    ∃ (σ : ℕ → ℕ) (D : RationalReadoutDensities μ A ι), StrictMono σ ∧
      ∀ i (a : A) (γ : Lp ℝ 1 μ),
        Tendsto (fun k => ∫ z, phase i (base (σ k)) z *
          (a : C(X, ℝ)) (state i (base (σ k)) z) * γ z ∂μ) atTop
            (𝓝 (∫ z, γ z * D.density i a z ∂μ)) := by
  classical
  let _ : Countable A := hCount.to_subtype
  let _ : Encodable (ι × A) := Encodable.ofCountable (ι × A)
  let u (j k : ℕ) (z : Z) : ℝ :=
    match Encodable.decode (α := ι × A) j with
    | some (i, a) => phase i k z * (a : C(X, ℝ)) (state i k z)
    | none => 0
  let B (j : ℕ) : ℝ :=
    match Encodable.decode (α := ι × A) j with
    | some (_, a) => 2 * ‖(a : C(X, ℝ))‖
    | none => 0
  have hB (j : ℕ) : 0 ≤ B j := by
    unfold B
    split
    · positivity
    · exact le_rfl
  have hu (j k : ℕ) : AEStronglyMeasurable (u j k) μ := by
    cases hDecode : Encodable.decode (α := ι × A) j with
    | none =>
      simp only [u, hDecode]
      exact aestronglyMeasurable_const
    | some p =>
      simp only [u, hDecode]
      change AEStronglyMeasurable (phase p.1 k * ((p.2 : C(X, ℝ)) ∘ state p.1 k)) μ
      exact (hp p.1 k).mul (((p.2 : C(X, ℝ)).continuous.measurable.comp (hs p.1 k)).aestronglyMeasurable)
  have hub (j k : ℕ) : ∀ᵐ z ∂μ, ‖u j k z‖ ≤ B j := by
    cases hDecode : Encodable.decode (α := ι × A) j with
    | none => simp [u, B, hDecode]
    | some p =>
      filter_upwards [hb p.1 k] with z hz
      simp only [u, B, hDecode, norm_mul]
      exact mul_le_mul hz ((p.2 : C(X, ℝ)).norm_coe_le_norm _) (norm_nonneg _) (by norm_num)
  obtain ⟨σ, F, hσ, _, hF⟩ := exists_L1_pairing_limits u B hB hu hub base hBase
  let J (i : ι) (a : A) := F (Encodable.encode (i, a))
  have hSeq (i : ι) (a : A) (γ : Lp ℝ 1 μ) :
      Tendsto (fun k => ∫ z, phase i (base (σ k)) z *
        (a : C(X, ℝ)) (state i (base (σ k)) z) * γ z ∂μ) atTop (𝓝 (J i a γ)) := by
    simpa only [u, J, Encodable.encodek] using hF (Encodable.encode (i, a)) γ
  have hTop : Tendsto (fun k => base (σ k)) atTop atTop :=
    hBase.tendsto_atTop.comp hσ.tendsto_atTop
  obtain ⟨D, hD⟩ := exists_rationalReadoutDensities_of_pairingLimits A
    (fun i k => state i (base (σ k))) (fun i k => phase i (base (σ k)))
    (fun i k => hs i (base (σ k))) (fun i k => hp i (base (σ k)))
    (fun i k => hb i (base (σ k))) (fun i k => hNonneg i (base (σ k)))
    (fun i γ => (hUnit i γ).comp hTop) J hSeq
  refine ⟨σ, D, hσ, fun i a γ => ?_⟩
  rw [← hD i a γ]
  exact hSeq i a γ

end C2Riemannian
