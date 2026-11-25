module

public import C2Riemannian.ConditionalDensityAssembly
public import C2Riemannian.ConditionalPairingLimits
public import C2Riemannian.CountableReadouts

/-! # One common sequence of probability pairings for all continuous readouts (M31) -/

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped Topology

namespace C2Riemannian

variable {X Z ι : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Z]
  {μ : Measure Z} [IsFiniteMeasure μ] [IsSeparable μ] [Countable ι]

/-- One diagonal subsequence supplies positive normalized conditionals for
all phases. Every continuous readout is measurable in the conditioning
variable, and all (L^1) tests converge to its representing-measure pairing. -/
public theorem exists_conditional_pairing_subsequence
    (A : Subalgebra ℚ C(X, ℝ)) (hCount : (A : Set C(X, ℝ)).Countable)
    (hDense : Dense (A : Set C(X, ℝ))) (x₀ : X)
    (state : ι → ℕ → Z → X) (phase : ι → ℕ → Z → ℝ)
    (hs : ∀ i k, Measurable (state i k)) (hp : ∀ i k, AEStronglyMeasurable (phase i k) μ)
    (hb : ∀ i k, ∀ᵐ z ∂μ, ‖phase i k z‖ ≤ 2)
    (hNonneg : ∀ i k, ∀ᵐ z ∂μ, 0 ≤ phase i k z)
    (hUnit : ∀ i (γ : Lp ℝ 1 μ),
      Tendsto (fun k => ∫ z, phase i k z * γ z ∂μ) atTop (𝓝 (∫ z, γ z ∂μ)))
    (base : ℕ → ℕ) (hBase : StrictMono base) :
    ∃ (σ : ℕ → ℕ) (L : ι → Z → PositiveFunctional X), StrictMono σ ∧
      (∀ (i : ι) (f : C(X, ℝ)), Measurable (fun z => L i z f)) ∧
      ∀ (i : ι) (f : C(X, ℝ)) (γ : Lp ℝ 1 μ),
        Tendsto (fun k => ∫ z, phase i (base (σ k)) z * f (state i (base (σ k)) z) * γ z ∂μ)
          atTop (𝓝 (∫ z, (∫ x, f x ∂(L i z).representingMeasure) * γ z ∂μ)) := by
  obtain ⟨σ, D, hσ, hD⟩ :=
    exists_diagonal_rationalReadoutDensities A hCount state phase hs hp hb hNonneg hUnit base hBase
  obtain ⟨S, _, hSAe, L, hAgree, _, hMeas, _⟩ :=
    D.exists_conditional_functionals hCount hDense x₀
  refine ⟨σ, L, hσ, hMeas, fun i f γ => ?_⟩
  apply PositiveFunctional.conditional_pairing_tendsto_of_dense hDense (L i)
    (fun k => state i (base (σ k))) (fun k => phase i (base (σ k)))
    (fun k => hs i (base (σ k))) (fun k => hp i (base (σ k)))
    (fun k => hb i (base (σ k))) (fun g _ => hMeas i g) _ f γ
  intro G hG γ'
  let g : A := ⟨G, hG⟩
  have heq : (∫ z, γ' z * D.density i g z ∂μ) = ∫ z, L i z G * γ' z ∂μ := by
    apply integral_congr_ae
    filter_upwards [hSAe] with z hz
    rw [← hAgree i z hz g, mul_comm]
  rw [← heq]
  exact hD i g γ'

/-- The separable compact-state version chooses the rational algebra
automatically, before taking the common subsequence. -/
public theorem exists_conditional_pairing_subsequence_of_secondCountable
    [SecondCountableTopology X] [LocallyCompactSpace X] (x₀ : X)
    (state : ι → ℕ → Z → X) (phase : ι → ℕ → Z → ℝ)
    (hs : ∀ i k, Measurable (state i k)) (hp : ∀ i k, AEStronglyMeasurable (phase i k) μ)
    (hb : ∀ i k, ∀ᵐ z ∂μ, ‖phase i k z‖ ≤ 2)
    (hNonneg : ∀ i k, ∀ᵐ z ∂μ, 0 ≤ phase i k z)
    (hUnit : ∀ i (γ : Lp ℝ 1 μ),
      Tendsto (fun k => ∫ z, phase i k z * γ z ∂μ) atTop (𝓝 (∫ z, γ z ∂μ)))
    (base : ℕ → ℕ) (hBase : StrictMono base) :
    ∃ (σ : ℕ → ℕ) (L : ι → Z → PositiveFunctional X), StrictMono σ ∧
      (∀ (i : ι) (f : C(X, ℝ)), Measurable (fun z => L i z f)) ∧
      ∀ (i : ι) (f : C(X, ℝ)) (γ : Lp ℝ 1 μ),
        Tendsto (fun k => ∫ z, phase i (base (σ k)) z * f (state i (base (σ k)) z) * γ z ∂μ)
          atTop (𝓝 (∫ z, (∫ x, f x ∂(L i z).representingMeasure) * γ z ∂μ)) := by
  obtain ⟨A, hCount, hDense, _⟩ := exists_countable_dense_readout_algebra (fun _ : ℕ => (1 : C(X, ℝ)))
  exact exists_conditional_pairing_subsequence A hCount hDense x₀ state phase hs hp hb hNonneg hUnit base hBase

end C2Riemannian
