module

public import C2Riemannian.PhaseTangentialIBP
public import C2Riemannian.PhysicalPhaseWeight
import Mathlib.Analysis.InnerProductSpace.LinearMap

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions Topology

namespace C2Riemannian.PhysicalLayerRow

variable {Q : Set Plane} {directions : PhysicalDirections} {s δ : ℝ}
  {layer : IdealLayer} {p : PhysicalPrefix Q} {next : ℕ → PhysicalPrefix Q}
  (row : PhysicalLayerRow directions s δ layer p next) (i : p.Active) (sign : Bool)

public theorem measurable_phaseWeight (k : ℕ) : Measurable (row.phaseWeight i sign k) :=
  measurable_const.mul ((measurable_phaseIndicator (isOpen_phaseInterval sign _)).comp
    (measurable_const.mul (innerSL ℝ (directions.normal layer s)).continuous.measurable))

public theorem norm_phaseWeight_le (k : ℕ) (x : Plane) : ‖row.phaseWeight i sign k x‖ ≤ 2 := by
  let z := (row.frequencyContract.frequency k : ℝ) * inner ℝ (directions.normal layer s) x
  have h := phaseIndicator_mem_Icc (phaseInterval sign (row.frequencyContract.width k)) z
  change ‖2 * phaseIndicator (phaseInterval sign (row.frequencyContract.width k)) z‖ ≤ 2
  rw [Real.norm_of_nonneg (mul_nonneg (by norm_num) h.1)]
  exact mul_le_of_le_one_right (by norm_num) h.2

public theorem phaseWeight_invariant {τ : Plane} (hτ : inner ℝ (directions.normal layer s) τ = 0)
    (k : ℕ) (x : Plane) (t : ℝ) : row.phaseWeight i sign k (x + t • τ) =
      row.phaseWeight i sign k x := by
  exact phase_invariant_of_linearForm
    (fun q => 2 * phaseIndicator (phaseInterval sign (row.frequencyContract.width k))
      (row.frequencyContract.frequency k * q)) (innerSL ℝ (directions.normal layer s)) hτ x t

/-- The gradient term of tangential integration by parts converges on the actual
parent plateau along any strictly increasing sequence of layer frequencies. -/
public theorem phaseWeight_gradient_test_limit
    (hn : directions.normal layer s ≠ 0) (k : ℕ → ℕ) (hk : StrictMono k)
    (τ : Plane) (φ : 𝓓(parentOpen p i, ℝ)) {g : ℕ → Plane → ℝ} {g₀ : Plane → ℝ}
    (hi : ∀ j, LocallyIntegrableOn (g j) (parentOpen p i) volume)
    (hi₀ : LocallyIntegrableOn g₀ (parentOpen p i) volume)
    {d : ℕ → ℝ} (hd : Tendsto d atTop (𝓝 0))
    (hg : ∀ j, ∀ x ∈ tsupport (φ : Plane → ℝ), ‖g j x - g₀ x‖ ≤ d j) :
    Tendsto (fun j => ∫ x in p.platform i.1, row.phaseWeight i sign (k j) x *
      (lineDeriv ℝ (φ : Plane → ℝ) x τ * g j x)) atTop
      (𝓝 (∫ x in p.platform i.1, lineDeriv ℝ (φ : Plane → ℝ) x τ * g₀ x)) := by
  exact phase_weighted_gradient_tendsto (a := fun j => row.phaseWeight i sign (k j))
    φ τ (by norm_num) (fun j => Eventually.of_forall (row.norm_phaseWeight_le i sign (k j)))
    (fun j => (row.measurable_phaseWeight i sign (k j)).aestronglyMeasurable)
    (fun _ hγ => row.phaseWeight_test_limit i sign hn k hk hγ) hi hi₀ hd hg

/-- A scalar tangential Hessian readout of a physical phase has the same conditional
first moment as the limiting tangential Hessian. -/
public theorem conditional_phase_tangent_ae
    (hn : directions.normal layer s ≠ 0) (k : ℕ → ℕ) (hk : StrictMono k)
    {τ : Plane} (hτ : inner ℝ (directions.normal layer s) τ = 0)
    {g h : ℕ → Plane → ℝ} {g₀ h₀ b : Plane → ℝ}
    (hw : ∀ j, TauCeti.HasWeakLineDerivOn volume (parentOpen p i) (g j) (h j) τ)
    (hw₀ : TauCeti.HasWeakLineDerivOn volume (parentOpen p i) g₀ h₀ τ)
    (hbi : LocallyIntegrableOn b (parentOpen p i) volume)
    (hu : ∀ φ : 𝓓(parentOpen p i, ℝ), ∃ d : ℕ → ℝ, Tendsto d atTop (𝓝 0) ∧
      ∀ j, ∀ x ∈ tsupport (φ : Plane → ℝ), ‖g j x - g₀ x‖ ≤ d j)
    (hmean : ∀ φ : 𝓓(parentOpen p i, ℝ),
      Tendsto (fun j => ∫ x in p.platform i.1, row.phaseWeight i sign (k j) x * (φ x * h j x))
        atTop (𝓝 (∫ x in p.platform i.1, φ x * b x))) :
    b =ᵐ[volume.restrict (p.platform i.1)] h₀ := by
  apply ae_eq_of_test_integrals (U := parentOpen p i) hbi hw₀.locallyIntegrableOn_deriv
  intro φ
  have hparent : (parentOpen p i : Set Plane) = p.platform i.1 := rfl
  obtain ⟨d, hd, hdom⟩ := hu φ
  have hg := row.phaseWeight_gradient_test_limit i sign hn k hk τ φ
    (fun j => (hw j).locallyIntegrableOn) hw₀.locallyIntegrableOn hd hdom
  have hseq (j : ℕ) : (∫ x in p.platform i.1, row.phaseWeight i sign (k j) x * (φ x * h j x)) =
      -∫ x in p.platform i.1, row.phaseWeight i sign (k j) x *
        (lineDeriv ℝ (φ : Plane → ℝ) x τ * g j x) := by
    have hh := phase_tangential_ibp (hw j)
      (row.measurable_phaseWeight i sign (k j)).aestronglyMeasurable (C := 2) (by norm_num)
      (Eventually.of_forall (row.norm_phaseWeight_le i sign (k j)))
      (row.phaseWeight_invariant i sign hτ (k j)) φ
    have he := congrArg Neg.neg hh.symm
    simpa only [hparent, smul_eq_mul, neg_neg] using he
  have he := tendsto_nhds_unique_of_eventuallyEq (hmean φ) hg.neg (Eventually.of_forall hseq)
  have hi := hw₀.integral_lineDeriv_smul_eq_neg_integral_smul φ
  rw [← TauCeti.setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul φ τ,
    ← TauCeti.setIntegral_smul_eq_integral_smul φ] at hi
  simp only [hparent, smul_eq_mul] at hi ⊢
  rw [he, hi, neg_neg]

end C2Riemannian.PhysicalLayerRow
