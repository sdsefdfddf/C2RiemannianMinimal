module

public import C2Riemannian.DiagonalPairings
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

set_option autoImplicit false

open MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology

namespace C2Riemannian

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

@[expose] public noncomputable def pairingLinear (u : X → ℝ) {B : ℝ}
    (hu : AEStronglyMeasurable u μ) (hb : ∀ᵐ x ∂μ, ‖u x‖ ≤ B) : Lp ℝ 1 μ →ₗ[ℝ] ℝ where
  toFun f := ∫ x, u x * f x ∂μ
  map_add' f g := by
    have hi (v : Lp ℝ 1 μ) : Integrable (fun x => u x * v x) μ :=
      (L1.integrable_coeFn v).bdd_mul hu hb
    rw [← integral_add (hi f) (hi g)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add f g] with x hx
    rw [hx, Pi.add_apply, mul_add]
  map_smul' c f := by
    simp only [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c f] with x hx
    rw [hx, Pi.smul_apply, smul_eq_mul, mul_left_comm]

public theorem pairingLinear_bound {u : X → ℝ} {B : ℝ}
    (hu : AEStronglyMeasurable u μ) (hb : ∀ᵐ x ∂μ, ‖u x‖ ≤ B) (f : Lp ℝ 1 μ) :
    ‖pairingLinear u hu hb f‖ ≤ B * ‖f‖ := by
  change ‖∫ x, u x * f x ∂μ‖ ≤ _
  have hi : Integrable (fun x => u x * f x) μ := (L1.integrable_coeFn f).bdd_mul hu hb
  calc
    _ ≤ ∫ x, ‖u x * f x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, B * ‖f x‖ ∂μ := by
      apply integral_mono_ae hi.norm ((L1.integrable_coeFn f).norm.const_mul B)
      filter_upwards [hb] with x hx
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    _ = B * ‖f‖ := by rw [integral_const_mul, L1.norm_eq_integral_norm]

/-- Integration against an essentially bounded scalar readout is continuous on L¹. -/
@[expose] public noncomputable def boundedPairing (u : X → ℝ) {B : ℝ}
    (hu : AEStronglyMeasurable u μ) (hb : ∀ᵐ x ∂μ, ‖u x‖ ≤ B) : Lp ℝ 1 μ →L[ℝ] ℝ :=
  (pairingLinear u hu hb).mkContinuous B (pairingLinear_bound hu hb)

public theorem boundedPairing_apply {u : X → ℝ} {B : ℝ}
    (hu : AEStronglyMeasurable u μ) (hb : ∀ᵐ x ∂μ, ‖u x‖ ≤ B) (f : Lp ℝ 1 μ) :
    boundedPairing u hu hb f = ∫ x, u x * f x ∂μ :=
  rfl

/-- Simultaneous L¹ pairing limits of countably many sequences of bounded readouts. -/
public theorem exists_L1_pairing_limits [MeasureTheory.IsSeparable μ]
    (u : ℕ → ℕ → X → ℝ) (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hu : ∀ j n, AEStronglyMeasurable (u j n) μ)
    (hb : ∀ j n, ∀ᵐ x ∂μ, ‖u j n x‖ ≤ B j)
    (base : ℕ → ℕ) (hBase : StrictMono base) :
    ∃ (σ : ℕ → ℕ) (F : ℕ → Lp ℝ 1 μ →L[ℝ] ℝ), StrictMono σ ∧
      (∀ j, ‖F j‖ ≤ B j) ∧ ∀ j (f : Lp ℝ 1 μ),
        Tendsto (fun n => ∫ x, u j (base (σ n)) x * f x ∂μ) atTop (𝓝 (F j f)) := by
  let _ : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩
  let _ : Fact ((1 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.one_ne_top⟩
  let L j n := boundedPairing (u j n) (hu j n) (hb j n)
  have hL (j n : ℕ) : ‖L j n‖ ≤ B j :=
    (pairingLinear (u j n) (hu j n) (hb j n)).mkContinuous_norm_le
      (hB j) (pairingLinear_bound (hu j n) (hb j n))
  exact exists_diagonal_continuousLinearMap_limits L B hB hL base hBase

end C2Riemannian



