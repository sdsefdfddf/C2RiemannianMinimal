module

public import C2Riemannian.FrequencySelection
public import C2Riemannian.ExactChildren
public import C2Riemannian.OscillatoryRemainder
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped ContDiff Topology BigOperators ENNReal

namespace C2Riemannian

/-- The width used before shifting to the common exhaustion tail. -/
@[expose] public noncomputable def layerWidth (k : ℕ) : ℝ :=
  (1 / 16) * (1 / ((k : ℝ) + 1))

public theorem layerWidth_pos (k : ℕ) : 0 < layerWidth k := by
  unfold layerWidth
  positivity

public theorem layerWidth_le (k : ℕ) : layerWidth k ≤ 1 / 16 := by
  have hDenom : (1 : ℝ) ≤ (k : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg k)
  have h : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 :=
    (div_le_iff₀ (by positivity)).mpr (by simpa only [one_mul] using hDenom)
  exact (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1 / 16)).trans_eq (mul_one _)

public theorem layerWidth_antitone : Antitone layerWidth := by
  intro i j hij
  have hCast : (i : ℝ) ≤ j := by exact_mod_cast hij
  have hDenom : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by linarith only [hCast]
  exact mul_le_mul_of_nonneg_left
    (one_div_le_one_div_of_le (by positivity) hDenom)
    (by norm_num)

public theorem layerWidth_tendsto : Tendsto layerWidth atTop (𝓝 0) := by
  have h : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  change Tendsto (fun k : ℕ => (1 / 16 : ℝ) * (1 / ((k : ℝ) + 1))) atTop (𝓝 0)
  simpa only [mul_zero] using h.const_mul (1 / 16 : ℝ)

/-- Relative area tolerance in the layer selection. -/
@[expose] public noncomputable def layerAreaTolerance (depth : ℕ) (BT : ℝ) : ℝ :=
  1 / (2000 * ((depth : ℝ) + 1) * (1 + 25 * BT))

public theorem layerAreaTolerance_bounds (depth : ℕ) {BT : ℝ} (hBT : 0 ≤ BT) :
    0 < layerAreaTolerance depth BT ∧ layerAreaTolerance depth BT < 1 / 2 := by
  have hDepth : (1 : ℝ) ≤ (depth : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg depth)
  have hBT' : 1 ≤ 1 + 25 * BT := by linarith
  have hDenom : 2000 ≤ 2000 * ((depth : ℝ) + 1) * (1 + 25 * BT) := by
    have h := mul_le_mul hDepth hBT' (by norm_num) (by positivity)
    nlinarith only [h]
  unfold layerAreaTolerance
  exact ⟨by positivity, one_div_lt_one_div_of_lt (by norm_num) (by linarith only [hDenom])⟩

/-- Uniform bound for the indicated derivative of the quantitative cutoff. -/
@[expose] public noncomputable def cutoffDerivativeConstant (r : ℝ) (k i : ℕ) : ℝ :=
  (4 / interiorRadius r k) ^ i * ∫ x, tensorHS (iteratedFDeriv ℝ i unitMollifier x)

private theorem cutoffDerivativeConstant_nonneg {r : ℝ} (hr : 0 < r) (k i : ℕ) :
    0 ≤ cutoffDerivativeConstant r k i := by
  have ht := interiorRadius_pos hr k
  unfold cutoffDerivativeConstant
  exact mul_nonneg (by positivity) (integral_nonneg fun _ => norm_nonneg _)

/-- The coefficient of the inverse frequency in the exact remainder estimate. -/
@[expose] public noncomputable def layerRemainderConstant (j : ℕ) (r : ℝ) (k : ℕ)
    (γ : ℝ) (n : Plane) : ℝ :=
  |γ| * ∑ i ∈ (Finset.range (j + 1)).erase 0,
    (j.choose i : ℝ) * (cutoffDerivativeConstant r k i * (‖n‖ ^ (j - i) * (2 : ℝ) ^ i))

/-- A single coefficient bounds both remainders, the value and the first derivative. -/
@[expose] public noncomputable def layerSizeConstant (r : ℝ) (k : ℕ)
    (b a : ℝ) (n : Plane) : ℝ :=
  max (layerRemainderConstant 2 r k b n) (max (layerRemainderConstant 4 r k a n)
    (max (4 * |b|) (|b| * (4 * cutoffDerivativeConstant r k 1 + 2 * ‖n‖))))

private theorem norm_fderiv_eq_tensorHS_one (χ : Plane → ℝ) (x : Plane) :
    ‖fderiv ℝ χ x‖ = tensorHS (iteratedFDeriv ℝ 1 χ x) := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  have hDual := b.norm_dual (fderiv ℝ χ x)
  have hSum :
      (∑ v : Fin 1 → Fin 2, ‖(fderiv ℝ χ x) (b (v 0))‖ ^ 2) =
        ∑ i : Fin 2, (fderiv ℝ χ x) (b i) ^ 2 := by
    apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 2))
    intro v
    simp only [Real.norm_eq_abs, sq_abs]
    rfl
  rw [tensorHS_eq_sqrt_sum]
  simp only [iteratedFDeriv_one_apply]
  change ‖fderiv ℝ χ x‖ = √(∑ v : Fin 1 → Fin 2, ‖(fderiv ℝ χ x) (b (v 0))‖ ^ 2)
  rw [hSum, ← hDual, Real.sqrt_sq (norm_nonneg _)]

private theorem layer_errors_le_constant {P : Set Plane} (hBound : Bornology.IsBounded P)
    (E : InteriorExhaustion P) (k : ℕ) (e b a L : ℝ) (hL : 1 ≤ L) (n : Plane) (x : Plane) :
    let χ := quantitativeCutoff P E.radius k
    let C := layerSizeConstant E.radius k b a n
    tensorHS (oscillatoryRemainder 2 χ e b L (innerSL ℝ n) x) ≤ C / L ∧
    tensorHS (oscillatoryRemainder 4 χ e a L (innerSL ℝ n) x) ≤ C / L ∧
    |oscillatoryPotential 2 χ e b L (innerSL ℝ n) x| ≤ C / L ∧
    ‖fderiv ℝ (oscillatoryPotential 2 χ e b L (innerSL ℝ n)) x‖ ≤ C / L := by
  let χ := quantitativeCutoff P E.radius k
  let D := cutoffDerivativeConstant E.radius k
  let C := layerSizeConstant E.radius k b a n
  let d := innerSL ℝ n
  have hd : ‖d‖ = ‖n‖ := by simp [d]
  have hLp : 0 < L := zero_lt_one.trans_le hL
  obtain ⟨hSmooth, _, _, _, hRange, _, hDerivative⟩ := quantitativeCutoff_spec hBound E k
  have hχAbs : |χ x| ≤ 1 :=
    (abs_of_nonneg (hRange x).1).trans_le (hRange x).2
  have hNormD : ‖fderiv ℝ χ x‖ ≤ D 1 := by
    rw [norm_fderiv_eq_tensorHS_one]
    exact hDerivative 1 x
  have hPow : L ≤ L ^ (2 : ℕ) := by
    simpa only [pow_one] using pow_le_pow_right₀ hL (by decide : 1 ≤ (2 : ℕ))
  have hRem (j : ℕ) (γ : ℝ) :
      tensorHS (oscillatoryRemainder j χ e γ L d x) ≤ layerRemainderConstant j E.radius k γ n / L := by
    have h := tensorHS_oscillatoryRemainder_le j hSmooth e γ L hL d x
    rw [hd] at h
    calc
      _ ≤ (|γ| / L) * ∑ i ∈ (Finset.range (j + 1)).erase 0,
          (j.choose i : ℝ) * (D i * (‖n‖ ^ (j - i) * (2 : ℝ) ^ i)) := by
        refine h.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by positivity))
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hDerivative i x) (by positivity))
          (Nat.cast_nonneg _)
      _ = _ := by unfold layerRemainderConstant; ring
  have hC₂ : layerRemainderConstant 2 E.radius k b n ≤ C := le_max_left _ _
  have hC₄ : layerRemainderConstant 4 E.radius k a n ≤ C :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hC₀ : 4 * |b| ≤ C :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hC₁ : |b| * (4 * D 1 + 2 * ‖n‖) ≤ C :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨(hRem 2 b).trans (div_le_div_of_nonneg_right hC₂ hLp.le),
    (hRem 4 a).trans (div_le_div_of_nonneg_right hC₄ hLp.le), ?_, ?_⟩
  · exact (abs_oscillatoryPotential_two_le e b L hLp d x hχAbs).trans
      ((div_le_div_of_nonneg_left (by positivity) hLp hPow).trans
        (div_le_div_of_nonneg_right hC₀ hLp.le))
  · have h := norm_fderiv_oscillatoryPotential_two_le e b L hLp d x
      ((hSmooth.differentiable (by simp)) x) hχAbs
    rw [hd] at h
    have hFrac : 4 * ‖fderiv ℝ χ x‖ / L ^ (2 : ℕ) ≤ 4 * D 1 / L := by
      calc
        _ ≤ 4 * D 1 / L ^ (2 : ℕ) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hNormD (by norm_num)) (sq_nonneg L)
        _ ≤ _ := div_le_div_of_nonneg_left
          (mul_nonneg (by norm_num) (cutoffDerivativeConstant_nonneg E.radius_pos k 1)) hLp hPow
    calc
      _ ≤ |b| * (4 * D 1 / L + 2 * ‖n‖ / L) :=
        h.trans (mul_le_mul_of_nonneg_left (add_le_add hFrac le_rfl) (abs_nonneg _))
      _ = |b| * (4 * D 1 + 2 * ‖n‖) / L := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hC₁ hLp.le

/-- The data selected simultaneously for a finite layer of parent platforms. -/
public structure LayerFrequencyContract {ι : Type*} (P : ι → Set Plane)
    (E : ∀ i, InteriorExhaustion (P i)) (n : ι → Plane) (b a : ι → ℝ) (δ : ℝ) where
  shift : ℕ
  frequency : ℕ → ℕ
  strictMono_frequency : StrictMono frequency
  frequency_ge_one : ∀ k, 1 ≤ frequency k
  frequency_gt_succ : ∀ k, k + 1 < frequency k
  width_small : ∀ k, 2 * layerWidth (k + shift) < δ / 4
  parent_area_loss : ∀ k i,
    volume.real (P i \ parentInterior (P i) (E i).radius (k + shift)) < δ * volume.real (P i) / 4
  inner_span : ∀ k i, 2 < 2 * (E i).radius * (frequency k : ℝ) * ‖n i‖
  frequency_gt_size : ∀ (k : ℕ) i,
    ((k : ℝ) + 1) * layerSizeConstant (E i).radius (k + shift) (b i) (a i) (n i) < frequency k
  area_error : ∀ k i positive,
    |volume.real (childPlatform (parentInterior (P i) (E i).radius (k + shift)) positive
      (layerWidth (k + shift)) (frequency k) (n i)) -
      (1 / 2 - 2 * layerWidth (k + shift)) *
        volume.real (parentInterior (P i) (E i).radius (k + shift))| < δ * volume.real (P i) / 4
  residual_two : ∀ k i x,
    tensorHS (oscillatoryRemainder 2 (quantitativeCutoff (P i) (E i).radius (k + shift))
      (layerWidth (k + shift)) (b i) (frequency k) (innerSL ℝ (n i)) x) ≤ 1 / ((k : ℝ) + 1)
  residual_four : ∀ k i x,
    tensorHS (oscillatoryRemainder 4 (quantitativeCutoff (P i) (E i).radius (k + shift))
      (layerWidth (k + shift)) (a i) (frequency k) (innerSL ℝ (n i)) x) ≤ 1 / ((k : ℝ) + 1)
  value_two : ∀ k i x,
    |oscillatoryPotential 2 (quantitativeCutoff (P i) (E i).radius (k + shift))
      (layerWidth (k + shift)) (b i) (frequency k) (innerSL ℝ (n i)) x| ≤ 1 / ((k : ℝ) + 1)
  derivative_two : ∀ k i x,
    ‖fderiv ℝ (oscillatoryPotential 2 (quantitativeCutoff (P i) (E i).radius (k + shift))
      (layerWidth (k + shift)) (b i) (frequency k) (innerSL ℝ (n i))) x‖ ≤ 1 / ((k : ℝ) + 1)
  child_nonempty : ∀ k i positive,
    (childPlatform (parentInterior (P i) (E i).radius (k + shift)) positive
      (layerWidth (k + shift)) (frequency k) (n i)).Nonempty

namespace LayerFrequencyContract

variable {ι : Type*} {P : ι → Set Plane} {E : ∀ i, InteriorExhaustion (P i)}
    {n : ι → Plane} {b a : ι → ℝ} {δ : ℝ}

@[expose] public noncomputable def inner (C : LayerFrequencyContract P E n b a δ) (k : ℕ) (i : ι) :
    Set Plane :=
  parentInterior (P i) (E i).radius (k + C.shift)

@[expose] public noncomputable def cutoff (C : LayerFrequencyContract P E n b a δ) (k : ℕ) (i : ι) :
    Plane → ℝ :=
  quantitativeCutoff (P i) (E i).radius (k + C.shift)

@[expose] public noncomputable def width (C : LayerFrequencyContract P E n b a δ) (k : ℕ) : ℝ :=
  layerWidth (k + C.shift)

public theorem tendsto_frequency (C : LayerFrequencyContract P E n b a δ) :
    Tendsto C.frequency atTop atTop := C.strictMono_frequency.tendsto_atTop

public theorem tendsto_width (C : LayerFrequencyContract P E n b a δ) :
    Tendsto C.width atTop (𝓝 0) := (layerWidth_tendsto).comp (tendsto_add_atTop_nat C.shift)

public theorem eventually_contains_compact (C : LayerFrequencyContract P E n b a δ)
    (i : ι) (S : Set Plane) (hS : S ⊆ P i) (hComp : IsCompact S) :
    ∀ᶠ k in atTop, S ⊆ C.inner k i :=
  (tendsto_add_atTop_nat C.shift).eventually ((E i).eventually_contains_compact S hS hComp)


public theorem width_pos (C : LayerFrequencyContract P E n b a δ) (k : ℕ) :
    0 < C.width k := layerWidth_pos _

public theorem width_le_one_sixteenth (C : LayerFrequencyContract P E n b a δ) (k : ℕ) :
    C.width k ≤ 1 / 16 := layerWidth_le _

public theorem width_antitone (C : LayerFrequencyContract P E n b a δ) : Antitone C.width :=
  fun _ _ h => layerWidth_antitone (Nat.add_le_add_right h C.shift)

public theorem inner_open (C : LayerFrequencyContract P E n b a δ) (k : ℕ) (i : ι) :
    IsOpen (C.inner k i) := parentInterior_open _ _ _

public theorem inner_subset (C : LayerFrequencyContract P E n b a δ) (k : ℕ) (i : ι) :
    C.inner k i ⊆ P i := (E i).inside _

public theorem cutoff_one_near_inner (C : LayerFrequencyContract P E n b a δ)
    (hBound : ∀ i, Bornology.IsBounded (P i)) (k : ℕ) (i : ι) :
    ∃ V : Set Plane, IsOpen V ∧ closure (C.inner k i) ⊆ V ∧
      ∀ x ∈ V, C.cutoff k i x = 1 :=
  quantitativeCutoff_one_near_closure (hBound i) (E i) (k + C.shift)

public theorem child_measures (C : LayerFrequencyContract P E n b a δ)
    (hδ : 0 < δ) (hδ' : δ < 1 / 2) (k : ℕ) (i : ι) :
    let child (positive : Bool) := childPlatform (C.inner k i) positive (C.width k) (C.frequency k) (n i)
    (∀ positive : Bool, |volume.real (child positive) - volume.real (P i) / 2| < δ * volume.real (P i)) ∧
      volume.real (P i \ (child true ∪ child false)) ≤ 2 * δ * volume.real (P i) ∧
      ∀ positive : Bool, (child positive).Nonempty :=
  child_platform_measure (C.inner_open k i) (C.inner_subset k i) (E i).volume_finite
    (ENNReal.toReal_pos (ne_of_gt (E i).volume_pos) (E i).volume_finite)
    hδ hδ' (C.width_pos k) (C.width_le_one_sixteenth k) (C.width_small k)
    (n i) (C.parent_area_loss k i) (C.area_error k i)

end LayerFrequencyContract


/-- A common exhaustion tail and strictly increasing integer frequencies meet
the simultaneous area, phase-span and oscillatory error conditions. -/
public theorem exists_layer_frequency_contract {ι : Type*} [Finite ι]
    {P : ι → Set Plane} (hBound : ∀ i, Bornology.IsBounded (P i))
    (E : ∀ i, InteriorExhaustion (P i)) (n : ι → Plane) (hn : ∀ i, n i ≠ 0)
    (b a : ι → ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    Nonempty (LayerFrequencyContract P E n b a δ) := by
  obtain ⟨N, hParent⟩ := choose_common_parent_exhaustion_tail E hδ
  have hWidthLimit : Tendsto (fun k => 2 * layerWidth k) atTop (𝓝 0) := by
    simpa only [mul_zero] using layerWidth_tendsto.const_mul 2
  have hWidthTail : ∀ᶠ k in atTop, 2 * layerWidth k < δ / 4 :=
    hWidthLimit (eventually_lt_nhds (by positivity))
  obtain ⟨M, hWidth⟩ := eventually_atTop.mp hWidthTail
  let shift := N + M
  let U (k : ℕ) (i : ι) := parentInterior (P i) (E i).radius (k + shift)
  let e (k : ℕ) := layerWidth (k + shift)
  let size (k : ℕ) (i : ι) := layerSizeConstant (E i).radius (k + shift) (b i) (a i) (n i)
  have hWidthSmall (k : ℕ) : 2 * e k < δ / 4 :=
    hWidth (k + shift) (by dsimp [shift]; omega)
  have hParentSmall (k : ℕ) (i : ι) : volume.real (P i \ U k i) < δ * volume.real (P i) / 4 := by
    change (volume (P i \ parentInterior (P i) (E i).radius (k + shift))).toReal <
      δ * (volume (P i)).toReal / 4
    rw [show k + shift = (k + M) + N by dsimp [shift]; omega]
    exact hParent (k + M) i
  have hUopen (k : ℕ) (i : ι) : IsOpen (U k i) := parentInterior_open _ _ _
  have hUsub (k : ℕ) (i : ι) : U k i ⊆ P i := (E i).inside _
  have hPpos (i : ι) : 0 < volume.real (P i) :=
    ENNReal.toReal_pos (ne_of_gt (E i).volume_pos) (E i).volume_finite
  let Accept (k : ℕ) (i : ι) (L : ℕ) : Prop :=
    k + 1 < L ∧ ((k : ℝ) + 1) * size k i < (L : ℝ) ∧
    2 < 2 * (E i).radius * (L : ℝ) * ‖n i‖ ∧
    ∀ positive : Bool,
      |volume.real (childPlatform (U k i) positive (e k) (L : ℝ) (n i)) -
        (1 / 2 - 2 * e k) * volume.real (U k i)| < δ * volume.real (P i) / 4
  have hAccept (k : ℕ) (i : ι) : ∀ᶠ L : ℕ in atTop, Accept k i L := by
    have hRadius := (E i).radius_pos
    have hNorm : 0 < ‖n i‖ := norm_pos_iff.mpr (hn i)
    have hProd := mul_pos hRadius hNorm
    let threshold := max (((k : ℝ) + 1) * size k i)
      (max ((k : ℝ) + 1) (1 / ((E i).radius * ‖n i‖)))
    have hLarge : ∀ᶠ L : ℕ in atTop, threshold < (L : ℝ) :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_gt_atTop threshold)
    have hη : 0 < δ * volume.real (P i) / 4 := div_pos (mul_pos hδ (hPpos i)) (by norm_num)
    have hArea := eventually_child_area_nat (hUopen k i)
      (measure_ne_top_of_subset (hUsub k i) (E i).volume_finite)
      (hn i) (layerWidth_pos (k + shift)) (layerWidth_le (k + shift))
      hη
    filter_upwards [hLarge, hArea] with L hL hAreaL
    have hSucc : ((k : ℝ) + 1) < L :=
      ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hL
    have hAmp : ((k : ℝ) + 1) * size k i < L := (le_max_left _ _).trans_lt hL
    have hSpan : 1 / ((E i).radius * ‖n i‖) < L :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hL
    have hMul := (div_lt_iff₀ hProd).mp hSpan
    refine ⟨by exact_mod_cast hSucc, hAmp, ?_, hAreaL⟩
    nlinarith only [hMul]
  let AllAccept (k : ℕ) (_ : Unit) (L : ℕ) := k + 1 < L ∧ ∀ i, Accept k i L
  have hAll (k : ℕ) (u : Unit) : ∀ᶠ L : ℕ in atTop, AllAccept k u L :=
    (eventually_gt_atTop (k + 1)).and (Filter.eventually_all.mpr (hAccept k))
  obtain ⟨L, hStrict, hL, hAllFreq⟩ := choose_layer_frequencies AllAccept hAll
  have hForall (k : ℕ) (i : ι) : Accept k i (L k) := (hAllFreq k ()).2 i
  have hError (k : ℕ) (i : ι) (x : Plane) :=
    layer_errors_le_constant (hBound i) (E i) (k + shift) (e k) (b i) (a i) (L k)
      (by exact_mod_cast hL k) (n i) x
  have hSmall (k : ℕ) (i : ι) : size k i / (L k : ℝ) ≤ 1 / ((k : ℝ) + 1) := by
    have hLpos : (0 : ℝ) < L k := by exact_mod_cast ((Nat.zero_lt_succ k).trans (hForall k i).1)
    apply (div_le_div_iff₀ hLpos (by positivity)).mpr
    have h := (hForall k i).2.1
    linarith only [h]
  refine ⟨⟨shift, L, hStrict, hL, fun k => (hAllFreq k ()).1, hWidthSmall, hParentSmall,
    fun k i => (hForall k i).2.2.1, fun k i => (hForall k i).2.1, fun k i => (hForall k i).2.2.2,
    fun k i x => (hError k i x).1.trans (hSmall k i),
    fun k i x => (hError k i x).2.1.trans (hSmall k i),
    fun k i x => (hError k i x).2.2.1.trans (hSmall k i),
    fun k i x => (hError k i x).2.2.2.trans (hSmall k i), ?_⟩⟩
  · intro k i
    exact (child_platform_measure (hUopen k i) (hUsub k i) (E i).volume_finite (hPpos i)
      hδ hδ' (layerWidth_pos (k + shift)) (layerWidth_le (k + shift)) (hWidthSmall k)
      (n i) (hParentSmall k i) (hForall k i).2.2.2).2.2


public theorem exists_layer_frequency_contract_of_depth {ι : Type*} [Finite ι]
    {P : ι → Set Plane} (hBound : ∀ i, Bornology.IsBounded (P i))
    (E : ∀ i, InteriorExhaustion (P i)) (n : ι → Plane) (hn : ∀ i, n i ≠ 0)
    (b a : ι → ℝ) (depth : ℕ) {BT : ℝ} (hBT : 0 ≤ BT) :
    Nonempty (LayerFrequencyContract P E n b a (layerAreaTolerance depth BT)) :=
  exists_layer_frequency_contract hBound E n hn b a
    (layerAreaTolerance_bounds depth hBT).1 (layerAreaTolerance_bounds depth hBT).2

end C2Riemannian
