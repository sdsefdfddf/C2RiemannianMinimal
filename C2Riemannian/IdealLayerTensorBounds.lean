module

public import C2Riemannian.IdealLayerRealization
public import C2Riemannian.IdealSecondBounds
public import C2Riemannian.IdealFourthBounds
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Ring

/-! # Ideal tensor bounds for an actual layer (M24–M25) -/

set_option autoImplicit false

open Set MeasureTheory C2Riemannian.IdealNode
open scoped BigOperators ContDiff

namespace C2Riemannian

private theorem sum_word_succ {j : ℕ} (f : (Fin (j + 1) → Fin 2) → ℝ) :
    (∑ w, f w) = ∑ v : Fin 2, ∑ w : Fin j → Fin 2, f (Fin.cons v w) := by
  calc
    _ = ∑ p : Fin 2 × (Fin j → Fin 2), f (Fin.cons p.1 p.2) :=
      (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (j + 1) => Fin 2))
        (fun p => f (Fin.cons p.1 p.2)) f (fun _ => rfl)).symm
    _ = _ := Fintype.sum_prod_type _

/-- For an ideal second tensor, the word-coordinate norm is the scalar
Frobenius norm with both mixed slots included. -/
public theorem tensorHS_eq_scalarHess_of_words (A : Plane [×2]→L[ℝ] ℝ) (H : ScalarHess)
    (h : ∀ w : Fin 2 → Fin 2, A (basisWord w) = secondWordValue H w) :
    tensorHS A = √H.frobeniusSq := by
  rw [tensorHS_eq_sqrt_sum]
  change √(∑ w : Fin 2 → Fin 2, ‖A (basisWord w)‖ ^ 2) = _
  simp only [h, Real.norm_eq_abs, sq_abs]
  congr 1
  simp [sum_word_succ, Fin.sum_univ_two, secondWordValue, ScalarHess.frobeniusSq]
  ring

private theorem wordWeight_cons_val {j : ℕ} (i : Fin 2) (w : Fin j → Fin 2) :
    (wordWeight (Fin.cons i w)).val = i.val + (wordWeight w).val := by
  change (∑ k, (Fin.cons (α := fun _ : Fin (j + 1) => Fin 2) i w k).val) =
    i.val + ∑ k, (w k).val
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

private theorem wordWeight_nil_val (w : Fin 0 → Fin 2) : (wordWeight w).val = 0 := by
  simp [wordWeight]

/-- Fourth-order Cartesian words of weight (i) have multiplicity
(Nat.choose 4 i), giving the prescribed ideal fourth norm. -/
public theorem tensorHS_eq_fourthNorm_of_words (A : Plane [×4]→L[ℝ] ℝ) (T : Fin 5 → ℝ)
    (h : ∀ w : Fin 4 → Fin 2, A (basisWord w) = T (wordWeight w)) :
    tensorHS A = fourthNorm T := by
  rw [tensorHS_eq_sqrt_sum, fourthNorm]
  change √(∑ w : Fin 4 → Fin 2, ‖A (basisWord w)‖ ^ 2) = _
  simp only [h, Real.norm_eq_abs, sq_abs]
  congr 1
  let T' (i : ℕ) := T ⟨i % 5, Nat.mod_lt _ (by decide)⟩
  have hT (w : Fin 4 → Fin 2) : T (wordWeight w) = T' (wordWeight w).val := by
    apply congrArg T
    exact Fin.ext (Nat.mod_eq_of_lt (wordWeight w).isLt).symm
  simp only [hT]
  norm_num [sum_word_succ, Fin.sum_univ_succ, wordWeight_cons_val, wordWeight_nil_val, Nat.choose, T']
  ring

/-- Actual ideal-matched potentials preserve both global budgets under a
frequency-contract layer. The two hypotheses on ideal children are supplied
by the ideal schedule's second and fourth bounds. -/
public theorem realizedLayerIdeal_bounds {ι : Type*} {P : ι → Set Plane}
    {E : ∀ i, InteriorExhaustion (P i)} {δ : ℝ} (layer : IdealLayer) (node : ι → IdealNode) (s : ℝ)
    (C : LayerFrequencyContract P E (fun _ => layer.normal s)
      (fun i => layer.secondAmplitude (node i)) (fun _ => layer.fourthAmplitude) δ)
    (I : Finset ι) (hDisjoint : Set.PairwiseDisjoint (I : Set ι) P)
    (hOpen : ∀ i ∈ I, IsOpen (P i)) (hBound : ∀ i ∈ I, Bornology.IsBounded (P i))
    (k : ℕ) {W₂ W₄ : Plane → ℝ} (hW₂ : ContDiff ℝ ∞ W₂) (hW₄ : ContDiff ℝ ∞ W₄)
    (hSecond : ∀ i ∈ I, ∀ x ∈ P i, matchesSecondJet W₂ x (node i))
    (hFourth : ∀ i ∈ I, ∀ x ∈ P i, matchesFourthJet W₄ x (node i))
    (B₄ : ℝ)
    (hOld₂ : ∀ x, tensorHS (iteratedFDeriv ℝ 2 W₂ x) ≤ √(11 / 2 : ℝ) + 1)
    (hOld₄ : ∀ x, tensorHS (iteratedFDeriv ℝ 4 W₄ x) ≤ B₄ + 1)
    (hIdeal₂ : ∀ i ∈ I, ∀ positive, ((node i).child layer s positive).scalar.frobeniusSq ≤ 11 / 2)
    (hIdeal₄ : ∀ i ∈ I, ∀ positive, fourthNorm ((node i).child layer s positive).fourth ≤ B₄) :
    (∀ x, tensorHS (iteratedFDeriv ℝ 2
      (realizedLayerPotential C I k 2 (fun i => layer.secondAmplitude (node i)) W₂) x) ≤
        √(11 / 2 : ℝ) + 1) ∧
    ∀ x, tensorHS (iteratedFDeriv ℝ 4
      (realizedLayerPotential C I k 4 (fun _ => layer.fourthAmplitude) W₄) x) ≤ B₄ + 1 := by
  let d := innerSL ℝ (layer.normal s)
  let γ (i : ι) := layer.secondAmplitude (node i)
  let α := layer.fourthAmplitude
  let A₂ (i : ι) := iteratedFDeriv ℝ 2 W₂ (E i).center
  let A₄ (i : ι) := iteratedFDeriv ℝ 4 W₄ (E i).center
  have hCenter (i : ι) : (E i).center ∈ P i :=
    (E i).inside 0 ((E i).inner_ball 0 (Metric.mem_ball_self (E i).radius_pos))
  have hA₂ (i : ι) (hi : i ∈ I) (x : Plane) (hx : x ∈ P i) :
      iteratedFDeriv ℝ 2 W₂ x = A₂ i :=
    eq_of_basisWord_eq fun w =>
      (hSecond i hi x hx w).trans (hSecond i hi (E i).center (hCenter i) w).symm
  have hA₄ (i : ι) (hi : i ∈ I) (x : Plane) (hx : x ∈ P i) :
      iteratedFDeriv ℝ 4 W₄ x = A₄ i :=
    eq_of_basisWord_eq fun w =>
      (hFourth i hi x hx w).trans (hFourth i hi (E i).center (hCenter i) w).symm
  have hL : (C.frequency k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (C.frequency_ge_one k))
  have hη : 1 / ((k : ℝ) + 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg k))
  have hCS (i : ι) (hi : i ∈ I) := quantitativeCutoff_spec (hBound i hi) (E i) (k + C.shift)
  have hSmooth (i : ι) (hi : i ∈ I) : ContDiff ℝ ∞ (C.cutoff k i) := (hCS i hi).1
  have hSupp (i : ι) (hi : i ∈ I) : tsupport (C.cutoff k i) ⊆ P i := (hCS i hi).2.2.2.1
  have hRange (i : ι) (hi : i ∈ I) (x : Plane) (_hx : x ∈ P i) : |C.cutoff k i x| ≤ 1 :=
    (abs_of_nonneg ((hCS i hi).2.2.2.2.1 x).1).trans_le ((hCS i hi).2.2.2.2.1 x).2
  have hChild₂ (i : ι) (hi : i ∈ I) (p : Bool) :
      tensorHS (A₂ i + (childSign p * γ i) • directionalTensor 2 d) ≤ √(11 / 2 : ℝ) := by
    rw [tensorHS_eq_scalarHess_of_words _ ((node i).child layer s p).scalar]
    · exact Real.sqrt_le_sqrt (hIdeal₂ i hi p)
    · intro w
      simp only [A₂, add_apply, smul_apply, smul_eq_mul, directionalTensor_apply, d,
        innerSL_apply_apply, γ, hSecond i hi _ (hCenter i) w, idealChild_secondWord]
  have hChild₄ (i : ι) (hi : i ∈ I) (p : Bool) :
      tensorHS (A₄ i + (childSign p * α) • directionalTensor 4 d) ≤ B₄ := by
    rw [tensorHS_eq_fourthNorm_of_words _ ((node i).child layer s p).fourth]
    · exact hIdeal₄ i hi p
    · intro w
      simp only [A₄, add_apply, smul_apply, smul_eq_mul, directionalTensor_apply, d,
        innerSL_apply_apply, α, hFourth i hi _ (hCenter i) w, idealChild_fourthWord]
  constructor
  · exact realize_layer_derivative_bound I hDisjoint hOpen 2 hW₂ (C.cutoff k) hSmooth hSupp
      (C.width k) (C.frequency k) (√(11 / 2 : ℝ)) _ hL hη γ (fun _ => d) A₂ hOld₂ hA₂ hRange
      (fun i hi => by simpa [childSign] using hChild₂ i hi true)
      (fun i hi => by
        have heq : A₂ i + ((-1 : ℝ) * γ i) • directionalTensor 2 d =
            A₂ i - γ i • directionalTensor 2 d := by
          ext w
          simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
          ring
        rw [← heq]
        exact hChild₂ i hi false)
      (fun i _ x _ => C.residual_two k i x)
  · exact realize_layer_derivative_bound I hDisjoint hOpen 4 hW₄ (C.cutoff k) hSmooth hSupp
      (C.width k) (C.frequency k) B₄ _ hL hη (fun _ => α) (fun _ => d) A₄ hOld₄ hA₄ hRange
      (fun i hi => by simpa [childSign] using hChild₄ i hi true)
      (fun i hi => by
        have heq : A₄ i + ((-1 : ℝ) * α) • directionalTensor 4 d =
            A₄ i - α • directionalTensor 4 d := by
          ext w
          simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
          ring
        rw [← heq]
        exact hChild₄ i hi false)
      (fun i _ x _ => C.residual_four k i x)

/-- The same fourth-order budget holds at every prefix of the labelled schedule. -/
public theorem IdealNode.all_layer_node_fourth_norm_bound (N J depth : ℕ) (s : ℝ)
    (hs : |s| ≤ 1) (node : IdealNode)
    (hNode : node ∈ run ((idealLayers 0 (SplitStep.schedule N J)).take depth) s) :
    fourthNorm node.fourth ≤ 4 * (2 : ℝ) ^ (4 * N * J) := by
  have hTake (prior d : ℕ) (steps : List SplitStep) :
      (idealLayers prior steps).take d = idealLayers prior (steps.take d) := by
    induction d generalizing prior steps with
    | zero => rfl
    | succ d ih =>
      cases steps with
      | nil => rfl
      | cons step steps => simp [idealLayers, ih]
  rw [hTake] at hNode
  have hCount :
      tableCount ((SplitStep.schedule N J).take depth) ≤ 4 * N * J := by
    calc
      _ ≤ tableCount ((SplitStep.schedule N J).take depth) +
          tableCount ((SplitStep.schedule N J).drop depth) := le_add_of_nonneg_right (Nat.zero_le _)
      _ = tableCount (SplitStep.schedule N J) := by rw [← tableCount_append, List.take_append_drop]
      _ = _ := tableCount_schedule N J
  apply fourthNorm_le _ _ (by positivity)
  intro i
  have h := run_fourth_coord_bound _ s hs node hNode i
  exact (h.trans (sub_le_self _ zero_le_one)).trans (pow_le_pow_right₀ one_le_two hCount)

end C2Riemannian
