module

public import C2Riemannian.OscillatoryPotential
public import C2Riemannian.QuantitativeCutoff
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Data.List.OfFn
import Mathlib.Analysis.InnerProductSpace.Dual

set_option autoImplicit false

open Filter
open scoped ContDiff Topology BigOperators

namespace C2Riemannian

/-- The highest-order derivative after subtraction of the term where all
derivatives fall on the periodic factor. -/
@[expose] public noncomputable def oscillatoryRemainder (j : ℕ) (χ : Plane → ℝ)
    (e γ L : ℝ) (d : Plane →L[ℝ] ℝ) (x : Plane) : Plane [×j]→L[ℝ] ℝ :=
  iteratedFDeriv ℝ j (oscillatoryPotential j χ e γ L d) x -
    iteratedFDeriv ℝ j (oscillatoryPotential j (fun _ => χ x) e γ L d) x

private theorem iteratedFDeriv_oscillatoryPotential_frozen (j : ℕ) (χ : Plane → ℝ)
    (e γ L : ℝ) (hL : L ≠ 0) (d : Plane →L[ℝ] ℝ) (x : Plane) (v : Fin j → Plane) :
    iteratedFDeriv ℝ j (oscillatoryPotential j (fun _ => χ x) e γ L d) x v =
      γ * χ x * smooth_square_wave e ((L • d) x) * ∏ i, d (v i) := by
  have hEq : oscillatoryPotential j (fun _ => χ x) e γ L d =
      oscillatoryPotential j (fun _ => 1) e (γ * χ x) L d := by
    funext y
    simp only [oscillatoryPotential, one_mul, div_eq_mul_inv]
    ring
  rw [hEq]
  exact iteratedFDeriv_oscillatoryPotential_on_plateau j e (γ * χ x) L hL d
    (Eventually.of_forall fun _ => rfl) v

public theorem iteratedFDeriv_oscillatoryPotential_eq_main_add_remainder (j : ℕ) (χ : Plane → ℝ)
    (e γ L : ℝ) (hL : L ≠ 0) (d : Plane →L[ℝ] ℝ) (x : Plane) (v : Fin j → Plane) :
    iteratedFDeriv ℝ j (oscillatoryPotential j χ e γ L d) x v =
      γ * χ x * smooth_square_wave e ((L • d) x) * (∏ i, d (v i)) +
        oscillatoryRemainder j χ e γ L d x v := by
  rw [← iteratedFDeriv_oscillatoryPotential_frozen j χ e γ L hL d x v]
  simp only [oscillatoryRemainder, sub_apply]
  ring

public theorem oscillatoryRemainder_zero_on_plateau (j : ℕ) {χ : Plane → ℝ}
    (e γ L : ℝ) (hL : L ≠ 0) (d : Plane →L[ℝ] ℝ) {x : Plane}
    (hχ : ∀ᶠ y in 𝓝 x, χ y = 1) : oscillatoryRemainder j χ e γ L d x = 0 := by
  ext v
  have hloc : {y | χ y = 1} ∈ 𝓝 x := hχ
  have hMem : x ∈ {y | χ y = 1} := mem_of_mem_nhds hloc
  have hx : χ x = 1 := hMem
  simp only [oscillatoryRemainder, sub_apply, zero_apply]
  rw [iteratedFDeriv_oscillatoryPotential_on_plateau j e γ L hL d hχ v,
    iteratedFDeriv_oscillatoryPotential_frozen j χ e γ L hL d x v, hx, mul_one, sub_self]

private theorem norm_phase_derivative_le {i j : ℕ} (hi : i ≤ j) (e L : ℝ) (hL : 0 < L)
    (d : Plane →L[ℝ] ℝ) (x : Plane) :
    ‖iteratedFDeriv ℝ (j - i) (profilePrimitive e j ∘ (L • d)) x‖ ≤
      (2 : ℝ) ^ i * (L * ‖d‖) ^ (j - i) := by
  let A : Plane →L[ℝ] ℝ := L • d
  have hSmooth := (profilePrimitive_properties e j).1
  rw [A.iteratedFDeriv_comp_right hSmooth x (by simp)]
  have h := (iteratedFDeriv ℝ (j - i) (profilePrimitive e j) (A x)).norm_compContinuousLinearMap_le
    (fun _ => A)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h
  have hAbs : ‖iteratedDeriv (j - i) (profilePrimitive e j) (A x)‖ ≤ (2 : ℝ) ^ i := by
    rw [Real.norm_eq_abs]
    exact abs_iteratedDeriv_profilePrimitive_le e hi (A x)
  have hA : ‖A‖ = L * ‖d‖ := by
    simp only [A, norm_smul, Real.norm_eq_abs, abs_of_pos hL]
  exact h.trans (by rw [← hA]; exact mul_le_mul_of_nonneg_right hAbs (by positivity))

/-- The highest-order remainder in operator norm, with the binomial
multiplicities of the product rule and one inverse power of frequency. -/
public theorem norm_oscillatoryRemainder_le (j : ℕ) {χ : Plane → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (e γ L : ℝ) (hL : 1 ≤ L) (d : Plane →L[ℝ] ℝ) (x : Plane) :
    ‖oscillatoryRemainder j χ e γ L d x‖ ≤
      (|γ| / L) * ∑ i ∈ (Finset.range (j + 1)).erase 0,
        (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ * ‖d‖ ^ (j - i) * (2 : ℝ) ^ i := by
  let η (y : Plane) := χ y - χ x
  let ψ := profilePrimitive e j ∘ (L • d)
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hη : ContDiff ℝ ∞ η := hχ.sub contDiff_const
  have hψ : ContDiff ℝ ∞ ψ := (profilePrimitive_properties e j).1.comp (L • d).contDiff
  have hSub := iteratedFDeriv_sub_apply (x := x)
    (f := oscillatoryPotential j χ e γ L d)
    (g := oscillatoryPotential j (fun _ => χ x) e γ L d)
    ((contDiff_oscillatoryPotential j hχ e γ L d).of_le (show (j : ℕ∞ω) ≤ ∞ by simp)).contDiffAt
    ((contDiff_oscillatoryPotential j contDiff_const e γ L d).of_le
      (show (j : ℕ∞ω) ≤ ∞ by simp)).contDiffAt
  have hEq : oscillatoryPotential j χ e γ L d - oscillatoryPotential j (fun _ => χ x) e γ L d =
      fun y => (γ / L ^ j) • (η y * ψ y) := by
    funext y
    simp only [oscillatoryPotential, η, ψ, Pi.sub_apply, Function.comp_apply, smul_eq_mul]
    ring
  have hDeriv : oscillatoryRemainder j χ e γ L d x =
      (γ / L ^ j) • iteratedFDeriv ℝ j (fun y => η y * ψ y) x := by
    unfold oscillatoryRemainder
    rw [← hSub, hEq, iteratedFDeriv_const_smul_apply' (((hη.mul hψ).of_le
      (show (j : ℕ∞ω) ≤ ∞ by simp)).contDiffAt)]
  rw [hDeriv, norm_smul, Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hLp]
  let T (i : ℕ) := (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i η x‖ *
    ‖iteratedFDeriv ℝ (j - i) ψ x‖
  have hVanishing : T 0 = 0 := by
    simp [T, η]
  have hSum := norm_iteratedFDeriv_mul_le hη hψ x (n := j) (by simp)
  change ‖iteratedFDeriv ℝ j (fun y => η y * ψ y) x‖ ≤ ∑ i ∈ Finset.range (j + 1), T i at hSum
  have hz : 0 ∈ Finset.range (j + 1) := Finset.mem_range.mpr j.succ_pos
  rw [← Finset.sum_erase_add _ _ hz, hVanishing, add_zero] at hSum
  refine (mul_le_mul_of_nonneg_left hSum (by positivity)).trans ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hne := (Finset.mem_erase.mp hi).1
  have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_erase.mp hi).2)
  have hEta : iteratedFDeriv ℝ i η x = iteratedFDeriv ℝ i χ x := by
    change iteratedFDeriv ℝ i (χ - fun _ : Plane => χ x) x = _
    rw [iteratedFDeriv_sub_apply (hχ.contDiffAt.of_le (by simp)) contDiffAt_const,
      iteratedFDeriv_const_of_ne hne, Pi.zero_apply, sub_zero]
  have hFreq : L ≤ L ^ i := by
    simpa only [pow_one] using pow_le_pow_right₀ hL (Nat.pos_of_ne_zero hne)
  have hLpower : L ^ i * L ^ (j - i) = L ^ j := by rw [← pow_add, Nat.add_sub_of_le hij]
  calc
    _ ≤ (|γ| / L ^ j) *
        ((j.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ * ((2 : ℝ) ^ i * (L * ‖d‖) ^ (j - i))) := by
      change (|γ| / L ^ j) *
        ((j.choose i : ℝ) * ‖iteratedFDeriv ℝ i η x‖ * ‖iteratedFDeriv ℝ (j - i) ψ x‖) ≤ _
      rw [hEta]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (norm_phase_derivative_le hij e L hLp d x) (by positivity))
        (by positivity)
    _ = (|γ| / L ^ i) * ((j.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ * ‖d‖ ^ (j - i) * (2 : ℝ) ^ i) := by
      rw [mul_pow, ← hLpower]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left (abs_nonneg _) hLp hFreq) (by positivity)

/-- The planar Hilbert–Schmidt norm is bounded by the operator norm times
the square root of the number of ordered coordinates. -/
public theorem tensorHS_le_opNorm {j : ℕ} (A : Plane [×j]→L[ℝ] ℝ) :
    tensorHS A ≤ Real.sqrt ((2 : ℝ) ^ j) * ‖A‖ := by
  rw [tensorHS_eq_sqrt_sum]
  refine (Real.sqrt_le_iff).mpr ⟨by positivity, ?_⟩
  have hCoord (v : Fin j → Fin 2) :
      ‖A (fun k => EuclideanSpace.basisFun (Fin 2) ℝ (v k))‖ ≤ ‖A‖ := by
    have h := A.le_opNorm (fun k => EuclideanSpace.basisFun (Fin 2) ℝ (v k))
    have hUnit (k : Fin j) : ‖EuclideanSpace.basisFun (Fin 2) ℝ (v k)‖ = 1 :=
      (EuclideanSpace.basisFun (Fin 2) ℝ).orthonormal.norm_eq_one _
    simpa only [hUnit, Finset.prod_const_one, mul_one] using h
  calc
    _ ≤ ∑ _v : Fin j → Fin 2, ‖A‖ ^ 2 := by
      apply Finset.sum_le_sum
      exact fun v _ => pow_le_pow_left₀ (norm_nonneg _) (hCoord v) 2
    _ = _ := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      simp [nsmul_eq_mul]

/-- A Hilbert–Schmidt remainder estimate with the explicit conversion
factor from the ordered Cartesian coordinates. -/
public theorem tensorHS_oscillatoryRemainder_le_of_opNorm (j : ℕ) {χ : Plane → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (e γ L : ℝ) (hL : 1 ≤ L) (d : Plane →L[ℝ] ℝ) (x : Plane) :
    tensorHS (oscillatoryRemainder j χ e γ L d x) ≤
      Real.sqrt ((2 : ℝ) ^ j) * ((|γ| / L) * ∑ i ∈ (Finset.range (j + 1)).erase 0,
        (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ * ‖d‖ ^ (j - i) * (2 : ℝ) ^ i) :=
  (tensorHS_le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (norm_oscillatoryRemainder_le j hχ e γ L hL d x) (by positivity))


/-- A sequence of directional derivatives, with the first direction applied
to the derivative in the remaining directions. -/
@[expose] public noncomputable def orderedDerivative (dirs : List Plane) (f : Plane → ℝ) :
    Plane → ℝ :=
  match dirs with
  | [] => f
  | v :: tail => fun x => fderiv ℝ (orderedDerivative tail f) x v

/-- The ordered pairs of subsequences obtained by assigning each position to
the left or right factor. The list retains repeated position assignments. -/
@[expose] public def splitDirections : List Plane → List (List Plane × List Plane)
  | [] => [([], [])]
  | v :: tail =>
      let splits := splitDirections tail
      splits.map (fun p => (v :: p.1, p.2)) ++ splits.map (fun p => (p.1, v :: p.2))

private theorem contDiff_orderedDerivative (dirs : List Plane) {f : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (orderedDerivative dirs f) := by
  induction dirs with
  | nil => exact hf
  | cons v tail ih =>
    change ContDiff ℝ ∞ (fun x => fderiv ℝ (orderedDerivative tail f) x v)
    exact (ContinuousLinearMap.apply ℝ ℝ v).contDiff.comp
      ((contDiff_infty_iff_fderiv.mp ih).2)

private theorem fderiv_list_sum_apply {ι : Type*} (s : List ι) (a : ι → Plane → ℝ)
    (ha : ∀ i, ContDiff ℝ ∞ (a i)) (x v : Plane) :
    fderiv ℝ (fun y => (s.map fun i => a i y).sum) x v =
      (s.map fun i => fderiv ℝ (a i) x v).sum := by
  have hSmooth (l : List ι) : ContDiff ℝ ∞ (fun y => (l.map fun i => a i y).sum) := by
    induction l with
    | nil => exact contDiff_const
    | cons i l ih =>
      change ContDiff ℝ ∞ (fun y => a i y + (l.map fun j => a j y).sum)
      exact (ha i).add ih
  induction s with
  | nil => simp
  | cons i s ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [fderiv_fun_add (((ha i).differentiable (by simp)) x)
      (((hSmooth s).differentiable (by simp)) x), add_apply, ih]

/-- The ordered product formula, with one term for each assignment of positions
in the direction list to the two factors. -/
public theorem orderedDerivative_mul (dirs : List Plane) {f g : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : Plane) :
    orderedDerivative dirs (fun y => f y * g y) x =
      ((splitDirections dirs).map fun s =>
        orderedDerivative s.1 f x * orderedDerivative s.2 g x).sum := by
  induction dirs generalizing x with
  | nil => simp [orderedDerivative, splitDirections]
  | cons v dirs ih =>
    let a (s : List Plane × List Plane) (y : Plane) :=
      orderedDerivative s.1 f y * orderedDerivative s.2 g y
    have hSmooth (s : List Plane × List Plane) : ContDiff ℝ ∞ (a s) :=
      (contDiff_orderedDerivative s.1 hf).mul (contDiff_orderedDerivative s.2 hg)
    have hEq : orderedDerivative dirs (fun y => f y * g y) =
        fun y => ((splitDirections dirs).map fun s => a s y).sum := funext ih
    change fderiv ℝ (orderedDerivative dirs (fun y => f y * g y)) x v = _
    rw [hEq, fderiv_list_sum_apply _ a hSmooth]
    have hEach (s : List Plane × List Plane) : fderiv ℝ (a s) x v =
        orderedDerivative (v :: s.1) f x * orderedDerivative s.2 g x +
          orderedDerivative s.1 f x * orderedDerivative (v :: s.2) g x := by
      change fderiv ℝ (fun y => orderedDerivative s.1 f y * orderedDerivative s.2 g y) x v = _
      rw [fderiv_fun_mul (((contDiff_orderedDerivative s.1 hf).differentiable (by simp)) x)
        (((contDiff_orderedDerivative s.2 hg).differentiable (by simp)) x)]
      simp only [add_apply, smul_apply, smul_eq_mul,
        orderedDerivative]
      ring
    simp only [hEach, List.sum_map_add, splitDirections, List.map_append, List.sum_append, List.map_map]
    rfl

public theorem orderedDerivative_ofFn (j : ℕ) {f : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (x : Plane) (v : Fin j → Plane) :
    orderedDerivative (List.ofFn v) f x = iteratedFDeriv ℝ j f x v := by
  induction j generalizing x with
  | zero => simp [orderedDerivative]
  | succ j ih =>
    rw [List.ofFn_succ]
    change fderiv ℝ (orderedDerivative (List.ofFn (Fin.tail v)) f) x (v 0) = _
    rw [show orderedDerivative (List.ofFn (Fin.tail v)) f =
      fun y => iteratedFDeriv ℝ j f y (Fin.tail v) from funext fun y => ih y (Fin.tail v)]
    symm
    exact (((hf.iteratedFDeriv_right (m := 1) (i := j) (by simp)).differentiable (by decide)) x)
      |>.iteratedFDeriv_succ_apply_left'

/-- The iterated Fréchet derivative product formula evaluated on an ordered
tuple. Each list entry represents one subset of positions. -/
public theorem iteratedFDeriv_mul_ordered (j : ℕ) {f g : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : Plane) (v : Fin j → Plane) :
    iteratedFDeriv ℝ j (fun y => f y * g y) x v =
      ((splitDirections (List.ofFn v)).map fun s =>
        orderedDerivative s.1 f x * orderedDerivative s.2 g x).sum := by
  rw [← orderedDerivative_ofFn j (hf.mul hg) x v]
  exact orderedDerivative_mul (List.ofFn v) hf hg x

/-- One choice of which factor receives each derivative position. -/
private inductive SlotMask : ℕ → Type
  | nil : SlotMask 0
  | left {n : ℕ} : SlotMask n → SlotMask (n + 1)
  | right {n : ℕ} : SlotMask n → SlotMask (n + 1)

private def SlotMask.leftCount {n : ℕ} : SlotMask n → ℕ
  | .nil => 0
  | .left p => p.leftCount + 1
  | .right p => p.leftCount

private def SlotMask.rightCount {n : ℕ} : SlotMask n → ℕ
  | .nil => 0
  | .left p => p.rightCount
  | .right p => p.rightCount + 1

private theorem SlotMask.count_sum {n : ℕ} (p : SlotMask n) :
    p.leftCount + p.rightCount = n := by
  induction p <;> simp only [SlotMask.leftCount, SlotMask.rightCount] <;> omega

private def allSlots (n : ℕ) : List (SlotMask n) :=
  match n with
  | 0 => [.nil]
  | n + 1 => (allSlots n).map SlotMask.left ++ (allSlots n).map SlotMask.right

private def splitWord {α : Type*} {n : ℕ} (p : SlotMask n) (v : Fin n → α) :
    (Fin p.leftCount → α) × (Fin p.rightCount → α) :=
  match p with
  | .nil => (v, v)
  | .left q =>
      let parts := splitWord q (Fin.tail v)
      (Fin.cons (v 0) parts.1, parts.2)
  | .right q =>
      let parts := splitWord q (Fin.tail v)
      (parts.1, Fin.cons (v 0) parts.2)

private def joinWord {α : Type*} {n : ℕ} (p : SlotMask n)
    (v : (Fin p.leftCount → α) × (Fin p.rightCount → α)) : Fin n → α :=
  match p with
  | .nil => v.1
  | .left q => Fin.cons (v.1 (0 : Fin (q.leftCount + 1))) (joinWord q (Fin.tail v.1, v.2))
  | .right q => Fin.cons (v.2 (0 : Fin (q.rightCount + 1))) (joinWord q (v.1, Fin.tail v.2))

private theorem join_splitWord {α : Type*} {n : ℕ} (p : SlotMask n) (v : Fin n → α) :
    joinWord p (splitWord p v) = v := by
  induction p with
  | nil => rfl
  | @left n q ih =>
    let l : Fin q.leftCount → α := (splitWord q (Fin.tail v)).1
    let r : Fin q.rightCount → α := (splitWord q (Fin.tail v)).2
    let w : Fin (q.leftCount + 1) → α := Fin.cons (α := fun _ => α) (v 0) l
    change Fin.cons (α := fun _ : Fin (n + 1) => α) (w 0)
      (joinWord q (Fin.tail w, r)) = v
    have hHead : w 0 = v 0 := Fin.cons_zero _ _
    have hTail : Fin.tail w = l := Fin.tail_cons _ _
    rw [hHead, hTail]
    change Fin.cons (v 0) (joinWord q (splitWord q (Fin.tail v))) = v
    rw [ih]
    exact Fin.cons_self_tail v
  | @right n q ih =>
    let l : Fin q.leftCount → α := (splitWord q (Fin.tail v)).1
    let r : Fin q.rightCount → α := (splitWord q (Fin.tail v)).2
    let w : Fin (q.rightCount + 1) → α := Fin.cons (α := fun _ => α) (v 0) r
    change Fin.cons (α := fun _ : Fin (n + 1) => α) (w 0)
      (joinWord q (l, Fin.tail w)) = v
    have hHead : w 0 = v 0 := Fin.cons_zero _ _
    have hTail : Fin.tail w = r := Fin.tail_cons _ _
    rw [hHead, hTail]
    change Fin.cons (v 0) (joinWord q (splitWord q (Fin.tail v))) = v
    rw [ih]
    exact Fin.cons_self_tail v

private theorem split_joinWord {α : Type*} {n : ℕ} (p : SlotMask n)
    (v : (Fin p.leftCount → α) × (Fin p.rightCount → α)) :
    splitWord p (joinWord p v) = v := by
  induction p with
  | nil => exact Prod.ext rfl (funext fun i => Fin.elim0 i)
  | left q ih =>
    simp only [joinWord, splitWord, Fin.cons_zero, Fin.tail_cons, ih]
    exact Prod.ext (Fin.cons_self_tail (n := q.leftCount) v.1) rfl
  | right q ih =>
    simp only [joinWord, splitWord, Fin.cons_zero, Fin.tail_cons, ih]
    exact Prod.ext rfl (Fin.cons_self_tail (n := q.rightCount) v.2)

private def splitWordEquiv {α : Type*} {n : ℕ} (p : SlotMask n) :
    (Fin n → α) ≃ ((Fin p.leftCount → α) × (Fin p.rightCount → α)) :=
  ⟨splitWord p, joinWord p, join_splitWord p, split_joinWord p⟩

private theorem splitDirections_eq_mask {n : ℕ} (v : Fin n → Plane) :
    splitDirections (List.ofFn v) =
      (allSlots n).map fun p => (List.ofFn (splitWord p v).1, List.ofFn (splitWord p v).2) := by
  induction n with
  | zero => simp [splitDirections, allSlots, splitWord, SlotMask.leftCount, SlotMask.rightCount, List.ofFn_zero]
  | succ n ih =>
    simp only [List.ofFn_succ, splitDirections, allSlots, List.map_append, List.map_map]
    rw [ih]
    simp only [List.map_map, Function.comp_def]
    apply congrArg₂ List.append
    · apply List.map_congr_left
      intro p _
      exact Prod.ext (List.ofFn_cons (v 0) (splitWord p (Fin.tail v)).1).symm rfl
    · apply List.map_congr_left
      intro p _
      exact Prod.ext rfl (List.ofFn_cons (v 0) (splitWord p (Fin.tail v)).2).symm

private theorem sum_slots_weight (n : ℕ) (w : ℕ → ℝ) :
    ((allSlots n).map fun p => w p.leftCount).sum =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * w i := by
  induction n generalizing w with
  | zero => simp [allSlots, SlotMask.leftCount]
  | succ n ih =>
    simp only [allSlots, List.map_append, List.sum_append, List.map_map]
    change ((allSlots n).map fun p => w (p.leftCount + 1)).sum +
      ((allSlots n).map fun p => w p.leftCount).sum = _
    rw [ih (fun i => w (i + 1)), ih w]
    have hShift :
        (∑ i ∈ Finset.range (n + 1), (n.choose (i + 1) : ℝ) * w (i + 1)) + w 0 =
          ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * w i := by
      rw [Finset.sum_range_succ (n := n), Nat.choose_eq_zero_of_lt n.lt_succ_self]
      simp only [Nat.cast_zero, zero_mul, add_zero]
      rw [Finset.sum_range_succ' (n := n)]
      simp
    rw [Finset.sum_range_succ' (n := n + 1)]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.choose_succ_succ, Nat.cast_add,
      add_mul, Finset.sum_add_distrib]
    rw [← hShift]
    ac_rfl

private noncomputable def wordVector {n : ℕ} (a : (Fin n → Fin 2) → ℝ) :
    EuclideanSpace ℝ (Fin n → Fin 2) :=
  WithLp.toLp 2 a

private theorem norm_wordVector_mul_split {n : ℕ} (p : SlotMask n)
    (a : (Fin p.leftCount → Fin 2) → ℝ) (b : (Fin p.rightCount → Fin 2) → ℝ) :
    ‖wordVector (fun v => a (splitWord p v).1 * b (splitWord p v).2)‖ =
      ‖wordVector a‖ * ‖wordVector b‖ := by
  simp only [wordVector, PiLp.norm_eq_of_L2, Real.norm_eq_abs, sq_abs]
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  congr 1
  calc
    _ = ∑ z : (Fin p.leftCount → Fin 2) × (Fin p.rightCount → Fin 2),
        (a z.1 * b z.2) ^ 2 :=
      Fintype.sum_equiv (splitWordEquiv p) _ _ (fun _ => rfl)
    _ = _ := by
      simp only [mul_pow, Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul]

private theorem norm_wordVector_list_sum_le {n : ℕ} {ι : Type*} (l : List ι)
    (A : ι → (Fin n → Fin 2) → ℝ) :
    ‖wordVector (fun v => (l.map fun p => A p v).sum)‖ ≤
      (l.map fun p => ‖wordVector (A p)‖).sum := by
  induction l with
  | nil =>
    change ‖wordVector (0 : (Fin n → Fin 2) → ℝ)‖ ≤ 0
    simp [wordVector]
  | cons p l ih =>
    simp only [List.map_cons, List.sum_cons]
    have heq : wordVector (fun v => A p v + (l.map fun q => A q v).sum) =
        wordVector (A p) + wordVector (fun v => (l.map fun q => A q v).sum) := rfl
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ih)

private theorem splitWord_comp {α β : Type*} {n : ℕ} (p : SlotMask n) (k : α → β) (v : Fin n → α) :
    splitWord p (k ∘ v) =
      (k ∘ (splitWord p v).1, k ∘ (splitWord p v).2) := by
  induction p with
  | nil => rfl
  | @left n q ih =>
    change (Fin.cons (k (v 0)) (splitWord q (k ∘ Fin.tail v)).1,
      (splitWord q (k ∘ Fin.tail v)).2) =
      (k ∘ Fin.cons (v 0) (splitWord q (Fin.tail v)).1, k ∘ (splitWord q (Fin.tail v)).2)
    rw [ih]
    exact Prod.ext (by funext j; cases j using Fin.cases <;> rfl) rfl
  | right q ih =>
    change ((splitWord q (k ∘ Fin.tail v)).1,
      Fin.cons (k (v 0)) (splitWord q (k ∘ Fin.tail v)).2) =
      (k ∘ (splitWord q (Fin.tail v)).1, k ∘ Fin.cons (v 0) (splitWord q (Fin.tail v)).2)
    rw [ih]
    exact Prod.ext rfl (by funext j; cases j using Fin.cases <;> rfl)

/-- The product rule in Hilbert–Schmidt norm, with exact binomial
multiplicities for the ordered derivative positions. -/
public theorem tensorHS_iteratedFDeriv_mul_le (n : ℕ) {f g : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : Plane) :
    tensorHS (iteratedFDeriv ℝ n (fun y => f y * g y) x) ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (tensorHS (iteratedFDeriv ℝ i f x) * tensorHS (iteratedFDeriv ℝ (n - i) g x)) := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  let a (i : ℕ) (v : Fin i → Fin 2) := iteratedFDeriv ℝ i f x (fun j => b (v j))
  let c (i : ℕ) (v : Fin i → Fin 2) := iteratedFDeriv ℝ i g x (fun j => b (v j))
  let D (p : SlotMask n) (v : Fin n → Fin 2) :=
    a p.leftCount (splitWord p v).1 * c p.rightCount (splitWord p v).2
  have hA (i : ℕ) : ‖wordVector (a i)‖ = tensorHS (iteratedFDeriv ℝ i f x) := rfl
  have hC (i : ℕ) : ‖wordVector (c i)‖ = tensorHS (iteratedFDeriv ℝ i g x) := rfl
  have hD (p : SlotMask n) : ‖wordVector (D p)‖ =
      tensorHS (iteratedFDeriv ℝ p.leftCount f x) *
        tensorHS (iteratedFDeriv ℝ (n - p.leftCount) g x) := by
    have hr : p.rightCount = n - p.leftCount := by have hs := p.count_sum; omega
    rw [show D p = (fun v => a p.leftCount (splitWord p v).1 * c p.rightCount (splitWord p v).2)
      from rfl, norm_wordVector_mul_split, hA, hC, hr]
  have hTensor : tensorCoordinates n (iteratedFDeriv ℝ n (fun y => f y * g y) x) =
      wordVector (fun v => ((allSlots n).map fun p => D p v).sum) := by
    ext v
    change iteratedFDeriv ℝ n (fun y => f y * g y) x (b ∘ v) =
      ((allSlots n).map fun p => D p v).sum
    rw [iteratedFDeriv_mul_ordered n hf hg x, splitDirections_eq_mask, List.map_map]
    congr 1
    apply List.map_congr_left
    intro p _
    simp only [Function.comp_apply, orderedDerivative_ofFn _ hf, orderedDerivative_ofFn _ hg]
    rw [splitWord_comp p (⇑b) v]
    rfl
  rw [tensorHS, hTensor]
  refine (norm_wordVector_list_sum_le (allSlots n) D).trans_eq ?_
  simp only [hD]
  exact sum_slots_weight n (fun i =>
    tensorHS (iteratedFDeriv ℝ i f x) * tensorHS (iteratedFDeriv ℝ (n - i) g x))

private theorem sum_word_prod_sq (j : ℕ) (d : Fin 2 → ℝ) :
    (∑ v : Fin j → Fin 2, (∏ i, d (v i)) ^ 2) = (∑ i, d i ^ 2) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    let E := (Fin.consEquiv (fun _ : Fin (j + 1) => Fin 2)).symm
    calc
      _ = ∑ p : Fin 2 × (Fin j → Fin 2), d p.1 ^ 2 * (∏ i, d (p.2 i)) ^ 2 := by
        apply Fintype.sum_equiv E
        intro v
        change (∏ i, d (v i)) ^ 2 = d (v 0) ^ 2 * (∏ i, d (Fin.tail v i)) ^ 2
        rw [Fin.prod_univ_succ, mul_pow]
        rfl
      _ = (∑ i, d i ^ 2) * (∑ v : Fin j → Fin 2, (∏ i, d (v i)) ^ 2) := by
        simp only [Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul]
      _ = _ := by rw [ih, pow_succ']

private theorem tensorHS_phase_derivative_le {i j : ℕ} (hi : i ≤ j) (e L : ℝ) (hL : 0 < L)
    (d : Plane →L[ℝ] ℝ) (x : Plane) :
    tensorHS (iteratedFDeriv ℝ (j - i) (profilePrimitive e j ∘ (L • d)) x) ≤
      (2 : ℝ) ^ i * (L * ‖d‖) ^ (j - i) := by
  let A : Plane →L[ℝ] ℝ := L • d
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  have hSmooth := (profilePrimitive_properties e j).1
  have hA : ‖A‖ = L * ‖d‖ := by
    simp only [A, norm_smul, Real.norm_eq_abs, abs_of_pos hL]
  have hDual : ‖A‖ ^ 2 = ∑ ℓ, A (b ℓ) ^ 2 := b.norm_dual A
  have hDeriv (v : Fin (j - i) → Plane) :
      iteratedFDeriv ℝ (j - i) (profilePrimitive e j ∘ A) x v =
        iteratedDeriv (j - i) (profilePrimitive e j) (A x) * ∏ ℓ, A (v ℓ) := by
    rw [A.iteratedFDeriv_comp_right hSmooth x (by simp)]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul]
    ring
  have hPower : (‖A‖ ^ 2) ^ (j - i) = (‖A‖ ^ (j - i)) ^ 2 := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 (j - i)]
  have hAbs := abs_iteratedDeriv_profilePrimitive_le e hi (A x)
  change tensorHS (iteratedFDeriv ℝ (j - i) (profilePrimitive e j ∘ A) x) ≤ _
  rw [tensorHS_eq_sqrt_sum, ← hA]
  change √(∑ v : Fin (j - i) → Fin 2,
    ‖iteratedFDeriv ℝ (j - i) (profilePrimitive e j ∘ A) x (fun ℓ => b (v ℓ))‖ ^ 2) ≤ _
  simp only [hDeriv, Real.norm_eq_abs, sq_abs, mul_pow]
  have hWord := sum_word_prod_sq (j - i) (fun z : Fin 2 => A (b z))
  rw [← Finset.mul_sum, hWord, ← hDual, hPower]
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right (by
    rw [← sq_abs (iteratedDeriv (j - i) (profilePrimitive e j) (A x))]
    exact pow_le_pow_left₀ (abs_nonneg _) hAbs 2) (sq_nonneg _)

private theorem tensorHS_smul {n : ℕ} (c : ℝ) (A : Plane [×n]→L[ℝ] ℝ) :
    tensorHS (c • A) = |c| * tensorHS A := by
  rw [tensorHS, map_smul, norm_smul, Real.norm_eq_abs, tensorHS]

set_option maxHeartbeats 650000 in
/-- The Hilbert–Schmidt bound for the highest-order remainder, with the
binomial coefficients of the product rule for the second and fourth potentials. -/
public theorem tensorHS_oscillatoryRemainder_le (j : ℕ) {χ : Plane → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (e γ L : ℝ) (hL : 1 ≤ L) (d : Plane →L[ℝ] ℝ) (x : Plane) :
    tensorHS (oscillatoryRemainder j χ e γ L d x) ≤
      (|γ| / L) * ∑ i ∈ (Finset.range (j + 1)).erase 0,
        (j.choose i : ℝ) * (tensorHS (iteratedFDeriv ℝ i χ x) * (‖d‖ ^ (j - i) * (2 : ℝ) ^ i)) := by
  let η (y : Plane) := χ y - χ x
  let ψ := profilePrimitive e j ∘ (L • d)
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hη : ContDiff ℝ ∞ η := hχ.sub contDiff_const
  have hψ : ContDiff ℝ ∞ ψ := (profilePrimitive_properties e j).1.comp (L • d).contDiff
  have hSub := iteratedFDeriv_sub_apply (x := x)
    (f := oscillatoryPotential j χ e γ L d)
    (g := oscillatoryPotential j (fun _ => χ x) e γ L d)
    ((contDiff_oscillatoryPotential j hχ e γ L d).of_le (show (j : ℕ∞ω) ≤ ∞ by simp)).contDiffAt
    ((contDiff_oscillatoryPotential j contDiff_const e γ L d).of_le
      (show (j : ℕ∞ω) ≤ ∞ by simp)).contDiffAt
  have hEq : oscillatoryPotential j χ e γ L d - oscillatoryPotential j (fun _ => χ x) e γ L d =
      fun y => (γ / L ^ j) • (η y * ψ y) := by
    funext y
    simp only [oscillatoryPotential, η, ψ, Pi.sub_apply, Function.comp_apply, smul_eq_mul]
    ring
  have hDeriv : oscillatoryRemainder j χ e γ L d x =
      (γ / L ^ j) • iteratedFDeriv ℝ j (fun y => η y * ψ y) x := by
    unfold oscillatoryRemainder
    rw [← hSub, hEq, iteratedFDeriv_const_smul_apply' (((hη.mul hψ).of_le
      (show (j : ℕ∞ω) ≤ ∞ by simp)).contDiffAt)]
  rw [hDeriv, tensorHS_smul, abs_div, abs_pow, abs_of_pos hLp]
  let T (i : ℕ) := (j.choose i : ℝ) *
    (tensorHS (iteratedFDeriv ℝ i η x) * tensorHS (iteratedFDeriv ℝ (j - i) ψ x))
  have hη0 : iteratedFDeriv ℝ 0 η x = 0 := by
    ext v
    simp [η]
  have hVanishing : T 0 = 0 := by simp [T, hη0, tensorHS]
  have hSum := tensorHS_iteratedFDeriv_mul_le j hη hψ x
  change tensorHS (iteratedFDeriv ℝ j (fun y => η y * ψ y) x) ≤
    ∑ i ∈ Finset.range (j + 1), T i at hSum
  have hz : 0 ∈ Finset.range (j + 1) := Finset.mem_range.mpr j.succ_pos
  rw [← Finset.sum_erase_add _ _ hz, hVanishing, add_zero] at hSum
  refine (mul_le_mul_of_nonneg_left hSum (by positivity)).trans ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hne := (Finset.mem_erase.mp hi).1
  have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_erase.mp hi).2)
  have hEta : iteratedFDeriv ℝ i η x = iteratedFDeriv ℝ i χ x := by
    change iteratedFDeriv ℝ i (χ - fun _ : Plane => χ x) x = _
    rw [iteratedFDeriv_sub_apply (hχ.contDiffAt.of_le (by simp)) contDiffAt_const,
      iteratedFDeriv_const_of_ne hne, Pi.zero_apply, sub_zero]
  have hFreq : L ≤ L ^ i := by
    simpa only [pow_one] using pow_le_pow_right₀ hL (Nat.pos_of_ne_zero hne)
  have hLpower : L ^ i * L ^ (j - i) = L ^ j := by rw [← pow_add, Nat.add_sub_of_le hij]
  calc
    _ ≤ (|γ| / L ^ j) *
        ((j.choose i : ℝ) * (tensorHS (iteratedFDeriv ℝ i χ x) * ((2 : ℝ) ^ i * (L * ‖d‖) ^ (j - i)))) := by
      change (|γ| / L ^ j) * ((j.choose i : ℝ) *
        (tensorHS (iteratedFDeriv ℝ i η x) * tensorHS (iteratedFDeriv ℝ (j - i) ψ x))) ≤ _
      rw [hEta]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (tensorHS_phase_derivative_le hij e L hLp d x) (norm_nonneg _))
        (Nat.cast_nonneg _)) (by positivity)
    _ = (|γ| / L ^ i) *
      ((j.choose i : ℝ) * (tensorHS (iteratedFDeriv ℝ i χ x) * (‖d‖ ^ (j - i) * (2 : ℝ) ^ i))) := by
      rw [mul_pow, ← hLpower]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left (abs_nonneg _) hLp hFreq) (by unfold tensorHS; positivity)

end C2Riemannian
