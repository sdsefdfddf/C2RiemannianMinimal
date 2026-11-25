module

public import C2Riemannian.RealizationInvariant
public import C2Riemannian.LayerFrequencyContract
public import C2Riemannian.IdealSchedule
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! # Matching one physical layer with the ideal children (M25) -/

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped BigOperators ContDiff Topology

namespace C2Riemannian

/-- A planar vector given by its two Cartesian coordinates. -/
@[expose] public noncomputable def coordinateDirection (nx ny : ℝ) : Plane :=
  WithLp.toLp 2 ![nx, ny]

private theorem inner_coordinateDirection_basis (nx ny : ℝ) (i : Fin 2) :
    inner ℝ (coordinateDirection nx ny) (EuclideanSpace.basisFun (Fin 2) ℝ i) =
      (![nx, ny] : Fin 2 → ℝ) i :=
  EuclideanSpace.inner_basisFun_real (Fin 2) (coordinateDirection nx ny) i

namespace IdealLayer

/-- The normal in the current row of the ideal schedule. -/
@[expose] public noncomputable def normal (layer : IdealLayer) (s : ℝ) : Plane :=
  match layer.step with
  | .vertical => coordinateDirection 0 1
  | .first => coordinateDirection 1 s
  | .second | .fourth => coordinateDirection 1 0
  | .third => coordinateDirection 1 (-s)

/-- The second-order amplitude before applying the child's sign. -/
@[expose] public noncomputable def secondAmplitude (layer : IdealLayer) (node : IdealNode) : ℝ :=
  match layer.step with
  | .vertical => 1
  | .first | .third => -node.sigma
  | .second | .fourth => node.sigma

/-- The fourth-order amplitude before applying the child's sign. -/
@[expose] public noncomputable def fourthAmplitude (layer : IdealLayer) : ℝ :=
  match layer.step with
  | .vertical => 0
  | _ => 2 ^ layer.priorTableSteps

public theorem normal_ne_zero (layer : IdealLayer) (s : ℝ) : layer.normal s ≠ 0 := by
  intro hh
  cases layer with
  | mk step count =>
    cases step
    · have h := congrArg (fun z : Plane => z 1) hh
      simp [normal, coordinateDirection] at h
    all_goals
      have h := congrArg (fun z : Plane => z 0) hh
      simp [normal, coordinateDirection] at h

end IdealLayer

/-- The Cartesian basis tuple specified by a word of length `j`. -/
@[expose] public noncomputable def basisWord {j : ℕ} (w : Fin j → Fin 2) : Fin j → Plane :=
  fun i => EuclideanSpace.basisFun (Fin 2) ℝ (w i)

/-- Equality on basis words determines the full continuous multilinear tensor. -/
public theorem eq_of_basisWord_eq {j : ℕ} {A B : Plane [×j]→L[ℝ] ℝ}
    (h : ∀ w : Fin j → Fin 2, A (basisWord w) = B (basisWord w)) : A = B :=
  ContinuousMultilinearMap.toMultilinearMap_injective
    (Module.Basis.ext_multilinear (fun _ => (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis) h)

/-- The value of the Hessian on one Cartesian basis pair. -/
@[expose] public def secondWordValue (A : ScalarHess) (w : Fin 2 → Fin 2) : ℝ :=
  if w 0 = 0 then
    if w 1 = 0 then A.xx else A.xy
  else
    if w 1 = 0 then A.xy else A.yy

/-- Number of vertical entries in a Cartesian basis word. -/
@[expose] public def wordWeight {j : ℕ} (w : Fin j → Fin 2) : Fin (j + 1) :=
  ⟨∑ i, (w i).val, Nat.lt_succ_of_le (calc
    (∑ i, (w i).val) ≤ ∑ _i : Fin j, (1 : ℕ) :=
      Finset.sum_le_sum fun i _ => Nat.le_of_lt_succ (w i).isLt
    _ = j := by simp)⟩

/-- Each second-order tensor coefficient matches the ideal symmetric Hessian. -/
@[expose] public noncomputable def matchesSecondJet (W : Plane → ℝ) (x : Plane) (node : IdealNode) : Prop :=
  ∀ w : Fin 2 → Fin 2, iteratedFDeriv ℝ 2 W x (basisWord w) = secondWordValue node.scalar w

/-- Each fourth-order tensor coefficient matches the ideal entry with that
number of vertical slots. -/
@[expose] public noncomputable def matchesFourthJet (W : Plane → ℝ) (x : Plane) (node : IdealNode) : Prop :=
  ∀ w : Fin 4 → Fin 2, iteratedFDeriv ℝ 4 W x (basisWord w) = node.fourth (wordWeight w)

private theorem secondWordValue_rankOneUpdate (A : ScalarHess) (c nx ny : ℝ)
    (w : Fin 2 → Fin 2) :
    secondWordValue (A.rankOneUpdate c nx ny) w =
      secondWordValue A w +
        c * ∏ i, inner ℝ (coordinateDirection nx ny) (basisWord w i) := by
  simp only [secondWordValue, Fin.prod_univ_two, basisWord, inner_coordinateDirection_basis,
    ScalarHess.rankOneUpdate]
  generalize h₀ : w 0 = i
  generalize h₁ : w 1 = j
  fin_cases i <;> fin_cases j <;> simp [pow_two, mul_comm, mul_left_comm]

private theorem prod_inner_slope {j : ℕ} (t : ℝ) (w : Fin j → Fin 2) :
    (∏ i, inner ℝ (coordinateDirection 1 t) (basisWord w i)) = t ^ (wordWeight w).val := by
  have h (i : Fin j) : inner ℝ (coordinateDirection 1 t) (basisWord w i) = t ^ (w i).val := by
    rw [basisWord, inner_coordinateDirection_basis]
    generalize h : w i = b
    fin_cases b <;> simp
  simp only [h, wordWeight, Finset.prod_pow_eq_pow_sum]

/-- The ideal child rule agrees with the signed second-order rank-one update
on every Cartesian basis pair. -/
public theorem idealChild_secondWord (layer : IdealLayer) (node : IdealNode)
    (s : ℝ) (positive : Bool) (w : Fin 2 → Fin 2) :
    secondWordValue (node.child layer s positive).scalar w =
      secondWordValue node.scalar w +
        childSign positive * layer.secondAmplitude node *
          ∏ i, inner ℝ (layer.normal s) (basisWord w i) := by
  cases layer with
  | mk step count =>
    cases step <;>
      simp only [IdealNode.child, SplitStep.scalarChild, IdealLayer.normal, IdealLayer.secondAmplitude,
        childSign, mul_one, secondWordValue_rankOneUpdate]

/-- The ideal fourth-order update is the same rank-one update on every
Cartesian basis word, including the zero-amplitude vertical step. -/
public theorem idealChild_fourthWord (layer : IdealLayer) (node : IdealNode)
    (s : ℝ) (positive : Bool) (w : Fin 4 → Fin 2) :
    (node.child layer s positive).fourth (wordWeight w) =
      node.fourth (wordWeight w) +
        childSign positive * layer.fourthAmplitude *
          ∏ i, inner ℝ (layer.normal s) (basisWord w i) := by
  cases layer with
  | mk step count =>
    cases step <;>
      simp only [IdealNode.child, IdealLayer.normal, IdealLayer.fourthAmplitude, childSign,
        prod_inner_slope, mul_zero, zero_mul, add_zero]

/-- Every pair of a physical parent label and a sign has its corresponding
ideal history, and distinct labels give distinct histories. -/
public theorem child_history_injective {ι : Type*} (node : ι → IdealNode)
    (hParent : Function.Injective fun i => (node i).history) (layer : IdealLayer) (s : ℝ) :
    Function.Injective fun p : ι × Bool => ((node p.1).child layer s p.2).history := by
  intro p q hpq
  have h : (node p.1).history ++ [p.2] = (node q.1).history ++ [q.2] := hpq
  have hLen : (node p.1).history.length = (node q.1).history.length := by
    have h' := congrArg List.length h
    simpa only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] using h'
  obtain ⟨hParents, hSigns⟩ := List.append_inj h hLen
  exact Prod.ext (hParent hParents) (List.cons.inj hSigns).1

/-- The explicit bijection between physical children and their ideal history image. -/
@[expose] public noncomputable def childHistoryEquiv {ι : Type*} (node : ι → IdealNode)
    (hParent : Function.Injective fun i => (node i).history) (layer : IdealLayer) (s : ℝ) :
    (ι × Bool) ≃ Set.range (fun p : ι × Bool => ((node p.1).child layer s p.2).history) :=
  Equiv.ofInjective _ (child_history_injective node hParent layer s)

/-- M22 chooses actual frequencies for every parent of this ideal layer. -/
public theorem exists_ideal_layer_frequency_contract {ι : Type*} [Finite ι]
    {P : ι → Set Plane} (hBound : ∀ i, Bornology.IsBounded (P i))
    (E : ∀ i, InteriorExhaustion (P i)) (layer : IdealLayer) (node : ι → IdealNode)
    (s : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    Nonempty (LayerFrequencyContract P E (fun _ => layer.normal s)
      (fun i => layer.secondAmplitude (node i)) (fun _ => layer.fourthAmplitude) δ) :=
  exists_layer_frequency_contract hBound E (fun _ => layer.normal s)
    (fun _ => layer.normal_ne_zero s) (fun i => layer.secondAmplitude (node i))
    (fun _ => layer.fourthAmplitude) hδ hδ'

section PhysicalLayer

variable {ι : Type*} {P : ι → Set Plane} {E : ∀ i, InteriorExhaustion (P i)}
  {n : ι → Plane} {b a : ι → ℝ} {δ : ℝ}

/-- The child region associated to a frequency-contract entry. -/
@[expose] public noncomputable def realizedChild (C : LayerFrequencyContract P E n b a δ)
    (k : ℕ) (i : ι) (positive : Bool) : Set Plane :=
  childPlatform (C.inner k i) positive (C.width k) (C.frequency k) (n i)

/-- The actual scalar potential after adding the order-`j` oscillations for
all active parents. -/
@[expose] public noncomputable def realizedLayerPotential (C : LayerFrequencyContract P E n b a δ)
    (I : Finset ι) (k j : ℕ) (γ : ι → ℝ) (W : Plane → ℝ) : Plane → ℝ :=
  addLayer I W (fun i => oscillatoryPotential j (C.cutoff k i) (C.width k)
    (γ i) (C.frequency k) (innerSL ℝ (n i)))

/-- Children at distinct physical labels are disjoint, including children of
different parents and opposite-sign children of a single parent. -/
public theorem realizedChild_pairwiseDisjoint (C : LayerFrequencyContract P E n b a δ)
    (hP : Pairwise fun i j => Disjoint (P i) (P j)) (k : ℕ) :
    Pairwise (fun p q : ι × Bool => Disjoint (realizedChild C k p.1 p.2) (realizedChild C k q.1 q.2)) := by
  intro p q hpq
  by_cases hp : p.1 = q.1
  · have hsign : p.2 ≠ q.2 := fun h => hpq (Prod.ext hp h)
    cases p with
    | mk i positive =>
      cases q with
      | mk l other =>
        dsimp at hp
        subst l
        cases positive <;> cases other
        · exact (hsign rfl).elim
        · exact (childPlatform_disjoint _ (C.width_pos k) (C.width_le_one_sixteenth k)
            (C.frequency k) (n i)).symm
        · exact childPlatform_disjoint _ (C.width_pos k) (C.width_le_one_sixteenth k)
            (C.frequency k) (n i)
        · exact (hsign rfl).elim
  · exact (hP hp).mono (inter_subset_left.trans (C.inner_subset k p.1))
      (inter_subset_left.trans (C.inner_subset k q.1))

end PhysicalLayer

/-- On each physical child the two new potentials match the ideal child's
second and fourth tensors, coefficient by coefficient. -/
public theorem realizedLayerIdeal_jets {ι : Type*} {P : ι → Set Plane}
    {E : ∀ i, InteriorExhaustion (P i)} {δ : ℝ}
    (layer : IdealLayer) (node : ι → IdealNode) (s : ℝ)
    (C : LayerFrequencyContract P E (fun _ => layer.normal s)
      (fun i => layer.secondAmplitude (node i)) (fun _ => layer.fourthAmplitude) δ)
    (I : Finset ι) (hDisjoint : Set.PairwiseDisjoint (I : Set ι) P)
    (hOpen : ∀ i ∈ I, IsOpen (P i)) (hBound : ∀ i ∈ I, Bornology.IsBounded (P i))
    (k : ℕ) {W₂ W₄ : Plane → ℝ} (hW₂ : ContDiff ℝ ∞ W₂) (hW₄ : ContDiff ℝ ∞ W₄)
    (hSecond : ∀ i ∈ I, ∀ x ∈ P i, matchesSecondJet W₂ x (node i))
    (hFourth : ∀ i ∈ I, ∀ x ∈ P i, matchesFourthJet W₄ x (node i))
    {i : ι} (hi : i ∈ I) (positive : Bool) {x : Plane} (hx : x ∈ realizedChild C k i positive) :
    matchesSecondJet (realizedLayerPotential C I k 2 (fun i => layer.secondAmplitude (node i)) W₂)
      x ((node i).child layer s positive) ∧
    matchesFourthJet (realizedLayerPotential C I k 4 (fun _ => layer.fourthAmplitude) W₄)
      x ((node i).child layer s positive) := by
  have hxP := C.inner_subset k i hx.1
  have hL : (C.frequency k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (C.frequency_ge_one k))
  constructor
  · intro w
    change iteratedFDeriv ℝ 2 (addLayer I W₂ (fun q =>
      oscillatoryPotential 2 (quantitativeCutoff (P q) (E q).radius (k + C.shift))
        (C.width k) (layer.secondAmplitude (node q)) (C.frequency k)
        (innerSL ℝ (layer.normal s)))) x (basisWord w) = _
    rw [realize_layer_preserves_jets I hDisjoint hOpen hBound E (k + C.shift) 2
      (C.width_pos k) (C.width_le_one_sixteenth k) hL (fun q => layer.secondAmplitude (node q))
      (fun _ => layer.normal s) hW₂ hi positive hx (basisWord w), hSecond i hi x hxP w]
    exact (idealChild_secondWord layer (node i) s positive w).symm
  · intro w
    change iteratedFDeriv ℝ 4 (addLayer I W₄ (fun q =>
      oscillatoryPotential 4 (quantitativeCutoff (P q) (E q).radius (k + C.shift))
        (C.width k) layer.fourthAmplitude (C.frequency k)
        (innerSL ℝ (layer.normal s)))) x (basisWord w) = _
    rw [realize_layer_preserves_jets I hDisjoint hOpen hBound E (k + C.shift) 4
      (C.width_pos k) (C.width_le_one_sixteenth k) hL (fun _ => layer.fourthAmplitude)
      (fun _ => layer.normal s) hW₄ hi positive hx (basisWord w), hFourth i hi x hxP w]
    exact (idealChild_fourthWord layer (node i) s positive w).symm

end C2Riemannian
