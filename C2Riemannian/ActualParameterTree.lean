module

public import C2Riemannian.PhysicalParameterTree
public import C2Riemannian.IdealLayerRealization

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace C2Riemannian

@[expose] public noncomputable def idealPhysicalDirections : PhysicalDirections where
  normal := IdealLayer.normal
  secondAmplitude := IdealLayer.secondAmplitude
  fourthAmplitude := IdealLayer.fourthAmplitude

/-- Both classical tensors agree with the ideal node on each platform. -/
@[expose] public def PhysicalPrefix.ExactJets {Q : Set Plane} (p : PhysicalPrefix Q) : Prop :=
  ∀ i x, x ∈ p.platform i →
    matchesSecondJet p.secondPotential x (p.ideal i) ∧ matchesFourthJet p.fourthPotential x (p.ideal i)

public theorem exists_ideal_physical_row {Q : Set Plane} (hQ : Bornology.IsBounded Q)
    (p : PhysicalPrefix Q) (hp : p.ExactJets) (layer : IdealLayer) (s δ : ℝ)
    (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    ∃ next : ℕ → PhysicalPrefix Q, Nonempty (PhysicalLayerRow idealPhysicalDirections s δ layer p next) ∧
      ∀ k, (next k).ExactJets := by
  classical
  let P (i : p.Active) := p.platform i.1
  have hBound (i : p.Active) : Bornology.IsBounded (P i) := hQ.subset (p.platform_subset i.1)
  let E (i : p.Active) := Classical.choice
    (exhaust_parent (p.platform_open i.1) (p.platform_nonempty i.1) (hBound i))
  obtain ⟨C⟩ := exists_ideal_layer_frequency_contract hBound E layer
    (fun i : p.Active => p.ideal i.1) s hδ hδ'
  let L := (p.Active × Bool) ⊕ p.Stopped
  have : Fintype p.Stopped := Fintype.ofFinite (α := {i : p.Label // (p.ideal i).active = false})
  let A : L → IdealNode := Sum.elim
    (fun i => (p.ideal i.1.1).child layer s i.2) (fun i => p.ideal i.1)
  let S (k : ℕ) : L → Set Plane :=
    Sum.elim (fun i => realizedChild C k i.1 i.2) (fun i => p.platform i.1)
  have hSub (k : ℕ) (i : p.Active × Bool) : realizedChild C k i.1 i.2 ⊆ P i.1 :=
    inter_subset_left.trans (C.inner_subset k i.1)
  have hDis (i : p.Active) (j : p.Stopped) : Disjoint (P i) (p.platform j.1) :=
    p.platform_disjoint (fun h => by
      have hi := i.2
      rw [h, j.2] at hi
      contradiction)
  have hPair : Pairwise (fun i j => Disjoint (P i) (P j)) :=
    fun _ _ h => p.platform_disjoint (fun hij => h (Subtype.ext hij))
  let G (k j : ℕ) (amp : p.Active → ℝ) (i : p.Active) :=
    oscillatoryPotential j (C.cutoff k i) (C.width k) (amp i) (C.frequency k)
      (innerSL ℝ (layer.normal s))
  have hS (k j : ℕ) (amp : p.Active → ℝ) (i : p.Active) : tsupport (G k j amp i) ⊆ P i :=
    (tsupport_oscillatoryPotential_subset _ _ _ _ _ _).trans
      (quantitativeCutoff_spec (hBound i) (E i) (k + C.shift)).2.2.2.1
  have hSmooth (k j : ℕ) (amp : p.Active → ℝ) (i : p.Active) : ContDiff ℝ ∞ (G k j amp i) :=
    contDiff_oscillatoryPotential j (quantitativeCutoff_spec (hBound i) (E i) (k + C.shift)).1 _ _ _ _
  let b (i : p.Active) := layer.secondAmplitude (p.ideal i.1)
  let a (_ : p.Active) := layer.fourthAmplitude
  have h₂ (k : ℕ) := addLayer_smooth_supported Finset.univ hQ (G := G k 2 b)
    p.smooth_second p.support_second (fun i _ => hSmooth k 2 b i)
      (fun i _ => (hS k 2 b i).trans (p.platform_subset i.1))
  have h₄ (k : ℕ) := addLayer_smooth_supported Finset.univ hQ (G := G k 4 a)
    p.smooth_fourth p.support_fourth (fun i _ => hSmooth k 4 a i)
      (fun i _ => (hS k 4 a i).trans (p.platform_subset i.1))
  let next (k : ℕ) : PhysicalPrefix Q := {
    parameterIndices := p.parameterIndices ++ [k]
    Label := L
    ideal := A
    platform := S k
    platform_open := fun i => match i with
      | .inl (j, sign) => childPlatform_open (C.inner_open k j) sign _ _ _
      | .inr j => p.platform_open j.1
    platform_nonempty := fun i => match i with
      | .inl (j, sign) => C.child_nonempty k j sign
      | .inr j => p.platform_nonempty j.1
    platform_subset := fun i => match i with
      | .inl q => (hSub k q).trans (p.platform_subset q.1.1)
      | .inr q => p.platform_subset q.1
    platform_disjoint := by
      intro i j hij
      cases i with
      | inl i =>
        cases j with
        | inl j => exact realizedChild_pairwiseDisjoint C hPair k (fun h => hij (congrArg Sum.inl h))
        | inr j => exact (hDis i.1 j).mono_left (hSub k i)
      | inr i =>
        cases j with
        | inl j => exact ((hDis j.1 i).mono_left (hSub k j)).symm
        | inr j => exact p.platform_disjoint (fun h => hij (congrArg Sum.inr (Subtype.ext h)))
    has_active := by
      obtain ⟨i, hi⟩ := p.has_active
      exact ⟨Sum.inl (⟨i, hi⟩, true), layer.step.positive_continues⟩
    secondPotential := addLayer Finset.univ p.secondPotential (G k 2 b)
    fourthPotential := addLayer Finset.univ p.fourthPotential (G k 4 a)
    smooth_second := (h₂ k).1
    smooth_fourth := (h₄ k).1
    support_second := (h₂ k).2.2
    support_fourth := (h₄ k).2.2
  }
  refine ⟨next, ⟨{
    exhaustion := E
    frequencyContract := C
    childLabel := fun _ => ⟨Sum.inl, Sum.inl_injective⟩
    stoppedLabel := fun _ => ⟨Sum.inr, Sum.inr_injective⟩
    covers_labels := ?_
    disjoint_labels := ?_
    child_platform := fun _ _ _ => rfl
    child_ideal := fun _ _ _ => rfl
    stopped_platform := fun _ _ => rfl
    stopped_ideal := fun _ _ => rfl
    extends_prefix := fun _ => rfl
    extends_second := fun _ => rfl
    extends_fourth := fun _ => rfl }⟩, ?_⟩
  · intro k
    apply eq_univ_of_forall
    intro i
    cases i with
    | inl i => exact Or.inl ⟨i, rfl⟩
    | inr i => exact Or.inr ⟨i, rfl⟩
  · intro k
    apply Set.disjoint_left.mpr
    rintro i ⟨j, rfl⟩ ⟨q, h⟩
    change Sum.inr q = Sum.inl j at h
    contradiction
  · intro k i x hx
    cases i with
    | inl i =>
      exact realizedLayerIdeal_jets layer (fun j : p.Active => p.ideal j.1) s C Finset.univ
        p.active_pairwiseDisjoint (fun j _ => p.platform_open j.1) (fun j _ => hBound j) k
        p.smooth_second p.smooth_fourth (fun j _ y hy => (hp j.1 y hy).1)
        (fun j _ y hy => (hp j.1 y hy).2) (Finset.mem_univ i.1) i.2 hx
    | inr i =>
      have hNear (j : ℕ) (amp : p.Active → ℝ) (W : Plane → ℝ) :
          addLayer Finset.univ W (G k j amp) =ᶠ[𝓝 x] W :=
        addLayer_eventuallyEq_of_outside_supports _ _ _
          (fun q _ hq => Set.disjoint_left.mp (hDis q i) (hS k j amp q hq) hx)
      have hp' := hp i.1 x hx
      constructor
      · intro w
        exact (congrArg (fun T => T (basisWord w)) ((Filter.EventuallyEq.iteratedFDeriv ℝ (hNear 2 b p.secondPotential) 2).eq_of_nhds)).trans (hp'.1 w)
      · intro w
        exact (congrArg (fun T => T (basisWord w)) ((Filter.EventuallyEq.iteratedFDeriv ℝ (hNear 4 a p.fourthPotential) 4).eq_of_nhds)).trans (hp'.2 w)

public theorem exists_ideal_physical_tree {Q : Set Plane} (hQ : Bornology.IsBounded Q)
    (p : PhysicalPrefix Q) (hp : p.ExactJets) (layers : List IdealLayer) (s δ : ℝ)
    (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    Nonempty (PhysicalParameterTree idealPhysicalDirections s δ (fun _ q => q.ExactJets) layers p) :=
  PhysicalParameterTree.exists_of_layer_rows
    (fun layer _ q hq => exists_ideal_physical_row hQ q hq layer s δ hδ hδ') layers p hp

public theorem PhysicalPrefix.root_exactJets (Q : Set Plane) (hOpen : IsOpen Q)
    (hNonempty : Q.Nonempty) : (PhysicalPrefix.root Q hOpen hNonempty).ExactJets := by
  intro i x hx
  constructor
  · intro w
    change iteratedFDeriv ℝ 2 (0 : Plane → ℝ) x (basisWord w) = secondWordValue IdealNode.root.scalar w
    simp [IdealNode.root, secondWordValue, iteratedFDeriv_zero]
  · intro w
    change iteratedFDeriv ℝ 4 (0 : Plane → ℝ) x (basisWord w) = IdealNode.root.fourth (wordWeight w)
    simp [IdealNode.root, iteratedFDeriv_zero]

public theorem exists_root_ideal_physical_tree {Q : Set Plane} (hQ : Bornology.IsBounded Q)
    (hOpen : IsOpen Q) (hNonempty : Q.Nonempty) (layers : List IdealLayer) (s δ : ℝ)
    (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    Nonempty (PhysicalParameterTree idealPhysicalDirections s δ (fun _ q => q.ExactJets)
      layers (PhysicalPrefix.root Q hOpen hNonempty)) :=
  exists_ideal_physical_tree hQ _ (PhysicalPrefix.root_exactJets Q hOpen hNonempty) layers s δ hδ hδ'

/-- Realize every row of the prescribed split schedule from the zero potentials. -/
public theorem exists_scheduled_ideal_physical_tree {Q : Set Plane} (hQ : Bornology.IsBounded Q)
    (hOpen : IsOpen Q) (hNonempty : Q.Nonempty) (N J : ℕ) (s δ : ℝ)
    (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    Nonempty (PhysicalParameterTree idealPhysicalDirections s δ (fun _ q => q.ExactJets)
      (idealLayers 0 (SplitStep.schedule N J)) (PhysicalPrefix.root Q hOpen hNonempty)) :=
  exists_root_ideal_physical_tree hQ hOpen hNonempty _ s δ hδ hδ'

end C2Riemannian
