module

public import C2Riemannian.ParameterTreeRealization
public import C2Riemannian.LayerFrequencyContract
public import C2Riemannian.IdealSchedule
public import C2Riemannian.LayerGluing
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

open Filter Set
open scoped ContDiff Topology BigOperators

namespace C2Riemannian

/-- The value and first derivative of a finite layer obey the same pointwise
bound as a single correction when the parent platforms are disjoint. -/
public theorem addLayer_c1_difference_le {ι : Type*} (I : Finset ι)
    {P : ι → Set Plane} {W : Plane → ℝ} {G : ι → Plane → ℝ}
    (hDisjoint : Set.PairwiseDisjoint (I : Set ι) P)
    (hOpen : ∀ i ∈ I, IsOpen (P i)) (hSupport : ∀ i ∈ I, tsupport (G i) ⊆ P i)
    (hW : ContDiff ℝ ∞ W) (hG : ∀ i ∈ I, ContDiff ℝ ∞ (G i))
    {η : ℝ} (hη : 0 ≤ η)
    (hValue : ∀ i ∈ I, ∀ x ∈ P i, ‖G i x‖ ≤ η)
    (hGradient : ∀ i ∈ I, ∀ x ∈ P i, ‖fderiv ℝ (G i) x‖ ≤ η) (x : Plane) :
    ‖addLayer I W G x - W x‖ ≤ η ∧
      ‖fderiv ℝ (addLayer I W G) x - fderiv ℝ W x‖ ≤ η := by
  by_cases h : ∃ i ∈ I, x ∈ P i
  · obtain ⟨i, hi, hx⟩ := h
    have hOn := addLayer_eqOn_parent (f := W) hDisjoint hSupport hi
    have hNear : addLayer I W G =ᶠ[𝓝 x] (fun y => W y + G i y) :=
      eventually_of_mem ((hOpen i hi).mem_nhds hx) hOn
    have hn : fderiv ℝ (addLayer I W G) x = fderiv ℝ W x + fderiv ℝ (G i) x :=
      hNear.fderiv_eq.trans (fderiv_fun_add ((hW.differentiable (by simp)) x)
        (((hG i hi).differentiable (by simp)) x))
    constructor
    · rw [hOn hx, add_sub_cancel_left]
      exact hValue i hi x hx
    · rw [hn, add_sub_cancel_left]
      exact hGradient i hi x hx
  · have hNear := addLayer_eventuallyEq_of_outside_supports I W G
      (fun i hi hx => h ⟨i, hi, hSupport i hi hx⟩)
    rw [hNear.eq_of_nhds, hNear.fderiv_eq, sub_self, sub_self, norm_zero, norm_zero]
    exact ⟨hη, hη⟩

/-- One fixed physical realization at a prefix of the parameter tree. -/
public structure PhysicalPrefix (Q : Set Plane) where
  parameterIndices : List ℕ
  Label : Type
  [labelFintype : Fintype Label]
  ideal : Label → IdealNode
  platform : Label → Set Plane
  platform_open : ∀ i, IsOpen (platform i)
  platform_nonempty : ∀ i, (platform i).Nonempty
  platform_subset : ∀ i, platform i ⊆ Q
  platform_disjoint : Pairwise (fun i j => Disjoint (platform i) (platform j))
  has_active : ∃ i, (ideal i).active = true
  secondPotential : Plane → ℝ
  fourthPotential : Plane → ℝ
  smooth_second : ContDiff ℝ ∞ secondPotential
  smooth_fourth : ContDiff ℝ ∞ fourthPotential
  support_second : tsupport secondPotential ⊆ Q
  support_fourth : tsupport fourthPotential ⊆ Q

attribute [instance] PhysicalPrefix.labelFintype

namespace PhysicalPrefix

variable {Q : Set Plane}

/-- Labels of the platforms on which the next layer acts. -/
@[expose] public def Active (p : PhysicalPrefix Q) : Type :=
  {i : p.Label // (p.ideal i).active = true}

/-- Labels of platforms set aside at earlier layers. -/
@[expose] public def Stopped (p : PhysicalPrefix Q) : Type :=
  {i : p.Label // (p.ideal i).active = false}

public instance (p : PhysicalPrefix Q) : Fintype p.Active := by
  unfold Active
  infer_instance

@[expose] public def activeRegion (p : PhysicalPrefix Q) : Set Plane :=
  ⋃ i : p.Active, p.platform i.1

@[expose] public def stoppedRegion (p : PhysicalPrefix Q) : Set Plane :=
  ⋃ i : p.Stopped, p.platform i.1

@[expose] public def transitionRegion (p : PhysicalPrefix Q) : Set Plane :=
  Q \ (p.activeRegion ∪ p.stoppedRegion)

/-- The normalized input associated to a physical prefix. -/
@[expose] public noncomputable def input (p : PhysicalPrefix Q) : Plane → ℝ :=
  (1 / 5 : ℝ) • p.secondPotential

public theorem activeRegion_nonempty (p : PhysicalPrefix Q) : p.activeRegion.Nonempty := by
  obtain ⟨i, hi⟩ := p.has_active
  obtain ⟨x, hx⟩ := p.platform_nonempty i
  exact ⟨x, mem_iUnion.mpr ⟨⟨i, hi⟩, hx⟩⟩

public theorem input_smooth (p : PhysicalPrefix Q) : ContDiff ℝ ∞ p.input :=
  contDiff_const.smul p.smooth_second

public theorem active_pairwiseDisjoint (p : PhysicalPrefix Q) :
    Set.PairwiseDisjoint ((Finset.univ : Finset p.Active) : Set p.Active) (fun i => p.platform i.1) := by
  intro i _ j _ h
  exact p.platform_disjoint (fun hij => h (Subtype.ext hij))

/-- The root consists of the original platform and the two zero potentials. -/
@[expose] public noncomputable def root (Q : Set Plane) (hOpen : IsOpen Q)
    (hNonempty : Q.Nonempty) : PhysicalPrefix Q where
  parameterIndices := []
  Label := Unit
  ideal := fun _ => IdealNode.root
  platform := fun _ => Q
  platform_open := fun _ => hOpen
  platform_nonempty := fun _ => hNonempty
  platform_subset := fun _ => Subset.rfl
  platform_disjoint := fun i j h => (h (Subsingleton.elim i j)).elim
  has_active := ⟨(), rfl⟩
  secondPotential := 0
  fourthPotential := 0
  smooth_second := contDiff_const
  smooth_fourth := contDiff_const
  support_second := by simp
  support_fourth := by simp

end PhysicalPrefix

/-- The direction and two signed amplitudes read from an ideal layer. -/
public structure PhysicalDirections where
  normal : IdealLayer → ℝ → Plane
  secondAmplitude : IdealLayer → IdealNode → ℝ
  fourthAmplitude : IdealLayer → ℝ

/-- A physical row stores the common M22 selection and every child platform,
including children that become stopped. The old stopped labels persist. -/
public structure PhysicalLayerRow {Q : Set Plane} (directions : PhysicalDirections) (s δ : ℝ)
    (layer : IdealLayer) (p : PhysicalPrefix Q) (next : ℕ → PhysicalPrefix Q) where
  exhaustion : ∀ i : p.Active, InteriorExhaustion (p.platform i.1)
  frequencyContract : LayerFrequencyContract (fun i : p.Active => p.platform i.1) exhaustion
    (fun _ => directions.normal layer s)
    (fun i => directions.secondAmplitude layer (p.ideal i.1))
    (fun _ => directions.fourthAmplitude layer) δ
  childLabel : ∀ k, p.Active × Bool ↪ (next k).Label
  stoppedLabel : ∀ k, p.Stopped ↪ (next k).Label
  covers_labels : ∀ k, Set.range (childLabel k) ∪ Set.range (stoppedLabel k) = Set.univ
  disjoint_labels : ∀ k, Disjoint (Set.range (childLabel k)) (Set.range (stoppedLabel k))
  child_platform : ∀ k (i : p.Active) sign, (next k).platform (childLabel k (i, sign)) =
    childPlatform (frequencyContract.inner k i) sign (frequencyContract.width k)
      (frequencyContract.frequency k) (directions.normal layer s)
  child_ideal : ∀ k (i : p.Active) sign, (next k).ideal (childLabel k (i, sign)) =
    (p.ideal i.1).child layer s sign
  stopped_platform : ∀ k (i : p.Stopped), (next k).platform (stoppedLabel k i) = p.platform i.1
  stopped_ideal : ∀ k (i : p.Stopped), (next k).ideal (stoppedLabel k i) = p.ideal i.1
  extends_prefix : ∀ k, (next k).parameterIndices = p.parameterIndices ++ [k]
  extends_second : ∀ k, (next k).secondPotential =
    addLayer Finset.univ p.secondPotential (fun i : p.Active =>
      oscillatoryPotential 2 (frequencyContract.cutoff k i) (frequencyContract.width k)
        (directions.secondAmplitude layer (p.ideal i.1)) (frequencyContract.frequency k)
        (innerSL ℝ (directions.normal layer s)))
  extends_fourth : ∀ k, (next k).fourthPotential =
    addLayer Finset.univ p.fourthPotential (fun i : p.Active =>
      oscillatoryPotential 4 (frequencyContract.cutoff k i) (frequencyContract.width k)
        (directions.fourthAmplitude layer) (frequencyContract.frequency k)
        (innerSL ℝ (directions.normal layer s)))


namespace PhysicalLayerRow

variable {Q : Set Plane} {directions : PhysicalDirections} {s δ : ℝ}
    {layer : IdealLayer} {p : PhysicalPrefix Q} {next : ℕ → PhysicalPrefix Q}

public theorem second_c1_difference (row : PhysicalLayerRow directions s δ layer p next)
    (hBound : ∀ i : p.Active, Bornology.IsBounded (p.platform i.1)) (k : ℕ) (x : Plane) :
    ‖(next k).secondPotential x - p.secondPotential x‖ ≤ 1 / ((k : ℝ) + 1) ∧
      ‖fderiv ℝ (next k).secondPotential x - fderiv ℝ p.secondPotential x‖ ≤ 1 / ((k : ℝ) + 1) := by
  let C := row.frequencyContract
  let G (i : p.Active) := oscillatoryPotential 2 (C.cutoff k i) (C.width k)
    (directions.secondAmplitude layer (p.ideal i.1)) (C.frequency k)
    (innerSL ℝ (directions.normal layer s))
  have hCutoff (i : p.Active) :=
    quantitativeCutoff_spec (hBound i) (row.exhaustion i) (k + C.shift)
  have hSupp (i : p.Active) : tsupport (G i) ⊆ p.platform i.1 :=
    (tsupport_oscillatoryPotential_subset _ _ _ _ _ _).trans (hCutoff i).2.2.2.1
  have hSmooth (i : p.Active) : ContDiff ℝ ∞ (G i) :=
    contDiff_oscillatoryPotential 2 (hCutoff i).1 _ _ _ _
  have hEst :=
    addLayer_c1_difference_le Finset.univ (G := G) p.active_pairwiseDisjoint
      (fun i _ => p.platform_open i.1) (fun i _ => hSupp i) p.smooth_second (fun i _ => hSmooth i)
      (show 0 ≤ 1 / ((k : ℝ) + 1) by positivity)
      (fun i _ y _ => by simpa only [G, Real.norm_eq_abs, LayerFrequencyContract.cutoff, LayerFrequencyContract.width] using C.value_two k i y)
      (fun i _ y _ => C.derivative_two k i y) x
  rw [row.extends_second k]
  exact hEst

public theorem input_c1_difference (row : PhysicalLayerRow directions s δ layer p next)
    (hBound : ∀ i : p.Active, Bornology.IsBounded (p.platform i.1)) (k : ℕ) (x : Plane) :
    ‖(next k).input x - p.input x‖ ≤ (1 / 5) * (1 / ((k : ℝ) + 1)) ∧
      ‖fderiv ℝ (next k).input x - fderiv ℝ p.input x‖ ≤ (1 / 5) * (1 / ((k : ℝ) + 1)) := by
  have h := row.second_c1_difference hBound k x
  have hD (q : PhysicalPrefix Q) : fderiv ℝ q.input x = (1 / 5 : ℝ) • fderiv ℝ q.secondPotential x :=
    fderiv_const_smul ((q.smooth_second.differentiable (by simp)) x) _
  have hValue : (next k).input x - p.input x =
      (1 / 5 : ℝ) • ((next k).secondPotential x - p.secondPotential x) := by
    simp only [PhysicalPrefix.input, Pi.smul_apply, smul_sub]
  have hScale : ‖(1 / 5 : ℝ)‖ = 1 / 5 :=
    Real.norm_of_nonneg (by norm_num)
  constructor
  · rw [hValue, norm_smul, hScale]
    exact mul_le_mul_of_nonneg_left h.1 (by norm_num)
  · rw [hD, hD, ← smul_sub, norm_smul, hScale]
    exact mul_le_mul_of_nonneg_left h.2 (by norm_num)

/-- The actual children at a fixed prefix converge to its normalized input
uniformly on the plane, in both values and first derivatives. -/
public theorem input_c1_tendsto (row : PhysicalLayerRow directions s δ layer p next)
    (hBound : ∀ i : p.Active, Bornology.IsBounded (p.platform i.1)) :
    TendstoUniformly (fun k => (next k).input) p.input atTop ∧
      TendstoUniformly (fun k => fderiv ℝ (next k).input) (fderiv ℝ p.input) atTop := by
  have hRate : Tendsto (fun k : ℕ => (1 / 5 : ℝ) * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    have h : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [mul_zero] using h.const_mul (1 / 5 : ℝ)
  constructor
  · apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    have ht : ∀ᶠ k : ℕ in atTop, (1 / 5 : ℝ) * (1 / ((k : ℝ) + 1)) < ε :=
      hRate (eventually_lt_nhds hε)
    exact ht.mono fun k hk x => by
      rw [dist_comm, dist_eq_norm]
      exact (row.input_c1_difference hBound k x).1.trans_lt hk
  · apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    have ht : ∀ᶠ k : ℕ in atTop, (1 / 5 : ℝ) * (1 / ((k : ℝ) + 1)) < ε :=
      hRate (eventually_lt_nhds hε)
    exact ht.mono fun k hk x => by
      rw [dist_comm, dist_eq_norm]
      exact (row.input_c1_difference hBound k x).2.trans_lt hk

end PhysicalLayerRow

/-- A schedule-indexed tree that stores one simultaneous physical row
contract at each branching prefix. -/
public inductive PhysicalParameterTree {Q : Set Plane} (directions : PhysicalDirections)
    (s δ : ℝ) (Valid : List IdealLayer → PhysicalPrefix Q → Prop) :
    List IdealLayer → PhysicalPrefix Q → Type 1
  | terminal (p : PhysicalPrefix Q) (hp : Valid [] p) :
      PhysicalParameterTree directions s δ Valid [] p
  | branch {layer : IdealLayer} {tail : List IdealLayer} (p : PhysicalPrefix Q)
      (hp : Valid (layer :: tail) p) (next : ℕ → PhysicalPrefix Q)
      (row : PhysicalLayerRow directions s δ layer p next)
      (subtree : ∀ k, PhysicalParameterTree directions s δ Valid tail (next k)) :
      PhysicalParameterTree directions s δ Valid (layer :: tail) p

namespace PhysicalParameterTree

variable {Q : Set Plane} {directions : PhysicalDirections} {s δ : ℝ}
    {Valid : List IdealLayer → PhysicalPrefix Q → Prop}

public theorem exists_of_layer_rows
    (hStep : ∀ layer tail p, Valid (layer :: tail) p →
      ∃ next : ℕ → PhysicalPrefix Q, Nonempty (PhysicalLayerRow directions s δ layer p next) ∧
        ∀ k, Valid tail (next k))
    (layers : List IdealLayer) (p : PhysicalPrefix Q) (hp : Valid layers p) :
    Nonempty (PhysicalParameterTree directions s δ Valid layers p) := by
  classical
  induction layers generalizing p with
  | nil => exact ⟨.terminal p hp⟩
  | cons layer tail ih =>
    obtain ⟨next, ⟨row⟩, hNext⟩ := hStep layer tail p hp
    exact ⟨.branch p hp next row (fun k => Classical.choice (ih (next k) (hNext k)))⟩

/-- The same parameter tree with the row contracts forgotten. -/
@[expose] public def toParameterTree : {layers : List IdealLayer} → {p : PhysicalPrefix Q} →
    PhysicalParameterTree directions s δ Valid layers p → ParameterTree (PhysicalPrefix Q) layers.length
  | _, _, .terminal p _ => .leaf p
  | _, _, .branch p _ _ _ subtrees => .node p (fun k => toParameterTree (subtrees k))

public theorem root_payload {layers : List IdealLayer} {p : PhysicalPrefix Q}
    (T : PhysicalParameterTree directions s δ Valid layers p) :
    T.toParameterTree.payload = p := by
  cases T <;> rfl

@[expose] public def pathIndices : {d : ℕ} → ParameterTree.Path d → List ℕ
  | _, .nil => []
  | _, .cons k rest => k :: pathIndices rest

public theorem leaf_prefix {layers : List IdealLayer} {p : PhysicalPrefix Q}
    (T : PhysicalParameterTree directions s δ Valid layers p) (path : ParameterTree.Path layers.length) :
    (T.toParameterTree.leafAt path).parameterIndices = p.parameterIndices ++ pathIndices path := by
  induction T with
  | terminal p hp =>
    cases path
    exact (List.append_nil p.parameterIndices).symm
  | branch p hp next row subtrees ih =>
    cases path with
    | cons k rest =>
      change (((subtrees k).toParameterTree.leafAt rest).parameterIndices) = p.parameterIndices ++ k :: pathIndices rest
      rw [ih k rest, row.extends_prefix k, List.append_assoc]
      rfl

public theorem leaf_valid {layers : List IdealLayer} {p : PhysicalPrefix Q}
    (T : PhysicalParameterTree directions s δ Valid layers p) (path : ParameterTree.Path layers.length) :
    Valid [] (T.toParameterTree.leafAt path) := by
  induction T with
  | terminal p hp =>
    cases path
    exact hp
  | branch p hp next row subtrees ih =>
    cases path with
    | cons k rest => exact ih k rest

@[expose] public def zeroPath : (d : ℕ) → ParameterTree.Path d
  | 0 => .nil
  | n + 1 => .cons 0 (zeroPath n)

/-- The terminal input and its fourth-order potential are read from one path. -/
@[expose] public noncomputable def leafPotentials {layers : List IdealLayer} {p : PhysicalPrefix Q}
    (T : PhysicalParameterTree directions s δ Valid layers p) (path : ParameterTree.Path layers.length) :
    (Plane → ℝ) × (Plane → ℝ) :=
  let leaf := T.toParameterTree.leafAt path
  (leaf.input, leaf.fourthPotential)

@[expose] public noncomputable def terminalInputs {layers : List IdealLayer} {p : PhysicalPrefix Q}
    (T : PhysicalParameterTree directions s δ Valid layers p) : Set (Plane → ℝ) :=
  Set.range fun path => (T.leafPotentials path).1

public theorem terminalInputs_nonempty {layers : List IdealLayer} {p : PhysicalPrefix Q}
    (T : PhysicalParameterTree directions s δ Valid layers p) : T.terminalInputs.Nonempty :=
  ⟨(T.leafPotentials (zeroPath layers.length)).1, Set.mem_range_self _⟩

end PhysicalParameterTree

end C2Riemannian
