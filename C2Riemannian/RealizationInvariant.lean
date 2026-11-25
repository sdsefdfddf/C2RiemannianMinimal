module

public import C2Riemannian.ExactChildren
public import C2Riemannian.LayerGluing
public import C2Riemannian.OscillatoryRemainder
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Layerwise tensor bounds and first-exit preservation (M24) -/

set_option autoImplicit false

open Filter Set
open scoped BigOperators ContDiff Topology

namespace C2Riemannian

/-- The rank-one tensor taking the product of one scalar directional readout in every slot. -/
@[expose] public noncomputable def directionalTensor (j : ℕ) (d : Plane →L[ℝ] ℝ) :
    Plane [×j]→L[ℝ] ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℝ j ℝ).compContinuousLinearMap (fun _ => d)

@[simp] public theorem directionalTensor_apply (j : ℕ) (d : Plane →L[ℝ] ℝ)
    (v : Fin j → Plane) : directionalTensor j d v = ∏ i, d (v i) := by
  simp only [directionalTensor, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.prod_ofFn]

public theorem tensorHS_add_le {j : ℕ} (A B : Plane [×j]→L[ℝ] ℝ) :
    tensorHS (A + B) ≤ tensorHS A + tensorHS B := by
  simp only [tensorHS, map_add]
  exact norm_add_le _ _

public theorem tensorHS_smul_eq {j : ℕ} (s : ℝ) (A : Plane [×j]→L[ℝ] ℝ) :
    tensorHS (s • A) = |s| * tensorHS A := by
  simp only [tensorHS, map_smul, norm_smul, Real.norm_eq_abs]

/-- Between the two ideal child states, only the current remainder contributes
to the excess over their common bound. -/
public theorem tensorHS_interpolate_add_remainder {j : ℕ}
    (A D R : Plane [×j]→L[ℝ] ℝ) (w B η : ℝ) (hw : |w| ≤ 1)
    (hPlus : tensorHS (A + D) ≤ B) (hMinus : tensorHS (A - D) ≤ B)
    (hR : tensorHS R ≤ η) :
    tensorHS (A + w • D + R) ≤ B + η := by
  let a : ℝ := (1 + w) / 2
  have hw' := abs_le.mp hw
  have ha₀ : 0 ≤ a := by dsimp [a]; linarith only [hw'.1]
  have ha₁ : 0 ≤ 1 - a := by dsimp [a]; linarith only [hw'.2]
  have hEq : A + w • D = a • (A + D) + (1 - a) • (A - D) := by
    ext v
    simp only [add_apply, sub_apply,
      smul_apply, smul_eq_mul, a]
    ring
  calc
    _ ≤ tensorHS (A + w • D) + tensorHS R := tensorHS_add_le _ _
    _ ≤ B + η := by
      apply add_le_add _ hR
      rw [hEq]
      calc
        _ ≤ tensorHS (a • (A + D)) + tensorHS ((1 - a) • (A - D)) := tensorHS_add_le _ _
        _ = a * tensorHS (A + D) + (1 - a) * tensorHS (A - D) := by
          rw [tensorHS_smul_eq, tensorHS_smul_eq, abs_of_nonneg ha₀, abs_of_nonneg ha₁]
        _ ≤ a * B + (1 - a) * B :=
          add_le_add (mul_le_mul_of_nonneg_left hPlus ha₀) (mul_le_mul_of_nonneg_left hMinus ha₁)
        _ = B := by ring

/-- A finite layer of smooth corrections is smooth and remains supported in
the common domain of the old potential and all corrections. -/
public theorem addLayer_smooth_supported {ι : Type*} (I : Finset ι)
    {Q : Set Plane} (hQ : Bornology.IsBounded Q) {W : Plane → ℝ} {G : ι → Plane → ℝ}
    (hW : ContDiff ℝ ∞ W) (hWS : tsupport W ⊆ Q)
    (hG : ∀ i ∈ I, ContDiff ℝ ∞ (G i)) (hGS : ∀ i ∈ I, tsupport (G i) ⊆ Q) :
    ContDiff ℝ ∞ (addLayer I W G) ∧ HasCompactSupport (addLayer I W G) ∧
      tsupport (addLayer I W G) ⊆ Q := by
  have hSupp : tsupport (addLayer I W G) ⊆ Q := by
    intro x hx
    by_contra hnx
    have hg := addLayer_eventuallyEq_of_outside_supports I W G
      (fun i hi hxi => hnx (hGS i hi hxi))
    have hf : W =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp
      (fun hxi => hnx (hWS hxi))
    exact (notMem_tsupport_iff_eventuallyEq.mpr (hg.trans hf)) hx
  have hSmooth : ContDiff ℝ ∞ (addLayer I W G) := hW.add (ContDiff.sum hG)
  exact ⟨hSmooth, Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport _) (hQ.subset hSupp), hSupp⟩

/-- The parent ideal bounds and this layer's remainder bound control the
new tensor at all points of the parent, including its transition region. -/
public theorem tensorHS_add_oscillatoryPotential_bound (j : ℕ)
    {W χ : Plane → ℝ} (hW : ContDiff ℝ ∞ W) (hχ : ContDiff ℝ ∞ χ)
    (e γ L B η : ℝ) (hL : L ≠ 0) (d : Plane →L[ℝ] ℝ)
    (x : Plane) (hχx : |χ x| ≤ 1) (A : Plane [×j]→L[ℝ] ℝ)
    (hIdeal : iteratedFDeriv ℝ j W x = A)
    (hPlus : tensorHS (A + γ • directionalTensor j d) ≤ B)
    (hMinus : tensorHS (A - γ • directionalTensor j d) ≤ B)
    (hR : tensorHS (oscillatoryRemainder j χ e γ L d x) ≤ η) :
    tensorHS (iteratedFDeriv ℝ j (W + oscillatoryPotential j χ e γ L d) x) ≤ B + η := by
  let w := χ x * smooth_square_wave e ((L • d) x)
  have hw : |w| ≤ 1 := by
    rw [show w = χ x * smooth_square_wave e ((L • d) x) from rfl, abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) hχx).trans (abs_smooth_square_wave_le_one _ _)
  have hOsc := contDiff_oscillatoryPotential j hχ e γ L d
  have hEq : iteratedFDeriv ℝ j (oscillatoryPotential j χ e γ L d) x =
      w • (γ • directionalTensor j d) + oscillatoryRemainder j χ e γ L d x := by
    ext v
    rw [iteratedFDeriv_oscillatoryPotential_eq_main_add_remainder j χ e γ L hL d]
    simp only [add_apply, smul_apply, smul_eq_mul, directionalTensor_apply, w]
    ring
  rw [iteratedFDeriv_add_apply (hW.contDiffAt.of_le (by simp)) (hOsc.contDiffAt.of_le (by simp)),
    hIdeal, hEq, ← add_assoc]
  exact tensorHS_interpolate_add_remainder A (γ • directionalTensor j d) _ w B η hw hPlus hMinus hR

/-- One actual layer obeys the previous global budget. Inside an active
parent its bound uses ideal children and only this layer's remainder,
and outside all active parents the full tensor is unchanged. -/
public theorem realize_layer_derivative_bound {ι : Type*} (I : Finset ι)
    {P : ι → Set Plane} (hDisjoint : Set.PairwiseDisjoint (I : Set ι) P)
    (hOpen : ∀ i ∈ I, IsOpen (P i))
    (j : ℕ) {W : Plane → ℝ} (hW : ContDiff ℝ ∞ W)
    (χ : ι → Plane → ℝ) (hχ : ∀ i ∈ I, ContDiff ℝ ∞ (χ i))
    (hχS : ∀ i ∈ I, tsupport (χ i) ⊆ P i)
    (e L B η : ℝ) (hL : L ≠ 0) (hη : η ≤ 1)
    (γ : ι → ℝ) (d : ι → Plane →L[ℝ] ℝ) (A : ι → Plane [×j]→L[ℝ] ℝ)
    (hOld : ∀ x, tensorHS (iteratedFDeriv ℝ j W x) ≤ B + 1)
    (hIdeal : ∀ i ∈ I, ∀ x ∈ P i, iteratedFDeriv ℝ j W x = A i)
    (hχBound : ∀ i ∈ I, ∀ x ∈ P i, |χ i x| ≤ 1)
    (hPlus : ∀ i ∈ I, tensorHS (A i + γ i • directionalTensor j (d i)) ≤ B)
    (hMinus : ∀ i ∈ I, tensorHS (A i - γ i • directionalTensor j (d i)) ≤ B)
    (hR : ∀ i ∈ I, ∀ x ∈ P i, tensorHS (oscillatoryRemainder j (χ i) e (γ i) L (d i) x) ≤ η) :
    ∀ x, tensorHS (iteratedFDeriv ℝ j
      (addLayer I W (fun i => oscillatoryPotential j (χ i) e (γ i) L (d i))) x) ≤ B + 1 := by
  let G (i : ι) := oscillatoryPotential j (χ i) e (γ i) L (d i)
  have hG i (hi : i ∈ I) : tsupport (G i) ⊆ P i :=
    (tsupport_oscillatoryPotential_subset j (χ i) e (γ i) L (d i)).trans (hχS i hi)
  intro x
  by_cases hx : ∃ i ∈ I, x ∈ P i
  · obtain ⟨i, hi, hxi⟩ := hx
    have hTensor := iteratedFDeriv_addLayer_parent (f := W) hDisjoint hG hi (hOpen i hi) hxi j
    rw [hTensor]
    exact (tensorHS_add_oscillatoryPotential_bound j hW (hχ i hi) e (γ i) L B η hL (d i)
      x (hχBound i hi x hxi) (A i) (hIdeal i hi x hxi) (hPlus i hi) (hMinus i hi)
      (hR i hi x hxi)).trans (add_le_add_right hη _)
  · have hFreeze := addLayer_eventuallyEq_of_outside_supports I W G
      (fun i hi hxi => hx ⟨i, hi, hG i hi hxi⟩)
    rw [(hFreeze.iteratedFDeriv ℝ j).eq_of_nhds]
    exact hOld x

/-- At an exact child, the full layer has the signed derivative update of
its own parent's correction. This applies at orders two and four. -/
public theorem realize_layer_preserves_jets {ι : Type*} (I : Finset ι)
    {P : ι → Set Plane} (hDisjoint : Set.PairwiseDisjoint (I : Set ι) P)
    (hOpen : ∀ i ∈ I, IsOpen (P i)) (hBound : ∀ i ∈ I, Bornology.IsBounded (P i))
    (E : ∀ i, InteriorExhaustion (P i)) (k j : ℕ) {e L : ℝ}
    (he : 0 < e) (he' : e ≤ 1 / 16) (hL : L ≠ 0)
    (γ : ι → ℝ) (n : ι → Plane) {W : Plane → ℝ} (hW : ContDiff ℝ ∞ W)
    {i : ι} (hi : i ∈ I) (positive : Bool)
    {x : Plane} (hx : x ∈ childPlatform (parentInterior (P i) (E i).radius k) positive e L (n i))
    (v : Fin j → Plane) :
    iteratedFDeriv ℝ j (addLayer I W fun q =>
      oscillatoryPotential j (quantitativeCutoff (P q) (E q).radius k)
        e (γ q) L (innerSL ℝ (n q))) x v =
    iteratedFDeriv ℝ j W x v + childSign positive * γ i * ∏ l, inner ℝ (n i) (v l) := by
  let G (q : ι) := oscillatoryPotential j (quantitativeCutoff (P q) (E q).radius k)
    e (γ q) L (innerSL ℝ (n q))
  have hG q (hq : q ∈ I) : tsupport (G q) ⊆ P q :=
    (tsupport_oscillatoryPotential_subset _ _ _ _ _ _).trans (quantitativeCutoff_spec (hBound q hq) (E q) k).2.2.2.1
  have hPi := (E i).inside k hx.1
  have hh := iteratedFDeriv_addLayer_parent (f := W) hDisjoint hG hi (hOpen i hi) hPi j
  rw [hh]
  exact exact_child_jets (hBound i hi) (E i) k j he he' hL (n i) (γ i) positive hW hx v

/-- Once a point is outside a nested active region, later layers preserve
all of its derivatives. The support condition is expressed as local equality. -/
public theorem iteratedFDeriv_frozen_after_exit (j : ℕ) (active : ℕ → Set Plane)
    (hNested : Antitone active) (W : ℕ → Plane → ℝ)
    (hLocal : ∀ k x, x ∉ active k → W (k + 1) =ᶠ[𝓝 x] W k)
    {q d : ℕ} (hqd : q ≤ d) {x : Plane} (hx : x ∉ active q) :
    iteratedFDeriv ℝ j (W d) x = iteratedFDeriv ℝ j (W q) x := by
  induction d, hqd using Nat.le_induction with
  | base => rfl
  | succ d hqd ih =>
    have hxd : x ∉ active d := fun h => hx (hNested hqd h)
    exact ((hLocal d x hxd).iteratedFDeriv ℝ j).eq_of_nhds.trans ih

/-- At a first exit, the single transition allowance at that layer controls
the tensor at every later depth. -/
public theorem tensorHS_first_exit_bound (j : ℕ) (active : ℕ → Set Plane)
    (hNested : Antitone active) (W : ℕ → Plane → ℝ)
    (hLocal : ∀ k x, x ∉ active k → W (k + 1) =ᶠ[𝓝 x] W k)
    (B : ℝ) (η : ℕ → ℝ)
    (hStep : ∀ k x, x ∈ active k → tensorHS (iteratedFDeriv ℝ j (W (k + 1)) x) ≤ B + η k)
    {d : ℕ} {x : Plane} (hRoot : x ∈ active 0) (hExit : x ∉ active d) :
    ∃ k < d, x ∈ active k ∧ x ∉ active (k + 1) ∧
      iteratedFDeriv ℝ j (W d) x = iteratedFDeriv ℝ j (W (k + 1)) x ∧
      tensorHS (iteratedFDeriv ℝ j (W d) x) ≤ B + η k := by
  have hFirst (q : ℕ) : x ∉ active q → ∃ k < q, x ∈ active k ∧ x ∉ active (k + 1) := by
    induction q with
    | zero => exact fun h => (h hRoot).elim
    | succ q ih =>
      intro h
      by_cases hq : x ∈ active q
      · exact ⟨q, Nat.lt_succ_self q, hq, h⟩
      · obtain ⟨k, hk, ha, hb⟩ := ih hq
        exact ⟨k, hk.trans (Nat.lt_succ_self q), ha, hb⟩
  obtain ⟨k, hk, hin, hout⟩ := hFirst d hExit
  have hFreeze := iteratedFDeriv_frozen_after_exit j active hNested W hLocal hk hout
  refine ⟨k, hk, hin, hout, hFreeze, ?_⟩
  rw [hFreeze]
  exact hStep k x hin

/-- A layer sequence with exact active tensors and at most one unit of error
at each transition has the bound `B + 1` at every depth. -/
public theorem tensorHS_all_prefixes_le (j : ℕ) (active : ℕ → Set Plane)
    (hNested : Antitone active) (W : ℕ → Plane → ℝ)
    (hLocal : ∀ k x, x ∉ active k → W (k + 1) =ᶠ[𝓝 x] W k)
    (B : ℝ) (η : ℕ → ℝ) (hη : ∀ k, η k ≤ 1)
    (hRoot : ∀ x, tensorHS (iteratedFDeriv ℝ j (W 0) x) ≤ B)
    (hActive : ∀ k x, x ∈ active k → tensorHS (iteratedFDeriv ℝ j (W k) x) ≤ B)
    (hStep : ∀ k x, x ∈ active k → tensorHS (iteratedFDeriv ℝ j (W (k + 1)) x) ≤ B + η k)
    (d : ℕ) (x : Plane) :
    tensorHS (iteratedFDeriv ℝ j (W d) x) ≤ B + 1 := by
  by_cases hxd : x ∈ active d
  · exact (hActive d x hxd).trans (le_add_of_nonneg_right zero_le_one)
  · by_cases hx₀ : x ∈ active 0
    · obtain ⟨k, _, _, _, _, hBound⟩ := tensorHS_first_exit_bound j active hNested W hLocal B η hStep hx₀ hxd
      exact hBound.trans (add_le_add_right (hη k) B)
    · rw [iteratedFDeriv_frozen_after_exit j active hNested W hLocal (Nat.zero_le d) hx₀]
      exact (hRoot x).trans (le_add_of_nonneg_right zero_le_one)

/-- The active region of a finite layer, independently of the support of the
individual correction inside each parent. -/
@[expose] public def activeRegion {ι : Type*} (I : Finset ι) (P : ι → Set Plane) : Set Plane :=
  {x | ∃ i ∈ I, x ∈ P i}

public theorem addLayer_eventuallyEq_outside_activeRegion {ι : Type*}
    (I : Finset ι) (P : ι → Set Plane) (W : Plane → ℝ) (G : ι → Plane → ℝ)
    (hG : ∀ i ∈ I, tsupport (G i) ⊆ P i) {x : Plane} (hx : x ∉ activeRegion I P) :
    addLayer I W G =ᶠ[𝓝 x] W :=
  addLayer_eventuallyEq_of_outside_supports I W G
    (fun i hi hxG => hx ⟨i, hi, hG i hi hxG⟩)

/-- Division by five converts the ideal second-order bound and one remainder
allowance to a strict unit tensor bound. -/
public theorem tensorHS_normalized_profile_lt_one {W : Plane → ℝ} (hW : ContDiff ℝ ∞ W)
    {x : Plane} (h : tensorHS (iteratedFDeriv ℝ 2 W x) ≤ √(11 / 2 : ℝ) + 1) :
    tensorHS (iteratedFDeriv ℝ 2 (fun y => W y / 5) x) < 1 := by
  have hfun : (fun y => W y / 5) = (1 / 5 : ℝ) • W := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hd : iteratedFDeriv ℝ 2 ((1 / 5 : ℝ) • W) x =
      (1 / 5 : ℝ) • iteratedFDeriv ℝ 2 W x :=
    iteratedFDeriv_const_smul_apply (hW.contDiffAt.of_le (by simp))
  rw [hfun, hd, tensorHS_smul_eq, abs_of_nonneg (by norm_num : 0 ≤ (1 / 5 : ℝ))]
  have hs : √(11 / 2 : ℝ) < 4 := by
    rw [← Real.sqrt_sq (show 0 ≤ (4 : ℝ) by norm_num)]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith only [h, hs]

end C2Riemannian
