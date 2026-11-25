module

public import C2Riemannian.HessianAlgebra
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Order.Filter.Finite

set_option autoImplicit false

open Filter Set
open scoped Topology BigOperators

namespace C2Riemannian

/-- Add one finite layer of corrections, each attached to one active parent. -/
@[expose] public noncomputable def addLayer {ι : Type*} (I : Finset ι) (f : Plane → ℝ)
    (g : ι → Plane → ℝ) (x : Plane) : ℝ := f x + ∑ i ∈ I, g i x

/-- At a parent, all corrections from other parents vanish. -/
public theorem addLayer_eqOn_parent {ι : Type*} {I : Finset ι}
    {P : ι → Set Plane} {f : Plane → ℝ} {g : ι → Plane → ℝ}
    (hDisjoint : Set.PairwiseDisjoint (I : Set ι) P)
    (hSupport : ∀ i ∈ I, tsupport (g i) ⊆ P i) {i : ι} (hi : i ∈ I) :
    EqOn (addLayer I f g) (fun x => f x + g i x) (P i) := by
  classical
  intro x hx
  unfold addLayer
  congr 1
  apply Finset.sum_eq_single_of_mem i hi
  intro j hj hji
  apply image_eq_zero_of_notMem_tsupport
  intro ht
  exact Set.disjoint_left.mp (hDisjoint hj hi hji) (hSupport j hj ht) hx

/-- Inside an open parent all derivatives of the layer addition are those
of its single correction plus the previous potential. -/
public theorem iteratedFDeriv_addLayer_parent {ι : Type*} {I : Finset ι}
    {P : ι → Set Plane} {f : Plane → ℝ} {g : ι → Plane → ℝ}
    (hDisjoint : Set.PairwiseDisjoint (I : Set ι) P)
    (hSupport : ∀ i ∈ I, tsupport (g i) ⊆ P i) {i : ι} (hi : i ∈ I)
    (hOpen : IsOpen (P i)) {x : Plane} (hx : x ∈ P i) (n : ℕ) :
    iteratedFDeriv ℝ n (addLayer I f g) x =
      iteratedFDeriv ℝ n (fun y => f y + g i y) x := by
  have h : addLayer I f g =ᶠ[𝓝 x] (fun y => f y + g i y) :=
    eventually_of_mem (hOpen.mem_nhds hx) (addLayer_eqOn_parent hDisjoint hSupport hi)
  exact (h.iteratedFDeriv ℝ n).eq_of_nhds

/-- A point outside all correction supports has a neighborhood on which this
layer leaves the potential unchanged. -/
public theorem addLayer_eventuallyEq_of_outside_supports {ι : Type*} (I : Finset ι)
    (f : Plane → ℝ) (g : ι → Plane → ℝ) {x : Plane}
    (hx : ∀ i ∈ I, x ∉ tsupport (g i)) :
    addLayer I f g =ᶠ[𝓝 x] f := by
  have hEventually : ∀ᶠ y in 𝓝 x, ∀ i ∈ I, y ∉ tsupport (g i) :=
    (eventually_all_finset I).2 fun i hi =>
      (isClosed_tsupport (g i)).isOpen_compl.mem_nhds (hx i hi)
  filter_upwards [hEventually] with y hy
  have hZero : (∑ i ∈ I, g i y) = 0 :=
    Finset.sum_eq_zero fun i hi => image_eq_zero_of_notMem_tsupport (hy i hi)
  simp only [addLayer, hZero, add_zero]

end C2Riemannian

