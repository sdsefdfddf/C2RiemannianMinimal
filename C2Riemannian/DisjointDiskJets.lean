module

public import C2Riemannian.C2DiskBanach
public import Mathlib.Topology.MetricSpace.Cauchy

set_option autoImplicit false

open Set Filter
open scoped Topology BigOperators BoundedContinuousFunction

namespace C2Riemannian.C2ClosedDisk

variable {a : Plane} {R : ℝ}

/-- Evaluation of the three fields at one point of the closed disk. -/
@[expose] public def pointJet (x : Metric.closedBall a R) :
    C2ClosedDisk a R →ₗ[ℝ] ℝ × Plane × DiskHessian where
  toFun u := (u.1.1 x, u.1.2.1 x, u.1.2.2 x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

public theorem pointJet_continuous (x : Metric.closedBall a R) :
    Continuous (pointJet x : C2ClosedDisk a R → ℝ × Plane × DiskHessian) := by
  change Continuous (fun u : C2ClosedDisk a R => (u.1.1 x, u.1.2.1 x, u.1.2.2 x))
  have h₁ : Continuous (fun u : C2ClosedDisk a R => u.1.1 x) :=
    (continuous_eval_const x).comp (continuous_fst.comp continuous_subtype_val)
  have h₂ : Continuous (fun u : C2ClosedDisk a R => u.1.2.1 x) :=
    (continuous_eval_const x).comp (continuous_fst.comp (continuous_snd.comp continuous_subtype_val))
  have h₃ : Continuous (fun u : C2ClosedDisk a R => u.1.2.2 x) :=
    (continuous_eval_const x).comp (continuous_snd.comp (continuous_snd.comp continuous_subtype_val))
  exact h₁.prodMk (h₂.prodMk h₃)

public theorem norm_pointJet_le (u : C2ClosedDisk a R) (x : Metric.closedBall a R) :
    ‖pointJet x u‖ ≤ ‖u‖ := by
  rw [u.norm_eq]
  change max ‖u.1.1 x‖ (max ‖u.1.2.1 x‖ ‖u.1.2.2 x‖) ≤ _
  exact max_le_max (BoundedContinuousFunction.norm_coe_le_norm _ _)
    (max_le_max (BoundedContinuousFunction.norm_coe_le_norm _ _)
      (BoundedContinuousFunction.norm_coe_le_norm _ _))

public theorem norm_le_of_pointJet_le {u : C2ClosedDisk a R} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, ‖pointJet x u‖ ≤ C) : ‖u‖ ≤ C := by
  rw [u.norm_eq]
  refine max_le ?_ (max_le ?_ ?_)
  · apply (BoundedContinuousFunction.norm_le hC).mpr
    intro x
    exact (le_max_left ‖u.1.1 x‖ (max ‖u.1.2.1 x‖ ‖u.1.2.2 x‖)).trans (h x)
  · apply (BoundedContinuousFunction.norm_le hC).mpr
    intro x
    exact (le_max_left ‖u.1.2.1 x‖ ‖u.1.2.2 x‖).trans ((le_max_right _ _).trans (h x))
  · apply (BoundedContinuousFunction.norm_le hC).mpr
    intro x
    exact (le_max_right ‖u.1.2.1 x‖ ‖u.1.2.2 x‖).trans ((le_max_right _ _).trans (h x))

section Disjoint

variable (S : ℕ → Set Plane) (u : ℕ → C2ClosedDisk a R)
    (hS : Pairwise fun i j => Disjoint (S i) (S j))
    (hZero : ∀ n (x : Metric.closedBall a R), (x : Plane) ∉ S n → pointJet x (u n) = 0)

include hS hZero in
private theorem pointJet_sum_eq_of_mem {I : Finset ℕ} {i : ℕ} (hi : i ∈ I)
    {x : Metric.closedBall a R} (hx : (x : Plane) ∈ S i) :
    pointJet x (∑ j ∈ I, u j) = pointJet x (u i) := by
  rw [map_sum]
  refine Finset.sum_eq_single i ?_ (fun h => (h hi).elim)
  intro j _ hji
  apply hZero
  exact fun hj => Set.disjoint_left.mp (hS hji) hj hx

include hZero in
private theorem pointJet_sum_eq_zero {I : Finset ℕ} {x : Metric.closedBall a R}
    (hx : ∀ i ∈ I, (x : Plane) ∉ S i) : pointJet x (∑ j ∈ I, u j) = 0 := by
  rw [map_sum]
  exact Finset.sum_eq_zero fun j hj => hZero j x (hx j hj)

include hS hZero in
/-- The maximum of the participating bounds controls a finite sum whose jet
supports are pairwise disjoint. -/
public theorem norm_finset_sum_le_of_disjoint_support (I : Finset ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hBound : ∀ i ∈ I, ‖u i‖ ≤ C) : ‖∑ i ∈ I, u i‖ ≤ C := by
  classical
  apply norm_le_of_pointJet_le hC
  intro x
  by_cases hx : ∃ i ∈ I, (x : Plane) ∈ S i
  · obtain ⟨i, hi, hxi⟩ := hx
    rw [pointJet_sum_eq_of_mem S u hS hZero hi hxi]
    exact (norm_pointJet_le _ _).trans (hBound i hi)
  · rw [pointJet_sum_eq_zero S u hZero (fun i hi hxi => hx ⟨i, hi, hxi⟩), norm_zero]
    exact hC

include hS hZero in
/-- A pointwise disjoint sequence of small disk jets converges in the full C²
norm, even when the individual norm bounds are not summable. -/
public theorem exists_tendsto_disjoint_jet_sums (A : ℕ → ℝ)
    (hA : Tendsto A atTop (𝓝 0)) (hBound : ∀ n, ‖u n‖ ≤ A n) :
    ∃ v : C2ClosedDisk a R, Tendsto (fun N => ∑ n ∈ Finset.range N, u n) atTop (𝓝 v) := by
  apply cauchySeq_tendsto_of_complete
  refine Metric.cauchySeq_iff'.mpr fun ε hε => ?_
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hA (gt_mem_nhds (half_pos hε)))
  refine ⟨N, ?_⟩
  intro n hn
  let I := SDiff.sdiff (Finset.range n) (Finset.range N)
  have hsub : Finset.range N ⊆ Finset.range n := Finset.range_mono hn
  have heq : (∑ i ∈ Finset.range n, u i) - (∑ i ∈ Finset.range N, u i) = ∑ i ∈ I, u i := by
    rw [← Finset.sum_sdiff hsub]
    apply Subtype.ext
    let X : C2DiskFields a R := (∑ i ∈ I, u i : C2ClosedDisk a R).1
    let Y : C2DiskFields a R := (∑ i ∈ Finset.range N, u i : C2ClosedDisk a R).1
    change X + Y - Y = X
    exact add_sub_cancel_right X Y
  have hDiff : ‖∑ i ∈ I, u i‖ ≤ ε / 2 := by
    apply norm_finset_sum_le_of_disjoint_support S u hS hZero I (half_pos hε).le
    intro j hj
    have hjN : N ≤ j :=
      Nat.le_of_not_gt (fun h => (Finset.mem_sdiff.mp hj).2 (Finset.mem_range.mpr h))
    exact (hBound j).trans (hN j hjN).le
  change dist ((∑ i ∈ Finset.range n, u i : C2ClosedDisk a R).1 : C2DiskFields a R)
    (∑ i ∈ Finset.range N, u i : C2ClosedDisk a R).1 < ε
  rw [dist_eq_norm]
  change ‖(∑ i ∈ Finset.range n, u i) - (∑ i ∈ Finset.range N, u i)‖ < ε
  rw [heq]
  exact hDiff.trans_lt (half_lt_self hε)

include hS hZero in
/-- At a point in a specified support, the limit has exactly that term's jet;
at a point outside all supports, it has the zero jet. -/
public theorem disjoint_jet_sum_limit_fields {v : C2ClosedDisk a R}
    (hV : Tendsto (fun N => ∑ n ∈ Finset.range N, u n) atTop (𝓝 v)) :
    (∀ i (x : Metric.closedBall a R), (x : Plane) ∈ S i → pointJet x v = pointJet x (u i)) ∧
      (∀ (x : Metric.closedBall a R), (∀ i, (x : Plane) ∉ S i) → pointJet x v = 0) := by
  constructor
  · intro i x hx
    have hT := ((pointJet_continuous x).tendsto v).comp hV
    refine tendsto_nhds_unique_of_eventuallyEq hT tendsto_const_nhds ?_
    filter_upwards [eventually_ge_atTop (i + 1)] with n hn
    exact pointJet_sum_eq_of_mem S u hS hZero (Finset.mem_range.mpr (Nat.lt_of_succ_le hn)) hx
  · intro x hx
    have hT := ((pointJet_continuous x).tendsto v).comp hV
    refine tendsto_nhds_unique_of_eventuallyEq hT tendsto_const_nhds ?_
    exact Eventually.of_forall fun n => pointJet_sum_eq_zero S u hZero (fun i _ => hx i)

end Disjoint
end C2Riemannian.C2ClosedDisk
