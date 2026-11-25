module

public import C2Riemannian.HessianAlgebra
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace C2Riemannian.TorusDiskGeometry

/-- The positive disk index is n+1. The first center has coordinate 1/8. -/
@[expose] public noncomputable def centerCoord (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 3)

@[expose] public noncomputable def center (n : ℕ) : Plane := EuclideanSpace.single 0 (centerCoord n)

@[expose] public noncomputable def radius (n : ℕ) : ℝ := centerCoord n / 8

@[expose] public noncomputable def disk (n : ℕ) : Set Plane := Metric.ball (center n) (radius n)

@[expose] public noncomputable def closedDisk (n : ℕ) : Set Plane := Metric.closedBall (center n) (radius n)

@[expose] public def fundamentalSquare : Set Plane :=
  {x | ∀ i : Fin 2, x i ∈ Ioo (-1 / 2 : ℝ) (1 / 2)}

public theorem centerCoord_pos (n : ℕ) : 0 < centerCoord n := by unfold centerCoord; positivity

public theorem radius_pos (n : ℕ) : 0 < radius n := div_pos (centerCoord_pos n) (by norm_num)

public theorem centerCoord_le (n : ℕ) : centerCoord n ≤ 1 / 8 := by
  change (1 / 2 : ℝ) ^ (n + 3) ≤ 1 / 8
  calc
    _ ≤ (1 / 2 : ℝ) ^ (3 : ℕ) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ = _ := by norm_num

public theorem radius_le (n : ℕ) : radius n ≤ 1 / 64 := by
  unfold radius
  linarith only [centerCoord_le n]

public theorem centerCoord_le_half_of_lt {i j : ℕ} (h : i < j) :
    centerCoord j ≤ centerCoord i / 2 := by
  calc
    _ ≤ (1 / 2 : ℝ) ^ (i + 3 + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ = _ := by rw [centerCoord, pow_succ]; ring

public theorem norm_center (n : ℕ) : ‖center n‖ = centerCoord n := by
  simp [center, Real.norm_eq_abs, abs_of_nonneg (centerCoord_pos n).le]

private theorem dist_centers_of_lt {i j : ℕ} (h : i < j) :
    dist (center i) (center j) = centerCoord i - centerCoord j := by
  unfold center
  rw [PiLp.dist_single_same]
  have h' := centerCoord_le_half_of_lt h
  rw [Real.dist_eq, abs_of_nonneg]
  linarith only [h', centerCoord_pos i]

private theorem disjoint_closed_disks_of_lt {i j : ℕ} (h : i < j) :
    Disjoint (closedDisk i) (closedDisk j) := by
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hI := Metric.mem_closedBall.mp hxi
  have hJ := Metric.mem_closedBall.mp hxj
  have hT := dist_triangle (center i) x (center j)
  rw [dist_centers_of_lt h, dist_comm (center i) x] at hT
  have hHalf := centerCoord_le_half_of_lt h
  change dist x (center i) ≤ centerCoord i / 8 at hI
  change dist x (center j) ≤ centerCoord j / 8 at hJ
  linarith only [hI, hJ, hT, hHalf, centerCoord_pos i]

/-- The closed disks of the chosen sequence are pairwise disjoint. -/
public theorem disjoint_closed_disks : Pairwise (fun i j => Disjoint (closedDisk i) (closedDisk j)) := by
  intro i j h
  rcases lt_or_gt_of_ne h with hij | hji
  · exact disjoint_closed_disks_of_lt hij
  · exact (disjoint_closed_disks_of_lt hji).symm

public theorem norm_bounds_of_mem_closedDisk {n : ℕ} {x : Plane} (hx : x ∈ closedDisk n) :
    7 * radius n ≤ ‖x‖ ∧ ‖x‖ ≤ 9 * radius n := by
  have h := Metric.mem_closedBall.mp hx
  have hU := dist_triangle x (center n) (0 : Plane)
  have hL := dist_triangle (center n) x (0 : Plane)
  simp only [dist_zero_right, norm_center] at hU hL
  rw [dist_comm (center n) x] at hL
  unfold radius at *
  constructor <;> linarith only [h, hU, hL]

public theorem zero_notMem_closedDisk (n : ℕ) : (0 : Plane) ∉ closedDisk n := by
  intro hz
  have h := (norm_bounds_of_mem_closedDisk hz).1
  rw [norm_zero] at h
  linarith only [h, radius_pos n]

/-- All the closed disks lie in the concentric closed disk of radius 9/64. -/
public theorem closedDisk_subset_smallBall (n : ℕ) :
    closedDisk n ⊆ Metric.closedBall (0 : Plane) (9 / 64) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (norm_bounds_of_mem_closedDisk hx).2.trans (by linarith only [radius_le n])

public theorem disks_in_fundamental_domain (n : ℕ) : closedDisk n ⊆ fundamentalSquare := by
  intro x hx i
  have h := Metric.mem_closedBall.mp (closedDisk_subset_smallBall n hx)
  rw [dist_zero_right] at h
  have hi := (PiLp.norm_apply_le x i).trans h
  rw [Real.norm_eq_abs] at hi
  obtain ⟨hL, hU⟩ := abs_le.mp hi
  exact ⟨by linarith only [hL], by linarith only [hU]⟩

public theorem radius_tendsto : Tendsto radius atTop (𝓝 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  have hs : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 3)) atTop (𝓝 0) :=
    h.comp (tendsto_add_atTop_nat 3)
  change Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 3) / 8) atTop (𝓝 0)
  simpa only [zero_div] using hs.div_const 8

/-- Every neighborhood of zero contains all sufficiently late closed disks. -/
public theorem eventually_closedDisk_subset_ball {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, closedDisk n ⊆ Metric.ball (0 : Plane) ε := by
  have ht : Tendsto (fun n => 9 * radius n) atTop (𝓝 0) := by
    simpa only [mul_zero] using radius_tendsto.const_mul (9 : ℝ)
  filter_upwards [ht (gt_mem_nhds hε)] with n hn x hx
  rw [Metric.mem_ball, dist_zero_right]
  exact (norm_bounds_of_mem_closedDisk hx).2.trans_lt hn

/-- A closed set away from zero meets only finitely many closed disks. -/
public theorem disks_only_accumulate_at_origin {K : Set Plane} (hK : IsClosed K)
    (h0 : (0 : Plane) ∉ K) : {n | (closedDisk n ∩ K).Nonempty}.Finite := by
  obtain ⟨ε, hε, hBall⟩ := Metric.mem_nhds_iff.mp (hK.isOpen_compl.mem_nhds h0)
  obtain ⟨N, hTail⟩ := eventually_atTop.mp (eventually_closedDisk_subset_ball hε)
  refine (Set.finite_lt_nat N).subset ?_
  intro n hn
  by_contra! hn'
  obtain ⟨x, hx, hxK⟩ := hn
  exact hBall (hTail n (Nat.le_of_not_gt hn') hx) hxK

end C2Riemannian.TorusDiskGeometry
