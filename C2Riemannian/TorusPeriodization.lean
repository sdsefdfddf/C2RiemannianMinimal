module

public import C2Riemannian.TorusDiskGeometry
public import C2Riemannian.QuantitativeCutoff
public import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped ContDiff Topology

namespace C2Riemannian.TorusDiskGeometry

/-- Integer coordinates embedded in the Euclidean covering plane. -/
@[expose] public noncomputable def lattice (k : Fin 2 → ℤ) : Plane :=
  WithLp.toLp 2 fun i => (k i : ℝ)

public theorem lattice_zero : lattice 0 = 0 := by
  apply (WithLp.ext_iff 2).mpr
  funext i
  simp [lattice]

public theorem lattice_add (j k : Fin 2 → ℤ) : lattice (j + k) = lattice j + lattice k := by
  apply (WithLp.ext_iff 2).mpr
  funext i
  simp [lattice]

/-- Distinct integer translates of the origin are at least one unit apart. -/
public theorem lattice_separation {j k : Fin 2 → ℤ} (h : j ≠ k) :
    1 ≤ dist (lattice j) (lattice k) := by
  obtain ⟨i, hi⟩ : ∃ i, j i ≠ k i := by
    by_contra! h'
    exact h (funext h')
  have hC : ‖(lattice j - lattice k) i‖ ≤ ‖lattice j - lattice k‖ := PiLp.norm_apply_le _ _
  rw [dist_eq_norm]
  apply le_trans _ hC
  change 1 ≤ ‖(j i : ℝ) - (k i : ℝ)‖
  rw [Real.norm_eq_abs, ← Int.cast_sub, ← Int.cast_abs]
  have hp : 0 < |j i - k i| := abs_pos.mpr (sub_ne_zero.mpr hi)
  exact_mod_cast (show (1 : ℤ) ≤ |j i - k i| by omega)

private theorem unique_near_lattice {x : Plane} {j k : Fin 2 → ℤ}
    (hj : x - lattice j ∈ Metric.ball (0 : Plane) (1 / 4))
    (hk : x - lattice k ∈ Metric.ball (0 : Plane) (1 / 4)) : j = k := by
  by_contra h
  have hSep := lattice_separation h
  have hT := dist_triangle (lattice j) x (lattice k)
  rw [dist_comm (lattice j) x] at hT
  rw [Metric.mem_ball, dist_zero_right, ← dist_eq_norm] at hj hk
  linarith only [hT, hSep, hj, hk]

/-- Periodization with disjoint quarter-radius patches. The given profile is
zero before reaching any patch boundary. -/
@[expose] public noncomputable def periodize (f : Plane → ℝ) (x : Plane) : ℝ := by
  classical
  exact if h : ∃ k : Fin 2 → ℤ, x - lattice k ∈ Metric.ball (0 : Plane) (1 / 4)
    then f (x - lattice (Classical.choose h)) else 0

public theorem periodize_eq_in_patch (f : Plane → ℝ) {x : Plane} {k : Fin 2 → ℤ}
    (hx : x - lattice k ∈ Metric.ball (0 : Plane) (1 / 4)) :
    periodize f x = f (x - lattice k) := by
  classical
  have h : ∃ j : Fin 2 → ℤ, x - lattice j ∈ Metric.ball (0 : Plane) (1 / 4) := ⟨k, hx⟩
  rw [periodize, dite_eq_left h, unique_near_lattice (Classical.choose_spec h) hx]

private theorem periodize_eq_zero_of_outside_supports {f : Plane → ℝ}
    (hSupp : tsupport f ⊆ Metric.closedBall (0 : Plane) (9 / 64))
    {x : Plane} (hx : ∀ k, x - lattice k ∉ Metric.closedBall (0 : Plane) (9 / 64)) :
    periodize f x = 0 := by
  classical
  by_cases h : ∃ k : Fin 2 → ℤ, x - lattice k ∈ Metric.ball (0 : Plane) (1 / 4)
  · obtain ⟨k, hk⟩ := h
    rw [periodize_eq_in_patch f hk]
    exact image_eq_zero_of_notMem_tsupport (fun h => hx k (hSupp h))
  · rw [periodize, dite_eq_right h]

public theorem periodize_add_lattice (f : Plane → ℝ) (x : Plane) (k : Fin 2 → ℤ) :
    periodize f (x + lattice k) = periodize f x := by
  classical
  by_cases hx : ∃ j, x - lattice j ∈ Metric.ball (0 : Plane) (1 / 4)
  · obtain ⟨j, hj⟩ := hx
    have hShift : x + lattice k - lattice (j + k) = x - lattice j := by rw [lattice_add]; abel
    have hNear : x + lattice k - lattice (j + k) ∈ Metric.ball (0 : Plane) (1 / 4) :=
      hShift.symm ▸ hj
    rw [periodize_eq_in_patch f hNear, periodize_eq_in_patch f hj, hShift]
  · have hx' : ¬ ∃ j, x + lattice k - lattice j ∈ Metric.ball (0 : Plane) (1 / 4) := by
      rintro ⟨j, hj⟩
      apply hx
      refine ⟨j - k, ?_⟩
      have hShift : x - lattice (j - k) = x + lattice k - lattice j := by
        have he := lattice_add (j - k) k
        rw [sub_add_cancel] at he
        rw [he]
        abel
      exact hShift.symm ▸ hj
    have hL : periodize f (x + lattice k) = 0 := by rw [periodize, dite_eq_right hx']
    have hR : periodize f x = 0 := by rw [periodize, dite_eq_right hx]
    rw [hL, hR]

/-- At every point, the periodization equals locally either a translated
profile or the zero function. -/
public theorem periodize_local {f : Plane → ℝ}
    (hSupp : tsupport f ⊆ Metric.closedBall (0 : Plane) (9 / 64)) (x : Plane) :
    (∃ k : Fin 2 → ℤ, periodize f =ᶠ[𝓝 x] fun y => f (y - lattice k)) ∨
      periodize f =ᶠ[𝓝 x] 0 := by
  classical
  by_cases hx : ∃ k, x - lattice k ∈ Metric.ball (0 : Plane) (1 / 4)
  · obtain ⟨k, hk⟩ := hx
    left
    refine ⟨k, ?_⟩
    have hOpen : IsOpen ((fun y : Plane => y - lattice k) ⁻¹' Metric.ball (0 : Plane) (1 / 4)) :=
      Metric.isOpen_ball.preimage (continuous_id.sub continuous_const)
    filter_upwards [hOpen.mem_nhds hk] with y hy
    exact periodize_eq_in_patch f hy
  · right
    filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 7 / 64)] with y hy
    apply periodize_eq_zero_of_outside_supports hSupp
    intro k hk
    have hT := dist_triangle x y (lattice k)
    have h1 := Metric.mem_ball.mp hy
    have h2 := Metric.mem_closedBall.mp hk
    rw [dist_zero_right, ← dist_eq_norm] at h2
    apply hx
    refine ⟨k, Metric.mem_ball.mpr ?_⟩
    rw [dist_zero_right, ← dist_eq_norm]
    rw [dist_comm x y] at hT
    linarith only [hT, h1, h2]

public theorem contDiff_two_periodize {f : Plane → ℝ} (hf : ContDiff ℝ 2 f)
    (hSupp : tsupport f ⊆ Metric.closedBall (0 : Plane) (9 / 64)) :
    ContDiff ℝ 2 (periodize f) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases periodize_local hSupp x with ⟨k, hk⟩ | hz
  · exact (hf.comp (contDiff_id.sub contDiff_const)).contDiffAt.congr_of_eventuallyEq hk
  · exact contDiffAt_const.congr_of_eventuallyEq hz

public theorem smooth_periodize_off_lattice {f : Plane → ℝ}
    (hf : ContDiffOn ℝ ∞ f ({0}ᶜ : Set Plane))
    (hSupp : tsupport f ⊆ Metric.closedBall (0 : Plane) (9 / 64)) :
    ContDiffOn ℝ ∞ (periodize f) (Set.range lattice)ᶜ := by
  intro x hx
  rcases periodize_local hSupp x with ⟨k, hk⟩ | hz
  · have h0 : x - lattice k ∈ ({0}ᶜ : Set Plane) := by
      intro h
      apply hx
      exact ⟨k, (sub_eq_zero.mp h).symm⟩
    have hF := hf.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds h0)
    have hC : ContDiffAt ℝ ∞ (fun y : Plane => y - lattice k) x :=
      (contDiff_id.sub contDiff_const).contDiffAt
    exact ((hF.comp x hC).congr_of_eventuallyEq hk).contDiffWithinAt
  · exact (contDiffAt_const.congr_of_eventuallyEq hz).contDiffWithinAt

/-- The periodized coefficient agrees with the original profile near zero. -/
public theorem periodize_nhds_origin (f : Plane → ℝ) : periodize f =ᶠ[𝓝 (0 : Plane)] f := by
  filter_upwards [Metric.ball_mem_nhds (0 : Plane) (by norm_num : (0 : ℝ) < 1 / 4)] with x hx
  have h : x - lattice 0 ∈ Metric.ball (0 : Plane) (1 / 4) := by simpa [lattice_zero] using hx
  simpa [lattice_zero] using periodize_eq_in_patch f h

public theorem norm_periodize_le {f : Plane → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, ‖f x‖ ≤ C) (x : Plane) : ‖periodize f x‖ ≤ C := by
  classical
  by_cases hx : ∃ k, x - lattice k ∈ Metric.ball (0 : Plane) (1 / 4)
  · obtain ⟨k, hk⟩ := hx
    rw [periodize_eq_in_patch f hk]
    exact h _
  · rw [periodize, dite_eq_right hx, norm_zero]
    exact hC

/-- The zeroth, first and second uniform bounds pass to the periodization
with the same constants, because every local model is an integer translate
or the zero function. -/
public theorem periodize_bounds {f : Plane → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hSupp : tsupport f ⊆ Metric.closedBall (0 : Plane) (9 / 64))
    (h₀ : ∀ x, ‖f x‖ ≤ C)
    (h₁ : ∀ x, ‖fderiv ℝ f x‖ ≤ C)
    (h₂ : ∀ x, tensorHS (iteratedFDeriv ℝ 2 f x) ≤ C)
    (x : Plane) :
    ‖periodize f x‖ ≤ C ∧ ‖fderiv ℝ (periodize f) x‖ ≤ C ∧
      tensorHS (iteratedFDeriv ℝ 2 (periodize f) x) ≤ C := by
  refine ⟨norm_periodize_le hC h₀ x, ?_⟩
  rcases periodize_local hSupp x with ⟨k, hk⟩ | hz
  · constructor
    · rw [hk.fderiv_eq, fderiv_comp_sub]
      exact h₁ _
    · rw [(hk.iteratedFDeriv ℝ 2).eq_of_nhds, iteratedFDeriv_comp_sub]
      exact h₂ _
  · constructor
    · rw [hz.fderiv_eq, fderiv_zero, Pi.zero_apply, norm_zero]
      exact hC
    · rw [(hz.iteratedFDeriv ℝ 2).eq_of_nhds, iteratedFDeriv_zero, Pi.zero_apply,
        tensorHS, map_zero, norm_zero]
      exact hC

end C2Riemannian.TorusDiskGeometry
