module

public import C2Riemannian.InteriorExhaustion
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped Topology

namespace C2Riemannian

/-- One strictly increasing natural frequency sequence meets all eventual
constraints of the finite family at each step. -/
public theorem choose_layer_frequencies {ι : Type*} [Finite ι]
    (Accept : ℕ → ι → ℕ → Prop) (h : ∀ k i, ∀ᶠ L in atTop, Accept k i L) :
    ∃ L : ℕ → ℕ, StrictMono L ∧ (∀ k, 1 ≤ L k) ∧ ∀ k i, Accept k i (L k) := by
  classical
  have hAll (k : ℕ) : ∀ᶠ L in atTop, ∀ i, Accept k i L :=
    Filter.eventually_all.mpr (h k)
  choose M hM using fun k => eventually_atTop.mp (hAll k)
  let L : ℕ → ℕ := Nat.rec (max 1 (M 0)) (fun k v => max (v + 1) (M (k + 1)))
  have hStrict : StrictMono L := strictMono_nat_of_lt_succ fun k =>
    Nat.lt_succ_self (L k) |>.trans_le (le_max_left _ _)
  have hM' (k : ℕ) : M k ≤ L k := by
    cases k with
    | zero => exact le_max_right _ _
    | succ k => exact le_max_right _ _
  exact ⟨L, hStrict, fun k => (le_max_left 1 (M 0)).trans (hStrict.monotone (Nat.zero_le k)),
    fun k i => hM k (L k) (hM' k) i⟩

/-- A common shift of the exhaustion puts all parent area losses below
the prescribed relative tolerance. -/
public theorem choose_common_parent_exhaustion_tail {ι : Type*} [Finite ι]
    {P : ι → Set Plane} (E : ∀ i, InteriorExhaustion (P i)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ k i,
      (volume (P i \ parentInterior (P i) (E i).radius (k + N))).toReal <
        δ * (volume (P i)).toReal / 4 := by
  have hpos (i : ι) : 0 < δ * (volume (P i)).toReal / 4 := by
    have hArea := ENNReal.toReal_pos (ne_of_gt (E i).volume_pos) (E i).volume_finite
    positivity
  have hEach (i : ι) : ∀ᶠ n in atTop,
      (volume (P i \ parentInterior (P i) (E i).radius n)).toReal <
        δ * (volume (P i)).toReal / 4 :=
    (E i).area_remainder_tendsto (eventually_lt_nhds (hpos i))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (Filter.eventually_all.mpr hEach)
  exact ⟨N, fun k i => hN (k + N) (Nat.le_add_left N k) i⟩

end C2Riemannian
