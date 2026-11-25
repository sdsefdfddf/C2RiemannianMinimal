module

public import C2Riemannian.BoundedPhysicalTree
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

open Set

namespace C2Riemannian

/-- The prescribed slope of the oblique splitting directions. -/
@[expose] public noncomputable def splittingSlope (N : ℕ) : ℝ :=
  1 / Real.sqrt (2 * (N : ℝ))

/-- A scheduled tree with the actual normalized slope and relative area tolerance. -/
public theorem exists_realized_parameter_tree {Q : Set Plane} (hQ : Bornology.IsBounded Q)
    (hOpen : IsOpen Q) (hNonempty : Q.Nonempty) (N J : ℕ) (hN : 2 ≤ N) (_hJ : 1 ≤ J) :
    Nonempty (PhysicalParameterTree idealPhysicalDirections (splittingSlope N)
      (layerAreaTolerance (SplitStep.schedule N J).length (4 * (2 : ℝ) ^ (4 * N * J) + 1))
      (ScheduledPhysicalInvariant N J (splittingSlope N))
      (idealLayers 0 (SplitStep.schedule N J)) (PhysicalPrefix.root Q hOpen hNonempty)) := by
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hN)
  have hSq : (Real.sqrt (2 * (N : ℝ))) ^ 2 = 2 * (N : ℝ) :=
    Real.sq_sqrt (mul_nonneg (by norm_num) hNp.le)
  have hs : 2 * (N : ℝ) * splittingSlope N ^ 2 = 1 := by
    rw [splittingSlope, div_pow, one_pow, hSq, mul_one_div_cancel (by positivity)]
  obtain ⟨hδ, hδ'⟩ := layerAreaTolerance_bounds (SplitStep.schedule N J).length
    (BT := 4 * (2 : ℝ) ^ (4 * N * J) + 1) (by positivity)
  exact exists_bounded_scheduled_physical_tree hQ hOpen hNonempty N J _ _ hN hs hδ hδ'

end C2Riemannian
