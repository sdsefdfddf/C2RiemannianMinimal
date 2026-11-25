module

public import C2Riemannian.PhysicalParameterTree
public import C2Riemannian.VerticalEnergy
public import C2Riemannian.HessianReadoutBounds
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Filter MeasureTheory Set

namespace C2Riemannian.PositiveFunctional

variable {X : Type*} [TopologicalSpace X] {m : ℕ}

/-- The horizontal step transfers the continuing phase bound to the parent. -/
public theorem horizontal_parent_energy_le (L : PositiveFunctional X)
    (Y : C(X, Target m)) (H : Hess3 m) (B : ℝ) (hY : L.mean Y = H.yy)
    (hB : L (energyReadout Y) ≤ B) : H.energy ≤ B := by
  have he := L.horizontal_energy_eq Y H hY
  linarith only [he, L.variance_nonneg Y, hB]

/-- Two continuing vertical phases transfer their common budget with any
established lower bound for the gain of their arithmetic average. -/
public theorem vertical_parent_energy_add_le (Lpos Lneg : PositiveFunctional X)
    (Y : C(X, Target m)) (H : Hess3 m) (B g : ℝ)
    (hBpos : Lpos (energyReadout Y) ≤ B) (hBneg : Lneg (energyReadout Y) ≤ B)
    (hGain : g ≤ (Lpos (energyReadout Y) + Lneg (energyReadout Y)) / 2 - H.energy) :
    H.energy + g ≤ B := by
  linarith only [hBpos, hBneg, hGain]

/-- The upper budget on the continuing oblique phase subtracts its gain from
the parent's budget. A signed gain may be used. -/
public theorem oblique_parent_energy_add_le (L : PositiveFunctional X)
    (Y : C(X, Target m)) (H : Hess3 m) (B g : ℝ)
    (hB : L (energyReadout Y) ≤ B) (hGain : g ≤ L (energyReadout Y) - H.energy) :
    H.energy + g ≤ B := by
  linarith only [hB, hGain]

/-- The negative phase gives the gain for a vertical step with the linear source. -/
public theorem vertical_linear_parent_energy_le (Lpos Lneg : PositiveFunctional X)
    (U Z Y : C(X, Target m)) (H : Hess3 m) (K θ B : ℝ)
    (hK : 0 < K) (hθ : 0 ≤ θ)
    (hU : Lneg.mean U = H.xx) (hZ : Lneg.mean Z = H.xy)
    (hU₂ : Lneg (sqNormReadout U) ≤ K ^ 2)
    (hY : H.yy = (1 / 2 : ℝ) • (Lpos.mean Y + Lneg.mean Y))
    (hJump : θ / 10 ≤ Lneg (qReadout U Z Y) - H.q)
    (hBpos : Lpos (energyReadout Y) ≤ B) (hBneg : Lneg (energyReadout Y) ≤ B) :
    H.energy + θ ^ 2 / (400 * K ^ 2) ≤ B := by
  have hmean : Lpos.mean Y + Lneg.mean Y = (2 : ℝ) • H.yy := by
    rw [hY, smul_smul]
    norm_num
  exact vertical_parent_energy_add_le Lpos Lneg Y H B _ hBpos hBneg
    (vertical_linear_energy_lower Lpos Lneg U Z Y H K θ hK hθ hU hZ hU₂ hmean hJump)

/-- A vertical step for the reverse source uses both phases and zero gain. -/
public theorem vertical_reverse_parent_energy_le (Lpos Lneg : PositiveFunctional X)
    (Y : C(X, Target m)) (H : Hess3 m) (B : ℝ)
    (hY : H.yy = (1 / 2 : ℝ) • (Lpos.mean Y + Lneg.mean Y))
    (hBpos : Lpos (energyReadout Y) ≤ B) (hBneg : Lneg (energyReadout Y) ≤ B) :
    H.energy ≤ B := by
  have hmean : Lpos.mean Y + Lneg.mean Y = (2 : ℝ) • H.yy := by
    rw [hY, smul_smul]
    norm_num
  simpa only [add_zero] using vertical_parent_energy_add_le Lpos Lneg Y H B 0 hBpos hBneg
    (vertical_energy_nonneg Lpos Lneg Y H hmean)

/-- The linear source transfers the continuing oblique phase with the cubic loss. -/
public theorem oblique_linear_parent_energy_le (L : PositiveFunctional X)
    (U Z Y : C(X, Target m)) (H : Hess3 m) (β : Target m) (t K B : ℝ)
    (hK : 1 ≤ K) (ht : |t| ≤ 1)
    (hU : L.mean U = H.xx + β) (hZ : L.mean Z = H.xy + t • β)
    (hY : L.mean Y = H.yy + t ^ 2 • β)
    (hU₂ : L (sqNormReadout U) ≤ K ^ 2)
    (hxx : ‖H.xx‖ ≤ K) (hxy : ‖H.xy‖ ≤ K) (hβ : ‖β‖ ≤ 2 * K)
    (hJump : -(t ^ 2 / 10) ≤ L (qReadout U Z Y) - H.q)
    (hB : L (energyReadout Y) ≤ B) :
    H.energy + -(7 * K ^ 2 * |t| ^ 3) ≤ B :=
  oblique_parent_energy_add_le L Y H B _ hB
    (L.oblique_linear_energy_lower U Z Y H β t K hK ht hU hZ hY hU₂ hxx hxy hβ hJump)

/-- The reverse source transfers the signed oblique gain, keeping its exact curvature contribution. -/
public theorem oblique_reverse_parent_energy_le (L : PositiveFunctional X)
    (U Z Y : C(X, Target m)) (H : Hess3 m) (β : Target m) (t K B jump : ℝ)
    (hK : 0 ≤ K) (ht : |t| ≤ 1)
    (hU : L.mean U = H.xx + β) (hZ : L.mean Z = H.xy + t • β)
    (hY : L.mean Y = H.yy + t ^ 2 • β)
    (hU₂ : L (sqNormReadout U) ≤ K ^ 2)
    (hxx : ‖H.xx‖ ≤ K) (hxy : ‖H.xy‖ ≤ K) (hβ : ‖β‖ ≤ 2 * K)
    (hJump : t ^ 2 * (L (qReadout U Z Y) - H.q) = jump)
    (hB : L (energyReadout Y) ≤ B) :
    H.energy + (jump - 7 * K ^ 2 * |t| ^ 3) ≤ B := by
  apply oblique_parent_energy_add_le L Y H B _ hB
  simpa only [hJump] using L.oblique_energy_lower_cubic U Z Y H β t K hK ht hU hZ hY hU₂ hxx hxy hβ
end C2Riemannian.PositiveFunctional

namespace C2Riemannian.PhysicalPrefix

/-- The same energy estimate on each active platform holds on the whole active
region of the physical prefix. -/
public theorem activeRegion_energy_add_le {Q : Set Plane} (p : PhysicalPrefix Q)
    (E : Plane → ℝ) (g B : ℝ)
    (h : ∀ i : p.Active, ∀ᵐ x ∂volume.restrict (p.platform i.1), E x + g ≤ B) :
    ∀ᵐ x ∂volume.restrict p.activeRegion, E x ≤ B - g := by
  unfold activeRegion
  exact (ae_restrict_iUnion_iff _ _).2 fun i => (h i).mono fun x hx => le_sub_iff_add_le.mpr hx

/-- A finite list of residual layer gains determines the remaining budget. -/
@[expose] public noncomputable def energyBudget (K : ℝ) : List ℝ → ℝ
  | [] => K ^ 2 / 2
  | g :: gains => energyBudget K gains - g

@[simp] public theorem energyBudget_nil (K : ℝ) :
    energyBudget K [] = K ^ 2 / 2 := rfl

@[simp] public theorem energyBudget_cons (K g : ℝ) (gains : List ℝ) :
    energyBudget K (g :: gains) = energyBudget K gains - g := rfl

public theorem energyBudget_eq (K : ℝ) (gains : List ℝ) :
    energyBudget K gains = K ^ 2 / 2 - gains.sum := by
  induction gains with
  | nil => simp
  | cons g gains ih =>
    simp only [energyBudget_cons, List.sum_cons, ih]
    linarith

end C2Riemannian.PhysicalPrefix
