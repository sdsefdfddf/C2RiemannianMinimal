module

public import C2Riemannian.FunctionalMoments
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Oblique step energy, M37–38 (paper (22)–(23)) -/

set_option autoImplicit false

namespace C2Riemannian
namespace PositiveFunctional

variable {α : Type*} [TopologicalSpace α] {m : ℕ}

/-- Subtract the mean from a vector readout. -/
@[expose] public def centered (L : PositiveFunctional α) (U : C(α, Target m)) :
    C(α, Target m) :=
  U - ContinuousMap.const α (L.mean U)

/-- Variance of a vector readout. -/
@[expose] public noncomputable def variance (L : PositiveFunctional α) (U : C(α, Target m)) : ℝ :=
  L (sqNormReadout (L.centered U))

/-- The curvature readout of the three Hessian entries. -/
@[expose] public noncomputable def qReadout (X Z Y : C(α, Target m)) : C(α, ℝ) :=
  innerReadout X Y - sqNormReadout Z

/-- The energy readout of the normal Hessian entry. -/
@[expose] public noncomputable def energyReadout (Y : C(α, Target m)) : C(α, ℝ) :=
  (1 / 2 : ℝ) • sqNormReadout Y

@[simp] public theorem qReadout_apply (X Z Y : C(α, Target m)) (x : α) :
    qReadout X Z Y x = (Hess3.mk (X x) (Z x) (Y x)).q := by
  simp [qReadout, Hess3.q]

@[simp] public theorem energyReadout_apply (Y : C(α, Target m)) (x : α) :
    energyReadout Y x = ‖Y x‖ ^ 2 / 2 := by
  simp only [energyReadout, ContinuousMap.smul_apply, smul_eq_mul, sqNormReadout_apply]
  ring

/-- The covariance contribution to the curvature readout. -/
@[expose] public noncomputable def curvatureCovariance
    (L : PositiveFunctional α) (X Z Y : C(α, Target m)) : ℝ :=
  L (innerReadout (L.centered X) (L.centered Y)) - L.variance Z

public theorem variance_nonneg (L : PositiveFunctional α) (U : C(α, Target m)) :
    0 ≤ L.variance U :=
  L.map_sqNormReadout_nonneg _

public theorem variance_eq (L : PositiveFunctional α) (U : C(α, Target m)) :
    L.variance U = L (sqNormReadout U) - ‖L.mean U‖ ^ 2 :=
  L.functional_variance U

public theorem map_qReadout (L : PositiveFunctional α) (X Z Y : C(α, Target m)) :
    L (qReadout X Z Y) = (Hess3.mk (L.mean X) (L.mean Z) (L.mean Y)).q +
      L.curvatureCovariance X Z Y := by
  simp only [qReadout, map_sub, Hess3.q, curvatureCovariance, centered, L.centered_inner,
    L.variance_eq, real_inner_self_eq_norm_sq]
  ring

public theorem map_energyReadout (L : PositiveFunctional α) (Y : C(α, Target m)) :
    L (energyReadout Y) = ‖L.mean Y‖ ^ 2 / 2 + L.variance Y / 2 := by
  simp only [energyReadout, map_smul, smul_eq_mul, L.variance_eq]
  ring

/-- The curvature and energy changes under the oblique mean constraints. -/
public theorem oblique_curvature_energy (L : PositiveFunctional α) (X Z Y : C(α, Target m))
    (H₀ : Hess3 m) (β : Target m) (t : ℝ)
    (hX : L.mean X = H₀.xx + β) (hZ : L.mean Z = H₀.xy + t • β)
    (hY : L.mean Y = H₀.yy + t ^ 2 • β) :
    L (qReadout X Z Y) - H₀.q =
        inner ℝ β (H₀.yy - (2 * t) • H₀.xy + t ^ 2 • H₀.xx) +
          L.curvatureCovariance X Z Y ∧
      L (energyReadout Y) - H₀.energy =
        t ^ 2 * inner ℝ β H₀.yy + t ^ 4 * ‖β‖ ^ 2 / 2 + L.variance Y / 2 := by
  constructor
  · rw [L.map_qReadout, hX, hZ, hY]
    simp only [Hess3.q, inner_add_left, inner_add_right, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm H₀.xx β, real_inner_comm H₀.xy β]
    ring
  · rw [L.map_energyReadout, hY, Hess3.energy, norm_add_sq_real, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, real_inner_smul_right, real_inner_comm H₀.yy β]
    ring

public theorem curvatureCovariance_le (L : PositiveFunctional α) (X Z Y : C(α, Target m))
    (K : ℝ) (hK : 0 ≤ K) (hX : L (sqNormReadout X) ≤ K ^ 2) :
    L.curvatureCovariance X Z Y ≤ K * √(L.variance Y) := by
  have hVX : L.variance X ≤ K ^ 2 := by
    rw [L.variance_eq]
    exact (sub_le_self _ (sq_nonneg _)).trans hX
  have hsqrt : √(L.variance X) ≤ K := by
    rw [← Real.sqrt_sq hK]
    exact Real.sqrt_le_sqrt hVX
  calc
    L.curvatureCovariance X Z Y
        ≤ L (innerReadout (L.centered X) (L.centered Y)) :=
      sub_le_self _ (L.variance_nonneg Z)
    _ ≤ |L (innerReadout (L.centered X) (L.centered Y))| := le_abs_self _
    _ ≤ √(L.variance X) * √(L.variance Y) :=
      L.abs_map_innerReadout_le _ _
    _ ≤ K * √(L.variance Y) := mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _)

/-- The signed oblique energy lower bound before restricting the slope. -/
public theorem oblique_energy_lower (L : PositiveFunctional α) (X Z Y : C(α, Target m))
    (H₀ : Hess3 m) (β : Target m) (t K : ℝ) (hK : 0 ≤ K)
    (hX : L.mean X = H₀.xx + β) (hZ : L.mean Z = H₀.xy + t • β)
    (hY : L.mean Y = H₀.yy + t ^ 2 • β)
    (hX₂ : L (sqNormReadout X) ≤ K ^ 2)
    (hxx : ‖H₀.xx‖ ≤ K) (hxy : ‖H₀.xy‖ ≤ K) (hβ : ‖β‖ ≤ 2 * K) :
    t ^ 2 * (L (qReadout X Z Y) - H₀.q) - 4 * K ^ 2 * |t| ^ 3 -
        (5 / 2 : ℝ) * K ^ 2 * t ^ 4 ≤ L (energyReadout Y) - H₀.energy := by
  obtain ⟨hq, he⟩ := L.oblique_curvature_energy X Z Y H₀ β t hX hZ hY
  have hq' : L (qReadout X Z Y) - H₀.q =
      inner ℝ β H₀.yy - 2 * t * inner ℝ β H₀.xy +
        t ^ 2 * inner ℝ β H₀.xx + L.curvatureCovariance X Z Y := by
    rw [hq, inner_add_right, inner_sub_right, real_inner_smul_right, real_inner_smul_right]
  have hE : L (energyReadout Y) - H₀.energy =
      t ^ 2 * (L (qReadout X Z Y) - H₀.q) +
        2 * t ^ 3 * inner ℝ β H₀.xy - t ^ 4 * inner ℝ β H₀.xx +
        t ^ 4 * ‖β‖ ^ 2 / 2 + L.variance Y / 2 - t ^ 2 * L.curvatureCovariance X Z Y := by
    rw [he, hq']
    ring
  have hprod (u : Target m) (hu : ‖u‖ ≤ K) : |inner ℝ β u| ≤ 2 * K ^ 2 := by
    calc
      |inner ℝ β u| ≤ ‖β‖ * ‖u‖ := abs_real_inner_le_norm _ _
      _ ≤ (2 * K) * K :=
        mul_le_mul hβ hu (norm_nonneg _) (mul_nonneg (by norm_num) hK)
      _ = 2 * K ^ 2 := by ring
  have hxy₃ : -(4 * K ^ 2 * |t| ^ 3) ≤ 2 * t ^ 3 * inner ℝ β H₀.xy := by
    apply neg_le_of_abs_le
    rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
    calc
      (2 * |t| ^ 3) * |inner ℝ β H₀.xy| ≤ (2 * |t| ^ 3) * (2 * K ^ 2) :=
        mul_le_mul_of_nonneg_left (hprod _ hxy) (mul_nonneg (by norm_num) (pow_nonneg (abs_nonneg _) _))
      _ = 4 * K ^ 2 * |t| ^ 3 := by ring
  have hxx₄ : t ^ 4 * inner ℝ β H₀.xx ≤ t ^ 4 * (2 * K ^ 2) :=
    mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hprod _ hxx)) (by positivity)
  have hcov := mul_le_mul_of_nonneg_left (L.curvatureCovariance_le X Z Y K hK hX₂) (sq_nonneg t)
  have hV : (√(L.variance Y)) ^ 2 = L.variance Y := Real.sq_sqrt (L.variance_nonneg Y)
  have hcomplete : -(K ^ 2 * t ^ 4 / 2) ≤ L.variance Y / 2 - t ^ 2 * L.curvatureCovariance X Z Y := by
    nlinarith only [hcov, hV, sq_nonneg (√(L.variance Y) - K * t ^ 2)]
  have hβ₄ : 0 ≤ t ^ 4 * ‖β‖ ^ 2 / 2 := by positivity
  rw [hE]
  linarith only [hxy₃, hxx₄, hcomplete, hβ₄]

/-- For slopes of absolute value at most one the error is bounded by the cubic term. -/
public theorem oblique_energy_lower_cubic (L : PositiveFunctional α) (X Z Y : C(α, Target m))
    (H₀ : Hess3 m) (β : Target m) (t K : ℝ) (hK : 0 ≤ K) (ht : |t| ≤ 1)
    (hX : L.mean X = H₀.xx + β) (hZ : L.mean Z = H₀.xy + t • β)
    (hY : L.mean Y = H₀.yy + t ^ 2 • β)
    (hX₂ : L (sqNormReadout X) ≤ K ^ 2)
    (hxx : ‖H₀.xx‖ ≤ K) (hxy : ‖H₀.xy‖ ≤ K) (hβ : ‖β‖ ≤ 2 * K) :
    t ^ 2 * (L (qReadout X Z Y) - H₀.q) - 7 * K ^ 2 * |t| ^ 3 ≤
      L (energyReadout Y) - H₀.energy := by
  have h₄ : t ^ 4 ≤ |t| ^ 3 := by
    calc
      t ^ 4 = |t| ^ 4 := (abs_of_nonneg (show 0 ≤ t ^ 4 by positivity)).symm.trans (abs_pow t 4)
      _ = |t| ^ 3 * |t| := by ring
      _ ≤ |t| ^ 3 := mul_le_of_le_one_right (by positivity) ht
  have hscaled := mul_le_mul_of_nonneg_left h₄ (show 0 ≤ (5 / 2 : ℝ) * K ^ 2 by positivity)
  have hcube : 0 ≤ K ^ 2 * |t| ^ 3 := by positivity
  have h := L.oblique_energy_lower X Z Y H₀ β t K hK hX hZ hY hX₂ hxx hxy hβ
  linarith only [hscaled, hcube, h]

public theorem horizontal_energy_eq (L : PositiveFunctional α) (Y : C(α, Target m))
    (H₀ : Hess3 m) (hY : L.mean Y = H₀.yy) :
    L (energyReadout Y) - H₀.energy = L.variance Y / 2 := by
  rw [L.map_energyReadout, hY, Hess3.energy]
  ring

/-- A linear source jump bounded below by `-t²/10` gives an unsigned cubic loss. -/
public theorem oblique_linear_energy_lower (L : PositiveFunctional α) (X Z Y : C(α, Target m))
    (H₀ : Hess3 m) (β : Target m) (t K : ℝ) (hK : 1 ≤ K) (ht : |t| ≤ 1)
    (hX : L.mean X = H₀.xx + β) (hZ : L.mean Z = H₀.xy + t • β)
    (hY : L.mean Y = H₀.yy + t ^ 2 • β)
    (hX₂ : L (sqNormReadout X) ≤ K ^ 2)
    (hxx : ‖H₀.xx‖ ≤ K) (hxy : ‖H₀.xy‖ ≤ K) (hβ : ‖β‖ ≤ 2 * K)
    (hjump : -(t ^ 2 / 10) ≤ L (qReadout X Z Y) - H₀.q) :
    -(7 * K ^ 2 * |t| ^ 3) ≤ L (energyReadout Y) - H₀.energy := by
  have hK₀ : 0 ≤ K := le_trans (by norm_num) hK
  have hK₂ : 1 ≤ K ^ 2 := by nlinarith only [hK, sq_nonneg (K - 1)]
  have h₄ : t ^ 4 ≤ |t| ^ 3 := by
    calc
      t ^ 4 = |t| ^ 4 :=
        (abs_of_nonneg (show 0 ≤ t ^ 4 by positivity)).symm.trans (abs_pow t 4)
      _ = |t| ^ 3 * |t| := by ring
      _ ≤ |t| ^ 3 := mul_le_of_le_one_right (by positivity) ht
  have h₄' : t ^ 4 ≤ K ^ 2 * |t| ^ 3 := by
    calc
      t ^ 4 ≤ |t| ^ 3 := h₄
      _ = 1 * |t| ^ 3 := (one_mul _).symm
      _ ≤ K ^ 2 * |t| ^ 3 := mul_le_mul_of_nonneg_right hK₂ (by positivity)
  have hscaled := mul_le_mul_of_nonneg_left h₄ (show 0 ≤ (5 / 2 : ℝ) * K ^ 2 by positivity)
  have hcube : 0 ≤ K ^ 2 * |t| ^ 3 := by positivity
  have hΔ := mul_le_mul_of_nonneg_left hjump (sq_nonneg t)
  have h := L.oblique_energy_lower X Z Y H₀ β t K hK₀ hX hZ hY hX₂ hxx hxy hβ
  linarith only [h, hΔ, hscaled, h₄', hcube]

end PositiveFunctional
end C2Riemannian
