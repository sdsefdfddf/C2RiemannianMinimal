module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace C2Riemannian

/-- The entries of a scalar symmetric Hessian in the planar coordinates. -/
public structure ScalarHess where
  xx : ℝ
  xy : ℝ
  yy : ℝ

namespace ScalarHess

@[expose] public noncomputable def det (A : ScalarHess) : ℝ :=
  A.xx * A.yy - A.xy ^ 2

@[expose] public noncomputable def frobeniusSq (A : ScalarHess) : ℝ :=
  A.xx ^ 2 + 2 * A.xy ^ 2 + A.yy ^ 2

@[expose] public noncomputable def rankOneUpdate (A : ScalarHess) (u nx ny : ℝ) : ScalarHess :=
  ⟨A.xx + u * nx ^ 2, A.xy + u * nx * ny, A.yy + u * ny ^ 2⟩

public theorem det_rankone_increment (A : ScalarHess) (u nx ny : ℝ) :
    (A.rankOneUpdate u nx ny).det - A.det =
      u * (A.yy * nx ^ 2 - 2 * A.xy * nx * ny + A.xx * ny ^ 2) := by
  simp only [det, rankOneUpdate]
  ring

public theorem det_rankone_mean (A : ScalarHess) (u nx ny : ℝ) :
    ((A.rankOneUpdate u nx ny).det + (A.rankOneUpdate (-u) nx ny).det) / 2 = A.det := by
  have hpos := A.det_rankone_increment u nx ny
  have hneg := A.det_rankone_increment (-u) nx ny
  calc
    _ = A.det + ((A.rankOneUpdate u nx ny).det - A.det +
        ((A.rankOneUpdate (-u) nx ny).det - A.det)) / 2 := by ring
    _ = A.det := by rw [hpos, hneg]; ring

@[expose] public noncomputable def scale (c : ℝ) (A : ScalarHess) : ScalarHess :=
  ⟨c * A.xx, c * A.xy, c * A.yy⟩

public theorem det_scale (c : ℝ) (A : ScalarHess) : (A.scale c).det = c ^ 2 * A.det := by
  simp only [det, scale]
  ring

public theorem frobeniusSq_scale (c : ℝ) (A : ScalarHess) :
    (A.scale c).frobeniusSq = c ^ 2 * A.frobeniusSq := by
  simp only [frobeniusSq, scale]
  ring

@[expose] public noncomputable def linearSource (background theta : ℝ) (A : ScalarHess) : ℝ :=
  -background / 2 - theta * A.yy / 10

@[expose] public noncomputable def reverseSource (A : ScalarHess) : ℝ := -A.det / 25

public theorem reverseSource_eq_neg_scaled_det (A : ScalarHess) :
    A.reverseSource = -(A.scale (1 / 5)).det := by
  rw [det_scale]
  unfold reverseSource
  ring

public theorem linearSource_rankOne (A : ScalarHess) (background theta u nx ny : ℝ) :
    (A.rankOneUpdate u nx ny).linearSource background theta -
      A.linearSource background theta = -theta * u * ny ^ 2 / 10 := by
  simp only [linearSource, rankOneUpdate]
  ring

public theorem reverseSource_rankOne (A : ScalarHess) (u nx ny : ℝ) :
    (A.rankOneUpdate u nx ny).reverseSource - A.reverseSource =
      -u * (A.yy * nx ^ 2 - 2 * A.xy * nx * ny + A.xx * ny ^ 2) / 25 := by
  have h := A.det_rankone_increment u nx ny
  unfold reverseSource
  linarith only [h]

public theorem linearSource_negative_vertical (A : ScalarHess) (background theta : ℝ) :
    (A.rankOneUpdate (-1) 0 1).linearSource background theta -
      A.linearSource background theta = theta / 10 := by
  rw [linearSource_rankOne]
  ring

public theorem abs_linearSource_jump_le (A : ScalarHess) (background theta u nx ny : ℝ)
    (ht : 0 ≤ theta) (ht' : theta ≤ 1) (hu : |u| ≤ 1) :
    |(A.rankOneUpdate u nx ny).linearSource background theta -
      A.linearSource background theta| ≤ ny ^ 2 / 10 := by
  rw [linearSource_rankOne, abs_div, abs_mul, abs_mul, abs_neg,
    abs_of_nonneg ht, abs_of_nonneg (sq_nonneg ny), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 10)]
  have htu : theta * |u| ≤ 1 := by
    calc
      theta * |u| ≤ theta * 1 := mul_le_mul_of_nonneg_left hu ht
      _ ≤ 1 := by simpa only [mul_one] using ht'
  exact div_le_div_of_nonneg_right (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right htu (sq_nonneg ny)) (by norm_num)

end ScalarHess
end C2Riemannian
