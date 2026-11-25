module

public import C2Riemannian.HessianAlgebra
public import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace C2Riemannian

public abbrev HessSpace (m : ℕ) := WithLp 2 (Target m × WithLp 2 (Target m × Target m))

namespace Hess3

variable {m : ℕ}

/-- The middle entry represents two entries of the symmetric Hessian. -/
@[expose] public noncomputable def coordinates (H : Hess3 m) : HessSpace m :=
  WithLp.toLp 2 (H.xx, WithLp.toLp 2 (Real.sqrt 2 • H.xy, H.yy))

public theorem norm_coordinates_sq (H : Hess3 m) : ‖H.coordinates‖ ^ 2 = H.frobeniusSq := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖H.xx‖ ^ 2 + ‖WithLp.toLp 2 (Real.sqrt 2 • H.xy, H.yy)‖ ^ 2 = _
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖H.xx‖ ^ 2 + (‖Real.sqrt 2 • H.xy‖ ^ 2 + ‖H.yy‖ ^ 2) = _
  rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (by norm_num)]
  unfold frobeniusSq
  ring

public theorem norm_coordinates (H : Hess3 m) : ‖H.coordinates‖ = H.frobenius :=
  (sq_eq_sq₀ (norm_nonneg _) H.frobenius_nonneg).mp
    (H.norm_coordinates_sq.trans H.sq_frobenius.symm)

public theorem inner_coordinates (H : Hess3 m) (e : HessSpace m) :
    inner ℝ H.coordinates e = inner ℝ H.xx e.fst +
      (Real.sqrt 2 * inner ℝ H.xy e.snd.fst + inner ℝ H.yy e.snd.snd) := by
  rw [WithLp.prod_inner_apply]
  change inner ℝ H.xx e.fst + inner ℝ (WithLp.toLp 2 (Real.sqrt 2 • H.xy, H.yy)) e.snd = _
  rw [WithLp.prod_inner_apply]
  change inner ℝ H.xx e.fst +
    (inner ℝ (Real.sqrt 2 • H.xy) e.snd.fst + inner ℝ H.yy e.snd.snd) = _
  rw [real_inner_smul_left]

end Hess3

/-- The canonical linear evaluation of a second derivative field into the
weighted Cartesian Hessian coordinates. -/
@[expose] public noncomputable def hessianColumns {m : ℕ} :
    (Plane →L[ℝ] (Plane →L[ℝ] Target m)) →L[ℝ] HessSpace m :=
  let ex : Plane := EuclideanSpace.single 0 1
  let ey : Plane := EuclideanSpace.single 1 1
  let ev (u v : Plane) := (ContinuousLinearMap.apply ℝ (Target m) u).comp
    (ContinuousLinearMap.apply ℝ (Plane →L[ℝ] Target m) v)
  let yz := (WithLp.prodContinuousLinearEquiv 2 ℝ (Target m) (Target m)).symm.toContinuousLinearMap.comp
    ((Real.sqrt 2 • ev ex ey).prod (ev ey ey))
  (WithLp.prodContinuousLinearEquiv 2 ℝ (Target m) (WithLp 2 (Target m × Target m))).symm
    |>.toContinuousLinearMap.comp ((ev ex ex).prod yz)

public theorem hessianColumns_apply {m : ℕ} (B : Plane →L[ℝ] Plane →L[ℝ] Target m) :
    let ex : Plane := EuclideanSpace.single 0 1
    let ey : Plane := EuclideanSpace.single 1 1
    hessianColumns B = (⟨B ex ex, B ey ex, B ey ey⟩ : Hess3 m).coordinates := rfl

end C2Riemannian
