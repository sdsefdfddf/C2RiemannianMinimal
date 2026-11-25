module

public import C2Riemannian.CountableReadouts
public import C2Riemannian.ObliqueEnergy

set_option autoImplicit false

open Set

namespace C2Riemannian.HessianBall

variable {m : ℕ} {K : ℝ}

public theorem outer_fst_continuous : Continuous (fun H : HessSpace m => H.fst) :=
  WithLp.continuous_fst 2 (Target m) (WithLp 2 (Target m × Target m))

public theorem outer_snd_continuous : Continuous (fun H : HessSpace m => H.snd) :=
  WithLp.continuous_snd 2 (Target m) (WithLp 2 (Target m × Target m))

@[expose] public def xx : C(HessianBall m K, Target m) :=
  ⟨fun H => H.val.fst, outer_fst_continuous.comp continuous_subtype_val⟩

@[expose] public noncomputable def xy : C(HessianBall m K, Target m) :=
  ⟨fun H => (Real.sqrt 2)⁻¹ • H.val.snd.fst,
    by
      have h : Continuous (fun H : HessianBall m K => H.val.snd.fst) :=
        (WithLp.continuous_fst 2 (Target m) (Target m)).comp
          (outer_snd_continuous.comp continuous_subtype_val)
      exact h.const_smul ((Real.sqrt (2 : ℝ))⁻¹ : ℝ)⟩

@[expose] public def yy : C(HessianBall m K, Target m) :=
  ⟨fun H => H.val.snd.snd,
    (WithLp.continuous_snd 2 (Target m) (Target m)).comp
      (outer_snd_continuous.comp continuous_subtype_val)⟩

/-- A Hessian with the Frobenius bound is a point of the compact state ball. -/
@[expose] public noncomputable def ofHessian (H : Hess3 m) (hH : H.frobenius ≤ K) : HessianBall m K :=
  ⟨H.coordinates, by simpa only [Metric.mem_closedBall, dist_zero_right, H.norm_coordinates] using hH⟩

@[simp] public theorem xx_ofHessian (H : Hess3 m) (hH : H.frobenius ≤ K) :
    xx (ofHessian H hH) = H.xx := rfl

@[simp] public theorem xy_ofHessian (H : Hess3 m) (hH : H.frobenius ≤ K) :
    xy (ofHessian H hH) = H.xy := by
  simp only [xy, ofHessian, Hess3.coordinates]
  change (Real.sqrt 2)⁻¹ • (Real.sqrt 2 • H.xy) = H.xy
  rw [smul_smul, inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by norm_num)), one_smul]

@[simp] public theorem yy_ofHessian (H : Hess3 m) (hH : H.frobenius ≤ K) :
    yy (ofHessian H hH) = H.yy := rfl

@[expose] public noncomputable def curvature : C(HessianBall m K, ℝ) :=
  PositiveFunctional.qReadout xx xy yy

@[simp] public theorem curvature_ofHessian (H : Hess3 m) (hH : H.frobenius ≤ K) :
    curvature (ofHessian H hH) = H.q := by
  simp only [curvature, PositiveFunctional.qReadout_apply, xx_ofHessian, xy_ofHessian, yy_ofHessian]

end C2Riemannian.HessianBall


