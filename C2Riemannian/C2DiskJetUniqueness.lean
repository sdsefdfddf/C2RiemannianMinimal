module

public import C2Riemannian.C2DiskBanach
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp

set_option autoImplicit false

open Set
open scoped ContDiff BoundedContinuousFunction

namespace C2Riemannian

private theorem dense_diskInterior {a : Plane} {R : ℝ} (hR : 0 < R) :
    Dense (((↑) : Metric.closedBall a R → Plane) ⁻¹' Metric.ball a R) := by
  intro x
  rw [closure_subtype]
  have himage : ((↑) : Metric.closedBall a R → Plane) ''
      (((↑) : Metric.closedBall a R → Plane) ⁻¹' Metric.ball a R) = Metric.ball a R := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      exact ⟨⟨y, Metric.ball_subset_closedBall hy⟩, hy, rfl⟩
  rw [himage, closure_ball a hR.ne']
  exact x.property

private theorem diskHessianAction_injective : Function.Injective diskHessianAction := by
  intro H K h
  have hm := Matrix.toEuclideanLin.injective (LinearMap.toContinuousLinearMap.injective h)
  apply (WithLp.ext_iff 2).mpr
  funext key
  exact congrFun (congrFun hm key.1) key.2

/-- The value of a closed-disk function determines both derivative fields. -/
public theorem C2ClosedDisk.ext_value {a : Plane} {R : ℝ} (hR : 0 < R)
    {u v : C2ClosedDisk a R} (h : u.1.1 = v.1.1) : u = v := by
  have hu : u.1.Compatible := u.2
  have hv : v.1.Compatible := v.2
  have hGrad : u.1.2.1 = v.1.2.1 := by
    apply BoundedContinuousFunction.ext
    intro x
    have hInjective : Function.Injective (innerSL ℝ (E := Plane)) := by
      intro p q hpq
      have hz : innerSL ℝ (p - q) = 0 := by rw [map_sub, hpq, sub_self]
      have hn := innerSL_apply_norm ℝ (p - q)
      rw [hz, norm_zero] at hn
      exact sub_eq_zero.mp (norm_eq_zero.mp hn.symm)
    apply hInjective
    refine EqOn.closure ?_ ((innerSL ℝ (E := Plane)).continuous.comp u.1.2.1.continuous)
      ((innerSL ℝ (E := Plane)).continuous.comp v.1.2.1.continuous) (dense_diskInterior hR x)
    intro y hy
    have hU := ((hu.1 y hy).1).fderiv
    have hV := ((hv.1 y hy).1).fderiv
    rw [h] at hU
    exact hU.symm.trans hV
  have hHess : u.1.2.2 = v.1.2.2 := by
    apply BoundedContinuousFunction.ext
    intro x
    apply diskHessianAction_injective
    refine EqOn.closure ?_ (diskHessianAction.continuous.comp u.1.2.2.continuous)
      (diskHessianAction.continuous.comp v.1.2.2.continuous) (dense_diskInterior hR x)
    intro y hy
    have hU := ((hu.1 y hy).2).fderiv
    have hV := ((hv.1 y hy).2).fderiv
    rw [hGrad] at hU
    exact hU.symm.trans hV
  apply Subtype.ext
  exact Prod.ext h (Prod.ext hGrad hHess)

/-- The compatible continuous jet is a classical C² coefficient in the interior. -/
public theorem C2ClosedDisk.contDiffOn_value {a : Plane} {R : ℝ} (u : C2ClosedDisk a R) :
    ContDiffOn ℝ 2 (diskFieldExtension u.1.1) (Metric.ball a R) := by
  let S := Metric.ball a R
  let f : Plane → ℝ := diskFieldExtension u.1.1
  let g : Plane → Plane := diskFieldExtension u.1.2.1
  let H : Plane → DiskHessian := diskFieldExtension u.1.2.2
  let L : Plane →L[ℝ] (Plane →L[ℝ] ℝ) := innerSL ℝ
  have uJet : u.1.Compatible := u.2
  have hH : ContinuousOn H (Metric.closedBall a R) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have h : (Metric.closedBall a R).domRestrict H = (u.1.2.2 : Metric.closedBall a R → DiskHessian) :=
      funext fun x => diskFieldExtension_of_mem _ x.property
    rw [h]
    exact u.1.2.2.continuous
  have hg (x : Plane) (hx : x ∈ S) : HasFDerivAt g (diskHessianAction (H x)) x := by
    simpa only [H, diskFieldExtension_of_mem _ (Metric.ball_subset_closedBall hx)] using (uJet.1 x hx).2
  have hf (x : Plane) (hx : x ∈ S) : HasFDerivAt f (L (g x)) x := by
    simpa only [g, L, diskFieldExtension_of_mem _ (Metric.ball_subset_closedBall hx)] using (uJet.1 x hx).1
  have hD : ContinuousOn (fderiv ℝ g) S :=
    (diskHessianAction.continuous.comp_continuousOn (hH.mono Metric.ball_subset_closedBall)).congr
      (fun x hx => (hg x hx).fderiv)
  have hC₁ : ContDiffOn ℝ (0 + 1) g S :=
    (contDiffOn_succ_iff_fderiv_of_isOpen Metric.isOpen_ball).mpr
      ⟨fun x hx => (hg x hx).differentiableAt.differentiableWithinAt, by simp, contDiffOn_zero.mpr hD⟩
  have hC₂ : ContDiffOn ℝ (1 + 1) f S :=
    (contDiffOn_succ_iff_fderiv_of_isOpen Metric.isOpen_ball).mpr
      ⟨fun x hx => (hf x hx).differentiableAt.differentiableWithinAt, by simp,
        (L.contDiff.comp_contDiffOn (by simpa only [zero_add] using hC₁)).congr
          (fun x hx => (hf x hx).fderiv)⟩
  exact hC₂

end C2Riemannian
