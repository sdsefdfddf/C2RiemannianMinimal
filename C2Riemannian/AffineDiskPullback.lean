module

public import C2Riemannian.BoundedDiskNormalization
public import C2Riemannian.ClassicalJetBounds
public import C2Riemannian.ClassicalToWeakJet
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff ENNReal NNReal Topology

namespace C2Riemannian.WeakJet2

variable {m : ℕ}

@[expose] public def unitDisk : Opens Plane := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩

@[expose] public def diskDilation (a : Plane) (r : ℝ) (x : Plane) : Plane := a + r • x

public theorem diskDilation_mapsTo (a : Plane) {r : ℝ} (hr : 0 < r) :
    MapsTo (diskDilation a r) (unitDisk : Set Plane) (Metric.ball a r) := by
  intro x hx
  change x ∈ Metric.ball (0 : Plane) 1 at hx
  rw [Metric.mem_ball, dist_zero_right] at hx
  rw [Metric.mem_ball, dist_eq_norm, diskDilation, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le]
  simpa only [mul_one] using mul_lt_mul_of_pos_left hx hr

public theorem diskDilation_quasiMeasurePreserving (a : Plane) {r : ℝ} (hr : 0 < r) :
    QuasiMeasurePreserving (diskDilation a r) (volume.restrict (unitDisk : Set Plane))
      (volume.restrict (Metric.ball a r)) := by
  exact (((quasiMeasurePreserving_add_left volume a).comp
    (Measure.quasiMeasurePreserving_smul volume hr.ne')).restrict (diskDilation_mapsTo a hr))

private theorem hasFDerivAt_diskDilation (a : Plane) (r : ℝ) (x : Plane) :
    HasFDerivAt (diskDilation a r) (r • ContinuousLinearMap.id ℝ Plane) x :=
  ((ContinuousLinearMap.id ℝ Plane).hasFDerivAt.const_smul r).const_add a

/-- The weak Hessian rescales exactly under the disk dilation, after affine normalization. -/
public theorem exists_radial_pullback (a : Plane) (r c : ℝ) (hr : 0 < r) (K : ℝ≥0)
    (w : WeakJet2 m (⟨Metric.ball a r, Metric.isOpen_ball⟩ : Opens Plane))
    (hW : MemLp w.value ∞ (volume.restrict (Metric.ball a r)))
    (hP : MemLp w.gradient ∞ (volume.restrict (Metric.ball a r)))
    (hK : ∀ᵐ x ∂volume.restrict (Metric.ball a r), (w.hessian x).frobenius ≤ (K : ℝ)) :
    ∃ w' : WeakJet2 m unitDisk,
      MemLp w'.value ∞ (volume.restrict (unitDisk : Set Plane)) ∧
      MemLp w'.gradient ∞ (volume.restrict (unitDisk : Set Plane)) ∧
      ∀ᵐ x ∂volume.restrict (unitDisk : Set Plane),
        w'.hessian x = (w.hessian (diskDilation a r x)).scale (c * r ^ 2) := by
  obtain ⟨v, hvGrad, hvSecond, _, hvC, _, _, hvVal, hvP, hvLip⟩ :=
    w.exists_normalized_bounded_disk_weakJet a r hr K hW hP hK
  let D := diskDilation a r
  let V := fun x => c • v.value (D x)
  let P := fun x => (c * r) • v.gradient (D x)
  have hMaps := diskDilation_mapsTo a hr
  have hD := hasFDerivAt_diskDilation a r
  have hDLip : LipschitzWith ‖r‖₊ D := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (a + r • x) (a + r • y) ≤ ‖r‖ * dist x y
    rw [dist_add_left, dist_eq_norm, ← smul_sub, norm_smul, ← dist_eq_norm]
  have hpLip := (lipschitzOnWith_gradient_of_gradHS hvLip).comp hDLip.lipschitzOnWith hMaps
  let S : (Plane →L[ℝ] Target m) →L[ℝ] (Plane →L[ℝ] Target m) :=
    (c * r) • ContinuousLinearMap.id ℝ _
  have hpLip' : LipschitzOnWith (‖S‖₊ * (K * ‖r‖₊)) P (unitDisk : Set Plane) :=
    S.lipschitzWith.comp_lipschitzOnWith hpLip
  have hpLoc : LocallyLipschitzOn (unitDisk : Set Plane) P := fun _ _ =>
    ⟨_, _, self_mem_nhdsWithin, hpLip'⟩
  have hvD (x : Plane) (hx : x ∈ Metric.ball a r) : HasFDerivAt v.value (v.gradient x) x := by
    rw [hvGrad]
    exact ((hvC.differentiableOn (by decide) x hx).differentiableAt
      (Metric.isOpen_ball.mem_nhds hx)).hasFDerivAt
  have hVD (x : Plane) (hx : x ∈ (unitDisk : Set Plane)) : HasFDerivAt V (P x) x := by
    have h := ((hvD (D x) (hMaps hx)).comp x (hD x)).const_smul c
    have he : c • ((v.gradient (D x)).comp (r • ContinuousLinearMap.id ℝ Plane)) = P x := by
      apply ContinuousLinearMap.ext
      intro y
      change c • v.gradient (D x) (r • y) = (c * r) • v.gradient (D x) y
      rw [map_smul, smul_smul]
    rw [he] at h
    exact h
  have hCont : ContinuousOn V (unitDisk : Set Plane) :=
    fun x hx => (hVD x hx).continuousAt.continuousWithinAt
  have hPae : fderiv ℝ V =ᵐ[volume.restrict (unitDisk : Set Plane)] P :=
    (ae_restrict_mem unitDisk.isOpen.measurableSet).mono fun x hx => (hVD x hx).fderiv
  have hpInt : LocallyIntegrableOn P (unitDisk : Set Plane) volume :=
    hpLoc.continuousOn.locallyIntegrableOn unitDisk.isOpen.measurableSet
  have hWeakVal : TauCeti.HasWeakFDerivOn volume unitDisk V P :=
    (TauCeti.hasWeakFDerivOn_of_differentiableOn
      (hCont.locallyIntegrableOn unitDisk.isOpen.measurableSet)
      ((locallyIntegrableOn_congr hPae).mpr hpInt)
      (fun x hx => (hVD x hx).differentiableAt)).congr_ae_deriv hPae
  let w' : WeakJet2 m unitDisk :=
    ⟨V, P, fderiv ℝ P, hWeakVal, hasWeakFDerivOn_of_locallyLipschitz hpLoc⟩
  have hvGradLip : LocallyLipschitzOn (Metric.ball a r) v.gradient :=
    fun _ _ => ⟨K, _, self_mem_nhdsWithin, lipschitzOnWith_gradient_of_gradHS hvLip⟩
  have hvA := v.weak_gradient.ae_eq (hasWeakFDerivOn_of_locallyLipschitz
    (U := (⟨Metric.ball a r, Metric.isOpen_ball⟩ : Opens Plane)) hvGradLip)
  have hvdiff := ae_differentiableAt_of_locallyLipschitzOn
    (U := (⟨Metric.ball a r, Metric.isOpen_ball⟩ : Opens Plane)) hvGradLip
  have hDμ := diskDilation_quasiMeasurePreserving a hr
  refine ⟨w', ?_, ?_, ?_⟩
  · have hVI : LocallyIntegrableOn V (unitDisk : Set Plane) volume :=
      hCont.locallyIntegrableOn unitDisk.isOpen.measurableSet
    have hm := hVI.aestronglyMeasurable
    apply memLp_top_of_bound hm (‖c‖ * ((K : ℝ) * r ^ 2 / 2))
    filter_upwards [ae_restrict_mem unitDisk.isOpen.measurableSet] with x hx
    change ‖c • v.value (D x)‖ ≤ _
    rw [norm_smul]
    have hd := le_of_lt (Metric.mem_ball.mp (hMaps hx))
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg c)
    exact (hvVal (D x) (hMaps hx)).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ dist_nonneg hd 2) K.coe_nonneg) (by norm_num))
  · have hm := hpInt.aestronglyMeasurable
    apply memLp_top_of_bound hm (‖c * r‖ * (K : ℝ) * r)
    filter_upwards [ae_restrict_mem unitDisk.isOpen.measurableSet] with x hx
    change ‖(c * r) • v.gradient (D x)‖ ≤ _
    rw [norm_smul, mul_assoc]
    have hg := (opNorm_le_gradHS (v.gradient (D x))).trans (hvP (D x) (hMaps hx))
    exact mul_le_mul_of_nonneg_left
      (hg.trans (mul_le_mul_of_nonneg_left (le_of_lt (Metric.mem_ball.mp (hMaps hx))) K.coe_nonneg))
      (norm_nonneg _)
  · filter_upwards [hDμ.ae_eq_comp hvA, hDμ.ae hvdiff] with x hx hy
    have hpd := (((hy.hasFDerivAt).comp x (hD x)).const_smul (c * r)).fderiv
    have hpd' : fderiv ℝ P x =
        (c * r) • ((fderiv ℝ v.gradient (D x)).comp (r • ContinuousLinearMap.id ℝ Plane)) := hpd
    change v.second (D x) = fderiv ℝ v.gradient (D x) at hx
    rw [← hx, hvSecond] at hpd'
    unfold WeakJet2.hessian Hess3.scale
    change Hess3.mk ((fderiv ℝ P x) _ _) ((fderiv ℝ P x) _ _) ((fderiv ℝ P x) _ _) = _
    rw [hpd']
    have hc : c * r * r = c * r ^ 2 := by ring
    congr 1 <;> simp only [smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_smul, hc, D]

end C2Riemannian.WeakJet2
