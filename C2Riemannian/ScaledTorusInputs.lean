module

public import C2Riemannian.TorusDiskGeometry
public import C2Riemannian.UniversalTorusInputs
public import C2Riemannian.DisjointDiskJets
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology BoundedContinuousFunction

namespace C2Riemannian.TorusDiskGeometry

/-- The affine coordinate on the n-th disk. -/
@[expose] public noncomputable def scaledCoordinate (n : ℕ) (x : Plane) : Plane :=
  (radius n)⁻¹ • (x - center n)

public theorem scaledCoordinate_mem_unitDisk {n : ℕ} {x : Plane} :
    scaledCoordinate n x ∈ Metric.ball (0 : Plane) 1 ↔ x ∈ disk n := by
  change scaledCoordinate n x ∈ Metric.ball (0 : Plane) 1 ↔ dist x (center n) < radius n
  rw [Metric.mem_ball, dist_zero_right, scaledCoordinate, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr (radius_pos n).le),
    inv_mul_lt_one₀ (radius_pos n), dist_eq_norm]

/-- Dilation of the profile without the separate small amplitude. -/
@[expose] public noncomputable def scaledInput (F : UniversalTorusInputs) (n : ℕ) (x : Plane) : ℝ :=
  (radius n) ^ 2 * F.profile n (scaledCoordinate n x)

public theorem scaledInput_smooth (F : UniversalTorusInputs) (n : ℕ) :
    ContDiff ℝ ∞ (scaledInput F n) := by
  have hc : ContDiff ℝ ∞ (scaledCoordinate n) := by
    change ContDiff ℝ ∞ ((radius n)⁻¹ • (fun x : Plane => x - center n))
    have hId : ContDiff ℝ ∞ (fun x : Plane => x) := contDiff_id
    have hConst : ContDiff ℝ ∞ (fun _ : Plane => center n) := contDiff_const
    exact ContDiff.const_smul ((radius n)⁻¹) (hId.sub hConst)
  exact contDiff_const.mul ((F.smooth n).comp hc)

/-- The scaled profile is supported strictly inside its own disk. -/
public theorem scaled_bump_support (F : UniversalTorusInputs) (n : ℕ) :
    tsupport (scaledInput F n) ⊆ disk n := by
  have hCont : Continuous (scaledCoordinate n) := by
    change Continuous ((radius n)⁻¹ • (fun x : Plane => x - center n))
    exact (continuous_id.sub continuous_const).const_smul _
  have h₀ : Function.support (scaledInput F n) ⊆ scaledCoordinate n ⁻¹' tsupport (F.profile n) := by
    intro x hx
    by_contra h
    have hZ := image_eq_zero_of_notMem_tsupport
      (show scaledCoordinate n x ∉ tsupport (F.profile n) from h)
    exact hx (by simp [scaledInput, hZ])
  refine (closure_minimal h₀ ((isClosed_tsupport _).preimage hCont)).trans ?_
  intro x hx
  apply scaledCoordinate_mem_unitDisk.mp
  exact standardObstructionSquare_closure (subset_closure (F.supported n hx))

/-- Each k-th derivative scales by r⁽²⁻ᵏ⁾, expressed with natural powers. -/
public theorem scaledInput_iteratedFDeriv (F : UniversalTorusInputs) (n k : ℕ) (x : Plane) :
    iteratedFDeriv ℝ k (scaledInput F n) x =
      ((radius n) ^ 2 * ((radius n)⁻¹) ^ k) •
        iteratedFDeriv ℝ k (F.profile n) (scaledCoordinate n x) := by
  let L : Plane →L[ℝ] Plane := (radius n)⁻¹ • ContinuousLinearMap.id ℝ Plane
  change iteratedFDeriv ℝ k (fun y => ((radius n) ^ 2 • (F.profile n ∘ L)) (y - center n)) x = _
  rw [iteratedFDeriv_comp_sub,
    iteratedFDeriv_const_smul_apply (((F.smooth n).comp L.contDiff).contDiffAt.of_le (by simp)),
    L.iteratedFDeriv_comp_right (F.smooth n) _ (by simp)]
  ext v
  change (radius n) ^ 2 • iteratedFDeriv ℝ k (F.profile n) (scaledCoordinate n x)
      (fun j => (radius n)⁻¹ • v j) =
    ((radius n) ^ 2 * ((radius n)⁻¹) ^ k) • iteratedFDeriv ℝ k (F.profile n) (scaledCoordinate n x) v
  have h := (iteratedFDeriv ℝ k (F.profile n) (scaledCoordinate n x)).toMultilinearMap.map_smul_univ
    (fun _ => (radius n)⁻¹) v
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  change iteratedFDeriv ℝ k (F.profile n) (scaledCoordinate n x) (fun j => (radius n)⁻¹ • v j) =
    ((radius n)⁻¹) ^ k • iteratedFDeriv ℝ k (F.profile n) (scaledCoordinate n x) v at h
  rw [h, smul_smul]

public theorem scaledInput_second (F : UniversalTorusInputs) (n : ℕ) (x : Plane) :
    iteratedFDeriv ℝ 2 (scaledInput F n) x =
      iteratedFDeriv ℝ 2 (F.profile n) (scaledCoordinate n x) := by
  rw [scaledInput_iteratedFDeriv]
  have h : (radius n) ^ 2 * ((radius n)⁻¹) ^ 2 = 1 := by
    field_simp [ne_of_gt (radius_pos n)]
  rw [h, one_smul]

public theorem disk_subset_unitDisk (n : ℕ) : disk n ⊆ Metric.ball (0 : Plane) 1 :=
  Metric.ball_subset_closedBall.trans
    ((closedDisk_subset_smallBall n).trans (Metric.closedBall_subset_ball (by norm_num)))

/-- The full disk jet of one scaled profile satisfies the common bound two. -/
@[expose] public noncomputable def scaledUnitJet (F : UniversalTorusInputs) (n : ℕ) :
    C2ClosedDisk (0 : Plane) 1 :=
  closedUnitDiskJet ((scaledInput_smooth F n).of_le (by simp))

public theorem scaledUnitJet_bound (F : UniversalTorusInputs) (n : ℕ) :
    ‖scaledUnitJet F n‖ ≤ 2 := by
  apply support_unit_disk_hess_bound_to_C2
  · exact (scaled_bump_support F n).trans (disk_subset_unitDisk n)
  · intro x _
    rw [scaledInput_second]
    exact F.hessian_bound n _

public theorem scaledUnitJet_value (F : UniversalTorusInputs) (n : ℕ)
    (x : Metric.closedBall (0 : Plane) 1) : (scaledUnitJet F n).1.1 x = scaledInput F n x :=
  closedUnitDiskJet_value _ _

/-- The perturbation amplitude at positive index n+1. -/
@[expose] public noncomputable def amplitude (δ₀ : ℝ) (n : ℕ) : ℝ :=
  δ₀ / ((n : ℝ) + 1)

public theorem amplitude_tendsto (δ₀ : ℝ) : Tendsto (amplitude δ₀) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => δ₀ / ((n : ℝ) + 1)) atTop (𝓝 0)
  simpa only [div_eq_mul_inv, one_mul, mul_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto
      (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0)).const_mul δ₀

@[expose] public noncomputable def amplitudeJet (F : UniversalTorusInputs) (δ₀ : ℝ) (n : ℕ) :
    C2ClosedDisk (0 : Plane) 1 :=
  amplitude δ₀ n • scaledUnitJet F n

public theorem amplitudeJet_bound (F : UniversalTorusInputs) {δ₀ : ℝ} (hδ : 0 ≤ δ₀) (n : ℕ) :
    ‖amplitudeJet F δ₀ n‖ ≤ 2 * amplitude δ₀ n := by
  have hδn : 0 ≤ amplitude δ₀ n := div_nonneg hδ (by positivity)
  change ‖(amplitude δ₀ n : ℝ) • (scaledUnitJet F n).1‖ ≤ 2 * amplitude δ₀ n
  rw [norm_smul, Real.norm_of_nonneg hδn, mul_comm (2 : ℝ)]
  exact mul_le_mul_of_nonneg_left (scaledUnitJet_bound F n) hδn

private theorem hessianVector_zero : hessianVector 0 = 0 := by
  apply (WithLp.ext_iff 2).mpr
  funext ij
  simp [hessianVector]

public theorem pointJet_scaledUnitJet_zero_off_disk (F : UniversalTorusInputs) (n : ℕ)
    (x : Metric.closedBall (0 : Plane) 1) (hx : (x : Plane) ∉ disk n) :
    C2ClosedDisk.pointJet x (scaledUnitJet F n) = 0 := by
  have hSupp : (x : Plane) ∉ tsupport (scaledInput F n) :=
    fun h => hx (scaled_bump_support F n h)
  have hNear : scaledInput F n =ᶠ[𝓝 (x : Plane)] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hSupp
  have hD : fderiv ℝ (scaledInput F n) x = 0 := by simpa using hNear.fderiv_eq (𝕜 := ℝ)
  have hD₂ : fderiv ℝ (fderiv ℝ (scaledInput F n)) x = 0 := by
    simpa using (hNear.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  change (scaledInput F n x, gradientVector (fderiv ℝ (scaledInput F n) x),
    hessianVector (fderiv ℝ (fderiv ℝ (scaledInput F n)) x)) = 0
  rw [hNear.eq_of_nhds, hD, hD₂, map_zero, hessianVector_zero]
  rfl

public theorem pointJet_amplitudeJet_zero_off_disk (F : UniversalTorusInputs) (δ₀ : ℝ) (n : ℕ)
    (x : Metric.closedBall (0 : Plane) 1) (hx : (x : Plane) ∉ disk n) :
    C2ClosedDisk.pointJet x (amplitudeJet F δ₀ n) = 0 := by
  unfold amplitudeJet
  rw [map_smul, pointJet_scaledUnitJet_zero_off_disk F n x hx, smul_zero]

end C2Riemannian.TorusDiskGeometry
