module

public import C2Riemannian.TorusPeriodization
public import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped ContDiff Topology

namespace C2Riemannian.TorusDiskGeometry

/-- The flat two-torus, as a product of two additive circles. -/
public abbrev FlatTorus := Fin 2 → AddCircle (1 : ℝ)

/-- Projection from the Euclidean covering plane to the torus. -/
@[expose] public noncomputable def torusProjection (x : Plane) : FlatTorus :=
  fun i => (x i : AddCircle (1 : ℝ))

public theorem torusProjection_openQuotient : IsOpenQuotientMap torusProjection := by
  let e := PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)
  let f (_ : Fin 2) : ℝ → AddCircle (1 : ℝ) := QuotientAddGroup.mk
  have h : IsOpenQuotientMap (Pi.map f) :=
    IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)
  exact h.comp e.isOpenQuotientMap

public theorem torusProjection_sub (x y : Plane) :
    torusProjection (x - y) = torusProjection x - torusProjection y := by
  funext i
  exact AddCircle.coe_sub 1 (x i) (y i)

public theorem torusProjection_eq_iff {x y : Plane} :
    torusProjection x = torusProjection y ↔ ∃ k : Fin 2 → ℤ, x = y + lattice k := by
  constructor
  · intro h
    have hI (i : Fin 2) : ∃ z : ℤ, (z : ℝ) = x i - y i := by
      have hi := congrFun h i
      have hp : ((x i - y i : ℝ) : AddCircle (1 : ℝ)) = 0 := by
        change (x i : AddCircle (1 : ℝ)) = (y i : AddCircle (1 : ℝ)) at hi
        rw [AddCircle.coe_sub, hi, sub_self]
      obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff 1).mp hp
      exact ⟨z, by simpa [zsmul_eq_mul] using hz⟩
    choose k hk using hI
    refine ⟨k, (WithLp.ext_iff 2).mpr ?_⟩
    funext i
    change x i = y i + (k i : ℝ)
    rw [hk]
    ring
  · rintro ⟨k, rfl⟩
    funext i
    change ((y i + (k i : ℝ) : ℝ) : AddCircle (1 : ℝ)) = (y i : AddCircle (1 : ℝ))
    have hi : ((k i : ℝ) : AddCircle (1 : ℝ)) = 0 :=
      (AddCircle.coe_eq_zero_iff 1).mpr ⟨k i, by simp [zsmul_eq_mul]⟩
    rw [AddCircle.coe_add, hi, add_zero]

/-- The quotient projection restricted to any quarter-radius disk is an
open embedding, giving flat coordinate charts. -/
public theorem flatPatch_openEmbedding (a : Plane) :
    Topology.IsOpenEmbedding (fun x : Metric.ball a (1 / 4) => torusProjection x.1) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact torusProjection_openQuotient.continuous.comp continuous_subtype_val
  · intro x y h
    obtain ⟨k, hk⟩ := torusProjection_eq_iff.mp h
    by_cases h0 : k = 0
    · apply Subtype.ext
      simpa only [h0, lattice_zero, add_zero] using hk
    · exfalso
      have hL := lattice_separation h0
      rw [lattice_zero, dist_zero_right] at hL
      have hT := dist_triangle (x : Plane) a y
      rw [dist_comm a y] at hT
      have hx := Metric.mem_ball.mp x.property
      have hy := Metric.mem_ball.mp y.property
      have hnorm : dist (x : Plane) y = ‖lattice k‖ := by
        rw [hk, dist_eq_norm, add_sub_cancel_left]
      linarith only [hL, hT, hx, hy, hnorm]
  · exact torusProjection_openQuotient.isOpenMap.comp Metric.isOpen_ball.isOpenEmbedding_subtypeVal.isOpenMap

/-- On overlaps, the two flat coordinates differ locally by one integer
translation, so the same parallel frame defines the metric in every chart. -/
public theorem flatPatch_transition_germ {a b x y : Plane}
    (hx : x ∈ Metric.ball a (1 / 4)) (hy : y ∈ Metric.ball b (1 / 4))
    (hproj : torusProjection x = torusProjection y) :
    ∃ k : Fin 2 → ℤ, x - lattice k = y ∧
      ∀ᶠ z in 𝓝 x, z ∈ Metric.ball a (1 / 4) ∧
        z - lattice k ∈ Metric.ball b (1 / 4) ∧ torusProjection (z - lattice k) = torusProjection z := by
  obtain ⟨k, hk⟩ := torusProjection_eq_iff.mp hproj
  have hxy : x - lattice k = y := by rw [hk, add_sub_cancel_right]
  refine ⟨k, hxy, ?_⟩
  have hMap : Continuous (fun z : Plane => z - lattice k) := continuous_id.sub continuous_const
  have hN : ∀ᶠ z in 𝓝 x, z - lattice k ∈ Metric.ball b (1 / 4) := by
    apply hMap.continuousAt.preimage_mem_nhds
    rw [hxy]
    exact Metric.isOpen_ball.mem_nhds hy
  filter_upwards [Metric.isOpen_ball.mem_nhds hx, hN] with z hz₁ hz₂
  refine ⟨hz₁, hz₂, ?_⟩
  symm
  exact torusProjection_eq_iff.mpr ⟨k, (sub_add_cancel z (lattice k)).symm⟩

@[expose] public noncomputable def torusRepresentative (q : FlatTorus) : Plane :=
  Classical.choose (torusProjection_openQuotient.surjective q)

private theorem projection_representative (q : FlatTorus) :
    torusProjection (torusRepresentative q) = q :=
  Classical.choose_spec (torusProjection_openQuotient.surjective q)

/-- The descended scalar coefficient, translated to have its distinguished
point at the specified torus point. -/
@[expose] public noncomputable def torusCoefficient (f : Plane → ℝ) (o q : FlatTorus) : ℝ :=
  periodize f (torusRepresentative (q - o))

public theorem torusCoefficient_in_flat_coordinates (f : Plane → ℝ) (x a : Plane) :
    torusCoefficient f (torusProjection a) (torusProjection x) = periodize f (x - a) := by
  unfold torusCoefficient
  rw [← torusProjection_sub]
  obtain ⟨k, hk⟩ := torusProjection_eq_iff.mp (projection_representative (torusProjection (x - a)))
  rw [hk, periodize_add_lattice]

public theorem torusCoefficient_contDiff_two_lift {f : Plane → ℝ} (hf : ContDiff ℝ 2 f)
    (hSupp : tsupport f ⊆ Metric.closedBall (0 : Plane) (9 / 64)) (o : FlatTorus) :
    ContDiff ℝ 2 (torusCoefficient f o ∘ torusProjection) := by
  obtain ⟨a, rfl⟩ := torusProjection_openQuotient.surjective o
  have heq : torusCoefficient f (torusProjection a) ∘ torusProjection =
      fun x => periodize f (x - a) := funext fun x => torusCoefficient_in_flat_coordinates f x a
  rw [heq]
  exact (contDiff_two_periodize hf hSupp).comp (contDiff_id.sub contDiff_const)

public theorem torusCoefficient_continuous {f : Plane → ℝ} (hf : ContDiff ℝ 2 f)
    (hSupp : tsupport f ⊆ Metric.closedBall (0 : Plane) (9 / 64)) (o : FlatTorus) :
    Continuous (torusCoefficient f o) :=
  torusProjection_openQuotient.continuous_comp_iff.mp (torusCoefficient_contDiff_two_lift hf hSupp o).continuous

/-- The lift is smooth away from the fibers of the distinguished torus point. -/
public theorem torusCoefficient_smooth_off_fiber {f : Plane → ℝ}
    (hf : ContDiffOn ℝ ∞ f ({0}ᶜ : Set Plane))
    (hSupp : tsupport f ⊆ Metric.closedBall (0 : Plane) (9 / 64)) (o : FlatTorus) :
    ContDiffOn ℝ ∞ (torusCoefficient f o ∘ torusProjection) {x | torusProjection x ≠ o} := by
  obtain ⟨a, rfl⟩ := torusProjection_openQuotient.surjective o
  have heq : torusCoefficient f (torusProjection a) ∘ torusProjection =
      fun x => periodize f (x - a) := funext fun x => torusCoefficient_in_flat_coordinates f x a
  rw [heq]
  apply (smooth_periodize_off_lattice hf hSupp).comp (contDiff_id.sub contDiff_const).contDiffOn
  intro x hx
  rintro ⟨k, hk⟩
  apply hx
  exact torusProjection_eq_iff.mpr ⟨k, (sub_eq_iff_eq_add.mp hk.symm).trans (add_comm _ _)⟩

/-- In coordinates centered at the distinguished point the descended
coefficient has the original profile as its germ. -/
public theorem torusCoefficient_origin_germ (f : Plane → ℝ) (a : Plane) :
    (fun x => torusCoefficient f (torusProjection a) (torusProjection (a + x))) =ᶠ[𝓝 0] f := by
  filter_upwards [periodize_nhds_origin f] with x hx
  rw [torusCoefficient_in_flat_coordinates, add_sub_cancel_left]
  exact hx

/-- In the common flat frame the metric perturbation has only its first
diagonal component, so its derivative bounds are the scalar lift bounds. -/
public theorem torusCoefficient_lift_bounds {f : Plane → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hSupp : tsupport f ⊆ Metric.closedBall (0 : Plane) (9 / 64))
    (h₀ : ∀ x, ‖f x‖ ≤ C)
    (h₁ : ∀ x, ‖fderiv ℝ f x‖ ≤ C)
    (h₂ : ∀ x, tensorHS (iteratedFDeriv ℝ 2 f x) ≤ C)
    (o : FlatTorus) (x : Plane) :
    ‖torusCoefficient f o (torusProjection x)‖ ≤ C ∧
      ‖fderiv ℝ (torusCoefficient f o ∘ torusProjection) x‖ ≤ C ∧
      tensorHS (iteratedFDeriv ℝ 2 (torusCoefficient f o ∘ torusProjection) x) ≤ C := by
  obtain ⟨a, rfl⟩ := torusProjection_openQuotient.surjective o
  have heq : torusCoefficient f (torusProjection a) ∘ torusProjection =
      fun x => periodize f (x - a) := funext fun x => torusCoefficient_in_flat_coordinates f x a
  rw [torusCoefficient_in_flat_coordinates, heq, fderiv_comp_sub, iteratedFDeriv_comp_sub]
  exact periodize_bounds hC hSupp h₀ h₁ h₂ _
/-- The metric in the parallel frame of the flat torus. -/
@[expose] public noncomputable def torusMetricForm (f : Plane → ℝ) (o q : FlatTorus)
    (X Y : Plane) : ℝ :=
  (1 + torusCoefficient f o q) * X 0 * Y 0 + X 1 * Y 1

public theorem torusMetricForm_positive {f : Plane → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hsmall : C ≤ 1 / 4) (hf : ∀ x, ‖f x‖ ≤ C) (o q : FlatTorus)
    {X : Plane} (hX : X ≠ 0) : 0 < torusMetricForm f o q X X := by
  have hV := norm_periodize_le hC hf (torusRepresentative (q - o))
  change ‖torusCoefficient f o q‖ ≤ C at hV
  rw [Real.norm_eq_abs] at hV
  have hCoeff : 0 < 1 + torusCoefficient f o q := by
    linarith only [(abs_le.mp hV).1, hsmall]
  have hEntry : X 0 ≠ 0 ∨ X 1 ≠ 0 := by
    by_contra! h
    apply hX
    apply (WithLp.ext_iff 2).mpr
    funext i
    fin_cases i
    · exact h.1
    · exact h.2
  unfold torusMetricForm
  rcases hEntry with h | h
  · have hp := mul_pos hCoeff (sq_pos_of_ne_zero h)
    nlinarith only [hp, sq_nonneg (X 1)]
  · have hp := sq_pos_of_ne_zero h
    have h₀ := mul_nonneg hCoeff.le (sq_nonneg (X 0))
    nlinarith only [hp, h₀]

/-- The metric is uniformly bounded below by three quarters of the flat metric. -/
public theorem torusMetricForm_lower {f : Plane → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hsmall : C ≤ 1 / 4) (hf : ∀ x, ‖f x‖ ≤ C) (o q : FlatTorus) (X : Plane) :
    (3 / 4 : ℝ) * ‖X‖ ^ 2 ≤ torusMetricForm f o q X X := by
  have hV := norm_periodize_le hC hf (torusRepresentative (q - o))
  change ‖torusCoefficient f o q‖ ≤ C at hV
  rw [Real.norm_eq_abs] at hV
  have hc : (3 / 4 : ℝ) ≤ 1 + torusCoefficient f o q := by
    linarith only [(abs_le.mp hV).1, hsmall]
  have hSq := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ) X
  rw [Fin.sum_univ_two] at hSq
  simp only [Real.norm_eq_abs, sq_abs] at hSq
  have hp := mul_nonneg (sub_nonneg.mpr hc) (sq_nonneg (X 0))
  unfold torusMetricForm
  nlinarith only [hp, hSq, sq_nonneg (X 1)]

end C2Riemannian.TorusDiskGeometry
