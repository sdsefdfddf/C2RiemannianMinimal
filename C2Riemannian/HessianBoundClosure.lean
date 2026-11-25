module

public import C2Riemannian.HessianFrobenius
public import C2Riemannian.HessianTestLimit
public import C2Riemannian.ExactBoundTestLimit
import Mathlib.Tactic.Ring

set_option autoImplicit false

open MeasureTheory Set Filter TopologicalSpace
open scoped Distributions Topology

namespace C2Riemannian.WeakJet2

variable {m : ℕ} {U : Opens Plane}

private theorem weighted_second_integrable (w : WeakJet2 m U) (a b : Plane) (φ : 𝓓(U, ℝ)) :
    Integrable (fun x => φ x • w.second x b a) (volume.restrict (U : Set Plane)) :=
  (TauCeti.integrable_smul_of_locallyIntegrableOn
    (w.weak_component b a).locallyIntegrableOn_deriv φ).integrableOn

private theorem inner_second_test (w : WeakJet2 m U) (a b : Plane) (e : Target m) (φ : 𝓓(U, ℝ)) :
    (∫ x in ↑U, φ x * inner ℝ (w.second x b a) e) =
      inner ℝ (∫ x in ↑U, φ x • w.second x b a) e := by
  calc
    _ = ∫ x in ↑U, inner ℝ e (φ x • w.second x b a) := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        change φ x * inner ℝ (w.second x b a) e = inner ℝ e (φ x • w.second x b a)
        rw [real_inner_smul_right, real_inner_comm (w.second x b a) e]
    _ = _ := (integral_inner (𝕜 := ℝ) (weighted_second_integrable w a b φ) e).trans
      (real_inner_comm _ _)

public theorem hessian_coordinates_test (w : WeakJet2 m U) (e : HessSpace m) (φ : 𝓓(U, ℝ)) :
    (∫ x in ↑U, φ x * inner ℝ (w.hessian x).coordinates e) =
      inner ℝ (∫ x in ↑U, φ x • w.second x (EuclideanSpace.single 0 1)
        (EuclideanSpace.single 0 1)) e.fst +
      (Real.sqrt 2 * inner ℝ (∫ x in ↑U, φ x • w.second x (EuclideanSpace.single 1 1)
        (EuclideanSpace.single 0 1)) e.snd.fst +
      inner ℝ (∫ x in ↑U, φ x • w.second x (EuclideanSpace.single 1 1)
        (EuclideanSpace.single 1 1)) e.snd.snd) := by
  let ex : Plane := EuclideanSpace.single 0 1
  let ey : Plane := EuclideanSpace.single 1 1
  have hint (a b : Plane) (v : Target m) :
      Integrable (fun x => φ x * inner ℝ (w.second x b a) v) (volume.restrict (U : Set Plane)) := by
    simpa only [real_inner_smul_left] using (weighted_second_integrable w a b φ).inner_const (𝕜 := ℝ) v
  simp only [Hess3.inner_coordinates, hessian, mul_add]
  change (∫ x in ↑U, φ x * inner ℝ (w.second x ex ex) e.fst +
    (φ x * (Real.sqrt 2 * inner ℝ (w.second x ey ex) e.snd.fst) +
      φ x * inner ℝ (w.second x ey ey) e.snd.snd)) = _
  have hxy : Integrable (fun x => φ x * (Real.sqrt 2 * inner ℝ (w.second x ey ex) e.snd.fst))
      (volume.restrict (U : Set Plane)) := by
    simpa only [mul_left_comm] using (hint ex ey e.snd.fst).const_mul (Real.sqrt 2)
  have hadd :
      (∫ x in ↑U, φ x * inner ℝ (w.second x ex ex) e.fst +
        (φ x * (Real.sqrt 2 * inner ℝ (w.second x ey ex) e.snd.fst) +
          φ x * inner ℝ (w.second x ey ey) e.snd.snd)) =
      (∫ x in ↑U, φ x * inner ℝ (w.second x ex ex) e.fst) +
      ((∫ x in ↑U, φ x * (Real.sqrt 2 * inner ℝ (w.second x ey ex) e.snd.fst)) +
        ∫ x in ↑U, φ x * inner ℝ (w.second x ey ey) e.snd.snd) := by
    have h₁ := integral_add (hint ex ex e.fst) (hxy.add (hint ey ey e.snd.snd))
    have h₂ := integral_add hxy (hint ey ey e.snd.snd)
    exact h₁.trans (congrArg (fun r : ℝ => (∫ x in ↑U, φ x * inner ℝ (w.second x ex ex) e.fst) + r) h₂)
  rw [hadd]
  have hmul : (∫ x in ↑U, φ x * (Real.sqrt 2 * inner ℝ (w.second x ey ex) e.snd.fst)) =
      Real.sqrt 2 * (∫ x in ↑U, φ x * inner ℝ (w.second x ey ex) e.snd.fst) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun _ => mul_left_comm _ _ _
  rw [hmul, inner_second_test w ex ex e.fst φ, inner_second_test w ex ey e.snd.fst φ,
    inner_second_test w ey ey e.snd.snd φ]

public theorem tendsto_hessian_coordinates_test {W : ℕ → WeakJet2 m U} {w : WeakJet2 m U}
    (hcol : ∀ (v u : Plane) (φ : 𝓓(U, ℝ)), Tendsto
      (fun n => ∫ x in ↑U, φ x • (W n).second x v u) atTop
      (𝓝 (∫ x in ↑U, φ x • w.second x v u))) (e : HessSpace m) (φ : 𝓓(U, ℝ)) :
    Tendsto (fun n => ∫ x in ↑U, φ x * inner ℝ ((W n).hessian x).coordinates e) atTop
      (𝓝 (∫ x in ↑U, φ x * inner ℝ (w.hessian x).coordinates e)) := by
  let ex : Plane := EuclideanSpace.single 0 1
  let ey : Plane := EuclideanSpace.single 1 1
  have hinner (v u : Plane) (c : Target m) : Tendsto
      (fun n => inner ℝ (∫ x in ↑U, φ x • (W n).second x v u) c) atTop
      (𝓝 (inner ℝ (∫ x in ↑U, φ x • w.second x v u) c)) :=
    (hcol v u φ).inner tendsto_const_nhds
  simp only [hessian_coordinates_test]
  exact (hinner ex ex e.fst).add (((hinner ey ex e.snd.fst).const_mul (Real.sqrt 2)).add
    (hinner ey ey e.snd.snd))

/-- The same Frobenius bound holds for the weak Hessian of a same-domain limit
whose Hessian columns converge distributionally. -/
public theorem hessian_bound_of_test_limits {W : ℕ → WeakJet2 m U} {w : WeakJet2 m U}
    (hW : ∀ n, IntegrableOn (fun x => ((W n).hessian x).coordinates) (U : Set Plane) volume)
    (hw : IntegrableOn (fun x => (w.hessian x).coordinates) (U : Set Plane) volume)
    {K : ℝ} (hK : 0 ≤ K) (d : ℕ → HessSpace m)
    (hd : Metric.sphere 0 1 ⊆ closure (Set.range d)) (hd₁ : ∀ j, ‖d j‖ ≤ 1)
    (hb : ∀ n, ∀ᵐ x ∂volume.restrict (U : Set Plane), ((W n).hessian x).frobenius ≤ K)
    (hcol : ∀ (v u : Plane) (φ : 𝓓(U, ℝ)), Tendsto
      (fun n => ∫ x in ↑U, φ x • (W n).second x v u) atTop
      (𝓝 (∫ x in ↑U, φ x • w.second x v u))) :
    ∀ᵐ x ∂volume.restrict (U : Set Plane), (w.hessian x).frobenius ≤ K := by
  have hh := ae_norm_le_of_direction_test_limits hK d hd hd₁ hW hw
    (fun n => (hb n).mono fun x hx => ((W n).hessian x).norm_coordinates.trans_le hx)
    (fun j φ => tendsto_hessian_coordinates_test hcol (d j) φ)
  exact hh.mono fun x hx => (w.hessian x).norm_coordinates ▸ hx

private theorem exists_dense_hessian_directions {m : ℕ} (hm : 0 < m) :
    ∃ d : ℕ → HessSpace m, Metric.sphere 0 1 ⊆ closure (Set.range d) ∧ ∀ j, ‖d j‖ ≤ 1 := by
  let A : Hess3 m := ⟨EuclideanSpace.single ⟨0, hm⟩ 1, 0, 0⟩
  have hA : A.coordinates ∈ Metric.sphere (0 : HessSpace m) 1 := by
    rw [Metric.mem_sphere, dist_zero_right, A.norm_coordinates, Hess3.frobenius, Hess3.frobeniusSq]
    simp [A, EuclideanSpace.single, PiLp.norm_single]
  let _ : Nonempty (Metric.sphere (0 : HessSpace m) 1) := ⟨⟨A.coordinates, hA⟩⟩
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq (Metric.sphere (0 : HessSpace m) 1)
  refine ⟨fun j => (d j).val, ?_, ?_⟩
  · intro e he
    have he' : (⟨e, he⟩ : Metric.sphere (0 : HessSpace m) 1) ∈ closure (Set.range d) := hd _
    refine map_mem_closure continuous_subtype_val he' ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨n, rfl⟩
  · intro j
    have h := (d j).property
    rw [Metric.mem_sphere, dist_zero_right] at h
    exact h.le

public theorem hessian_bound_of_test_limits_pos_dimension (hm : 0 < m)
    {W : ℕ → WeakJet2 m U} {w : WeakJet2 m U}
    (hW : ∀ n, IntegrableOn (fun x => ((W n).hessian x).coordinates) (U : Set Plane) volume)
    (hw : IntegrableOn (fun x => (w.hessian x).coordinates) (U : Set Plane) volume) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ n, ∀ᵐ x ∂volume.restrict (U : Set Plane), ((W n).hessian x).frobenius ≤ K)
    (hcol : ∀ (v u : Plane) (φ : 𝓓(U, ℝ)), Tendsto
      (fun n => ∫ x in ↑U, φ x • (W n).second x v u) atTop
      (𝓝 (∫ x in ↑U, φ x • w.second x v u))) :
    ∀ᵐ x ∂volume.restrict (U : Set Plane), (w.hessian x).frobenius ≤ K := by
  obtain ⟨d, hd, hd'⟩ := exists_dense_hessian_directions hm
  exact hessian_bound_of_test_limits hW hw hK d hd hd' hb hcol

/-- Compact-uniform gradient convergence gives all tested weak second-column limits. -/
public theorem second_column_limits_of_gradient {W : ℕ → WeakJet2 m U} {w : WeakJet2 m U}
    (P : ℝ) (hP : ∀ n x, x ∈ (U : Set Plane) → ‖(W n).gradient x‖ ≤ P)
    (hUniform : ∀ s : Set Plane, s ⊆ (U : Set Plane) → IsCompact s →
      TendstoUniformlyOn (fun n => (W n).gradient) w.gradient atTop s) :
    ∀ (v u : Plane) (φ : 𝓓(U, ℝ)), Tendsto
      (fun n => ∫ x in ↑U, φ x • (W n).second x v u) atTop
      (𝓝 (∫ x in ↑U, φ x • w.second x v u)) := by
  intro v u φ
  let ψ : 𝓓(U, ℝ) := TestFunction.lineDerivCLM ℝ v φ
  let E := ContinuousLinearMap.apply ℝ (Target m) u
  refine tendsto_second_column_test v u φ (P * ‖u‖) ?_ ?_
  · intro n x hx
    exact ((W n).gradient x).le_opNorm u |>.trans
      (mul_le_mul_of_nonneg_right (hP n x (ψ.tsupport_subset hx)) (norm_nonneg _))
  · exact E.uniformContinuous.comp_tendstoUniformlyOn
      (hUniform _ ψ.tsupport_subset ψ.hasCompactSupport)

/-- An essentially bounded Hessian has integrable weighted coordinates on a disk. -/
public theorem hessian_coordinates_integrable (w : WeakJet2 m U)
    [IsFiniteMeasure (volume.restrict (U : Set Plane))]
    (hB : AEStronglyMeasurable w.second (volume.restrict (U : Set Plane))) {K : ℝ}
    (hb : ∀ᵐ x ∂volume.restrict (U : Set Plane), (w.hessian x).frobenius ≤ K) :
    IntegrableOn (fun x => (w.hessian x).coordinates) (U : Set Plane) volume := by
  have hmeas : AEStronglyMeasurable (fun x => (w.hessian x).coordinates)
      (volume.restrict (U : Set Plane)) := by
    simpa only [Function.comp_def, hessianColumns_apply, hessian] using
      (hessianColumns (m := m)).continuous.comp_aestronglyMeasurable hB
  exact memLp_one_iff_integrable.mp (MemLp.of_bound hmeas K
    (hb.mono fun x hx => (w.hessian x).norm_coordinates.trans_le hx))

end C2Riemannian.WeakJet2
