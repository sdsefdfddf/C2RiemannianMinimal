module

public import C2Riemannian.WeakOrderTests
public import C2Riemannian.WeakNormRecovery

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions Topology

namespace C2Riemannian

/-- Test convergence of Hilbert-valued fields preserves their exact essential norm bound.
Here `d` is a countable dense family of directions in the unit sphere. -/
public theorem ae_norm_le_of_direction_test_limits {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {U : Opens Plane} {F : ℕ → Plane → E} {f : Plane → E}
    {K : ℝ} (hK : 0 ≤ K) (d : ℕ → E) (hd : Metric.sphere 0 1 ⊆ closure (Set.range d))
    (hd₁ : ∀ j, ‖d j‖ ≤ 1)
    (hF : ∀ n, IntegrableOn (F n) (U : Set Plane) volume)
    (hf : IntegrableOn f (U : Set Plane) volume)
    (hbound : ∀ n, ∀ᵐ x ∂volume.restrict (U : Set Plane), ‖F n x‖ ≤ K)
    (hlim : ∀ j (φ : 𝓓(U, ℝ)), Tendsto
      (fun n => ∫ x in ↑U, φ x * inner ℝ (F n x) (d j)) atTop
      (𝓝 (∫ x in ↑U, φ x * inner ℝ (f x) (d j)))) :
    ∀ᵐ x ∂volume.restrict (U : Set Plane), ‖f x‖ ≤ K := by
  let μ := volume.restrict (U : Set Plane)
  apply ae_norm_le_of_inner_dense_directions hK d hd
  intro j
  have hiInner : IntegrableOn (fun x => inner ℝ (f x) (d j)) (U : Set Plane) volume :=
    hf.inner_const (d j)
  have hl : LocallyIntegrableOn (fun x => inner ℝ (f x) (d j) - K) U volume :=
    hiInner.locallyIntegrableOn.sub ((locallyIntegrable_const K).locallyIntegrableOn _)
  have hnonpos : ∀ᵐ x ∂μ, inner ℝ (f x) (d j) - K ≤ 0 := by
    apply ae_nonpos_of_locallyIntegrable_nonneg_test_integrals hl
    intro φ hφ
    obtain ⟨B, hb⟩ := φ.hasCompactSupport.exists_bound_of_continuous φ.continuous
    have hi : Integrable (φ : Plane → ℝ) μ :=
      (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).integrableOn
    have hiK : Integrable (fun x => φ x * K) μ := hi.mul_const K
    have hiProd (p : Plane → E) (hp : Integrable p μ) :
        Integrable (fun x => φ x * inner ℝ (p x) (d j)) μ :=
      (hp.inner_const (d j)).bdd_mul φ.continuous.aestronglyMeasurable (ae_of_all μ hb)
    have hle (n : ℕ) : (∫ x in ↑U, φ x * inner ℝ (F n x) (d j)) ≤ ∫ x in ↑U, φ x * K := by
      apply integral_mono_ae (hiProd _ (hF n)) hiK
      filter_upwards [hbound n] with x hx
      apply mul_le_mul_of_nonneg_left _ (hφ x)
      exact (real_inner_le_norm _ _).trans
        ((mul_le_of_le_one_right (norm_nonneg _) (hd₁ j)).trans hx)
    have hlimle := le_of_tendsto (hlim j φ) (Eventually.of_forall hle)
    simp only [mul_sub]
    rw [integral_sub (hiProd _ hf) hiK]
    exact sub_nonpos.mpr hlimle
  exact hnonpos.mono fun _ hx => sub_nonpos.mp hx

end C2Riemannian
