module

public import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false

open Filter Set MeasureTheory

namespace C2Riemannian

/-- Testing a field against a countable dense set of unit directions recovers
the original pointwise norm bound on one common full-measure set. -/
public theorem ae_norm_le_of_inner_dense_directions {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure α} {f : α → E}
    {K : ℝ} (hK : 0 ≤ K) (d : ℕ → E) (hd : Metric.sphere 0 1 ⊆ closure (Set.range d))
    (h : ∀ n, ∀ᵐ x ∂μ, inner ℝ (f x) (d n) ≤ K) :
    ∀ᵐ x ∂μ, ‖f x‖ ≤ K := by
  filter_upwards [ae_all_iff.mpr h] with x hx
  by_cases hz : f x = 0
  · simpa only [hz, norm_zero] using hK
  have hn : 0 < ‖f x‖ := norm_pos_iff.mpr hz
  let u : E := (‖f x‖⁻¹ : ℝ) • f x
  have hu : u ∈ Metric.sphere 0 1 := by
    dsimp only [u]
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  have hset : closure (Set.range d) ⊆ {v | inner ℝ (f x) v ≤ K} := by
    apply closure_minimal
    · rintro _ ⟨n, rfl⟩
      exact hx n
    · exact isClosed_le (continuous_const.inner continuous_id) continuous_const
  have hv : inner ℝ (f x) u ≤ K := hset (hd hu)
  have he : inner ℝ (f x) u = ‖f x‖ := by
    dsimp only [u]
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq, pow_two,
      ← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul]
  simpa only [he] using hv

end C2Riemannian
