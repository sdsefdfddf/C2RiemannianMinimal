module

public import C2Riemannian.WeakProducts
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology

namespace C2Riemannian.StrongL2

variable {α E ι : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  {μ : Measure α} {l : Filter ι} [NeBot l] {F : ι → α → E} {f g : α → E}

/-- Two strong L² limits of the same representatives agree almost everywhere. -/
public theorem ae_eq (hf : StrongL2 l μ F f) (hg : StrongL2 l μ F g) : f =ᵐ[μ] g := by
  have hfg : Integrable (fun x => ‖f x - g x‖ ^ (2 : ℕ)) μ :=
    (hf.limit_mem.sub hg.limit_mem).integrable_norm_pow (p := 2) (by decide)
  have hle (i : ι) : (∫ x, ‖f x - g x‖ ^ (2 : ℕ) ∂μ) ≤
      2 * (∫ x, ‖F i x - f x‖ ^ (2 : ℕ) ∂μ) + 2 * ∫ x, ‖F i x - g x‖ ^ (2 : ℕ) ∂μ := by
    have hf' : Integrable (fun x => ‖F i x - f x‖ ^ (2 : ℕ)) μ :=
      ((hf.mem i).sub hf.limit_mem).integrable_norm_pow (p := 2) (by decide)
    have hg' : Integrable (fun x => ‖F i x - g x‖ ^ (2 : ℕ)) μ :=
      ((hg.mem i).sub hg.limit_mem).integrable_norm_pow (p := 2) (by decide)
    calc
      _ ≤ ∫ x, 2 * ‖F i x - f x‖ ^ (2 : ℕ) + 2 * ‖F i x - g x‖ ^ (2 : ℕ) ∂μ := by
        refine integral_mono hfg ((hf'.const_mul 2).add (hg'.const_mul 2)) ?_
        intro x
        have ht : ‖f x - g x‖ ≤ ‖F i x - f x‖ + ‖F i x - g x‖ := by
          have ht₀ := norm_add_le (f x - F i x) (F i x - g x)
          rw [sub_add_sub_cancel, norm_sub_rev (f x) (F i x)] at ht₀
          exact ht₀
        calc
          _ ≤ (‖F i x - f x‖ + ‖F i x - g x‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) ht 2
          _ ≤ _ := by nlinarith only [sq_nonneg (‖F i x - f x‖ - ‖F i x - g x‖)]
      _ = _ := by rw [integral_add (hf'.const_mul 2) (hg'.const_mul 2), integral_const_mul,
        integral_const_mul]
  have hlim := (hf.error.const_mul (2 : ℝ)).add (hg.error.const_mul (2 : ℝ))
  simp only [Real.rpow_two, mul_zero, add_zero] at hlim
  have hzero : (∫ x, ‖f x - g x‖ ^ (2 : ℕ) ∂μ) = 0 :=
    le_antisymm (ge_of_tendsto hlim (Eventually.of_forall hle))
      (integral_nonneg fun _ => sq_nonneg _)
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖f x - g x‖) hfg).mp hzero
  filter_upwards [hae] with x hx
  have hz : ‖f x - g x‖ = 0 := by
    have hm : ‖f x - g x‖ * ‖f x - g x‖ = 0 := by simpa only [pow_two, Pi.zero_apply] using hx
    exact (mul_eq_zero.mp hm).elim id id
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

end C2Riemannian.StrongL2
