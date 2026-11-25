module

public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology ENNReal

namespace C2Riemannian

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure α}

public theorem integrable_weak_inner {f g : α → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => inner ℝ (f x) (g x)) μ := by
  refine (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]

omit [InnerProductSpace ℝ E] in
private theorem integrable_norm_product {f g : α → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => ‖f x‖ * ‖g x‖) μ := by
  simpa [RCLike.inner_apply, mul_comm] using integrable_weak_inner hf.norm hg.norm

/-- The Cauchy–Schwarz bound for the L¹ norm of a pointwise inner product. -/
public theorem integral_norm_inner_le {f g : α → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, ‖inner ℝ (f x) (g x)‖ ∂μ) ≤
      (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
        (∫ x, ‖g x‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
  calc
    _ ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂μ :=
      integral_mono (integrable_weak_inner hf hg).norm (integrable_norm_product hf hg)
        (fun x => norm_inner_le_norm _ _)
    _ ≤ _ := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
      (by simpa using hf) (by simpa using hg)

public theorem integral_norm_inner_sub_le {f' g' f g : α → E}
    (hf' : MemLp f' 2 μ) (hg' : MemLp g' 2 μ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, ‖inner ℝ (f' x) (g' x) - inner ℝ (f x) (g x)‖ ∂μ) ≤
      (∫ x, ‖f' x - f x‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
          (∫ x, ‖g' x‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) +
        (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
          (∫ x, ‖g' x - g x‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
  have h₁ := (integrable_weak_inner (hf'.sub hf) hg').norm
  have h₂ := (integrable_weak_inner hf (hg'.sub hg)).norm
  refine (integral_mono ((integrable_weak_inner hf' hg').sub (integrable_weak_inner hf hg)).norm
    (h₁.add h₂) ?_).trans ?_
  · intro x
    simp only [Pi.sub_apply, Pi.add_apply]
    have hsplit : inner ℝ (f' x) (g' x) - inner ℝ (f x) (g x) =
        inner ℝ (f' x - f x) (g' x) + inner ℝ (f x) (g' x - g x) := by
      rw [inner_sub_left, inner_sub_right]
      abel
    rw [hsplit]
    exact norm_add_le _ _
  · simp only [Pi.add_apply]
    rw [integral_add h₁ h₂]
    exact add_le_add (integral_norm_inner_le (hf'.sub hf) hg') (integral_norm_inner_le hf (hg'.sub hg))

public theorem tendsto_integral_norm_inner_sub {ι : Type*} {l : Filter ι}
    {F G : ι → α → E} {f g : α → E}
    (hF : ∀ i, MemLp (F i) 2 μ) (hG : ∀ i, MemLp (G i) 2 μ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hFlim : Tendsto (fun i => ∫ x, ‖F i x - f x‖ ^ (2 : ℝ) ∂μ) l (𝓝 0))
    (hGlim : Tendsto (fun i => ∫ x, ‖G i x - g x‖ ^ (2 : ℝ) ∂μ) l (𝓝 0))
    (C : ℝ) (hC : ∀ᶠ i in l,
      (∫ x, ‖G i x‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) ≤ C) :
    Tendsto (fun i => ∫ x, ‖inner ℝ (F i x) (G i x) - inner ℝ (f x) (g x)‖ ∂μ) l (𝓝 0) := by
  have hpow : ContinuousAt (fun x : ℝ => x ^ (1 / 2 : ℝ)) 0 :=
    Real.continuousAt_rpow_const _ _ (.inr (by norm_num))
  have hF' := hpow.tendsto.comp hFlim
  have hG' := hpow.tendsto.comp hGlim
  have hz : (0 : ℝ) ^ (1 / 2 : ℝ) = 0 := by norm_num
  rw [hz] at hF' hG'
  have hupper := (hF'.mul_const C).add (hG'.const_mul
    ((∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)))
  simp only [zero_mul, mul_zero, add_zero] at hupper
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · exact Eventually.of_forall fun _ => integral_nonneg fun _ => norm_nonneg _
  · filter_upwards [hC] with i hi
    refine (integral_norm_inner_sub_le (hF i) (hG i) hf hg).trans (add_le_add ?_ le_rfl)
    exact mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _)

/-- Strong L¹ convergence suffices for testing against any fixed bounded measurable weight. -/
public theorem tendsto_bounded_test_of_l1 {ι : Type*} {l : Filter ι}
    {F : ι → α → ℝ} {f φ : α → ℝ}
    (hF : ∀ i, Integrable (F i) μ) (hf : Integrable f μ)
    (hφ : AEStronglyMeasurable φ μ) (C : ℝ) (hb : ∀ᵐ x ∂μ, ‖φ x‖ ≤ C)
    (hlim : Tendsto (fun i => ∫ x, ‖F i x - f x‖ ∂μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, φ x * F i x ∂μ) l (𝓝 (∫ x, φ x * f x ∂μ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hupper := hlim.const_mul C
  rw [mul_zero] at hupper
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall fun _ => norm_nonneg _) (Eventually.of_forall fun i => ?_)
  rw [← integral_sub ((hF i).bdd_mul hφ hb) (hf.bdd_mul hφ hb)]
  simp only [← mul_sub]
  calc
    _ ≤ ∫ x, ‖φ x * (F i x - f x)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, C * ‖F i x - f x‖ ∂μ := by
      refine integral_mono_ae (((hF i).sub hf).bdd_mul hφ hb).norm
        (((hF i).sub hf).norm.const_mul C) ?_
      filter_upwards [hb] with x hx
      exact (norm_mul _ _).le.trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
    _ = _ := integral_const_mul _ _

/-- Strong L² convergence expressed in terms of representatives and square integrals. -/
public structure StrongL2 {ι : Type*} (l : Filter ι) (μ : Measure α)
    (F : ι → α → E) (f : α → E) : Prop where
  mem : ∀ i, MemLp (F i) 2 μ
  limit_mem : MemLp f 2 μ
  error : Tendsto (fun i => ∫ x, ‖F i x - f x‖ ^ (2 : ℝ) ∂μ) l (𝓝 0)

namespace StrongL2

variable {ι : Type*} {l : Filter ι} {F G : ι → α → E} {f g : α → E}

omit [InnerProductSpace ℝ E] in
/-- Derive the eventual bound on square integrals needed in the product estimate. -/
public theorem eventually_bounded (hf : StrongL2 l μ F f) : ∃ C : ℝ,
    ∀ᶠ i in l, (∫ x, ‖F i x‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) ≤ C := by
  refine ⟨Real.sqrt (2 + 2 * ∫ x, ‖f x‖ ^ (2 : ℕ) ∂μ), ?_⟩
  have hlt : ∀ᶠ i in l, (∫ x, ‖F i x - f x‖ ^ (2 : ℝ) ∂μ) < 1 :=
    hf.error (eventually_lt_nhds (by norm_num))
  filter_upwards [hlt] with i hi
  rw [← Real.sqrt_eq_rpow]
  apply Real.sqrt_le_sqrt
  simp only [Real.rpow_two] at hi ⊢
  have hi₀ := (hf.mem i).integrable_norm_pow (p := 2) (by decide)
  have hi₁ : Integrable (fun x => ‖F i x - f x‖ ^ (2 : ℕ)) μ :=
    ((hf.mem i).sub hf.limit_mem).integrable_norm_pow (p := 2) (by decide)
  have hi₂ := hf.limit_mem.integrable_norm_pow (p := 2) (by decide)
  calc
    _ ≤ ∫ x, 2 * ‖F i x - f x‖ ^ 2 + 2 * ‖f x‖ ^ 2 ∂μ := by
      refine integral_mono hi₀ ((hi₁.const_mul 2).add (hi₂.const_mul 2)) ?_
      intro x
      have ht : ‖F i x‖ ≤ ‖F i x - f x‖ + ‖f x‖ := by
        simpa only [sub_add_cancel] using norm_add_le (F i x - f x) (f x)
      calc
        ‖F i x‖ ^ 2 ≤ (‖F i x - f x‖ + ‖f x‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) ht 2
        _ ≤ _ := by nlinarith only [sq_nonneg (‖F i x - f x‖ - ‖f x‖)]
    _ = 2 * (∫ x, ‖F i x - f x‖ ^ 2 ∂μ) + 2 * (∫ x, ‖f x‖ ^ 2 ∂μ) := by
      rw [integral_add (hi₁.const_mul 2) (hi₂.const_mul 2), integral_const_mul,
        integral_const_mul]
    _ ≤ _ := by linarith only [hi]

public theorem inner_test_tendsto (hf : StrongL2 l μ F f) (hg : StrongL2 l μ G g)
    {φ : α → ℝ} (hφ : AEStronglyMeasurable φ μ) (B : ℝ) (hb : ∀ᵐ x ∂μ, ‖φ x‖ ≤ B) :
    Tendsto (fun i => ∫ x, φ x * inner ℝ (F i x) (G i x) ∂μ) l
      (𝓝 (∫ x, φ x * inner ℝ (f x) (g x) ∂μ)) := by
  obtain ⟨C, hC⟩ := hg.eventually_bounded
  exact tendsto_bounded_test_of_l1 (fun i => integrable_weak_inner (hf.mem i) (hg.mem i))
    (integrable_weak_inner hf.limit_mem hg.limit_mem) hφ B hb
    (tendsto_integral_norm_inner_sub hf.mem hg.mem hf.limit_mem hg.limit_mem hf.error hg.error C hC)

end StrongL2

end C2Riemannian
