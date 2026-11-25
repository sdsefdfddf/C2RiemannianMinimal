module

public import C2Riemannian.ConditionalRiesz
public import C2Riemannian.PairingDensities
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open MeasureTheory Set Filter TopologicalSpace
open scoped Topology

namespace C2Riemannian.PositiveFunctional

private theorem tendsto_extend_from_dense {E : Type*} [PseudoMetricSpace E] {D : Set E}
    (hD : Dense D) {f : ℕ → E → ℝ} {g : E → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ n x y, dist (f n x) (f n y) ≤ C * dist x y)
    (hg : ∀ x y, dist (g x) (g y) ≤ C * dist x y)
    (hlim : ∀ x ∈ D, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (x : E) : Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  let δ : ℝ := ε / (3 * (C + 1))
  have hδ : 0 < δ := by positivity
  obtain ⟨y, hyD, hxy⟩ := Metric.mem_closure_iff.mp (hD x) δ hδ
  have hsmall : C * dist x y ≤ ε / 3 := by
    calc
      _ ≤ (C + 1) * dist x y := mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
      _ ≤ (C + 1) * δ := mul_le_mul_of_nonneg_left hxy.le (by positivity)
      _ = _ := by
        dsimp [δ]
        field_simp
  filter_upwards [Metric.tendsto_nhds.mp (hlim y hyD) (ε / 3) (by positivity)] with n hn
  have hb := (hf n x y).trans hsmall
  have hc : dist (g y) (g x) ≤ ε / 3 := by
    rw [dist_comm (g y)]
    exact (hg x y).trans hsmall
  have htri : dist (f n x) (g x) ≤
      dist (f n x) (f n y) + dist (f n y) (g y) + dist (g y) (g x) := by
    exact (dist_triangle (f n x) (g y) (g x)).trans
      (add_le_add (dist_triangle (f n x) (f n y) (g y)) le_rfl)
  linarith only [htri, hb, hn, hc]

private theorem pairing_difference_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (γ : Lp ℝ 1 μ) {f g : Ω → ℝ}
    (hf : Integrable (fun x => f x * γ x) μ) (hg : Integrable (fun x => g x * γ x) μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖f x - g x‖ ≤ C) :
    dist (∫ x, f x * γ x ∂μ) (∫ x, g x * γ x ∂μ) ≤ C * ‖γ‖ := by
  rw [dist_eq_norm, ← integral_sub hf hg]
  simp only [← sub_mul]
  calc
    _ ≤ ∫ x, C * ‖γ x‖ ∂μ := by
      apply norm_integral_le_of_norm_le ((L1.integrable_coeFn γ).norm.const_mul _)
      filter_upwards [hC] with x hx
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    _ = C * ‖γ‖ := by rw [integral_const_mul, L1.norm_eq_integral_norm]

variable {X Ω : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] [MeasurableSpace Ω] {μ : Measure Ω}

/-- All continuous tests have the same pairing limit once it is established on a uniformly
dense family. The source sequence and phase multipliers are the same for all readouts. -/
public theorem conditional_pairing_tendsto_of_dense
    {D : Set C(X, ℝ)} (hD : Dense D) (L : Ω → PositiveFunctional X)
    (state : ℕ → Ω → X) (phase : ℕ → Ω → ℝ)
    (hs : ∀ n, Measurable (state n)) (hp : ∀ n, AEStronglyMeasurable (phase n) μ)
    (hb : ∀ n, ∀ᵐ x ∂μ, ‖phase n x‖ ≤ 2)
    (hm : ∀ f ∈ D, Measurable (fun x => L x f))
    (hlim : ∀ f ∈ D, ∀ γ : Lp ℝ 1 μ,
      Tendsto (fun n => ∫ x, phase n x * f (state n x) * γ x ∂μ) atTop
        (𝓝 (∫ x, L x f * γ x ∂μ)))
    (f : C(X, ℝ)) (γ : Lp ℝ 1 μ) :
    Tendsto (fun n => ∫ x, phase n x * f (state n x) * γ x ∂μ) atTop
      (𝓝 (∫ x, (∫ y, f y ∂(L x).representingMeasure) * γ x ∂μ)) := by
  simp only [integral_representingMeasure]
  let F (n : ℕ) (f : C(X, ℝ)) := ∫ x, (phase n x * f (state n x)) * γ x ∂μ
  let G (f : C(X, ℝ)) := ∫ x, L x f * γ x ∂μ
  have hRaw (n : ℕ) (f : C(X, ℝ)) : Integrable (fun x => phase n x * f (state n x) * γ x) μ := by
    refine (L1.integrable_coeFn γ).bdd_mul (c := 2 * ‖f‖) ((hp n).mul
      ((f.continuous.measurable.comp (hs n)).aestronglyMeasurable)) ?_
    filter_upwards [hb n] with x hx
    rw [norm_mul]
    exact mul_le_mul hx (f.norm_coe_le_norm _) (norm_nonneg _) (by norm_num)
  have hInt (f : C(X, ℝ)) : Integrable (fun x => L x f * γ x) μ :=
    (L1.integrable_coeFn γ).bdd_mul
      ((measurable_readout_of_dense hD L hm f).aestronglyMeasurable)
      (Eventually.of_forall fun x => (L x).norm_readout_le f)
  have hF (n : ℕ) (f g : C(X, ℝ)) : dist (F n f) (F n g) ≤ (2 * ‖γ‖) * dist f g := by
    have hi := pairing_difference_bound γ (hRaw n f) (hRaw n g)
      (C := 2 * dist f g) ?_
    · exact hi.trans_eq (by ring)
    · filter_upwards [hb n] with x hx
      rw [← mul_sub, norm_mul, dist_eq_norm]
      exact mul_le_mul hx ((f - g).norm_coe_le_norm _) (norm_nonneg _) (by norm_num)
  have hG (f g : C(X, ℝ)) : dist (G f) (G g) ≤ (2 * ‖γ‖) * dist f g := by
    have hi := pairing_difference_bound γ (hInt f) (hInt g) (C := dist f g) ?_
    · have hmul : 0 ≤ ‖γ‖ * dist f g := mul_nonneg (norm_nonneg _) dist_nonneg
      exact hi.trans (by nlinarith only [hmul])
    · exact Eventually.of_forall fun x => by
        rw [← map_sub, dist_eq_norm]
        exact (L x).norm_readout_le _
  exact tendsto_extend_from_dense hD (mul_nonneg (by norm_num) (norm_nonneg γ)) hF hG
    (fun g hg => hlim g hg γ) f

/-- The (L^1) pairing limits represented by densities on a dense family determine every
conditional probability pairing on the same subsequence. -/
public theorem conditional_pairing_tendsto_of_densities
    {D : Set C(X, ℝ)} (hD : Dense D) (L : Ω → PositiveFunctional X)
    (state : ℕ → Ω → X) (phase : ℕ → Ω → ℝ)
    (hs : ∀ n, Measurable (state n)) (hp : ∀ n, AEStronglyMeasurable (phase n) μ)
    (hb : ∀ n, ∀ᵐ x ∂μ, ‖phase n x‖ ≤ 2)
    (hm : ∀ f ∈ D, Measurable (fun x => L x f))
    (J : D → (Lp ℝ 1 μ →L[ℝ] ℝ)) (density : D → Ω → ℝ)
    (hseq : ∀ f : D, ∀ γ : Lp ℝ 1 μ,
      Tendsto (fun n => ∫ x, phase n x * (f : C(X, ℝ)) (state n x) * γ x ∂μ) atTop (𝓝 (J f γ)))
    (hrep : ∀ f γ, J f γ = ∫ x, γ x * density f x ∂μ)
    (hagree : ∀ f : D, ∀ᵐ x ∂μ, density f x = L x f)
    (f : C(X, ℝ)) (γ : Lp ℝ 1 μ) :
    Tendsto (fun n => ∫ x, phase n x * f (state n x) * γ x ∂μ) atTop
      (𝓝 (∫ x, (∫ y, f y ∂(L x).representingMeasure) * γ x ∂μ)) := by
  refine conditional_pairing_tendsto_of_dense hD L state phase hs hp hb hm ?_ f γ
  intro g hg γ'
  let g' : D := ⟨g, hg⟩
  have heq : J g' γ' = ∫ x, L x g * γ' x ∂μ := by
    rw [hrep g' γ']
    apply integral_congr_ae
    filter_upwards [hagree g'] with x hx
    rw [hx, mul_comm]
  exact heq ▸ hseq g' γ'

end C2Riemannian.PositiveFunctional


