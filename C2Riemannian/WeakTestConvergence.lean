module

public import C2Riemannian.WeakCompatibilityLimit
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Tactic.Ring

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology ENNReal

namespace C2Riemannian

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {s : Set α}

/-- Uniform convergence on a finite-measure test set, with a common bound,
gives strong L² convergence for the restricted measure. -/
public theorem strongL2_of_uniformOn {F : ℕ → α → E} {f : α → E}
    (hs : MeasurableSet s) (hFinite : μ s ≠ ∞)
    (hF : ∀ n, AEStronglyMeasurable (F n) (μ.restrict s))
    (hf : AEStronglyMeasurable f (μ.restrict s))
    (K : ℝ) (hBound : ∀ n x, x ∈ s → ‖F n x‖ ≤ K) (hfBound : ∀ x ∈ s, ‖f x‖ ≤ K)
    (hUniform : TendstoUniformlyOn F f atTop s) :
    StrongL2 atTop (μ.restrict s) F f := by
  let _ : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.mpr hFinite
  have hMem : ∀ᵐ x ∂μ.restrict s, x ∈ s := ae_restrict_mem hs
  refine ⟨fun n => MemLp.of_bound (hF n) K (hMem.mono (hBound n)),
    MemLp.of_bound hf K (hMem.mono hfBound), ?_⟩
  have hError : Tendsto (fun n => ∫ x, ‖F n x - f x‖ ^ (2 : ℕ) ∂μ.restrict s)
      atTop (𝓝 (∫ _ : α, (0 : ℝ) ∂μ.restrict s)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (2 * K) ^ (2 : ℕ))
    · intro n
      exact ((hF n).sub hf).norm.pow 2
    · exact integrable_const _
    · intro n
      filter_upwards [hMem] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      apply pow_le_pow_left₀ (norm_nonneg _)
      have hSum := add_le_add (hBound n x hx) (hfBound x hx)
      rw [two_mul]
      exact (norm_sub_le _ _).trans hSum
    · filter_upwards [hMem] with x hx
      simpa using (((hUniform.tendsto_at hx).sub_const (f x)).norm.pow 2)
  simpa only [integral_zero, Real.rpow_two] using hError

/-- Uniformly convergent bounded scalar fields can be integrated against a
bounded weight on the restricted measure of the test set. -/
public theorem tendsto_setIntegral_bounded_test_of_uniformOn
    {F : ℕ → α → ℝ} {f φ : α → ℝ}
    (hs : MeasurableSet s) (hFinite : μ s ≠ ∞)
    (hF : ∀ n, AEStronglyMeasurable (F n) (μ.restrict s))
    (hφ : AEStronglyMeasurable φ (μ.restrict s))
    (K B : ℝ) (hBound : ∀ n x, x ∈ s → ‖F n x‖ ≤ K)
    (hWeight : ∀ x ∈ s, ‖φ x‖ ≤ B) (hB : 0 ≤ B)
    (hUniform : TendstoUniformlyOn F f atTop s) :
    Tendsto (fun n => ∫ x in s, φ x * F n x ∂μ) atTop (𝓝 (∫ x in s, φ x * f x ∂μ)) := by
  let _ : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.mpr hFinite
  have hMem : ∀ᵐ x ∂μ.restrict s, x ∈ s := ae_restrict_mem hs
  apply tendsto_integral_of_dominated_convergence (fun _ => B * K)
  · exact fun n => hφ.mul (hF n)
  · exact integrable_const _
  · intro n
    filter_upwards [hMem] with x hx
    rw [norm_mul]
    exact mul_le_mul (hWeight x hx) (hBound n x hx) (norm_nonneg _) hB
  · filter_upwards [hMem] with x hx
    exact (hUniform.tendsto_at hx).const_mul (φ x)

/-- Pairing the inner products of two uniformly convergent vector fields
against a bounded test on a finite-measure set. -/
public theorem tendsto_setIntegral_inner_test_of_uniformOn [InnerProductSpace ℝ E]
    {F G : ℕ → α → E} {f g : α → E} {φ : α → ℝ}
    (hs : MeasurableSet s) (hFinite : μ s ≠ ∞)
    (hF : ∀ n, AEStronglyMeasurable (F n) (μ.restrict s))
    (hG : ∀ n, AEStronglyMeasurable (G n) (μ.restrict s))
    (hf : AEStronglyMeasurable f (μ.restrict s)) (hg : AEStronglyMeasurable g (μ.restrict s))
    (hφ : AEStronglyMeasurable φ (μ.restrict s)) (K B : ℝ)
    (hBoundF : ∀ n x, x ∈ s → ‖F n x‖ ≤ K) (hBoundG : ∀ n x, x ∈ s → ‖G n x‖ ≤ K)
    (hBoundf : ∀ x ∈ s, ‖f x‖ ≤ K) (hBoundg : ∀ x ∈ s, ‖g x‖ ≤ K)
    (hWeight : ∀ x ∈ s, ‖φ x‖ ≤ B)
    (hUniformF : TendstoUniformlyOn F f atTop s) (hUniformG : TendstoUniformlyOn G g atTop s) :
    Tendsto (fun n => ∫ x in s, φ x * inner ℝ (F n x) (G n x) ∂μ) atTop
      (𝓝 (∫ x in s, φ x * inner ℝ (f x) (g x) ∂μ)) := by
  have hStrongF := strongL2_of_uniformOn hs hFinite hF hf K hBoundF hBoundf hUniformF
  have hStrongG := strongL2_of_uniformOn hs hFinite hG hg K hBoundG hBoundg hUniformG
  exact hStrongF.inner_test_tendsto hStrongG hφ B ((ae_restrict_mem hs).mono hWeight)


/-- The Gram compatibility identities turn convergence of the gradient pairings
into convergence of the tested Hessian quadratic form. On a test set the
gradient hypotheses follow from `strongL2_of_uniformOn`. -/
public theorem tendsto_gram_quadratic_test {m : ℕ}
    {φ ψxx ψxy ψyy : α → ℝ} {Px Py X Z Y : α → Target m}
    {PX PY XX ZZ YY : ℕ → α → Target m}
    (hxx : AEStronglyMeasurable ψxx μ) (hxy : AEStronglyMeasurable ψxy μ)
    (hyy : AEStronglyMeasurable ψyy μ) (B : ℝ)
    (bxx : ∀ᵐ x ∂μ, ‖ψxx x‖ ≤ B) (bxy : ∀ᵐ x ∂μ, ‖ψxy x‖ ≤ B)
    (byy : ∀ᵐ x ∂μ, ‖ψyy x‖ ≤ B)
    (hPx : StrongL2 atTop μ PX Px) (hPy : StrongL2 atTop μ PY Py)
    (hApprox : ∀ᶠ n in atTop, gramTest μ φ ψxx ψxy ψyy
      (PX n) (PY n) (XX n) (ZZ n) (YY n))
    (hLimit : gramTest μ φ ψxx ψxy ψyy Px Py X Z Y) :
    Tendsto (fun n =>
      (∫ x, φ x * inner ℝ (XX n x) (YY n x) ∂μ) -
      (∫ x, φ x * inner ℝ (ZZ n x) (ZZ n x) ∂μ)) atTop
      (𝓝 ((∫ x, φ x * inner ℝ (X x) (Y x) ∂μ) -
        (∫ x, φ x * inner ℝ (Z x) (Z x) ∂μ))) := by
  have hRight := ((hPx.inner_test_tendsto hPx hyy B byy).add
    (hPy.inner_test_tendsto hPy hxx B bxx)).sub
    ((hPx.inner_test_tendsto hPy hxy B bxy).const_mul 2)
  unfold gramTest at hLimit
  rw [← hLimit] at hRight
  have hScaled := hRight.congr' (hApprox.mono fun _ h => h.symm)
  have hCancel (a : ℝ) : (-1 / 2 : ℝ) * (-2 * a) = a := by ring
  let qApprox (n : ℕ) :=
    (∫ x, φ x * inner ℝ (XX n x) (YY n x) ∂μ) -
      (∫ x, φ x * inner ℝ (ZZ n x) (ZZ n x) ∂μ)
  let qLimit := (∫ x, φ x * inner ℝ (X x) (Y x) ∂μ) -
      (∫ x, φ x * inner ℝ (Z x) (Z x) ∂μ)
  have hScaled' : Tendsto (fun n => -2 * qApprox n) atTop (𝓝 (-2 * qLimit)) := hScaled
  have hUnscaled : Tendsto (fun n => (-1 / 2 : ℝ) * (-2 * qApprox n))
      atTop (𝓝 ((-1 / 2 : ℝ) * (-2 * qLimit))) := hScaled'.const_mul (-1 / 2)
  simp only [hCancel] at hUnscaled
  exact hUnscaled

end C2Riemannian
