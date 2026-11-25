module

public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Topology.UniformSpace.UniformApproximation

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace C2Riemannian

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A locally uniform limit of derivatives is the derivative of the pointwise
limit. Continuity of the derivative fields gives a C¹ limit on the open set. -/
public theorem contDiffOn_one_of_locally_uniform_derivatives {ι : Type*}
    {l : Filter ι} [NeBot l] {Ω : Set E} (hΩ : IsOpen Ω)
    {W : ι → E → F} {P : ι → E → E →L[ℝ] F}
    {w : E → F} {p : E → E →L[ℝ] F}
    (hDeriv : ∀ n x, x ∈ Ω → HasFDerivAt (W n) (P n x) x)
    (hContinuous : ∀ n, ContinuousOn (P n) Ω)
    (hValues : ∀ x ∈ Ω, Tendsto (fun n => W n x) l (𝓝 (w x)))
    (hFields : TendstoLocallyUniformlyOn P p l Ω) :
    ContDiffOn ℝ 1 w Ω ∧ ∀ x ∈ Ω, HasFDerivAt w (p x) x := by
  have hd (x : E) (hx : x ∈ Ω) : HasFDerivAt w (p x) x :=
    hasFDerivAt_of_tendstoLocallyUniformlyOn hΩ hFields hDeriv hValues hx
  have hc : ContinuousOn p Ω := hFields.continuousOn
    (Eventually.of_forall hContinuous).frequently
  have hDF : ContinuousOn (fderiv ℝ w) Ω :=
    hc.congr (fun x hx => (hd x hx).fderiv)
  refine ⟨?_, hd⟩
  have h : ContDiffOn ℝ (0 + 1) w Ω :=
    (contDiffOn_succ_iff_fderiv_of_isOpen hΩ).mpr
      ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt, by simp,
        contDiffOn_zero.mpr hDF⟩
  simpa only [zero_add] using h

/-- Uniform limits on every member of a compact exhaustion determine a C¹
limit potential and its derivative on the open domain. -/
public theorem contDiffOn_one_of_compact_exhaustion [LocallyCompactSpace E]
    {Ω : Set E} (hΩ : IsOpen Ω) (s : ℕ → Set E)
    (hExhaust : ∀ k : Set E, k ⊆ Ω → IsCompact k → ∃ j, k ⊆ s j)
    {W : ℕ → E → F} {P : ℕ → E → E →L[ℝ] F}
    {w : E → F} {p : E → E →L[ℝ] F}
    (hDeriv : ∀ n x, x ∈ Ω → HasFDerivAt (W n) (P n x) x)
    (hContinuous : ∀ n, ContinuousOn (P n) Ω)
    (hValues : ∀ j, TendstoUniformlyOn W w atTop (s j))
    (hFields : ∀ j, TendstoUniformlyOn P p atTop (s j)) :
    ContDiffOn ℝ 1 w Ω ∧ ∀ x ∈ Ω, HasFDerivAt w (p x) x := by
  have hW : TendstoLocallyUniformlyOn W w atTop Ω := by
    apply (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).mpr
    intro k hSub hk
    obtain ⟨j, hj⟩ := hExhaust k hSub hk
    exact (hValues j).mono hj
  have hP : TendstoLocallyUniformlyOn P p atTop Ω := by
    apply (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).mpr
    intro k hSub hk
    obtain ⟨j, hj⟩ := hExhaust k hSub hk
    exact (hFields j).mono hj
  exact contDiffOn_one_of_locally_uniform_derivatives hΩ hDeriv hContinuous
    (fun _ hx => hW.tendsto_at hx) hP

end C2Riemannian
