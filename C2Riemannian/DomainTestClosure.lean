module

public import C2Riemannian.WeakAnalysis

set_option autoImplicit false

open Filter MeasureTheory TopologicalSpace
open scoped Distributions Topology

namespace C2Riemannian

/-- Equality of locally integrable fields is closed under convergence of all
compactly supported smooth test pairings on the same open set. -/
public theorem ae_eq_of_same_domain_test_limits {ι F : Type*} {l : Filter ι} [NeBot l]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {U : Opens Plane} {a b : ι → Plane → F} {f g : Plane → F}
    (hf : LocallyIntegrableOn f U volume) (hg : LocallyIntegrableOn g U volume)
    (heq : ∀ᶠ n in l, a n =ᵐ[volume.restrict (U : Set Plane)] b n)
    (ha : ∀ φ : 𝓓(U, ℝ), Tendsto (fun n => ∫ x in ↑U, φ x • a n x) l
      (𝓝 (∫ x in ↑U, φ x • f x)))
    (hb : ∀ φ : 𝓓(U, ℝ), Tendsto (fun n => ∫ x in ↑U, φ x • b n x) l
      (𝓝 (∫ x in ↑U, φ x • g x))) :
    f =ᵐ[volume.restrict (U : Set Plane)] g := by
  refine ae_eq_of_test_integrals hf hg fun φ => ?_
  refine tendsto_nhds_unique_of_eventuallyEq (ha φ) (hb φ) ?_
  filter_upwards [heq] with n hn
  exact integral_congr_ae (hn.mono fun x hx => congrArg (fun y : F => φ x • y) hx)

end C2Riemannian
