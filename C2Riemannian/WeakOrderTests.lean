module

public import C2Riemannian.WeakMollificationStrong

set_option autoImplicit false

open MeasureTheory Set Filter TopologicalSpace
open scoped ContDiff Distributions Topology

namespace C2Riemannian

private noncomputable def kernelTest {U : Opens Plane} (φ : ContDiffBump (0 : Plane)) (x : Plane)
    (hx : Metric.closedBall x φ.rOut ⊆ (U : Set Plane)) : 𝓓(U, ℝ) := by
  let ρ : Plane → ℝ := φ.normed volume
  have hc : ContDiff ℝ ∞ (fun y => ρ (x - y)) :=
    φ.contDiff_normed.comp (contDiff_const.sub contDiff_id)
  have hcompact : HasCompactSupport (fun y => ρ (x - y)) :=
    φ.hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft x)
  have hs : tsupport (fun y => ρ (x - y)) ⊆ (U : Set Plane) := by
    change tsupport (ρ ∘ Homeomorph.subLeft x) ⊆ (U : Set Plane)
    rw [tsupport_comp_eq_preimage, show tsupport ρ = Metric.closedBall 0 φ.rOut from φ.tsupport_normed_eq]
    intro y hy
    apply hx
    change x - y ∈ Metric.closedBall (0 : Plane) φ.rOut at hy
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_sub_rev] using hy
  exact ⟨_, hc, hcompact, hs⟩

private theorem mollify_eq_kernel_integral {U : Opens Plane} (f : Plane → ℝ)
    (φ : ContDiffBump (0 : Plane)) (x : Plane)
    (hx : Metric.closedBall x φ.rOut ⊆ (U : Set Plane)) :
    WeakJet2.mollify U φ f x = ∫ y in ↑U, kernelTest φ x hx y * f y := by
  change (∫ y, φ.normed volume (x - y) * (U : Set Plane).indicator f y) =
    ∫ y in ↑U, φ.normed volume (x - y) * f y
  rw [← integral_indicator U.isOpen.measurableSet]
  congr 1
  ext y
  by_cases hy : y ∈ (U : Set Plane) <;> simp [hy]

/-- An integrable scalar field is nonpositive almost everywhere on an open set if its
integral against every nonnegative smooth compactly supported test is nonpositive. -/
public theorem ae_nonpos_of_nonneg_test_integrals {U : Opens Plane} {f : Plane → ℝ}
    (hf : IntegrableOn f (U : Set Plane) volume)
    (htest : ∀ φ : 𝓓(U, ℝ), (∀ x, 0 ≤ φ x) → (∫ x in ↑U, φ x * f x) ≤ 0) :
    ∀ᵐ x ∂volume.restrict (U : Set Plane), f x ≤ 0 := by
  have ha := WeakJet2.mollify_ae_tendsto (memLp_one_iff_integrable.2 hf) le_rfl
    WeakJet2.shrinkingBump WeakJet2.shrinkingBump_rOut_tendsto WeakJet2.shrinkingBump_ratio
  have hu : ∀ᵐ x ∂volume.restrict (U : Set Plane), x ∈ (U : Set Plane) :=
    ae_restrict_mem U.isOpen.measurableSet
  filter_upwards [ha, hu] with x hlim hx
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (U.isOpen.mem_nhds hx)
  have hr : ∀ᶠ n in atTop, (WeakJet2.shrinkingBump n).rOut < δ :=
    WeakJet2.shrinkingBump_rOut_tendsto.eventually (gt_mem_nhds hδ)
  apply le_of_tendsto hlim
  filter_upwards [hr] with n hn
  have hfit := (Metric.closedBall_subset_ball hn).trans hball
  rw [mollify_eq_kernel_integral f _ x hfit]
  exact htest _ fun y => (WeakJet2.shrinkingBump n).nonneg_normed (x - y)

/-- Nonnegative compactly supported smooth tests determine the almost-everywhere order of
locally integrable scalar fields on an open set. -/
public theorem ae_nonpos_of_locallyIntegrable_nonneg_test_integrals
    {U : Opens Plane} {f : Plane → ℝ} (hf : LocallyIntegrableOn f U volume)
    (htest : ∀ φ : 𝓓(U, ℝ), (∀ x, 0 ≤ φ x) → (∫ x in ↑U, φ x * f x) ≤ 0) :
    ∀ᵐ x ∂volume.restrict (U : Set Plane), f x ≤ 0 := by
  obtain ⟨s, hs, hcover, hint⟩ := hf.exists_nat_integrableOn
  let V (n : ℕ) : Opens Plane := ⟨s n ∩ (U : Set Plane), (hs n).inter U.isOpen⟩
  have hlocal (n : ℕ) : ∀ᵐ x ∂volume.restrict (V n : Set Plane), f x ≤ 0 := by
    apply ae_nonpos_of_nonneg_test_integrals (hint n)
    intro φ hφ
    let ψ : 𝓓(U, ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport,
      φ.tsupport_subset.trans inter_subset_right⟩
    have h₁ := TauCeti.setIntegral_smul_eq_integral_smul (μ := volume) (w := f) φ
    have h₂ := TauCeti.setIntegral_smul_eq_integral_smul (μ := volume) (w := f) ψ
    simp only [smul_eq_mul] at h₁ h₂
    have heq : (∫ x in ↑(V n), φ x * f x) = ∫ x in ↑U, ψ x * f x := h₁.trans h₂.symm
    rw [heq]
    exact htest ψ hφ
  have heq : (U : Set Plane) = ⋃ n, (V n : Set Plane) := by
    ext x
    simp only [mem_iUnion, V, Opens.coe_mk, mem_inter_iff]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover hx)
      exact ⟨n, hn, hx⟩
    · rintro ⟨n, _, hx⟩
      exact hx
  rw [heq]
  exact (ae_restrict_iUnion_iff _ _).2 hlocal

end C2Riemannian
