module

public import C2Riemannian.PhysicalTangentialConstraint
public import C2Riemannian.NormalizedCompactness

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions Topology

namespace C2Riemannian

/-- On a compact test support, the uniform error of continuous functions has a
nonnegative scalar bound tending to zero. -/
public theorem uniform_error_on_compact {E F : Type*} [TopologicalSpace E]
    [NormedAddCommGroup F] {S : Set E} (hS : IsCompact S) {g : ℕ → E → F} {g₀ : E → F}
    (hc : ∀ n, ContinuousOn (g n) S) (hc₀ : ContinuousOn g₀ S)
    (hu : TendstoUniformlyOn g g₀ atTop S) :
    ∃ d : ℕ → ℝ, Tendsto d atTop (𝓝 0) ∧ ∀ n, ∀ x ∈ S, ‖g n x - g₀ x‖ ≤ d n := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hn
  · exact ⟨fun _ => 0, tendsto_const_nhds, by simp⟩
  have hmax (n : ℕ) : ∃ x ∈ S, IsMaxOn (fun y => ‖g n y - g₀ y‖) S x :=
    hS.exists_isMaxOn hn ((hc n).sub hc₀).norm
  choose x hx hm using hmax
  refine ⟨fun n => ‖g n (x n) - g₀ (x n)‖, ?_, fun n y hy => hm n hy⟩
  rw [tendsto_order]
  refine ⟨fun b hb => Eventually.of_forall fun _ => hb.trans_le (norm_nonneg _), ?_⟩
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu ε hε] with n h
  have hd := h (x n) (hx n)
  rwa [dist_comm, dist_eq_norm] at hd

namespace PhysicalLayerRow

variable {Q : Set Plane} {directions : PhysicalDirections} {s δ : ℝ}
  {layer : IdealLayer} {p : PhysicalPrefix Q} {next : ℕ → PhysicalPrefix Q}

/-- The compact-exhaustion gradient convergence of normalized weak jets yields
the conditional tangency identity for each scalar Hessian readout. -/
public theorem conditional_phase_tangent_weakJet_ae {m : ℕ}
    (row : PhysicalLayerRow directions s δ layer p next) (i : p.Active) (sign : Bool)
    (hn : directions.normal layer s ≠ 0) (k : ℕ → ℕ) (hk : StrictMono k)
    {τ : Plane} (hτ : inner ℝ (directions.normal layer s) τ = 0)
    (w : ℕ → WeakJet2 m (parentOpen p i)) (w₀ : WeakJet2 m (parentOpen p i))
    (v : Plane) (ℓ : Target m →L[ℝ] ℝ) (a : Plane) (R : ℝ)
    (hsub : p.platform i.1 ⊆ Metric.ball a R)
    (hgc : ∀ j, ContinuousOn (w j).gradient (p.platform i.1))
    (hgc₀ : ContinuousOn w₀.gradient (p.platform i.1))
    (hgu : ∀ n, TendstoUniformlyOn (fun j => (w j).gradient) w₀.gradient atTop
      (diskExhaustion a R n))
    {b : Plane → ℝ} (hb : LocallyIntegrableOn b (parentOpen p i) volume)
    (hmean : ∀ φ : 𝓓(parentOpen p i, ℝ),
      Tendsto (fun j => ∫ x in p.platform i.1, row.phaseWeight i sign (k j) x *
        (φ x * ℓ ((w j).second x τ v))) atTop (𝓝 (∫ x in p.platform i.1, φ x * b x))) :
    b =ᵐ[volume.restrict (p.platform i.1)] fun x => ℓ (w₀.second x τ v) := by
  apply row.conditional_phase_tangent_ae i sign hn k hk hτ
    (fun j => ((w j).weak_component τ v).clm_comp ℓ) ((w₀.weak_component τ v).clm_comp ℓ) hb
    ?_ hmean
  intro φ
  let S := tsupport (φ : Plane → ℝ)
  have hS : S ⊆ p.platform i.1 := φ.tsupport_subset
  obtain ⟨n, hSn⟩ := diskExhaustion_covers_compacts a R S (hS.trans hsub) φ.hasCompactSupport
  let L : (Plane →L[ℝ] Target m) →L[ℝ] ℝ := ℓ.comp (ContinuousLinearMap.apply ℝ _ v)
  exact uniform_error_on_compact φ.hasCompactSupport
    (fun j => L.continuous.comp_continuousOn ((hgc j).mono hS))
    (L.continuous.comp_continuousOn (hgc₀.mono hS))
    (L.uniformContinuous.comp_tendstoUniformlyOn ((hgu n).mono hSn))

end PhysicalLayerRow
end C2Riemannian
