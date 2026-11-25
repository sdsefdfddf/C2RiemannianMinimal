module

public import C2Riemannian.DiskSolvability
public import C2Riemannian.PhysicalCertificateInduction

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

namespace C2Riemannian.PhysicalPrefix

variable {Q : Set Plane}

/-- One whole-disk solution with an energy bound on each active platform. -/
@[expose] public def HasEnergySolution (p : PhysicalPrefix Q) (m : ℕ) (a : Plane)
    (R K : ℝ≥0) (F : Plane → ℝ) (B : ℝ) : Prop :=
  ∃ w : WeakJet2 m (⟨Metric.ball a R, Metric.isOpen_ball⟩ : Opens Plane),
    MemLp w.value ∞ (volume.restrict (Metric.ball a R)) ∧
    MemLp w.gradient ∞ (volume.restrict (Metric.ball a R)) ∧
    MemLp w.second ∞ (volume.restrict (Metric.ball a R)) ∧
    (∀ᵐ x ∂volume.restrict (Metric.ball a R), (w.hessian x).frobenius ≤ (K : ℝ)) ∧
    ((fun x => (w.hessian x).q) =ᵐ[volume.restrict (Metric.ball a R)] F) ∧
    ∀ i : p.Active, ∀ᵐ x ∂volume.restrict (p.platform i.1), (w.hessian x).energy ≤ B

/-- The terminal certificate uses the energy bound of the full Frobenius ball. -/
public theorem hasEnergySolution_of_solves (p : PhysicalPrefix Q) {m : ℕ} {a : Plane}
    {R K : ℝ≥0} {F : Plane → ℝ} (hQ : Q ⊆ Metric.ball a R)
    (hSol : WeakJet2.DiskSolvability.Solves m a R K F) :
    p.HasEnergySolution m a R K F ((K : ℝ) ^ 2 / 2) := by
  obtain ⟨w, hv, hg, hs, hb, hF⟩ := hSol
  refine ⟨w, hv, hg, hs, hb, hF, fun i => ?_⟩
  have hsub := (p.platform_subset i.1).trans hQ
  filter_upwards [MeasureTheory.ae_mono (Measure.restrict_mono hsub le_rfl) hb] with x hx
  apply (w.hessian x).energy_le.trans
  rw [← (w.hessian x).sq_frobenius]
  exact div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (w.hessian x).frobenius_nonneg hx 2) (by norm_num)

/-- A negative budget is impossible on a nonempty active open platform. -/
public theorem budget_nonneg_of_hasEnergySolution (p : PhysicalPrefix Q) {m : ℕ} {a : Plane}
    {R K : ℝ≥0} {F : Plane → ℝ} {B : ℝ} (i : p.Active)
    (hSol : p.HasEnergySolution m a R K F B) : 0 ≤ B := by
  obtain ⟨w, _, _, _, _, _, hB⟩ := hSol
  have hPos : 0 < volume (p.platform i.1) :=
    (p.platform_open i.1).measure_pos _ (p.platform_nonempty i.1)
  let _ : NeZero ((volume : Measure Plane).restrict (p.platform i.1)) :=
    ⟨fun h => hPos.ne' (Measure.restrict_eq_zero.mp h)⟩
  obtain ⟨x, hx⟩ := (hB i).exists
  exact (w.hessian x).energy_nonneg.trans hx

end C2Riemannian.PhysicalPrefix
