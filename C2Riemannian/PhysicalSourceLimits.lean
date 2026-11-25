module

public import C2Riemannian.PhysicalParameterTree
public import C2Riemannian.DiskSolvability
public import C2Riemannian.ScalarSourceContinuity
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions NNReal ENNReal Topology

namespace C2Riemannian

namespace PhysicalPrefix

/-- The metric coefficient attached to a physical prefix in the linear case. -/
@[expose] public noncomputable def metricCoefficient {Q : Set Plane} (p : PhysicalPrefix Q)
    (v₀ : Plane → ℝ) (θ : ℝ) (x : Plane) : ℝ := v₀ x + θ * p.input x

@[expose] public noncomputable def linearSource {Q : Set Plane} (p : PhysicalPrefix Q)
    (v₀ : Plane → ℝ) (θ : ℝ) (x : Plane) : ℝ :=
  -WeakJet2.metricYY (p.metricCoefficient v₀ θ) x / 2

public theorem metricCoefficient_contDiffOn {Q U : Set Plane} (p : PhysicalPrefix Q)
    {v₀ : Plane → ℝ} (hv₀ : ContDiffOn ℝ 2 v₀ U) (θ : ℝ) :
    ContDiffOn ℝ 2 (p.metricCoefficient v₀ θ) U :=
  hv₀.add (contDiffOn_const.mul (p.input_smooth.of_le (by simp)).contDiffOn)

public theorem linearSource_locallyIntegrable {Q : Set Plane} (p : PhysicalPrefix Q)
    {U : Opens Plane} {v₀ : Plane → ℝ} (hv₀ : ContDiffOn ℝ 2 v₀ (U : Set Plane)) (θ : ℝ) :
    LocallyIntegrableOn (p.linearSource v₀ θ) (U : Set Plane) volume := by
  have hc : ContinuousOn (p.linearSource v₀ θ) (U : Set Plane) :=
    (WeakJet2.metricYY_continuousOn (p.metricCoefficient_contDiffOn hv₀ θ)).neg.div_const 2
  exact hc.locallyIntegrableOn U.isOpen.measurableSet

/-- The reverse source of a prefix is the negative determinant of its scalar Hessian. -/
@[expose] public noncomputable def reverseSource {Q : Set Plane} (p : PhysicalPrefix Q)
    (x : Plane) : ℝ := -scalarHessianDet p.input x

end PhysicalPrefix

namespace PhysicalLayerRow

variable {Q : Set Plane} {directions : PhysicalDirections} {s δ : ℝ} {layer : IdealLayer}
  {p : PhysicalPrefix Q} {next : ℕ → PhysicalPrefix Q}

/-- For a fixed prefix, the realized linear sources of its children converge
against every compactly supported smooth test on the original domain. -/
public theorem linear_source_test_limits (row : PhysicalLayerRow directions s δ layer p next)
    (hBound : ∀ i : p.Active, Bornology.IsBounded (p.platform i.1))
    {U : Opens Plane} {v₀ : Plane → ℝ} (hv₀ : ContDiffOn ℝ 2 v₀ (U : Set Plane))
    (θ : ℝ) (φ : 𝓓(U, ℝ)) :
    Tendsto (fun n => ∫ x in ↑U, φ x • (next n).linearSource v₀ θ x) atTop
      (𝓝 (∫ x in ↑U, φ x • p.linearSource v₀ θ x)) := by
  have hc (n : ℕ) := (next n).metricCoefficient_contDiffOn hv₀ θ
  have hp := p.metricCoefficient_contDiffOn hv₀ θ
  apply WeakJet2.metric_source_tendsto_of_locally_uniform hc hp _ φ
  intro S _ _
  apply TendstoUniformly.tendstoUniformlyOn
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have hε' : 0 < ε / (‖θ‖ + 1) :=
    div_pos hε (add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one)
  filter_upwards [Metric.tendstoUniformly_iff.mp (row.input_c1_tendsto hBound).1 _ hε'] with n hn
  intro x
  rw [dist_eq_norm]
  have hDiff : p.metricCoefficient v₀ θ x - (next n).metricCoefficient v₀ θ x =
      θ * (p.input x - (next n).input x) := by
    simp [PhysicalPrefix.metricCoefficient, mul_sub]
  rw [hDiff, norm_mul]
  have hDist : ‖p.input x - (next n).input x‖ < ε / (‖θ‖ + 1) := by
    simpa only [dist_eq_norm] using hn x
  calc
    _ ≤ (‖θ‖ + 1) * ‖p.input x - (next n).input x‖ :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg _)
    _ < (‖θ‖ + 1) * (ε / (‖θ‖ + 1)) :=
      mul_lt_mul_of_pos_left hDist (add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one)
    _ = ε := by rw [mul_comm, div_mul_cancel₀ _ (by positivity)]

/-- A strictly increasing sequence of solvable children yields a solution of the
parent's linear source on the original disk with the same Frobenius bound. -/
public theorem linear_parent_solvable (row : PhysicalLayerRow directions s δ layer p next)
    (hBound : ∀ i : p.Active, Bornology.IsBounded (p.platform i.1))
    {m : ℕ} (hm : 0 < m) (a : Plane) (R K : ℝ≥0) (hR : 0 < R)
    {v₀ : Plane → ℝ} (hv₀ : ContDiffOn ℝ 2 v₀ (Metric.ball a R)) (θ : ℝ)
    (k : ℕ → ℕ) (hk : StrictMono k)
    (hSol : ∀ n, WeakJet2.DiskSolvability.Solves m a R K ((next (k n)).linearSource v₀ θ)) :
    WeakJet2.DiskSolvability.Solves m a R K (p.linearSource v₀ θ) :=
  WeakJet2.DiskSolvability.solves_of_subsequence_test_limits hm hR hk hSol
    (p.linearSource_locallyIntegrable (U := ⟨Metric.ball a R, Metric.isOpen_ball⟩) hv₀ θ)
    (fun ψ => row.linear_source_test_limits hBound hv₀ θ ψ)

/-- The compactness certificate is indexed by the given sequence of solvable
children and records the common further subsequence for the parent. -/
public theorem linear_parent_solution_limit (row : PhysicalLayerRow directions s δ layer p next)
    (hBound : ∀ i : p.Active, Bornology.IsBounded (p.platform i.1))
    {m : ℕ} (hm : 0 < m) (a : Plane) (R K : ℝ≥0) (hR : 0 < R)
    {v₀ : Plane → ℝ} (hv₀ : ContDiffOn ℝ 2 v₀ (Metric.ball a R)) (θ : ℝ)
    (k : ℕ → ℕ) (hk : StrictMono k)
    (W : ℕ → WeakJet2 m (⟨Metric.ball a R, Metric.isOpen_ball⟩ : Opens Plane))
    (hValue : ∀ n j, MemLp (W n).value ∞
      (volume.restrict (WeakJet2.openDiskExhaustion a R j : Set Plane)))
    (hGradient : ∀ n j, MemLp (W n).gradient ∞
      (volume.restrict (WeakJet2.openDiskExhaustion a R j : Set Plane)))
    (hHess : ∀ n, ∀ᵐ x ∂volume.restrict (Metric.ball a R),
      ((W n).hessian x).frobenius ≤ (K : ℝ))
    (hEq : ∀ n, (fun x => ((W n).hessian x).q) =ᵐ[volume.restrict (Metric.ball a R)]
      (next (k n)).linearSource v₀ θ) :
    ∃ C : WeakJet2.SameDiskLimit a R K W,
      (fun x => (C.limit.hessian x).q) =ᵐ[volume.restrict (Metric.ball a R)] p.linearSource v₀ θ :=
  WeakJet2.exists_same_disk_solution_limit hm a R K hR W hValue hGradient hHess
    (fun n => (next (k n)).linearSource v₀ θ) (p.linearSource v₀ θ) hEq
    (p.linearSource_locallyIntegrable (U := ⟨Metric.ball a R, Metric.isOpen_ball⟩) hv₀ θ)
    (fun ψ => (row.linear_source_test_limits hBound hv₀ θ ψ).comp hk.tendsto_atTop)

/-- For a fixed prefix, all reverse sources converge distributionally on the
same domain as the parent source. -/
public theorem reverse_source_test_limits (row : PhysicalLayerRow directions s δ layer p next)
    (hBound : ∀ i : p.Active, Bornology.IsBounded (p.platform i.1))
    {U : Opens Plane} (φ : 𝓓(U, ℝ)) :
    Tendsto (fun n => ∫ x in ↑U, φ x • (next n).reverseSource x) atTop
      (𝓝 (∫ x in ↑U, φ x • p.reverseSource x)) := by
  apply reverse_scalar_source_test_limits
    (fun n => (next n).input_smooth.of_le (by simp)) (p.input_smooth.of_le (by simp)) _ _ φ
  · intro x
    exact (row.input_c1_tendsto hBound).2.tendsto_at x
  · intro n x
    have hDenom : (1 : ℝ) ≤ (n : ℝ) + 1 :=
      le_add_of_nonneg_left (Nat.cast_nonneg n)
    have hRate : 1 / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_iff₀ (by positivity)).mpr (by simp [hDenom])
    exact ((row.input_c1_difference hBound n x).2.trans
      (mul_le_mul_of_nonneg_left hRate (by norm_num))).trans (by norm_num)

/-- The same further subsequence of reverse-source solutions records the
full parent compactness certificate on the original disk. -/
public theorem reverse_parent_solution_limit (row : PhysicalLayerRow directions s δ layer p next)
    (hBound : ∀ i : p.Active, Bornology.IsBounded (p.platform i.1))
    {m : ℕ} (hm : 0 < m) (a : Plane) (R K : ℝ≥0) (hR : 0 < R)
    (k : ℕ → ℕ) (hk : StrictMono k)
    (W : ℕ → WeakJet2 m (⟨Metric.ball a R, Metric.isOpen_ball⟩ : Opens Plane))
    (hValue : ∀ n j, MemLp (W n).value ∞
      (volume.restrict (WeakJet2.openDiskExhaustion a R j : Set Plane)))
    (hGradient : ∀ n j, MemLp (W n).gradient ∞
      (volume.restrict (WeakJet2.openDiskExhaustion a R j : Set Plane)))
    (hHess : ∀ n, ∀ᵐ x ∂volume.restrict (Metric.ball a R),
      ((W n).hessian x).frobenius ≤ (K : ℝ))
    (hEq : ∀ n, (fun x => ((W n).hessian x).q) =ᵐ[volume.restrict (Metric.ball a R)]
      (next (k n)).reverseSource) :
    ∃ C : WeakJet2.SameDiskLimit a R K W,
      (fun x => (C.limit.hessian x).q) =ᵐ[volume.restrict (Metric.ball a R)] p.reverseSource := by
  have hc : Continuous p.reverseSource :=
    (continuous_scalarHessianDet (p.input_smooth.of_le (by simp))).neg
  have hf : LocallyIntegrableOn p.reverseSource (Metric.ball a R) volume :=
    hc.continuousOn.locallyIntegrableOn Metric.isOpen_ball.measurableSet
  exact WeakJet2.exists_same_disk_solution_limit hm a R K hR W hValue hGradient hHess
    (fun n => (next (k n)).reverseSource) p.reverseSource hEq hf
    (fun ψ => (row.reverse_source_test_limits hBound ψ).comp hk.tendsto_atTop)

end PhysicalLayerRow
end C2Riemannian

