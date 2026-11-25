module

public import C2Riemannian.SameDiskClosure
public import C2Riemannian.SourceContinuity
import Mathlib.Topology.Sequences

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal NNReal Topology

namespace C2Riemannian.WeakJet2

namespace DiskSolvability

variable (m : ℕ) (a : Plane) (R K : ℝ≥0)

/-- A solution of the scalar source equation on the original disk with a fixed
Frobenius bound and essentially bounded weak derivative fields. -/
@[expose] public def Solves (F : Plane → ℝ) : Prop :=
  ∃ w : WeakJet2 m (⟨Metric.ball a R, Metric.isOpen_ball⟩ : Opens Plane),
    MemLp w.value ∞ (volume.restrict (Metric.ball a R)) ∧
    MemLp w.gradient ∞ (volume.restrict (Metric.ball a R)) ∧
    MemLp w.second ∞ (volume.restrict (Metric.ball a R)) ∧
    (∀ᵐ x ∂volume.restrict (Metric.ball a R), (w.hessian x).frobenius ≤ (K : ℝ)) ∧
    (fun x => (w.hessian x).q) =ᵐ[volume.restrict (Metric.ball a R)] F

variable {m a R K}

/-- Fixed-bound solution sets are sequentially closed under distributional convergence
of sources with a locally integrable limit. -/
public theorem solves_of_test_limits (hm : 0 < m) (hR : 0 < R)
    {F : ℕ → Plane → ℝ} {f : Plane → ℝ}
    (hSol : ∀ n, Solves m a R K (F n)) (hf : LocallyIntegrableOn f (Metric.ball a R) volume)
    (hSource : ∀ ψ : 𝓓((⟨Metric.ball a R, Metric.isOpen_ball⟩ : Opens Plane), ℝ),
      Tendsto (fun n => ∫ x in Metric.ball a R, ψ x • F n x) atTop
        (𝓝 (∫ x in Metric.ball a R, ψ x • f x))) :
    Solves m a R K f := by
  choose W hValue hGradient hSecond hFrob hEq using hSol
  have hMeasure (j : ℕ) :
      (volume : Measure Plane).restrict (openDiskExhaustion a R j : Set Plane) ≤
      volume.restrict (Metric.ball a R) :=
    Measure.restrict_mono (openDiskExhaustion_subset a R j) le_rfl
  obtain ⟨C, hC⟩ := exists_same_disk_solution_limit hm a R K hR W
    (fun n j => (hValue n).mono_measure (hMeasure j))
    (fun n j => (hGradient n).mono_measure (hMeasure j)) hFrob F f hEq hf hSource
  exact ⟨C.limit, C.bounds.value_mem, C.bounds.gradient_mem, C.bounds.second_mem,
    C.bounds.frobenius_bound, hC⟩

/-- It suffices to check the source limit on any one strictly increasing sequence
of solvable indices. -/
public theorem solves_of_subsequence_test_limits (hm : 0 < m) (hR : 0 < R)
    {F : ℕ → Plane → ℝ} {f : Plane → ℝ} {k : ℕ → ℕ} (hk : StrictMono k)
    (hSol : ∀ n, Solves m a R K (F (k n))) (hf : LocallyIntegrableOn f (Metric.ball a R) volume)
    (hSource : ∀ ψ : 𝓓((⟨Metric.ball a R, Metric.isOpen_ball⟩ : Opens Plane), ℝ),
      Tendsto (fun n => ∫ x in Metric.ball a R, ψ x • F n x) atTop
        (𝓝 (∫ x in Metric.ball a R, ψ x • f x))) :
    Solves m a R K f :=
  solves_of_test_limits hm hR hSol hf (fun ψ => (hSource ψ).comp hk.tendsto_atTop)

/-- The solution set is closed in a sequential parameter space when all fixed
distributional pairings depend continuously on the parameter. -/
public theorem isClosed_solvable_parameters {X : Type*} [TopologicalSpace X] [SequentialSpace X]
    (hm : 0 < m) (hR : 0 < R) (source : X → Plane → ℝ)
    (hIntegrable : ∀ z, LocallyIntegrableOn (source z) (Metric.ball a R) volume)
    (hTest : ∀ ψ : 𝓓((⟨Metric.ball a R, Metric.isOpen_ball⟩ : Opens Plane), ℝ),
      Continuous (fun z => ∫ x in Metric.ball a R, ψ x • source z x)) :
    IsClosed {z | Solves m a R K (source z)} := by
  apply IsSeqClosed.isClosed
  intro z z₀ hz hlim
  exact solves_of_test_limits hm hR hz (hIntegrable z₀)
    (fun ψ => (hTest ψ).continuousAt.tendsto.comp hlim)

end DiskSolvability
end C2Riemannian.WeakJet2
