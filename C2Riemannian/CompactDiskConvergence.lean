module

import C2Riemannian.DiagonalSubsequence

public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Sequences

set_option autoImplicit false

open Filter Set
open scoped Topology NNReal BoundedContinuousFunction

namespace C2Riemannian

/-- Uniform Lipschitz control and compact containment of the values give a
uniformly convergent subsequence on a compact domain. The limit retains both
the Lipschitz bound and compact containment. -/
public theorem compact_lipschitz_subsequence
    {X Y : Type*} [PseudoMetricSpace X] [CompactSpace X] [MetricSpace Y]
    (K : ℝ≥0) (F : ℕ → X → Y) (hF : ∀ n, LipschitzWith K (F n))
    (s : Set Y) (hs : IsCompact s) (hRange : ∀ n x, F n x ∈ s) :
    ∃ (g : X →ᵇ Y) (k : ℕ → ℕ),
      StrictMono k ∧ LipschitzWith K g ∧ (∀ x, g x ∈ s) ∧
      TendstoUniformly (fun n => F (k n)) g atTop := by
  let seq (n : ℕ) : X →ᵇ Y :=
    BoundedContinuousFunction.mkOfCompact ⟨F n, (hF n).continuous⟩
  have hValues (f : X →ᵇ Y) (x : X) (hf : f ∈ range seq) : f x ∈ s := by
    obtain ⟨n, rfl⟩ := hf
    exact hRange n x
  have hLip (f : range seq) : LipschitzWith K (f.1 : X → Y) := by
    obtain ⟨f, ⟨n, rfl⟩⟩ := f
    exact hF n
  have hEqui : Equicontinuous (fun f : range seq => (f.1 : X → Y)) :=
    (LipschitzWith.uniformEquicontinuous _ K hLip).equicontinuous
  have hCompact : IsCompact (closure (range seq)) :=
    BoundedContinuousFunction.arzela_ascoli s hs (range seq) hValues hEqui
  obtain ⟨g, _, k, hk, hConvergence⟩ :=
    hCompact.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  have hUniform : TendstoUniformly (fun n => F (k n)) g atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hConvergence
  refine ⟨g, k, hk, LipschitzWith.of_dist_le_mul fun x y => ?_, fun x => ?_, hUniform⟩
  · exact le_of_tendsto ((hUniform.tendsto_at x).dist (hUniform.tendsto_at y))
      (Eventually.of_forall fun n => (hF (k n)).dist_le_mul x y)
  · exact hs.isClosed.mem_of_tendsto (hUniform.tendsto_at x)
      (Eventually.of_forall fun n => hRange (k n) x)

/-- The compact-subtype formulation for bounded Lipschitz maps with values in
a finite-dimensional real normed space. -/
public theorem compact_set_bounded_lipschitz_subsequence
    {X Y : Type*} [PseudoMetricSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] {s : Set X} (hs : IsCompact s)
    (K : ℝ≥0) (R : ℝ) (F : ℕ → s → Y)
    (hF : ∀ n, LipschitzWith K (F n)) (hBound : ∀ n x, ‖F n x‖ ≤ R) :
    ∃ (g : s →ᵇ Y) (k : ℕ → ℕ),
      StrictMono k ∧ LipschitzWith K g ∧ (∀ x, ‖g x‖ ≤ R) ∧
      TendstoUniformly (fun n => F (k n)) g atTop := by
  let _ : CompactSpace s := isCompact_iff_compactSpace.mp hs
  have hRange (n : ℕ) (x : s) : F n x ∈ Metric.closedBall (0 : Y) R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hBound n x
  obtain ⟨g, k, hk, hgLip, hgRange, hUniform⟩ :=
    compact_lipschitz_subsequence K F hF (Metric.closedBall (0 : Y) R)
      (isCompact_closedBall 0 R) hRange
  exact ⟨g, k, hk, hgLip, fun x => by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hgRange x, hUniform⟩


/-- An exhaustion by countably many compact sets gives a common subsequence
and a single limit. Pointwise uniqueness identifies the limits on overlaps. -/
public theorem compact_cover_bounded_lipschitz_subsequence
    {X Y : Type*} [PseudoMetricSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] (s : ℕ → Set X) (hs : ∀ j, IsCompact (s j))
    (hCover : ∀ x, ∃ j, x ∈ s j)
    (K : ℝ≥0) (R : ℝ) (F : ℕ → X → Y)
    (hF : ∀ n, LipschitzWith K (F n)) (hBound : ∀ n x, ‖F n x‖ ≤ R) :
    ∃ (g : X → Y) (k : ℕ → ℕ),
      StrictMono k ∧ LipschitzWith K g ∧ (∀ x, ‖g x‖ ≤ R) ∧
      ∀ j, TendstoUniformlyOn (fun n => F (k n)) g atTop (s j) := by
  let P (j : ℕ) (σ : ℕ → ℕ) :=
    ∃ g : s j → Y, TendstoUniformly (fun n (x : s j) => F (σ n) x) g atTop
  have hRefine (j : ℕ) (σ : ℕ → ℕ) :
      ∃ k : ℕ → ℕ, StrictMono k ∧ P j (σ ∘ k) := by
    obtain ⟨g, k, hk, _, _, hUniform⟩ :=
      compact_set_bounded_lipschitz_subsequence (hs j) K R
        (fun n (x : s j) => F (σ n) x)
        (fun n => (hF (σ n)).comp (LipschitzWith.subtype_val (s j)) |>.weaken (by simp))
        (fun n x => hBound (σ n) x)
    exact ⟨k, hk, g, hUniform⟩
  have hStable (j : ℕ) (σ k : ℕ → ℕ) (hk : StrictMono k)
      (hσ : P j σ) : P j (σ ∘ k) := by
    obtain ⟨g, hg⟩ := hσ
    exact ⟨g, fun u hu => hk.tendsto_atTop.eventually (hg u hu)⟩
  have hTail (j : ℕ) (σ : ℕ → ℕ) (c : ℕ)
      (hσ : P j (fun n => σ (n + c))) : P j σ := by
    obtain ⟨g, hg⟩ := hσ
    refine ⟨g, fun u hu => ?_⟩
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hg u hu)
    refine eventually_atTop.mpr ⟨N + c, fun n hn => ?_⟩
    have hc : c ≤ n := (Nat.le_add_left c N).trans hn
    have hm : N ≤ n - c := (Nat.le_sub_iff_add_le hc).mpr hn
    simpa only [Nat.sub_add_cancel hc] using hN (n - c) hm
  obtain ⟨k, hk, hEach⟩ := diagonal_subsequence P
    (fun j σ _ => hRefine j σ)
    (fun j σ τ _ hτ => hStable j σ τ hτ)
    (fun j σ c _ => hTail j σ c)
  choose localLimit hLocal using hEach
  choose level hLevel using hCover
  let g (x : X) := localLimit (level x) ⟨x, hLevel x⟩
  have hPoint (x : X) : Tendsto (fun n => F (k n) x) atTop (𝓝 (g x)) :=
    (hLocal (level x)).tendsto_at ⟨x, hLevel x⟩
  have hAgree (j : ℕ) (x : X) (hx : x ∈ s j) : g x = localLimit j ⟨x, hx⟩ :=
    tendsto_nhds_unique (hPoint x) ((hLocal j).tendsto_at ⟨x, hx⟩)
  refine ⟨g, k, hk, LipschitzWith.of_dist_le_mul fun x y => ?_, fun x => ?_,
    fun j u hu => ?_⟩
  · exact le_of_tendsto ((hPoint x).dist (hPoint y))
      (Eventually.of_forall fun n => (hF (k n)).dist_le_mul x y)
  · exact le_of_tendsto (continuous_norm.continuousAt.tendsto.comp (hPoint x))
      (Eventually.of_forall fun n => hBound (k n) x)
  · exact (hLocal j u hu).mono fun _ hn x hx => by
      rw [hAgree j x hx]
      exact hn ⟨x, hx⟩

end C2Riemannian
