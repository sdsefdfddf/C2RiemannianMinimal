module

public import C2Riemannian.DiagonalSubsequence
public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Data.Nat.Pairing
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Filter Set TopologicalSpace
open scoped Topology

namespace C2Riemannian

/-- Countably many bounded scalar pairings admit one common convergent subsequence. -/
public theorem exists_diagonal_pairing_limits
    (a : ℕ → ℕ → ℝ) (B : ℕ → ℝ) (hb : ∀ j n, ‖a j n‖ ≤ B j)
    (base : ℕ → ℕ) (hBase : StrictMono base) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ j, ∃ c : ℝ, Tendsto (fun n => a j (base (σ n))) atTop (𝓝 c) := by
  let R (j : ℕ) (k : ℕ → ℕ) : Prop := ∃ c : ℝ, Tendsto (fun n => a j (k n)) atTop (𝓝 c)
  apply diagonal_subsequence_from R _ _ _ base hBase
  · intro j k hk
    obtain ⟨c, _, t, ht, hlim⟩ := (isCompact_Icc (a := -B j) (b := B j)).tendsto_subseq
      (x := fun n => a j (k n)) (fun n => abs_le.mp (by simpa only [Real.norm_eq_abs] using hb j (k n)))
    exact ⟨t, ht, c, hlim⟩
  · intro j k t _ ht h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, hc.comp ht.tendsto_atTop⟩
  · intro j k c _ h
    obtain ⟨z, hz⟩ := h
    exact ⟨z, (tendsto_add_atTop_iff_nat (f := fun n => a j (k n)) c).mp hz⟩

private theorem norm_apply_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) {B : ℝ} (hL : ‖L‖ ≤ B) (x : E) :
    ‖L x‖ ≤ B * ‖x‖ :=
  (L.le_opNorm x).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))

/-- Limits on a dense sequence extend to bounded linear pairings on the whole
test space. The same subsequence works for every pairing and every test. -/
public theorem exists_diagonal_continuousLinearMap_limits
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SeparableSpace E]
    (L : ℕ → ℕ → E →L[ℝ] ℝ) (B : ℕ → ℝ)
    (hB : ∀ j, 0 ≤ B j) (hL : ∀ j n, ‖L j n‖ ≤ B j)
    (base : ℕ → ℕ) (hBase : StrictMono base) :
    ∃ (σ : ℕ → ℕ) (limit : ℕ → E →L[ℝ] ℝ), StrictMono σ ∧
      (∀ j, ‖limit j‖ ≤ B j) ∧
      ∀ j x, Tendsto (fun n => L j (base (σ n)) x) atTop (𝓝 (limit j x)) := by
  obtain ⟨u, hu⟩ := exists_dense_seq E
  let a (p n : ℕ) := L p.unpair.1 n (u p.unpair.2)
  let C (p : ℕ) := B p.unpair.1 * ‖u p.unpair.2‖
  obtain ⟨σ, hσ, hConverges⟩ := exists_diagonal_pairing_limits a C
    (fun p n => norm_apply_le (L p.unpair.1 n) (hL p.unpair.1 n) (u p.unpair.2)) base hBase
  let T (j n : ℕ) := L j (base (σ n))
  have hDense (j i : ℕ) : ∃ l : ℝ, Tendsto (fun n => T j n (u i)) atTop (𝓝 l) := by
    simpa only [a, Nat.unpair_pair, T] using hConverges (Nat.pair j i)
  have hCauchy (j : ℕ) (x : E) : CauchySeq (fun n => T j n x) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    let δ := (ε / 4) / (B j + 1)
    have hδ : 0 < δ := div_pos (by positivity) (by linarith [hB j])
    obtain ⟨i, hi⟩ := Metric.denseRange_iff.mp hu x δ hδ
    obtain ⟨l, hl⟩ := hDense j i
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      (Metric.tendsto_nhds.mp hl (ε / 4) (by positivity))
    have hPair (n m : ℕ) (hn : N ≤ n) (hm : N ≤ m) :
        dist (T j n (u i)) (T j m (u i)) < ε / 2 := by
      have hn' := hN n hn
      have hm' := hN m hm
      rw [dist_comm] at hm'
      exact (dist_triangle _ l _).trans_lt (by linarith)
    have hClose (n : ℕ) : dist (T j n x) (T j n (u i)) ≤ ε / 4 := by
      rw [dist_eq_norm, ← map_sub]
      have hDist : ‖x - u i‖ ≤ δ := by simpa only [dist_eq_norm, dist_comm] using hi.le
      calc
        _ ≤ B j * ‖x - u i‖ := norm_apply_le _ (hL j (base (σ n))) _
        _ ≤ (B j + 1) * δ := mul_le_mul (by linarith) hDist (norm_nonneg _) (by linarith [hB j])
        _ = ε / 4 := by
          dsimp [δ]
          rw [mul_comm, div_mul_cancel₀ _ (by linarith [hB j])]
    refine ⟨N, fun n hn m hm => ?_⟩
    have hd := dist_triangle4 (T j n x) (T j n (u i)) (T j m (u i)) (T j m x)
    have hLast := hClose m
    rw [dist_comm] at hLast
    linarith only [hd, hClose n, hPair n m hn hm, hLast]
  choose f hf using fun j x => cauchySeq_tendsto_of_complete (hCauchy j x)
  have hBound (j : ℕ) (x : E) : ‖f j x‖ ≤ B j * ‖x‖ :=
    le_of_tendsto (hf j x).norm (Eventually.of_forall fun n => norm_apply_le _ (hL j (base (σ n))) _)
  let M (j : ℕ) : E →ₗ[ℝ] ℝ :=
    { toFun := f j
      map_add' := fun x y => tendsto_nhds_unique (hf j (x + y))
        (by simpa only [map_add] using (hf j x).add (hf j y))
      map_smul' := fun c x => tendsto_nhds_unique (hf j (c • x))
        (by simpa only [map_smul, RingHom.id_apply] using (hf j x).const_smul c) }
  refine ⟨σ, fun j => (M j).mkContinuous (B j) (hBound j), hσ, ?_, hf⟩
  intro j
  exact (M j).mkContinuous_norm_le (hB j) (hBound j)

end C2Riemannian
