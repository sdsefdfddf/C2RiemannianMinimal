module

public import C2Riemannian.WeakRepresentative
public import C2Riemannian.NormalizedCompactness
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.Linarith

/-! # Gluing classical representatives on the concentric disks of M03 -/

set_option autoImplicit false

open MeasureTheory Filter TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace C2Riemannian.WeakJet2

variable {m : ℕ}

/-- The concentric open disks corresponding to the compact disk exhaustion. -/
@[expose] public noncomputable def openDiskExhaustion (a : Plane) (r : ℝ) (j : ℕ) : Opens Plane :=
  ⟨Metric.ball a (r - 1 / ((j : ℝ) + 1)), Metric.isOpen_ball⟩

public theorem openDiskExhaustion_subset (a : Plane) (r : ℝ) (j : ℕ) :
    (openDiskExhaustion a r j : Set Plane) ⊆ Metric.ball a r :=
  Metric.ball_subset_closedBall.trans (diskExhaustion_subset a r j)

/-- A closed level fits strictly inside the next open level. -/
public theorem diskExhaustion_subset_open_succ (a : Plane) (r : ℝ) (j : ℕ) :
    diskExhaustion a r j ⊆ (openDiskExhaustion a r (j + 1) : Set Plane) := by
  intro x hx
  have hr : r - 1 / ((j : ℝ) + 1) < r - 1 / (((j + 1 : ℕ) : ℝ) + 1) := by
    rw [Nat.cast_add, Nat.cast_one]
    have h₁ : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have h₂ : (j : ℝ) + 1 < (j : ℝ) + 1 + 1 := lt_add_of_pos_right _ zero_lt_one
    exact sub_lt_sub_left (one_div_lt_one_div_of_lt h₁ h₂) _
  exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hx).trans_lt hr)

public theorem exists_openDiskExhaustion_of_mem {a x : Plane} {r : ℝ}
    (hx : x ∈ Metric.ball a r) : ∃ j, x ∈ (openDiskExhaustion a r j : Set Plane) := by
  obtain ⟨j, hj⟩ := diskExhaustion_covers_compacts a r {x}
    (singleton_subset_iff.mpr hx) isCompact_singleton
  exact ⟨j + 1, diskExhaustion_subset_open_succ a r j (hj (mem_singleton x))⟩

/-- Equality almost everywhere on an open overlap determines the same classical
value wherever both representatives are continuous. -/
private theorem eqOn_inter_of_rep {E : Type*} [TopologicalSpace E] [T2Space E]
    {s t : Set Plane} (hs : IsOpen s) (ht : IsOpen t) {f g u : Plane → E}
    (hf : ContinuousOn f s) (hg : ContinuousOn g t)
    (hfu : f =ᵐ[volume.restrict s] u) (hgu : g =ᵐ[volume.restrict t] u) :
    EqOn f g (s ∩ t) := by
  have hfs : f =ᵐ[volume.restrict (s ∩ t)] u :=
    ae_mono (Measure.restrict_mono inter_subset_left le_rfl) hfu
  have hgt : g =ᵐ[volume.restrict (s ∩ t)] u :=
    ae_mono (Measure.restrict_mono inter_subset_right le_rfl) hgu
  exact Measure.eqOn_open_of_ae_eq (hfs.trans hgt.symm) (hs.inter ht)
    (hf.mono inter_subset_left) (hg.mono inter_subset_right)

/-- Glue the weak jet on a planar disk using local essential bounds on the
value and gradient, and a single Frobenius bound on the entire disk. -/
public theorem exists_classical_representative_on_disk (a : Plane) (r : ℝ)
    (w : WeakJet2 m (⟨Metric.ball a r, Metric.isOpen_ball⟩ : Opens Plane))
    (M₀ M₁ : ℕ → ℝ≥0) (K : ℝ≥0)
    (hw : ∀ j, MemLp w.value ∞ (volume.restrict (openDiskExhaustion a r j : Set Plane)))
    (hP : ∀ j, MemLp w.gradient ∞ (volume.restrict (openDiskExhaustion a r j : Set Plane)))
    (hB : ∀ j, MemLp w.second ∞ (volume.restrict (openDiskExhaustion a r j : Set Plane)))
    (hValue : ∀ j, ∀ᵐ x ∂volume.restrict (openDiskExhaustion a r j : Set Plane), ‖w.value x‖ ≤ (M₀ j : ℝ))
    (hGradient : ∀ j, ∀ᵐ x ∂volume.restrict (openDiskExhaustion a r j : Set Plane),
      gradHS (w.gradient x) ≤ (M₁ j : ℝ))
    (hHessian : ∀ᵐ x ∂volume.restrict (Metric.ball a r), (w.hessian x).frobenius ≤ (K : ℝ)) :
    ∃ (W : Plane → Target m) (P : Plane → Plane →L[ℝ] Target m),
      ContDiffOn ℝ 1 W (Metric.ball a r) ∧
      (∀ x ∈ Metric.ball a r, HasFDerivAt W (P x) x) ∧
      (∀ x ∈ Metric.ball a r, ∀ y ∈ Metric.ball a r, gradHS (P x - P y) ≤ (K : ℝ) * dist x y) ∧
      W =ᵐ[volume.restrict (Metric.ball a r)] w.value ∧
      P =ᵐ[volume.restrict (Metric.ball a r)] w.gradient := by
  classical
  let V (j : ℕ) := openDiskExhaustion a r j
  have hSub j : (V j : Set Plane) ⊆ Metric.ball a r := openDiskExhaustion_subset a r j
  have hClosed j : diskExhaustion a r j ⊆ (V (j + 1) : Set Plane) :=
    diskExhaustion_subset_open_succ a r j
  have hLocal (j : ℕ) :
      ∃ (W : Plane → Target m) (P : Plane → Plane →L[ℝ] Target m),
        ContDiffOn ℝ 1 W (V j : Set Plane) ∧
        (∀ x ∈ (V j : Set Plane), HasFDerivAt W (P x) x) ∧
        (∀ x ∈ diskExhaustion a r j, ∀ y ∈ diskExhaustion a r j,
          gradHS (P x - P y) ≤ (K : ℝ) * dist x y) ∧
        W =ᵐ[volume.restrict (V j : Set Plane)] w.value ∧
        P =ᵐ[volume.restrict (V j : Set Plane)] w.gradient := by
    let wj := w.restrict (V := V (j + 1)) (hSub (j + 1))
    have hHj : ∀ᵐ x ∂volume.restrict (V (j + 1) : Set Plane), (wj.hessian x).frobenius ≤ (K : ℝ) :=
      ae_mono (Measure.restrict_mono (hSub (j + 1)) le_rfl) hHessian
    exact wj.exists_classical_representative_on_ball a (r - 1 / ((j : ℝ) + 1)) (hClosed j)
      (hw (j + 1)) (hP (j + 1)) (hB (j + 1)) (M₀ (j + 1)) (M₁ (j + 1)) K
      (hValue (j + 1)) (hGradient (j + 1)) hHj
  choose Wj Pj hSmooth hDeriv hLip hAew hAep using hLocal
  have hpCont (j : ℕ) : ContinuousOn (Pj j) (V j : Set Plane) := by
    apply (LipschitzOnWith.of_dist_le_mul (K := K) (s := (V j : Set Plane)) ?_).continuousOn
    intro x hx y hy
    rw [dist_eq_norm]
    exact (opNorm_le_gradHS _).trans (hLip j _ (Metric.ball_subset_closedBall hx)
      _ (Metric.ball_subset_closedBall hy))
  have hAgreeW (i j : ℕ) : EqOn (Wj i) (Wj j) ((V i : Set Plane) ∩ (V j : Set Plane)) :=
    eqOn_inter_of_rep (V i).isOpen (V j).isOpen (hSmooth i).continuousOn
      (hSmooth j).continuousOn (hAew i) (hAew j)
  have hAgreeP (i j : ℕ) : EqOn (Pj i) (Pj j) ((V i : Set Plane) ∩ (V j : Set Plane)) :=
    eqOn_inter_of_rep (V i).isOpen (V j).isOpen (hpCont i) (hpCont j) (hAep i) (hAep j)
  have hCover (x : Plane) (hx : x ∈ Metric.ball a r) : ∃ j, x ∈ (V j : Set Plane) :=
    exists_openDiskExhaustion_of_mem hx
  let W (x : Plane) := if hx : x ∈ Metric.ball a r then Wj (hCover x hx).choose x else 0
  let P (x : Plane) := if hx : x ∈ Metric.ball a r then Pj (hCover x hx).choose x else 0
  have hWj (j : ℕ) : EqOn W (Wj j) (V j : Set Plane) := by
    intro x hx
    have hxΩ := hSub j hx
    change (if h : x ∈ Metric.ball a r then Wj (hCover x h).choose x else 0) = Wj j x
    rw [dite_eq_left hxΩ]
    exact hAgreeW _ j ⟨(hCover x hxΩ).choose_spec, hx⟩
  have hPj (j : ℕ) : EqOn P (Pj j) (V j : Set Plane) := by
    intro x hx
    have hxΩ := hSub j hx
    change (if h : x ∈ Metric.ball a r then Pj (hCover x h).choose x else 0) = Pj j x
    rw [dite_eq_left hxΩ]
    exact hAgreeP _ j ⟨(hCover x hxΩ).choose_spec, hx⟩
  refine ⟨W, P, ?_, ?_, ?_, ?_, ?_⟩
  · apply contDiffOn_of_locally_contDiffOn
    intro x hx
    obtain ⟨j, hxj⟩ := hCover x hx
    exact ⟨V j, (V j).isOpen, hxj, ((hSmooth j).congr (hWj j)).mono inter_subset_right⟩
  · intro x hx
    obtain ⟨j, hxj⟩ := hCover x hx
    rw [hPj j hxj]
    exact (hDeriv j x hxj).congr_of_eventuallyEq
      (Filter.eventually_of_mem ((V j).isOpen.mem_nhds hxj) (hWj j))
  · intro x hx y hy
    have hxy : ({x, y} : Set Plane) ⊆ Metric.ball a r := by
      simp only [insert_subset_iff, singleton_subset_iff]
      exact ⟨hx, hy⟩
    obtain ⟨j, hj⟩ := diskExhaustion_covers_compacts a r {x, y} hxy
      (isCompact_singleton.insert x)
    have hxj : x ∈ diskExhaustion a r j := hj (mem_insert x _)
    have hyj : y ∈ diskExhaustion a r j := hj (mem_insert_of_mem x (mem_singleton y))
    have hx' : x ∈ diskExhaustion a r (j + 1) := Metric.ball_subset_closedBall (hClosed j hxj)
    have hy' : y ∈ diskExhaustion a r (j + 1) := Metric.ball_subset_closedBall (hClosed j hyj)
    rw [hPj (j + 1) (hClosed j hxj), hPj (j + 1) (hClosed j hyj)]
    exact hLip (j + 1) x hx' y hy'
  · have hAll : ∀ᵐ x ∂(volume : Measure Plane), ∀ j, x ∈ (V j : Set Plane) → Wj j x = w.value x :=
      ae_all_iff.mpr fun j => ae_imp_of_ae_restrict (hAew j)
    filter_upwards [ae_restrict_of_ae hAll, ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hΩ
    obtain ⟨j, hxj⟩ := hCover x hΩ
    exact (hWj j hxj).trans (hx j hxj)
  · have hAll : ∀ᵐ x ∂(volume : Measure Plane), ∀ j, x ∈ (V j : Set Plane) → Pj j x = w.gradient x :=
      ae_all_iff.mpr fun j => ae_imp_of_ae_restrict (hAep j)
    filter_upwards [ae_restrict_of_ae hAll, ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hΩ
    obtain ⟨j, hxj⟩ := hCover x hΩ
    exact (hPj j hxj).trans (hx j hxj)

end C2Riemannian.WeakJet2
