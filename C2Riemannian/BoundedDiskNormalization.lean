module

public import C2Riemannian.DiskWeakNormalization
public import C2Riemannian.WeakSecondOperatorBound
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open MeasureTheory TopologicalSpace Set
open scoped ENNReal NNReal

namespace C2Riemannian.WeakJet2

variable {m : ℕ}

private theorem exists_ae_norm_bound {E : Type*} [NormedAddCommGroup E]
    {f : Plane → E} {μ : Measure Plane} (hf : MemLp f ∞ μ) :
    ∃ C : ℝ≥0, ∀ᵐ x ∂μ, ‖f x‖ ≤ (C : ℝ) := by
  have h : eLpNormEssSup f μ < ⊤ := by
    simpa only [eLpNorm_exponent_top hf.aestronglyMeasurable] using hf.eLpNorm_lt_top
  exact eLpNormEssSup_lt_top_iff_isBoundedUnder.mp h

private theorem gradHS_le_bound (A : Plane →L[ℝ] Target m) (C : ℝ≥0)
    (hA : ‖A‖ ≤ (C : ℝ)) : gradHS A ≤ ((2 * C : ℝ≥0) : ℝ) := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  have hb (i : Fin 2) : ‖A (b i)‖ ≤ (C : ℝ) := by
    calc
      ‖A (b i)‖ ≤ ‖A‖ * ‖b i‖ := A.le_opNorm _
      _ = ‖A‖ := by rw [b.orthonormal.norm_eq_one i, mul_one]
      _ ≤ _ := hA
  have hs (i : Fin 2) : ‖A (b i)‖ ^ 2 ≤ (C : ℝ) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hb i) 2
  change √(∑ i : Fin 2, ‖A (b i)‖ ^ 2) ≤ _
  rw [Fin.sum_univ_two, NNReal.coe_mul, NNReal.coe_ofNat]
  apply (Real.sqrt_le_iff).2
  exact ⟨mul_nonneg (by norm_num) C.coe_nonneg,
    by nlinarith [hs 0, hs 1, sq_nonneg (C : ℝ)]⟩

/-- A locally bounded disk jet admits a normalized classical representative with the same Hessian. -/
public theorem exists_normalized_locally_bounded_disk_weakJet (a : Plane) (r : ℝ) (hr : 0 < r)
    (w : WeakJet2 m (⟨Metric.ball a r, Metric.isOpen_ball⟩ : Opens Plane)) (K : ℝ≥0)
    (hw : ∀ j, MemLp w.value ∞ (volume.restrict (openDiskExhaustion a r j : Set Plane)))
    (hP : ∀ j, MemLp w.gradient ∞ (volume.restrict (openDiskExhaustion a r j : Set Plane)))
    (hK : ∀ᵐ x ∂volume.restrict (Metric.ball a r), (w.hessian x).frobenius ≤ (K : ℝ)) :
    ∃ v : WeakJet2 m (⟨Metric.ball a r, Metric.isOpen_ball⟩ : Opens Plane),
      v.gradient = fderiv ℝ v.value ∧ v.second = w.second ∧ v.hessian = w.hessian ∧
      ContDiffOn ℝ 1 v.value (Metric.ball a r) ∧ v.value a = 0 ∧ v.gradient a = 0 ∧
      (∀ x ∈ Metric.ball a r, ‖v.value x‖ ≤ (K : ℝ) * dist x a ^ 2 / 2) ∧
      (∀ x ∈ Metric.ball a r, gradHS (v.gradient x) ≤ (K : ℝ) * dist x a) ∧
      (∀ x ∈ Metric.ball a r, ∀ y ∈ Metric.ball a r,
        gradHS (v.gradient x - v.gradient y) ≤ (K : ℝ) * dist x y) := by
  choose C₀ h₀ using fun j => exists_ae_norm_bound (hw j)
  choose C₁ h₁ using fun j => exists_ae_norm_bound (hP j)
  have hB := w.second_memLp_top_of_frobenius_ae_le hK
  have hsub (j : ℕ) : volume.restrict (openDiskExhaustion a r j : Set Plane) ≤
      volume.restrict (Metric.ball a r) :=
    Measure.restrict_mono (openDiskExhaustion_subset a r j) le_rfl
  obtain ⟨W, P, hW, hD, hLip, hRep, _⟩ :=
    w.exists_classical_representative_on_disk a r C₀ (fun j => 2 * C₁ j) K hw hP
      (fun j => hB.mono_measure (hsub j)) h₀
      (fun j => (h₁ j).mono fun x hx => gradHS_le_bound (w.gradient x) (C₁ j) hx) hK
  obtain ⟨v, _, hv⟩ := w.exists_normalized_disk_weakJet a r hr hW hD hRep K hLip
  exact ⟨v, hv⟩

/-- A bounded disk jet admits a normalized classical representative with the same Hessian. -/
public theorem exists_normalized_bounded_disk_weakJet (a : Plane) (r : ℝ) (hr : 0 < r)
    (w : WeakJet2 m (⟨Metric.ball a r, Metric.isOpen_ball⟩ : Opens Plane)) (K : ℝ≥0)
    (hw : MemLp w.value ∞ (volume.restrict (Metric.ball a r)))
    (hP : MemLp w.gradient ∞ (volume.restrict (Metric.ball a r)))
    (hK : ∀ᵐ x ∂volume.restrict (Metric.ball a r), (w.hessian x).frobenius ≤ (K : ℝ)) :
    ∃ v : WeakJet2 m (⟨Metric.ball a r, Metric.isOpen_ball⟩ : Opens Plane),
      v.gradient = fderiv ℝ v.value ∧ v.second = w.second ∧ v.hessian = w.hessian ∧
      ContDiffOn ℝ 1 v.value (Metric.ball a r) ∧ v.value a = 0 ∧ v.gradient a = 0 ∧
      (∀ x ∈ Metric.ball a r, ‖v.value x‖ ≤ (K : ℝ) * dist x a ^ 2 / 2) ∧
      (∀ x ∈ Metric.ball a r, gradHS (v.gradient x) ≤ (K : ℝ) * dist x a) ∧
      (∀ x ∈ Metric.ball a r, ∀ y ∈ Metric.ball a r,
        gradHS (v.gradient x - v.gradient y) ≤ (K : ℝ) * dist x y) :=
  w.exists_normalized_locally_bounded_disk_weakJet a r hr K
    (fun j => hw.mono_measure (Measure.restrict_mono (openDiskExhaustion_subset a r j) le_rfl))
    (fun j => hP.mono_measure (Measure.restrict_mono (openDiskExhaustion_subset a r j) le_rfl)) hK

end C2Riemannian.WeakJet2

