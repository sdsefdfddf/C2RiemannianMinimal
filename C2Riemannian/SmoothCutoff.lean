module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false

open Set

namespace C2Riemannian

/-- An interior compact set has a smooth cutoff equal to one on an open
neighborhood and supported in the ambient open set. -/
public theorem exists_compact_inner_cutoff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {C Ω : Set E}
    (hC : IsCompact C) (hΩ : IsOpen Ω) (hSub : C ⊆ Ω) :
    ∃ (χ : E → ℝ) (V : Set E), ContDiff ℝ (↑(⊤ : ℕ∞)) χ ∧
      HasCompactSupport χ ∧ tsupport χ ⊆ Ω ∧ (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧
      IsOpen V ∧ C ⊆ V ∧ ∀ x ∈ V, χ x = 1 := by
  let _ : ProperSpace E := FiniteDimensional.proper ℝ E
  obtain ⟨r, hr, hInside⟩ := hC.exists_cthickening_subset_open hΩ hSub
  let D := Metric.cthickening (r / 2) C
  let V := Metric.thickening (r / 2) C
  have hHalf : r / 2 < r := half_lt_self hr
  have hD : D ⊆ Metric.thickening r C := Metric.cthickening_subset_thickening' hr hHalf C
  obtain ⟨χ, hSmooth, hRange, hSupport, hOne⟩ := exists_contDiff_support_eq_eq_one_iff
    Metric.isOpen_thickening (Metric.isClosed_cthickening (E := C) (δ := r / 2)) hD
  have hTsupport : tsupport χ ⊆ Metric.cthickening r C := by
    simpa only [tsupport, hSupport] using Metric.closure_thickening_subset_cthickening r C
  refine ⟨χ, V, hSmooth, ?_, hTsupport.trans hInside, fun x => hRange (mem_range_self x),
    Metric.isOpen_thickening, ?_, fun x hx => (hOne x).mp (Metric.thickening_subset_cthickening _ _ hx)⟩
  · exact (hC.cthickening (r := r)).of_isClosed_subset (isClosed_tsupport χ) hTsupport
  · exact Metric.self_subset_thickening (half_pos hr) C

end C2Riemannian

