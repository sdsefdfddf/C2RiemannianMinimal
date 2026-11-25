module

public import C2Riemannian.SmoothCompatibility

set_option autoImplicit false

open MeasureTheory Set TopologicalSpace
open scoped ContDiff ENNReal

namespace C2Riemannian.WeakJet2

variable {m : ℕ} {U : Opens Plane} (w : WeakJet2 m U)

public theorem lineDeriv_mollify {p q r : ℝ≥0∞}
    (hw : MemLp w.value p (volume.restrict (U : Set Plane)))
    (hP : MemLp w.gradient q (volume.restrict (U : Set Plane)))
    (hB : MemLp w.second r (volume.restrict (U : Set Plane)))
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (φ : ContDiffBump (0 : Plane)) (x d : Plane)
    (hx : Metric.closedBall x φ.rOut ⊆ (U : Set Plane)) :
    lineDeriv ℝ (mollify U φ w.value) x d = mollify U φ w.gradient x d :=
  ((w.mollify_derivatives hw hP hB hp hq hr φ x hx).1.hasLineDerivAt d).lineDeriv

/-- The classical Cartesian Hessian of the smooth mollified potential reads the
same zero-extended weak second field on its interior convolution domain. -/
public theorem classicalHessian_mollify {p q r : ℝ≥0∞}
    (hw : MemLp w.value p (volume.restrict (U : Set Plane)))
    (hP : MemLp w.gradient q (volume.restrict (U : Set Plane)))
    (hB : MemLp w.second r (volume.restrict (U : Set Plane)))
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (φ : ContDiffBump (0 : Plane)) (x : Plane)
    (hx : Metric.closedBall x φ.rOut ⊆ (U : Set Plane)) :
    let ex : Plane := EuclideanSpace.single 0 1
    let ey : Plane := EuclideanSpace.single 1 1
    classicalHessian (mollify U φ w.value) x =
      ⟨mollify U φ w.second x ex ex, mollify U φ w.second x ey ex,
        mollify U φ w.second x ey ey⟩ := by
  have hdiff := (contDiff_mollify hw hp φ).differentiable (by simp)
  have hline (a b : Plane) :
      lineDeriv ℝ (fun z => lineDeriv ℝ (mollify U φ w.value) z a) x b =
        mollify U φ w.second x b a := by
    have hcol : (fun z => lineDeriv ℝ (mollify U φ w.value) z a) =
        (fun z => fderiv ℝ (mollify U φ w.value) z a) := by
      funext z
      exact (hdiff z).lineDeriv_eq_fderiv
    rw [hcol]
    have hd := w.mollify_second hw hP hB hp hq hr φ x hx
    exact (((ContinuousLinearMap.apply ℝ (Target m) a).hasFDerivAt.comp x hd).hasLineDerivAt b).lineDeriv
  simp only [classicalHessian, hline]

end C2Riemannian.WeakJet2
