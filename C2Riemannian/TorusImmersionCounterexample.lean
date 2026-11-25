module

public import C2Riemannian.TorusCounterexample
public import C2Riemannian.TorusIsometricEmbedding
import C2Riemannian.ClassicalC11ImmersionJet
import Mathlib.Tactic.Ring

set_option autoImplicit false

open MeasureTheory
open scoped ContDiff

namespace C2Riemannian

open TorusDiskGeometry

private noncomputable def torusBilinForm (f : Plane → ℝ) (o q : FlatTorus) :
    LinearMap.BilinForm ℝ Plane :=
  LinearMap.mk₂ ℝ (torusMetricForm f o q)
    (by intros; simp only [torusMetricForm, PiLp.add_apply]; ring)
    (by intros; simp only [torusMetricForm, PiLp.smul_apply, smul_eq_mul]; ring)
    (by intros; simp only [torusMetricForm, PiLp.add_apply]; ring)
    (by intros; simp only [torusMetricForm, PiLp.smul_apply, smul_eq_mul]; ring)

/-- For any specified point of the two-torus, some C² Riemannian metric has
no local C¹,¹ isometric immersion there into any finite-dimensional Euclidean space. -/
public theorem exists_c2_torus_metric_not_locally_c11_isometrically_immersible (o : FlatTorus) :
    ∃ g : C2TorusMetric, ¬ ∃ m : ℕ, g.HasLocalC11IsometricImmersion o m := by
  obtain ⟨f, _, _, hC2, _, hPos, _, _, hNoLocal, _⟩ :=
    theorem_A o (ε := 1) zero_lt_one
  let g : C2TorusMetric :=
    { form := torusBilinForm f o
      symmetric := by
        intro q X Y
        simp only [torusBilinForm, LinearMap.mk₂_apply, torusMetricForm]
        ring
      positive := hPos
      contDiff := by
        intro X Y
        exact (((contDiff_const.add hC2).mul contDiff_const).mul contDiff_const).add
          contDiff_const }
  refine ⟨g, ?_⟩
  rintro ⟨m, a, ha, U, h0, hU, W, hC1, hLip, hIso⟩
  have hGram (x : Plane) (hx : x ∈ (U : Set Plane)) :
      let D := fderiv ℝ W x
      inner ℝ (D WeakJet2.ex) (D WeakJet2.ex) = 1 + centeredCoefficient f o a x ∧
      inner ℝ (D WeakJet2.ey) (D WeakJet2.ey) = 1 ∧
      inner ℝ (D WeakJet2.ex) (D WeakJet2.ey) = 0 := by
    dsimp only
    refine ⟨?_, ?_, ?_⟩
    · simpa [g, torusBilinForm, torusMetricForm, centeredCoefficient, WeakJet2.ex,
        PiLp.single_apply] using hIso x hx WeakJet2.ex WeakJet2.ex
    · simpa [g, torusBilinForm, torusMetricForm, WeakJet2.ey, PiLp.single_apply]
        using hIso x hx WeakJet2.ey WeakJet2.ey
    · simpa [g, torusBilinForm, torusMetricForm, WeakJet2.ex, WeakJet2.ey,
        PiLp.single_apply] using hIso x hx WeakJet2.ex WeakJet2.ey
  cases m with
  | zero =>
      let D := fderiv ℝ W 0
      have hYY : inner ℝ (D WeakJet2.ey) (D WeakJet2.ey) = 1 := (hGram 0 h0).2.1
      have hZero : D WeakJet2.ey = 0 := Subsingleton.elim _ _
      exact zero_ne_one (by simpa only [hZero, inner_zero_left] using hYY)
  | succ m =>
      let w := weakJet2_of_contDiffOn_locallyLipschitz hC1 hLip
      have hBound : w.LocallyBoundedOnCompacts :=
        weakJet2_of_contDiffOn_locallyLipschitz_locallyBounded hC1 hLip
      apply hNoLocal m.succ m.succ_pos
      refine ⟨a, ha, U, h0, hU, w, hBound, ?_⟩
      unfold WeakJet2.IsometryInChart
      exact (ae_restrict_mem U.isOpen.measurableSet).mono fun x hx => hGram x hx

/-- Some C² metric on the two-torus has no global C¹,¹ isometric immersion. -/
public theorem exists_c2_torus_metric_not_c11_isometrically_immersible :
    ∃ g : C2TorusMetric,
      ¬ ∃ (m : ℕ) (F : FlatTorus → Target m), g.IsC11IsometricImmersion F := by
  obtain ⟨g, hNoLocal⟩ := exists_c2_torus_metric_not_locally_c11_isometrically_immersible 0
  refine ⟨g, ?_⟩
  rintro ⟨m, F, hF⟩
  exact hNoLocal ⟨m, hF.hasLocal 0⟩

/-- The same obstruction excludes C² isometric immersions. -/
public theorem exists_c2_torus_metric_not_c2_isometrically_immersible :
    ∃ g : C2TorusMetric,
      ¬ ∃ (m : ℕ) (F : FlatTorus → Target m), g.IsC2IsometricImmersion F := by
  obtain ⟨g, hNoImmersion⟩ := exists_c2_torus_metric_not_c11_isometrically_immersible
  refine ⟨g, ?_⟩
  rintro ⟨m, F, hF⟩
  exact hNoImmersion ⟨m, F, hF.isC11IsometricImmersion⟩

/-- Some C² metric on the two-torus has no C² isometric embedding. -/
public theorem exists_c2_torus_metric_not_isometrically_embeddable :
    ∃ g : C2TorusMetric,
      ¬ ∃ (m : ℕ) (F : FlatTorus → Target m), g.IsC2IsometricEmbedding F := by
  obtain ⟨g, hNoImmersion⟩ := exists_c2_torus_metric_not_c2_isometrically_immersible
  refine ⟨g, ?_⟩
  rintro ⟨m, F, hF⟩
  exact hNoImmersion ⟨m, F, hF.2⟩

end C2Riemannian
