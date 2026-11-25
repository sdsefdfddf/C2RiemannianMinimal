module

public import C2Riemannian.FlatTorusMetric
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.LinearAlgebra.BilinearMap

set_option autoImplicit false

open TopologicalSpace
open scoped ContDiff

namespace C2Riemannian

open TorusDiskGeometry

/-- A C² Riemannian metric on the two-torus, expressed in its global parallel frame. -/
public structure C2TorusMetric where
  form : FlatTorus → LinearMap.BilinForm ℝ Plane
  symmetric : ∀ q X Y, form q X Y = form q Y X
  positive : ∀ q X, X ≠ 0 → 0 < form q X X
  contDiff : ∀ X Y, ContDiff ℝ 2 (fun x => form (torusProjection x) X Y)

/-- The pullback of the Euclidean inner product in the parallel frame. -/
@[expose] public def C2TorusMetric.HasIsometricDifferential {m : ℕ}
    (g : C2TorusMetric) (F : FlatTorus → Target m) : Prop :=
  ∀ x X Y,
    let D := fderiv ℝ (F ∘ torusProjection) x
    inner ℝ (D X) (D Y) = g.form (torusProjection x) X Y

/-- A C¹ map with locally Lipschitz derivative and an isometric differential. -/
@[expose] public def C2TorusMetric.IsC11IsometricImmersion {m : ℕ}
    (g : C2TorusMetric) (F : FlatTorus → Target m) : Prop :=
  ContDiff ℝ 1 (F ∘ torusProjection) ∧
    LocallyLipschitz (fderiv ℝ (F ∘ torusProjection)) ∧ g.HasIsometricDifferential F

/-- A C² map whose differential pulls back the Euclidean inner product to the metric. -/
@[expose] public def C2TorusMetric.IsC2IsometricImmersion {m : ℕ}
    (g : C2TorusMetric) (F : FlatTorus → Target m) : Prop :=
  ContDiff ℝ 2 (F ∘ torusProjection) ∧ g.HasIsometricDifferential F

/-- A C² isometric immersion that is a topological embedding. -/
@[expose] public def C2TorusMetric.IsC2IsometricEmbedding {m : ℕ}
    (g : C2TorusMetric) (F : FlatTorus → Target m) : Prop :=
  Topology.IsEmbedding F ∧ g.IsC2IsometricImmersion F

/-- A C¹,¹ isometric immersion on an open neighborhood in a centered flat chart. -/
@[expose] public def C2TorusMetric.HasLocalC11IsometricImmersion
    (g : C2TorusMetric) (o : FlatTorus) (m : ℕ) : Prop :=
  ∃ a : Plane, torusProjection a = o ∧
    ∃ U : Opens Plane, (0 : Plane) ∈ (U : Set Plane) ∧
      (U : Set Plane) ⊆ Metric.ball 0 (1 / 4) ∧
      ∃ W : Plane → Target m, ContDiffOn ℝ 1 W (U : Set Plane) ∧
        LocallyLipschitzOn (U : Set Plane) (fderiv ℝ W) ∧
        ∀ x ∈ (U : Set Plane), ∀ X Y,
          let D := fderiv ℝ W x
          inner ℝ (D X) (D Y) = g.form (torusProjection (a + x)) X Y

public theorem C2TorusMetric.IsC2IsometricImmersion.isC11IsometricImmersion {m : ℕ}
    {g : C2TorusMetric} {F : FlatTorus → Target m}
    (h : g.IsC2IsometricImmersion F) : g.IsC11IsometricImmersion F := by
  have hGrad : ContDiff ℝ 1 (fderiv ℝ (F ∘ torusProjection)) :=
    h.1.fderiv_right (by decide)
  exact ⟨h.1.of_le (by decide), hGrad.locallyLipschitz, h.2⟩

public theorem C2TorusMetric.IsC11IsometricImmersion.hasLocal {m : ℕ}
    {g : C2TorusMetric} {F : FlatTorus → Target m}
    (h : g.IsC11IsometricImmersion F) (o : FlatTorus) :
    g.HasLocalC11IsometricImmersion o m := by
  obtain ⟨a, ha⟩ := torusProjection_openQuotient.surjective o
  let U : Opens Plane := ⟨Metric.ball 0 (1 / 4), Metric.isOpen_ball⟩
  let W : Plane → Target m := fun x => F (torusProjection (a + x))
  have hShift : ContDiff ℝ 1 (fun x : Plane => a + x) := contDiff_const.add contDiff_id
  have hGrad : fderiv ℝ W = fderiv ℝ (F ∘ torusProjection) ∘ (fun x => a + x) := by
    funext x
    exact fderiv_comp_add_left (f := fun y => F (torusProjection y)) a
  refine ⟨a, ha, U, Metric.mem_ball_self (by norm_num), Set.Subset.rfl, W,
    (h.1.comp hShift).contDiffOn, ?_, ?_⟩
  · rw [hGrad]
    exact (h.2.1.comp hShift.locallyLipschitz).locallyLipschitzOn
  · intro x _ X Y
    dsimp only
    rw [hGrad]
    exact h.2.2 (a + x) X Y

end C2Riemannian
