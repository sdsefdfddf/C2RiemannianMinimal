module

public import C2Riemannian.DerivativeLimit
public import C2Riemannian.HessianAlgebra
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff BoundedContinuousFunction

namespace C2Riemannian

/-- Cartesian Hessian entries in the Euclidean norm, equal to the Frobenius norm. -/
public abbrev DiskHessian := EuclideanSpace ℝ (Fin 2 × Fin 2)

/-- Cartesian Hessian coordinates acting on a direction. -/
@[expose] public noncomputable def diskHessianAction :
    DiskHessian →L[ℝ] (Plane →L[ℝ] Plane) :=
  let entries : DiskHessian →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
    { toFun := fun H i j => H (i, j)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  (LinearMap.toContinuousLinearMap.toLinearMap.comp
    (Matrix.toEuclideanLin.toLinearMap.comp entries)).toContinuousLinearMap

/-- The three continuous fields, with the product maximum of their sup norms. -/
public abbrev C2DiskFields (a : Plane) (R : ℝ) :=
  (Metric.closedBall a R →ᵇ ℝ) ×
    (Metric.closedBall a R →ᵇ Plane) × (Metric.closedBall a R →ᵇ DiskHessian)

@[expose] public noncomputable def diskFieldExtension {K : Set Plane} {F : Type*} [Zero F] (f : K → F) (x : Plane) : F := by
  classical
  exact if hx : x ∈ K then f ⟨x, hx⟩ else 0

public theorem diskFieldExtension_of_mem {K : Set Plane} {F : Type*} [Zero F]
    (f : K → F) {x : Plane} (hx : x ∈ K) : diskFieldExtension f x = f ⟨x, hx⟩ := by
  classical
  simp only [diskFieldExtension, dite_eq_left hx]

@[simp] private theorem diskFieldExtension_subtype {K : Set Plane} {F : Type*} [Zero F]
    (f : K → F) (x : K) : diskFieldExtension f x = f x := by simp [diskFieldExtension, x.property]

private theorem diskFieldExtension_add {K : Set Plane} {F : Type*} [AddZeroClass F]
    (f g : K → F) : diskFieldExtension (f + g) = diskFieldExtension f + diskFieldExtension g := by
  classical
  funext x
  by_cases h : x ∈ K <;> simp [diskFieldExtension, h]

private theorem diskFieldExtension_smul {K : Set Plane} {F : Type*} [AddCommMonoid F] [Module ℝ F]
    (c : ℝ) (f : K → F) : diskFieldExtension (c • f) = c • diskFieldExtension f := by
  classical
  funext x
  by_cases h : x ∈ K <;> simp [diskFieldExtension, h]

private theorem uniformOn_diskFieldExtension {K : Set Plane} {F : Type*}
    [NormedAddCommGroup F] {u : ℕ → K →ᵇ F} {v : K →ᵇ F}
    (h : Tendsto u atTop (𝓝 v)) :
    TendstoUniformlyOn (fun n => diskFieldExtension (u n)) (diskFieldExtension v) atTop K := by
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  simpa only [Function.comp_def, diskFieldExtension_subtype] using
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp h

/-- Interior Fréchet derivative relations and symmetry for a continuous disk jet. -/
@[expose] public def C2DiskFields.Compatible {a : Plane} {R : ℝ} (U : C2DiskFields a R) : Prop :=
  (∀ x (hx : x ∈ Metric.ball a R),
    HasFDerivAt (diskFieldExtension U.1) (innerSL ℝ (U.2.1 ⟨x, Metric.ball_subset_closedBall hx⟩)) x ∧
    HasFDerivAt (diskFieldExtension U.2.1) (diskHessianAction (U.2.2 ⟨x, Metric.ball_subset_closedBall hx⟩)) x) ∧
  ∀ x i j, U.2.2 x (i, j) = U.2.2 x (j, i)

/-- The disk jet submodule has the inherited maximum norm. -/
@[expose] public noncomputable def c2ClosedDiskSubmodule (a : Plane) (R : ℝ) :
    Submodule ℝ (C2DiskFields a R) where
  carrier := {u | u.Compatible}
  zero_mem' := by
    change C2DiskFields.Compatible (0 : C2DiskFields a R)
    constructor
    · intro x hx
      change HasFDerivAt (diskFieldExtension (0 : Metric.closedBall a R → ℝ)) (innerSL ℝ (0 : Plane)) x ∧
        HasFDerivAt (diskFieldExtension (0 : Metric.closedBall a R → Plane)) (diskHessianAction 0) x
      have hzero {F : Type} [Zero F] : diskFieldExtension (0 : Metric.closedBall a R → F) = 0 := by
        funext y
        simp [diskFieldExtension]
      rw [hzero, hzero, map_zero, map_zero]
      exact ⟨hasFDerivAt_const _ _, hasFDerivAt_const _ _⟩
    · intros
      rfl
  add_mem' := by
    intro u v hu hv
    change u.Compatible at hu
    change v.Compatible at hv
    constructor
    · intro x hx
      change HasFDerivAt (diskFieldExtension ((u.1 : Metric.closedBall a R → ℝ) + (v.1 : Metric.closedBall a R → ℝ))) _ x ∧
        HasFDerivAt (diskFieldExtension ((u.2.1 : Metric.closedBall a R → Plane) + (v.2.1 : Metric.closedBall a R → Plane))) _ x
      rw [diskFieldExtension_add, diskFieldExtension_add]
      refine ⟨?_, ?_⟩
      · change HasFDerivAt _ (innerSL ℝ (u.2.1 _ + v.2.1 _)) x
        rw [map_add]
        exact (hu.1 x hx).1.add (hv.1 x hx).1
      · change HasFDerivAt _ (diskHessianAction (u.2.2 _ + v.2.2 _)) x
        rw [map_add]
        exact (hu.1 x hx).2.add (hv.1 x hx).2
    · intro x i j
      change u.2.2 x (i, j) + v.2.2 x (i, j) = u.2.2 x (j, i) + v.2.2 x (j, i)
      rw [hu.2 x i j, hv.2 x i j]
  smul_mem' := by
    intro c u hu
    change u.Compatible at hu
    constructor
    · intro x hx
      change HasFDerivAt (diskFieldExtension (c • (u.1 : Metric.closedBall a R → ℝ))) _ x ∧
        HasFDerivAt (diskFieldExtension (c • (u.2.1 : Metric.closedBall a R → Plane))) _ x
      rw [diskFieldExtension_smul, diskFieldExtension_smul]
      refine ⟨?_, ?_⟩
      · change HasFDerivAt _ (innerSL ℝ (c • u.2.1 _)) x
        rw [map_smul]
        exact (hu.1 x hx).1.const_smul c
      · change HasFDerivAt _ (diskHessianAction (c • u.2.2 _)) x
        rw [map_smul]
        exact (hu.1 x hx).2.const_smul c
    · intro x i j
      change c • u.2.2 x (i, j) = c • u.2.2 x (j, i)
      rw [hu.2 x i j]

public theorem c2ClosedDisk_isClosed (a : Plane) (R : ℝ) :
    IsClosed ((c2ClosedDiskSubmodule a R : Submodule ℝ _) : Set (C2DiskFields a R)) := by
  rw [← isSeqClosed_iff_isClosed]
  intro u v hu hlim
  have hlimU : Tendsto (fun n => (u n).1) atTop (𝓝 v.1) :=
    (continuous_fst.tendsto v).comp hlim
  have hlimG : Tendsto (fun n => (u n).2.1) atTop (𝓝 v.2.1) :=
    ((continuous_fst.comp continuous_snd).tendsto v).comp hlim
  have hlimH : Tendsto (fun n => (u n).2.2) atTop (𝓝 v.2.2) :=
    ((continuous_snd.comp continuous_snd).tendsto v).comp hlim
  have hU := uniformOn_diskFieldExtension hlimU
  have hG := uniformOn_diskFieldExtension hlimG
  have hH := uniformOn_diskFieldExtension hlimH
  have hGD := (innerSL ℝ (E := Plane)).uniformContinuous.comp_tendstoUniformlyOn hG
  have hHD := diskHessianAction.uniformContinuous.comp_tendstoUniformlyOn hH
  have hFirst (x : Plane) (hx : x ∈ Metric.ball a R) := hasFDerivAt_of_tendstoLocallyUniformlyOn Metric.isOpen_ball
    (hGD.mono Metric.ball_subset_closedBall).tendstoLocallyUniformlyOn
    (fun n x hx => by
      simpa only [Function.comp_apply, diskFieldExtension_of_mem _ (Metric.ball_subset_closedBall hx)]
        using ((hu n).1 x hx).1)
    (fun x hx => hU.tendsto_at (Metric.ball_subset_closedBall hx)) hx
  have hSecond (x : Plane) (hx : x ∈ Metric.ball a R) := hasFDerivAt_of_tendstoLocallyUniformlyOn Metric.isOpen_ball
    (hHD.mono Metric.ball_subset_closedBall).tendstoLocallyUniformlyOn
    (fun n x hx => by
      simpa only [Function.comp_apply, diskFieldExtension_of_mem _ (Metric.ball_subset_closedBall hx)]
        using ((hu n).1 x hx).2)
    (fun x hx => hG.tendsto_at (Metric.ball_subset_closedBall hx)) hx
  change v.Compatible
  constructor
  · intro x hx
    have h₁ := hFirst x hx
    have h₂ := hSecond x hx
    simpa only [Function.comp_apply, diskFieldExtension_of_mem _ (Metric.ball_subset_closedBall hx)]
      using And.intro h₁ h₂
  · intro x i j
    have hA := (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlimH).tendsto_at x
    have hi := (EuclideanSpace.proj (i, j)).continuous.tendsto _ |>.comp hA
    have hj := (EuclideanSpace.proj (j, i)).continuous.tendsto _ |>.comp hA
    exact tendsto_nhds_unique_of_eventuallyEq hi hj (Eventually.of_forall fun n => (hu n).2 x i j)

/-- Real C² functions on a closed planar disk with continuous boundary jets. -/
public abbrev C2ClosedDisk (a : Plane) (R : ℝ) := ↥(c2ClosedDiskSubmodule a R)

public noncomputable instance C2ClosedDisk_complete (a : Plane) (R : ℝ) :
    CompleteSpace (C2ClosedDisk a R) := (c2ClosedDisk_isClosed a R).completeSpace_coe

public theorem C2ClosedDisk.norm_eq {a : Plane} {R : ℝ} (u : C2ClosedDisk a R) :
    ‖u‖ = max ‖u.1.1‖ (max ‖u.1.2.1‖ ‖u.1.2.2‖) := rfl

public theorem c2_ball_baire (a : Plane) (R : ℝ) :
    BaireSpace (Metric.ball (0 : C2ClosedDisk a R) (1 / 4000)) :=
  Metric.isOpen_ball.baireSpace

public theorem c2_ball_nonempty (a : Plane) (R : ℝ) :
    (Metric.ball (0 : C2ClosedDisk a R) (1 / 4000)).Nonempty :=
  ⟨0, Metric.mem_ball_self (by norm_num)⟩

end C2Riemannian
