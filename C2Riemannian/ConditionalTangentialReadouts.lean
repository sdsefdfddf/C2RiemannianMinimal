module

public import C2Riemannian.CompactTangentialConstraint
public import C2Riemannian.WeakHessianReadouts
public import C2Riemannian.TangentialForm
public import C2Riemannian.IdealLayerRealization
import C2Riemannian.ConditionalRiesz
import C2Riemannian.WeakSmoothTesting
import Mathlib.Tactic.FinCases

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions Topology ENNReal

namespace C2Riemannian

open WeakJet2 (ex ey)

namespace HessianBall

variable {m : ℕ} {K : ℝ}

/-- Conditional means of the three vector entries of a symmetric Hessian. -/
@[expose] public noncomputable def meanHessian (L : PositiveFunctional (HessianBall m K)) : Hess3 m :=
  ⟨L.mean xx, L.mean xy, L.mean yy⟩

/-- The vector readout of the first Cartesian Hessian column applied to `τ`. -/
@[expose] public noncomputable def tangentX (τ : Plane) : C(HessianBall m K, Target m) :=
  τ 0 • xx + τ 1 • xy

/-- The vector readout of the second Cartesian Hessian column applied to `τ`. -/
@[expose] public noncomputable def tangentY (τ : Plane) : C(HessianBall m K, Target m) :=
  τ 0 • xy + τ 1 • yy

private theorem mean_tangentX (L : PositiveFunctional (HessianBall m K)) (τ : Plane) (c : Fin m) :
    L (PositiveFunctional.coord (tangentX τ) c) = ((meanHessian L).applyRows (τ 0) (τ 1)).1 c := by
  have h : PositiveFunctional.coord (tangentX (K := K) τ) c =
      τ 0 • PositiveFunctional.coord xx c + τ 1 • PositiveFunctional.coord xy c := by
    ext x
    rfl
  rw [h, map_add, map_smul, map_smul]
  rfl

private theorem mean_tangentY (L : PositiveFunctional (HessianBall m K)) (τ : Plane) (c : Fin m) :
    L (PositiveFunctional.coord (tangentY τ) c) = ((meanHessian L).applyRows (τ 0) (τ 1)).2 c := by
  have h : PositiveFunctional.coord (tangentY (K := K) τ) c =
      τ 0 • PositiveFunctional.coord xy c + τ 1 • PositiveFunctional.coord yy c := by
    ext x
    rfl
  rw [h, map_add, map_smul, map_smul]
  rfl

end HessianBall

private theorem tangent_coordinates (τ : Plane) : τ = τ 0 • ex + τ 1 • ey := by
  ext i
  fin_cases i <;> simp [ex, ey, EuclideanSpace.single]

private theorem second_tangent_coordinates {m : ℕ} {U : Opens Plane} (w : WeakJet2 m U)
    (τ : Plane) : ∀ᵐ x ∂volume.restrict (U : Set Plane),
    (w.hessian x).applyRows (τ 0) (τ 1) = (w.second x τ ex, w.second x τ ey) := by
  filter_upwards [w.hessian_xy_ae] with x hxy
  have h (v : Plane) : w.second x τ v = τ 0 • w.second x ex v + τ 1 • w.second x ey v := by
    calc
      w.second x τ v = w.second x (τ 0 • ex + τ 1 • ey) v :=
        congrArg (fun u => w.second x u v) (tangent_coordinates τ)
      _ = _ := by rw [map_add, map_smul, map_smul]; rfl
  rw [h ex, h ey]
  change (τ 0 • w.second x ex ex + τ 1 • w.second x ey ex,
    τ 0 • (w.hessian x).xy + τ 1 • w.second x ey ey) = _
  rw [hxy]

namespace PhysicalLayerRow

variable {Q : Set Plane} {directions : PhysicalDirections} {s δ : ℝ}
  {layer : IdealLayer} {p : PhysicalPrefix Q} {next : ℕ → PhysicalPrefix Q}

/-- Both phase means share the parent Hessian's two tangential readouts, on a
single full-measure subset of the parent plateau. -/
public theorem conditional_phase_mean_tangent_ae {m : ℕ} {K R : ℝ} {a : Plane}
    (row : PhysicalLayerRow directions s δ layer p next) (i : p.Active)
    (hn : directions.normal layer s ≠ 0) (k : ℕ → ℕ) (hk : StrictMono k)
    (τ : Plane) (hτ : inner ℝ (directions.normal layer s) τ = 0)
    (hp : p.platform i.1 ⊆ Metric.ball a R)
    {U : Opens Plane} (hU : parentOpen p i ≤ U)
    (w : ℕ → WeakJet2 m U) (w₀ : WeakJet2 m U)
    (hgc : ∀ j, ContinuousOn (w j).gradient (p.platform i.1))
    (hgc₀ : ContinuousOn w₀.gradient (p.platform i.1))
    (hgu : ∀ n, TendstoUniformlyOn (fun j => (w j).gradient) w₀.gradient atTop
      (diskExhaustion a R n))
    (state : ℕ → Plane → HessianBall m K)
    (hState : ∀ j, ∀ᵐ x ∂volume.restrict (U : Set Plane),
      (state j x).val = ((w j).hessian x).coordinates)
    (L : Bool → Plane → PositiveFunctional (HessianBall m K))
    (hL : ∀ sign f, Measurable (fun x => L sign x f))
    (hPair : ∀ sign f (γ : Plane → ℝ), IntegrableOn γ (p.platform i.1) volume →
      Tendsto (fun j => ∫ x in p.platform i.1, row.phaseWeight i sign (k j) x * f (state j x) * γ x)
        atTop (𝓝 (∫ x in p.platform i.1, L sign x f * γ x))) :
    ∀ᵐ x ∂volume.restrict (p.platform i.1), ∀ sign,
      (HessianBall.meanHessian (L sign x)).applyRows (τ 0) (τ 1) =
        (w₀.hessian x).applyRows (τ 0) (τ 1) := by
  let P := p.platform i.1
  have hs (j : ℕ) : ∀ᵐ x ∂volume.restrict P,
      HessianBall.tangentX τ (state j x) = (w j).second x τ ex ∧
      HessianBall.tangentY τ (state j x) = (w j).second x τ ey := by
    filter_upwards [(w j).hessian_state_readouts_ae (hState j) hU,
      ae_mono (Measure.restrict_mono hU le_rfl) (second_tangent_coordinates (w j) τ)] with x hx hy
    constructor
    · simpa only [HessianBall.tangentX, ContinuousMap.add_apply, ContinuousMap.smul_apply,
        hx.1, hx.2.1, Hess3.applyRows] using congrArg Prod.fst hy
    · simpa only [HessianBall.tangentY, ContinuousMap.add_apply, ContinuousMap.smul_apply,
        hx.2.1, hx.2.2.1, Hess3.applyRows] using congrArg Prod.snd hy
  have hcoord (sign : Bool) (A : C(HessianBall m K, Target m)) (v : Plane)
      (hA : ∀ j, ∀ᵐ x ∂volume.restrict P, A (state j x) = (w j).second x τ v) (c : Fin m) :
      ∀ᵐ x ∂volume.restrict P, L sign x (PositiveFunctional.coord A c) = w₀.second x τ v c := by
    let _ : CompactSpace (HessianBall m K) :=
      isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : HessSpace m) K)
    let f := PositiveFunctional.coord A c
    have hb : LocallyIntegrableOn (fun x => L sign x f) (parentOpen p i) volume :=
      ((memLp_top_of_bound (hL sign f).aestronglyMeasurable ‖f‖
        (Eventually.of_forall fun x => (L sign x).norm_readout_le f)).locallyIntegrable
          (by simp)).locallyIntegrableOn _
    apply row.conditional_phase_tangent_weakJet_ae i sign hn k hk hτ
      (fun j => (w j).restrict hU) (w₀.restrict hU) v (EuclideanSpace.proj c) a R hp hgc hgc₀ hgu hb
    intro φ
    have hφ : IntegrableOn (φ : Plane → ℝ) P volume :=
      (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).integrableOn
    have hh := hPair sign f φ hφ
    have heq (j : ℕ) : (∫ x in P, row.phaseWeight i sign (k j) x * f (state j x) * φ x) =
        ∫ x in P, row.phaseWeight i sign (k j) x *
          (φ x * (EuclideanSpace.proj c) (((w j).restrict hU).second x τ v)) := by
      apply integral_congr_ae
      filter_upwards [hA j] with x hx
      change row.phaseWeight i sign (k j) x * A (state j x) c * φ x =
        row.phaseWeight i sign (k j) x * (φ x * (w j).second x τ v c)
      rw [hx]
      ac_rfl
    simpa only [mul_comm] using hh.congr heq
  have hX := ae_all_iff.2 (fun sign : Bool => ae_all_iff.2 (fun c : Fin m =>
    hcoord sign (HessianBall.tangentX τ) ex (fun j => (hs j).mono fun _ hx => hx.1) c))
  have hY := ae_all_iff.2 (fun sign : Bool => ae_all_iff.2 (fun c : Fin m =>
    hcoord sign (HessianBall.tangentY τ) ey (fun j => (hs j).mono fun _ hx => hx.2) c))
  filter_upwards [hX, hY, ae_mono (Measure.restrict_mono hU le_rfl)
    (second_tangent_coordinates w₀ τ)] with x hx hy hw sign
  rw [hw]
  apply Prod.ext
  · ext c
    rw [← HessianBall.mean_tangentX]
    exact hx sign c
  · ext c
    rw [← HessianBall.mean_tangentY]
    exact hy sign c

end PhysicalLayerRow

/-- The tangent to the table-row normal `(1,t)` has coordinates `(-t,1)`. -/
public theorem inner_oblique_tangent (t : ℝ) :
    inner ℝ (coordinateDirection 1 t) (coordinateDirection (-t) 1) = 0 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, coordinateDirection]

/-- The tangent to the vertical-row normal `(0,1)` has coordinates `(1,0)`. -/
public theorem inner_vertical_tangent :
    inner ℝ (coordinateDirection 0 1) (coordinateDirection 1 0) = 0 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, coordinateDirection]

namespace HessianBall

/-- The two oblique phase means have the coordinate form required in the
oblique energy comparison. The parameter `t` allows either sign and zero. -/
public theorem oblique_mean_forms_ae {m : ℕ} {K : ℝ} {μ : Measure Plane}
    (L : Bool → Plane → PositiveFunctional (HessianBall m K)) (H₀ : Plane → Hess3 m) (t : ℝ)
    (h : ∀ᵐ x ∂μ, ∀ sign,
      (meanHessian (L sign x)).applyRows (coordinateDirection (-t) 1 0)
        (coordinateDirection (-t) 1 1) =
      (H₀ x).applyRows (coordinateDirection (-t) 1 0) (coordinateDirection (-t) 1 1)) :
    ∀ᵐ x ∂μ, ∀ sign,
      (meanHessian (L sign x)).xy = (H₀ x).xy + t • ((meanHessian (L sign x)).xx - (H₀ x).xx) ∧
      (meanHessian (L sign x)).yy = (H₀ x).yy + t ^ 2 • ((meanHessian (L sign x)).xx - (H₀ x).xx) := by
  filter_upwards [h] with x hx sign
  exact Hess3.oblique_mean_of_applyRows_eq _ _ t (hx sign)

/-- The two vertical phase means preserve the parent's horizontal and mixed
Hessian entries. -/
public theorem vertical_mean_forms_ae {m : ℕ} {K : ℝ} {μ : Measure Plane}
    (L : Bool → Plane → PositiveFunctional (HessianBall m K)) (H₀ : Plane → Hess3 m)
    (h : ∀ᵐ x ∂μ, ∀ sign,
      (meanHessian (L sign x)).applyRows (coordinateDirection 1 0 0)
        (coordinateDirection 1 0 1) =
      (H₀ x).applyRows (coordinateDirection 1 0 0) (coordinateDirection 1 0 1)) :
    ∀ᵐ x ∂μ, ∀ sign, (meanHessian (L sign x)).xx = (H₀ x).xx ∧
      (meanHessian (L sign x)).xy = (H₀ x).xy := by
  filter_upwards [h] with x hx sign
  exact Hess3.vertical_mean_of_applyRows_eq _ _ (hx sign)

end HessianBall
end C2Riemannian
