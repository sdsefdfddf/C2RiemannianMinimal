module

public import C2Riemannian.GeneralMollificationL2
public import C2Riemannian.WeakCompatibility
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false

open MeasureTheory Filter Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology

namespace C2Riemannian.WeakJet2

variable {m : ℕ} {U : Opens Plane} (w : WeakJet2 m U)

private noncomputable def secondComponentMap (a b : Plane) :
    (Plane →L[ℝ] (Plane →L[ℝ] Target m)) →L[ℝ] Target m :=
  (ContinuousLinearMap.apply ℝ (Target m) a).comp
    (ContinuousLinearMap.apply ℝ (Plane →L[ℝ] Target m) b)

/-- The Gram test identity for square-integrable weak jets on a finite-measure open domain. -/
public theorem weak_gramTest_l2 [IsFiniteMeasure (volume.restrict (U : Set Plane))]
    (hw : MemLp w.value 2 (volume.restrict (U : Set Plane)))
    (hP : MemLp w.gradient 2 (volume.restrict (U : Set Plane)))
    (hB : MemLp w.second 2 (volume.restrict (U : Set Plane)))
    (φ : 𝓓(U, ℝ)) :
    gramTest (volume.restrict (U : Set Plane)) φ
      (testSecond ex ex φ) (testSecond ey ex φ) (testSecond ey ey φ)
      (fun x => w.gradient x ex) (fun x => w.gradient x ey)
      (fun x => w.second x ex ex) (fun x => w.second x ey ex)
      (fun x => w.second x ey ey) := by
  let μ := volume.restrict (U : Set Plane)
  have hgrad (d : Plane) : StrongL2 atTop μ
      (fun n x => mollify U (shrinkingBump n) w.gradient x d) (fun x => w.gradient x d) :=
    mollify_clm_strongL2 (V := U) le_rfl hP shrinkingBump
      shrinkingBump_rOut_tendsto shrinkingBump_ratio (ContinuousLinearMap.apply ℝ (Target m) d)
  have hhess (a b : Plane) : StrongL2 atTop μ
      (fun n x => mollify U (shrinkingBump n) w.second x b a) (fun x => w.second x b a) := by
    have h := mollify_clm_strongL2 (U := U) (V := U) (f := w.second)
      le_rfl hB shrinkingBump shrinkingBump_rOut_tendsto shrinkingBump_ratio (secondComponentMap (m := m) a b)
    simpa only [secondComponentMap, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] using h
  let φxx := testSecond ex ex φ
  let φxy := testSecond ey ex φ
  let φyy := testSecond ey ey φ
  obtain ⟨C₀, hc₀⟩ := φ.hasCompactSupport.exists_bound_of_continuous φ.continuous
  obtain ⟨Cxx, hcxx⟩ := φxx.hasCompactSupport.exists_bound_of_continuous φxx.continuous
  obtain ⟨Cxy, hcxy⟩ := φxy.hasCompactSupport.exists_bound_of_continuous φxy.continuous
  obtain ⟨Cyy, hcyy⟩ := φyy.hasCompactSupport.exists_bound_of_continuous φyy.continuous
  let C := max (max C₀ Cxx) (max Cxy Cyy)
  exact gramTest_of_strongL2 φ.continuous.aestronglyMeasurable φxx.continuous.aestronglyMeasurable
    φxy.continuous.aestronglyMeasurable φyy.continuous.aestronglyMeasurable C
    (Eventually.of_forall fun x => (hc₀ x).trans ((le_max_left _ _).trans (le_max_left _ _)))
    (Eventually.of_forall fun x => (hcxx x).trans ((le_max_right _ _).trans (le_max_left _ _)))
    (Eventually.of_forall fun x => (hcxy x).trans ((le_max_left _ _).trans (le_max_right _ _)))
    (Eventually.of_forall fun x => (hcyy x).trans ((le_max_right _ _).trans (le_max_right _ _)))
    (hgrad ex) (hgrad ey) (hhess ex ex) (hhess ex ey) (hhess ey ey)
    (w.gramTest_mollify_eventually hw hP hB (by simp) (by simp) (by simp)
      shrinkingBump shrinkingBump_rOut_tendsto φ)

private theorem integral_eq_of_test_eq {V : Opens Plane} (φ : 𝓓(U, ℝ)) (ψ : 𝓓(V, ℝ))
    (heq : (φ : Plane → ℝ) = ψ) (f : Plane → ℝ) :
    (∫ x in ↑U, φ x * f x) = ∫ x in ↑V, ψ x * f x := by
  have hU := TauCeti.setIntegral_smul_eq_integral_smul (μ := volume) (w := f) φ
  have hV := TauCeti.setIntegral_smul_eq_integral_smul (μ := volume) (w := f) ψ
  simp only [smul_eq_mul] at hU hV
  rw [hU, hV]
  exact integral_congr_ae (Eventually.of_forall fun x => congrArg (· * f x) (congrFun heq x))

/-- The distributional Gram compatibility identity for a locally square-integrable weak
second jet. The local square-integrability hypotheses are on every compact subset of the domain. -/
public theorem weak_gramTest_local_l2
    (hlocal : ∀ s : Set Plane, IsCompact s → s ⊆ (U : Set Plane) →
      MemLp w.value 2 (volume.restrict s) ∧ MemLp w.gradient 2 (volume.restrict s) ∧
      MemLp w.second 2 (volume.restrict s))
    (φ : 𝓓(U, ℝ)) :
    gramTest (volume.restrict (U : Set Plane)) φ
      (testSecond ex ex φ) (testSecond ey ex φ) (testSecond ey ey φ)
      (fun x => w.gradient x ex) (fun x => w.gradient x ey)
      (fun x => w.second x ex ex) (fun x => w.second x ey ex)
      (fun x => w.second x ey ey) := by
  obtain ⟨δ, hδ, hsub⟩ := φ.hasCompactSupport.exists_cthickening_subset_open
    U.isOpen φ.tsupport_subset
  let s := Metric.cthickening δ (tsupport (φ : Plane → ℝ))
  let V : Opens Plane := ⟨Metric.thickening δ (tsupport (φ : Plane → ℝ)), Metric.isOpen_thickening⟩
  have hVs : (V : Set Plane) ⊆ s := Metric.thickening_subset_cthickening _ _
  have hVU : V ≤ U := hVs.trans hsub
  have hcs : IsCompact s := φ.hasCompactSupport.cthickening
  have hvr : (volume : Measure Plane).restrict (V : Set Plane) ≤ volume.restrict s :=
    Measure.restrict_mono hVs le_rfl
  have : IsFiniteMeasure (volume.restrict (V : Set Plane)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
        exact (measure_mono hVs).trans_lt hcs.measure_lt_top⟩
  obtain ⟨hw, hP, hB⟩ := hlocal s hcs hsub
  let ψ : 𝓓(V, ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, Metric.self_subset_thickening hδ _⟩
  have heq : (φ : Plane → ℝ) = ψ := rfl
  have hdeq (a b : Plane) : (testSecond a b φ : Plane → ℝ) = testSecond a b ψ := by
    funext x
    rw [testSecond_apply, testSecond_apply, heq]
  have htest := (w.restrict hVU).weak_gramTest_l2 (hw.mono_measure hvr)
    (hP.mono_measure hvr) (hB.mono_measure hvr) ψ
  unfold gramTest at htest ⊢
  rw [integral_eq_of_test_eq φ ψ heq, integral_eq_of_test_eq φ ψ heq,
    integral_eq_of_test_eq _ _ (hdeq ey ey), integral_eq_of_test_eq _ _ (hdeq ex ex),
    integral_eq_of_test_eq _ _ (hdeq ey ex)]
  exact htest

end C2Riemannian.WeakJet2

