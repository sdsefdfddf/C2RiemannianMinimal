module

public import C2Riemannian.WeakSmoothTesting
public import C2Riemannian.WeakMollificationStrong

set_option autoImplicit false

open MeasureTheory Filter Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology

namespace C2Riemannian.WeakJet2

variable {m : ℕ} {U : Opens Plane} (w : WeakJet2 m U)

private noncomputable def jetComponent (a b : Plane) :
    (Plane →L[ℝ] (Plane →L[ℝ] Target m)) →L[ℝ] Target m :=
  (ContinuousLinearMap.apply ℝ (Target m) a).comp
    (ContinuousLinearMap.apply ℝ (Plane →L[ℝ] Target m) b)

set_option maxHeartbeats 700000 in
/-- The distributional Gram compatibility identity for a bounded weak second jet
on a finite-measure open domain. -/
public theorem weak_gramTest [IsFiniteMeasure (volume.restrict (U : Set Plane))]
    (hw : MemLp w.value ∞ (volume.restrict (U : Set Plane)))
    (hP : MemLp w.gradient ∞ (volume.restrict (U : Set Plane)))
    (hB : MemLp w.second ∞ (volume.restrict (U : Set Plane)))
    {Cp Cb : ℝ} (hCp : 0 ≤ Cp) (hCb : 0 ≤ Cb)
    (bP : ∀ᵐ x ∂volume.restrict (U : Set Plane), ‖w.gradient x‖ ≤ Cp)
    (bB : ∀ᵐ x ∂volume.restrict (U : Set Plane), ‖w.second x‖ ≤ Cb)
    (φ : 𝓓(U, ℝ)) :
    gramTest (volume.restrict (U : Set Plane)) φ
      (testSecond ex ex φ) (testSecond ey ex φ) (testSecond ey ey φ)
      (fun x => w.gradient x ex) (fun x => w.gradient x ey)
      (fun x => w.second x ex ex) (fun x => w.second x ey ex)
      (fun x => w.second x ey ey) := by
  let μ := volume.restrict (U : Set Plane)
  have hgrad (d : Plane) : StrongL2 atTop μ
      (fun n x => mollify U (shrinkingBump n) w.gradient x d) (fun x => w.gradient x d) :=
    mollify_clm_strongL2_of_bound (V := U) le_rfl hP hCp bP shrinkingBump
      shrinkingBump_rOut_tendsto shrinkingBump_ratio (ContinuousLinearMap.apply ℝ (Target m) d)
  have hhess (a b : Plane) : StrongL2 atTop μ
      (fun n x => mollify U (shrinkingBump n) w.second x b a) (fun x => w.second x b a) := by
    have h := mollify_clm_strongL2_of_bound (U := U) (V := U) (f := w.second)
      le_rfl hB hCb bB shrinkingBump shrinkingBump_rOut_tendsto shrinkingBump_ratio
      (jetComponent (m := m) a b)
    simpa only [jetComponent, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] using h
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

end C2Riemannian.WeakJet2
