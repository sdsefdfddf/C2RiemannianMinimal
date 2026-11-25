module

public import C2Riemannian.PhysicalSourceLimits
public import C2Riemannian.ActualParameterTree
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped ContDiff Topology

namespace C2Riemannian

open WeakJet2 (ex ey metricYY)

/-- Identification of the iterated directional derivative with the corresponding
entry of the second Fréchet derivative. -/
private theorem lineDeriv₂_eq_iteratedFDeriv {f : Plane → ℝ} {x : Plane}
    {U : Set Plane} (hU : IsOpen U) (hx : x ∈ U)
    (hf : ContDiffOn ℝ 2 f U) (a b : Plane) :
    lineDeriv ℝ (fun y => lineDeriv ℝ f y a) x b =
      iteratedFDeriv ℝ 2 f x ![b, a] := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    DifferentiableWithinAt.differentiableAt
      ((hf.fderiv_of_isOpen hU (by decide : (1 : ℕ∞ω) + 1 ≤ 2)).differentiableOn_one x hx)
      (hU.mem_nhds hx)
  have hNear : (fun y => lineDeriv ℝ f y a) =ᶠ[𝓝 x] fun y => fderiv ℝ f y a :=
    by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact ((hf.differentiableOn (by decide) y hy).differentiableAt
        (hU.mem_nhds hy)).lineDeriv_eq_fderiv
  rw [hNear.lineDeriv_eq, iteratedFDeriv_two_apply]
  exact (((ContinuousLinearMap.apply ℝ ℝ a).hasFDerivAt.comp x hd.hasFDerivAt).hasLineDerivAt b).lineDeriv

private theorem input_tensor_entry {Q : Set Plane} (p : PhysicalPrefix Q) (i : p.Label)
    {x : Plane} (hx : x ∈ p.platform i) (hp : p.ExactJets) (w : Fin 2 → Fin 2) :
    iteratedFDeriv ℝ 2 p.input x (basisWord w) = secondWordValue (p.ideal i).scalar w / 5 := by
  have hSmooth : ContDiffAt ℝ 2 p.secondPotential x :=
    (p.smooth_second.of_le (by simp)).contDiffAt
  have h := (hp i x hx).1 w
  unfold PhysicalPrefix.input
  rw [iteratedFDeriv_const_smul_apply hSmooth, smul_apply, h, smul_eq_mul]
  ring

private theorem basisWord_xx : basisWord (![(0 : Fin 2), 0] : Fin 2 → Fin 2) = ![ex, ex] := by
  funext i
  fin_cases i <;> simp [basisWord, ex, EuclideanSpace.basisFun_apply]

private theorem basisWord_yy : basisWord (![(1 : Fin 2), 1] : Fin 2 → Fin 2) = ![ey, ey] := by
  funext i
  fin_cases i <;> simp [basisWord, ey, EuclideanSpace.basisFun_apply]

private theorem basisWord_yx : basisWord (![(1 : Fin 2), 0] : Fin 2 → Fin 2) = ![ey, ex] := by
  funext i
  fin_cases i <;> simp [basisWord, ex, ey, EuclideanSpace.basisFun_apply]

/-- The reverse source is the exact negative normalized scalar determinant on
every platform, including platforms that stop. -/
public theorem PhysicalPrefix.reverseSource_eq_ideal {Q : Set Plane} (p : PhysicalPrefix Q)
    (hp : p.ExactJets) (i : p.Label) {x : Plane} (hx : x ∈ p.platform i) :
    p.reverseSource x = -(p.ideal i).scalar.det / 25 := by
  have hF : ContDiffOn ℝ 2 p.input (univ : Set Plane) :=
    (p.input_smooth.of_le (by simp)).contDiffOn
  have hxx := input_tensor_entry p i hx hp ![0, 0]
  have hyy := input_tensor_entry p i hx hp ![1, 1]
  have hxy := input_tensor_entry p i hx hp ![1, 0]
  rw [basisWord_xx] at hxx
  rw [basisWord_yy] at hyy
  rw [basisWord_yx] at hxy
  simp [secondWordValue] at hxx hyy hxy
  unfold PhysicalPrefix.reverseSource scalarHessianDet ScalarHess.det
  rw [lineDeriv₂_eq_iteratedFDeriv isOpen_univ (mem_univ x) hF ex ex,
    lineDeriv₂_eq_iteratedFDeriv isOpen_univ (mem_univ x) hF ey ey,
    lineDeriv₂_eq_iteratedFDeriv isOpen_univ (mem_univ x) hF ex ey, hxx, hyy, hxy]
  ring

private theorem second_add_const_mul {v f : Plane → ℝ} {U : Set Plane}
    (hU : IsOpen U) {x : Plane} (hx : x ∈ U)
    (hv : ContDiffOn ℝ 2 v U) (hf : ContDiffOn ℝ 2 f U) (θ : ℝ) :
    fderiv ℝ (fderiv ℝ (fun y => v y + θ * f y)) x =
      fderiv ℝ (fderiv ℝ v) x + θ • fderiv ℝ (fderiv ℝ f) x := by
  have hDiff (g : Plane → ℝ) (hg : ContDiffOn ℝ 2 g U) (y : Plane) (hy : y ∈ U) :
      DifferentiableAt ℝ g y :=
    (hg.differentiableOn (by decide) y hy).differentiableAt (hU.mem_nhds hy)
  have hNear : fderiv ℝ (fun y => v y + θ * f y) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ v y + θ • fderiv ℝ f y) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (((hDiff v hv y hy).hasFDerivAt).add
      ((hDiff f hf y hy).hasFDerivAt.const_mul θ)).fderiv
  have h' (g : Plane → ℝ) (hg : ContDiffOn ℝ 2 g U) : DifferentiableAt ℝ (fderiv ℝ g) x :=
    DifferentiableWithinAt.differentiableAt
      ((hg.fderiv_of_isOpen hU (by decide : (1 : ℕ∞ω) + 1 ≤ 2)).differentiableOn_one x hx)
      (hU.mem_nhds hx)
  rw [hNear.fderiv_eq]
  exact (((h' v hv).hasFDerivAt).add ((h' f hf).hasFDerivAt.const_smul θ)).fderiv

/-- On every exact platform the linear source is the background derivative
plus the ideal state's vertical coefficient with its prescribed scale. -/
public theorem PhysicalPrefix.linearSource_eq_ideal {Q U : Set Plane} (p : PhysicalPrefix Q)
    (hp : p.ExactJets) (i : p.Label) {x : Plane} (hx : x ∈ p.platform i)
    (hU : IsOpen U) (hxU : x ∈ U) {v₀ : Plane → ℝ} (hv₀ : ContDiffOn ℝ 2 v₀ U) (θ : ℝ) :
    p.linearSource v₀ θ x = -metricYY v₀ x / 2 - (θ / 10) * (p.ideal i).scalar.yy := by
  have hF : ContDiffOn ℝ 2 p.input U := (p.input_smooth.of_le (by simp)).contDiffOn
  have hyy := input_tensor_entry p i hx hp ![1, 1]
  rw [basisWord_yy] at hyy
  simp [secondWordValue] at hyy
  unfold PhysicalPrefix.linearSource metricYY
  rw [lineDeriv₂_eq_iteratedFDeriv hU hxU (p.metricCoefficient_contDiffOn hv₀ θ) ey ey,
    lineDeriv₂_eq_iteratedFDeriv hU hxU hv₀ ey ey]
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
  have hDeriv := second_add_const_mul hU hxU hv₀ hF θ
  change -fderiv ℝ (fderiv ℝ (fun y => v₀ y + θ * p.input y)) x ey ey / 2 =
    -fderiv ℝ (fderiv ℝ v₀) x ey ey / 2 - (θ / 10) * (p.ideal i).scalar.yy
  rw [hDeriv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [iteratedFDeriv_two_apply] at hyy
  change fderiv ℝ (fderiv ℝ p.input) x ey ey = _ at hyy
  rw [hyy]
  ring

end C2Riemannian
