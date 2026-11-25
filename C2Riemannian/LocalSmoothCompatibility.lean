module

public import C2Riemannian.SmoothCompatibility
import C2Riemannian.SmoothCutoff
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions Topology

namespace C2Riemannian

variable {m : ℕ}

private theorem eqOn_lineDeriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : Set Plane} (hV : IsOpen V) {f g : Plane → F} (h : EqOn f g V) (d : Plane) :
    ∀ x ∈ V, lineDeriv ℝ f x d = lineDeriv ℝ g x d := by
  intro x hx
  have he : f =ᶠ[𝓝 x] g := eventually_of_mem (hV.mem_nhds hx) h
  exact he.lineDeriv_eq

private theorem eqOn_lineDeriv₂ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : Set Plane} (hV : IsOpen V) {f g : Plane → F} (h : EqOn f g V) (d e : Plane)
    (x : Plane) (hx : x ∈ V) :
    lineDeriv ℝ (fun z => lineDeriv ℝ f z d) x e =
      lineDeriv ℝ (fun z => lineDeriv ℝ g z d) x e :=
  eqOn_lineDeriv hV (eqOn_lineDeriv hV h d) e x hx

private theorem eqOn_classicalHessian {V : Set Plane} (hV : IsOpen V)
    {F G : Plane → Target m} (h : EqOn F G V) :
    EqOn (classicalHessian F) (classicalHessian G) V := by
  intro x hx
  dsimp only [classicalHessian]
  simp only [eqOn_lineDeriv₂ hV h _ _ x hx]

private theorem exists_global_smooth_at_compact {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ∞} {Ω C : Set Plane}
    {W : Plane → E} (hΩ : IsOpen Ω) (hW : ContDiffOn ℝ (↑n) W Ω)
    (hC : IsCompact C) (hSub : C ⊆ Ω) :
    ∃ (F : Plane → E) (V : Set Plane), ContDiff ℝ (↑n) F ∧
      IsOpen V ∧ C ⊆ V ∧ EqOn F W V := by
  obtain ⟨χ, V, hχ, _, hs, _, hV, hCV, hOne⟩ := exists_compact_inner_cutoff hC hΩ hSub
  let F := fun x => χ x • W x
  have hχ' : ContDiff ℝ (↑n) χ := hχ.of_le (by simp)
  refine ⟨F, V, contDiff_iff_contDiffAt.mpr ?_, hV, hCV, ?_⟩
  · intro x
    by_cases hx : x ∈ Ω
    · exact hχ'.contDiffAt.smul (hW.contDiffAt (hΩ.mem_nhds hx))
    · apply (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq
      have hn : (tsupport χ)ᶜ ∈ 𝓝 x :=
        (isClosed_tsupport χ).isOpen_compl.mem_nhds (fun h => hx (hs h))
      filter_upwards [hn] with y hy
      simp only [F, image_eq_zero_of_notMem_tsupport hy, zero_smul]
  · intro x hx
    simp only [F, hOne x hx, one_smul]

public theorem smooth_compatibility_on {Ω : Set Plane} {W : Plane → Target m}
    (hΩ : IsOpen Ω) (hW : ContDiffOn ℝ 3 W Ω) {x : Plane} (hx : x ∈ Ω) :
    let ex : Plane := EuclideanSpace.single 0 1
    let ey : Plane := EuclideanSpace.single 1 1
    let Px := fun z => lineDeriv ℝ W z ex
    let Py := fun z => lineDeriv ℝ W z ey
    lineDeriv ℝ (fun z => lineDeriv ℝ (fun y => inner ℝ (Px y) (Px y)) z ey) x ey +
      lineDeriv ℝ (fun z => lineDeriv ℝ (fun y => inner ℝ (Py y) (Py y)) z ex) x ex -
      2 * lineDeriv ℝ (fun z => lineDeriv ℝ (fun y => inner ℝ (Px y) (Py y)) z ey) x ex =
      -2 * (classicalHessian W x).q := by
  obtain ⟨F, V, hF, hV, hCV, hEq⟩ :=
    exists_global_smooth_at_compact (n := 3) hΩ hW isCompact_singleton (singleton_subset_iff.mpr hx)
  have hxV : x ∈ V := hCV (mem_singleton x)
  have hGram (d e : Plane) :
      EqOn (fun y => inner ℝ (lineDeriv ℝ F y d) (lineDeriv ℝ F y e))
        (fun y => inner ℝ (lineDeriv ℝ W y d) (lineDeriv ℝ W y e)) V := by
    intro y hy
    dsimp only
    rw [eqOn_lineDeriv hV hEq d y hy, eqOn_lineDeriv hV hEq e y hy]
  have h := smooth_compatibility hF x
  dsimp only at h ⊢
  simp only [eqOn_lineDeriv₂ hV (hGram _ _) _ _ x hxV,
    eqOn_classicalHessian hV hEq hxV] at h
  exact h

public theorem smooth_compatibility_test_on {U : Opens Plane} {W : Plane → Target m}
    (hW : ContDiffOn ℝ 3 W (U : Set Plane)) (φ : 𝓓(U, ℝ)) :
    let ex : Plane := EuclideanSpace.single 0 1
    let ey : Plane := EuclideanSpace.single 1 1
    let Px := fun z => lineDeriv ℝ W z ex
    let Py := fun z => lineDeriv ℝ W z ey
    (-2 * (∫ x in ↑U, φ x * (classicalHessian W x).q) =
      (∫ x in ↑U, lineDeriv ℝ (fun z => lineDeriv ℝ (φ : Plane → ℝ) z ey) x ey *
        inner ℝ (Px x) (Px x)) +
      (∫ x in ↑U, lineDeriv ℝ (fun z => lineDeriv ℝ (φ : Plane → ℝ) z ex) x ex *
        inner ℝ (Py x) (Py x)) -
      2 * (∫ x in ↑U, lineDeriv ℝ (fun z => lineDeriv ℝ (φ : Plane → ℝ) z ey) x ex *
        inner ℝ (Px x) (Py x))) := by
  obtain ⟨F, V, hF, hV, hCV, hEq⟩ :=
    exists_global_smooth_at_compact (n := 3) U.isOpen hW φ.hasCompactSupport φ.tsupport_subset
  have hHess : (∫ x in ↑U, φ x * (classicalHessian F x).q) =
      ∫ x in ↑U, φ x * (classicalHessian W x).q := by
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ tsupport (φ : Plane → ℝ)
    · rw [eqOn_classicalHessian hV hEq (hCV hx)]
    · have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp only [hz, zero_mul]
  have hGram (a b d e : Plane) :
      (∫ x in ↑U, lineDeriv ℝ (fun z => lineDeriv ℝ (φ : Plane → ℝ) z a) x b *
        inner ℝ (lineDeriv ℝ F x d) (lineDeriv ℝ F x e)) =
      ∫ x in ↑U, lineDeriv ℝ (fun z => lineDeriv ℝ (φ : Plane → ℝ) z a) x b *
        inner ℝ (lineDeriv ℝ W x d) (lineDeriv ℝ W x e) := by
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ tsupport (φ : Plane → ℝ)
    · rw [eqOn_lineDeriv hV hEq d x (hCV hx), eqOn_lineDeriv hV hEq e x (hCV hx)]
    · have h : (fun z => lineDeriv ℝ (φ : Plane → ℝ) z a) =ᶠ[𝓝 x] (fun _ => 0) :=
        (eventually_of_mem ((isClosed_tsupport (φ : Plane → ℝ)).isOpen_compl.mem_nhds hx)
          fun _ hz => TauCeti.lineDeriv_eq_zero_of_notMem_tsupport φ hz a)
      have hDerivative : lineDeriv ℝ (fun z => lineDeriv ℝ (φ : Plane → ℝ) z a) x b = 0 :=
        h.lineDeriv_eq.trans (by simpa only [zero_apply] using
          ((hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) x).hasLineDerivAt b).lineDeriv)
      simp only [hDerivative, zero_mul]
  have h := smooth_compatibility_test hF φ
  dsimp only at h ⊢
  rw [hHess, hGram, hGram, hGram] at h
  exact h

/-- Two directional integrations by parts for a function smooth on the test domain. -/
public theorem integral_lineDeriv₂_mul_on {U : Opens Plane} {f : Plane → ℝ}
    (hf : ContDiffOn ℝ 2 f (U : Set Plane)) (a b : Plane) (φ : 𝓓(U, ℝ)) :
    (∫ x in ↑U, φ x * lineDeriv ℝ (fun z => lineDeriv ℝ f z a) x b) =
      ∫ x in ↑U, lineDeriv ℝ (fun z => lineDeriv ℝ (φ : Plane → ℝ) z b) x a * f x := by
  obtain ⟨F, V, hF, hV, hCV, hEq⟩ :=
    exists_global_smooth_at_compact (n := 2) U.isOpen hf φ.hasCompactSupport φ.tsupport_subset
  have hLeft : (∫ x in ↑U, φ x * lineDeriv ℝ (fun z => lineDeriv ℝ f z a) x b) =
      ∫ x in ↑U, φ x * lineDeriv ℝ (fun z => lineDeriv ℝ F z a) x b := by
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ tsupport (φ : Plane → ℝ)
    · rw [eqOn_lineDeriv₂ hV hEq a b x (hCV hx)]
    · have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp only [hz, zero_mul]
  rw [hLeft, integral_lineDeriv₂_mul hF a b φ]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ tsupport (φ : Plane → ℝ)
  · rw [show F x = f x from hEq (hCV hx)]
  · have h : (fun z => lineDeriv ℝ (φ : Plane → ℝ) z b) =ᶠ[𝓝 x] (fun _ => 0) :=
      (eventually_of_mem ((isClosed_tsupport (φ : Plane → ℝ)).isOpen_compl.mem_nhds hx)
        fun _ hz => TauCeti.lineDeriv_eq_zero_of_notMem_tsupport φ hz b)
    have hDerivative : lineDeriv ℝ (fun z => lineDeriv ℝ (φ : Plane → ℝ) z b) x a = 0 :=
      h.lineDeriv_eq.trans (by simpa only [zero_apply] using
        ((hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) x).hasLineDerivAt a).lineDeriv)
    simp only [hDerivative, zero_mul]

end C2Riemannian
