module

public import C2Riemannian.AffineNormalization
public import C2Riemannian.CompactDiskConvergence
public import C2Riemannian.DerivativeLimit

set_option autoImplicit false

open Filter Set
open scoped Topology NNReal BigOperators

namespace C2Riemannian

private theorem continuous_gradHS {m : ℕ} :
    Continuous (gradHS : (Plane →L[ℝ] Target m) → ℝ) := by
  unfold gradHS
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ =>
    ((ContinuousLinearMap.apply ℝ (Target m) (EuclideanSpace.basisFun (Fin 2) ℝ i)).continuous.norm).pow 2)

/-- Normalized potentials with a common Hilbert–Schmidt Lipschitz bound on
their derivatives admit a common C¹ limit on a bounded open convex domain.
The limit retains the same Hilbert–Schmidt difference bound. -/
public theorem normalized_potentials_compactness {m : ℕ}
    {Ω : Set Plane} (hΩ : IsOpen Ω) (hConvex : Convex ℝ Ω)
    {a : Plane} (ha : a ∈ Ω) (R K : ℝ≥0)
    (hRadius : ∀ x ∈ Ω, dist x a ≤ R)
    (s : ℕ → Set Plane) (hs : ∀ j, IsCompact (s j)) (hSub : ∀ j, s j ⊆ Ω)
    (hExhaust : ∀ t : Set Plane, t ⊆ Ω → IsCompact t → ∃ j, t ⊆ s j)
    (W : ℕ → Plane → Target m)
    (hDiff : ∀ n x, x ∈ Ω → DifferentiableAt ℝ (W n) x)
    (hCont : ∀ n, ContinuousOn (fderiv ℝ (W n)) Ω)
    (hHS : ∀ n x, x ∈ Ω → ∀ y, y ∈ Ω →
      gradHS (fderiv ℝ (W n) x - fderiv ℝ (W n) y) ≤ (K : ℝ) * dist x y) :
    ∃ (w : Plane → Target m) (p : Plane → Plane →L[ℝ] Target m) (k : ℕ → ℕ),
      StrictMono k ∧ ContDiffOn ℝ 1 w Ω ∧
      (∀ x ∈ Ω, HasFDerivAt w (p x) x) ∧ w a = 0 ∧ p a = 0 ∧
      (∀ x ∈ Ω, ∀ y ∈ Ω, gradHS (p x - p y) ≤ (K : ℝ) * dist x y) ∧
      (∀ j, TendstoUniformlyOn (fun n => normalize_height (W (k n)) a) w atTop (s j)) ∧
      (∀ j, TendstoUniformlyOn (fun n => fderiv ℝ (normalize_height (W (k n)) a)) p atTop (s j)) := by
  classical
  let N (n : ℕ) := normalize_height (W n) a
  let P (n : ℕ) := fderiv ℝ (N n)
  let U (n : ℕ) (x : Ω) := (N n x.1, P n x.1)
  let L : ℝ≥0 := max (K * R) K
  have hULip (n : ℕ) : LipschitzWith L (U n) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Prod.dist_eq]
    change max (dist (N n x.1) (N n y.1)) (dist (P n x.1) (P n y.1)) ≤
      (L : ℝ) * dist x.1 y.1
    have hL₁ : (K : ℝ) * R ≤ L := by exact_mod_cast le_max_left (K * R) K
    have hL₂ : (K : ℝ) ≤ L := by exact_mod_cast le_max_right (K * R) K
    apply max_le
    · exact (normalized_height_dist_le hConvex ha (hDiff n) K.coe_nonneg (hHS n) hRadius
        x.2 y.2).trans (mul_le_mul_of_nonneg_right hL₁ dist_nonneg)
    · rw [dist_eq_norm]
      exact (opNorm_le_gradHS _).trans
        (((normalized_gradient_bounds ha (hDiff n) (hHS n)).1 _ x.2 _ y.2).trans
          (mul_le_mul_of_nonneg_right hL₂ dist_nonneg))
  have hUBound (n : ℕ) (x : Ω) : ‖U n x‖ ≤ (L : ℝ) * R := by
    let a' : Ω := ⟨a, ha⟩
    have hZero : U n a' = 0 := by
      simp [U, N, P, a', fderiv_normalize_height_self (hDiff n a ha)]
    have hDist := (hULip n).dist_le_mul x a'
    rw [hZero, dist_zero_right] at hDist
    exact hDist.trans (mul_le_mul_of_nonneg_left (hRadius x.1 x.2) L.coe_nonneg)
  let t (j : ℕ) : Set Ω := Subtype.val ⁻¹' s j
  have ht (j : ℕ) : IsCompact (t j) := by
    change IsCompact (Subtype.val ⁻¹' s j : Set Ω)
    rw [Subtype.isCompact_iff, image_preimage_eq_inter_range, Subtype.range_coe,
      inter_eq_left.mpr (hSub j)]
    exact hs j
  have hCover (x : Ω) : ∃ j, x ∈ t j := by
    obtain ⟨j, hj⟩ := hExhaust {x.1} (singleton_subset_iff.mpr x.2) isCompact_singleton
    exact ⟨j, hj (mem_singleton x.1)⟩
  obtain ⟨g, k, hk, _, _, hUniform⟩ :=
    compact_cover_bounded_lipschitz_subsequence t ht hCover L ((L : ℝ) * R) U hULip hUBound
  let w (x : Plane) : Target m := if hx : x ∈ Ω then (g ⟨x, hx⟩).1 else 0
  let p (x : Plane) : Plane →L[ℝ] Target m := if hx : x ∈ Ω then (g ⟨x, hx⟩).2 else 0
  have hU (j : ℕ) :
      TendstoUniformlyOn (fun n x => (N (k n) x, P (k n) x)) (fun x => (w x, p x))
        atTop (s j) := by
    intro v hv
    exact (hUniform j v hv).mono fun _ hn x hx => by
      simpa only [w, p, dite_eq_left (hSub j hx), U] using hn ⟨x, hSub j hx⟩ hx
  have hw (j : ℕ) : TendstoUniformlyOn (fun n => N (k n)) w atTop (s j) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    exact (Metric.tendstoUniformlyOn_iff.mp (hU j) ε hε).mono fun _ hn x hx =>
      (le_max_left _ _).trans_lt (hn x hx)
  have hp (j : ℕ) : TendstoUniformlyOn (fun n => P (k n)) p atTop (s j) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    exact (Metric.tendstoUniformlyOn_iff.mp (hU j) ε hε).mono fun _ hn x hx =>
      (le_max_right _ _).trans_lt (hn x hx)
  have hNormalDerivative (n : ℕ) (x : Plane) (hx : x ∈ Ω) : HasFDerivAt (N n) (P n x) x :=
    (hasFDerivAt_normalize_height (a := a) (hDiff n x hx)).differentiableAt.hasFDerivAt
  have hNormalContinuous (n : ℕ) : ContinuousOn (P n) Ω := by
    exact ((hCont n).sub continuousOn_const).congr fun x hx => fderiv_normalize_height (hDiff n x hx)
  obtain ⟨hC1, hDeriv⟩ := contDiffOn_one_of_compact_exhaustion hΩ s hExhaust
    (fun n => hNormalDerivative (k n)) (fun n => hNormalContinuous (k n)) hw hp
  have hwPoint (x : Plane) (hx : x ∈ Ω) : Tendsto (fun n => N (k n) x) atTop (𝓝 (w x)) := by
    obtain ⟨j, hj⟩ := hCover ⟨x, hx⟩
    exact (hw j).tendsto_at hj
  have hpPoint (x : Plane) (hx : x ∈ Ω) : Tendsto (fun n => P (k n) x) atTop (𝓝 (p x)) := by
    obtain ⟨j, hj⟩ := hCover ⟨x, hx⟩
    exact (hp j).tendsto_at hj
  refine ⟨w, p, k, hk, hC1, hDeriv, ?_, ?_, ?_, hw, hp⟩
  · exact tendsto_nhds_unique (hwPoint a ha) (by simpa only [N, normalize_height_self] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : Target m)) atTop (𝓝 0)))
  · exact tendsto_nhds_unique (hpPoint a ha) (by
      simpa only [P, N, fderiv_normalize_height_self (hDiff _ a ha)] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : Plane →L[ℝ] Target m)) atTop (𝓝 0)))
  · intro x hx y hy
    have hLimit := continuous_gradHS.continuousAt.tendsto.comp ((hpPoint x hx).sub (hpPoint y hy))
    exact le_of_tendsto hLimit (Eventually.of_forall fun n =>
      (normalized_gradient_bounds ha (hDiff (k n)) (hHS (k n))).1 x hx y hy)


/-- Its radius increases to `r`; early balls may be empty for small `r`. -/
@[expose] public noncomputable def diskExhaustion (a : Plane) (r : ℝ) (j : ℕ) : Set Plane :=
  Metric.closedBall a (r - 1 / ((j : ℝ) + 1))

public theorem diskExhaustion_compact (a : Plane) (r : ℝ) (j : ℕ) :
    IsCompact (diskExhaustion a r j) :=
  isCompact_closedBall _ _

public theorem diskExhaustion_subset (a : Plane) (r : ℝ) (j : ℕ) :
    diskExhaustion a r j ⊆ Metric.ball a r := by
  intro x hx
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hr : r - 1 / ((j : ℝ) + 1) < r :=
    sub_lt_self _ (one_div_pos.mpr hj)
  exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hx).trans_lt hr)

public theorem diskExhaustion_covers_compacts (a : Plane) (r : ℝ)
    (t : Set Plane) (ht : t ⊆ Metric.ball a r) (hCompact : IsCompact t) :
    ∃ j, t ⊆ diskExhaustion a r j := by
  rcases t.eq_empty_or_nonempty with rfl | htNonempty
  · exact ⟨0, empty_subset _⟩
  obtain ⟨x, hx, hMax⟩ := hCompact.exists_isMaxOn htNonempty
    ((continuous_id.dist continuous_const).continuousOn :
      ContinuousOn (fun y : Plane => dist y a) t)
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt
    (sub_pos.mpr (Metric.mem_ball.mp (ht hx)))
  refine ⟨j, fun y hy => Metric.mem_closedBall.mpr ?_⟩
  have hxy : dist y a ≤ dist x a := hMax hy
  exact hxy.trans (by linarith only [hj])


/-- The normalized subsequence theorem on a planar disk with its concentric
closed-ball exhaustion. -/
public theorem normalized_disk_potentials_compactness {m : ℕ} (a : Plane)
    (R K : ℝ≥0) (hR : 0 < R) (W : ℕ → Plane → Target m)
    (hDiff : ∀ n x, x ∈ Metric.ball a R → DifferentiableAt ℝ (W n) x)
    (hCont : ∀ n, ContinuousOn (fderiv ℝ (W n)) (Metric.ball a R))
    (hHS : ∀ n x, x ∈ Metric.ball a R → ∀ y, y ∈ Metric.ball a R →
      gradHS (fderiv ℝ (W n) x - fderiv ℝ (W n) y) ≤ (K : ℝ) * dist x y) :
    ∃ (w : Plane → Target m) (p : Plane → Plane →L[ℝ] Target m) (k : ℕ → ℕ),
      StrictMono k ∧ ContDiffOn ℝ 1 w (Metric.ball a R) ∧
      (∀ x ∈ Metric.ball a R, HasFDerivAt w (p x) x) ∧ w a = 0 ∧ p a = 0 ∧
      (∀ x ∈ Metric.ball a R, ∀ y ∈ Metric.ball a R,
        gradHS (p x - p y) ≤ (K : ℝ) * dist x y) ∧
      (∀ j, TendstoUniformlyOn (fun n => normalize_height (W (k n)) a) w atTop
        (diskExhaustion a R j)) ∧
      (∀ j, TendstoUniformlyOn (fun n => fderiv ℝ (normalize_height (W (k n)) a)) p atTop
        (diskExhaustion a R j)) :=
  normalized_potentials_compactness Metric.isOpen_ball (convex_ball a R)
    (Metric.mem_ball_self (by exact_mod_cast hR)) R K
    (fun _ hx => (Metric.mem_ball.mp hx).le)
    (diskExhaustion a R) (diskExhaustion_compact a R) (diskExhaustion_subset a R)
    (diskExhaustion_covers_compacts a R) W hDiff hCont hHS

end C2Riemannian
