module

public import C2Riemannian.IdealSchedule
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace C2Riemannian.IdealNode

/-- The sign of an ideal node is inherited between vertical steps and reset to a sign at a vertical split. -/
public theorem run_sigma_sq (layers : List IdealLayer) (s : ℝ) {node : IdealNode}
    (h : node ∈ run layers s) : node.sigma ^ 2 = 1 := by
  have hFold (ls : List IdealLayer) (nodes : List IdealNode)
      (hn : ∀ p ∈ nodes, p.sigma ^ 2 = 1) :
      ∀ p ∈ ls.foldl (fun ns layer => ns.flatMap fun q => q.split layer s) nodes, p.sigma ^ 2 = 1 := by
    induction ls generalizing nodes with
    | nil => exact hn
    | cons layer ls ih =>
      apply ih
      intro p hp
      obtain ⟨q, hq, hp⟩ := List.mem_flatMap.mp hp
      have hq' := hn q hq
      by_cases ha : q.active = true
      · simp [split, ha] at hp
        rcases hp with rfl | rfl <;>
          cases layer with
          | mk step count => cases step <;> simp [child, hq']
      · have ha' : q.active = false := Bool.eq_false_of_not_eq_true ha
        simp only [split, ha', Bool.false_eq_true, ite_false, List.mem_singleton] at hp
        simpa [hp] using hq'
  apply hFold layers [root] _ node h
  intro p hp
  simp only [List.mem_singleton] at hp
  subst p
  norm_num [root]

/-- The negative vertical phase has the exact linear source increment. -/
public theorem vertical_negative_linear_jump (node : IdealNode) (layer : IdealLayer)
    (h : layer.step = .vertical) (s θ : ℝ) :
    (θ / 10) * (node.scalar.yy - (node.child layer s false).scalar.yy) = θ / 10 := by
  simp [child, h, SplitStep.scalarChild, ScalarHess.rankOneUpdate]

/-- Each continuing sloped phase of the linear source has the lower bound used in the cubic estimate. -/
public theorem oblique_positive_linear_jump (node : IdealNode) (layer : IdealLayer)
    (h : layer.step = .first ∨ layer.step = .third) (s θ : ℝ)
    (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) (hσ : node.sigma ^ 2 = 1) :
    -(s ^ 2 / 10) ≤ (θ / 10) * (node.scalar.yy - (node.child layer s true).scalar.yy) := by
  have hσ' : -1 ≤ node.sigma := by nlinarith [mul_self_nonneg (node.sigma + 1)]
  have hs : -(s ^ 2) ≤ θ * node.sigma * s ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hσ' hθ
    have h' : -1 ≤ θ * node.sigma := by linarith
    nlinarith only [mul_le_mul_of_nonneg_right h' (sq_nonneg s)]
  rcases h with h | h <;> simp only [child, h, SplitStep.scalarChild, ite_true, one_mul, ScalarHess.rankOneUpdate] <;>
    nlinarith only [hs]

end C2Riemannian.IdealNode
