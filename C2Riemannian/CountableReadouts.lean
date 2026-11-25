module

public import C2Riemannian.HessianFrobenius
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

set_option autoImplicit false

open Set MeasureTheory TopologicalSpace

namespace C2Riemannian

/-- A countable rational algebra dense in the continuous scalar readouts,
including any given countable family of distinguished readouts. -/
public theorem exists_countable_dense_readout_algebra
    {X : Type*} [TopologicalSpace X] [SecondCountableTopology X] [LocallyCompactSpace X]
    (distinguished : ℕ → C(X, ℝ)) :
    ∃ A : Subalgebra ℚ C(X, ℝ), (A : Set C(X, ℝ)).Countable ∧ Dense (A : Set C(X, ℝ)) ∧
      ∀ n, distinguished n ∈ A := by
  obtain ⟨dense, hDense⟩ := exists_dense_seq (C(X, ℝ))
  let g : Bool × ℕ → C(X, ℝ) := fun p => if p.1 then distinguished p.2 else dense p.2
  let ev : MvPolynomial (Bool × ℕ) ℚ →ₐ[ℚ] C(X, ℝ) := MvPolynomial.aeval g
  have hGen (p : Bool × ℕ) : g p ∈ ev.range :=
    ⟨MvPolynomial.X p, MvPolynomial.aeval_X g p⟩
  let _ : Countable (MvPolynomial (Bool × ℕ) ℚ) :=
    (AddMonoidAlgebra.coeff_injective :
      Function.Injective (AddMonoidAlgebra.coeff :
        MvPolynomial (Bool × ℕ) ℚ → (((Bool × ℕ) →₀ ℕ) →₀ ℚ))).countable
  refine ⟨ev.range, Set.countable_range ev, hDense.mono ?_, ?_⟩
  · rintro _ ⟨n, rfl⟩
    change dense n ∈ ev.range
    simpa only [g, Bool.false_eq_true, ite_false] using hGen (false, n)
  · intro n
    simpa only [g, ite_true] using hGen (true, n)

/-- The Hessian state space used for conditional readouts, in Frobenius coordinates. -/
public abbrev HessianBall (m : ℕ) (K : ℝ) :=
  ↥(Metric.closedBall (0 : HessSpace m) K)

/-- The compact Hessian ball has a countable dense rational readout algebra. -/
public theorem exists_hessian_readout_algebra (m : ℕ) (K : ℝ)
    (distinguished : ℕ → C(HessianBall m K, ℝ)) :
    ∃ A : Subalgebra ℚ C(HessianBall m K, ℝ),
      (A : Set C(HessianBall m K, ℝ)).Countable ∧ Dense (A : Set C(HessianBall m K, ℝ)) ∧
      ∀ n, distinguished n ∈ A := by
  let _ : CompactSpace (HessianBall m K) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : HessSpace m) K)
  exact exists_countable_dense_readout_algebra distinguished

/-- A dense sequence of L¹ tests for a finite measure on the Borel plane. -/
public theorem exists_dense_L1_tests (μ : Measure Plane) [IsFiniteMeasure μ] :
    ∃ test : ℕ → Lp ℝ 1 μ, DenseRange test := by
  let _ : Fact ((1 : ENNReal) ≤ 1) := ⟨le_rfl⟩
  let _ : Fact ((1 : ENNReal) ≠ ⊤) := ⟨ENNReal.one_ne_top⟩
  exact exists_dense_seq _

end C2Riemannian
