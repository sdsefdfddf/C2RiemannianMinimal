module

public import C2Riemannian.HessianAlgebra
public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Moments of positive normalized functionals

The conditional functionals of §5.1 act on real continuous readouts. The moment
identities in M32 apply on any topological state space.
-/

set_option autoImplicit false

namespace C2Riemannian

open scoped BigOperators

/-- Real positive linear functionals taking the constant one to one. -/
public structure PositiveFunctional (α : Type*) [TopologicalSpace α] extends
    C(α, ℝ) →ₚ[ℝ] ℝ where
  map_one : toPositiveLinearMap 1 = 1

namespace PositiveFunctional

variable {α : Type*} [TopologicalSpace α]

public instance : FunLike (PositiveFunctional α) C(α, ℝ) ℝ where
  coe L := L.toPositiveLinearMap
  coe_injective L M h := by
    cases L
    cases M
    congr
    exact DFunLike.coe_injective h

public instance : LinearMapClass (PositiveFunctional α) ℝ C(α, ℝ) ℝ where
  map_add L := map_add L.toPositiveLinearMap
  map_smulₛₗ L := map_smulₛₗ L.toPositiveLinearMap

public instance : OrderHomClass (PositiveFunctional α) C(α, ℝ) ℝ where
  map_rel L := fun {_ _} h => L.toPositiveLinearMap.monotone' h

@[simp] public theorem map_const (L : PositiveFunctional α) (c : ℝ) :
    L (ContinuousMap.const α c) = c := by
  have h : ContinuousMap.const α c = c • (1 : C(α, ℝ)) := by
    ext x
    simp
  rw [h, map_smul, smul_eq_mul]
  change c * L.toPositiveLinearMap 1 = c
  rw [L.map_one, mul_one]

/-- Point evaluation is a positive normalized functional. -/
@[expose] public def eval (x : α) : PositiveFunctional α where
  toPositiveLinearMap :=
    { toLinearMap :=
        { toFun := fun f => f x
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      monotone' := fun _ _ h => h x }
  map_one := rfl

@[simp] public theorem eval_apply (x : α) (f : C(α, ℝ)) : eval x f = f x := rfl

/-- Positivity compares a readout with any pointwise constant upper bound. -/
public theorem map_le_const (L : PositiveFunctional α) {f : C(α, ℝ)} {c : ℝ}
    (h : ∀ x, f x ≤ c) : L f ≤ c := by
  rw [← L.map_const c]
  exact L.toPositiveLinearMap.monotone' (ContinuousMap.le_def.mpr h)

end PositiveFunctional

section Readouts

variable {α E : Type*} [TopologicalSpace α]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The pointwise real inner product of two continuous vector readouts. -/
@[expose] public noncomputable def innerReadout (U V : C(α, E)) : C(α, ℝ) :=
  ⟨fun x => inner ℝ (U x) (V x), U.continuous.inner V.continuous⟩

@[simp] public theorem innerReadout_apply (U V : C(α, E)) (x : α) :
    innerReadout U V x = inner ℝ (U x) (V x) := rfl

/-- The pointwise squared Euclidean norm of a continuous vector readout. -/
@[expose] public noncomputable def sqNormReadout (U : C(α, E)) : C(α, ℝ) :=
  innerReadout U U

@[simp] public theorem sqNormReadout_apply (U : C(α, E)) (x : α) :
    sqNormReadout U x = ‖U x‖ ^ 2 :=
  real_inner_self_eq_norm_sq _

end Readouts

namespace PositiveFunctional

variable {α E : Type*} [TopologicalSpace α]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

public theorem map_sqNormReadout_nonneg (L : PositiveFunctional α) (U : C(α, E)) :
    0 ≤ L (sqNormReadout U) := by
  apply _root_.map_nonneg L
  rw [ContinuousMap.le_def]
  intro x
  simpa only [ContinuousMap.zero_apply, sqNormReadout_apply] using sq_nonneg ‖U x‖

/-- Positivity of the squared norm of every real linear combination gives
Cauchy–Schwarz for the bilinear form defined by the functional. -/
public theorem functional_CauchySchwarz (L : PositiveFunctional α) (U V : C(α, E)) :
    |L (innerReadout U V)| ^ 2 ≤ L (sqNormReadout U) * L (sqNormReadout V) := by
  have h (t : ℝ) :
      sqNormReadout (U - t • V) =
        (t * t) • sqNormReadout V + (-2 * t) • innerReadout U V + sqNormReadout U := by
    ext x
    simp only [sqNormReadout, innerReadout_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
      ContinuousMap.add_apply, smul_eq_mul, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right]
    rw [real_inner_comm (V x) (U x)]
    ring
  have hquad (t : ℝ) : 0 ≤ L (sqNormReadout V) * (t * t) +
      (-2 * L (innerReadout U V)) * t + L (sqNormReadout U) := by
    have hpos := L.map_sqNormReadout_nonneg (U - t • V)
    rw [h t, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hpos
    convert hpos using 1; ring
  have hd := discrim_le_zero hquad
  rw [discrim] at hd
  rw [sq_abs]
  nlinarith only [hd]

public theorem abs_map_innerReadout_le (L : PositiveFunctional α) (U V : C(α, E)) :
    |L (innerReadout U V)| ≤ √(L (sqNormReadout U)) * √(L (sqNormReadout V)) := by
  rw [← Real.sqrt_mul (L.map_sqNormReadout_nonneg U), ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by simpa only [sq_abs] using L.functional_CauchySchwarz U V)

public theorem scalar_CauchySchwarz (L : PositiveFunctional α) (f g : C(α, ℝ)) :
    |L (f * g)| ^ 2 ≤ L (f ^ 2) * L (g ^ 2) := by
  have h (u v : C(α, ℝ)) : innerReadout u v = u * v := by
    ext x
    exact Real.inner_apply _ _
  simpa only [sqNormReadout, h, pow_two] using L.functional_CauchySchwarz f g

/-- Scalar variance around the scalar mean. -/
public theorem scalar_variance (L : PositiveFunctional α) (f : C(α, ℝ)) :
    L ((f - ContinuousMap.const α (L f)) ^ 2) = L (f ^ 2) - (L f) ^ 2 := by
  have h : (f - ContinuousMap.const α (L f)) ^ 2 =
      f ^ 2 - (2 * L f) • f + ContinuousMap.const α ((L f) ^ 2) := by
    ext x
    simp only [ContinuousMap.pow_apply, ContinuousMap.sub_apply, ContinuousMap.add_apply,
      ContinuousMap.smul_apply, ContinuousMap.const_apply, smul_eq_mul]
    ring
  rw [h, map_add, map_sub, map_smul, smul_eq_mul, L.map_const]
  ring

public theorem scalar_mean_sq_le (L : PositiveFunctional α) (f : C(α, ℝ)) :
    (L f) ^ 2 ≤ L (f ^ 2) := by
  rw [← sub_nonneg, ← L.scalar_variance]
  exact _root_.map_nonneg L (ContinuousMap.le_def.mpr fun x => sq_nonneg
    ((f - ContinuousMap.const α (L f)) x))

variable {m : ℕ}

/-- The scalar readout of a single Euclidean coordinate. -/
@[expose] public def coord (U : C(α, Target m)) (i : Fin m) : C(α, ℝ) :=
  ⟨fun x => U x i, (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i).comp U.continuous⟩

/-- Euclidean mean, obtained by applying the same functional to every coordinate. -/
@[expose] public def mean (L : PositiveFunctional α) (U : C(α, Target m)) : Target m :=
  WithLp.toLp 2 (fun i => L (coord U i))

@[simp] public theorem mean_apply (L : PositiveFunctional α) (U : C(α, Target m)) (i : Fin m) :
    L.mean U i = L (coord U i) := rfl

public theorem map_innerReadout_const_right (L : PositiveFunctional α)
    (U : C(α, Target m)) (b : Target m) :
    L (innerReadout U (ContinuousMap.const α b)) = inner ℝ (L.mean U) b := by
  have h : innerReadout U (ContinuousMap.const α b) = ∑ i, (b i) • coord U i := by
    ext x
    simp [PiLp.inner_apply, coord]
  rw [h, map_sum, PiLp.inner_apply]
  simp only [map_smul, smul_eq_mul, Real.inner_apply, mean_apply, mul_comm]

public theorem map_innerReadout_const_left (L : PositiveFunctional α)
    (a : Target m) (V : C(α, Target m)) :
    L (innerReadout (ContinuousMap.const α a) V) = inner ℝ a (L.mean V) := by
  rw [← real_inner_comm a (L.mean V), ← L.map_innerReadout_const_right V a]
  congr 1
  ext x
  simp only [innerReadout_apply]
  exact real_inner_comm _ _

public theorem translate_inner (L : PositiveFunctional α) (U V : C(α, Target m))
    (a b : Target m) :
    L (innerReadout (U - ContinuousMap.const α a) (V - ContinuousMap.const α b)) =
      L (innerReadout U V) - inner ℝ (L.mean U) b -
        inner ℝ a (L.mean V) + inner ℝ a b := by
  have h : innerReadout (U - ContinuousMap.const α a) (V - ContinuousMap.const α b) =
      innerReadout U V - innerReadout U (ContinuousMap.const α b) -
        innerReadout (ContinuousMap.const α a) V + ContinuousMap.const α (inner ℝ a b) := by
    ext x
    simp only [innerReadout_apply, ContinuousMap.sub_apply, ContinuousMap.add_apply,
      ContinuousMap.const_apply, inner_sub_left, inner_sub_right]
    ring
  rw [h, map_add, map_sub, map_sub, L.map_const,
    L.map_innerReadout_const_right, L.map_innerReadout_const_left]

public theorem centered_inner (L : PositiveFunctional α) (U V : C(α, Target m)) :
    L (innerReadout (U - ContinuousMap.const α (L.mean U))
      (V - ContinuousMap.const α (L.mean V))) =
      L (innerReadout U V) - inner ℝ (L.mean U) (L.mean V) := by
  rw [L.translate_inner]
  ring

public theorem translate_sqNorm (L : PositiveFunctional α) (U : C(α, Target m))
    (a : Target m) :
    L (sqNormReadout (U - ContinuousMap.const α a)) =
      L (sqNormReadout U) - 2 * inner ℝ a (L.mean U) + ‖a‖ ^ 2 := by
  simp only [sqNormReadout, L.translate_inner, real_inner_comm (L.mean U) a,
    real_inner_self_eq_norm_sq]
  ring

public theorem functional_variance (L : PositiveFunctional α) (U : C(α, Target m)) :
    L (sqNormReadout (U - ContinuousMap.const α (L.mean U))) =
      L (sqNormReadout U) - ‖L.mean U‖ ^ 2 := by
  exact (L.centered_inner U U).trans (by rw [real_inner_self_eq_norm_sq]; rfl)

public theorem norm_mean_sq_le (L : PositiveFunctional α) (U : C(α, Target m)) :
    ‖L.mean U‖ ^ 2 ≤ L (sqNormReadout U) := by
  rw [← sub_nonneg, ← L.functional_variance]
  exact L.map_sqNormReadout_nonneg _

/-- Frobenius squared readout of continuous Hessian entries. -/
@[expose] public noncomputable def frobeniusSqReadout (X Z Y : C(α, Target m)) : C(α, ℝ) :=
  sqNormReadout X + (2 : ℝ) • sqNormReadout Z + sqNormReadout Y

@[simp] public theorem frobeniusSqReadout_apply (X Z Y : C(α, Target m)) (x : α) :
    frobeniusSqReadout X Z Y x = (Hess3.mk (X x) (Z x) (Y x)).frobeniusSq := by
  simp [frobeniusSqReadout, Hess3.frobeniusSq]

/-- Jensen's inequality for the Hessian mean and preservation of a Frobenius ball. -/
public theorem mean_hess_bound (L : PositiveFunctional α) (X Z Y : C(α, Target m)) (K : ℝ)
    (hK : ∀ x, (Hess3.mk (X x) (Z x) (Y x)).frobeniusSq ≤ K ^ 2) :
    (Hess3.mk (L.mean X) (L.mean Z) (L.mean Y)).frobeniusSq ≤
      L (frobeniusSqReadout X Z Y) ∧ L (frobeniusSqReadout X Z Y) ≤ K ^ 2 := by
  constructor
  · rw [frobeniusSqReadout, map_add, map_add, map_smul, smul_eq_mul, Hess3.frobeniusSq]
    exact add_le_add
      (add_le_add (L.norm_mean_sq_le X) (mul_le_mul_of_nonneg_left (L.norm_mean_sq_le Z) (by norm_num)))
      (L.norm_mean_sq_le Y)
  · exact L.map_le_const (fun x => (frobeniusSqReadout_apply X Z Y x).trans_le (hK x))

/-- Individual second moment bounds on the Frobenius ball. -/
public theorem hess_entry_moment_bounds (L : PositiveFunctional α) (X Z Y : C(α, Target m))
    (K : ℝ) (hK : ∀ x, (Hess3.mk (X x) (Z x) (Y x)).frobeniusSq ≤ K ^ 2) :
    L (sqNormReadout X) ≤ K ^ 2 ∧ L (sqNormReadout Z) ≤ K ^ 2 / 2 ∧
      L (sqNormReadout Y) ≤ K ^ 2 := by
  have h := (L.mean_hess_bound X Z Y K hK).2
  rw [frobeniusSqReadout, map_add, map_add, map_smul, smul_eq_mul] at h
  have hX := L.map_sqNormReadout_nonneg X
  have hZ := L.map_sqNormReadout_nonneg Z
  have hY := L.map_sqNormReadout_nonneg Y
  exact ⟨by linarith only [h, hZ, hY], by linarith only [h, hX, hY],
    by linarith only [h, hX, hZ]⟩

public theorem frobenius_mean_le (L : PositiveFunctional α) (X Z Y : C(α, Target m))
    (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ x, (Hess3.mk (X x) (Z x) (Y x)).frobeniusSq ≤ K ^ 2) :
    (Hess3.mk (L.mean X) (L.mean Z) (L.mean Y)).frobenius ≤ K := by
  obtain ⟨hmean, hmoment⟩ := L.mean_hess_bound X Z Y K h
  rw [Hess3.frobenius, ← Real.sqrt_sq hK]
  exact Real.sqrt_le_sqrt (hmean.trans hmoment)

end PositiveFunctional
end C2Riemannian
