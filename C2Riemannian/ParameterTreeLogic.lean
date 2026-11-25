module

public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Order.OrderIsoNat

set_option autoImplicit false

universe u

namespace C2Riemannian

/-- A finite-depth parameter tree with a payload at each prefix.
The successors correspond to the natural-number choices of frequency. -/
public inductive ParameterTree (A : Type u) : ℕ → Type u
  | leaf : A → ParameterTree A 0
  | node {r : ℕ} : A → (ℕ → ParameterTree A r) → ParameterTree A (r + 1)

namespace ParameterTree

variable {A : Type u} {r : ℕ}

/-- The payload attached to the root of a subtree. -/
@[expose] public def payload : ParameterTree A r → A
  | .leaf x => x
  | .node x _ => x

@[expose] public def Good (S : A → Prop) {r : ℕ} : ParameterTree A r → Prop
  | .leaf x => S x
  | .node _ children => {k | Good S (children k)}.Infinite

@[expose] public def HasLeaf (P : A → Prop) {r : ℕ} : ParameterTree A r → Prop
  | .leaf x => P x
  | .node _ children => ∃ k, HasLeaf P (children k)

@[expose] public def EveryLeaf (P : A → Prop) {r : ℕ} : ParameterTree A r → Prop
  | .leaf x => P x
  | .node _ children => ∀ k, EveryLeaf P (children k)

/-- A list of successor choices whose length is the remaining depth. -/
public inductive Path : ℕ → Type
  | nil : Path 0
  | cons {r : ℕ} : ℕ → Path r → Path (r + 1)

/-- Follow all choices in a path and return the corresponding terminal payload. -/
@[expose] public def leafAt {r : ℕ} : ParameterTree A r → Path r → A
  | .leaf x, .nil => x
  | .node _ children, .cons k path => leafAt (children k) path

public theorem good_leaf_iff (S : A → Prop) (x : A) :
    Good S (.leaf x) ↔ S x := Iff.rfl

public theorem good_nonterminal_iff (S : A → Prop) (x : A)
    (children : ℕ → ParameterTree A r) :
    Good S (.node x children) ↔ {k | Good S (children k)}.Infinite := Iff.rfl

public theorem good_of_everyLeaf (S : A → Prop) (t : ParameterTree A r) :
    EveryLeaf S t → Good S t := by
  induction t with
  | leaf x => exact id
  | node x children ih =>
    intro hall
    change (∀ k, EveryLeaf S (children k)) at hall
    rw [good_nonterminal_iff]
    exact Set.infinite_univ.mono (fun k _ => ih k (hall k))

/-- Every prescribed tail of the good successor indices contains a strictly
increasing sequence of good successors. -/
public theorem infinite_good_children_subsequence (S : A → Prop) (x : A)
    (children : ℕ → ParameterTree A r) (h : Good S (.node x children)) (start : ℕ) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ i, start ≤ k i ∧ Good S (children (k i)) := by
  classical
  let indices := {k | Good S (children k)} \ Set.Iio start
  have hInitial : (Set.Iio start).Finite := by
    simpa only [Finset.coe_Iio] using (Finset.Iio start).finite_toSet
  have hi : indices.Infinite := ((good_nonterminal_iff S x children).mp h).sdiff hInitial
  let _ : Infinite indices := hi.to_subtype
  let k := Nat.orderEmbeddingOfSet indices
  refine ⟨k, k.strictMono, fun i => ?_⟩
  have hr : Set.range k = indices := Nat.orderEmbeddingOfSet_range indices
  have hk : k i ∈ indices := hr ▸ Set.mem_range_self i
  exact ⟨le_of_not_gt hk.2, hk.1⟩

public theorem two_bad_child_exists (S T : A → Prop) (x : A)
    (children : ℕ → ParameterTree A r) (hs : ¬ Good S (.node x children))
    (ht : ¬ Good T (.node x children)) :
    ∃ k, ¬ Good S (children k) ∧ ¬ Good T (children k) := by
  have hfs : {k | Good S (children k)}.Finite :=
    Set.not_infinite.mp (fun h => hs ((good_nonterminal_iff S x children).mpr h))
  have hft : {k | Good T (children k)}.Finite :=
    Set.not_infinite.mp (fun h => ht ((good_nonterminal_iff T x children).mpr h))
  obtain ⟨k, hk⟩ := (hfs.union hft).exists_notMem
  exact ⟨k, fun h => hk (Or.inl h), fun h => hk (Or.inr h)⟩

public theorem hasLeaf_of_both_bad (S T : A → Prop) (t : ParameterTree A r) :
    ¬ Good S t → ¬ Good T t → HasLeaf (fun x => ¬ S x ∧ ¬ T x) t := by
  induction t with
  | leaf x =>
    intro hs ht
    exact ⟨hs, ht⟩
  | node x children ih =>
    intro hs ht
    obtain ⟨k, hks, hkt⟩ := two_bad_child_exists S T x children hs ht
    exact ⟨k, ih k hks hkt⟩

public theorem exists_path_of_hasLeaf (P : A → Prop) (t : ParameterTree A r) :
    HasLeaf P t → ∃ p : Path r, P (leafAt t p) := by
  induction t with
  | leaf x =>
    intro hx
    exact ⟨.nil, hx⟩
  | node x children ih =>
    intro h
    obtain ⟨k, hk⟩ := h
    obtain ⟨p, hp⟩ := ih k hk
    exact ⟨.cons k p, hp⟩

public theorem exists_path_of_both_bad (S T : A → Prop) (t : ParameterTree A r)
    (hs : ¬ Good S t) (ht : ¬ Good T t) :
    ∃ p : Path r, ¬ S (leafAt t p) ∧ ¬ T (leafAt t p) :=
  exists_path_of_hasLeaf _ t (hasLeaf_of_both_bad S T t hs ht)

end ParameterTree

end C2Riemannian
