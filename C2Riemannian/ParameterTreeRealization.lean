module

public import C2Riemannian.ParameterTreeLogic

set_option autoImplicit false

universe u

namespace C2Riemannian.ParameterTree

variable {A : Type u}

/-- Every parent carries a simultaneous contract for its full sequence of successors.
The natural number is the remaining depth. -/
@[expose] public def SatisfiesRealization (Valid : ℕ → A → Prop)
    (Successors : ℕ → A → (ℕ → A) → Prop) :
    {r : ℕ} → ParameterTree A r → Prop
  | 0, .leaf a => Valid 0 a
  | r + 1, .node a next =>
      Valid (r + 1) a ∧ Successors r a (fun k => (next k).payload) ∧
        ∀ k, SatisfiesRealization Valid Successors (next k)

/-- Simultaneous choices at each valid parent yield an entire realized tree
with the prescribed root and a successor at each natural index. -/
public theorem exists_of_realized_successors
    (Valid : ℕ → A → Prop) (Successors : ℕ → A → (ℕ → A) → Prop)
    (hStep : ∀ r a, Valid (r + 1) a →
      ∃ next : ℕ → A, Successors r a next ∧ ∀ k, Valid r (next k))
    (r : ℕ) (a : A) (ha : Valid r a) :
    ∃ t : ParameterTree A r, t.payload = a ∧ SatisfiesRealization Valid Successors t := by
  induction r generalizing a with
  | zero => exact ⟨.leaf a, rfl, ha⟩
  | succ r ih =>
      obtain ⟨next, hNext, hValid⟩ := hStep r a ha
      choose t hPayload hTree using fun k => ih (next k) (hValid k)
      refine ⟨.node a t, rfl, ha, ?_, hTree⟩
      have hEq : (fun k => (t k).payload) = next := funext hPayload
      exact hEq.symm ▸ hNext

/-- Every terminal path ends at data satisfying the terminal contract. -/
public theorem satisfiesRealization_leafAt
    {Valid : ℕ → A → Prop} {Successors : ℕ → A → (ℕ → A) → Prop}
    {r : ℕ} (t : ParameterTree A r) (h : SatisfiesRealization Valid Successors t)
    (p : Path r) : Valid 0 (leafAt t p) := by
  induction t with
  | leaf a =>
      cases p
      exact h
  | node a next ih =>
      cases p with
      | cons k tail => exact ih k (h.2.2 k) tail

end C2Riemannian.ParameterTree

