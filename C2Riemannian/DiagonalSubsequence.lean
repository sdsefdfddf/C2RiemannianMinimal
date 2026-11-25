module

public import Mathlib.Order.WellFounded
public import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Set.Function

set_option autoImplicit false

namespace C2Riemannian

private theorem strictMono_factor_of_range {f g : ℕ → ℕ}
    (hf : StrictMono f) (hg : StrictMono g) (hr : Set.range g ⊆ Set.range f) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ g = f ∘ k := by
  have he (n : ℕ) : ∃ i, f i = g n := hr (Set.mem_range_self n)
  choose k hk using he
  have hmono : StrictMono k := by
    intro m n hmn
    apply (hf.lt_iff_lt).mp
    rw [hk m, hk n]
    exact hg hmn
  exact ⟨k, hmono, funext fun n => (hk n).symm⟩

/-- Countably many properties of an index sequence hold on a common subsequence
when each can be obtained by refinement, survives further refinement, and
extends from a tail of the sequence to the entire sequence. -/
public theorem diagonal_subsequence
    (R : ℕ → (ℕ → ℕ) → Prop)
    (refine_one : ∀ j σ, StrictMono σ → ∃ k : ℕ → ℕ, StrictMono k ∧ R j (σ ∘ k))
    (refine_stable : ∀ j σ k, StrictMono σ → StrictMono k → R j σ → R j (σ ∘ k))
    (tail_stable : ∀ j σ (c : ℕ), StrictMono σ → R j (fun n => σ (n + c)) → R j σ) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∀ j, R j τ := by
  let MonotoneIndex := {σ : ℕ → ℕ // StrictMono σ}
  let next (j : ℕ) (σ : MonotoneIndex) : MonotoneIndex :=
    ⟨(refine_one j σ.1 σ.2).choose, (refine_one j σ.1 σ.2).choose_spec.1⟩
  let row : ℕ → MonotoneIndex :=
    fun n => Nat.rec ⟨id, fun _ _ h => h⟩
      (fun j σ => ⟨σ.1 ∘ (next j σ).1, σ.2.comp (next j σ).2⟩) n
  have hStep (j n : ℕ) : (row (j + 1)).1 n = (row j).1 ((next j (row j)).1 n) := rfl
  have hRow (j : ℕ) : R j (row (j + 1)).1 :=
    (refine_one j (row j).1 (row j).2).choose_spec.2
  have hNested (m n : ℕ) (hmn : m ≤ n) :
      Set.range (row n).1 ⊆ Set.range (row m).1 := by
    refine Nat.le_induction (fun _ hx => hx) (fun j _ ih => ?_) n hmn
    rintro _ ⟨i, rfl⟩
    exact ih ⟨(next j (row j)).1 i, (hStep j i).symm⟩
  let τ (n : ℕ) := (row n).1 n
  have hτ : StrictMono τ := by
    apply strictMono_nat_of_lt_succ
    intro n
    change (row n).1 n < (row (n + 1)).1 (n + 1)
    rw [hStep]
    exact ((row n).2 (Nat.lt_succ_self n)).trans_le
      ((row n).2.monotone (next n (row n)).2.le_apply)
  refine ⟨τ, hτ, fun j => ?_⟩
  let tail (n : ℕ) := τ (n + (j + 1))
  have ht : StrictMono tail := fun _ _ h => hτ (Nat.add_lt_add_right h (j + 1))
  have hr : Set.range tail ⊆ Set.range (row (j + 1)).1 := by
    rintro _ ⟨n, rfl⟩
    exact hNested (j + 1) (n + (j + 1)) (Nat.le_add_left _ _) (Set.mem_range_self _)
  obtain ⟨k, hk, hFactor⟩ := strictMono_factor_of_range (row (j + 1)).2 ht hr
  apply tail_stable j τ (j + 1) hτ
  change R j tail
  rw [hFactor]
  exact refine_stable j (row (j + 1)).1 k (row (j + 1)).2 hk (hRow j)


/-- The common subsequence can be taken inside a prescribed index sequence. -/
public theorem diagonal_subsequence_from
    (R : ℕ → (ℕ → ℕ) → Prop)
    (refine_one : ∀ j σ, StrictMono σ → ∃ k : ℕ → ℕ, StrictMono k ∧ R j (σ ∘ k))
    (refine_stable : ∀ j σ k, StrictMono σ → StrictMono k → R j σ → R j (σ ∘ k))
    (tail_stable : ∀ j σ (c : ℕ), StrictMono σ → R j (fun n => σ (n + c)) → R j σ)
    (base : ℕ → ℕ) (hBase : StrictMono base) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∀ j, R j (base ∘ τ) :=
  diagonal_subsequence (fun j σ => R j (base ∘ σ))
    (fun j σ hσ => refine_one j (base ∘ σ) (hBase.comp hσ))
    (fun j σ k hσ hk h => refine_stable j (base ∘ σ) k (hBase.comp hσ) hk h)
    (fun j σ c hσ h => tail_stable j (base ∘ σ) c (hBase.comp hσ) h)

end C2Riemannian
