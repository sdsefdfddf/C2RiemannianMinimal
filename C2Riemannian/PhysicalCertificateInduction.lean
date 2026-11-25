module

public import C2Riemannian.PhysicalParameterTree
public import C2Riemannian.GoodInduction

set_option autoImplicit false

namespace C2Riemannian.PhysicalParameterTree

variable {Q : Set Plane} {directions : PhysicalDirections} {s δ : ℝ}
  {Valid : List IdealLayer → PhysicalPrefix Q → Prop}

/-- Inverse induction on a realized physical tree. The one-layer transfer
receives the actual row and the validation of its parent and child prefixes. -/
public theorem physical_certificate_of_good
    (S : PhysicalPrefix Q → Prop) (C : List IdealLayer → PhysicalPrefix Q → Prop)
    (hTerminal : ∀ p, Valid [] p → S p → C [] p)
    (hLayer : ∀ layer tail p next,
      PhysicalLayerRow directions s δ layer p next →
      Valid (layer :: tail) p → (∀ j, Valid tail (next j)) →
      ∀ k : ℕ → ℕ, StrictMono k → (∀ j, C tail (next (k j))) → C (layer :: tail) p)
    {layers : List IdealLayer} {p : PhysicalPrefix Q}
    (T : PhysicalParameterTree directions s δ Valid layers p)
    (hGood : ParameterTree.Good S T.toParameterTree) : C layers p := by
  induction T with
  | terminal p hp =>
    exact hTerminal p hp ((ParameterTree.good_leaf_iff S p).mp hGood)
  | @branch layer tail p hp next row children ih =>
    change ParameterTree.Good S (.node p (fun j => (children j).toParameterTree)) at hGood
    obtain ⟨k, hk, hChosen⟩ := ParameterTree.infinite_good_children_subsequence S p
      (fun j => (children j).toParameterTree) hGood 0
    have hValid (j : ℕ) : Valid tail (next j) := by
      cases children j with
      | terminal _ h => exact h
      | branch _ h _ _ _ => exact h
    exact hLayer layer tail p next row hp hValid k hk (fun j => ih (k j) (hChosen j).2)

end C2Riemannian.PhysicalParameterTree
