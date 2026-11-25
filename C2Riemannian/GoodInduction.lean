module

public import C2Riemannian.ParameterTreeLogic

set_option autoImplicit false

universe u

namespace C2Riemannian.ParameterTree

variable {A : Type u}

/-- The terminal and one-layer implications on the prefixes of the given tree.
A certificate may depend on the remaining depth and on the realized subtree.
The one-layer implication consumes certificates on one strictly increasing
sequence of good successor indices. -/
@[expose] public def HasCertificateTransfer
    (S : A → Prop) (C : {d : ℕ} → ParameterTree A d → Prop) :
    {r : ℕ} → ParameterTree A r → Prop
  | _, .leaf x => S x → C (.leaf x)
  | _, .node x children =>
      (∀ k, HasCertificateTransfer S C (children k)) ∧
      (∀ k : ℕ → ℕ, StrictMono k → (∀ i, Good S (children (k i))) →
        (∀ i, C (children (k i))) → C (.node x children))

/-- Inverse induction on the remaining depth propagates certificates to every
good root for which terminal certificates and one-layer transfer are available. -/
public theorem certificate_of_good {r : ℕ} (S : A → Prop)
    (C : {d : ℕ} → ParameterTree A d → Prop) (t : ParameterTree A r)
    (hTransfer : HasCertificateTransfer S C t) (hGood : Good S t) : C t := by
  induction t with
  | leaf x =>
    exact hTransfer ((good_leaf_iff S x).mp hGood)
  | node x children ih =>
    obtain ⟨k, hk, hChosen⟩ := infinite_good_children_subsequence S x children hGood 0
    have hGoodChild (i : ℕ) : Good S (children (k i)) := (hChosen i).2
    have hCertChild (i : ℕ) : C (children (k i)) :=
      ih (k i) (hTransfer.1 (k i)) (hGoodChild i)
    exact hTransfer.2 k hk hGoodChild hCertChild

public theorem bad_of_no_certificate {r : ℕ} (S : A → Prop)
    (C : {d : ℕ} → ParameterTree A d → Prop) (t : ParameterTree A r)
    (hTransfer : HasCertificateTransfer S C t) (hRoot : ¬ C t) : ¬ Good S t :=
  fun hGood => hRoot (certificate_of_good S C t hTransfer hGood)

/-- Obstructions to the two root certificates give one terminal path at which
both terminal predicates fail. -/
public theorem exists_path_of_two_root_obstructions {r : ℕ} (S T : A → Prop)
    (C D : {d : ℕ} → ParameterTree A d → Prop) (t : ParameterTree A r)
    (hTransferC : HasCertificateTransfer S C t) (hTransferD : HasCertificateTransfer T D t)
    (hRootC : ¬ C t) (hRootD : ¬ D t) :
    ∃ p : Path r, ¬ S (leafAt t p) ∧ ¬ T (leafAt t p) :=
  exists_path_of_both_bad S T t
    (bad_of_no_certificate S C t hTransferC hRootC)
    (bad_of_no_certificate T D t hTransferD hRootD)

end C2Riemannian.ParameterTree
