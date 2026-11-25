module

public import C2Riemannian.PhysicalConditionalSource
public import C2Riemannian.LinearLayerJumps
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Set
open scoped ContDiff

namespace C2Riemannian.PhysicalLayerRow

variable {Q : Set Plane} {directions : PhysicalDirections} {s δ : ℝ}
  {layer : IdealLayer} {p : PhysicalPrefix Q} {next : ℕ → PhysicalPrefix Q}

@[expose] public noncomputable def linearJump (p : PhysicalPrefix Q) (layer : IdealLayer)
    (s θ : ℝ) (i : p.Active) (sign : Bool) : ℝ :=
  (θ / 10) * ((p.ideal i.1).scalar.yy - ((p.ideal i.1).child layer s sign).scalar.yy)

@[expose] public noncomputable def reverseJump (p : PhysicalPrefix Q) (layer : IdealLayer)
    (s : ℝ) (i : p.Active) (sign : Bool) : ℝ :=
  ((p.ideal i.1).child layer s sign).scalar.reverseSource - (p.ideal i.1).scalar.reverseSource

private theorem child_subset_parent (row : PhysicalLayerRow directions s δ layer p next)
    (i : p.Active) (sign : Bool) (n : ℕ) :
    (next n).platform (row.childLabel n (i, sign)) ⊆ p.platform i.1 := by
  rw [row.child_platform]
  exact fun _ hx => row.frequencyContract.inner_subset n i hx.1

public theorem linear_exact_child_profile (row : PhysicalLayerRow directions s δ layer p next)
    (hp : p.ExactJets) (hExact : ∀ n, (next n).ExactJets)
    (i : p.Active) (sign : Bool) (n : ℕ)
    {v₀ : Plane → ℝ} (hv₀ : ContDiffOn ℝ 2 v₀ (p.platform i.1)) (θ : ℝ) :
    EqOn ((next n).linearSource v₀ θ) (fun x => p.linearSource v₀ θ x + linearJump p layer s θ i sign)
      ((next n).platform (row.childLabel n (i, sign))) := by
  intro x hx
  change (next n).linearSource v₀ θ x = p.linearSource v₀ θ x + linearJump p layer s θ i sign
  have hxp := child_subset_parent row i sign n hx
  rw [(next n).linearSource_eq_ideal (hExact n) _ hx (p.platform_open i.1) hxp hv₀ θ,
    p.linearSource_eq_ideal hp i.1 hxp (p.platform_open i.1) hxp hv₀ θ, row.child_ideal]
  unfold linearJump
  ring

public theorem reverse_exact_child_profile (row : PhysicalLayerRow directions s δ layer p next)
    (hp : p.ExactJets) (hExact : ∀ n, (next n).ExactJets)
    (i : p.Active) (sign : Bool) (n : ℕ) :
    EqOn (next n).reverseSource (fun x => p.reverseSource x + reverseJump p layer s i sign)
      ((next n).platform (row.childLabel n (i, sign))) := by
  intro x hx
  change (next n).reverseSource x = p.reverseSource x + reverseJump p layer s i sign
  have hxp := child_subset_parent row i sign n hx
  rw [(next n).reverseSource_eq_ideal (hExact n) _ hx, p.reverseSource_eq_ideal hp i.1 hxp, row.child_ideal]
  unfold reverseJump ScalarHess.reverseSource
  ring

end C2Riemannian.PhysicalLayerRow
