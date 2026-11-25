module

public import C2Riemannian.SameDiskTangency
public import C2Riemannian.SameDiskBarycenter
public import C2Riemannian.SameDiskConditionalEnergy

set_option autoImplicit false
set_option maxHeartbeats 900000

open Filter MeasureTheory Set TopologicalSpace
open scoped NNReal Distributions Topology

namespace C2Riemannian.PhysicalLayerRow

variable {Q : Set Plane} {s δ : ℝ} {layer : IdealLayer}
  {p : PhysicalPrefix Q} {next : ℕ → PhysicalPrefix Q}
  {m : ℕ} {a : Plane} {R K : ℝ≥0}

/-- One same-disk limit and one common extraction supply the constitutive
identities and the energy upper bounds on both phases of every active parent. -/
public theorem exists_same_disk_phase_transfers
    (row : PhysicalLayerRow idealPhysicalDirections s δ layer p next)
    (hQ : Q ⊆ Metric.ball a R) (hBoundedQ : Bornology.IsBounded Q)
    {W : ℕ → WeakJet2 m (⟨Metric.ball a R, Metric.isOpen_ball⟩ : Opens Plane)}
    (C : WeakJet2.SameDiskLimit a R K W) (base : ℕ → ℕ) (hBase : StrictMono base)
    (F : PhysicalPrefix Q → Plane → ℝ) (Δ : p.Active → Bool → ℝ) (B : ℝ)
    (hHess : ∀ j, ∀ᵐ x ∂volume.restrict (Metric.ball a R),
      ((W j).hessian x).frobenius ≤ (K : ℝ))
    (hChildren : ∀ j, (fun x => ((W j).hessian x).q)
      =ᵐ[volume.restrict (Metric.ball a R)] F (next (base j)))
    (hParent : (fun x => (C.limit.hessian x).q) =ᵐ[volume.restrict (Metric.ball a R)] F p)
    (hSourceInt : ∀ i : p.Active, LocallyIntegrableOn (F p) (p.platform i.1) volume)
    (hJump : ∀ (i : p.Active) sign n, EqOn (F (next n)) (fun x => F p x + Δ i sign)
      ((next n).platform (row.childLabel n (i, sign))))
    (hEnergy : ∀ j (i : (next (base j)).Active),
      ∀ᵐ x ∂volume.restrict ((next (base j)).platform i.1), ((W j).hessian x).energy ≤ B) :
    ∃ L : p.Active × Bool → Plane → PositiveFunctional (HessianBall m K),
      ∀ i : p.Active, ∀ᵐ x ∂volume.restrict (p.platform i.1),
        (C.limit.hessian x).frobenius ≤ (K : ℝ) ∧
        (C.limit.hessian x).yy = (1 / 2 : ℝ) •
          ((L (i, true) x).mean HessianBall.yy + (L (i, false) x).mean HessianBall.yy) ∧
        ∀ sign, (HessianBall.meanHessian (L (i, sign) x)).applyRows (layer.tangent s 0) (layer.tangent s 1) =
          (C.limit.hessian x).applyRows (layer.tangent s 0) (layer.tangent s 1) ∧
          L (i, sign) x HessianBall.curvature - (C.limit.hessian x).q = Δ i sign ∧
          (layer.step.continues sign = true → L (i, sign) x HessianBall.energy ≤ B) := by
  have hn : idealPhysicalDirections.normal layer s ≠ 0 := layer.normal_ne_zero s
  obtain ⟨σ, state, L, hσ, hState, hEq, hL, hPair⟩ :=
    row.exists_same_disk_conditional_pairings hBoundedQ hn C hHess base hBase
  refine ⟨L, fun i => ?_⟩
  let P := p.platform i.1
  let k := base ∘ C.subseq ∘ σ
  let index := C.subseq ∘ σ
  let Lphase := fun sign x => L (i, sign) x
  have hsub : P ⊆ Metric.ball a R := (p.platform_subset i.1).trans hQ
  have hm := Measure.restrict_mono hsub (le_rfl : (volume : Measure Plane) ≤ volume)
  have hk : StrictMono k := hBase.comp (C.strictMono_subseq.comp hσ)
  have hBary := row.same_disk_hessian_barycenter_ae hn C i hsub base σ hBase hσ
    state hState hEq Lphase (fun sign f => hL (i, sign) f) (fun sign f γ => hPair (i, sign) f γ)
  have hTan := row.same_disk_conditional_phase_mean_tangent_ae i hn (layer.tangent s)
    (layer.inner_normal_tangent s) C hsub base σ hBase hσ state L hEq hL hPair
  have hCurv (sign : Bool) :
      ∀ᵐ x ∂volume.restrict P, Lphase sign x HessianBall.curvature - (C.limit.hessian x).q = Δ i sign := by
    let q := HessianBall.curvature (m := m) (K := (K : ℝ))
    let _ : CompactSpace (HessianBall m K) :=
      isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : HessSpace m) K)
    let _ : IsFiniteMeasure (volume.restrict P) :=
      isFiniteMeasure_restrict.mpr (hBoundedQ.subset (p.platform_subset i.1)).measure_lt_top.ne
    have hi : IntegrableOn (fun x => Lphase sign x q) P volume :=
      Integrable.of_bound (hL (i, sign) q).aestronglyMeasurable ‖q‖
        (Eventually.of_forall fun x => (Lphase sign x).norm_readout_le q)
    have hb : LocallyIntegrableOn (fun x => F p x + Δ i sign) P volume :=
      (hSourceInt i).add (continuousOn_const.locallyIntegrableOn (p.platform_open i.1).measurableSet)
    have hChild (j : ℕ) : (fun x => q (state (index j) x))
        =ᵐ[volume.restrict P] F (next (k j)) := by
      filter_upwards [(C.normalized (index j)).hessian_state_readouts_ae (hEq (index j)) hsub,
        MeasureTheory.ae_mono hm (hChildren (index j))] with x hq hx
      refine hq.2.2.2.trans ?_
      change ((C.normalized (index j)).hessian x).q = F (next (base (index j))) x
      rw [(C.normalized_data (index j)).2.1]
      exact hx
    have hh := row.conditional_phase_source_ae i sign hn k hk (fun n => F (next n))
      (fun j x => q (state (index j) x)) (fun x => F p x + Δ i sign) (fun x => Lphase sign x q)
      hb hi.locallyIntegrableOn hChild (hJump i sign) ?_
    · filter_upwards [hh, MeasureTheory.ae_mono hm hParent] with x hx hpq
      change Lphase sign x q - (C.limit.hessian x).q = Δ i sign
      rw [hx, hpq, add_sub_cancel_left]
    · intro φ
      have hφ : IntegrableOn (φ : Plane → ℝ) P volume :=
        (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).integrableOn
      simpa only [k, index, Lphase, Function.comp_apply, mul_comm, mul_left_comm, mul_assoc] using hPair (i, sign) q φ hφ
  have hE (sign : Bool) : ∀ᵐ x ∂volume.restrict P,
      layer.step.continues sign = true → Lphase sign x HessianBall.energy ≤ B := by
    by_cases hContinue : layer.step.continues sign = true
    · refine (row.same_disk_conditional_energy_bound i sign hContinue hQ hBoundedQ hn k hk
        (C.normalized ∘ index) (state ∘ index) (Lphase sign) B
        (fun j => hState (index j)) (fun j => hEq (index j)) (hL (i, sign) HessianBall.energy)
        ?_ (hPair (i, sign) HessianBall.energy)).mono (fun _ hx _ => hx)
      intro j i'
      change ∀ᵐ x ∂volume.restrict ((next (base (index j))).platform i'.1),
        ((C.normalized (index j)).hessian x).energy ≤ B
      rw [(C.normalized_data (index j)).2.1]
      exact hEnergy (index j) i'
    · exact Eventually.of_forall fun _ hx => (hContinue hx).elim
  filter_upwards [MeasureTheory.ae_mono hm C.bounds.frobenius_bound, hBary, hTan,
    ae_all_iff.2 hCurv, ae_all_iff.2 hE] with x hH hY ht hq he
  exact ⟨hH, hY.2.2, fun sign => ⟨ht sign, hq sign, he sign⟩⟩

end C2Riemannian.PhysicalLayerRow
