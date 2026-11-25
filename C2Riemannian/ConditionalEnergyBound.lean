module

public import C2Riemannian.PhysicalPhaseWeight
public import C2Riemannian.WeakOrderTests

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions Topology

namespace C2Riemannian.PhysicalLayerRow

variable {Q : Set Plane} {directions : PhysicalDirections} {s δ : ℝ}
  {layer : IdealLayer} {p : PhysicalPrefix Q} {next : ℕ → PhysicalPrefix Q}

/-- An almost-everywhere upper bound on the selected child platforms passes
to their conditional energy readout on the parent platform. -/
public theorem conditional_energy_bound_ae
    (row : PhysicalLayerRow directions s δ layer p next)
    (i : p.Active) (sign : Bool) (hn : directions.normal layer s ≠ 0)
    (k : ℕ → ℕ) (hk : StrictMono k) (energy : ℕ → Plane → ℝ) (readout : Plane → ℝ) (B : ℝ)
    (hr : LocallyIntegrableOn readout (p.platform i.1) volume)
    (hChild : ∀ j, ∀ᵐ x ∂volume.restrict (p.platform i.1),
      x ∈ (next (k j)).platform (row.childLabel (k j) (i, sign)) → energy j x ≤ B)
    (hInt : ∀ j (φ : 𝓓(parentOpen p i, ℝ)),
      IntegrableOn (fun x => row.phaseWeight i sign (k j) x * energy j x * φ x)
        (p.platform i.1) volume ∧
      IntegrableOn (fun x => row.phaseWeight i sign (k j) x * B * φ x)
        (p.platform i.1) volume)
    (hCond : ∀ φ : 𝓓(parentOpen p i, ℝ),
      Tendsto (fun j => ∫ x in p.platform i.1, row.phaseWeight i sign (k j) x * energy j x * φ x)
        atTop (𝓝 (∫ x in p.platform i.1, φ x * readout x))) :
    ∀ᵐ x ∂volume.restrict (p.platform i.1), readout x ≤ B := by
  have hConst : LocallyIntegrableOn (fun _ : Plane => B) (p.platform i.1) volume :=
    continuous_const.continuousOn.locallyIntegrableOn (p.platform_open i.1).measurableSet
  have h := ae_nonpos_of_locallyIntegrable_nonneg_test_integrals (U := parentOpen p i) (hr.sub hConst) ?_
  · exact h.mono fun x hx => sub_nonpos.mp hx
  · intro φ hφ
    have hφInt : IntegrableOn (fun x => B * φ x) (p.platform i.1) volume :=
      (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).integrableOn.const_mul B
    have hLimit : Tendsto (fun j => ∫ x in p.platform i.1, row.phaseWeight i sign (k j) x * B * φ x)
        atTop (𝓝 (∫ x in p.platform i.1, B * φ x)) := by
      simpa only [mul_assoc] using row.phaseWeight_test_limit i sign hn k hk hφInt
    have hComp := row.frequencyContract.eventually_contains_compact i
      (tsupport (φ : Plane → ℝ)) φ.tsupport_subset φ.hasCompactSupport
    have hLe := le_of_tendsto_of_tendsto (hCond φ) hLimit ?_
    · simp only [Pi.sub_apply, mul_sub]
      have hri : IntegrableOn (fun x => φ x * readout x) (p.platform i.1) volume := by
        simpa only [smul_eq_mul] using (TauCeti.integrable_smul_of_locallyIntegrableOn hr φ).integrableOn
      have hbi : IntegrableOn (fun x => φ x * B) (p.platform i.1) volume := by
        simpa only [mul_comm] using hφInt
      have hP : (parentOpen p i : Set Plane) = p.platform i.1 := rfl
      rw [hP, integral_sub hri hbi]
      exact sub_nonpos.mpr (by simpa only [mul_comm] using hLe)
    · filter_upwards [hk.tendsto_atTop.eventually hComp] with j hj
      apply integral_mono_ae (hInt j φ).1 (hInt j φ).2
      filter_upwards [hChild j] with x hx
      by_cases hφx : x ∈ tsupport (φ : Plane → ℝ)
      · by_cases hw : row.phaseWeight i sign (k j) x = 0
        · simp only [hw, zero_mul, le_refl]
        · have hChildMem := row.mem_child_of_phaseWeight_ne_zero i sign (k j) (hj hφx) hw
          have hNonneg : 0 ≤ row.phaseWeight i sign (k j) x :=
            mul_nonneg (by norm_num) (phaseIndicator_mem_Icc _ _).1
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hx hChildMem) hNonneg) (hφ x)
      · simp only [image_eq_zero_of_notMem_tsupport hφx, mul_zero, le_refl]

end C2Riemannian.PhysicalLayerRow
