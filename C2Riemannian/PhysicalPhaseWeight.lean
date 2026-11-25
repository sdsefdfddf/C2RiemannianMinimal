module

public import C2Riemannian.PhysicalParameterTree
public import C2Riemannian.PhaseEquidistribution

set_option autoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped Topology

namespace C2Riemannian.PhysicalLayerRow

variable {Q : Set Plane} {directions : PhysicalDirections} {s δ : ℝ}
  {layer : IdealLayer} {p : PhysicalPrefix Q} {next : ℕ → PhysicalPrefix Q}

@[expose] public def parentOpen (p : PhysicalPrefix Q) (i : p.Active) : Opens Plane :=
  ⟨p.platform i.1, p.platform_open i.1⟩

/-- The factor two normalizes either phase to mass one in the weak-star limit. -/
@[expose] public noncomputable def phaseWeight (row : PhysicalLayerRow directions s δ layer p next)
    (_i : p.Active) (sign : Bool) (k : ℕ) (x : Plane) : ℝ :=
  2 * phaseIndicator (phaseInterval sign (row.frequencyContract.width k))
    (row.frequencyContract.frequency k * inner ℝ (directions.normal layer s) x)

public theorem mem_child_of_phaseWeight_ne_zero
    (row : PhysicalLayerRow directions s δ layer p next)
    (i : p.Active) (sign : Bool) (k : ℕ) {x : Plane}
    (hx : x ∈ row.frequencyContract.inner k i) (hw : row.phaseWeight i sign k x ≠ 0) :
    x ∈ (next k).platform (row.childLabel k (i, sign)) := by
  rw [row.child_platform]
  refine ⟨hx, ?_⟩
  by_contra h
  apply hw
  have h' : (row.frequencyContract.frequency k : ℝ) * inner ℝ (directions.normal layer s) x ∉
      periodicPhase (phaseInterval sign (row.frequencyContract.width k)) := h
  simp only [phaseWeight, phaseIndicator, indicator_of_notMem h', mul_zero]

/-- Equidistribution tests use the parent platform and the actual chosen
frequencies, including any strictly increasing subsequence. -/
public theorem phaseWeight_test_limit (row : PhysicalLayerRow directions s δ layer p next)
    (i : p.Active) (sign : Bool) (hn : directions.normal layer s ≠ 0)
    (k : ℕ → ℕ) (hk : StrictMono k) {γ : Plane → ℝ}
    (hγ : IntegrableOn γ (p.platform i.1) volume) :
    Tendsto (fun j => ∫ x in p.platform i.1, row.phaseWeight i sign (k j) x * γ x) atTop
      (𝓝 (∫ x in p.platform i.1, γ x)) := by
  have h := phase_weakstar_half (p.platform_open i.1) hn sign row.frequencyContract.width
    (fun n => (row.frequencyContract.frequency n : ℝ)) row.frequencyContract.width_pos
    row.frequencyContract.width_le_one_sixteenth row.frequencyContract.tendsto_width
    (fun n => by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 1) (row.frequencyContract.frequency_ge_one n))
    (tendsto_natCast_atTop_atTop.comp row.frequencyContract.tendsto_frequency) hγ
  exact h.comp hk.tendsto_atTop

end C2Riemannian.PhysicalLayerRow

