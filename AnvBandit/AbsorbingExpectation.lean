import AnvBandit.AbsorbingDrift
import AnvBandit.AbsorbingMeasurability
import AnvBandit.Potential

/-! Expected actual absorbed drift and finite positive-increment telescope.
No limit exchange or monotonicity of rounded phase lengths is assumed. -/
noncomputable section
open scoped BigOperators Classical
open Finset MeasureTheory ProbabilityTheory Preorder
set_option backward.isDefEq.respectTransparency false
namespace AnvBandit.Absorbing
open Execution ExecutionLaw ExecutionBounds
variable {n K : ℕ}

def expectedPotential (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (j : ℕ) : ℝ :=
  ∫ ω, Vpot (by have := p.hn; omega) C (holder p M.star)
    (state M p lam pathRewards (pathContacts p) j ω) ∂executionMeasure M p C lam

def expectedMissing (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (j : ℕ) : ℝ :=
  ∫ ω, ((univ \ state M p lam pathRewards (pathContacts p) j ω).card : ℝ)
    ∂executionMeasure M p C lam

def expectedError (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (j : ℕ) : ℝ :=
  ∫ ω, error M p lam pathRewards (pathContacts p) j ω ∂executionMeasure M p C lam

lemma expectedPotential_nonneg (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (j : ℕ) : 0 ≤ expectedPotential M p C lam j := by
  apply integral_nonneg
  intro ω
  unfold Vpot
  exact sum_nonneg fun i _ => ENNReal.toReal_nonneg

/-- C.8 after taking expectations. Integrability of every actual term has been
proved from finite-precontact factorization, not supplied as a premise. -/
theorem expected_drift (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (j : ℕ) :
    expectedMissing M p C lam j ≤ expectedPotential M p C lam j -
      expectedPotential M p C lam (j+1) +
      M1 (by have := p.hn; omega) C (holder p M.star) * expectedError M p C lam j := by
  let μ := executionMeasure M p C lam
  let t := p.phaseEnd (j+1)-1
  let G : MeasurableSpace (Path n) :=
    (Prod.instMeasurableSpace : MeasurableSpace (Precontact n t)).comap (beforeContact (n := n) t)
  let V := fun j ω => Vpot (by have := p.hn; omega) C (holder p M.star)
    (state M p lam pathRewards (pathContacts p) j ω)
  let m1 := M1 (by have := p.hn; omega) C (holder p M.star)
  have hv : Integrable (V j) μ := state_potential_integrable M p C lam j
  have he := (error_integrable M p C lam j).const_mul m1
  have hright : Integrable (fun ω => V j ω - μ[V (j+1) | G] ω +
      m1 * error M p lam pathRewards (pathContacts p) j ω) μ :=
    (hv.sub integrable_condExp).add he
  have hi := integral_mono_ae (missing_integrable M p C lam j) hright
    (conditional_absorbed_drift M p C lam j)
  have hG : G ≤ (MeasurableSpace.pi : MeasurableSpace (Path n)) := by
    dsimp only [G]
    exact (beforeContact_measurable (n := n) t).comap_le
  rw [integral_add
      (f := fun ω => V j ω - μ[V (j+1) | G] ω)
      (g := fun ω => m1 * error M p lam pathRewards (pathContacts p) j ω)
      (hv.sub integrable_condExp) he,
    integral_sub (f := V j) (g := μ[V (j+1) | G]) hv integrable_condExp,
    integral_condExp (μ := μ) (f := V (j+1)) hG, integral_const_mul] at hi
  exact hi

/-- Finite C.10. The positive increment is retained exactly; decreasing rounded
phase lengths are never silently treated as nondecreasing. -/
theorem finite_telescope (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (Ph : ℕ) :
    (∑ j ∈ range Ph, dEll p.H p.β (j+1) * expectedMissing M p C lam j) ≤
      (∑ j ∈ range Ph, posPart (dEll p.H p.β (j+1)-dEll p.H p.β j) *
        expectedPotential M p C lam j) +
      M1 (by have := p.hn; omega) C (holder p M.star) *
        ∑ j ∈ range Ph, dEll p.H p.β (j+1) * expectedError M p C lam j := by
  have hd : ∀ j, 0 ≤ dEll p.H p.β j := by
    intro j
    rw [← p.phaseLength_cast]
    positivity
  have hh : (∑ j ∈ range Ph, dEll p.H p.β (j+1) * expectedMissing M p C lam j) ≤
      ∑ j ∈ range Ph, dEll p.H p.β (j+1) *
        (expectedPotential M p C lam j - expectedPotential M p C lam (j+1) +
          M1 (by have := p.hn; omega) C (holder p M.star) * expectedError M p C lam j) :=
    sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (expected_drift M p C lam j) (hd (j+1))
  have hab := abel_bound (d := dEll p.H p.β)
    (u := fun ℓ => expectedPotential M p C lam (ℓ-1))
    (by simp [dEll, tEll]) hd (fun ℓ => expectedPotential_nonneg M p C lam (ℓ-1)) Ph
  simp only [Nat.add_sub_cancel, show ∀ j : ℕ, j+2-1 = j+1 by omega] at hab
  calc
    _ ≤ _ := hh
    _ = (∑ j ∈ range Ph, dEll p.H p.β (j+1) *
        (expectedPotential M p C lam j-expectedPotential M p C lam (j+1))) +
        M1 (by have := p.hn; omega) C (holder p M.star) *
        ∑ j ∈ range Ph, dEll p.H p.β (j+1) * expectedError M p C lam j := by
      rw [mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro j _
      ring
    _ ≤ _ := add_le_add hab le_rfl

end AnvBandit.Absorbing
