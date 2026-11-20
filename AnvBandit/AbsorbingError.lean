import AnvBandit.AbsorbingPublicCharge
import AnvBandit.AbsorbingExpectation

/-! The exact real phase-error sum, with one-based paper phases and zero-based
auxiliary states reconciled explicitly. -/
noncomputable section
open scoped BigOperators Classical
open Finset MeasureTheory
namespace AnvBandit.Absorbing
open Execution ExecutionLaw ExecutionBounds
variable {n K : ℕ} {Ω : Type*}

lemma error_weighted_sum_eq (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n) (ω : Ω) (Ph : ℕ) :
    (∑ j ∈ range Ph, dEll p.H p.β (j+1) * error M p lam X J j ω) =
      (∑ ℓ ∈ erroneousPhases M p lam X J ω Ph, (p.phaseEnd ℓ-p.phaseEnd (ℓ-1) : ℕ) : ℝ) := by
  let f := fun ℓ => ((p.phaseEnd ℓ-p.phaseEnd (ℓ-1) : ℕ) : ℝ) * error M p lam X J (ℓ-1) ω
  have hf0 : f 0 = 0 := by simp [f]
  have hs : (∑ j ∈ range Ph, dEll p.H p.β (j+1) * error M p lam X J j ω) =
      ∑ ℓ ∈ range (Ph+1), f ℓ := by
    rw [sum_range_succ']
    simp only [hf0, add_zero, f, Nat.add_sub_cancel, p.phaseLength_cast]
    have hz : dEll p.H p.β 0 = 0 := by simp [dEll, tEll]
    rw [hz, zero_mul, add_zero]
  rw [hs, erroneousPhases, sum_filter]
  apply sum_congr rfl
  intro ℓ hℓ
  by_cases hz : ℓ = 0
  · subst ℓ
    simp [f]
  · have hp : 1 ≤ ℓ := by omega
    simp only [f, error, Nat.sub_add_cancel hp, hp, true_and]
    split_ifs <;> simp

/-- Full pathwise C.9 for both original fatigue mechanisms, with the exact
personal/public minimum. No confidence event is supplied by the caller. -/
theorem actual_error_budget (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n) (ω : Ω) (Ph : ℕ) :
    (∑ j ∈ range Ph, dEll p.H p.β (j+1) * error M p lam X J j ω) ≤
      2 * M.Flam (unitCost M) p.L lam := by
  rw [error_weighted_sum_eq]
  fin_cases lam
  · exact actual_error_budget_personal_real M p 0 X J ω Ph
  · exact actual_error_budget_public M p X J ω Ph

lemma expected_error_budget (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (Ph : ℕ) :
    (∑ j ∈ range Ph, dEll p.H p.β (j+1) * expectedError M p C lam j) ≤
      2 * M.Flam (unitCost M) p.L lam := by
  let μ := executionMeasure M p C lam
  have hint : ∀ j ∈ range Ph, Integrable
      (fun ω => dEll p.H p.β (j+1) * error M p lam pathRewards (pathContacts p) j ω) μ :=
    fun j _ => (error_integrable M p C lam j).const_mul _
  have hi := integral_mono (integrable_finset_sum _ hint) (integrable_const
    (2 * M.Flam (unitCost M) p.L lam))
    (fun ω => actual_error_budget M p lam pathRewards (pathContacts p) ω Ph)
  rw [integral_finset_sum _ hint] at hi
  simp only [integral_const_mul, integral_const, measureReal_univ_eq_one, one_smul] at hi
  exact hi

/-- C.10 with the actual error budget discharged. Only the concrete ideal
remaining-series bound is left for C.13, not an arbitrary cost premise. -/
theorem finite_telescope_with_budget (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (Ph : ℕ) :
    (∑ j ∈ range Ph, dEll p.H p.β (j+1) * expectedMissing M p C lam j) ≤
      (∑ j ∈ range Ph, posPart (dEll p.H p.β (j+1)-dEll p.H p.β j) *
        expectedPotential M p C lam j) +
      2 * M1 (by have := p.hn; omega) C (holder p M.star) * M.Flam (unitCost M) p.L lam := by
  have hm : 0 ≤ M1 (by have := p.hn; omega) C (holder p M.star) := by
    rw [← Vpot_singleton]
    unfold Vpot
    exact sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have he := mul_le_mul_of_nonneg_left (expected_error_budget M p C lam Ph) hm
  have ht := finite_telescope M p C lam Ph
  nlinarith

end AnvBandit.Absorbing
