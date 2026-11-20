import AnvBandit.AbsorbingLoss
import AnvBandit.AbsorbingBound

/-! Exact actual potential branch. The legacy combination theorem's cost and
potential premises are discharged here, rather than exposed at the final entry. -/
noncomputable section
open scoped BigOperators Classical
open Finset MeasureTheory
namespace AnvBandit.Absorbing
open Execution ExecutionLaw ActualPropagation GlobalRegret
variable {n K : ℕ}

lemma missing_drift_budget (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (Ph : ℕ) :
    (∑ j ∈ range Ph, dEll p.H p.β (j+1) * expectedMissing M p C lam j) ≤
      (∑ j ∈ range Ph, dEll p.H p.β (j+1) *
        (expectedPotential M p C lam j-expectedPotential M p C lam (j+1))) +
      2 * M1 (by have := p.hn; omega) C (holder p M.star) * M.Flam (unitCost M) p.L lam := by
  have hd : ∀ j, 0 ≤ dEll p.H p.β j := by
    intro j
    rw [← p.phaseLength_cast]
    positivity
  have hh := sum_le_sum (fun j (_ : j ∈ range Ph) =>
    mul_le_mul_of_nonneg_left (expected_drift M p C lam j) (hd (j+1)))
  have he : (∑ j ∈ range Ph, dEll p.H p.β (j+1) *
        (expectedPotential M p C lam j-expectedPotential M p C lam (j+1) +
          M1 (by have := p.hn; omega) C (holder p M.star) * expectedError M p C lam j)) =
      (∑ j ∈ range Ph, dEll p.H p.β (j+1) *
        (expectedPotential M p C lam j-expectedPotential M p C lam (j+1))) +
      M1 (by have := p.hn; omega) C (holder p M.star) *
        ∑ j ∈ range Ph, dEll p.H p.β (j+1) * expectedError M p C lam j := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    ring
  rw [he] at hh
  have hm : 0 ≤ M1 (by have := p.hn; omega) C (holder p M.star) := by
    unfold M1
    exact sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hb := mul_le_mul_of_nonneg_left (expected_error_budget M p C lam Ph) hm
  nlinarith

/-- The exact potential branch for the actual Algorithm 1 and either original
fatigue mechanism, with no derived bound or algorithm invariant as an input.
Its left side is the same good-event expected loss used by the other branches. -/
theorem weighted_loss_potential_branch (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (c : Fin K → ℝ)
    (hc : ∀ k, 0 ≤ c k) (hstar : c M.star = 0) :
    goodLoss M p C lam c ≤ M.Flam c p.L lam + M.supOthers c *
      (2 * M1 (by have := p.hn; omega) C (holder p M.star) * M.Flam (unitCost M) p.L lam +
        concreteKbeta (by have := p.hn; omega) C (holder p M.star) p.H p.β (preparation M p)) := by
  let hd : 0 < n-1 := by have := p.hn; omega
  have hm : 0 ≤ M1 hd C (holder p M.star) := by
    unfold M1
    exact sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hdlen : ∀ ℓ, 0 ≤ dEll p.H p.β ℓ := by
    intro ℓ
    rw [← p.phaseLength_cast]
    positivity
  apply lemma_C_3 M c p.L lam p.T (dEll p.H p.β)
    (fun ℓ => expectedPotential M p C lam (ℓ-1)) (M1 hd C (holder p M.star))
    (concreteKbeta hd C (holder p M.star) p.H p.β (preparation M p)) (goodLoss M p C lam c)
    hc hm (by simp [dEll, tEll]) hdlen
    (fun ℓ => expectedPotential_nonneg M p C lam (ℓ-1))
  · have h0 := goodLoss_le_exploration_phases M p C lam c hc hstar
    have hmax : 0 ≤ M.supOthers c := (hc M.star).trans (cost_le_supOthers M c hc hstar M.star)
    have h1 := mul_le_mul_of_nonneg_left (missing_drift_budget M p C lam p.T) hmax
    have hnorm : ∀ j : ℕ, j+2-1 = j+1 := by intro j; omega
    simp only [Nat.add_sub_cancel, hnorm]
    change goodLoss M p C lam c ≤ M.Flam c p.L lam + M.supOthers c *
      (2 * M1 hd C (holder p M.star) * M.Flam (unitCost M) p.L lam + _)
    nlinarith
  · have h := potential_series_bound M p C lam p.T
    simpa only [Nat.add_sub_cancel] using h

end AnvBandit.Absorbing
