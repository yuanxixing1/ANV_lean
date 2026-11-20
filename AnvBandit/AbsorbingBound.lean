import AnvBandit.AbsorbingSeries
import AnvBandit.AbsorbingError
import AnvBandit.ConcreteKbeta

/-! Concrete C.13: original actual process, exact schedule positive increments,
true remaining-arrival series, exact exploration budget. -/
noncomputable section
open scoped BigOperators Classical
open Finset MeasureTheory
namespace AnvBandit.Absorbing
open Execution ExecutionLaw ActualPropagation
variable {n K : ℕ}

theorem potential_series_bound (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (Ph : ℕ) :
    (∑ j ∈ range Ph, posPart (dEll p.H p.β (j+1)-dEll p.H p.β j) *
      expectedPotential M p C lam j) ≤
      concreteKbeta (by have := p.hn; omega) C (holder p M.star) p.H p.β (preparation M p) := by
  have hs := concreteKbeta_summable p.hn C (holder p M.star)
    (H := (p.H : ℝ)) (β := p.β) (Nat.cast_nonneg _) p.hβ (preparation M p)
  calc
    _ ≤ ∑ j ∈ range Ph, scheduleOmega p.H p.β (j+1) *
        remainingV (by have := p.hn; omega) C (holder p M.star) (j-preparation M p) := by
      apply sum_le_sum
      intro j _
      have h := mul_le_mul_of_nonneg_left (expectedPotential_le_remaining M p C lam j)
        (scheduleOmega_nonneg p.H p.β (j+1))
      simpa only [scheduleOmega, Nat.add_sub_cancel] using h
    _ ≤ _ := hs.sum_le_tsum _ (fun j _ => mul_nonneg (scheduleOmega_nonneg p.H p.β (j+1))
      (remainingV_nonneg _ C (holder p M.star) (j-preparation M p)))

/-- Actual expected missing-holder phase budget, C.13. No drift, charging,
concentration, potential dominance or series finiteness premise remains. -/
theorem expected_missing_budget (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (Ph : ℕ) :
    (∑ j ∈ range Ph, dEll p.H p.β (j+1) * expectedMissing M p C lam j) ≤
      2 * M1 (by have := p.hn; omega) C (holder p M.star) * M.Flam (unitCost M) p.L lam +
      concreteKbeta (by have := p.hn; omega) C (holder p M.star) p.H p.β (preparation M p) := by
  have ht := finite_telescope_with_budget M p C lam Ph
  have hs := potential_series_bound M p C lam Ph
  linarith

end AnvBandit.Absorbing
