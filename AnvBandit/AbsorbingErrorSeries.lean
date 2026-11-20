import AnvBandit.AbsorbingError
import AnvBandit.AbsorbingTerminal

noncomputable section
open scoped BigOperators Classical
open Finset
namespace AnvBandit.Absorbing
open Execution
variable {n K : ℕ} {Ω : Type*}

lemma tsum_weighted_error_eq (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n) (ω : Ω) :
    (∑' j, dEll p.H p.β (j+1) * error M p lam X J j ω) =
      ∑ j ∈ range p.T, dEll p.H p.β (j+1) * error M p lam X J j ω := by
  apply tsum_eq_sum
  intro j hj
  have hT : p.T ≤ j := by simpa using hj
  rw [error_terminal_support M p lam X J j ((lastPhase_le_T p).trans (by omega)) ω, mul_zero]

/-- Exact infinite-series notation of C.9; its support is actually finite by
terminal absorption, so this step uses no unjustified limit exchange. -/
theorem actual_error_budget_series (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n) (ω : Ω) :
    (∑' j, dEll p.H p.β (j+1) * error M p lam X J j ω) ≤
      2 * M.Flam (unitCost M) p.L lam := by
  rw [tsum_weighted_error_eq]
  exact actual_error_budget M p lam X J ω p.T

end AnvBandit.Absorbing
