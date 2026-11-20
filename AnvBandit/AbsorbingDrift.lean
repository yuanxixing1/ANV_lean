import AnvBandit.AbsorbingConditional
import AnvBandit.ExecutionContacts

/-! C.8 for the actual execution law, with the original *joint* current contact
law transported through communication-before conditioning. -/
noncomputable section
open scoped BigOperators Classical
open Finset MeasureTheory ProbabilityTheory Preorder
namespace AnvBandit.Absorbing
open Execution ExecutionLaw ExecutionBounds
variable {n K : ℕ}

/-- Exact conditional C.8. The probability space and its joint conditional law
are constructed from original model parameters; no concentration, reliable-cache,
drift or propagation statement is an input hypothesis. -/
theorem conditional_absorbed_drift (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (j : ℕ) :
    let t := p.phaseEnd (j+1)-1
    ∀ᵐ ω ∂executionMeasure M p C lam,
      ((univ \ state M p lam pathRewards (pathContacts p) j ω).card : ℝ) ≤
        Vpot (by have := p.hn; omega) C (holder p M.star)
          (state M p lam pathRewards (pathContacts p) j ω) -
          (executionMeasure M p C lam)[fun ω =>
            Vpot (by have := p.hn; omega) C (holder p M.star)
              (state M p lam pathRewards (pathContacts p) (j+1) ω) |
            (inferInstance : MeasurableSpace (Precontact n t)).comap (beforeContact t)] ω +
          M1 (by have := p.hn; omega) C (holder p M.star) *
            error M p lam pathRewards (pathContacts p) j ω := by
  have hc := conditional_next_potential M p C lam j
  filter_upwards [hc] with ω hω
  rw [hω, contactDistribution_toMeasure]
  exact absorbed_contact_drift M p C lam pathRewards (pathContacts p) j ω

end AnvBandit.Absorbing
