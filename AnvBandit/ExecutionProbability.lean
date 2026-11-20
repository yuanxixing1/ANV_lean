import AnvBandit.ExecutionKernel
import AnvBandit.ExecutionBounds

/-!
# Actual finite-horizon concentration from the original stochastic construction

The final probability estimate below has only the environment, public configuration and
contact matrix as inputs. Conditional means, predictability and the concentration event are
proved from the execution kernel; none is an input assumption.
-/
noncomputable section
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory
namespace AnvBandit.ExecutionLaw
variable {n K : ℕ}

/-- Only already observed personal prefixes are tested. -/
def actualGoodEvent (M : DecayModel n K) (p : Execution.Params n K) (lam : Fin 2) : Set (Path n) :=
  ObservedPrefix.good (ExecutionBounds.selected p pathRewards (pathContacts p))
    (ExecutionBounds.reward pathRewards)
    (ExecutionBounds.mean M p lam pathRewards (pathContacts p)) p.T p.L

theorem selected_predictable (p : Execution.Params n K) (i : Fin n) (k : Fin K) (t : ℕ) :
    MeasurableSet[executionFiltration n t]
      {ω | ExecutionBounds.selected p pathRewards (pathContacts p) i k t ω = true} := by
  have h := (action_predictable p t i) (measurableSet_singleton k)
  convert h using 1
  ext ω
  simp [ExecutionBounds.selected]


/-- The event is measurable using only the completed horizon. -/
theorem actualGoodEvent_measurable (M : DecayModel n K) (p : Execution.Params n K)
    (lam : Fin 2) : MeasurableSet[executionFiltration n p.T] (actualGoodEvent M p lam) := by
  exact ObservedPrefix.good_measurable (executionFiltration n)
    (ExecutionBounds.selected p pathRewards (pathContacts p))
    (ExecutionBounds.reward pathRewards)
    (ExecutionBounds.mean M p lam pathRewards (pathContacts p))
    (selected_predictable p)
    (fun i k t => reward_adapted t i)
    (fun i k t => actualMean_predictable M p lam t i) p.L

/-- A.1 for the actual algorithm, both fatigue mechanisms and every legal finite horizon.
All raw probability hypotheses of the generic theorem are discharged by construction. -/
theorem actual_good_compl_le (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) :
    (executionMeasure M p C lam).real (actualGoodEvent M p lam)ᶜ ≤ p.δ := by
  have h := ObservedPrefix.measure_good_compl_le_finite
    (executionMeasure M p C lam) (executionFiltration n)
    (ExecutionBounds.selected p pathRewards (pathContacts p))
    (ExecutionBounds.reward pathRewards)
    (ExecutionBounds.mean M p lam pathRewards (pathContacts p))
    p.hn p.hK p.hT
    (fun i k t _ => selected_predictable p i k t)
    (fun i k t _ => reward_adapted t i)
    (fun i k t _ => actualMean_predictable M p lam t i)
    (fun i k t _ ω => by
      change rewardReal (pathRewards ω t i) = 0 ∨ rewardReal (pathRewards ω t i) = 1
      cases pathRewards ω t i <;> simp [rewardReal])
    (fun i k t _ ω => actualMean_mem M p lam (pathRewards ω) (pathContacts p ω) t i)
    (fun i k t _ => conditional_reward_mean M p C lam t i)
    p.δ p.hδ.1 p.hδ.2.le
  simpa [actualGoodEvent, Execution.Params.L, Ldelta, Nat.cast_mul, Nat.cast_ofNat] using h

/-- The proven finite event supplies all deterministic UCB/selection prerequisites. -/
def actualGoodRun (M : DecayModel n K) (p : Execution.Params n K) (lam : Fin 2)
    (ω : Path n) (hω : ω ∈ actualGoodEvent M p lam) : GoodRunOn M p.T :=
  ExecutionBounds.goodRunOn M p lam pathRewards (pathContacts p) ω hω

end AnvBandit.ExecutionLaw
