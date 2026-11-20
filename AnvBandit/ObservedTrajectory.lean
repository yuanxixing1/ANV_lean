import AnvBandit.ObservedRegret
import AnvBandit.TrajectoryExpectation

/-! True omniscient trajectory regret under arbitrary original observed laws. -/
noncomputable section
open scoped BigOperators ENNReal
open Finset MeasureTheory ProbabilityTheory Preorder
namespace AnvBandit.ObservedRegret
open Execution ExecutionLaw GlobalRegret TrajectoryExpectation
variable {n K : ℕ}

theorem pathActions_prefix_congr (p : Params n K) (ω ω' : Path n)
    (h : frestrictLe p.T ω = frestrictLe p.T ω') : pathActions p ω = pathActions p ω' := by
  funext i t
  unfold pathActions I
  rw [run_prefix_congr p ω ω' p.T t.val t.isLt.le h]

theorem pathActions_observed (p : Params n K) (ω : Path n) :
    pathActions p (observedPath p ω) = pathActions p ω := by
  funext i t
  unfold pathActions I
  rw [observedPath_run]

theorem pathReward_prefix_congr (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (ω ω' : Path n) (h : frestrictLe p.T ω = frestrictLe p.T ω') :
    pathReward M p lam ω = pathReward M p lam ω' := by
  unfold pathReward
  rw [pathActions_prefix_congr p ω ω' h]

theorem pathReward_observed (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (ω : Path n) : pathReward M p lam (observedPath p ω) = pathReward M p lam ω := by
  unfold pathReward
  rw [pathActions_observed]

/-- Same true Vstar oracle, with the actual trajectory expectation taken under ν. -/
def originalTeamRegret (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (ν : Measure (Path n)) : ℝ := oracle M p.T lam - ∫ ω, pathReward M p lam ω ∂ν

section OriginalLaw
variable (M : DecayModel n K) (p : Params n K) (C : ContactMatrix n) (lam : Fin 2)
    (ν : Measure (Path n)) [IsProbabilityMeasure ν]
    (hzero : ν.map (frestrictLe 0) = (observedMeasure M p C lam).map (frestrictLe 0))
    (hx : ∀ t < p.T, condDistrib (fun ω : Path n => (ω (t+1)).1) (frestrictLe t) ν
      =ᵐ[ν.map (frestrictLe t)] rewardKernel M p lam t)
    (hj : ∀ t < p.T, retainedContact p (t+1) →
      condDistrib (fun ω : Path n => (ω (t+1)).2)
        (fun ω : Path n => (frestrictLe t ω, (ω (t+1)).1)) ν
        =ᵐ[ν.map (fun ω => (frestrictLe t ω, (ω (t+1)).1))]
        Kernel.const (Prefix n t × (Fin n → Bool)) (contactDistribution C).toMeasure)
    (habsent : ∀ t < p.T, ¬retainedContact p (t+1) → ∀ᵐ ω ∂ν, (ω (t+1)).2 = id)

include hzero hx hj habsent

/-- Full joint trajectory value, including synchronous public-fatigue evaluation,
transfers exactly. This is not a reduction to marginal arm counts. -/
theorem original_pathReward_integral :
    (∫ ω, pathReward M p lam ω ∂ν) =
      ∫ ω, pathReward M p lam ω ∂executionMeasure M p C lam := by
  exact original_integral_eq M p C lam ν hzero hx hj habsent (pathReward M p lam)
    (pathReward_prefix_congr M p lam) (pathReward_observed M p lam)

theorem original_teamRegret_eq : originalTeamRegret M p lam ν = teamRegret M p C lam := by
  unfold originalTeamRegret teamRegret
  rw [original_pathReward_integral M p C lam ν hzero hx hj habsent]

end OriginalLaw
end AnvBandit.ObservedRegret
