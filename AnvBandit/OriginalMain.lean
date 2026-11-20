import AnvBandit.ObservedTrajectory
import AnvBandit.MainTheorems
noncomputable section
open scoped BigOperators ENNReal
open Finset MeasureTheory ProbabilityTheory Preorder
namespace AnvBandit.ObservedRegret
open Execution ExecutionLaw ActualPropagation TrajectoryExpectation GlobalRegret
variable {n K : ℕ}
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

/-- Full finite-horizon Theorem 4.1 under any original finite observed execution law.
The probability premises are only the original conditional joint laws and the deterministic
encoding of absent requests / initial dummy, not derived concentration or cost conditions. -/
theorem original_theorem_4_1 :
    originalTeamRegret M p lam ν ≤
      Uco ((n : ℝ)*p.T) (M.Gamma lam) ((n : ℝ)*M.supOthers (M.rho p.T lam)*p.T)
        (Main.actualEcost M p C lam (M.rho p.T lam))
        (p.δ*((n : ℝ)*M.supOthers (M.rho p.T lam)*p.T)) := by
  rw [original_teamRegret_eq M p C lam ν hzero hx hj habsent]
  exact Main.theorem_4_1 M p C lam

/-- C.4 under the same arbitrary original observed law. -/
theorem original_theorem_C_4 (c : Fin K → ℝ) (hc : ∀ k, 0 ≤ c k) (hstar : c M.star = 0) :
    (∫ ω, pathCost p c ω ∂ν) ≤ min ((n : ℝ)*M.supOthers c*p.T)
      (Main.actualEcost M p C lam c + p.δ*((n : ℝ)*M.supOthers c*p.T)) := by
  rw [original_weightedLoss_eq M p C lam ν hzero hx hj habsent c]
  exact Main.theorem_C_4 M p C lam c hc hstar

end OriginalLaw
end AnvBandit.ObservedRegret
