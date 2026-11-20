import AnvBandit.ObservedTrajectory
import AnvBandit.GlobalTheorem
noncomputable section
open scoped BigOperators ENNReal
open Finset MeasureTheory ProbabilityTheory Preorder
namespace AnvBandit.ObservedRegret
open Execution ExecutionLaw ActualPropagation TrajectoryExpectation GlobalTheorem
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

/-- Exact global branch under any original finite observed execution law. All premises
are original sequential probability laws or deterministic absence/dummy encodings. -/
theorem original_team_regret_global_bound :
    let c := M.rho p.T lam
    let cmax := M.supOthers c
    let Pbar := min (p.T : ℝ)
      (Pbeta (by have := p.hn; omega) C (holder p M.star) p.H (preparation M p) p.β)
    originalTeamRegret M p lam ν ≤ min ((n : ℝ)*p.T)
      (M.Gamma lam + min ((n : ℝ)*cmax*p.T)
        ((n : ℝ)*cmax*Pbar + M.Clam c p.L 0 lam + p.δ*((n : ℝ)*cmax*p.T))) := by
  rw [original_teamRegret_eq M p C lam ν hzero hx hj habsent]
  exact team_regret_global_bound M p C lam
end OriginalLaw
end AnvBandit.ObservedRegret
