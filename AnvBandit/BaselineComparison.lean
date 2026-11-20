import AnvBandit.MainTheorems
import AnvBandit.BaselineObserved

/-! Paper Corollary 4.2, instantiated to the two genuinely proved algorithm bounds.
A strict comparison of displayed bounds does not assert a strict order of actual regrets. -/
noncomputable section
namespace AnvBandit.BaselineComparison
variable {n K : ℕ}

def cooperativeBound (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) : ℝ :=
  Uco ((n : ℝ)*p.T) (M.Gamma lam) ((n : ℝ)*M.supOthers (M.rho p.T lam)*p.T)
    (Main.actualEcost M p C lam (M.rho p.T lam))
    (p.δ*((n : ℝ)*M.supOthers (M.rho p.T lam)*p.T))

def independentBound (M : DecayModel n K) (p : Execution.Params n K)
    (lam : Fin 2) : ℝ :=
  Uind ((n : ℝ)*p.T) (M.Gamma lam) ((n : ℝ)*M.supOthers (M.rho p.T lam)*p.T)
    (M.Flam (M.rho p.T lam) p.L lam)
    (p.δ*((n : ℝ)*M.supOthers (M.rho p.T lam)*p.T))

/-- Both upper bounds are first proved for actual executions. Only the paper's sufficient
numerical comparison conditions remain as assumptions of their strict comparison. -/
theorem corollary_4_2 (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2)
    (hcost : Main.actualEcost M p C lam (M.rho p.T lam) < M.Flam (M.rho p.T lam) p.L lam)
    (hcut : Main.actualEcost M p C lam (M.rho p.T lam) +
        p.δ*((n : ℝ)*M.supOthers (M.rho p.T lam)*p.T) <
      min ((n : ℝ)*M.supOthers (M.rho p.T lam)*p.T) ((n : ℝ)*p.T - M.Gamma lam)) :
    TrajectoryExpectation.teamRegret M p C lam ≤ cooperativeBound M p C lam ∧
    BaselineTrajectory.teamRegret M p lam ≤ independentBound M p lam ∧
    cooperativeBound M p C lam < independentBound M p lam := by
  refine ⟨Main.theorem_4_1 M p C lam, BaselineTrajectory.teamRegret_bound M p lam, ?_⟩
  exact AnvBandit.corollary_4_2 p.T (M.Gamma lam)
    ((n : ℝ)*M.supOthers (M.rho p.T lam)*p.T)
    (M.Flam (M.rho p.T lam) p.L lam)
    (Main.actualEcost M p C lam (M.rho p.T lam)) p.δ hcost hcut

end AnvBandit.BaselineComparison
