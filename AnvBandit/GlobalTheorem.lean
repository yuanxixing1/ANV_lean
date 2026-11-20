import AnvBandit.TrajectoryExpectation

/-! The first complete actual global-waiting regret branch, not the full three-branch result. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace AnvBandit.GlobalTheorem
open Execution ExecutionLaw ActualPropagation ActualWaiting GlobalRegret TrajectoryExpectation
variable {n K : ℕ}

theorem weightedLoss_trivial (M : DecayModel n K) (p : Params n K) (C : ContactMatrix n)
    (lam : Fin 2) (c : Fin K → ℝ) (cmax : ℝ)
    (hc : ∀ k, 0 ≤ c k) (hcmax : ∀ k, c k ≤ cmax) :
    weightedLoss M p C lam c ≤ (n : ℝ)*cmax*p.T := by
  have h := integral_mono_ae (pathCost_integrable M p C lam c cmax hc hcmax)
    (integrable_const ((n : ℝ)*cmax*p.T))
    (Filter.Eventually.of_forall (pathCost_le p c cmax hcmax))
  simpa [weightedLoss] using h

/-- P6 endpoint: actual trajectory pseudo-regret under the full original standard law,
for either fatigue mode, with exact terminal Cλ and one failure budget. No derived
concentration, reliability, stability, weighted-cost or regret inequality is a premise. -/
theorem team_regret_global_bound (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) :
    let c := M.rho p.T lam
    let cmax := M.supOthers c
    let Pbar := min (p.T : ℝ)
      (Pbeta (by have := p.hn; omega) C (holder p M.star) p.H (preparation M p) p.β)
    teamRegret M p C lam ≤ min ((n : ℝ)*p.T)
      (M.Gamma lam + min ((n : ℝ)*cmax*p.T)
        ((n : ℝ)*cmax*Pbar + M.Clam c p.L 0 lam + p.δ*((n : ℝ)*cmax*p.T))) := by
  dsimp
  let c := M.rho p.T lam
  let cmax := M.supOthers c
  have hc : ∀ k, 0 ≤ c k := M.rho_nonneg p.T lam
  have hs : c M.star = 0 := M.rho_star p.T lam
  have hm : ∀ k, c k ≤ cmax := weight_le_sup M c hc hs
  have hgood := goodLoss_global_paper M p C lam c cmax hc hs hm
  have hfail := weightedLoss_le_goodLoss_add_failure M p C lam c cmax hc hm
  have hwait : weightedLoss M p C lam c ≤
      (n : ℝ)*cmax*min (p.T : ℝ)
        (Pbeta (by have := p.hn; omega) C (holder p M.star) p.H (preparation M p) p.β) +
      M.Clam c p.L 0 lam + p.δ*((n : ℝ)*cmax*p.T) := by linarith
  have htriv := weightedLoss_trivial M p C lam c cmax hc hm
  have hmin := le_min htriv hwait
  have hconv := teamRegret_conversion M p C lam
  apply le_min (teamRegret_trivial M p C lam)
  change teamRegret M p C lam ≤ M.Gamma lam +
    min ((n : ℝ)*cmax*p.T)
      ((n : ℝ)*cmax*min (p.T : ℝ)
        (Pbeta (by have := p.hn; omega) C (holder p M.star) p.H (preparation M p) p.β) +
        M.Clam c p.L 0 lam + p.δ*((n : ℝ)*cmax*p.T))
  change teamRegret M p C lam ≤ M.Gamma lam + weightedLoss M p C lam c at hconv
  linarith

end AnvBandit.GlobalTheorem

