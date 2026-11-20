import AnvBandit.GlobalTheorem
import AnvBandit.ActualNodeExpectation
import AnvBandit.AbsorbingFinal
import AnvBandit.Statements

/-! Original-model three-branch finite-horizon paper endpoints.
Every analysis quantity is instantiated from the same actual execution and contact law. -/
noncomputable section
open scoped BigOperators
namespace AnvBandit.Main
open Execution ExecutionLaw ActualPropagation ActualWaiting GlobalRegret TrajectoryExpectation
variable {n K : ℕ}

/-- These are definitions of the paper's original network/schedule functionals, not assumptions. -/
def actualCaps (M : DecayModel n K) (p : Params n K) (C : ContactMatrix n) : Props where
  Pβ := min (p.T : ℝ) (Pbeta (by have := p.hn; omega) C (holder p M.star)
    p.H (preparation M p) p.β)
  Aβ := Abeta (by have := p.hn; omega) C (holder p M.star)
    p.H (preparation M p) p.β p.T
  M1 := AnvBandit.M1 (by have := p.hn; omega) C (holder p M.star)
  DP := AnvBandit.DP (by have := p.hn; omega) p.hn C (holder p M.star)
  Kβ := concreteKbeta (by have := p.hn; omega) C (holder p M.star)
    p.H p.β (preparation M p)

def actualEcost (M : DecayModel n K) (p : Params n K) (C : ContactMatrix n)
    (lam : Fin 2) (c : Fin K → ℝ) : ℝ :=
  Ecost
    (Eglob n (M.supOthers c) (actualCaps M p C).Pβ (M.Clam c p.L 0 lam))
    (Enode (M.supOthers c) (actualCaps M p C).Aβ
      (M.Clam c p.L (actualCaps M p C).DP lam))
    (Epot (M.Flam c p.L lam) (M.supOthers c) (actualCaps M p C).M1
      (M.Flam (Absorbing.unitCost M) p.L lam) (actualCaps M p C).Kβ)

/-- All three estimates bound precisely the same original-measure good-event loss. -/
theorem goodLoss_three_branches (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (c : Fin K → ℝ)
    (hc : ∀ k, 0 ≤ c k) (hstar : c M.star = 0) :
    goodLoss M p C lam c ≤ actualEcost M p C lam c := by
  have hg := goodLoss_global_paper M p C lam c (M.supOthers c) hc hstar
    (weight_le_sup M c hc hstar)
  have hn := ActualNodeExpectation.goodLoss_node M p C lam c hc hstar
  have hp := Absorbing.weighted_loss_potential_branch M p C lam c hc hstar
  exact le_min hg (le_min hn hp)

/-- C.4: original weighted expected loss, exact three branches and ONE failure budget. -/
theorem theorem_C_4 (M : DecayModel n K) (p : Params n K) (C : ContactMatrix n)
    (lam : Fin 2) (c : Fin K → ℝ) (hc : ∀ k, 0 ≤ c k) (hstar : c M.star = 0) :
    weightedLoss M p C lam c ≤ min ((n : ℝ)*M.supOthers c*p.T)
      (actualEcost M p C lam c + p.δ*((n : ℝ)*M.supOthers c*p.T)) := by
  have hm := weight_le_sup M c hc hstar
  have ht := GlobalTheorem.weightedLoss_trivial M p C lam c (M.supOthers c) hc hm
  have hg := goodLoss_three_branches M p C lam c hc hstar
  have hf := weightedLoss_le_goodLoss_add_failure M p C lam c (M.supOthers c) hc hm
  exact le_min ht (by linarith)

/-- The actual finite-horizon Theorem4.1: no free regret, cost, concentration, recommendation,
stability, propagation or integrability input. Exact paper double truncation is retained. -/
theorem theorem_4_1 (M : DecayModel n K) (p : Params n K) (C : ContactMatrix n) (lam : Fin 2) :
    teamRegret M p C lam ≤
      Uco ((n : ℝ)*p.T) (M.Gamma lam) ((n : ℝ)*M.supOthers (M.rho p.T lam)*p.T)
        (actualEcost M p C lam (M.rho p.T lam))
        (p.δ*((n : ℝ)*M.supOthers (M.rho p.T lam)*p.T)) := by
  have hw := theorem_C_4 M p C lam (M.rho p.T lam) (M.rho_nonneg p.T lam) (M.rho_star p.T lam)
  have hr := teamRegret_conversion M p C lam
  unfold Uco
  apply le_min (teamRegret_trivial M p C lam)
  linarith

/-- Bottom-value loss uses the same actual theorem without a trajectory-conversion constant. -/
theorem bottom_loss (M : DecayModel n K) (p : Params n K) (C : ContactMatrix n) (lam : Fin 2) :
    weightedLoss M p C lam M.gap ≤ min ((n : ℝ)*M.supOthers M.gap*p.T)
      (actualEcost M p C lam M.gap + p.δ*((n : ℝ)*M.supOthers M.gap*p.T)) :=
  theorem_C_4 M p C lam M.gap M.gap_nonneg M.gap_star

/-- The original row-stochastic input determines its attained positive minimum internally. -/
def canonicalContact (p : Params n K) (P : Fin n → Fin n → ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hrow : ∀ i, ∑ j, P i j = 1)
    (hirr : ∀ a b : Fin n, Relation.ReflTransGen (fun x y => 0 < P x y) a b) :
    ContactMatrix n :=
  ContactMatrix.ofStochasticIrreducible (by have := p.hn; omega) P hP hrow
    (fun a b => Relation.ReflTransGen.swap a b (hirr b a))

/-- Primary paper endpoint with only raw original matrix assumptions. The reverse graph
in the constructed contact object is exactly the information-flow orientation. -/
theorem theorem_4_1_canonical (M : DecayModel n K) (p : Params n K)
    (P : Fin n → Fin n → ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (hrow : ∀ i, ∑ j, P i j = 1)
    (hirr : ∀ a b : Fin n, Relation.ReflTransGen (fun x y => 0 < P x y) a b)
    (lam : Fin 2) :
    let C := canonicalContact p P hP hrow hirr
    teamRegret M p C lam ≤
      Uco ((n : ℝ)*p.T) (M.Gamma lam) ((n : ℝ)*M.supOthers (M.rho p.T lam)*p.T)
        (actualEcost M p C lam (M.rho p.T lam))
        (p.δ*((n : ℝ)*M.supOthers (M.rho p.T lam)*p.T)) :=
  theorem_4_1 M p (canonicalContact p P hP hrow hirr) lam

end AnvBandit.Main

