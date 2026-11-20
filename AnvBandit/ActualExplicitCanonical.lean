import AnvBandit.ActualAsymptotics

noncomputable section
open scoped BigOperators
namespace AnvBandit.ActualExplicitRegret
open Execution TrajectoryExpectation
variable {n K : ℕ}

/-- The exact paper constants: `pmin` is the attained minimum of the positive entries
of the supplied stochastic irreducible matrix, rather than an arbitrary lower bound. -/
theorem actual_explicit_canonical (M : DecayModel n K)
    (P : Fin n → Fin n → ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (hrow : ∀ i, ∑ j, P i j = 1)
    (hirr : ∀ a b : Fin n, Relation.ReflTransGen (fun x y => 0 < P y x) a b)
    (lam : Fin 2) (T h : ℕ) (ξ β : ℝ)
    (hT : 1 ≤ T) (hh : 1 ≤ h) (hξ : 0 < ξ) (hβ : 1 < β) :
    let C := ContactMatrix.ofStochasticIrreducible (by have := M.two_le_n; omega) P hP hrow hirr
    teamRegret M (explicitParams M T h ξ β hT hh hξ hβ) C lam ≤
      explicitBound M T h ξ β (epsP C) lam := by
  exact actual_explicit M _ lam T h ξ β hT hh hξ hβ

end AnvBandit.ActualExplicitRegret
