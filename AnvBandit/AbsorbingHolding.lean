import AnvBandit.ActualPublicBudget
import AnvBandit.ActualNodeFiniteCost

/-! Exact cost of actual pulls made while the optimum belongs to the active set. -/
noncomputable section
open scoped BigOperators Classical
open Finset
namespace AnvBandit.Absorbing
open Execution ExecutionLaw ExecutionBounds ActualPublicBudget
variable {n K : ℕ} {Ω : Type*}

def holdingCost (M : DecayModel n K) (p : Params n K) (X : ℕ → Fin n → Bool)
    (J : ℕ → Fin n → Fin n) (c : Fin K → ℝ) : ℝ :=
  ∑ t ∈ range p.T, ∑ i : Fin n,
    if M.star ∈ ((run p (realTape X) J t).nodes i).active then c (I p (realTape X) J t i) else 0

lemma holdingCost_eq (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n) (ω : Ω)
    (c : Fin K → ℝ) (hstar : c M.star = 0)
    (hg : ω ∈ ObservedPrefix.good (selected p X J) (reward X) (mean M p lam X J) p.T p.L) :
    holdingCost M p (X ω) (J ω) c =
      ∑ i : Fin n, ∑ k ∈ M.others, c k * (holdingTimes M p (X ω) (J ω) i k).card := by
  let R := goodRunOn M p lam X J ω hg
  unfold holdingCost
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  let S := (range p.T).filter (fun t => M.star ∈ ((run p (realTape (X ω)) (J ω) t).nodes i).active)
  change (∑ t ∈ range p.T, if M.star ∈ ((run p (realTape (X ω)) (J ω) t).nodes i).active
    then c (R.I t i) else 0) = _
  rw [← sum_filter]
  change (∑ t ∈ S, c (R.I t i)) = _
  rw [R.sum_by_arm]
  have he : (∑ k ∈ M.others, (S.filter (fun t => R.I t i = k)).card * c k) =
      ∑ k : Fin K, (S.filter (fun t => R.I t i = k)).card * c k := by
    apply sum_subset (subset_univ _)
    intro k _ hk
    have heq : k = M.star := by simpa [DecayModel.others] using hk
    rw [heq, hstar, mul_zero]
  rw [← he]
  apply sum_congr rfl
  intro k hk
  have hf : S.filter (fun t => R.I t i = k) = holdingTimes M p (X ω) (J ω) i k := by
    ext t
    simp only [S, holdingTimes, mem_filter]
    change ((_ ∧ _) ∧ _) ↔ (_ ∧ (_ ∧ _))
    tauto
  rw [hf, mul_comm]

theorem holdingCost_le_Flam (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n) (ω : Ω)
    (c : Fin K → ℝ) (hc : ∀ k, 0 ≤ c k) (hstar : c M.star = 0)
    (hg : ω ∈ ObservedPrefix.good (selected p X J) (reward X) (mean M p lam X J) p.T p.L) :
    holdingCost M p (X ω) (J ω) c ≤ M.Flam c p.L lam := by
  rw [holdingCost_eq M p lam X J ω c hstar hg]
  fin_cases lam
  · let R := goodRunOn M p 0 X J ω hg
    calc
      _ ≤ ∑ _i : Fin n, M.Wsum c p.L := by
        apply sum_le_sum
        intro i _
        apply sum_le_sum
        intro k hk
        have hne : k ≠ M.star := by simpa [DecayModel.others] using hk
        have hcount : (holdingTimes M p (X ω) (J ω) i k).card ≤ M.mkAll p.L k := R.pair_budget i hne
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcount) (hc k)
      _ = _ := by simp [DecayModel.Flam]
  · exact holding_cost_le_F1 M p X J ω c hc hg

end AnvBandit.Absorbing
