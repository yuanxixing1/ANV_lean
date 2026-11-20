import AnvBandit.ActualPropagation
import AnvBandit.ActualPublicBudget

/-! Exact two-mechanism global waiting path bound, including one shared public excess. -/
noncomputable section
open scoped BigOperators
open Finset
namespace AnvBandit.ActualPropagation
open Execution ExecutionLaw ExecutionBounds ActualPublicBudget
variable {n K : ℕ} {Ω : Type*}

theorem cap_nonneg (M : DecayModel n K) (c : Fin K → ℝ) (L : ℝ)
    (hc : ∀ k, 0 ≤ c k) : 0 ≤ M.Ccap c L := by
  unfold DecayModel.Ccap
  exact le_min (mul_nonneg (Nat.cast_nonneg _) (M.Wkappa_nonneg hc L))
    (add_nonneg (M.Wsum_nonneg hc L) (mul_nonneg (by positivity) (M.wmax_nonneg hc L)))

theorem publicCap_nonneg (M : DecayModel n K) (c : Fin K → ℝ) (L : ℝ)
    (hc : ∀ k, 0 ≤ c k) : 0 ≤ M.CNcap c L + M.Bpub c := by
  have hN : 0 ≤ M.CNcap c L := by
    rw [← Ccap_statisticalWeights M c L]
    exact cap_nonneg M _ L (statisticalWeights_nonneg M c hc L)
  have hpub : 0 ≤ M.Bpub c := by
    unfold DecayModel.Bpub
    apply mul_nonneg (by norm_num)
    apply sum_nonneg
    intro k hk
    apply mul_nonneg (div_nonneg (hc k) (M.gap_nonneg k))
    unfold DecayModel.Xi DecayModel.Dhalf DecayModel.Ahalf
    exact add_nonneg (tsum_nonneg (fun s => posPart_nonneg _))
      (mul_nonneg (Nat.cast_nonneg _) (posPart_nonneg _))
  exact add_nonneg hN hpub

theorem path_global_public_candidate (M : DecayModel n K) (p : Params n K)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n) (ω : Ω)
    (hg : ω ∈ ObservedPrefix.good (selected p X J) (reward X) (mean M p 1 X J) p.T p.L)
    (j : ℕ) (hcomplete : Inform (shiftedContacts M p (J ω)) {holder p M.star} j = univ)
    (c : Fin K → ℝ) (cmax : ℝ) (hc : ∀ k, 0 ≤ c k)
    (hstar : c M.star = 0) (hcmax : ∀ k, c k ≤ cmax) :
    (∑ t ∈ range p.T, ∑ i, c (I p (realTape (X ω)) (J ω) t i)) ≤
      (n : ℝ)*cmax*(min p.T (p.phaseEnd (preparation M p+j)) : ℕ) +
        (M.CNcap c p.L + M.Bpub c) := by
  let S := p.phaseEnd (preparation M p+j)
  by_cases hS : S < p.T
  · let D : Fin n → Finset (Fin K) := fun i => (run p (realTape (X ω)) (J ω) S).nodes i |>.D
    have hstable := stable_after_ideal_completion M p 1 X J ω hg j hS hcomplete
    have hall : ∀ i, M.star ∈ ((run p (realTape (X ω)) (J ω) S).nodes i).active := by
      intro i
      have h := informed_subset_actual M p 1 X J ω hg j hS
      exact (mem_holders _ _ _).mp (h (by rw [hcomplete]; exact mem_univ i))
    have htail := stable_tail_public_cost M p X J ω c S (holder p M.star) D hc hstar hg
      (by
        intro t i hSt ht
        rw [hstable t hSt ht.le i]
        rfl)
      (mem_sticky_holder p M.star)
      (fun i => (run p (realTape (X ω)) (J ω) S).nodes i |>.disjoint)
      (fun i => (run p (realTape (X ω)) (J ω) S).nodes i |>.card_le)
      hall (fun i => ((run p (realTape (X ω)) (J ω) S).nodes i).active_card_le p)
    rw [loss_split_at (I p (realTape (X ω)) (J ω)) c p.T S]
    exact add_le_add (waiting_cost_le _ c cmax hcmax p.T S) htail
  · have hcut : (range p.T).filter (fun t => t < S) = range p.T := by
      apply filter_eq_self.mpr
      intro t ht
      exact lt_of_lt_of_le (mem_range.mp ht) (Nat.le_of_not_gt hS)
    have hwait := waiting_cost_le (I p (realTape (X ω)) (J ω)) c cmax hcmax p.T S
    rw [hcut] at hwait
    exact hwait.trans (le_add_of_nonneg_right (publicCap_nonneg M c p.L hc))

theorem clam_zero_nonneg (M : DecayModel n K) (c : Fin K → ℝ) (L : ℝ)
    (hc : ∀ k, 0 ≤ c k) (lam : Fin 2) : 0 ≤ M.Clam c L 0 lam := by
  fin_cases lam
  · simpa [DecayModel.Clam] using cap_nonneg M c L hc
  · simpa [DecayModel.Clam] using le_min (cap_nonneg M c L hc) (publicCap_nonneg M c L hc)

/-- Exact Cλ(c;0) path bound for either mechanism. Reliability, actual stability and the
shared public budget are all derived, leaving only the finite good path/completion conditions. -/
theorem path_global_exact (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n) (ω : Ω)
    (hg : ω ∈ ObservedPrefix.good (selected p X J) (reward X) (mean M p lam X J) p.T p.L)
    (j : ℕ) (hcomplete : Inform (shiftedContacts M p (J ω)) {holder p M.star} j = univ)
    (c : Fin K → ℝ) (cmax : ℝ) (hc : ∀ k, 0 ≤ c k)
    (hstar : c M.star = 0) (hcmax : ∀ k, c k ≤ cmax) :
    (∑ t ∈ range p.T, ∑ i, c (I p (realTape (X ω)) (J ω) t i)) ≤
      (n : ℝ)*cmax*(min p.T (p.phaseEnd (preparation M p+j)) : ℕ) + M.Clam c p.L 0 lam := by
  have hp := path_global_personal_candidate M p lam X J ω hg j hcomplete c cmax hc hstar hcmax
  fin_cases lam
  · simpa [DecayModel.Clam] using hp
  · have hpub := path_global_public_candidate M p X J ω hg j hcomplete c cmax hc hstar hcmax
    simpa only [DecayModel.Clam, zero_mul, add_zero, min_add_add_left] using le_min hp hpub

end AnvBandit.ActualPropagation
