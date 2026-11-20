import AnvBandit.ActualPropagation
import AnvBandit.ActualNodeCost
import AnvBandit.ActualNodeFiniteCost

/-! The actual per-node arrival branch: arrival permanence and elimination budgets are
proved from finite observed-prefix concentration and the executable communication rule.
Ideal hitting certificates here are pathwise intermediates, to be supplied almost surely
by the original contact law. -/
noncomputable section
open scoped BigOperators
open Finset
namespace AnvBandit.ActualPropagation
open Execution ExecutionLaw ExecutionBounds
variable {n K : ℕ} {Ω : Type*}

lemma Inform_time_mono (J : ℕ → Fin n → Fin n) (A : Finset (Fin n)) :
    Monotone (Inform J A) := by
  apply monotone_nat_of_le_succ
  intro t
  exact subset_infStep (J t) _

/-- Once an ideal node arrival has occurred before the horizon, the actual node holds
`star` at every remaining action time. The only probabilistic premise is the finite good event. -/
theorem holds_after_ideal_arrival (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n) (ω : Ω)
    (hg : ω ∈ ObservedPrefix.good (selected p X J) (reward X) (mean M p lam X J) p.T p.L)
    (i : Fin n) (σ t : ℕ)
    (hi : i ∈ Inform (shiftedContacts M p (J ω)) {holder p M.star} σ)
    (ha : p.phaseEnd (preparation M p+σ) ≤ t) (ht : t < p.T) :
    M.star ∈ ((run p (realTape (X ω)) (J ω) t).nodes i).active := by
  let q := (run p (realTape (X ω)) (J ω) t).phase
  have hqpos : 1 ≤ q := (phase_bounds p _ _ t).1
  have hphase := phase_interval p (realTape (X ω)) (J ω) t ht
  have hq : preparation M p + σ < q :=
    p.phaseEnd_strictMono.lt_iff_lt.mp (lt_of_le_of_lt ha hphase.2)
  let j := q-1-preparation M p
  have hj : σ ≤ j := by dsimp [j]; omega
  have he : preparation M p+j = q-1 := by dsimp [j]; omega
  have hin : i ∈ Inform (shiftedContacts M p (J ω)) {holder p M.star} j :=
    Inform_time_mono _ _ hj hi
  have hboundary : p.phaseEnd (preparation M p+j) < p.T := by
    rw [he]
    exact lt_of_le_of_lt hphase.1 ht
  have hhold := informed_subset_actual M p lam X J ω hg j hboundary hin
  rw [mem_holders] at hhold
  rw [active_during_phase p (realTape (X ω)) (J ω) q hqpos t ht hphase.1 hphase.2 i]
  simpa only [he] using hhold

/-- The final state retains every already-arrived optimum, because the terminal round
has no communication. This is not an extra terminal update. -/
theorem holds_at_terminal_of_arrival (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n) (ω : Ω)
    (hg : ω ∈ ObservedPrefix.good (selected p X J) (reward X) (mean M p lam X J) p.T p.L)
    (i : Fin n) (σ : ℕ)
    (hi : i ∈ Inform (shiftedContacts M p (J ω)) {holder p M.star} σ)
    (ha : p.phaseEnd (preparation M p+σ) < p.T) :
    M.star ∈ ((run p (realTape (X ω)) (J ω) p.T).nodes i).active := by
  have hT : 0 < p.T := by have := p.hT; omega
  have he : p.T-1+1 = p.T := by omega
  have hh := holds_after_ideal_arrival M p lam X J ω hg i σ (p.T-1) hi (by omega) (by omega)
  have hc : ¬ communicates p (p.T-1) (run p (realTape (X ω)) (J ω) (p.T-1)) := by
    intro hc
    have := hc.2
    omega
  conv_lhs => rw [← he, run_succ]
  simpa only [step, if_pos (show p.T-1 < p.T by omega), if_neg hc,
    observe, LocalState.observe, LocalState.active] using hh

/-- Exact actual elimination budget for each arrived node. -/
theorem actual_elimination_budget (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n) (ω : Ω)
    (hg : ω ∈ ObservedPrefix.good (selected p X J) (reward X) (mean M p lam X J) p.T p.L)
    (i : Fin n) (σ τ : ℕ) (hστ : σ ≤ τ)
    (hcomplete : Inform (shiftedContacts M p (J ω)) {holder p M.star} τ = univ) :
    ((univ : Finset (Fin K)).filter (fun k =>
      k ∉ ((run p (realTape (X ω)) (J ω) p.T).nodes i).active ∧
      ∃ t ∈ range p.T, p.phaseEnd (preparation M p+σ) ≤ t ∧
        I p (realTape (X ω)) (J ω) t i = k)).card ≤ τ-σ := by
  by_cases ha : p.phaseEnd (preparation M p+σ) < p.T
  · let b := min p.T (p.phaseEnd (preparation M p+τ))
    have hab : p.phaseEnd (preparation M p+σ) ≤ b :=
      le_min ha.le (p.phaseEnd_strictMono.monotone (by omega))
    have hb : b ≤ p.phaseEnd (preparation M p+τ) := min_le_right _ _
    have hbT : b ≤ p.T := min_le_left _ _
    have hstable : ∀ t, b ≤ t → t ≤ p.T →
        ((run p (realTape (X ω)) (J ω) t).nodes i).active =
          ((run p (realTape (X ω)) (J ω) b).nodes i).active := by
      by_cases hcomp : p.phaseEnd (preparation M p+τ) < p.T
      · have he : b = p.phaseEnd (preparation M p+τ) := min_eq_right hcomp.le
        rw [he]
        intro t hbt ht
        exact stable_after_ideal_completion M p lam X J ω hg τ hcomp hcomplete t hbt ht i
      · have he : b = p.T := min_eq_left (by omega)
        intro t hbt ht
        have : t = b := by omega
        subst t
        rfl
    have hbnd := lost_selected_card_of_stable p (realTape (X ω)) (J ω) i
      (preparation M p+σ) (preparation M p+τ) b ha hab hb hbT hstable
    simpa only [Nat.add_sub_add_left] using hbnd
  · have hempty : ((univ : Finset (Fin K)).filter (fun k =>
      k ∉ ((run p (realTape (X ω)) (J ω) p.T).nodes i).active ∧
      ∃ t ∈ range p.T, p.phaseEnd (preparation M p+σ) ≤ t ∧
        I p (realTape (X ω)) (J ω) t i = k)) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro k hk
      obtain ⟨_, _, t, ht, hat, _⟩ := mem_filter.mp hk
      have := mem_range.mp ht
      omega
    rw [hempty, card_empty]
    exact Nat.zero_le _

/-- Actual per-node personal-threshold candidate, valid for either fatigue mechanism.
No arrival, elimination, reliability, or exploration bound is an input premise. The ideal
finite hitting certificates will be supplied almost surely by the contact-law bridge. -/
theorem path_node_personal_candidate (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n) (ω : Ω)
    (hg : ω ∈ ObservedPrefix.good (selected p X J) (reward X) (mean M p lam X J) p.T p.L)
    (σ : Fin n → ℕ) (τ : ℕ) (hστ : ∀ i, σ i ≤ τ)
    (harrived : ∀ i, i ∈ Inform (shiftedContacts M p (J ω)) {holder p M.star} (σ i))
    (hcomplete : Inform (shiftedContacts M p (J ω)) {holder p M.star} τ = univ)
    (c : Fin K → ℝ) (hc : ∀ k, 0 ≤ c k) (hstar : c M.star = 0) :
    (∑ t ∈ range p.T, ∑ i, c (I p (realTape (X ω)) (J ω) t i)) ≤
      M.supOthers c * ((∑ i, min p.T (p.phaseEnd (preparation M p+σ i)) : ℕ) : ℝ)
        + M.Ccap c p.L + M.wmax c p.L * ((∑ i : Fin n, (τ - σ i) : ℕ) : ℝ) := by
  let R := goodRunOn M p lam X J ω hg
  let D : Fin n → Finset (Fin K) := fun i => ((run p (realTape (X ω)) (J ω) p.T).nodes i).D
  apply R.node_cost_traj c (fun i => p.phaseEnd (preparation M p+σ i)) D
    (fun i => τ-σ i) (holder p M.star) hc hstar
  · exact mem_sticky_holder p M.star
  · intro i
    exact ((run p (realTape (X ω)) (J ω) p.T).nodes i).disjoint
  · intro i
    exact ((run p (realTape (X ω)) (J ω) p.T).nodes i).card_le
  · intro i hi
    exact holds_at_terminal_of_arrival M p lam X J ω hg i (σ i) (harrived i) hi
  · intro i
    exact ((run p (realTape (X ω)) (J ω) p.T).nodes i).active_card_le p
  · intro t i hat ht
    exact holds_after_ideal_arrival M p lam X J ω hg i (σ i) t (harrived i) hat ht
  · intro i
    exact actual_elimination_budget M p lam X J ω hg i (σ i) τ (hστ i) hcomplete

end AnvBandit.ActualPropagation
