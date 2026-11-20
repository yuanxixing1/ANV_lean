import AnvBandit.ExecutionBounds
import AnvBandit.ExecutionPropagation
import AnvBandit.FiniteCosts

/-!
# Finite-horizon actual/ideal propagation coupling

The local recommendation premise is discharged from the actual algorithm and the finite
observed-prefix good event. Statements are restricted to actual completed communication
stages; independent extension of contacts beyond the horizon is analysis-only.
-/
noncomputable section
open scoped BigOperators
open Finset

namespace AnvBandit.ActualPropagation
open Execution ExecutionLaw ExecutionBounds
variable {n K : ℕ} {Ω : Type*}

def preparation (M : DecayModel n K) (p : Params n K) : ℕ :=
  lastShortPhase (p.H : ℝ) p.β (M.Bschedule p.L : ℝ)

theorem phaseLength_cast (p : Params n K) (ℓ : ℕ) :
    ((p.phaseEnd ℓ - p.phaseEnd (ℓ - 1) : ℕ) : ℝ) = dEll p.H p.β ℓ := by
  rw [Nat.cast_sub (p.phaseEnd_strictMono.monotone (Nat.sub_le _ _))]
  simp [Params.phaseEnd, dEll, tEll]

theorem length_after_preparation (M : DecayModel n K) (p : Params n K)
    (ℓ : ℕ) (hℓ : preparation M p < ℓ) :
    M.Bschedule p.L < p.phaseEnd ℓ - p.phaseEnd (ℓ - 1) := by
  have hH : (0 : ℝ) < p.H := by
    exact_mod_cast (show 0 < p.H by have := p.hH; omega)
  obtain ⟨heq, hbound, hrel⟩ := reliable_phase_exact_budget M p.L hH p.hβ
  have hlen : (M.Bschedule p.L : ℝ) < dEll p.H p.β ℓ := by
    apply hrel ℓ
    rw [heq]
    exact hℓ
  rw [← phaseLength_cast p ℓ] at hlen
  exact_mod_cast hlen

/-- One actual completed reliable communication stage dominates one ideal step.
There is no externally supplied reliable-recommendation hypothesis. -/
theorem actual_phase_step (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n) (ω : Ω)
    (hg : ω ∈ ObservedPrefix.good (selected p X J) (reward X) (mean M p lam X J) p.T p.L)
    (ℓ : ℕ) (hℓ : preparation M p < ℓ) (ht : p.phaseEnd ℓ < p.T) :
    infStep (J ω ℓ) (holders M.star (run p (realTape (X ω)) (J ω) (p.phaseEnd (ℓ-1)))) ⊆
      holders M.star (run p (realTape (X ω)) (J ω) (p.phaseEnd ℓ)) := by
  have hpos : 1 ≤ ℓ := by omega
  have hpre : holders M.star (preBoundary p (realTape (X ω)) (J ω) ℓ) =
      holders M.star (run p (realTape (X ω)) (J ω) (p.phaseEnd (ℓ-1))) := by
    ext i
    simp only [mem_holders, preBoundary_active p _ _ ℓ hpos ht.le i]
  rw [run_boundary p _ _ ℓ hpos ht, ← hpre]
  apply infStep_subset_communicate_holders
  intro i hi
  apply reliable_cache M p lam X J ω hg ℓ hpos ht.le i
  · rw [hpre] at hi
    exact (mem_holders _ _ _).mp hi
  · exact length_after_preparation M p ℓ hℓ

def shiftedContacts (M : DecayModel n K) (p : Params n K)
    (J : ℕ → Fin n → Fin n) (j : ℕ) : Fin n → Fin n :=
  J (preparation M p + 1 + j)

theorem infStep_mono {A B : Finset (Fin n)} (j : Fin n → Fin n) (h : A ⊆ B) :
    infStep j A ⊆ infStep j B := by
  apply Finset.union_subset_union h
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h (Finset.mem_filter.mp hi).2⟩

/-- Every ideal informed node is an actual holder at the corresponding executed boundary.
When the boundary is outside the horizon, no claim of actual communication is made. -/
theorem informed_subset_actual (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n) (ω : Ω)
    (hg : ω ∈ ObservedPrefix.good (selected p X J) (reward X) (mean M p lam X J) p.T p.L)
    (j : ℕ) (ht : p.phaseEnd (preparation M p + j) < p.T) :
    Inform (shiftedContacts M p (J ω)) {holder p M.star} j ⊆
      holders M.star (run p (realTape (X ω)) (J ω) (p.phaseEnd (preparation M p + j))) := by
  induction j with
  | zero =>
    simp only [Inform_zero, Nat.add_zero, Finset.singleton_subset_iff]
    exact permanent_holder_mem p M.star _ _ _
  | succ j ih =>
    have hprev : p.phaseEnd (preparation M p + j) < p.T :=
      lt_trans (p.phaseEnd_strictMono (by omega)) ht
    have hlocal := actual_phase_step M p lam X J ω hg
      (preparation M p + j + 1) (by omega) (by simpa [Nat.add_assoc] using ht)
    rw [show preparation M p + j + 1 - 1 = preparation M p + j by omega] at hlocal
    have hmono := infStep_mono (shiftedContacts M p (J ω) j) (ih hprev)
    rw [Inform_succ]
    exact hmono.trans (by simpa [shiftedContacts, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hlocal)

/-- Once every node holds the optimum at a reliable boundary, the entire active sets
remain fixed, not merely their membership of the optimum. The terminal update guard
is used as defined by the real executor. -/
theorem stable_after_all_holders (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n) (ω : Ω)
    (hg : ω ∈ ObservedPrefix.good (selected p X J) (reward X) (mean M p lam X J) p.T p.L)
    (r : ℕ) (hr : preparation M p ≤ r) (hS : p.phaseEnd r < p.T)
    (hall : ∀ i, M.star ∈ ((run p (realTape (X ω)) (J ω) (p.phaseEnd r)).nodes i).active) :
    ∀ t, p.phaseEnd r ≤ t → t ≤ p.T → ∀ i,
      ((run p (realTape (X ω)) (J ω) t).nodes i).active =
        ((run p (realTape (X ω)) (J ω) (p.phaseEnd r)).nodes i).active := by
  let S := p.phaseEnd r
  have hinv : ∀ d, S+d ≤ p.T → ∀ i,
      ((run p (realTape (X ω)) (J ω) (S+d)).nodes i).active =
        ((run p (realTape (X ω)) (J ω) S).nodes i).active := by
    intro d
    induction d with
    | zero => intro _ i; simp
    | succ d ih =>
      intro hd i
      let t := S+d
      have ht : t < p.T := by dsimp [t]; omega
      have hprev := ih (by omega)
      by_cases hc : communicates p t (run p (realTape (X ω)) (J ω) t)
      · let q := (run p (realTape (X ω)) (J ω) t).phase
        have hqpos : 1 ≤ q := (phase_bounds p _ _ t).1
        have hqend : t+1 = p.phaseEnd q := hc.1
        have hqT : p.phaseEnd q < p.T := by rw [← hqend]; exact hc.2
        have hqr : r < q := by
          by_contra hn
          have hle := p.phaseEnd_strictMono.monotone (Nat.le_of_not_gt hn)
          have hSt : p.phaseEnd r ≤ t := by dsimp [t, S]; omega
          omega
        have hi := phase_interval p (realTape (X ω)) (J ω) t ht
        have ha (v : Fin n) := active_during_phase p (realTape (X ω)) (J ω)
          q hqpos t ht hi.1 hi.2 v
        have hstart : ∀ v, M.star ∈
            ((run p (realTape (X ω)) (J ω) (p.phaseEnd (q-1))).nodes v).active := by
          intro v
          rw [← ha v, hprev v]
          exact hall v
        have hrec : ∀ v, ((preBoundary p (realTape (X ω)) (J ω) q).nodes v).cache = M.star := by
          intro v
          exact reliable_cache M p lam X J ω hg q hqpos hqT.le v (hstart v)
            (length_after_preparation M p q (lt_of_le_of_lt hr hqr))
        have hhold : ∀ v, M.star ∈
            ((preBoundary p (realTape (X ω)) (J ω) q).nodes v).active := by
          intro v
          rw [preBoundary_active p _ _ q hqpos hqT.le v]
          exact hstart v
        have he := communicate_active_unchanged_of_all_reliable M.star
          (preBoundary p (realTape (X ω)) (J ω) q) (J ω q) hhold hrec i
        have htime : S + (d+1) = p.phaseEnd q := by dsimp [t] at hqend; omega
        rw [htime, run_boundary p _ _ q hqpos hqT, he,
          preBoundary_active p _ _ q hqpos hqT.le i, ← ha i]
        exact hprev i
      · have htime : S+(d+1) = t+1 := by dsimp [t]; omega
        rw [htime, run_succ]
        simp only [step, if_pos ht, if_neg hc]
        exact hprev i
  intro t hSt ht i
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hSt
  exact hinv d ht i

/-- Whole-set stability follows from ideal completion only when that boundary actually occurs. -/
theorem stable_after_ideal_completion (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n) (ω : Ω)
    (hg : ω ∈ ObservedPrefix.good (selected p X J) (reward X) (mean M p lam X J) p.T p.L)
    (j : ℕ) (ht : p.phaseEnd (preparation M p+j) < p.T)
    (hcomplete : Inform (shiftedContacts M p (J ω)) {holder p M.star} j = univ) :
    ∀ t, p.phaseEnd (preparation M p+j) ≤ t → t ≤ p.T → ∀ i,
      ((run p (realTape (X ω)) (J ω) t).nodes i).active =
        ((run p (realTape (X ω)) (J ω) (p.phaseEnd (preparation M p+j))).nodes i).active := by
  apply stable_after_all_holders M p lam X J ω hg _ (by omega) ht
  intro i
  have h := informed_subset_actual M p lam X J ω hg j ht
  exact (mem_holders _ _ _).mp (h (by rw [hcomplete]; exact mem_univ i))

/-- A pathwise waiting bound using the personal-threshold candidate, valid for either
fatigue mechanism. This is deliberately not the sharper public-minimum candidate and
not yet an expectation/regret theorem. Ideal completion will later hold almost surely
by the original contact law, not be a final theorem hypothesis. -/
theorem path_global_personal_candidate (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n) (ω : Ω)
    (hg : ω ∈ ObservedPrefix.good (selected p X J) (reward X) (mean M p lam X J) p.T p.L)
    (j : ℕ) (hcomplete : Inform (shiftedContacts M p (J ω)) {holder p M.star} j = univ)
    (c : Fin K → ℝ) (cmax : ℝ) (hc : ∀ k, 0 ≤ c k)
    (hstar : c M.star = 0) (hcmax : ∀ k, c k ≤ cmax) :
    (∑ t ∈ range p.T, ∑ i, c (I p (realTape (X ω)) (J ω) t i)) ≤
      (n : ℝ) * cmax * (min p.T (p.phaseEnd (preparation M p+j)) : ℕ) + M.Ccap c p.L := by
  let S := p.phaseEnd (preparation M p+j)
  by_cases hS : S < p.T
  · let R := goodRunOn M p lam X J ω hg
    let D : Fin n → Finset (Fin K) := fun i => (run p (realTape (X ω)) (J ω) S).nodes i |>.D
    have hstable := stable_after_ideal_completion M p lam X J ω hg j hS hcomplete
    have hall : ∀ i, M.star ∈ ((run p (realTape (X ω)) (J ω) S).nodes i).active := by
      intro i
      have h := informed_subset_actual M p lam X J ω hg j hS
      exact (mem_holders _ _ _).mp (h (by rw [hcomplete]; exact mem_univ i))
    apply R.global_wait_cost (by have := p.hn; omega) c cmax S (holder p M.star) D hc hstar hcmax
    · intro t i hSt ht
      change ((run p (realTape (X ω)) (J ω) t).nodes i).active = _
      rw [hstable t hSt ht.le i]
      rfl
    · exact mem_sticky_holder p M.star
    · intro i
      exact (run p (realTape (X ω)) (J ω) S).nodes i |>.disjoint
    · intro i
      exact (run p (realTape (X ω)) (J ω) S).nodes i |>.card_le
    · exact hall
    · intro i
      exact ((run p (realTape (X ω)) (J ω) S).nodes i).active_card_le p
  · have hcut : (range p.T).filter (fun t => t < S) = range p.T := by
      apply filter_eq_self.mpr
      intro t ht
      exact lt_of_lt_of_le (mem_range.mp ht) (Nat.le_of_not_gt hS)
    have hwait := waiting_cost_le (I p (realTape (X ω)) (J ω)) c cmax hcmax p.T S
    rw [hcut] at hwait
    have hcap : 0 ≤ M.Ccap c p.L := by
      unfold DecayModel.Ccap
      exact le_min (mul_nonneg (Nat.cast_nonneg _) (M.Wkappa_nonneg hc p.L))
        (add_nonneg (M.Wsum_nonneg hc p.L)
          (mul_nonneg (by positivity) (M.wmax_nonneg hc p.L)))
    exact hwait.trans (le_add_of_nonneg_right hcap)

end AnvBandit.ActualPropagation
