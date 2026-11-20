import AnvBandit.AbsorbingError
import AnvBandit.GlobalRegret
import AnvBandit.AbsorbingHolding

/-! Actual good-event path-cost decomposition. The last actual phase contributes
at most its nominal length; no terminal contact is added. -/
noncomputable section
open scoped BigOperators Classical
open Finset MeasureTheory
namespace AnvBandit.Absorbing
open Execution ExecutionLaw ExecutionBounds GlobalRegret
variable {n K : ℕ} {Ω : Type*}

def phaseTimes (p : Params n K) (X : ℕ → Fin n → ℝ)
    (J : ℕ → Fin n → Fin n) (j : ℕ) : Finset ℕ :=
  (range p.T).filter (fun t => (run p X J t).phase = j+1)

lemma phaseTimes_card_le (p : Params n K) (X : ℕ → Fin n → ℝ)
    (J : ℕ → Fin n → Fin n) (j : ℕ) :
    (phaseTimes p X J j).card ≤ p.phaseEnd (j+1)-p.phaseEnd j := by
  have hs : phaseTimes p X J j ⊆ Ico (p.phaseEnd j) (p.phaseEnd (j+1)) := by
    intro t ht
    have ht' := mem_filter.mp ht
    have hp := phase_interval p X J t (mem_range.mp ht'.1)
    rw [ht'.2, Nat.add_sub_cancel] at hp
    exact mem_Ico.mpr hp
  exact (card_le_card hs).trans_eq (Nat.card_Ico _ _)

lemma holders_eq_state_at_round (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n) (ω : Ω)
    (hg : prefixGood M p lam X J p.T ω) (t : ℕ) (ht : t < p.T) :
    holders M.star (run p (realTape (X ω)) (J ω) t) =
      state M p lam X J ((run p (realTape (X ω)) (J ω) t).phase-1) ω := by
  let ℓ := (run p (realTape (X ω)) (J ω) t).phase
  have hp := phase_interval p (realTape (X ω)) (J ω) t ht
  have hl : 1 ≤ ℓ := (phase_bounds p (realTape (X ω)) (J ω) t).1
  have hv : live M p lam X J (ℓ-1) ω :=
    ⟨hp.1.trans_lt ht, prefixGood_mono M p lam X J (hp.1.trans ht.le) hg⟩
  change _ = state M p lam X J (ℓ-1) ω
  rw [state, if_pos hv]
  ext i
  simp only [mem_holders]
  rw [active_during_phase p _ _ ℓ hl t ht hp.1 hp.2 i]

/-- Missing-holder node-rounds on the good event are bounded by nominal phase
lengths times the *actual absorbed* missing-set cardinalities. -/
theorem missing_rounds_le_phases (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n) (ω : Ω)
    (hg : prefixGood M p lam X J p.T ω) :
    (∑ t ∈ range p.T, ((univ \ holders M.star (run p (realTape (X ω)) (J ω) t)).card : ℝ)) ≤
      ∑ j ∈ range p.T, dEll p.H p.β (j+1) * ((univ \ state M p lam X J j ω).card : ℝ) := by
  let a := fun t => (run p (realTape (X ω)) (J ω) t).phase-1
  let z := fun j => ((univ \ state M p lam X J j ω).card : ℝ)
  have ha : ∀ t ∈ range p.T, a t ∈ range p.T := by
    intro t ht
    have hp := phase_bounds p (realTape (X ω)) (J ω) t
    have ht' := mem_range.mp ht
    exact mem_range.mpr (by dsimp [a]; omega)
  have hround : ∀ t ∈ range p.T,
      ((univ \ holders M.star (run p (realTape (X ω)) (J ω) t)).card : ℝ) = z (a t) := by
    intro t ht
    rw [holders_eq_state_at_round M p lam X J ω hg t (mem_range.mp ht)]
  have hsingle : ∀ t ∈ range p.T, z (a t) = ∑ j ∈ range p.T, if a t = j then z j else 0 := by
    intro t ht
    rw [sum_eq_single (a t)]
    · simp
    · intro j hj hne
      simp [Ne.symm hne]
    · exact fun h => (h (ha t ht)).elim
  calc
    _ = ∑ t ∈ range p.T, ∑ j ∈ range p.T, if a t = j then z j else 0 := by
      apply sum_congr rfl
      intro t ht
      exact (hround t ht).trans (hsingle t ht)
    _ = ∑ j ∈ range p.T, ∑ t ∈ range p.T, if a t = j then z j else 0 := sum_comm
    _ ≤ _ := by
      apply sum_le_sum
      intro j hj
      have he : (range p.T).filter (fun t => a t = j) = phaseTimes p (realTape (X ω)) (J ω) j := by
        ext t
        simp only [phaseTimes, mem_filter, mem_range]
        constructor
        · rintro ⟨ht, he⟩
          have hp := (phase_bounds p (realTape (X ω)) (J ω) t).1
          exact ⟨ht, by dsimp [a] at he; omega⟩
        · rintro ⟨ht, he⟩
          exact ⟨ht, by simp [a, he]⟩
      rw [← sum_filter, he, sum_const, nsmul_eq_mul]
      have hb := phaseTimes_card_le p (realTape (X ω)) (J ω) j
      have hbR : ((phaseTimes p (realTape (X ω)) (J ω) j).card : ℝ) ≤ dEll p.H p.β (j+1) := by
        rw [← p.phaseLength_cast]
        exact_mod_cast hb
      exact mul_le_mul_of_nonneg_right hbR (Nat.cast_nonneg _)

lemma round_cost_split_bound (M : DecayModel n K) (p : Params n K)
    (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n) (t : ℕ)
    (c : Fin K → ℝ) (cmax : ℝ) (hcmax : ∀ k, c k ≤ cmax) :
    (∑ i : Fin n, c (I p X J t i)) ≤
      (∑ i : Fin n, if M.star ∈ ((run p X J t).nodes i).active then c (I p X J t i) else 0) +
      cmax * ((univ \ holders M.star (run p X J t)).card : ℝ) := by
  let A := univ \ holders M.star (run p X J t)
  have hp : ∀ i : Fin n, c (I p X J t i) ≤
      (if M.star ∈ ((run p X J t).nodes i).active then c (I p X J t i) else 0) +
        (if i ∈ A then cmax else 0) := by
    intro i
    by_cases hi : M.star ∈ ((run p X J t).nodes i).active
    · simp [A, hi]
    · simpa [A, hi] using hcmax (I p X J t i)
  have hs := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin n))) => hp i)
  rw [sum_add_distrib] at hs
  have he : (∑ i : Fin n, if i ∈ A then cmax else 0) = cmax * (A.card : ℝ) := by
    rw [← sum_filter]
    simp [mul_comm]
  rwa [he] at hs

lemma cost_le_supOthers (M : DecayModel n K) (c : Fin K → ℝ)
    (hc : ∀ k, 0 ≤ c k) (hstar : c M.star = 0) : ∀ k, c k ≤ M.supOthers c := by
  intro k
  by_cases hk : k = M.star
  · obtain ⟨a, ha⟩ := M.others_nonempty
    rw [hk, hstar]
    exact (hc a).trans (M.le_supOthers ha)
  · exact M.le_supOthers (by simp [DecayModel.others, hk])

lemma Flam_nonneg (M : DecayModel n K) (c : Fin K → ℝ) (L : ℝ) (lam : Fin 2)
    (hc : ∀ k, 0 ≤ c k) : 0 ≤ M.Flam c L lam := by
  have hw := mul_nonneg (Nat.cast_nonneg n) (M.Wsum_nonneg hc L)
  have hn : 0 ≤ (n : ℝ) * M.WNsum c L := by
    apply mul_nonneg (Nat.cast_nonneg n)
    exact sum_nonneg fun k _ => mul_nonneg (hc k) (Nat.cast_nonneg _)
  have hb : 0 ≤ M.Bpub c := by
    unfold DecayModel.Bpub
    apply mul_nonneg (by norm_num)
    apply sum_nonneg
    intro k hk
    have hne : k ≠ M.star := by simpa [DecayModel.others] using hk
    exact mul_nonneg (div_nonneg (hc k) (M.gap_pos hne).le) (by
      unfold DecayModel.Xi DecayModel.Dhalf DecayModel.Ahalf
      exact add_nonneg (tsum_nonneg (fun _ => le_max_right _ _))
        (mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)))
  fin_cases lam
  · exact hw
  · exact le_min hw (add_nonneg hn hb)

def phaseMissingCost (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (ω : Path n) : ℝ :=
  ∑ j ∈ range p.T, dEll p.H p.β (j+1) *
    ((univ \ state M p lam pathRewards (pathContacts p) j ω).card : ℝ)

lemma phaseMissingCost_nonneg (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (ω : Path n) : 0 ≤ phaseMissingCost M p lam ω := by
  apply sum_nonneg
  intro j _
  apply mul_nonneg _ (Nat.cast_nonneg _)
  rw [← p.phaseLength_cast]
  positivity

lemma phaseMissingCost_integrable (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) :
    Integrable (phaseMissingCost M p lam) (executionMeasure M p C lam) :=
  integrable_finset_sum _ (fun j _ => (missing_integrable M p C lam j).const_mul _)

lemma integral_phaseMissingCost (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) :
    (∫ ω, phaseMissingCost M p lam ω ∂executionMeasure M p C lam) =
      ∑ j ∈ range p.T, dEll p.H p.β (j+1) * expectedMissing M p C lam j := by
  unfold phaseMissingCost
  rw [integral_finset_sum _
    (fun j _ => (missing_integrable M p C lam j).const_mul _)]
  simp only [integral_const_mul, expectedMissing]

/-- The actual good-event weighted path loss splits into exact exploration
budget and the actual missing-holder node-round charge. -/
theorem path_cost_le_exploration_phases (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (c : Fin K → ℝ) (hc : ∀ k, 0 ≤ c k) (hstar : c M.star = 0)
    (ω : Path n) (hg : ω ∈ actualGoodEvent M p lam) :
    pathCost p c ω ≤ M.Flam c p.L lam + M.supOthers c * phaseMissingCost M p lam ω := by
  have hmax := cost_le_supOthers M c hc hstar
  have hm0 : 0 ≤ M.supOthers c := (hc M.star).trans (hmax M.star)
  have hround := sum_le_sum (fun t (_ : t ∈ range p.T) =>
    round_cost_split_bound M p (realTape (pathRewards ω)) (pathContacts p ω) t c _ hmax)
  rw [sum_add_distrib, ← mul_sum] at hround
  have hhold := holdingCost_le_Flam M p lam pathRewards (pathContacts p) ω c hc hstar hg
  have hmiss := mul_le_mul_of_nonneg_left
    (missing_rounds_le_phases M p lam pathRewards (pathContacts p) ω hg) hm0
  change pathCost p c ω ≤ holdingCost M p (pathRewards ω) (pathContacts p ω) c + _ at hround
  exact hround.trans (add_le_add hhold hmiss)

/-- Good-event expectation shared with the global and node branches. The
failure penalty is deliberately not added here; the main theorem adds it once. -/
theorem goodLoss_le_exploration_phases (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (c : Fin K → ℝ)
    (hc : ∀ k, 0 ≤ c k) (hstar : c M.star = 0) :
    goodLoss M p C lam c ≤ M.Flam c p.L lam + M.supOthers c *
      ∑ j ∈ range p.T, dEll p.H p.β (j+1) * expectedMissing M p C lam j := by
  let μ := executionMeasure M p C lam
  have hmax := cost_le_supOthers M c hc hstar
  have hm0 : 0 ≤ M.supOthers c := (hc M.star).trans (hmax M.star)
  have hp : ∀ ω, goodCost M p lam c ω ≤ M.Flam c p.L lam +
      M.supOthers c * phaseMissingCost M p lam ω := by
    intro ω
    by_cases hg : ω ∈ actualGoodEvent M p lam
    · simpa only [goodCost, Set.indicator_of_mem hg] using
        path_cost_le_exploration_phases M p lam c hc hstar ω hg
    · simp only [goodCost, Set.indicator_of_notMem hg]
      exact add_nonneg (Flam_nonneg M c p.L lam hc)
        (mul_nonneg hm0 (phaseMissingCost_nonneg M p lam ω))
  have hi := integral_mono (goodCost_integrable M p C lam c _ hc hmax)
    ((integrable_const _).add ((phaseMissingCost_integrable M p C lam).const_mul _)) hp
  simp only [Pi.add_apply] at hi
  rw [integral_add (f := fun _ : Path n => M.Flam c p.L lam)
      (g := fun ω => M.supOthers c * phaseMissingCost M p lam ω)
      (integrable_const _) ((phaseMissingCost_integrable M p C lam).const_mul _),
    integral_const_mul, integral_phaseMissingCost] at hi
  simpa only [goodLoss, integral_const, measureReal_univ_eq_one, one_smul] using hi

end AnvBandit.Absorbing
