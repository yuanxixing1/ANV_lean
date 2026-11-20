import AnvBandit.BaselineProbability
import AnvBandit.BaselinePublicBudget
import AnvBandit.TrajectoryExpectation
noncomputable section
open scoped BigOperators ENNReal
open Finset MeasureTheory ProbabilityTheory

namespace AnvBandit.BaselineRegret
open BaselineExecution BaselineLaw
variable {n K : ℕ}

def pathCost (p : Params n K) (c : Fin K → ℝ) (ω : Path n) : ℝ :=
  ∑ t ∈ range p.T, ∑ i, c (I p (realTape (pathRewards ω)) (pathContacts p ω) t i)

def weightedLoss (M : DecayModel n K) (p : Params n K) 
    (lam : Fin 2) (c : Fin K → ℝ) : ℝ :=
  ∫ ω, pathCost p c ω ∂executionMeasure M p lam

def goodCost (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (c : Fin K → ℝ) : Path n → ℝ :=
  (actualGoodEvent M p lam).indicator (pathCost p c)

/-- The same good-event expected loss is shared by all three branches. -/
def goodLoss (M : DecayModel n K) (p : Params n K) 
    (lam : Fin 2) (c : Fin K → ℝ) : ℝ :=
  ∫ ω, goodCost M p lam c ω ∂executionMeasure M p lam

theorem pathCost_measurable (p : Params n K) (c : Fin K → ℝ) : Measurable (pathCost p c) := by
  apply Finset.measurable_sum
  intro t ht
  apply Finset.measurable_sum
  intro i hi
  exact (measurable_of_countable c).comp
    ((action_predictable p t i).mono ((executionFiltration n).le t) le_rfl)

theorem pathCost_nonneg (p : Params n K) (c : Fin K → ℝ) (hc : ∀ k, 0 ≤ c k)
    (ω : Path n) : 0 ≤ pathCost p c ω :=
  sum_nonneg (fun t _ => sum_nonneg (fun i _ => hc _))

theorem pathCost_le (p : Params n K) (c : Fin K → ℝ) (cmax : ℝ)
    (hcmax : ∀ k, c k ≤ cmax) (ω : Path n) : pathCost p c ω ≤ (n : ℝ)*cmax*p.T := by
  calc pathCost p c ω ≤ ∑ _t ∈ range p.T, ∑ _i : Fin n, cmax := by
         exact sum_le_sum (fun _ _ => sum_le_sum (fun _ _ => hcmax _))
       _ = (n : ℝ)*cmax*p.T := by simp; ring

theorem pathCost_integrable (M : DecayModel n K) (p : Params n K) 
    (lam : Fin 2) (c : Fin K → ℝ) (cmax : ℝ) (hc : ∀ k, 0 ≤ c k)
    (hcmax : ∀ k, c k ≤ cmax) : Integrable (pathCost p c) (executionMeasure M p lam) := by
  apply Integrable.of_bound (pathCost_measurable p c).stronglyMeasurable.aestronglyMeasurable
    ((n : ℝ)*cmax*p.T)
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (pathCost_nonneg p c hc ω)]
  exact pathCost_le p c cmax hcmax ω

theorem goodCost_integrable (M : DecayModel n K) (p : Params n K) 
    (lam : Fin 2) (c : Fin K → ℝ) (cmax : ℝ) (hc : ∀ k, 0 ≤ c k)
    (hcmax : ∀ k, c k ≤ cmax) : Integrable (goodCost M p lam c) (executionMeasure M p lam) :=
  (pathCost_integrable M p lam c cmax hc hcmax).indicator
    ((executionFiltration n).le p.T _ (actualGoodEvent_measurable M p lam))

theorem goodCost_nonneg (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (c : Fin K → ℝ) (hc : ∀ k, 0 ≤ c k) (ω : Path n) : 0 ≤ goodCost M p lam c ω := by
  classical
  by_cases h : ω ∈ actualGoodEvent M p lam
  · simpa [goodCost, h] using pathCost_nonneg p c hc ω
  · simp [goodCost, h]

theorem weightedLoss_le_goodLoss_add_failure (M : DecayModel n K) (p : Params n K)
     (lam : Fin 2) (c : Fin K → ℝ) (cmax : ℝ)
    (hc : ∀ k, 0 ≤ c k) (hcmax : ∀ k, c k ≤ cmax) :
    weightedLoss M p lam c ≤ goodLoss M p lam c + p.δ*((n : ℝ)*cmax*p.T) := by
  let μ := executionMeasure M p lam
  let E := actualGoodEvent M p lam
  let B : ℝ := (n : ℝ)*cmax*p.T
  let bad : Path n → ℝ := Eᶜ.indicator (fun _ => B)
  have hcm0 : 0 ≤ cmax := (hc M.star).trans (hcmax M.star)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hE : MeasurableSet E := (executionFiltration n).le p.T _ (actualGoodEvent_measurable M p lam)
  have hgI := goodCost_integrable M p lam c cmax hc hcmax
  have hbI : Integrable bad μ := (integrable_const B).indicator hE.compl
  have hpoint : ∀ ω, pathCost p c ω ≤ goodCost M p lam c ω + bad ω := by
    intro ω
    by_cases h : ω ∈ E
    · simp [goodCost, bad, E, h]
    · simpa [goodCost, bad, E, h] using pathCost_le p c cmax hcmax ω
  have hmono := integral_mono_ae (pathCost_integrable M p lam c cmax hc hcmax)
    (hgI.add hbI) (Filter.Eventually.of_forall hpoint)
  have hbad : (∫ ω, bad ω ∂μ) = μ.real Eᶜ*B := by
    simp [bad, hE.compl, smul_eq_mul]
  have hδ : μ.real Eᶜ*B ≤ p.δ*B :=
    mul_le_mul_of_nonneg_right (actual_good_compl_le M p lam) hB
  change (∫ ω, pathCost p c ω ∂μ) ≤
    ∫ ω, goodCost M p lam c ω + bad ω ∂μ at hmono
  rw [integral_add hgI hbI, hbad] at hmono
  change weightedLoss M p lam c ≤ goodLoss M p lam c + μ.real Eᶜ*B at hmono
  change weightedLoss M p lam c ≤ goodLoss M p lam c + p.δ*B
  linarith



/-- All arms are always available, so the holding cost is the entire cost. -/
theorem pathCost_eq_holding (M : DecayModel n K) (p : Params n K)
    (c : Fin K → ℝ) (hstar : c M.star = 0) (ω : Path n) :
    pathCost p c ω = ∑ i, ∑ k ∈ M.others, c k *
      (BaselinePublicBudget.holdingTimes M p (pathRewards ω) (pathContacts p ω) i k).card := by
  symm
  have hi (i : Fin n) : (∑ k ∈ M.others, c k *
      (BaselinePublicBudget.holdingTimes M p (pathRewards ω) (pathContacts p ω) i k).card) =
      ∑ t ∈ range p.T, c (I p (realTape (pathRewards ω)) (pathContacts p ω) t i) := by
    have he := M.sum_erase_star (fun k => c k *
      (BaselinePublicBudget.holdingTimes M p (pathRewards ω) (pathContacts p ω) i k).card)
    simp only [hstar, zero_mul, zero_add] at he
    rw [← he]
    simp only [BaselinePublicBudget.holdingTimes, LocalState.active, mem_univ, true_and,
      card_eq_sum_ones, sum_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      mul_sum, mul_ite, mul_one, mul_zero]
    rw [sum_comm]
    simp
  simp_rw [hi]
  exact sum_comm

theorem pathCost_good_bound (M : DecayModel n K) (p : Params n K)
    (lam : Fin 2) (c : Fin K → ℝ) (hc : ∀ k, 0 ≤ c k) (hstar : c M.star = 0)
    (ω : Path n) (hω : ω ∈ actualGoodEvent M p lam) :
    pathCost p c ω ≤ M.Flam c p.L lam := by
  rw [pathCost_eq_holding M p c hstar ω]
  fin_cases lam
  · let R := actualGoodRun M p 0 ω hω
    have hpair : ∀ i k, k ∈ M.others →
        c k * (BaselinePublicBudget.holdingTimes M p (pathRewards ω) (pathContacts p ω) i k).card ≤
          c k * (M.mkAll p.L k : ℝ) := by
      intro i k hk
      have hne : k ≠ M.star := by simpa [DecayModel.others] using hk
      have h := R.pair_budget i hne
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast h) (hc k)
    calc _ ≤ ∑ _i : Fin n, M.Wsum c p.L := by
           apply sum_le_sum; intro i _
           exact sum_le_sum (fun k hk => hpair i k hk)
         _ = M.Flam c p.L 0 := by simp [DecayModel.Flam]
  · exact BaselinePublicBudget.holding_cost_le_F1 M p pathRewards (pathContacts p) ω c hc hω

theorem goodLoss_bound (M : DecayModel n K) (p : Params n K)
    (lam : Fin 2) (c : Fin K → ℝ) (cmax : ℝ)
    (hc : ∀ k, 0 ≤ c k) (hcmax : ∀ k, c k ≤ cmax) (hstar : c M.star = 0) :
    goodLoss M p lam c ≤ M.Flam c p.L lam := by
  have hF : 0 ≤ M.Flam c p.L lam := by
    fin_cases lam
    · exact mul_nonneg (Nat.cast_nonneg _) (sum_nonneg (fun k _ => mul_nonneg (hc k) (Nat.cast_nonneg _)))
    · apply le_min
      · exact mul_nonneg (Nat.cast_nonneg _) (sum_nonneg (fun k _ => mul_nonneg (hc k) (Nat.cast_nonneg _)))
      · apply add_nonneg
        · exact mul_nonneg (Nat.cast_nonneg _) (sum_nonneg (fun k _ => mul_nonneg (hc k) (Nat.cast_nonneg _)))
        · unfold DecayModel.Bpub
          apply mul_nonneg (by norm_num)
          apply sum_nonneg
          intro k hk
          exact mul_nonneg (div_nonneg (hc k) (M.gap_pos (by simpa [DecayModel.others] using hk)).le)
            (by
              unfold DecayModel.Xi DecayModel.Dhalf DecayModel.Ahalf
              exact add_nonneg (tsum_nonneg (fun _ => le_max_right _ _))
                (mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)))
  have hpoint : ∀ ω, goodCost M p lam c ω ≤ M.Flam c p.L lam := by
    intro ω
    by_cases hω : ω ∈ actualGoodEvent M p lam
    · simpa [goodCost, hω] using pathCost_good_bound M p lam c hc hstar ω hω
    · simpa [goodCost, hω] using hF
  have h := integral_mono_ae (goodCost_integrable M p lam c cmax hc hcmax)
    (integrable_const (M.Flam c p.L lam)) (Filter.Eventually.of_forall hpoint)
  simpa [goodLoss] using h

theorem weightedLoss_bound (M : DecayModel n K) (p : Params n K)
    (lam : Fin 2) (c : Fin K → ℝ) (cmax : ℝ)
    (hc : ∀ k, 0 ≤ c k) (hcmax : ∀ k, c k ≤ cmax) (hstar : c M.star = 0) :
    weightedLoss M p lam c ≤ min ((n : ℝ)*cmax*p.T)
      (M.Flam c p.L lam + p.δ*((n : ℝ)*cmax*p.T)) := by
  apply le_min
  · have h := integral_mono_ae (pathCost_integrable M p lam c cmax hc hcmax)
      (integrable_const ((n : ℝ)*cmax*p.T))
      (Filter.Eventually.of_forall (pathCost_le p c cmax hcmax))
    simpa [weightedLoss] using h
  · have hfail := weightedLoss_le_goodLoss_add_failure M p lam c cmax hc hcmax
    have hgood := goodLoss_bound M p lam c cmax hc hcmax hstar
    linarith

end AnvBandit.BaselineRegret
