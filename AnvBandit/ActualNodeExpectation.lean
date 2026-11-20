import AnvBandit.ActualNodePublic
import AnvBandit.ActualNodeMoments
import AnvBandit.GlobalRegret

/-! Expected node branch on the one finite good event. Candidate expectations are taken
separately before taking their minimum; `Bpub` is paid only once and the bad-event cost
is deliberately left to the shared regret decomposition. -/
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators ENNReal
open Finset MeasureTheory ProbabilityTheory
namespace AnvBandit.ActualNodeExpectation
open Execution ExecutionLaw ActualPropagation ActualWaiting ActualNodeMoments GlobalRegret
variable {n K : ℕ}

private lemma cost_le_sup (M : DecayModel n K) (c : Fin K → ℝ)
    (hc : ∀ k, 0 ≤ c k) (hstar : c M.star = 0) : ∀ k, c k ≤ M.supOthers c := by
  intro k
  by_cases hk : k = M.star
  · obtain ⟨j,hj⟩ := M.others_nonempty
    rw [hk, hstar]
    exact (hc j).trans (M.le_supOthers hj)
  · exact M.le_supOthers (by simp [DecayModel.others, hk])

private lemma integrate_node_bound (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (c : Fin K → ℝ)
    (hc : ∀ k, 0 ≤ c k) (hstar : c M.star = 0) (cap slope extra : ℝ)
    (hpoint : ∀ᵐ ω ∂executionMeasure M p C lam,
      goodCost M p lam c ω ≤
        M.supOthers c * arrivalSum M p ω + cap + slope * residualSum M p ω + extra) :
    goodLoss M p C lam c ≤
      M.supOthers c * Abeta (by have := p.hn; omega) C (holder p M.star)
        p.H (preparation M p) p.β p.T + cap +
        slope * DP (by have := p.hn; omega) p.hn C (holder p M.star) + extra := by
  let μ := executionMeasure M p C lam
  have hE : MeasurableSet (actualGoodEvent M p lam) :=
    (executionFiltration n).le p.T _ (actualGoodEvent_measurable M p lam)
  have hleft := goodCost_integrable M p C lam c (M.supOthers c) hc (cost_le_sup M c hc hstar)
  have ha := arrivalSum_integrable M p C lam
  have hd := residualSum_integrable M p C lam
  have hright : Integrable (fun ω => M.supOthers c * arrivalSum M p ω + cap +
      slope * residualSum M p ω + extra) μ :=
    (((ha.const_mul _).add (integrable_const _)).add (hd.const_mul _)).add (integrable_const _)
  have hb := integral_mono_ae hleft hright hpoint
  have he : (∫ ω, M.supOthers c * arrivalSum M p ω + cap +
      slope * residualSum M p ω + extra ∂μ) =
      M.supOthers c * Abeta (by have := p.hn; omega) C (holder p M.star)
        p.H (preparation M p) p.β p.T + cap +
        slope * DP (by have := p.hn; omega) p.hn C (holder p M.star) + extra := by
    rw [integral_add
        (f := fun ω => M.supOthers c * arrivalSum M p ω + cap + slope * residualSum M p ω)
        (g := fun _ => extra)
        (((ha.const_mul (M.supOthers c)).add (integrable_const cap)).add (hd.const_mul slope))
        (integrable_const extra),
      integral_add (f := fun ω => M.supOthers c * arrivalSum M p ω + cap)
        (g := fun ω => slope * residualSum M p ω)
        ((ha.const_mul (M.supOthers c)).add (integrable_const cap)) (hd.const_mul slope),
      integral_add (f := fun ω => M.supOthers c * arrivalSum M p ω)
        (g := fun _ => cap) (ha.const_mul (M.supOthers c)) (integrable_const cap),
      integral_const_mul, integral_const_mul,
      integral_arrivalSum M p C lam, integral_residualSum M p C lam]
    simp [μ]
  rwa [he] at hb

/-- The actual personal node candidate, from the original model and legal parameters only. -/
theorem goodLoss_node_personal (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (c : Fin K → ℝ)
    (hc : ∀ k, 0 ≤ c k) (hstar : c M.star = 0) :
    goodLoss M p C lam c ≤
      M.supOthers c * Abeta (by have := p.hn; omega) C (holder p M.star)
        p.H (preparation M p) p.β p.T + M.Ccap c p.L +
        M.wmax c p.L * DP (by have := p.hn; omega) p.hn C (holder p M.star) := by
  have hcap : 0 ≤ M.Ccap c p.L := by
    unfold DecayModel.Ccap
    exact le_min (mul_nonneg (Nat.cast_nonneg _) (M.Wkappa_nonneg hc p.L))
      (add_nonneg (M.Wsum_nonneg hc p.L) (mul_nonneg (by positivity) (M.wmax_nonneg hc p.L)))
  have hmax : 0 ≤ M.supOthers c := (hc M.star).trans (cost_le_sup M c hc hstar M.star)
  have hb := integrate_node_bound M p C lam c hc hstar (M.Ccap c p.L) (M.wmax c p.L) 0 ?_
  · simpa only [add_zero] using hb
  filter_upwards [actual_complete_ae M p C lam, actual_arrived_ae M p C lam] with ω hcomplete harrived
  by_cases hg : ω ∈ actualGoodEvent M p lam
  · simp only [goodCost, Set.indicator_of_mem hg]
    have hp := path_node_personal_candidate M p lam pathRewards (pathContacts p) ω hg
      (actualSigma M p ω) (actualTau M p ω) (actualSigma_le_tau M p ω) harrived hcomplete c hc hstar
    simpa only [pathCost, arrivalSum, residualSum, actualArrival, Nat.cast_sum, add_zero] using hp
  · simp only [goodCost, Set.indicator_of_notMem hg]
    have ha : 0 ≤ arrivalSum M p ω := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    have hd : 0 ≤ residualSum M p ω := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    exact add_nonneg (add_nonneg (add_nonneg (mul_nonneg hmax ha) hcap)
      (mul_nonneg (M.wmax_nonneg hc p.L) hd)) le_rfl

/-- The actual public node candidate. The positive-area term is not multiplied by a node
count, removal count, or phase count. -/
theorem goodLoss_node_public (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (c : Fin K → ℝ)
    (hc : ∀ k, 0 ≤ c k) (hstar : c M.star = 0) :
    goodLoss M p C 1 c ≤
      M.supOthers c * Abeta (by have := p.hn; omega) C (holder p M.star)
        p.H (preparation M p) p.β p.T + M.CNcap c p.L +
        M.wNmax c p.L * DP (by have := p.hn; omega) p.hn C (holder p M.star) + M.Bpub c := by
  have hweights := ActualPublicBudget.statisticalWeights_nonneg M c hc p.L
  have hcap : 0 ≤ M.CNcap c p.L := by
    rw [← ActualPublicBudget.Ccap_statisticalWeights]
    unfold DecayModel.Ccap
    exact le_min (mul_nonneg (Nat.cast_nonneg _) (M.Wkappa_nonneg hweights p.L))
      (add_nonneg (M.Wsum_nonneg hweights p.L) (mul_nonneg (by positivity) (M.wmax_nonneg hweights p.L)))
  have hmaxN : 0 ≤ M.wNmax c p.L := by
    have hw : M.wk (ActualPublicBudget.statisticalWeights M c p.L) p.L = M.wkN c p.L :=
      funext (ActualPublicBudget.wk_statisticalWeights M c p.L)
    simpa only [DecayModel.wmax, DecayModel.wNmax, hw] using M.wmax_nonneg hweights p.L
  have hmax : 0 ≤ M.supOthers c := (hc M.star).trans (cost_le_sup M c hc hstar M.star)
  have hpub : 0 ≤ M.Bpub c := by
    unfold DecayModel.Bpub
    apply mul_nonneg (by norm_num)
    apply sum_nonneg
    intro k hk
    have hne : k ≠ M.star := by simpa [DecayModel.others] using hk
    exact mul_nonneg (div_nonneg (hc k) (M.gap_pos hne).le) (by
      unfold DecayModel.Xi DecayModel.Dhalf DecayModel.Ahalf
      exact add_nonneg (tsum_nonneg (fun _ => le_max_right _ _))
        (mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)))
  apply integrate_node_bound M p C 1 c hc hstar (M.CNcap c p.L) (M.wNmax c p.L) (M.Bpub c)
  filter_upwards [actual_complete_ae M p C 1, actual_arrived_ae M p C 1] with ω hcomplete harrived
  by_cases hg : ω ∈ actualGoodEvent M p 1
  · simp only [goodCost, Set.indicator_of_mem hg]
    have hp := path_node_public_candidate M p pathRewards (pathContacts p) ω hg
      (actualSigma M p ω) (actualTau M p ω) (actualSigma_le_tau M p ω) harrived hcomplete c hc hstar
    simpa only [pathCost, arrivalSum, residualSum, actualArrival, Nat.cast_sum] using hp
  · simp only [goodCost, Set.indicator_of_notMem hg]
    have ha : 0 ≤ arrivalSum M p ω := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    have hd : 0 ≤ residualSum M p ω := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    exact add_nonneg (add_nonneg (add_nonneg (mul_nonneg hmax ha) hcap)
      (mul_nonneg hmaxN hd)) hpub

/-- The public node branch takes the minimum only after integrating both candidates. -/
theorem goodLoss_node_public_min (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (c : Fin K → ℝ)
    (hc : ∀ k, 0 ≤ c k) (hstar : c M.star = 0) :
    goodLoss M p C 1 c ≤
      M.supOthers c * Abeta (by have := p.hn; omega) C (holder p M.star)
        p.H (preparation M p) p.β p.T +
        M.Clam c p.L (DP (by have := p.hn; omega) p.hn C (holder p M.star)) 1 := by
  have hp := goodLoss_node_personal M p C 1 c hc hstar
  have hn := goodLoss_node_public M p C c hc hstar
  change _ ≤ _ + min _ _
  rw [add_min]
  exact le_min (by nlinarith [hp]) (by nlinarith [hn])

/-- Full per-node expected weighted-cost branch (C.1), on the common finite good event.
All auxiliary probabilistic, permanence, removal, and exact capacity premises have been
proved from the original actual law. -/
theorem goodLoss_node (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (c : Fin K → ℝ)
    (hc : ∀ k, 0 ≤ c k) (hstar : c M.star = 0) :
    goodLoss M p C lam c ≤
      M.supOthers c * Abeta (by have := p.hn; omega) C (holder p M.star)
        p.H (preparation M p) p.β p.T +
        M.Clam c p.L (DP (by have := p.hn; omega) p.hn C (holder p M.star)) lam := by
  by_cases hl : lam = 0
  · subst lam
    have h := goodLoss_node_personal M p C 0 c hc hstar
    change _ ≤ _ + (M.Ccap c p.L + _ * M.wmax c p.L)
    nlinarith [h]
  · have h1 : lam = 1 := by
      apply Fin.ext
      have hn : lam.val ≠ 0 := fun h => hl (Fin.ext h)
      have hb := lam.isLt
      change lam.val = 1
      omega
    subst lam
    exact goodLoss_node_public_min M p C c hc hstar

end AnvBandit.ActualNodeExpectation
