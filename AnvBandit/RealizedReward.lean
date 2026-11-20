import AnvBandit.ObservedTrajectory

/-! The trajectory's fatigue indices are the actual maintained pre-round counters.
The expected observed reward equals the expected trajectory value. -/
noncomputable section
open scoped BigOperators ENNReal
open Finset MeasureTheory ProbabilityTheory Preorder
namespace AnvBandit.RealizedReward
open Execution ExecutionLaw TrajectoryExpectation ObservedRegret
variable {n K : ℕ}

theorem Nfin_pathActions (p : Params n K) (ω : Path n) (t : Fin p.T) (i : Fin n) (k : Fin K) :
    Nfin (pathActions p ω) t i k = N p (realTape (pathRewards ω)) (pathContacts p ω) t.val i k := by
  rw [N_eq_sum p _ _ t.val t.isLt.le, Nfin, card_eq_sum_ones, sum_filter]
  change (∑ s : Fin p.T, if s.val < t.val ∧
    I p (realTape (pathRewards ω)) (pathContacts p ω) s.val i = k then 1 else 0) = _
  rw [Fin.sum_univ_eq_sum_range (fun s => if s < t.val ∧
    I p (realTape (pathRewards ω)) (pathContacts p ω) s i = k then (1 : ℕ) else 0) p.T]
  calc
    _ = ∑ s ∈ range t.val, if s < t.val ∧
        I p (realTape (pathRewards ω)) (pathContacts p ω) s i = k then 1 else 0 := by
      symm
      apply sum_subset (range_mono t.isLt.le)
      intro s hs hst
      simp only [mem_range] at hst
      simp [hst]
    _ = _ := sum_congr rfl (fun s hs => by simp [mem_range.mp hs])

theorem pathReward_eq_actualMeans (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (ω : Path n) : pathReward M p lam ω =
      ∑ t : Fin p.T, ∑ i : Fin n,
        actualMean M p lam (pathRewards ω) (pathContacts p ω) t.val i := by
  unfold pathReward jointValue
  split <;> rename_i h
  · simp only [J0, qeff0, Nfin_pathActions, actualMean, effectiveUse, h, if_pos,
      pathActions]
  · simp only [J1, qeff1, Nfin_pathActions, actualMean, effectiveUse, h, if_false,
      pathActions, teamCount]

def realizedTotal (p : Params n K) (ω : Path n) : ℝ :=
  ∑ t : Fin p.T, ∑ i : Fin n, rewardReal (pathRewards ω t.val i)

theorem reward_integrable (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (t : ℕ) (i : Fin n) :
    Integrable (fun ω => rewardReal (pathRewards ω t i)) (executionMeasure M p C lam) := by
  apply Integrable.of_bound (C := 1)
  · exact ((reward_adapted t i).mono ((executionFiltration n).le (t+1))).aestronglyMeasurable
  · filter_upwards [] with ω
    simpa [Real.norm_eq_abs, abs_of_nonneg (rewardReal_mem _).1] using (rewardReal_mem (pathRewards ω t i)).2

theorem mean_integrable (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (t : ℕ) (i : Fin n) :
    Integrable (fun ω => actualMean M p lam (pathRewards ω) (pathContacts p ω) t i)
      (executionMeasure M p C lam) := by
  apply Integrable.of_bound (C := 1)
  · exact ((actualMean_predictable M p lam t i).mono ((executionFiltration n).le t)).aestronglyMeasurable
  · filter_upwards [] with ω
    simpa [Real.norm_eq_abs, abs_of_nonneg (actualMean_mem M p lam (pathRewards ω) (pathContacts p ω) t i).1]
      using (actualMean_mem M p lam (pathRewards ω) (pathContacts p ω) t i).2

theorem integral_reward_eq_mean (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (t : ℕ) (i : Fin n) :
    (∫ ω, rewardReal (pathRewards ω t i) ∂executionMeasure M p C lam) =
      ∫ ω, actualMean M p lam (pathRewards ω) (pathContacts p ω) t i ∂executionMeasure M p C lam := by
  rw [← integral_condExp ((executionFiltration n).le t)]
  exact integral_congr_ae (conditional_reward_mean M p C lam t i)

/-- The conditional mean is averaged at the actual observed history, never after
conditioning on the full future action trajectory. -/
theorem expected_realized_eq_pathReward (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) :
    (∫ ω, realizedTotal p ω ∂executionMeasure M p C lam) =
      ∫ ω, pathReward M p lam ω ∂executionMeasure M p C lam := by
  simp only [realizedTotal, pathReward_eq_actualMeans]
  rw [integral_finsetSum univ (fun t _ => integrable_finsetSum univ
      (fun i _ => reward_integrable M p C lam t.val i)),
    integral_finsetSum univ (fun t _ => integrable_finsetSum univ
      (fun i _ => mean_integrable M p C lam t.val i))]
  apply sum_congr rfl
  intro t ht
  rw [integral_finsetSum univ (fun i _ => reward_integrable M p C lam t.val i),
    integral_finsetSum univ (fun i _ => mean_integrable M p C lam t.val i)]
  exact sum_congr rfl (fun i _ => integral_reward_eq_mean M p C lam t.val i)

theorem realizedTotal_prefix_congr (p : Params n K) (ω ω' : Path n)
    (h : frestrictLe p.T ω = frestrictLe p.T ω') : realizedTotal p ω = realizedTotal p ω' := by
  apply sum_congr rfl
  intro t ht
  apply sum_congr rfl
  intro i hi
  have he : ω (t.val+1) = ω' (t.val+1) := congrFun h ⟨t.val+1, mem_Iic.mpr t.isLt⟩
  unfold pathRewards
  rw [he]

theorem realizedTotal_observed (p : Params n K) (ω : Path n) :
    realizedTotal p (observedPath p ω) = realizedTotal p ω := rfl

section OriginalLaw
variable (M : DecayModel n K) (p : Params n K) (C : ContactMatrix n) (lam : Fin 2)
    (ν : Measure (Path n)) [IsProbabilityMeasure ν]
    (hzero : ν.map (frestrictLe 0) = (observedMeasure M p C lam).map (frestrictLe 0))
    (hx : ∀ t < p.T, condDistrib (fun ω : Path n => (ω (t+1)).1) (frestrictLe t) ν
      =ᵐ[ν.map (frestrictLe t)] rewardKernel M p lam t)
    (hj : ∀ t < p.T, retainedContact p (t+1) →
      condDistrib (fun ω : Path n => (ω (t+1)).2)
        (fun ω : Path n => (frestrictLe t ω, (ω (t+1)).1)) ν
        =ᵐ[ν.map (fun ω => (frestrictLe t ω, (ω (t+1)).1))]
        Kernel.const (Prefix n t × (Fin n → Bool)) (contactDistribution C).toMeasure)
    (habsent : ∀ t < p.T, ¬retainedContact p (t+1) → ∀ᵐ ω ∂ν, (ω (t+1)).2 = id)

include hzero hx hj habsent

/-- The observed-reward interpretation also holds for every original finite law. -/
theorem expected_realized_eq_pathReward_original :
    (∫ ω, realizedTotal p ω ∂ν) = ∫ ω, pathReward M p lam ω ∂ν := by
  rw [original_integral_eq M p C lam ν hzero hx hj habsent (realizedTotal p)
    (realizedTotal_prefix_congr p) (realizedTotal_observed p),
    original_pathReward_integral M p C lam ν hzero hx hj habsent]
  exact expected_realized_eq_pathReward M p C lam

end OriginalLaw

end AnvBandit.RealizedReward
