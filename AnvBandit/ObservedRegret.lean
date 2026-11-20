import AnvBandit.ExecutionObserved
import AnvBandit.GlobalRegret

/-! Exact finite-horizon integral transfer to every original observed execution law.
No cost, concentration, or regret bound is assumed in the probability-law interface. -/
noncomputable section
open scoped BigOperators ENNReal
open Finset MeasureTheory ProbabilityTheory Preorder
namespace AnvBandit.ObservedRegret
open Execution ExecutionLaw GlobalRegret
variable {n K : ℕ}

/-- Actual states before the horizon depend only on the finite observed prefix. -/
theorem run_prefix_congr (p : Params n K) (ω ω' : Path n) (T t : ℕ)
    (ht : t ≤ T) (h : frestrictLe T ω = frestrictLe T ω') :
    run p (realTape (pathRewards ω)) (pathContacts p ω) t =
      run p (realTape (pathRewards ω')) (pathContacts p ω') t := by
  have he : ∀ r ≤ T, ω r = ω' r := by
    intro r hr
    exact congrFun h ⟨r, mem_Iic.mpr hr⟩
  apply run_congr
  · intro s hs
    unfold realTape pathRewards
    rw [he (s+1) (by omega)]
  · intro ℓ hℓ hT
    unfold pathContacts
    rw [he (p.phaseEnd ℓ) (hℓ.trans ht)]

theorem pathCost_prefix_congr (p : Params n K) (c : Fin K → ℝ) (ω ω' : Path n)
    (h : frestrictLe p.T ω = frestrictLe p.T ω') : pathCost p c ω = pathCost p c ω' := by
  apply sum_congr rfl
  intro t ht
  apply sum_congr rfl
  intro i hi
  unfold I
  rw [run_prefix_congr p ω ω' p.T t (Nat.le_of_lt (mem_range.mp ht)) h]

theorem pathCost_observed (p : Params n K) (c : Fin K → ℝ) (ω : Path n) :
    pathCost p c (observedPath p ω) = pathCost p c ω := by
  unfold pathCost I
  simp only [observedPath_run]

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

/-- General measurable finite statistic transfer. The two invariance premises describe
only a deterministic statistic; they impose no additional stochastic hypothesis. -/
theorem original_integral_eq (F : Path n → ℝ)
    (hfinite : ∀ ω ω', frestrictLe p.T ω = frestrictLe p.T ω' → F ω = F ω')
    (hmask : ∀ ω, F (observedPath p ω) = F ω) :
    (∫ ω, F ω ∂ν) = ∫ ω, F ω ∂executionMeasure M p C lam := by
  let f : Prefix n p.T → ℝ := fun h => F (extendPrefix p.T h)
  have hfactor : ∀ ω, f (frestrictLe p.T ω) = F ω := by
    intro ω
    exact hfinite _ _ (extendPrefix_restrict _ _)
  have hf : ∀ h, f (observedPrefix p p.T h) = f h := by
    intro h
    have hh := hfactor (observedPath p (extendPrefix p.T h))
    simpa only [observedPath_prefix, extendPrefix_restrict, hmask] using hh
  have hlaw : ∀ t < p.T,
      condDistrib (fun ω : Path n => ω (t+1)) (frestrictLe t) ν
        =ᵐ[ν.map (frestrictLe t)] observedKernel M p C lam t := by
    intro t ht
    exact observed_transition_of_original M p C lam ν t (hx t ht) (hj t ht) (habsent t ht)
  have he := finite_observed_statistic_transfer M p C lam ν hzero hlaw p.T le_rfl f hf
  have hm : Measurable (fun ω : Path n => f (frestrictLe p.T ω)) :=
    (measurable_of_countable f).comp (measurable_frestrictLe p.T)
  have hi := congrArg (fun μ : Measure ℝ => ∫ x, x ∂μ) he
  rw [integral_map (f := fun x : ℝ => x) hm.aemeasurable measurable_id.aestronglyMeasurable,
    integral_map (f := fun x : ℝ => x) hm.aemeasurable measurable_id.aestronglyMeasurable] at hi
  simpa only [hfactor] using hi

/-- Actual weighted action cost, not a free random variable, has the canonical expectation
under every original observed law. -/
theorem original_weightedLoss_eq (c : Fin K → ℝ) :
    (∫ ω, pathCost p c ω ∂ν) = weightedLoss M p C lam c := by
  exact original_integral_eq M p C lam ν hzero hx hj habsent (pathCost p c)
    (pathCost_prefix_congr p c) (pathCost_observed p c)

/-- The exact global weighted-cost candidate for arbitrary original observed laws.
This wrapper discharges canonical-law transfer rather than asking the user to assume it. -/
theorem original_weightedLoss_global (c : Fin K → ℝ) (cmax : ℝ)
    (hc : ∀ k, 0 ≤ c k) (hstar : c M.star = 0) (hcmax : ∀ k, c k ≤ cmax) :
    (∫ ω, pathCost p c ω ∂ν) ≤
      (n : ℝ)*cmax*ActualWaiting.expectedWaiting M p C lam + M.Clam c p.L 0 lam +
        p.δ*((n : ℝ)*cmax*p.T) := by
  rw [original_weightedLoss_eq M p C lam ν hzero hx hj habsent c]
  have hgood := goodLoss_global_exact M p C lam c cmax hc hstar hcmax
  have hbad := weightedLoss_le_goodLoss_add_failure M p C lam c cmax hc hcmax
  linarith

end OriginalLaw
end AnvBandit.ObservedRegret
