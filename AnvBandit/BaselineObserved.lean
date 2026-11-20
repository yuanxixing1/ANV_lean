import AnvBandit.BaselineTrajectory
import AnvBandit.ExecutionObserved

/-! Original reward-law coverage for the no-communication baseline.
The second outcome coordinate is merely the fixed identity encoding of absent communication.
There is no contact law premise, and no reward independence across rounds is assumed. -/
noncomputable section
open scoped BigOperators ENNReal
open Finset MeasureTheory ProbabilityTheory Preorder
namespace AnvBandit.BaselineObserved
open BaselineExecution BaselineLaw BaselineRegret BaselineTrajectory
variable {n K : ℕ}

theorem run_prefix_congr (p : Params n K) (ω ω' : Path n) (T t : ℕ)
    (ht : t ≤ T) (h : frestrictLe T ω = frestrictLe T ω') :
    run p (realTape (pathRewards ω)) (pathContacts p ω) t =
      run p (realTape (pathRewards ω')) (pathContacts p ω') t := by
  apply run_congr
  intro s hs
  have he := congrFun h ⟨s+1, mem_Iic.mpr (by omega)⟩
  change ω (s+1) = ω' (s+1) at he
  unfold realTape pathRewards
  rw [he]

theorem pathCost_prefix_congr (p : Params n K) (c : Fin K → ℝ) (ω ω' : Path n)
    (h : frestrictLe p.T ω = frestrictLe p.T ω') : pathCost p c ω = pathCost p c ω' := by
  apply sum_congr rfl
  intro t ht
  apply sum_congr rfl
  intro i hi
  unfold I
  rw [run_prefix_congr p ω ω' p.T t (Nat.le_of_lt (mem_range.mp ht)) h]

theorem pathActions_prefix_congr (p : Params n K) (ω ω' : Path n)
    (h : frestrictLe p.T ω = frestrictLe p.T ω') : pathActions p ω = pathActions p ω' := by
  funext i t
  unfold pathActions I
  rw [run_prefix_congr p ω ω' p.T t.val t.isLt.le h]

def originalTeamRegret (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (ν : Measure (Path n)) : ℝ := oracle M p.T lam - ∫ ω, pathReward M p lam ω ∂ν

section OriginalLaw
variable (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (ν : Measure (Path n)) [IsProbabilityMeasure ν]
    (hzero : ν.map (frestrictLe 0) = (executionMeasure M p lam).map (frestrictLe 0))
    (hx : ∀ t < p.T, condDistrib (fun ω : Path n => (ω (t+1)).1) (frestrictLe t) ν
      =ᵐ[ν.map (frestrictLe t)] rewardKernel M p lam t)
    (habsent : ∀ t < p.T, ∀ᵐ ω ∂ν, (ω (t+1)).2 = id)

include hx habsent in
/-- The encoded full outcome law follows from rewards alone, because no contact is observed. -/
theorem original_transition (t : ℕ) (ht : t < p.T) :
    condDistrib (fun ω : Path n => ω (t+1)) (frestrictLe t) ν
      =ᵐ[ν.map (frestrictLe t)] executionKernel M p lam t := by
  let f : (Fin n → Bool) → Outcome n := fun x => (x,id)
  have he : (fun ω : Path n => ω (t+1)) =ᵐ[ν]
      (fun ω => f ((ω (t+1)).1)) := by
    filter_upwards [habsent t ht] with ω hω
    apply Prod.ext
    · rfl
    · exact hω
  rw [condDistrib_congr_left he]
  have hc := condDistrib_comp (mβ := (inferInstance : MeasurableSpace (Prefix n t)))
    (frestrictLe t : Path n → Prefix n t) (μ := ν)
    (Y := fun ω : Path n => (ω (t+1)).1)
    (measurable_fst.comp (measurable_pi_apply (t+1))).aemeasurable
    (measurable_of_countable f)
  filter_upwards [hc, hx t ht] with h hc hx
  change condDistrib (f ∘ fun ω : Path n => (ω (t+1)).1) (frestrictLe t) ν h = _
  rw [hc, Kernel.map_apply _ (measurable_of_countable f), hx]
  change (rewardDistribution M p lam (replay p (prefixHistory t h)).2).toMeasure.map f = _
  rw [PMF.toMeasure_map f _ (measurable_of_countable f)]
  rfl

include hzero hx habsent
/-- Every finite statistic has the canonical expectation under the original conditional reward law. -/
theorem original_integral_eq (F : Path n → ℝ)
    (hfinite : ∀ ω ω', frestrictLe p.T ω = frestrictLe p.T ω' → F ω = F ω') :
    (∫ ω, F ω ∂ν) = ∫ ω, F ω ∂executionMeasure M p lam := by
  let f : Prefix n p.T → ℝ := fun h => F (ExecutionLaw.extendPrefix p.T h)
  have hfactor : ∀ ω, f (frestrictLe p.T ω) = F ω := by
    intro ω
    exact hfinite _ _ (ExecutionLaw.extendPrefix_restrict _ _)
  have he := finite_trajectory_law_unique M p lam ν hzero
    (original_transition M p lam ν hx habsent) p.T le_rfl
  have hi := congrArg (fun μ : Measure (Prefix n p.T) => ∫ h, f h ∂μ) he
  rw [integral_map (measurable_frestrictLe p.T).aemeasurable
    (measurable_of_countable f).stronglyMeasurable.aestronglyMeasurable,
    integral_map (measurable_frestrictLe p.T).aemeasurable
    (measurable_of_countable f).stronglyMeasurable.aestronglyMeasurable] at hi
  simpa only [hfactor] using hi

/-- C.5 under every original no-communication reward law, not only the canonical realization. -/
theorem original_weightedLoss_bound (c : Fin K → ℝ) (cmax : ℝ)
    (hc : ∀ k, 0 ≤ c k) (hcmax : ∀ k, c k ≤ cmax) (hstar : c M.star = 0) :
    (∫ ω, pathCost p c ω ∂ν) ≤ min ((n : ℝ)*cmax*p.T)
      (M.Flam c p.L lam + p.δ*((n : ℝ)*cmax*p.T)) := by
  rw [original_integral_eq M p lam ν hzero hx habsent (pathCost p c)
    (pathCost_prefix_congr p c)]
  exact weightedLoss_bound M p lam c cmax hc hcmax hstar

theorem original_teamRegret_eq : originalTeamRegret M p lam ν = teamRegret M p lam := by
  unfold originalTeamRegret teamRegret
  rw [original_integral_eq M p lam ν hzero hx habsent (pathReward M p lam)
    (by intro ω ω' h; unfold pathReward; rw [pathActions_prefix_congr p ω ω' h])]

/-- The original-law baseline bound, with the original synchronized joint oracle. -/
theorem original_teamRegret_bound :
    originalTeamRegret M p lam ν ≤ Uind ((n : ℝ)*p.T) (M.Gamma lam)
      ((n : ℝ)*M.supOthers (M.rho p.T lam)*p.T) (M.Flam (M.rho p.T lam) p.L lam)
      (p.δ*((n : ℝ)*M.supOthers (M.rho p.T lam)*p.T)) := by
  rw [original_teamRegret_eq M p lam ν hzero hx habsent]
  exact teamRegret_bound M p lam
end OriginalLaw
end AnvBandit.BaselineObserved
