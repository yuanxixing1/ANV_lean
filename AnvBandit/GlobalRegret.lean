import AnvBandit.ActualWaiting
import AnvBandit.ExecutionProbability
import AnvBandit.ActualGlobalPublic

/-!
# Expected weighted cost of the actual algorithm

All random variables below are functions of the constructed actual execution, not free
real-valued cost inputs. The first theorem integrates the personal-threshold waiting
candidate; the sharper public candidate and final trajectory conversion are separate steps.
-/
noncomputable section
open scoped BigOperators ENNReal
open Finset MeasureTheory ProbabilityTheory

namespace AnvBandit.GlobalRegret
open Execution ExecutionLaw ActualPropagation ActualWaiting
variable {n K : ℕ}

def pathCost (p : Params n K) (c : Fin K → ℝ) (ω : Path n) : ℝ :=
  ∑ t ∈ range p.T, ∑ i, c (I p (realTape (pathRewards ω)) (pathContacts p ω) t i)

def weightedLoss (M : DecayModel n K) (p : Params n K) (C : ContactMatrix n)
    (lam : Fin 2) (c : Fin K → ℝ) : ℝ :=
  ∫ ω, pathCost p c ω ∂executionMeasure M p C lam

def goodCost (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (c : Fin K → ℝ) : Path n → ℝ :=
  (actualGoodEvent M p lam).indicator (pathCost p c)

/-- The same good-event expected loss is shared by all three branches. -/
def goodLoss (M : DecayModel n K) (p : Params n K) (C : ContactMatrix n)
    (lam : Fin 2) (c : Fin K → ℝ) : ℝ :=
  ∫ ω, goodCost M p lam c ω ∂executionMeasure M p C lam

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
  have h := waiting_cost_le (I p (realTape (pathRewards ω)) (pathContacts p ω)) c cmax hcmax p.T p.T
  have hs : (range p.T).filter (fun t => t < p.T) = range p.T :=
    filter_eq_self.mpr (fun t ht => mem_range.mp ht)
  simpa only [pathCost, hs, Nat.min_self] using h

theorem pathCost_integrable (M : DecayModel n K) (p : Params n K) (C : ContactMatrix n)
    (lam : Fin 2) (c : Fin K → ℝ) (cmax : ℝ) (hc : ∀ k, 0 ≤ c k)
    (hcmax : ∀ k, c k ≤ cmax) : Integrable (pathCost p c) (executionMeasure M p C lam) := by
  apply Integrable.of_bound (pathCost_measurable p c).stronglyMeasurable.aestronglyMeasurable
    ((n : ℝ)*cmax*p.T)
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (pathCost_nonneg p c hc ω)]
  exact pathCost_le p c cmax hcmax ω

theorem goodCost_integrable (M : DecayModel n K) (p : Params n K) (C : ContactMatrix n)
    (lam : Fin 2) (c : Fin K → ℝ) (cmax : ℝ) (hc : ∀ k, 0 ≤ c k)
    (hcmax : ∀ k, c k ≤ cmax) : Integrable (goodCost M p lam c) (executionMeasure M p C lam) :=
  (pathCost_integrable M p C lam c cmax hc hcmax).indicator
    ((executionFiltration n).le p.T _ (actualGoodEvent_measurable M p lam))

theorem goodCost_nonneg (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (c : Fin K → ℝ) (hc : ∀ k, 0 ≤ c k) (ω : Path n) : 0 ≤ goodCost M p lam c ω := by
  classical
  by_cases h : ω ∈ actualGoodEvent M p lam
  · simpa [goodCost, h] using pathCost_nonneg p c hc ω
  · simp [goodCost, h]

theorem waiting_measurable (M : DecayModel n K) (p : Params n K) :
    Measurable (fun ω : Path n => ((min p.T (actualS M p ω) : ℕ) : ℝ)) := by
  simpa only [Nat.cast_min] using measurable_const.min (measurable_actualS_real M p)

theorem waiting_integrable (M : DecayModel n K) (p : Params n K) (C : ContactMatrix n)
    (lam : Fin 2) : Integrable (fun ω : Path n => ((min p.T (actualS M p ω) : ℕ) : ℝ))
      (executionMeasure M p C lam) := by
  apply Integrable.of_bound (waiting_measurable M p).stronglyMeasurable.aestronglyMeasurable (p.T : ℝ)
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact Nat.cast_le.mpr (Nat.min_le_left _ _)

theorem integral_waiting (M : DecayModel n K) (p : Params n K) (C : ContactMatrix n)
    (lam : Fin 2) :
    (∫ ω, ((min p.T (actualS M p ω) : ℕ) : ℝ) ∂executionMeasure M p C lam) =
      expectedWaiting M p C lam := by
  exact integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun ω => Nat.cast_nonneg _))
    (waiting_measurable M p).stronglyMeasurable.aestronglyMeasurable

/-- First actual expected-cost branch. All probability, recommendation, stability and
path-budget prerequisites are derived internally. This remains the personal-threshold
candidate for either fatigue mode, not the public-minimum or three-branch theorem. -/
theorem weightedLoss_global_personal_candidate (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (c : Fin K → ℝ) (cmax : ℝ)
    (hc : ∀ k, 0 ≤ c k) (hstar : c M.star = 0) (hcmax : ∀ k, c k ≤ cmax) :
    weightedLoss M p C lam c ≤ (n : ℝ)*cmax*expectedWaiting M p C lam +
      M.Ccap c p.L + p.δ*((n : ℝ)*cmax*p.T) := by
  let μ := executionMeasure M p C lam
  let E := actualGoodEvent M p lam
  let w : Path n → ℝ := fun ω => ((min p.T (actualS M p ω) : ℕ) : ℝ)
  let B : ℝ := (n : ℝ)*cmax*p.T
  let bad : Path n → ℝ := Eᶜ.indicator (fun _ => B)
  have hcm0 : 0 ≤ cmax := (hc M.star).trans (hcmax M.star)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hcap : 0 ≤ M.Ccap c p.L := by
    unfold DecayModel.Ccap
    exact le_min (mul_nonneg (Nat.cast_nonneg _) (M.Wkappa_nonneg hc p.L))
      (add_nonneg (M.Wsum_nonneg hc p.L) (mul_nonneg (by positivity) (M.wmax_nonneg hc p.L)))
  have hE : MeasurableSet E :=
    (executionFiltration n).le p.T _ (actualGoodEvent_measurable M p lam)
  have hw : Integrable w μ := waiting_integrable M p C lam
  have hb : Integrable bad μ := (integrable_const B).indicator hE.compl
  have hright : Integrable (fun ω => (n : ℝ)*cmax*w ω + M.Ccap c p.L + bad ω) μ :=
    ((hw.const_mul _).add (integrable_const _)).add hb
  have hpoint : ∀ᵐ ω ∂μ, pathCost p c ω ≤ (n : ℝ)*cmax*w ω + M.Ccap c p.L + bad ω := by
    filter_upwards [actual_complete_ae M p C lam] with ω hcomplete
    by_cases hg : ω ∈ E
    · have hpath := path_global_personal_candidate M p lam pathRewards (pathContacts p)
        ω hg (actualTau M p ω) hcomplete c cmax hc hstar hcmax
      simpa [pathCost, w, actualS, bad, hg, E] using hpath
    · have hbval : bad ω = B := by simp [bad, hg]
      rw [hbval]
      have hw0 : 0 ≤ w ω := Nat.cast_nonneg _
      have hbase := pathCost_le p c cmax hcmax ω
      have hwait0 : 0 ≤ (n : ℝ)*cmax*w ω := by positivity
      change pathCost p c ω ≤ (n : ℝ)*cmax*w ω + M.Ccap c p.L + (n : ℝ)*cmax*p.T
      linarith
  calc
    weightedLoss M p C lam c ≤ ∫ ω, (n : ℝ)*cmax*w ω + M.Ccap c p.L + bad ω ∂μ :=
      integral_mono_ae (pathCost_integrable M p C lam c cmax hc hcmax) hright hpoint
    _ = (n : ℝ)*cmax*expectedWaiting M p C lam + M.Ccap c p.L + μ.real Eᶜ*B := by
      rw [integral_add (f := fun ω => (n : ℝ)*cmax*w ω + M.Ccap c p.L) (g := bad)
          ((hw.const_mul ((n : ℝ)*cmax)).add (integrable_const (M.Ccap c p.L))) hb,
        integral_add (f := fun ω => (n : ℝ)*cmax*w ω) (g := fun _ => M.Ccap c p.L)
          (hw.const_mul ((n : ℝ)*cmax)) (integrable_const (M.Ccap c p.L)), integral_const_mul,
        integral_waiting M p C lam]
      simp [bad, hE.compl, μ, smul_eq_mul]
    _ ≤ _ := by
      have hδ : μ.real Eᶜ*B ≤ p.δ*B :=
        mul_le_mul_of_nonneg_right (actual_good_compl_le M p C lam) hB
      change (n : ℝ)*cmax*expectedWaiting M p C lam + M.Ccap c p.L + μ.real Eᶜ*B ≤
        (n : ℝ)*cmax*expectedWaiting M p C lam + M.Ccap c p.L + p.δ*B
      linarith

/-- Exact global good-event branch with both paper fatigue mechanisms and Cλ(c;0).
No derived bound, probability, reliability or stability is supplied as an input. -/
theorem goodLoss_global_exact (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (c : Fin K → ℝ) (cmax : ℝ)
    (hc : ∀ k, 0 ≤ c k) (hstar : c M.star = 0) (hcmax : ∀ k, c k ≤ cmax) :
    goodLoss M p C lam c ≤ (n : ℝ)*cmax*expectedWaiting M p C lam + M.Clam c p.L 0 lam := by
  let μ := executionMeasure M p C lam
  let w : Path n → ℝ := fun ω => ((min p.T (actualS M p ω) : ℕ) : ℝ)
  have hcm0 : 0 ≤ cmax := (hc M.star).trans (hcmax M.star)
  have hw : Integrable w μ := waiting_integrable M p C lam
  have hright : Integrable (fun ω => (n : ℝ)*cmax*w ω + M.Clam c p.L 0 lam) μ :=
    (hw.const_mul _).add (integrable_const _)
  have hpoint : ∀ᵐ ω ∂μ, goodCost M p lam c ω ≤ (n : ℝ)*cmax*w ω + M.Clam c p.L 0 lam := by
    filter_upwards [actual_complete_ae M p C lam] with ω hcomplete
    by_cases hg : ω ∈ actualGoodEvent M p lam
    · have hpath := path_global_exact M p lam pathRewards (pathContacts p) ω hg
        (actualTau M p ω) hcomplete c cmax hc hstar hcmax
      simpa [goodCost, pathCost, hg, w, actualS] using hpath
    · simp only [goodCost, Set.indicator_of_notMem hg]
      exact add_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hcm0) (Nat.cast_nonneg _))
        (clam_zero_nonneg M c p.L hc lam)
  calc
    goodLoss M p C lam c ≤ ∫ ω, (n : ℝ)*cmax*w ω + M.Clam c p.L 0 lam ∂μ :=
      integral_mono_ae (goodCost_integrable M p C lam c cmax hc hcmax) hright hpoint
    _ = _ := by
      rw [integral_add (f := fun ω => (n : ℝ)*cmax*w ω)
          (g := fun _ => M.Clam c p.L 0 lam) (hw.const_mul _) (integrable_const _),
        integral_const_mul, integral_waiting M p C lam]
      simp [μ]

/-- The exact global branch expressed with the paper's truncated propagation moment. -/
theorem goodLoss_global_paper (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (c : Fin K → ℝ) (cmax : ℝ)
    (hc : ∀ k, 0 ≤ c k) (hstar : c M.star = 0) (hcmax : ∀ k, c k ≤ cmax) :
    goodLoss M p C lam c ≤
      (n : ℝ)*cmax*min (p.T : ℝ)
        (Pbeta (by have := p.hn; omega) C (holder p M.star) p.H (preparation M p) p.β) +
      M.Clam c p.L 0 lam := by
  have h1 := goodLoss_global_exact M p C lam c cmax hc hstar hcmax
  have h2 := mul_le_mul_of_nonneg_left (expectedWaiting_le_truncated_Pbeta M p C lam)
    (mul_nonneg (Nat.cast_nonneg n) ((hc M.star).trans (hcmax M.star)))
  linarith

/-- Exactly one failure budget for the common loss, independent of which good-event branch
will later be selected. This is derived from the actual finite-event probability theorem. -/
theorem weightedLoss_le_goodLoss_add_failure (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (c : Fin K → ℝ) (cmax : ℝ)
    (hc : ∀ k, 0 ≤ c k) (hcmax : ∀ k, c k ≤ cmax) :
    weightedLoss M p C lam c ≤ goodLoss M p C lam c + p.δ*((n : ℝ)*cmax*p.T) := by
  let μ := executionMeasure M p C lam
  let E := actualGoodEvent M p lam
  let B : ℝ := (n : ℝ)*cmax*p.T
  let bad : Path n → ℝ := Eᶜ.indicator (fun _ => B)
  have hcm0 : 0 ≤ cmax := (hc M.star).trans (hcmax M.star)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hE : MeasurableSet E := (executionFiltration n).le p.T _ (actualGoodEvent_measurable M p lam)
  have hgI := goodCost_integrable M p C lam c cmax hc hcmax
  have hbI : Integrable bad μ := (integrable_const B).indicator hE.compl
  have hpoint : ∀ ω, pathCost p c ω ≤ goodCost M p lam c ω + bad ω := by
    intro ω
    by_cases h : ω ∈ E
    · simp [goodCost, bad, E, h]
    · simpa [goodCost, bad, E, h] using pathCost_le p c cmax hcmax ω
  have hmono := integral_mono_ae (pathCost_integrable M p C lam c cmax hc hcmax)
    (hgI.add hbI) (Filter.Eventually.of_forall hpoint)
  have hbad : (∫ ω, bad ω ∂μ) = μ.real Eᶜ*B := by
    simp [bad, hE.compl, smul_eq_mul]
  have hδ : μ.real Eᶜ*B ≤ p.δ*B :=
    mul_le_mul_of_nonneg_right (actual_good_compl_le M p C lam) hB
  change (∫ ω, pathCost p c ω ∂μ) ≤
    ∫ ω, goodCost M p lam c ω + bad ω ∂μ at hmono
  rw [integral_add hgI hbI, hbad] at hmono
  change weightedLoss M p C lam c ≤ goodLoss M p C lam c + μ.real Eᶜ*B at hmono
  change weightedLoss M p C lam c ≤ goodLoss M p C lam c + p.δ*B
  linarith

end AnvBandit.GlobalRegret
