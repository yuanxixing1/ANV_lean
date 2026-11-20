import AnvBandit.ActualWaiting

/-! Exact original-law node arrivals and residual delay moments. All integrability and
moment identities are proved; no free expectation-linearity premise is accepted. -/
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators ENNReal
open Finset MeasureTheory ProbabilityTheory
namespace AnvBandit.ActualNodeMoments
open Execution ExecutionLaw ActualPropagation ActualWaiting
variable {n K : ℕ}

lemma sigmaAllE_toReal (R : ℕ → Fin n → Fin n) (i0 i : Fin n) :
    (sigmaAllE R {i0} i).toReal = (sigmaStep R i0 i : ℝ) := by
  by_cases h : ∃ t, i ∈ Inform R {i0} t
  · rw [sigmaAllE_of_nonempty h]
    simp only [ENNReal.toReal_natCast, sigmaAll, sigmaStep]
  · have he : {t | i ∈ Inform R {i0} t} = (∅ : Set ℕ) := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun ht => h ⟨t, ht⟩
    have ht : sigmaAllE R {i0} i = ⊤ := by
      unfold sigmaAllE
      simp only [show ∀ t, ¬ i ∈ Inform R {i0} t from fun t ht => h ⟨t,ht⟩, if_false, iInf_const]
    rw [ht]
    simp [sigmaStep, he]

lemma measurable_sigmaR (hd : 0 < n-1) (i0 i : Fin n) :
    Measurable (fun b => sigmaR hd b i0 i) := by
  have hs := ((measurable_sigmaAllE {i0} i).comp (measurable_unblock hd)).ennreal_toReal
  have hm := hs.min (measurable_tau_real hd i0)
  simpa only [Function.comp_def, sigmaAllE_toReal, sigmaR, sigma, Nat.cast_min] using hm

lemma integrable_tauR (hn : 2 ≤ n) (C : ContactMatrix n) (i0 : Fin n) :
    Integrable (fun b => tauR (by omega) b i0) (procMeasure C (n-1)) := by
  have h := integrable_toReal_of_lintegral_ne_top
    (ENNReal.measurable_ofReal.comp (measurable_tau_real (by omega) i0)).aemeasurable
    (lintegral_tauR_ne_top hn C (ReachData.ofIrreducible C.irreducible i0))
  simpa only [Function.comp_def, ENNReal.toReal_ofReal (Nat.cast_nonneg _), tauR] using h

lemma integrable_sigmaR (hn : 2 ≤ n) (C : ContactMatrix n) (i0 i : Fin n) :
    Integrable (fun b => sigmaR (by omega) b i0 i) (procMeasure C (n-1)) := by
  have h := integrable_toReal_of_lintegral_ne_top
    (ENNReal.measurable_ofReal.comp (measurable_sigmaR (by omega) i0 i)).aemeasurable
    (lintegral_sigmaR_ne_top hn C (ReachData.ofIrreducible C.irreducible i0) i)
  simpa only [Function.comp_def, ENNReal.toReal_ofReal (sigmaR_nonneg _ _ _ _)] using h

lemma integral_tauR_eq_mu1 (hn : 2 ≤ n) (C : ContactMatrix n) (i0 : Fin n) :
    (∫ b, tauR (by omega) b i0 ∂procMeasure C (n-1)) = mu1 (by omega) hn C i0 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun b => tauR_nonneg _ b i0))
    (measurable_tau_real (by omega) i0).stronglyMeasurable.aestronglyMeasurable]
  simp [mu1, EtauPow]

def actualSigma (M : DecayModel n K) (p : Params n K) (ω : Path n) (i : Fin n) : ℕ :=
  sigma (by have := p.hn; omega) (actualBlocks M p ω) (holder p M.star) i

def actualArrival (M : DecayModel n K) (p : Params n K) (ω : Path n) (i : Fin n) : ℕ :=
  p.phaseEnd (preparation M p + actualSigma M p ω i)

def arrivalSum (M : DecayModel n K) (p : Params n K) (ω : Path n) : ℝ :=
  ∑ i : Fin n, ((min p.T (actualArrival M p ω i) : ℕ) : ℝ)

def residualSum (M : DecayModel n K) (p : Params n K) (ω : Path n) : ℝ :=
  ∑ i : Fin n, ((actualTau M p ω - actualSigma M p ω i : ℕ) : ℝ)

lemma actualSigma_le_tau (M : DecayModel n K) (p : Params n K) (ω : Path n) (i : Fin n) :
    actualSigma M p ω i ≤ actualTau M p ω := sigma_le_tau _ _ _

lemma actual_arrived_ae (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) :
    ∀ᵐ ω ∂executionMeasure M p C lam, ∀ i : Fin n,
      i ∈ Inform (shiftedContacts M p (pathContacts p ω)) {holder p M.star}
        (actualSigma M p ω i) := by
  filter_upwards [actual_complete_ae M p C lam] with ω hω
  intro i
  have he : unblock (by have := p.hn; omega) (actualBlocks M p ω) =
      shiftedContacts M p (pathContacts p ω) := by
    rw [actualBlocks, unblock_groupContacts, phaseStream_eq_shifted]
  have hmem : i ∈ Inform (shiftedContacts M p (pathContacts p ω)) {holder p M.star}
      (actualTau M p ω) := by rw [hω]; exact mem_univ _
  have hle : sigmaStep (shiftedContacts M p (pathContacts p ω)) (holder p M.star) i ≤
      actualTau M p ω := Nat.sInf_le hmem
  change i ∈ Inform _ _ (min (sigmaStep (unblock _ (actualBlocks M p ω)) _ i) _)
  rw [he]
  change i ∈ Inform _ _ (min (sigmaStep _ _ i) (actualTau M p ω))
  rw [min_eq_left hle]
  exact Nat.sInf_mem (show {t : ℕ | i ∈ Inform (shiftedContacts M p (pathContacts p ω))
    {holder p M.star} t}.Nonempty from ⟨actualTau M p ω, hmem⟩)

lemma actualArrival_eq_Anode (M : DecayModel n K) (p : Params n K) (ω : Path n) (i : Fin n) :
    (actualArrival M p ω i : ℝ) = Anode (by have := p.hn; omega) p.H
      (preparation M p) p.β (actualBlocks M p ω) (holder p M.star) i := by
  simp [actualArrival, actualSigma, Params.phaseEnd, Anode, sigmaR, Nat.cast_add]

lemma actualBlocks_preserving (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) :
    MeasurePreserving (actualBlocks M p) (executionMeasure M p C lam) (procMeasure C (n-1)) :=
  ⟨measurable_actualBlocks M p, actualBlocks_law M p C lam⟩

lemma integral_actualBlocks (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2)
    (f : (ℕ → Fin (n-1) → Fin n → Fin n) → ℝ)
    (hf : AEStronglyMeasurable f (procMeasure C (n-1))) :
    (∫ ω, f (actualBlocks M p ω) ∂executionMeasure M p C lam) =
      ∫ b, f b ∂procMeasure C (n-1) := by
  rw [← actualBlocks_law M p C lam]
  exact (integral_map (measurable_actualBlocks M p).aemeasurable
    (by rwa [actualBlocks_law M p C lam])).symm

lemma actualTau_integrable (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) :
    Integrable (fun ω => (actualTau M p ω : ℝ)) (executionMeasure M p C lam) :=
by
  have h := (actualBlocks_preserving M p C lam).integrable_comp_of_integrable
    (integrable_tauR p.hn C (holder p M.star))
  simpa only [Function.comp_def, tauR, actualTau] using h

lemma actualSigma_integrable (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (i : Fin n) :
    Integrable (fun ω => (actualSigma M p ω i : ℝ)) (executionMeasure M p C lam) :=
by
  have h := (actualBlocks_preserving M p C lam).integrable_comp_of_integrable
    (integrable_sigmaR p.hn C (holder p M.star) i)
  simpa only [Function.comp_def, sigmaR, actualSigma] using h

lemma residualSum_eq_sub (M : DecayModel n K) (p : Params n K) (ω : Path n) :
    residualSum M p ω = (n : ℝ) * actualTau M p ω - ∑ i : Fin n, (actualSigma M p ω i : ℝ) := by
  simp only [residualSum, Nat.cast_sub (actualSigma_le_tau M p ω _), sum_sub_distrib]
  simp

lemma residualSum_integrable (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) :
    Integrable (residualSum M p) (executionMeasure M p C lam) := by
  have ht := (actualTau_integrable M p C lam).const_mul (n : ℝ)
  have hs := integrable_finset_sum univ (fun i _ => actualSigma_integrable M p C lam i)
  have he : residualSum M p = (fun ω => (n : ℝ) * actualTau M p ω) -
      (fun ω => ∑ i : Fin n, (actualSigma M p ω i : ℝ)) := by
    funext ω
    exact residualSum_eq_sub M p ω
  rw [he]
  exact ht.sub hs

lemma integral_residualSum (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) :
    (∫ ω, residualSum M p ω ∂executionMeasure M p C lam) =
      DP (by have := p.hn; omega) p.hn C (holder p M.star) := by
  have ht := actualTau_integrable M p C lam
  have hs := fun i => actualSigma_integrable M p C lam i
  simp only [residualSum_eq_sub]
  rw [integral_sub (ht.const_mul _) (integrable_finset_sum univ (fun i _ => hs i)),
    integral_const_mul, integral_finset_sum _ (fun i _ => hs i)]
  have htint : (∫ ω, (actualTau M p ω : ℝ) ∂executionMeasure M p C lam) =
      mu1 (by have := p.hn; omega) p.hn C (holder p M.star) := by
    change (∫ ω, tauR (by have := p.hn; omega) (actualBlocks M p ω) (holder p M.star)
      ∂executionMeasure M p C lam) = _
    exact (integral_actualBlocks M p C lam
      (fun b => tauR (by have := p.hn; omega) b (holder p M.star))
      (measurable_tau_real (by have := p.hn; omega) (holder p M.star)).stronglyMeasurable.aestronglyMeasurable).trans
        (integral_tauR_eq_mu1 p.hn C _)
  rw [htint]
  unfold DP M1
  congr 1
  apply sum_congr rfl
  intro i _
  change (∫ ω, sigmaR (by have := p.hn; omega) (actualBlocks M p ω) (holder p M.star) i
    ∂executionMeasure M p C lam) = _
  refine (integral_actualBlocks M p C lam
    (fun b => sigmaR (by have := p.hn; omega) b (holder p M.star) i)
    (measurable_sigmaR (by have := p.hn; omega) (holder p M.star) i).stronglyMeasurable.aestronglyMeasurable).trans ?_
  exact integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun b => sigmaR_nonneg (by have := p.hn; omega) b (holder p M.star) i))
    (measurable_sigmaR (by have := p.hn; omega) (holder p M.star) i).stronglyMeasurable.aestronglyMeasurable

lemma measurable_Anode (hd : 0 < n-1) (H r β : ℝ) (i0 i : Fin n) :
    Measurable (fun b => Anode hd H r β b i0 i) := by
  unfold Anode
  exact measurable_const.mul
    ((measurable_of_countable (fun x : ℕ => (x : ℝ))).comp (Nat.measurable_ceil.comp
      ((measurable_const.add (measurable_sigmaR hd i0 i)).pow_const β)))

lemma arrival_each_measurable (M : DecayModel n K) (p : Params n K) (i : Fin n) :
    Measurable (fun ω : Path n => ((min p.T (actualArrival M p ω i) : ℕ) : ℝ)) := by
  have hm := (measurable_Anode (by have := p.hn; omega) p.H (preparation M p) p.β
    (holder p M.star) i).comp (measurable_actualBlocks M p)
  have he : (fun ω : Path n => (actualArrival M p ω i : ℝ)) =
      (fun ω => Anode (by have := p.hn; omega) p.H (preparation M p) p.β
        (actualBlocks M p ω) (holder p M.star) i) := funext (fun ω => actualArrival_eq_Anode M p ω i)
  simp only [Function.comp_def] at hm
  rw [← he] at hm
  simpa only [Nat.cast_min] using measurable_const.min hm

lemma arrival_each_integrable (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (i : Fin n) :
    Integrable (fun ω : Path n => ((min p.T (actualArrival M p ω i) : ℕ) : ℝ))
      (executionMeasure M p C lam) := by
  apply Integrable.of_bound (arrival_each_measurable M p i).stronglyMeasurable.aestronglyMeasurable
    (p.T : ℝ)
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact Nat.cast_le.mpr (Nat.min_le_left _ _)

lemma arrivalSum_integrable (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) :
    Integrable (arrivalSum M p) (executionMeasure M p C lam) :=
  integrable_finset_sum univ (fun i _ => arrival_each_integrable M p C lam i)

lemma integral_arrivalSum (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) :
    (∫ ω, arrivalSum M p ω ∂executionMeasure M p C lam) =
      Abeta (by have := p.hn; omega) C (holder p M.star) p.H (preparation M p) p.β p.T := by
  unfold arrivalSum Abeta
  rw [integral_finset_sum _ (fun i _ => arrival_each_integrable M p C lam i)]
  apply sum_congr rfl
  intro i _
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun ω => Nat.cast_nonneg _))
    (arrival_each_measurable M p i).stronglyMeasurable.aestronglyMeasurable]
  congr 1
  rw [← actualBlocks_law M p C lam]
  let f : (ℕ → Fin (n-1) → Fin n → Fin n) → ℝ≥0∞ := fun b =>
    ENNReal.ofReal (min (p.T : ℝ) (Anode (by have := p.hn; omega)
      (p.H : ℝ) (preparation M p : ℝ) p.β b (holder p M.star) i))
  have hf : Measurable f := ENNReal.measurable_ofReal.comp
    (measurable_const.min (measurable_Anode _ _ _ _ _ _))
  change _ = ∫⁻ b, f b ∂(executionMeasure M p C lam).map (actualBlocks M p)
  rw [lintegral_map hf (measurable_actualBlocks M p)]
  apply lintegral_congr
  intro ω
  dsimp [f]
  rw [← actualArrival_eq_Anode]
  simp [Nat.cast_min]

end AnvBandit.ActualNodeMoments
