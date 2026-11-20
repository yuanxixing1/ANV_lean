import AnvBandit.ExecutionKernel
import AnvBandit.ExecutionPhases

/-!
# The finite observed law, without fictitious contact assumptions

Inactive contact slots are deterministically erased. Coordinate zero is only the fixed dummy;
positive coordinates retain a contact exactly at a nonterminal nominal phase endpoint.
The projection leaves every actual execution state unchanged. Thus the full auxiliary product
construction is a convenience, not a restriction on the paper's observed probability law.
-/
noncomputable section
open scoped BigOperators Classical
open Finset MeasureTheory ProbabilityTheory Preorder
set_option maxHeartbeats 1000000
namespace AnvBandit.ExecutionLaw
variable {n K : ℕ}

/-- Retain coordinate zero (the dummy) and genuine nonterminal phase endpoints only. -/
def retainedContact (p : Execution.Params n K) (r : ℕ) : Prop :=
  ∃ ℓ, p.phaseEnd ℓ = r ∧ r < p.T

/-- A nonobserved contact is not randomized or constrained: it is simply absent, encoded by id. -/
def maskOutcome (p : Execution.Params n K) (r : ℕ) (o : Outcome n) : Outcome n :=
  (o.1, if retainedContact p r then o.2 else id)

def observedPath (p : Execution.Params n K) (ω : Path n) : Path n :=
  fun r => maskOutcome p r (ω r)

def observedPrefix (p : Execution.Params n K) (t : ℕ) (h : Prefix n t) : Prefix n t :=
  fun r => maskOutcome p r.val (h r)

@[simp] theorem observedPath_rewards (p : Execution.Params n K) (ω : Path n) :
    pathRewards (observedPath p ω) = pathRewards ω := rfl

@[simp] theorem observedPath_prefix (p : Execution.Params n K) (t : ℕ) (ω : Path n) :
    frestrictLe t (observedPath p ω) = observedPrefix p t (frestrictLe t ω) := rfl

/-- No state, action, count, or empirical statistic can see an erased contact. -/
theorem observedPath_run (p : Execution.Params n K) (ω : Path n) (t : ℕ) :
    Execution.run p (realTape (pathRewards (observedPath p ω)))
        (pathContacts p (observedPath p ω)) t =
      Execution.run p (realTape (pathRewards ω)) (pathContacts p ω) t := by
  apply Execution.run_congr
  · intro s hs
    rfl
  · intro ℓ hℓ hT
    simp only [pathContacts, observedPath, maskOutcome]
    rw [if_pos (show retainedContact p (p.phaseEnd ℓ) from ⟨ℓ, rfl, hT⟩)]

/-- The erasure criterion is exactly actual communication, not a restricted schedule. -/
theorem retainedContact_iff_communicates (p : Execution.Params n K) (ω : Path n)
    (t : ℕ) (ht : t < p.T) :
    retainedContact p (t+1) ↔ Execution.communicates p t
      (Execution.run p (realTape (pathRewards ω)) (pathContacts p ω) t) := by
  constructor
  · rintro ⟨ℓ, he, hT⟩
    have hℓ : 1 ≤ ℓ := by
      by_contra h
      have : ℓ = 0 := by omega
      simp [this] at he
    have hp := Execution.phase_before_boundary p (realTape (pathRewards ω))
      (pathContacts p ω) ℓ hℓ (by omega)
    have he' : p.phaseEnd ℓ - 1 = t := by omega
    rw [he'] at hp
    exact ⟨by rw [hp, he], hT⟩
  · intro hc
    exact ⟨_, hc.1.symm, hc.2⟩

/-- Extend a finite prefix only to use the deterministic replay identity. -/
def extendPrefix (t : ℕ) (h : Prefix n t) : Path n :=
  fun r => if hr : r ≤ t then h ⟨r, Finset.mem_Iic.mpr hr⟩ else default

@[simp] theorem extendPrefix_restrict (t : ℕ) (h : Prefix n t) :
    frestrictLe t (extendPrefix t h) = h := by
  funext r
  simp [extendPrefix, frestrictLe, Finset.mem_Iic.mp r.property]

/-- The transition state is invariant under deletion of all unused contact coordinates. -/
theorem observedPrefix_replay (p : Execution.Params n K) (t : ℕ) (h : Prefix n t) :
    (replay p (prefixHistory t (observedPrefix p t h))).2 =
      (replay p (prefixHistory t h)).2 := by
  have he := observedPath_run p (extendPrefix t h) t
  rw [← prefixHistory_frestrict, ← prefixHistory_frestrict] at he
  simpa only [observedPath_prefix, extendPrefix_restrict] using he

/-- The original observed one-step law: Bernoulli product, and only actual requests randomized. -/
def observedDistribution (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (t : ℕ) (s : Execution.State n K) : PMF (Outcome n) :=
  (outcomeDistribution M p C lam s).map (maskOutcome p (t+1))

theorem observedDistribution_requested (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (t : ℕ) (s : Execution.State n K)
    (hr : retainedContact p (t+1)) :
    observedDistribution M p C lam t s = outcomeDistribution M p C lam s := by
  have he : maskOutcome p (t+1) = id := by
    funext o
    simp [maskOutcome, hr]
  simp [observedDistribution, he, PMF.map_id]

theorem observedDistribution_unrequested (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (t : ℕ) (s : Execution.State n K)
    (hr : ¬ retainedContact p (t+1)) :
    observedDistribution M p C lam t s =
      (rewardDistribution M p lam s).map (fun x => (x, id)) := by
  have he : maskOutcome p (t+1) =
      (fun x : Fin n → Bool => (x, (id : Fin n → Fin n))) ∘ Prod.fst := by
    funext o
    simp [maskOutcome, hr]
  rw [observedDistribution, he, ← PMF.map_comp, outcomeDistribution_map_fst]

/-- Exact projected transition kernel on observed prefixes. -/
def observedKernel (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (t : ℕ) : Kernel (Prefix n t) (Outcome n) :=
  Kernel.ofFunOfCountable fun h =>
    (observedDistribution M p C lam t (replay p (prefixHistory t h)).2).toMeasure

instance observedKernel_markov (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (t : ℕ) :
    IsMarkovKernel (observedKernel M p C lam t) := by
  constructor
  intro h
  change IsProbabilityMeasure
    (observedDistribution M p C lam t (replay p (prefixHistory t h)).2).toMeasure
  infer_instance

/-- Pushforward of the full transition uses only the projected history. -/
theorem observedKernel_factor (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (t : ℕ) (h : Prefix n t) :
    (executionKernel M p C lam t h).map (maskOutcome p (t+1)) =
      observedKernel M p C lam t (observedPrefix p t h) := by
  change (outcomeDistribution M p C lam (replay p (prefixHistory t h)).2).toMeasure.map _ =
    (observedDistribution M p C lam t
      (replay p (prefixHistory t (observedPrefix p t h))).2).toMeasure
  rw [observedPrefix_replay]
  exact PMF.toMeasure_map _ _ (measurable_of_countable _)

/-- A finite/countable kernel pushforward lemma. The output kernel depends on the
projected input only; no conditional-independence assumption is added by forgetting data. -/
theorem map_compProd_factor {A B A' B' : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace A'] [MeasurableSpace B']
    [Countable A] [Countable B] [Countable A'] [Countable B']
    [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    [MeasurableSingletonClass A'] [MeasurableSingletonClass B']
    (μ : Measure A) [SFinite μ] (κ : Kernel A B) [IsSFiniteKernel κ]
    (η : Kernel A' B') [IsSFiniteKernel η] (f : A → A') (g : B → B')
    (h : ∀ a, (κ a).map g = η (f a)) :
    (μ ⊗ₘ κ).map (Prod.map f g) = (μ.map f) ⊗ₘ η := by
  ext s hs
  rw [Measure.map_apply (measurable_of_countable _) hs,
    Measure.compProd_apply ((measurable_of_countable _ ) hs),
    Measure.compProd_apply hs,
    lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  apply lintegral_congr
  intro a
  rw [← h a, Measure.map_apply (measurable_of_countable _)
    ((measurable_of_countable _) hs)]
  rfl

/-- Conditional contact law at a real request; otherwise the deterministic absence code. -/
def observedContactDistribution (p : Execution.Params n K) (C : ContactMatrix n) (t : ℕ) :
    PMF (Fin n → Fin n) :=
  (contactDistribution C).map (fun j => if retainedContact p (t+1) then j else id)

theorem observedContactDistribution_requested (p : Execution.Params n K)
    (C : ContactMatrix n) (t : ℕ) (hr : retainedContact p (t+1)) :
    observedContactDistribution p C t = contactDistribution C := by
  simp only [observedContactDistribution, if_pos hr]
  exact PMF.map_id _

theorem observedContactDistribution_unrequested (p : Execution.Params n K)
    (C : ContactMatrix n) (t : ℕ) (hr : ¬retainedContact p (t+1)) :
    observedContactDistribution p C t = PMF.pure id := by
  simp only [observedContactDistribution, if_neg hr]
  exact PMF.map_const (contactDistribution C) id

theorem sectR_const_eq {A B D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace D] (m : Measure D) (a : A) :
    Kernel.sectR (Kernel.const (A × B) m) a = Kernel.const B m := by
  ext b : 1
  rfl

/-- Reward first, then the conditional requested-contact product. -/
theorem observedKernel_split (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (t : ℕ) :
    observedKernel M p C lam t = rewardKernel M p lam t ⊗ₖ
      Kernel.const (Prefix n t × (Fin n → Bool))
        (observedContactDistribution p C t).toMeasure := by
  ext h : 1
  have he := congrArg (fun κ : Kernel (Prefix n t) (Outcome n) => κ h)
    (executionKernel_split M p C lam t)
  have hm := map_compProd_factor ((rewardKernel M p lam t) h)
    (Kernel.const (Fin n → Bool) (contactDistribution C).toMeasure)
    (Kernel.const (Fin n → Bool) (observedContactDistribution p C t).toMeasure)
    id (fun j => if retainedContact p (t+1) then j else id)
    (fun _ => PMF.toMeasure_map _ _ (measurable_of_countable _))
  change ((outcomeDistribution M p C lam (replay p (prefixHistory t h)).2).map
    (maskOutcome p (t+1))).toMeasure = _
  rw [← PMF.toMeasure_map _ _ (measurable_of_countable _)]
  change ((executionKernel M p C lam t) h).map _ = _
  rw [he]
  have hf : maskOutcome p (t+1) =
      Prod.map id (fun j : Fin n → Fin n => if retainedContact p (t+1) then j else id) := by
    funext o
    rfl
  rw [hf]
  simpa only [Measure.map_id, Kernel.compProd_apply_eq_compProd_sectR,
    Kernel.const_apply, sectR_const_eq] using hm

/-- Original sequential conditional laws imply the combined observed transition. The contact
premise is conditioned on the CURRENT rewards as well as the previous completed prefix. -/
theorem observed_joint_of_sequential (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (ν : Measure (Path n)) [IsProbabilityMeasure ν]
    (t : ℕ)
    (hx : condDistrib (fun ω : Path n => (ω (t+1)).1) (frestrictLe t) ν
      =ᵐ[ν.map (frestrictLe t)] rewardKernel M p lam t)
    (hj : condDistrib (fun ω : Path n => (ω (t+1)).2)
      (fun ω : Path n => (frestrictLe t ω, (ω (t+1)).1)) ν
      =ᵐ[ν.map (fun ω => (frestrictLe t ω, (ω (t+1)).1))]
      Kernel.const (Prefix n t × (Fin n → Bool))
        (observedContactDistribution p C t).toMeasure) :
    condDistrib (fun ω : Path n => ω (t+1)) (frestrictLe t) ν
      =ᵐ[ν.map (frestrictLe t)] observedKernel M p C lam t := by
  have hx' := (condDistrib_ae_eq_iff_measure_eq_compProd (μ := ν)
    (mβ := (inferInstance : MeasurableSpace (Prefix n t)))
    (Y := fun ω : Path n => (ω (t+1)).1) (frestrictLe t)
    (measurable_fst.comp (measurable_pi_apply (t+1))).aemeasurable
    (rewardKernel M p lam t)).mp hx
  have hj' := (condDistrib_ae_eq_iff_measure_eq_compProd (μ := ν)
    (mβ := (inferInstance : MeasurableSpace (Prefix n t × (Fin n → Bool))))
    (Y := fun ω : Path n => (ω (t+1)).2)
    (fun ω : Path n => (frestrictLe t ω, (ω (t+1)).1))
    (measurable_snd.comp (measurable_pi_apply (t+1))).aemeasurable
    (Kernel.const (Prefix n t × (Fin n → Bool))
      (observedContactDistribution p C t).toMeasure)).mp hj
  rw [hx'] at hj'
  have ha := congrArg (fun m : Measure ((Prefix n t × (Fin n → Bool)) × (Fin n → Fin n)) =>
    m.map MeasurableEquiv.prodAssoc) hj'
  rw [Measure.map_map (by fun_prop) (by fun_prop), Measure.compProd_assoc',
    ← observedKernel_split] at ha
  exact (condDistrib_ae_eq_iff_measure_eq_compProd (μ := ν)
    (mβ := (inferInstance : MeasurableSpace (Prefix n t)))
    (Y := fun ω : Path n => ω (t+1)) (frestrictLe t)
    (measurable_pi_apply (t+1)).aemeasurable (observedKernel M p C lam t)).mpr ha

/-- Unrequested slots require only the representation invariant 'absent = id', not a
random-contact model. Requested slots use precisely the original after-reward joint row law. -/
theorem observed_transition_of_original (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (ν : Measure (Path n)) [IsProbabilityMeasure ν]
    (t : ℕ)
    (hx : condDistrib (fun ω : Path n => (ω (t+1)).1) (frestrictLe t) ν
      =ᵐ[ν.map (frestrictLe t)] rewardKernel M p lam t)
    (hj : retainedContact p (t+1) →
      condDistrib (fun ω : Path n => (ω (t+1)).2)
        (fun ω : Path n => (frestrictLe t ω, (ω (t+1)).1)) ν
        =ᵐ[ν.map (fun ω => (frestrictLe t ω, (ω (t+1)).1))]
        Kernel.const (Prefix n t × (Fin n → Bool)) (contactDistribution C).toMeasure)
    (habsent : ¬retainedContact p (t+1) → ∀ᵐ ω ∂ν, (ω (t+1)).2 = id) :
    condDistrib (fun ω : Path n => ω (t+1)) (frestrictLe t) ν
      =ᵐ[ν.map (frestrictLe t)] observedKernel M p C lam t := by
  apply observed_joint_of_sequential M p C lam ν t hx
  by_cases hr : retainedContact p (t+1)
  · rw [observedContactDistribution_requested p C t hr]
    exact hj hr
  · rw [observedContactDistribution_unrequested p C t hr, PMF.toMeasure_pure]
    rw [condDistrib_congr_left (habsent hr)]
    have hh := condDistrib_const (μ := ν)
      (mβ := (inferInstance : MeasurableSpace (Prefix n t × (Fin n → Bool))))
      (fun ω : Path n => (frestrictLe t ω, (ω (t+1)).1)) (id : Fin n → Fin n)
    filter_upwards [hh] with h hh
    exact hh

theorem observedPath_measurable (p : Execution.Params n K) : Measurable (observedPath p) := by
  apply measurable_pi_lambda
  intro r
  exact (measurable_of_countable (maskOutcome p r)).comp (measurable_pi_apply r)

/-- The observed canonical law is the marginal of the auxiliary construction. -/
def observedMeasure (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) : Measure (Path n) :=
  (executionMeasure M p C lam).map (observedPath p)

instance observedMeasure_probability (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) : IsProbabilityMeasure (observedMeasure M p C lam) := by
  unfold observedMeasure
  exact Measure.isProbabilityMeasure_map (observedPath_measurable p).aemeasurable

/-- Projection of the full joint conditional law to exactly the observed sigma algebra. -/
theorem observed_joint_law (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (t : ℕ) :
    (observedMeasure M p C lam).map (fun ω => (frestrictLe t ω, ω (t+1))) =
      ((observedMeasure M p C lam).map (frestrictLe t)) ⊗ₘ observedKernel M p C lam t := by
  have hj := (condDistrib_ae_eq_iff_measure_eq_compProd (μ := executionMeasure M p C lam)
    (mβ := (inferInstance : MeasurableSpace (Prefix n t)))
    (Y := fun ω : Path n => ω (t+1)) (frestrictLe t)
    (measurable_pi_apply (t+1)).aemeasurable (executionKernel M p C lam t)).mp
      (conditional_outcome_law M p C lam t)
  have hm := congrArg (fun ν : Measure (Prefix n t × Outcome n) =>
    ν.map (Prod.map (observedPrefix p t) (maskOutcome p (t+1)))) hj
  rw [map_compProd_factor _ _ (observedKernel M p C lam t) _ _
    (observedKernel_factor M p C lam t)] at hm
  simp only [observedMeasure, Measure.map_map
    (measurable_frestrictLe t) (observedPath_measurable p)]
  rw [Measure.map_map (by fun_prop) (observedPath_measurable p)]
  rw [Measure.map_map (measurable_of_countable _) (by fun_prop),
    Measure.map_map (measurable_of_countable (observedPrefix p t)) (measurable_frestrictLe t)] at hm
  exact hm

theorem observed_conditional_law (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (t : ℕ) :
    condDistrib (fun ω : Path n => ω (t+1)) (frestrictLe t)
      (observedMeasure M p C lam) =ᵐ[(observedMeasure M p C lam).map (frestrictLe t)]
      observedKernel M p C lam t := by
  exact (condDistrib_ae_eq_iff_measure_eq_compProd (μ := observedMeasure M p C lam)
    (mβ := (inferInstance : MeasurableSpace (Prefix n t)))
    (Y := fun ω : Path n => ω (t+1)) (frestrictLe t)
    (measurable_pi_apply (t+1)).aemeasurable (observedKernel M p C lam t)).mpr
    (observed_joint_law M p C lam t)

/-- Original finite observed-law uniqueness. Inactive contacts are deterministically absent;
no product law is imposed on unobserved auxiliary contacts, nor any law beyond the horizon.
The only stochastic premise is the original joint one-round reward/request transition law. -/
theorem finite_observed_law_unique (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (ν : Measure (Path n)) [IsProbabilityMeasure ν]
    (hzero : ν.map (frestrictLe 0) = (observedMeasure M p C lam).map (frestrictLe 0))
    (hlaw : ∀ t < p.T,
      condDistrib (fun ω : Path n => ω (t+1)) (frestrictLe t) ν
        =ᵐ[ν.map (frestrictLe t)] observedKernel M p C lam t) :
    ∀ t ≤ p.T, ν.map (frestrictLe t) = (observedMeasure M p C lam).map (frestrictLe t) := by
  intro t ht
  induction t with
  | zero => exact hzero
  | succ t ih =>
    have ih := ih (by omega)
    have emb : MeasurableEmbedding (splitPrefix (n := n) t) :=
      ⟨splitPrefix_injective t, measurable_of_countable _,
        fun s hs => Set.to_countable _ |>.measurableSet⟩
    apply emb.map_injective
    rw [Measure.map_map (measurable_of_countable (splitPrefix (n := n) t)) (measurable_frestrictLe (t+1)),
        Measure.map_map (measurable_of_countable (splitPrefix (n := n) t)) (measurable_frestrictLe (t+1))]
    change ν.map (fun ω => (frestrictLe t ω, ω (t+1))) =
      (observedMeasure M p C lam).map (fun ω => (frestrictLe t ω, ω (t+1)))
    rw [(condDistrib_ae_eq_iff_measure_eq_compProd (frestrictLe t)
      (measurable_pi_apply (t+1)).aemeasurable (observedKernel M p C lam t)).mp
        (hlaw t (by omega)), observed_joint_law, ih]

/-- Every measurable finite-prefix statistic insensitive to unused contacts has exactly the
canonical law. This transfers arbitrary observed executions, not merely a chosen random seed model. -/
theorem finite_observed_statistic_transfer {A : Type*} [MeasurableSpace A]
    (M : DecayModel n K) (p : Execution.Params n K) (C : ContactMatrix n) (lam : Fin 2)
    (ν : Measure (Path n)) [IsProbabilityMeasure ν]
    (hzero : ν.map (frestrictLe 0) = (observedMeasure M p C lam).map (frestrictLe 0))
    (hlaw : ∀ t < p.T,
      condDistrib (fun ω : Path n => ω (t+1)) (frestrictLe t) ν
        =ᵐ[ν.map (frestrictLe t)] observedKernel M p C lam t)
    (t : ℕ) (ht : t ≤ p.T) (f : Prefix n t → A)
    (hf : ∀ h, f (observedPrefix p t h) = f h) :
    ν.map (fun ω => f (frestrictLe t ω)) =
      (executionMeasure M p C lam).map (fun ω => f (frestrictLe t ω)) := by
  have he := congrArg (fun m : Measure (Prefix n t) => m.map f)
    (finite_observed_law_unique M p C lam ν hzero hlaw t ht)
  rw [Measure.map_map (measurable_of_countable f) (measurable_frestrictLe t),
    Measure.map_map (measurable_of_countable f) (measurable_frestrictLe t)] at he
  rw [observedMeasure, Measure.map_map
    ((measurable_of_countable f).comp (measurable_frestrictLe t))
    (observedPath_measurable p)] at he
  have hfun : (f ∘ frestrictLe t) ∘ observedPath p = f ∘ frestrictLe t := by
    funext ω
    exact hf (frestrictLe t ω)
  rw [hfun] at he
  exact he

/-- In particular the whole actual state (all nodes, counts, rewards and phase) has the
same finite law in every original observed execution. -/
theorem finite_execution_state_transfer [MeasurableSpace (Execution.State n K)]
    (M : DecayModel n K) (p : Execution.Params n K) (C : ContactMatrix n) (lam : Fin 2)
    (ν : Measure (Path n)) [IsProbabilityMeasure ν]
    (hzero : ν.map (frestrictLe 0) = (observedMeasure M p C lam).map (frestrictLe 0))
    (hlaw : ∀ t < p.T,
      condDistrib (fun ω : Path n => ω (t+1)) (frestrictLe t) ν
        =ᵐ[ν.map (frestrictLe t)] observedKernel M p C lam t)
    (t : ℕ) (ht : t ≤ p.T) :
    ν.map (fun ω => Execution.run p (realTape (pathRewards ω)) (pathContacts p ω) t) =
      (executionMeasure M p C lam).map
        (fun ω => Execution.run p (realTape (pathRewards ω)) (pathContacts p ω) t) := by
  simpa only [prefixHistory_frestrict] using
    (finite_observed_statistic_transfer M p C lam ν hzero hlaw t ht
      (fun h => (replay p (prefixHistory t h)).2) (observedPrefix_replay p t))

/-- Coverage entry: arbitrary finite observed laws satisfying the paper's sequential laws
produce the same actual state distribution as the canonical construction. The zero-prefix
premise fixes only an unused deterministic initial dummy. The absence premise is the encoding
of 'no request', and imposes no law at all on unused auxiliary contacts. -/
theorem finite_original_execution_state_law [MeasurableSpace (Execution.State n K)]
    (M : DecayModel n K) (p : Execution.Params n K) (C : ContactMatrix n) (lam : Fin 2)
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
    (t : ℕ) (ht : t ≤ p.T) :
    ν.map (fun ω => Execution.run p (realTape (pathRewards ω)) (pathContacts p ω) t) =
      (executionMeasure M p C lam).map
        (fun ω => Execution.run p (realTape (pathRewards ω)) (pathContacts p ω) t) := by
  apply finite_execution_state_transfer M p C lam ν hzero _ t ht
  intro r hr
  exact observed_transition_of_original M p C lam ν r (hx r hr) (hj r hr) (habsent r hr)

/-- Full joint finite-prefix coverage, directly from the original sequential laws. This is
stronger than equality of one-time state marginals: every finite observed path event has the
same probability. No transition beyond T or unrequested auxiliary contact law is required. -/
theorem finite_original_observed_law
    (M : DecayModel n K) (p : Execution.Params n K) (C : ContactMatrix n) (lam : Fin 2)
    (ν : Measure (Path n)) [IsProbabilityMeasure ν]
    (hzero : ν.map (frestrictLe 0) = (observedMeasure M p C lam).map (frestrictLe 0))
    (hx : ∀ t < p.T, condDistrib (fun ω : Path n => (ω (t+1)).1) (frestrictLe t) ν
      =ᵐ[ν.map (frestrictLe t)] rewardKernel M p lam t)
    (hj : ∀ t < p.T, retainedContact p (t+1) →
      condDistrib (fun ω : Path n => (ω (t+1)).2)
        (fun ω : Path n => (frestrictLe t ω, (ω (t+1)).1)) ν
        =ᵐ[ν.map (fun ω => (frestrictLe t ω, (ω (t+1)).1))]
        Kernel.const (Prefix n t × (Fin n → Bool)) (contactDistribution C).toMeasure)
    (habsent : ∀ t < p.T, ¬retainedContact p (t+1) → ∀ᵐ ω ∂ν, (ω (t+1)).2 = id) :
    ∀ t ≤ p.T, ν.map (frestrictLe t) = (observedMeasure M p C lam).map (frestrictLe t) := by
  apply finite_observed_law_unique M p C lam ν hzero
  intro r hr
  exact observed_transition_of_original M p C lam ν r (hx r hr) (hj r hr) (habsent r hr)

end AnvBandit.ExecutionLaw
