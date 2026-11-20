import AnvBandit.ExecutionLaw
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Process.Filtration

/-!
# Standard execution law from fresh finite-state kernels

Coordinate zero is an unused deterministic dummy. Coordinate `t+1` supplies the round `t`
reward and a fresh contact vector. A contact is read only at a nonterminal phase boundary.
Unused contact coordinates and post-horizon coordinates are auxiliary randomness, not extra
observations or assumptions on the algorithm. The pre-round filtration contains no future
coordinate. The Ionescu–Tulcea construction supplies the complete joint conditional law.
-/
noncomputable section
open scoped BigOperators Classical
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Finset MeasureTheory ProbabilityTheory Preorder

namespace AnvBandit.ExecutionLaw

variable {n K : ℕ}

abbrev Path (n : ℕ) := ℕ → Outcome n
abbrev Prefix (n t : ℕ) := (i : Finset.Iic t) → Outcome n

instance contactVector_nonempty : Nonempty (Fin n → Fin n) := ⟨id⟩
instance outcome_inhabited : Inhabited (Outcome n) := ⟨((fun _ => false), id)⟩

/-- The actual completed outcomes in an initial segment; the dummy is omitted. -/
def prefixHistory (t : ℕ) (h : Prefix n t) : List (Outcome n) :=
  List.ofFn (fun i : Fin t => h ⟨i.val + 1, by simp only [Finset.mem_Iic]; omega⟩)

/-- Full joint one-step law, using only the already completed history. -/
def executionKernel (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (t : ℕ) : Kernel (Prefix n t) (Outcome n) :=
  Kernel.ofFunOfCountable fun h =>
    (outcomeDistribution M p C lam (replay p (prefixHistory t h)).2).toMeasure

instance executionKernel_markov (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (t : ℕ) :
    IsMarkovKernel (executionKernel M p C lam t) := by
  constructor
  intro h
  change IsProbabilityMeasure
    (outcomeDistribution M p C lam (replay p (prefixHistory t h)).2).toMeasure
  infer_instance

/-- Canonical law, constructed for every original model and contact matrix. -/
def executionMeasure (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) : Measure (Path n) :=
  Kernel.trajMeasure (Measure.dirac ((fun _ => false), id)) (executionKernel M p C lam)

instance executionMeasure_probability (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) :
    IsProbabilityMeasure (executionMeasure M p C lam) := by
  unfold executionMeasure
  infer_instance

/-- Pre-round information. The dummy has no operational role. -/
abbrev executionFiltration (n : ℕ) : Filtration ℕ (inferInstance : MeasurableSpace (Path n)) :=
  Filtration.piLE

/-- Bool reward tape read by the actual execution. -/
def pathRewards (ω : Path n) (t : ℕ) : Fin n → Bool := (ω (t + 1)).1

/-- Phase-indexed contact tape. A terminal contact is never used by the execution. -/
def pathContacts (p : Execution.Params n K) (ω : Path n) (ℓ : ℕ) : Fin n → Fin n :=
  (ω (p.phaseEnd ℓ)).2

/-- The full reward/contact vector has the prescribed joint conditional kernel.
This theorem is the nonempty-law construction, not an assumed concentration property. -/
theorem conditional_outcome_law (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (t : ℕ) :
    condDistrib (fun ω : Path n => ω (t + 1)) (frestrictLe t)
        (executionMeasure M p C lam)
      =ᵐ[(executionMeasure M p C lam).map (frestrictLe t)]
        executionKernel M p C lam t := by
  exact Kernel.condDistrib_trajMeasure

/-- Kernel history is precisely the actual execution history. -/
theorem prefixHistory_frestrict (p : Execution.Params n K) (ω : Path n) (t : ℕ) :
    (replay p (prefixHistory t (frestrictLe t ω))).2 =
      Execution.run p (realTape (pathRewards ω)) (pathContacts p ω) t := by
  exact replay_eq_run p ω t



/-- The whole finite execution state is determined measurably by the completed prefix.
The codomain may even use the discrete sigma-algebra: at a fixed finite round only finitely
many states are reachable from Boolean reward/contact prefixes. -/
theorem execution_measurable (p : Execution.Params n K) (t : ℕ) :
    Measurable[executionFiltration n t, ⊤]
      (fun ω : Path n => Execution.run p (realTape (pathRewards ω)) (pathContacts p ω) t) := by
  letI : MeasurableSpace (Execution.State n K) := ⊤
  rw [Filtration.piLE_eq_comap_frestrictLe]
  have hm : Measurable[(inferInstance : MeasurableSpace (Prefix n t)), ⊤]
      (fun h : Prefix n t => (replay p (prefixHistory t h)).2) := measurable_of_countable _
  have h := hm.comp (comap_measurable (m := (inferInstance : MeasurableSpace (Prefix n t)))
        (frestrictLe t : Path n → Prefix n t))
  convert h using 1
  funext ω
  simp only [Function.comp_apply]
  rw [prefixHistory_frestrict]

/-- The actual chosen action is measurable before the next reward vector is generated. -/
theorem action_predictable (p : Execution.Params n K) (t : ℕ) (i : Fin n) :
    Measurable[executionFiltration n t]
      (fun ω : Path n => Execution.I p (realTape (pathRewards ω)) (pathContacts p ω) t i) := by
  rw [Filtration.piLE_eq_comap_frestrictLe]
  have h := (measurable_of_countable
    (fun h : Prefix n t => Execution.actions p (replay p (prefixHistory t h)).2 i)).comp
      (comap_measurable (m := (inferInstance : MeasurableSpace (Prefix n t)))
        (frestrictLe t : Path n → Prefix n t))
  convert h using 1
  funext ω
  simp only [Function.comp_apply]
  rw [prefixHistory_frestrict]
  rfl

/-- Conditional means are history-dependent predictable quantities, not fixed pull streams. -/
theorem actualMean_predictable (M : DecayModel n K) (p : Execution.Params n K)
    (lam : Fin 2) (t : ℕ) (i : Fin n) :
    StronglyMeasurable[executionFiltration n t]
      (fun ω : Path n => actualMean M p lam (pathRewards ω) (pathContacts p ω) t i) := by
  apply Measurable.stronglyMeasurable
  rw [Filtration.piLE_eq_comap_frestrictLe]
  have h := (measurable_of_countable
    (fun h : Prefix n t => stateMean M p lam (replay p (prefixHistory t h)).2 i)).comp
      (comap_measurable (m := (inferInstance : MeasurableSpace (Prefix n t)))
        (frestrictLe t : Path n → Prefix n t))
  convert h using 1
  funext ω
  simp only [Function.comp_apply]
  rw [prefixHistory_frestrict, stateMean_run]

/-- A reward is observed at the end of its own round, not before it. -/
theorem reward_adapted (t : ℕ) (i : Fin n) :
    StronglyMeasurable[executionFiltration n (t + 1)]
      (fun ω : Path n => rewardReal (pathRewards ω t i)) := by
  apply Measurable.stronglyMeasurable
  rw [Filtration.piLE_eq_comap_frestrictLe]
  have h := (measurable_of_countable
    (fun h : Prefix n (t+1) => rewardReal ((h ⟨t+1, Finset.mem_Iic.mpr le_rfl⟩).1 i))).comp
      (comap_measurable (m := (inferInstance : MeasurableSpace (Prefix n (t+1))))
        (frestrictLe (t+1) : Path n → Prefix n (t+1)))
  exact h

/-- The mean of the joint one-step law is the actual model mean at its pre-round state. -/
theorem integral_outcome_reward (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (s : Execution.State n K) (i : Fin n) :
    ∫ o, rewardReal (o.1 i) ∂(outcomeDistribution M p C lam s).toMeasure =
      stateMean M p lam s i := by
  let q := PMF.bernoulli
    ⟨stateMean M p lam s i, (stateMean_mem M p lam s i).1⟩
    (stateMean_mem M p lam s i).2
  have hm : (outcomeDistribution M p C lam s).map (fun o => o.1 i) = q := by
    change (outcomeDistribution M p C lam s).map ((fun x : Fin n → Bool => x i) ∘ Prod.fst) = q
    rw [← PMF.map_comp]
    rw [outcomeDistribution_map_fst]
    exact finiteProduct_map_eval _ i
  calc
    _ = ∫ b, rewardReal b ∂q.toMeasure := by
      rw [← hm, ← PMF.toMeasure_map (fun o : Outcome n => o.1 i) (outcomeDistribution M p C lam s) (measurable_of_countable _)]
      rw [integral_map (by fun_prop) (by fun_prop)]
    _ = _ := by
      simp [q, PMF.integral_eq_sum, PMF.bernoulli_apply, rewardReal]
      rfl

/-- Conditional expectation is derived from the joint Bernoulli kernel, not assumed. -/
theorem conditional_reward_mean (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (t : ℕ) (i : Fin n) :
    (executionMeasure M p C lam)[fun ω => rewardReal (pathRewards ω t i) |
        executionFiltration n t] =ᵐ[executionMeasure M p C lam]
      fun ω => actualMean M p lam (pathRewards ω) (pathContacts p ω) t i := by
  let μ := executionMeasure M p C lam
  have hint : Integrable (fun ω : Path n => rewardReal ((ω (t+1)).1 i)) μ := by
    apply Integrable.of_bound (C := 1)
    · exact ((measurable_of_countable (fun o : Outcome n => rewardReal (o.1 i))).comp
        (measurable_pi_apply (t+1))).stronglyMeasurable.aestronglyMeasurable
    · filter_upwards [] with ω
      rcases rewardReal_mem ((ω (t+1)).1 i) with ⟨h0,h1⟩
      simpa [Real.norm_eq_abs, abs_of_nonneg h0] using h1
  have he := condExp_ae_eq_integral_condDistrib (μ := μ)
    (f := fun o : Outcome n => rewardReal (o.1 i))
    (measurable_frestrictLe t) (measurable_pi_apply (t+1)).aemeasurable
    (measurable_of_countable (fun o : Outcome n => rewardReal (o.1 i))).stronglyMeasurable hint
  have hk := ae_of_ae_map (measurable_frestrictLe t).aemeasurable
    (conditional_outcome_law M p C lam t)
  rw [Filtration.piLE_eq_comap_frestrictLe]
  filter_upwards [he, hk] with ω he hk
  change μ[fun ω => rewardReal ((ω (t+1)).1 i) |
    MeasurableSpace.pi.comap (frestrictLe t)] ω = _
  rw [he, hk]
  change (∫ o, rewardReal (o.1 i)
    ∂(outcomeDistribution M p C lam (replay p (prefixHistory t (frestrictLe t ω))).2).toMeasure) = _
  rw [integral_outcome_reward, prefixHistory_frestrict, stateMean_run]


/-- Split a completed prefix into its previous prefix and the newest outcome. -/
def splitPrefix (t : ℕ) (h : Prefix n (t+1)) : Prefix n t × Outcome n :=
  ((fun i => h ⟨i.val, Finset.mem_Iic.mpr (le_trans (Finset.mem_Iic.mp i.property) (Nat.le_succ t))⟩),
    h ⟨t+1, Finset.mem_Iic.mpr le_rfl⟩)

theorem splitPrefix_injective (t : ℕ) : Function.Injective (splitPrefix (n := n) t) := by
  intro a b hab
  funext i
  have hi := Finset.mem_Iic.mp i.property
  by_cases h : i.val ≤ t
  · exact congrFun (congrArg Prod.fst hab) ⟨i.val, Finset.mem_Iic.mpr h⟩
  · have hieq : i = ⟨t+1, Finset.mem_Iic.mpr le_rfl⟩ := by
      apply Subtype.ext
      change i.val = t + 1
      omega
    rw [hieq]
    exact congrArg Prod.snd hab

/-- Augmented trajectory uniqueness: every realization of the same augmented conditional joint
laws has the same finite trajectory distribution. Nothing is required after the horizon. -/
theorem finite_trajectory_law_unique (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (ν : Measure (Path n)) [IsProbabilityMeasure ν]
    (hzero : ν.map (frestrictLe 0) = (executionMeasure M p C lam).map (frestrictLe 0))
    (hlaw : ∀ t < p.T,
      condDistrib (fun ω : Path n => ω (t+1)) (frestrictLe t) ν
        =ᵐ[ν.map (frestrictLe t)] executionKernel M p C lam t) :
    ∀ t ≤ p.T, ν.map (frestrictLe t) = (executionMeasure M p C lam).map (frestrictLe t) := by
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
      (executionMeasure M p C lam).map (fun ω => (frestrictLe t ω, ω (t+1)))
    rw [(condDistrib_ae_eq_iff_measure_eq_compProd (frestrictLe t)
      (measurable_pi_apply (t+1)).aemeasurable (executionKernel M p C lam t)).mp
        (hlaw t (by omega))]
    rw [(condDistrib_ae_eq_iff_measure_eq_compProd (frestrictLe t)
      (measurable_pi_apply (t+1)).aemeasurable (executionKernel M p C lam t)).mp
        (conditional_outcome_law M p C lam t)]
    rw [ih]


/-- Reward part of the joint kernel. -/
def rewardKernel (M : DecayModel n K) (p : Execution.Params n K)
    (lam : Fin 2) (t : ℕ) : Kernel (Prefix n t) (Fin n → Bool) :=
  Kernel.ofFunOfCountable fun h =>
    (rewardDistribution M p lam (replay p (prefixHistory t h)).2).toMeasure

instance rewardKernel_markov (M : DecayModel n K) (p : Execution.Params n K)
    (lam : Fin 2) (t : ℕ) : IsMarkovKernel (rewardKernel M p lam t) := by
  constructor
  intro h
  change IsProbabilityMeasure
    (rewardDistribution M p lam (replay p (prefixHistory t h)).2).toMeasure
  infer_instance


/-- The joint reward vector has the product Bernoulli law determined by the past state. -/
theorem conditional_reward_law (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (t : ℕ) :
    condDistrib (fun ω : Path n => (ω (t+1)).1) (frestrictLe t)
        (executionMeasure M p C lam)
      =ᵐ[(executionMeasure M p C lam).map (frestrictLe t)] rewardKernel M p lam t := by
  have hc := condDistrib_comp (mβ := (inferInstance : MeasurableSpace (Prefix n t)))
    (frestrictLe t : Path n → Prefix n t)
    (μ := executionMeasure M p C lam) (Y := fun ω : Path n => ω (t+1))
    (measurable_pi_apply (t+1)).aemeasurable measurable_fst
  filter_upwards [hc, conditional_outcome_law M p C lam t] with h hc hk
  simp only [Function.comp_def] at hc
  rw [hc, Kernel.map_apply _ measurable_fst, hk]
  change (outcomeDistribution M p C lam (replay p (prefixHistory t h)).2).toMeasure.map Prod.fst = _
  rw [PMF.toMeasure_map Prod.fst _ measurable_fst, outcomeDistribution_map_fst]
  rfl

/-- Fresh contacts remain independent after the current rewards have been observed. -/
theorem executionKernel_split (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (t : ℕ) :
    executionKernel M p C lam t = rewardKernel M p lam t ⊗ₖ
      Kernel.const (Prefix n t × (Fin n → Bool)) (contactDistribution C).toMeasure := by
  ext h : 1
  apply Measure.ext_of_singleton
  intro o
  rcases o with ⟨x,j⟩
  change (outcomeDistribution M p C lam (replay p (prefixHistory t h)).2).toMeasure {(x,j)} = _
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  rw [outcomeDistribution_apply]
  rw [show ({(x,j)} : Set (Outcome n)) = {x} ×ˢ {j} by ext z; simp]
  rw [Kernel.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _)]
  simp only [Kernel.const_apply]
  simp only [lintegral_const, Measure.restrict_apply_univ]
  change _ = (contactDistribution C).toMeasure {j} *
    (rewardDistribution M p lam (replay p (prefixHistory t h)).2).toMeasure {x}
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  exact mul_comm _ _

/-- Joint conditional contact law given both all earlier outcomes and the current reward
vector. In particular it is not merely a collection of marginal row laws. -/
theorem contact_step_conditional_law (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (t : ℕ) :
    condDistrib (fun ω : Path n => (ω (t+1)).2)
        (fun ω : Path n => (frestrictLe t ω, (ω (t+1)).1)) (executionMeasure M p C lam)
      =ᵐ[(executionMeasure M p C lam).map (fun ω => (frestrictLe t ω, (ω (t+1)).1))]
        Kernel.const (Prefix n t × (Fin n → Bool)) (contactDistribution C).toMeasure := by
  let μ := executionMeasure M p C lam
  have hj := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ : ℕ => Outcome n) (κ := executionKernel M p C lam) (a := t)
    (μ₀ := Measure.dirac ((fun _ => false), id))
  have hsplit := congrArg (fun ν : Measure (Prefix n t × Outcome n) =>
    ν.map MeasurableEquiv.prodAssoc.symm) hj
  rw [executionKernel_split, Measure.compProd_assoc] at hsplit
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at hsplit
  have hfull : μ.map (fun ω : Path n => ((frestrictLe t ω, (ω (t+1)).1), (ω (t+1)).2)) =
      ((μ.map (frestrictLe t)) ⊗ₘ rewardKernel M p lam t) ⊗ₘ
        Kernel.const (Prefix n t × (Fin n → Bool)) (contactDistribution C).toMeasure := hsplit.symm
  have hfst := congrArg Measure.fst hfull
  rw [Measure.fst_map_prodMk (by fun_prop), Measure.fst_compProd] at hfst
  rw [← hfst] at hfull
  exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (by fun_prop) (by fun_prop) hfull


/-- Fresh whole contact vectors are independent of every completed round. -/
theorem contact_before_conditional_law (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (t : ℕ) :
    condDistrib (fun ω : Path n => (ω (t+1)).2) (frestrictLe t)
        (executionMeasure M p C lam)
      =ᵐ[(executionMeasure M p C lam).map (frestrictLe t)]
        Kernel.const (Prefix n t) (contactDistribution C).toMeasure := by
  have hc := condDistrib_comp (mβ := (inferInstance : MeasurableSpace (Prefix n t)))
    (frestrictLe t : Path n → Prefix n t)
    (μ := executionMeasure M p C lam) (Y := fun ω : Path n => ω (t+1))
    (measurable_pi_apply (t+1)).aemeasurable measurable_snd
  filter_upwards [hc, conditional_outcome_law M p C lam t] with h hc hk
  simp only [Function.comp_def] at hc
  rw [hc, Kernel.map_apply _ measurable_snd, hk]
  change (outcomeDistribution M p C lam (replay p (prefixHistory t h)).2).toMeasure.map Prod.snd = _
  rw [PMF.toMeasure_map Prod.snd _ measurable_snd, outcomeDistribution_map_snd]
  rfl

/-- Product factorization at a pre-round history, used for the analysis-only contact stream. -/
theorem history_contact_joint (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (t : ℕ) :
    (executionMeasure M p C lam).map (fun ω : Path n => (frestrictLe t ω, (ω (t+1)).2)) =
      ((executionMeasure M p C lam).map (frestrictLe t)).prod (contactDistribution C).toMeasure := by
  rw [← Measure.compProd_const]
  exact (condDistrib_ae_eq_iff_measure_eq_compProd (frestrictLe t)
    (μ := executionMeasure M p C lam) (Y := fun ω : Path n => (ω (t+1)).2)
    (measurable_snd.comp (measurable_pi_apply (t+1))).aemeasurable
    (Kernel.const (Prefix n t) (contactDistribution C).toMeasure)).mp
      (contact_before_conditional_law M p C lam t)

end AnvBandit.ExecutionLaw




