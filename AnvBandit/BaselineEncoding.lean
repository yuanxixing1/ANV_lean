import AnvBandit.BaselineObserved

/-! The canonical law satisfies the original reward-only encoding interface.
In particular, that interface is not an empty collection of probability measures. -/
noncomputable section
open MeasureTheory ProbabilityTheory Preorder
namespace AnvBandit.BaselineLaw
variable {n K : ℕ}

theorem kernel_no_contact (M : DecayModel n K) (p : BaselineExecution.Params n K)
    (lam : Fin 2) (t : ℕ) (h : Prefix n t) :
    ∀ᵐ o ∂executionKernel M p lam t h, o.2 = id := by
  change ∀ᵐ o ∂(outcomeDistribution M p lam (replay p (prefixHistory t h)).2).toMeasure,
    o.2 = id
  unfold outcomeDistribution
  rw [← PMF.toMeasure_map _ _ (measurable_of_countable _)]
  exact (ae_map_iff (measurable_of_countable _).aemeasurable
    (measurableSet_eq_fun measurable_snd measurable_const)).mpr
    (Filter.Eventually.of_forall (fun _ => rfl))

theorem canonical_no_contact (M : DecayModel n K) (p : BaselineExecution.Params n K)
    (lam : Fin 2) (t : ℕ) :
    ∀ᵐ ω ∂executionMeasure M p lam, (ω (t+1)).2 = id := by
  let μ := executionMeasure M p lam
  have hcomp : ∀ᵐ z ∂(μ.map (frestrictLe t) ⊗ₘ executionKernel M p lam t), z.2.2 = id := by
    apply (Measure.ae_compProd_iff (measurableSet_eq_fun (measurable_snd.comp measurable_snd)
      measurable_const)).mpr
    exact Filter.Eventually.of_forall (kernel_no_contact M p lam t)
  have he : μ.map (frestrictLe t) ⊗ₘ executionKernel M p lam t =
      μ.map (fun ω => (frestrictLe t ω, ω (t+1))) :=
    Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
  rw [he] at hcomp
  exact (ae_map_iff (by fun_prop)
    (measurableSet_eq_fun (measurable_snd.comp measurable_snd) measurable_const)).mp hcomp

/-- The constructed law itself satisfies every nontrivial original reward-law premise. -/
theorem canonical_original_law (M : DecayModel n K) (p : BaselineExecution.Params n K)
    (lam : Fin 2) :
    (∀ t < p.T, condDistrib (fun ω : Path n => (ω (t+1)).1) (frestrictLe t)
      (executionMeasure M p lam) =ᵐ[(executionMeasure M p lam).map (frestrictLe t)]
        rewardKernel M p lam t) ∧
    (∀ t < p.T, ∀ᵐ ω ∂executionMeasure M p lam, (ω (t+1)).2 = id) :=
  ⟨fun t _ => conditional_reward_law M p lam t, fun t _ => canonical_no_contact M p lam t⟩

end AnvBandit.BaselineLaw
