import AnvBandit.AbsorbingConditional

/-! Finite-precontact measurability and integrability, derived by explicit
factorization rather than supplied as actual-process structure fields. -/
noncomputable section
open scoped BigOperators Classical
open Finset MeasureTheory ProbabilityTheory Preorder
namespace AnvBandit.Absorbing
open Execution ExecutionLaw ExecutionBounds
variable {n K : ℕ}

lemma state_beforeContact (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (j t : ℕ) (ht : p.phaseEnd (j+1) = t+1) {ω ω' : Path n}
    (h : beforeContact t ω = beforeContact t ω') :
    state M p lam pathRewards (pathContacts p) j ω =
      state M p lam pathRewards (pathContacts p) j ω' := by
  have hj : p.phaseEnd j ≤ t := by
    have hh := p.phaseEnd_strictMono (show j < j+1 by omega)
    rw [ht] at hh
    omega
  have hg := prefixGood_beforeContact M p lam t (p.phaseEnd j) (by omega) h
  simp only [state, live, hg, run_eq_of_beforeContact_eq p t h (p.phaseEnd j) hj]
  all_goals split_ifs <;> rfl

lemma error_beforeContact (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (j t : ℕ) (ht : p.phaseEnd (j+1) = t+1) {ω ω' : Path n}
    (h : beforeContact t ω = beforeContact t ω') :
    error M p lam pathRewards (pathContacts p) j ω =
      error M p lam pathRewards (pathContacts p) j ω' := by
  have hg := prefixGood_beforeContact M p lam t (p.phaseEnd (j+1)) (by omega) h
  simp only [error, live, hg, preBoundary_beforeContact p j t ht h]
  all_goals split_ifs <;> rfl

/-- Any function with this explicit finite factorization is measurable in the
communication-before information, not merely in the full path sigma-algebra. -/
lemma measurable_precontact_of_congr {α : Type*} [MeasurableSpace α]
    (t : ℕ) (F : Path n → α)
    (hF : ∀ ω ω', beforeContact t ω = beforeContact t ω' → F ω = F ω') :
    Measurable[(inferInstance : MeasurableSpace (Precontact n t)).comap (beforeContact t)] F := by
  have hg := measurable_of_countable (fun z : Precontact n t => F (reconstruct t z))
  have hh := hg.comp (comap_measurable (m := (inferInstance : MeasurableSpace (Precontact n t)))
    (beforeContact t))
  convert hh using 1
  funext ω
  exact hF ω (reconstruct t (beforeContact t ω)) (beforeContact_reconstruct t _).symm

lemma integrable_precontact_of_congr (μ : Measure (Path n)) [IsFiniteMeasure μ]
    (t : ℕ) (F : Path n → ℝ)
    (hF : ∀ ω ω', beforeContact t ω = beforeContact t ω' → F ω = F ω') :
    Integrable F μ := by
  let g := fun z : Precontact n t => F (reconstruct t z)
  have hg : StronglyMeasurable g := (measurable_of_countable g).stronglyMeasurable
  have hi : Integrable (fun ω => g (beforeContact t ω)) μ :=
    (integrable_map_measure hg.aestronglyMeasurable (beforeContact_measurable t).aemeasurable).mp
      Integrable.of_finite
  convert hi using 1
  funext ω
  exact hF ω (reconstruct t (beforeContact t ω)) (beforeContact_reconstruct t _).symm

lemma state_potential_integrable (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (j : ℕ) :
    Integrable (fun ω => Vpot (by have := p.hn; omega) C (holder p M.star)
      (state M p lam pathRewards (pathContacts p) j ω)) (executionMeasure M p C lam) := by
  let t := p.phaseEnd (j+1)-1
  have hpos : 1 ≤ p.phaseEnd (j+1) := (show 1 ≤ j+1 by omega).trans (p.le_phaseEnd _)
  have ht : p.phaseEnd (j+1) = t+1 := by dsimp [t]; omega
  apply integrable_precontact_of_congr _ t
  intro ω ω' h
  rw [state_beforeContact M p lam j t ht h]

lemma error_integrable (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (j : ℕ) :
    Integrable (error M p lam pathRewards (pathContacts p) j) (executionMeasure M p C lam) := by
  let t := p.phaseEnd (j+1)-1
  have hpos : 1 ≤ p.phaseEnd (j+1) := (show 1 ≤ j+1 by omega).trans (p.le_phaseEnd _)
  have ht : p.phaseEnd (j+1) = t+1 := by dsimp [t]; omega
  apply integrable_precontact_of_congr _ t
  exact fun ω ω' h => error_beforeContact M p lam j t ht h

lemma missing_integrable (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (j : ℕ) :
    Integrable (fun ω => ((univ \ state M p lam pathRewards (pathContacts p) j ω).card : ℝ))
      (executionMeasure M p C lam) := by
  let t := p.phaseEnd (j+1)-1
  have hpos : 1 ≤ p.phaseEnd (j+1) := (show 1 ≤ j+1 by omega).trans (p.le_phaseEnd _)
  have ht : p.phaseEnd (j+1) = t+1 := by dsimp [t]; omega
  apply integrable_precontact_of_congr _ t
  intro ω ω' h
  rw [state_beforeContact M p lam j t ht h]

end AnvBandit.Absorbing
