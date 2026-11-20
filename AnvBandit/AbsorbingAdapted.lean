import AnvBandit.AbsorbingMeasurability

/-! Explicit adaptedness statements for paper G_ell: complete past plus this
phase's rewards/cache/tests, without this phase's contact vector. -/
noncomputable section
open scoped BigOperators Classical
open Finset MeasureTheory
namespace AnvBandit.Absorbing
open Execution ExecutionLaw
variable {n K : ℕ}

lemma state_measurable_beforeContact (M : DecayModel n K) (p : Params n K)
    (lam : Fin 2) (j : ℕ) :
    let t := p.phaseEnd (j+1)-1
    Measurable[(inferInstance : MeasurableSpace (Precontact n t)).comap (beforeContact t)]
      (state M p lam pathRewards (pathContacts p) j) := by
  dsimp only
  let t := p.phaseEnd (j+1)-1
  have hpos : 1 ≤ p.phaseEnd (j+1) := (show 1 ≤ j+1 by omega).trans (p.le_phaseEnd _)
  have ht : p.phaseEnd (j+1) = t+1 := by dsimp [t]; omega
  exact measurable_precontact_of_congr t _ (fun ω ω' h => state_beforeContact M p lam j t ht h)

lemma error_measurable_beforeContact (M : DecayModel n K) (p : Params n K)
    (lam : Fin 2) (j : ℕ) :
    let t := p.phaseEnd (j+1)-1
    Measurable[(inferInstance : MeasurableSpace (Precontact n t)).comap (beforeContact t)]
      (error M p lam pathRewards (pathContacts p) j) := by
  dsimp only
  let t := p.phaseEnd (j+1)-1
  have hpos : 1 ≤ p.phaseEnd (j+1) := (show 1 ≤ j+1 by omega).trans (p.le_phaseEnd _)
  have ht : p.phaseEnd (j+1) = t+1 := by dsimp [t]; omega
  exact measurable_precontact_of_congr t _ (fun ω ω' h => error_beforeContact M p lam j t ht h)

lemma prefixGood_measurable_beforeContact (M : DecayModel n K) (p : Params n K)
    (lam : Fin 2) (j : ℕ) :
    let t := p.phaseEnd (j+1)-1
    MeasurableSet[(inferInstance : MeasurableSpace (Precontact n t)).comap (beforeContact t)]
      {ω | prefixGood M p lam pathRewards (pathContacts p) (p.phaseEnd (j+1)) ω} := by
  dsimp only
  let t := p.phaseEnd (j+1)-1
  have hpos : 1 ≤ p.phaseEnd (j+1) := (show 1 ≤ j+1 by omega).trans (p.le_phaseEnd _)
  have ht : p.phaseEnd (j+1) ≤ t+1 := by dsimp [t]; omega
  have hm := measurable_precontact_of_congr t
    (fun ω : Path n => decide (prefixGood M p lam pathRewards (pathContacts p) (p.phaseEnd (j+1)) ω))
    (by
      intro ω ω' h
      rw [propext (prefixGood_beforeContact M p lam t (p.phaseEnd (j+1)) ht h)])
  have he := hm (measurableSet_singleton true)
  simpa only [Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using he

end AnvBandit.Absorbing
