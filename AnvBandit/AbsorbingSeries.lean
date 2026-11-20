import AnvBandit.AbsorbingCoupling
import AnvBandit.AbsorbingExpectation
import AnvBandit.ExecutionContacts
import AnvBandit.RemainingWaitReal

/-! C.12 on the actual constructed law, using the exact joint shifted-contact
law and all-path local-failure absorption, not conditioning on E_delta. -/
noncomputable section
open scoped BigOperators Classical
open Finset MeasureTheory ProbabilityTheory
namespace AnvBandit.Absorbing
open Execution ExecutionLaw ExecutionBounds ActualPropagation
variable {n K : ℕ}

lemma shiftedContacts_eq_phaseContactStream (M : DecayModel n K) (p : Params n K) :
    (fun ω : Path n => shiftedContacts M p (pathContacts p ω)) =
      phaseContactStream p (preparation M p) := by
  funext ω j
  simp [shiftedContacts, phaseContactStream, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The expected ideal potential coupled to the real run is exactly the
paper's remaining-arrival function, with the correct preparation+1 offset. -/
theorem actual_ideal_potential_integral (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (j : ℕ) :
    (∫ ω, Vpot (by have := p.hn; omega) C (holder p M.star)
      (Inform (shiftedContacts M p (pathContacts p ω)) {holder p M.star} j)
      ∂executionMeasure M p C lam) =
      remainingV (by have := p.hn; omega) C (holder p M.star) j := by
  let hd : 0 < n-1 := by have := p.hn; omega
  have hm : Measurable (phaseContactStream p (preparation M p)) := by
    unfold phaseContactStream pathContacts
    fun_prop
  have hlaw := actual_contact_stream_law M p C lam (preparation M p)
  rw [← integral_Vpot_inform_eq_remainingV (hd := hd) p.hn C (holder p M.star) j,
    ← hlaw, integral_map hm.aemeasurable
      (measurable_inform_function _ _ _).aestronglyMeasurable]
  rw [← shiftedContacts_eq_phaseContactStream M p]

/-- C.12, after the reliable preparation stages. -/
theorem expectedPotential_le_remaining_after (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (j : ℕ) :
    expectedPotential M p C lam (preparation M p+j) ≤
      remainingV (by have := p.hn; omega) C (holder p M.star) j := by
  let hd : 0 < n-1 := by have := p.hn; omega
  have hm : Measurable (phaseContactStream p (preparation M p)) := by
    unfold phaseContactStream pathContacts
    fun_prop
  have hi := integrable_Vpot_inform (hd := hd) p.hn C (holder p M.star) j
  rw [← actual_contact_stream_law M p C lam (preparation M p)] at hi
  have hint := (integrable_map_measure
    (measurable_inform_function _ _ _).aestronglyMeasurable hm.aemeasurable).mp hi
  rw [← shiftedContacts_eq_phaseContactStream M p] at hint
  have he := integral_mono (state_potential_integrable M p C lam (preparation M p+j)) hint
    (fun ω => potential_le_ideal M p C lam pathRewards (pathContacts p) j ω)
  simp only [Function.comp_apply] at he
  rw [actual_ideal_potential_integral] at he
  exact he

/-- Unified C.12 including the preparation prefix, where v_0=M1. -/
theorem expectedPotential_le_remaining (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (j : ℕ) :
    expectedPotential M p C lam j ≤
      remainingV (by have := p.hn; omega) C (holder p M.star) (j-preparation M p) := by
  by_cases hj : preparation M p ≤ j
  · have h := expectedPotential_le_remaining_after M p C lam (j-preparation M p)
    simpa [Nat.add_sub_of_le hj] using h
  · have hj' : j ≤ preparation M p := by omega
    rw [Nat.sub_eq_zero_of_le hj', remainingV_zero]
    have hi := integral_mono (state_potential_integrable M p C lam j)
      (integrable_const (M1 (by have := p.hn; omega) C (holder p M.star)))
      (fun ω => Vpot_le_M1 p.hn C
        (ReachData.ofIrreducible C.irreducible (holder p M.star))
        (source_mem_state M p lam pathRewards (pathContacts p) j ω))
    simpa [expectedPotential] using hi

end AnvBandit.Absorbing
