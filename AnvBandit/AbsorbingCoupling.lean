import AnvBandit.Absorbing
import AnvBandit.ActualPropagation

/-! All-path reliable coupling for the locally absorbed process. Unlike the
unabsorbed execution, it dominates the ideal process also on failure paths. -/
noncomputable section
open scoped BigOperators Classical
open Finset MeasureTheory Classical
namespace AnvBandit.Absorbing
open Execution ExecutionLaw ExecutionBounds ActualPropagation
variable {n K : ℕ} {Ω : Type*}

/-- From the first long enough phase onward, either the current prefix remains
good and actual reliability applies, or the next state has already absorbed.
There is no full-horizon good event in this theorem. -/
theorem reliable_step (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n)
    (j : ℕ) (hj : preparation M p ≤ j) (ω : Ω) :
    infStep (J ω (j+1)) (state M p lam X J j ω) ⊆
      state M p lam X J (j+1) ω := by
  by_cases hn : live M p lam X J (j+1) ω
  · have hp := live_mono M p lam X J (Nat.le_succ j) hn
    have he : holders M.star (preBoundary p (realTape (X ω)) (J ω) (j+1)) =
        state M p lam X J j ω := by
      rw [state, if_pos hp]
      ext i
      simp only [mem_holders, preBoundary_active p _ _ (j+1) (by omega) hn.1.le i,
        Nat.add_sub_cancel]
    conv_rhs => rw [state, if_pos hn, run_boundary p _ _ (j+1) (by omega) hn.1]
    rw [← he]
    apply infStep_subset_communicate_holders
    intro i hi
    apply reliable_cache_prefix M p lam X J ω (p.phaseEnd (j+1)) hn.1.le hn.2
      (j+1) (by omega) le_rfl i
    · rw [he, state, if_pos hp] at hi
      simpa only [mem_holders, Nat.add_sub_cancel] using hi
    · exact length_after_preparation M p (j+1) (by omega)
  · conv_rhs => rw [state, if_neg hn]
    exact subset_univ _

/-- C.12's pointwise inclusion, including paths which fail any later prefix
concentration test, and paths already beyond the terminal horizon. -/
theorem ideal_subset_state (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n)
    (j : ℕ) (ω : Ω) :
    Inform (shiftedContacts M p (J ω)) {holder p M.star} j ⊆
      state M p lam X J (preparation M p+j) ω := by
  induction j with
  | zero =>
    simp only [Inform_zero, Nat.add_zero, singleton_subset_iff]
    exact source_mem_state M p lam X J _ ω
  | succ j ih =>
    rw [Inform_succ]
    have hmono := ActualPropagation.infStep_mono (shiftedContacts M p (J ω) j) ih
    have hs := reliable_step M p lam X J (preparation M p+j) (by omega) ω
    exact hmono.trans (by simpa [shiftedContacts, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hs)

/-- The actual absorbed potential is bounded pathwise by the ideal remaining
potential, without conditioning the contact distribution on successful rewards. -/
theorem potential_le_ideal (M : DecayModel n K) (p : Params n K) (C : ContactMatrix n)
    (lam : Fin 2) (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n)
    (j : ℕ) (ω : Ω) :
    Vpot (by have := p.hn; omega) C (holder p M.star)
      (state M p lam X J (preparation M p+j) ω) ≤
    Vpot (by have := p.hn; omega) C (holder p M.star)
      (Inform (shiftedContacts M p (J ω)) {holder p M.star} j) := by
  apply Vpot_anti p.hn C (ReachData.ofIrreducible C.irreducible (holder p M.star))
  · exact subset_Inform _ _ _ (mem_singleton_self _)
  · exact ideal_subset_state M p lam X J j ω

end AnvBandit.Absorbing
