import AnvBandit.Absorbing

/-! Exact last actual phase and terminal support, including H≥T. -/
noncomputable section
open scoped BigOperators Classical
open Finset
namespace AnvBandit.Absorbing
open Execution
variable {n K : ℕ} {Ω : Type*}

def lastPhase (p : Params n K) : ℕ := Nat.find (show ∃ ℓ, p.T ≤ p.phaseEnd ℓ from
  ⟨p.T, p.le_phaseEnd p.T⟩)

lemma lastPhase_reaches (p : Params n K) : p.T ≤ p.phaseEnd (lastPhase p) := by
  unfold lastPhase
  exact Nat.find_spec (show ∃ ℓ, p.T ≤ p.phaseEnd ℓ from ⟨p.T, p.le_phaseEnd p.T⟩)

lemma lastPhase_pos (p : Params n K) : 1 ≤ lastPhase p := by
  have h := lastPhase_reaches p
  have hT := p.hT
  by_contra he
  have hz : lastPhase p = 0 := by omega
  simp only [hz, p.phaseEnd_zero] at h
  omega

lemma lastPhase_le_T (p : Params n K) : lastPhase p ≤ p.T := Nat.find_min' _ (p.le_phaseEnd p.T)

lemma phaseEnd_lt_horizon_iff (p : Params n K) (j : ℕ) :
    p.phaseEnd j < p.T ↔ j < lastPhase p := by
  constructor
  · intro h
    by_contra hn
    have hj : lastPhase p ≤ j := by omega
    have he := p.phaseEnd_strictMono.monotone hj
    have hr := lastPhase_reaches p
    omega
  · intro h
    exact lt_of_not_ge (Nat.find_min
      (show ∃ ℓ, p.T ≤ p.phaseEnd ℓ from ⟨p.T, p.le_phaseEnd p.T⟩) h)

lemma lastPhase_eq_one (p : Params n K) (h : p.T ≤ p.H) : lastPhase p = 1 := by
  have hup : lastPhase p ≤ 1 := Nat.find_min' _ (by simpa using h)
  have hlo := lastPhase_pos p
  omega

lemma state_after_lastPhase (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n)
    (j : ℕ) (hj : lastPhase p ≤ j) (ω : Ω) : state M p lam X J j ω = univ := by
  apply terminal_state
  exact (lastPhase_reaches p).trans (p.phaseEnd_strictMono.monotone hj)

lemma error_terminal_support (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n)
    (j : ℕ) (hj : lastPhase p ≤ j+1) (ω : Ω) : error M p lam X J j ω = 0 := by
  apply error_eq_zero_of_absorbed
  intro h
  have := (phaseEnd_lt_horizon_iff p (j+1)).mp h.1
  omega

/-- The live-state predicate depends only on a genuinely observed prefix. Even
when the nominal boundary lies beyond T, its inactive test has no influence. -/
lemma live_iff_observed_prefix (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n)
    (j : ℕ) (ω : Ω) :
    live M p lam X J j ω ↔ p.phaseEnd j < p.T ∧
      prefixGood M p lam X J (min (p.phaseEnd j) p.T) ω := by
  by_cases h : p.phaseEnd j < p.T
  · simp only [live, min_eq_left h.le]
  · simp [live, h]

end AnvBandit.Absorbing
