import AnvBandit.ExecutionBounds
import AnvBandit.ExecutionPropagation
import AnvBandit.PotentialBridge

/-!
# Local-prefix and terminal absorption for the actual execution

`state j` is the paper's `Z_{j+1}` (zero based completed-phase index).
The test uses only observations through that phase boundary, with the *original*
fixed confidence logarithm. No conditioning on the full good event occurs here.
The one-step contact integral below is a deterministic kernel calculation, not
an assertion of a conditional contact law. That law must be supplied by the
canonical actual-execution construction before taking conditional expectations.
-/
noncomputable section
open scoped BigOperators Classical
open Finset MeasureTheory
open Classical

namespace AnvBandit.Absorbing
open Execution ExecutionLaw ExecutionBounds
variable {n K : ℕ} {Ω : Type*}

def prefixGood (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n)
    (t : ℕ) (ω : Ω) : Prop :=
  ω ∈ ObservedPrefix.good (selected p X J) (reward X) (mean M p lam X J) t p.L

lemma prefixGood_mono (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n)
    {s t : ℕ} (hst : s ≤ t) {ω : Ω} (h : prefixGood M p lam X J t ω) :
    prefixGood M p lam X J s ω :=
  ObservedPrefix.good_prefix _ _ _ hst h

/-- The boundary is strictly before `T`: in particular a complete final phase
ending exactly at `T` is absorbed without communicating. -/
def live (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n)
    (j : ℕ) (ω : Ω) : Prop :=
  p.phaseEnd j < p.T ∧ prefixGood M p lam X J (p.phaseEnd j) ω

def state (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n)
    (j : ℕ) (ω : Ω) : Finset (Fin n) :=
  if live M p lam X J j ω then
    holders M.star (run p (realTape (X ω)) (J ω) (p.phaseEnd j)) else univ

lemma live_mono (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n)
    {a b : ℕ} (hab : a ≤ b) {ω : Ω} (h : live M p lam X J b ω) :
    live M p lam X J a ω := by
  have ht := p.phaseEnd_strictMono.monotone hab
  exact ⟨ht.trans_lt h.1, prefixGood_mono M p lam X J ht h.2⟩

lemma state_eq_univ_after_absorption (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n)
    {a b : ℕ} (hab : a ≤ b) {ω : Ω} (h : ¬live M p lam X J a ω) :
    state M p lam X J b ω = univ := by
  exact if_neg (fun hb => h (live_mono M p lam X J hab hb))

lemma source_mem_state (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n) (j : ℕ) (ω : Ω) :
    holder p M.star ∈ state M p lam X J j ω := by
  unfold state
  split_ifs
  · exact permanent_holder_mem p M.star _ _ _
  · exact mem_univ _

lemma terminal_state (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n)
    (j : ℕ) (hj : p.T ≤ p.phaseEnd j) (ω : Ω) :
    state M p lam X J j ω = univ := by
  exact if_neg (fun h => (not_lt_of_ge hj) h.1)

lemma terminal_potential (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n)
    (C : ContactMatrix n) (j : ℕ) (hj : p.T ≤ p.phaseEnd j) (ω : Ω) :
    Vpot (by have := p.hn; omega) C (holder p M.star) (state M p lam X J j ω) = 0 := by
  rw [terminal_state M p lam X J j hj ω, Vpot_univ]

/-- This test is used only when the entire current phase is still prefix-good
and actually communicates. In all other cases `error` below is zero. -/
def wrong (k : Fin K) (s : State n K) : Prop :=
  ∃ i, i ∈ holders k s ∧ (s.nodes i).cache ≠ k

def error (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n)
    (j : ℕ) (ω : Ω) : ℝ :=
  if live M p lam X J (j+1) ω ∧
      wrong M.star (preBoundary p (realTape (X ω)) (J ω) (j+1)) then 1 else 0

lemma error_eq_zero_of_absorbed (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n)
    (j : ℕ) (ω : Ω) (h : ¬live M p lam X J (j+1) ω) :
    error M p lam X J j ω = 0 := by simp [error, h]

/-- All local states contain their permanent sticky arms, even after an erroneous
recommendation; this does not assume early holder-set monotonicity. -/
lemma source_mem_holders_state (p : Params n K) (k : Fin K) (s : State n K) :
    holder p k ∈ holders k s := by
  rw [mem_holders]
  exact mem_union_left _ (mem_sticky_holder p k)

lemma reliable_of_not_wrong (k : Fin K) (s : State n K) (h : ¬wrong k s) :
    ∀ i, i ∈ holders k s → (s.nodes i).cache = k := by
  intro i hi
  by_contra hne
  exact h ⟨i, hi, hne⟩

/-- The exact one-step drift inequality integrated over the original contact
kernel. This is the nonabsorbing branch of C.8; current reward/cache are fixed.
No probability of a globally conditioned event appears in this statement. -/
theorem contact_integral_drift (p : Params n K) (C : ContactMatrix n)
    (k : Fin K) (s : State n K) :
    ((univ \ holders k s).card : ℝ) ≤
      Vpot (by have := p.hn; omega) C (holder p k) (holders k s) -
        (∫ R, Vpot (by have := p.hn; omega) C (holder p k)
          (holders k (communicate s R)) ∂stepDist C) +
        M1 (by have := p.hn; omega) C (holder p k) * (if wrong k s then 1 else 0) := by
  let hd : 0 < n - 1 := by have := p.hn; omega
  let i0 := holder p k
  let rd := ReachData.ofIrreducible C.irreducible i0
  have hsource := source_mem_holders_state p k s
  by_cases hw : wrong k s
  · have hlo := card_sdiff_le_Vpot (hd := hd) p.hn C rd hsource
    have hupper : (∫ R, Vpot hd C i0 (holders k (communicate s R)) ∂stepDist C) ≤
        M1 hd C i0 := by
      calc
        _ ≤ ∫ _R : Fin n → Fin n, M1 hd C i0 ∂stepDist C := by
          apply integral_mono Integrable.of_finite (integrable_const _)
          intro R
          exact Vpot_le_M1 p.hn C rd (source_mem_holders_state p k (communicate s R))
        _ = _ := by simp
    simp only [if_pos hw, mul_one]
    linarith
  · have hrec := Vpot_recursion_of_irreducible (hd := hd) p.hn C hsource
    have hle : (∫ R, Vpot hd C i0 (holders k (communicate s R)) ∂stepDist C) ≤
        ∫ R, Vpot hd C i0 (infStep R (holders k s)) ∂stepDist C := by
      apply integral_mono Integrable.of_finite Integrable.of_finite
      intro R
      exact Vpot_anti p.hn C rd (subset_infStep R _ hsource)
        (infStep_subset_communicate_holders k s R (reliable_of_not_wrong k s hw))
    simp only [if_neg hw, mul_zero, add_zero]
    linarith

/-- A cached wrong arm has at least as many phase pulls as the optimum.
Consequently twice the suboptimal phase pulls cover the entire phase length.
This is the local, actual-cache charging inequality used in C.9. -/
theorem wrong_cache_half (i : Fin n) (s : LocalState n K i) (k : Fin K)
    (hk : k ∈ s.active) (hne : s.cache ≠ k) :
    (∑ a ∈ s.active, s.C a) ≤ 2 * ∑ a ∈ s.active.erase k, s.C a := by
  have hmax : s.C k ≤ s.C s.cache := by
    exact_mod_cast (topArg_max (fun a => (s.C a : ℝ)) s.active s.active_nonempty hk)
  have hmem : s.cache ∈ s.active.erase k := mem_erase.mpr ⟨hne, s.cache_mem⟩
  have hle : s.C s.cache ≤ ∑ a ∈ s.active.erase k, s.C a :=
    single_le_sum (fun a _ => Nat.zero_le _) hmem
  have hsplit := sum_erase_add s.active s.C hk
  omega

/-- A contact-kernel version of the next state. All arguments other than `R`
are fixed at the instant immediately before this phase's communication. -/
def nextState (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n)
    (j : ℕ) (ω : Ω) (R : Fin n → Fin n) : Finset (Fin n) :=
  if live M p lam X J (j+1) ω then
    holders M.star (communicate (preBoundary p (realTape (X ω)) (J ω) (j+1)) R)
  else univ

lemma nextState_actual (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n)
    (j : ℕ) (ω : Ω) :
    nextState M p lam X J j ω (J ω (j+1)) = state M p lam X J (j+1) ω := by
  unfold nextState state
  split_ifs with h
  · rw [run_boundary p _ _ (j+1) (by omega) h.1]
  · rfl

/-- Exact kernel form of C.8 for the absorbed actual process. Conditional-law
transport is separate: the integration is against `stepDist C`, not the law
conditioned on the global confidence event. -/
theorem absorbed_contact_drift (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n)
    (j : ℕ) (ω : Ω) :
    ((univ \ state M p lam X J j ω).card : ℝ) ≤
      Vpot (by have := p.hn; omega) C (holder p M.star) (state M p lam X J j ω) -
        (∫ R, Vpot (by have := p.hn; omega) C (holder p M.star)
          (nextState M p lam X J j ω R) ∂stepDist C) +
        M1 (by have := p.hn; omega) C (holder p M.star) * error M p lam X J j ω := by
  by_cases hnext : live M p lam X J (j+1) ω
  · have hprev := live_mono M p lam X J (Nat.le_succ j) hnext
    have hpre : holders M.star (preBoundary p (realTape (X ω)) (J ω) (j+1)) =
        state M p lam X J j ω := by
      rw [state, if_pos hprev]
      ext i
      simp only [mem_holders, preBoundary_active p _ _ (j+1) (by omega) hnext.1.le i,
        Nat.add_sub_cancel]
    have h := contact_integral_drift p C M.star
      (preBoundary p (realTape (X ω)) (J ω) (j+1))
    simpa only [nextState, if_pos hnext, error, hnext, true_and, hpre, if_true] using h
  · have hlow := card_sdiff_le_Vpot (hd := by have := p.hn; omega) p.hn C
      (ReachData.ofIrreducible C.irreducible (holder p M.star))
      (source_mem_state M p lam X J j ω)
    simpa [nextState, hnext, error, Vpot_univ] using hlow

/-- Deterministic least-index offender; its value when no error occurs is unused. -/
def offenders (k : Fin K) (s : State n K) : Finset (Fin n) :=
  (holders k s).filter (fun i => (s.nodes i).cache ≠ k)

lemma offenders_nonempty_iff (k : Fin K) (s : State n K) :
    (offenders k s).Nonempty ↔ wrong k s := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (mem_filter.mp hi).1, (mem_filter.mp hi).2⟩
  · rintro ⟨i, hi, he⟩
    exact ⟨i, mem_filter.mpr ⟨hi, he⟩⟩

def blamed (p : Params n K) (k : Fin K) (s : State n K) : Fin n :=
  if h : (offenders k s).Nonempty then (offenders k s).min' h else holder p k

lemma blamed_spec (p : Params n K) (k : Fin K) (s : State n K) (h : wrong k s) :
    blamed p k s ∈ holders k s ∧ (s.nodes (blamed p k s)).cache ≠ k := by
  have hn := (offenders_nonempty_iff k s).mpr h
  have hm := (offenders k s).min'_mem hn
  rw [blamed, dif_pos hn]
  exact mem_filter.mp hm

lemma blamed_minimal (p : Params n K) (k : Fin K) (s : State n K)
    (h : wrong k s) (i : Fin n) (hi : i ∈ holders k s) (he : (s.nodes i).cache ≠ k) :
    blamed p k s ≤ i := by
  have hn := (offenders_nonempty_iff k s).mpr h
  simpa [blamed, hn] using (offenders k s).min'_le i (mem_filter.mpr ⟨hi, he⟩)

/-- For the actual erroneous completed phase, the selected least offender pays
at least half its nominal phase length in suboptimal pulls. -/
theorem erroneous_phase_half (M : DecayModel n K) (p : Params n K)
    (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (ht : p.phaseEnd ℓ ≤ p.T)
    (hwrong : wrong M.star (preBoundary p X J ℓ)) :
    p.phaseEnd ℓ - p.phaseEnd (ℓ-1) ≤
      2 * ∑ k ∈ ((preBoundary p X J ℓ).nodes
        (blamed p M.star (preBoundary p X J ℓ))).active.erase M.star,
        ((preBoundary p X J ℓ).nodes (blamed p M.star (preBoundary p X J ℓ))).C k := by
  have hb := blamed_spec p M.star (preBoundary p X J ℓ) hwrong
  have hh := wrong_cache_half (blamed p M.star (preBoundary p X J ℓ))
    ((preBoundary p X J ℓ).nodes (blamed p M.star (preBoundary p X J ℓ))) M.star
    ((mem_holders _ _ _).mp hb.1) hb.2
  rwa [preBoundary_total p X J ℓ hℓ ht] at hh

end AnvBandit.Absorbing
