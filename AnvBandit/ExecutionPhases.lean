import AnvBandit.Execution

/-! Exact nonterminal phase intervals and precommunication states of the real execution. -/
noncomputable section
open scoped BigOperators
open Finset
namespace AnvBandit.Execution
variable {n K : ℕ}

@[simp] theorem Params.phaseEnd_cast (p : Params n K) (ℓ : ℕ) :
    (p.phaseEnd ℓ : ℝ) = tEll p.H p.β ℓ := by
  simp [Params.phaseEnd, tEll]

theorem Params.phaseLength_cast (p : Params n K) (ℓ : ℕ) :
    ((p.phaseEnd ℓ - p.phaseEnd (ℓ-1) : ℕ) : ℝ) = dEll p.H p.β ℓ := by
  rw [Nat.cast_sub (p.phaseEnd_strictMono.monotone (Nat.sub_le ℓ 1))]
  simp [dEll]

theorem phase_interval (p : Params n K) (X : ℕ → Fin n → ℝ)
    (J : ℕ → Fin n → Fin n) (t : ℕ) (ht : t < p.T) :
    p.phaseEnd ((run p X J t).phase - 1) ≤ t ∧
      t < p.phaseEnd (run p X J t).phase := by
  induction t with
  | zero => simp [run, initial]; exact p.hH
  | succ t ih =>
    have ht0 : t < p.T := by omega
    have hi := ih ht0
    have hp := (phase_bounds p X J t).1
    rw [run_succ]
    simp only [step, if_pos ht0]
    by_cases hc : communicates p t (run p X J t)
    · have he := hc.1
      simp only [if_pos hc, communicate, observe, Nat.add_sub_cancel]
      constructor
      · omega
      · have hs := p.phaseEnd_strictMono (Nat.lt_succ_self (run p X J t).phase)
        simp only [Nat.succ_eq_add_one] at hs
        exact lt_of_eq_of_lt hc.1 hs
    · simp only [if_neg hc, observe]
      constructor
      · omega
      · have hne : t+1 ≠ p.phaseEnd (run p X J t).phase := by
          intro he
          exact hc ⟨he, ht⟩
        omega

/-- The nominal endpoint interval uniquely determines the current phase. -/
theorem phase_of_interval (p : Params n K) (X : ℕ → Fin n → ℝ)
    (J : ℕ → Fin n → Fin n) (ℓ t : ℕ) (hℓ : 1 ≤ ℓ) (ht : t < p.T)
    (hlo : p.phaseEnd (ℓ-1) ≤ t) (hhi : t < p.phaseEnd ℓ) :
    (run p X J t).phase = ℓ := by
  have hi := phase_interval p X J t ht
  have hp := (phase_bounds p X J t).1
  have ha : (run p X J t).phase - 1 < ℓ :=
    p.phaseEnd_strictMono.lt_iff_lt.mp (lt_of_le_of_lt hi.1 hhi)
  have hb : ℓ-1 < (run p X J t).phase :=
    p.phaseEnd_strictMono.lt_iff_lt.mp (lt_of_le_of_lt hlo hi.2)
  omega

/-- No update changes active arms between the phase start and its final reward. -/
theorem active_during_phase (p : Params n K) (X : ℕ → Fin n → ℝ)
    (J : ℕ → Fin n → Fin n) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (t : ℕ)
    (ht : t < p.T) (hlo : p.phaseEnd (ℓ-1) ≤ t) (hhi : t < p.phaseEnd ℓ)
    (i : Fin n) :
    ((run p X J t).nodes i).active =
      ((run p X J (p.phaseEnd (ℓ-1))).nodes i).active := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases he : t = p.phaseEnd (ℓ-1)
    · rw [he]
    · have htpos : 1 ≤ t := by omega
      have htprev : t-1 < p.T := by omega
      have hlo' : p.phaseEnd (ℓ-1) ≤ t-1 := by omega
      have hhi' : t-1 < p.phaseEnd ℓ := by omega
      have hp := phase_of_interval p X J ℓ (t-1) hℓ htprev hlo' hhi'
      have hc : ¬ communicates p (t-1) (run p X J (t-1)) := by
        intro hc
        have he := hc.1
        rw [hp] at he
        omega
      have hrec := ih (t-1) (by omega) htprev hlo' hhi'
      have heq : t-1+1=t := by omega
      conv_lhs => rw [← heq, run_succ]
      simpa only [step, if_pos htprev, if_neg hc, observe, LocalState.observe, LocalState.active]
        using hrec

/-- At a complete nonterminal boundary the new phase has already begun. -/
theorem phase_at_boundary (p : Params n K) (X : ℕ → Fin n → ℝ)
    (J : ℕ → Fin n → Fin n) (ℓ : ℕ) (ht : p.phaseEnd ℓ < p.T) :
    (run p X J (p.phaseEnd ℓ)).phase = ℓ+1 := by
  have hi := phase_interval p X J _ ht
  have hp := (phase_bounds p X J (p.phaseEnd ℓ)).1
  have hlo := p.phaseEnd_strictMono.le_iff_le.mp hi.1
  have hhi := p.phaseEnd_strictMono.lt_iff_lt.mp hi.2
  omega

/-- Before the last reward of an actual complete phase, the phase pointer is unchanged. -/
theorem phase_before_boundary (p : Params n K) (X : ℕ → Fin n → ℝ)
    (J : ℕ → Fin n → Fin n) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (ht : p.phaseEnd ℓ ≤ p.T) :
    (run p X J (p.phaseEnd ℓ - 1)).phase = ℓ := by
  have hpEnd : 1 ≤ p.phaseEnd ℓ := le_trans hℓ (p.le_phaseEnd ℓ)
  have hi := phase_interval p X J (p.phaseEnd ℓ - 1) (by omega)
  have hp := (phase_bounds p X J (p.phaseEnd ℓ - 1)).1
  have hlo : (run p X J (p.phaseEnd ℓ - 1)).phase - 1 < ℓ :=
    p.phaseEnd_strictMono.lt_iff_lt.mp (by omega)
  have hhi : ℓ ≤ (run p X J (p.phaseEnd ℓ - 1)).phase :=
    p.phaseEnd_strictMono.le_iff_le.mp (by omega)
  omega

/-- The cached recommendation must be read from here, before `run (phaseEnd ℓ)` resets C. -/
def preBoundary (p : Params n K) (X : ℕ → Fin n → ℝ)
    (J : ℕ → Fin n → Fin n) (ℓ : ℕ) : State n K :=
  observe p (run p X J (p.phaseEnd ℓ - 1)) (X (p.phaseEnd ℓ - 1))

theorem run_boundary (p : Params n K) (X : ℕ → Fin n → ℝ)
    (J : ℕ → Fin n → Fin n) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (ht : p.phaseEnd ℓ < p.T) :
    run p X J (p.phaseEnd ℓ) = communicate (preBoundary p X J ℓ) (J ℓ) := by
  have hpEnd : 1 ≤ p.phaseEnd ℓ := le_trans hℓ (p.le_phaseEnd ℓ)
  have hp := phase_before_boundary p X J ℓ hℓ ht.le
  have he : p.phaseEnd ℓ - 1 + 1 = p.phaseEnd ℓ := by omega
  conv_lhs => rw [← he, run_succ]
  have hc : communicates p (p.phaseEnd ℓ - 1) (run p X J (p.phaseEnd ℓ - 1)) := by
    exact ⟨by rw [hp, he], by omega⟩
  simp only [step, if_pos (show p.phaseEnd ℓ-1 < p.T by omega), if_pos hc, hp]
  rfl

/-- During a nonterminal phase cumulative counts split into prephase and current counts. -/
theorem phase_count_conservation (p : Params n K) (X : ℕ → Fin n → ℝ)
    (J : ℕ → Fin n → Fin n) (t : ℕ) (ht : t < p.T) (i : Fin n) (k : Fin K) :
    ((run p X J t).nodes i).C k +
      N p X J (p.phaseEnd ((run p X J t).phase - 1)) i k = N p X J t i k := by
  induction t with
  | zero => simp [run, initial, N]
  | succ t ih =>
    have ht0 : t < p.T := by omega
    have hi := ih ht0
    by_cases hc : communicates p t (run p X J t)
    · have he := hc.1
      simp only [run_succ, step, if_pos ht0, if_pos hc, communicate, observe,
        Nat.add_sub_cancel, LocalState.receive]
      split <;> simp only <;> rw [← he] <;> exact Nat.zero_add _
    · rw [N_step p X J ht0]
      simp only [run_succ, step, if_pos ht0, if_neg hc, observe, LocalState.observe]
      change (((run p X J t).nodes i).C k +
        (if I p X J t i = k then 1 else 0)) +
        N p X J (p.phaseEnd ((run p X J t).phase - 1)) i k = _
      omega

theorem preBoundary_active (p : Params n K) (X : ℕ → Fin n → ℝ)
    (J : ℕ → Fin n → Fin n) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (ht : p.phaseEnd ℓ ≤ p.T) (i : Fin n) :
    ((preBoundary p X J ℓ).nodes i).active =
      ((run p X J (p.phaseEnd (ℓ-1))).nodes i).active := by
  have he := p.phaseEnd_strictMono (show ℓ-1 < ℓ by omega)
  exact active_during_phase p X J ℓ hℓ (p.phaseEnd ℓ-1) (by omega)
    (by omega) (by omega) i

theorem preBoundary_count_conservation (p : Params n K) (X : ℕ → Fin n → ℝ)
    (J : ℕ → Fin n → Fin n) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (ht : p.phaseEnd ℓ ≤ p.T) (i : Fin n) (k : Fin K) :
    ((preBoundary p X J ℓ).nodes i).C k + N p X J (p.phaseEnd (ℓ-1)) i k =
      N p X J (p.phaseEnd ℓ) i k := by
  have hpEnd : 1 ≤ p.phaseEnd ℓ := le_trans hℓ (p.le_phaseEnd ℓ)
  have hc := phase_count_conservation p X J (p.phaseEnd ℓ-1) (by omega) i k
  rw [phase_before_boundary p X J ℓ hℓ ht] at hc
  have hn := N_step p X J (t := p.phaseEnd ℓ-1) (by omega) i k
  rw [show p.phaseEnd ℓ-1+1 = p.phaseEnd ℓ by omega] at hn
  change (((run p X J (p.phaseEnd ℓ-1)).nodes i).C k +
    (if I p X J (p.phaseEnd ℓ-1) i = k then 1 else 0)) + _ = _
  omega

theorem N_eq_of_no_selection (p : Params n K) (X : ℕ → Fin n → ℝ)
    (J : ℕ → Fin n → Fin n) (i : Fin n) (k : Fin K) (a b : ℕ)
    (hab : a ≤ b) (hbT : b ≤ p.T)
    (hsel : ∀ t, a ≤ t → t < b → I p X J t i ≠ k) :
    N p X J b i k = N p X J a i k := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    rw [N_step p X J (by omega), if_neg (hsel b hab (by omega)), add_zero]
    exact ih (by omega) (fun t hat htb => hsel t hat (by omega))

theorem preBoundary_count_support (p : Params n K) (X : ℕ → Fin n → ℝ)
    (J : ℕ → Fin n → Fin n) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (ht : p.phaseEnd ℓ ≤ p.T) (i : Fin n) (k : Fin K)
    (hk : k ∉ ((preBoundary p X J ℓ).nodes i).active) :
    ((preBoundary p X J ℓ).nodes i).C k = 0 := by
  have hab := (p.phaseEnd_strictMono (show ℓ-1 < ℓ by omega)).le
  have hc := preBoundary_count_conservation p X J ℓ hℓ ht i k
  have hn := N_eq_of_no_selection p X J i k _ _ hab ht (by
    intro t hat htb heq
    have hm := selected_mem p X J t i
    rw [heq, active_during_phase p X J ℓ hℓ t (lt_of_lt_of_le htb ht) hat htb i,
      ← preBoundary_active p X J ℓ hℓ ht i] at hm
    exact hk hm)
  omega

theorem preBoundary_total (p : Params n K) (X : ℕ → Fin n → ℝ)
    (J : ℕ → Fin n → Fin n) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (ht : p.phaseEnd ℓ ≤ p.T) (i : Fin n) :
    ∑ k ∈ ((preBoundary p X J ℓ).nodes i).active,
      ((preBoundary p X J ℓ).nodes i).C k = p.phaseEnd ℓ - p.phaseEnd (ℓ-1) := by
  have hab := (p.phaseEnd_strictMono (show ℓ-1 < ℓ by omega)).le
  have hc := congrArg (fun f : Fin K → ℕ => ∑ k, f k)
    (funext (preBoundary_count_conservation p X J ℓ hℓ ht i))
  simp only [sum_add_distrib] at hc
  rw [sum_N p X J _ (le_trans hab ht) i, sum_N p X J _ ht i] at hc
  have he : (∑ k ∈ ((preBoundary p X J ℓ).nodes i).active,
      ((preBoundary p X J ℓ).nodes i).C k) =
      ∑ k, ((preBoundary p X J ℓ).nodes i).C k := by
    apply sum_subset (subset_univ _)
    intro k _ hk
    exact preBoundary_count_support p X J ℓ hℓ ht i k hk
  rw [he]
  omega
end AnvBandit.Execution
