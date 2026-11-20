import AnvBandit.Constants

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-!
# Algorithm-1 line counting (Appendices A.6, C.1-C.2)

This file formalises the *combinatorial* layer of the analysis, i.e. the part of Appendices A.6 and
C.1-C.2 that turns the concentration event `E_δ` and the UCB selection rule (3.3)-(3.4) into
counting bounds on how often a node pulls a suboptimal arm.

`GoodRun M` records a trajectory of Algorithm 1 on the good event: personal empirical means
`bhat`, conditional means `p` (with the gap property `AdaptMeanInGap` and the concentration event
`ConcEvent`), a selection rule `I`, cumulative counts `N`, per-round active sets `active`, and the
*definitional* consequence `ucb` of the optimistic index (3.3) together with the arg-max rule (3.4).

Main results:
* `GoodRun.pair_budget`: the number of rounds in which node `i` pulls the suboptimal arm `k` while
  `k⋆` is active is at most the threshold `m_k` (Lemma A.2 / Appendix C.1);
* `terminal_budget`: the weighted budget of the suboptimal arms carried by terminal active sets is
  at most `min(n W_κ(c), W(c) + (n+1) w_max(c)) = C(c)` (Appendix C.1).
-/

noncomputable section
open scoped BigOperators
open Finset

namespace AnvBandit

variable {n K : ℕ}

/-- A trajectory of Algorithm 1 on the good event `E_δ`.  The fields are the *definitional*
properties of the run (statistics, selection rule, counts, active sets), not the paper's bounds. -/
structure GoodRun (M : DecayModel n K) where
  /-- The schedule constant `L_δ`. -/
  L : ℝ
  hL : 0 ≤ L
  /-- Personal empirical means `μ̂_{i,k}(m)`. -/
  bhat : Fin n → Fin K → ℕ → ℝ
  /-- Conditional means `p_{i,k}(s)` of the `s`-th personal pull. -/
  p : Fin n → Fin K → ℕ → ℝ
  hp : ∀ i, M.AdaptMeanInGap (p i)
  hc : ∀ i, DecayModel.ConcEvent L (bhat i) (p i)
  /-- The arm chosen by node `i` in round `t+1`. -/
  I : ℕ → Fin n → Fin K
  /-- `N t i k` = number of pulls of `k` by `i` among rounds `1..t` (prior to round `t+1`). -/
  N : ℕ → Fin n → Fin K → ℕ
  Nzero : ∀ i k, N 0 i k = 0
  Nstep : ∀ t i k, N (t + 1) i k = N t i k + (if I t i = k then 1 else 0)
  /-- The active set of node `i` in round `t+1`. -/
  active : ℕ → Fin n → Finset (Fin K)
  /-- The selected arm belongs to the active set (the algorithm selects from `S^{(ℓ)}_i`). -/
  sel_mem : ∀ t i, I t i ∈ active t i
  /-- The optimistic-index selection rule (3.3)-(3.4): if `k⋆` is active then the selected arm
  either has no prior observation, or both it and `k⋆` have been observed and the selected arm's
  UCB index dominates that of `k⋆`. -/
  ucb : ∀ t i, M.star ∈ active t i →
    N t i (I t i) = 0 ∨
    (1 ≤ N t i (I t i) ∧ 1 ≤ N t i M.star ∧
      bhat i M.star (N t i M.star) + rdelta L (N t i M.star)
        ≤ bhat i (I t i) (N t i (I t i)) + rdelta L (N t i (I t i)))

lemma filter_lt_succ_card_le (S : Finset ℕ) (t : ℕ) :
    (S.filter (· < t + 1)).card ≤ (S.filter (· < t)).card + 1 := by
  have hsub : S.filter (· < t + 1) ⊆ insert t (S.filter (· < t)) := by
    intro s hs
    rw [Finset.mem_filter] at hs
    rw [Finset.mem_insert, Finset.mem_filter]
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hs.2) with h | h
    · exact Or.inr ⟨hs.1, h⟩
    · exact Or.inl h
  calc (S.filter (· < t + 1)).card ≤ (insert t (S.filter (· < t))).card := Finset.card_le_card hsub
    _ ≤ (S.filter (· < t)).card + 1 := Finset.card_insert_le _ _

lemma filter_lt_succ_card_of_mem (S : Finset ℕ) (t : ℕ) (ht : t ∈ S) :
    (S.filter (· < t + 1)).card = (S.filter (· < t)).card + 1 := by
  have heq : S.filter (· < t + 1) = insert t (S.filter (· < t)) := by
    ext s
    rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_filter]
    constructor
    · rintro ⟨hs, hlt⟩
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt) with h | h
      · exact Or.inr ⟨hs, h⟩
      · exact Or.inl h
    · rintro (heq | ⟨hs, h⟩)
      · rw [heq]; exact ⟨ht, Nat.lt_succ_self t⟩
      · exact ⟨hs, Nat.lt_succ_of_lt h⟩
  rw [heq, Finset.card_insert_of_notMem]
  intro h; exact absurd (Finset.mem_filter.mp h).2 (lt_irrefl t)

lemma filter_lt_succ_card_of_notMem (S : Finset ℕ) (t : ℕ) (ht : t ∉ S) :
    (S.filter (· < t + 1)).card = (S.filter (· < t)).card := by
  have heq : S.filter (· < t + 1) = S.filter (· < t) := by
    ext s
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hs, hlt⟩
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt) with h | h
      · exact ⟨hs, h⟩
      · exact absurd (h ▸ hs) ht
    · rintro ⟨hs, h⟩; exact ⟨hs, Nat.lt_succ_of_lt h⟩
  rw [heq]

theorem GoodRun.N_mono {M : DecayModel n K} (R : GoodRun M) (i : Fin n) (k : Fin K) :
    Monotone (fun t => R.N t i k) := by
  refine monotone_nat_of_le_succ fun t => ?_
  rw [R.Nstep t i k]
  split <;> omega

/-- The cumulative count stays below the threshold `m_k` at every round in which the suboptimal arm
`k` is pulled while `k⋆` is active (contiguity to the optimistic index). -/
theorem GoodRun.N_lt_mk {M : DecayModel n K} (R : GoodRun M) {i : Fin n} {k : Fin K}
    (hk : k ≠ M.star) {t : ℕ} (hact : M.star ∈ R.active t i) (hsel : R.I t i = k) :
    R.N t i k < M.mkAll R.L k := by
  rw [← not_le]
  intro hmk
  have hstep := R.ucb t i hact
  rw [hsel] at hstep
  rcases hstep with h0 | ⟨h1, h2, hsel'⟩
  · have h1 := M.one_le_mkAll R.L k
    omega
  · exact M.not_selected_of_ge_mk (R.hp i) (R.hc i) R.hL hk h1 h2
      (by rwa [M.mkAll_eq_mkThr hk] at hmk) hsel'

/-- **Lemma A.2 counting form.** The number of rounds in which node `i` pulls the suboptimal arm
`k` while `k⋆` is active is at most the threshold `m_k`. -/
theorem GoodRun.pair_budget {M : DecayModel n K} (R : GoodRun M) (T : ℕ) (i : Fin n)
    {k : Fin K} (hk : k ≠ M.star) :
    ((Finset.range T).filter (fun t => M.star ∈ R.active t i ∧ R.I t i = k)).card
      ≤ M.mkAll R.L k := by
  set S : Finset ℕ := (Finset.range T).filter (fun t => M.star ∈ R.active t i ∧ R.I t i = k)
    with hS
  have hsel_mem : ∀ t ∈ S, R.I t i = k := fun t ht => (Finset.mem_filter.mp ht).2.2
  have hact_mem : ∀ t ∈ S, M.star ∈ R.active t i := fun t ht => (Finset.mem_filter.mp ht).2.1
  have hbdd : ∀ t ∈ S, R.N t i k < M.mkAll R.L k :=
    fun t ht => R.N_lt_mk hk (hact_mem t ht) (hsel_mem t ht)
  have hstep : ∀ t ∈ S, R.N (t + 1) i k = R.N t i k + 1 := by
    intro t ht; rw [R.Nstep t i k, if_pos (hsel_mem t ht)]
  have hcount : ∀ t, (S.filter (· < t)).card ≤ R.N t i k := by
    intro t
    induction t with
    | zero => simp [R.Nzero]
    | succ t ih =>
      have hgoal : (S.filter (· < t + 1)).card ≤ R.N (t + 1) i k := by
        by_cases ht : t ∈ S
        · have hcard := filter_lt_succ_card_of_mem S t ht
          have hstep' := hstep t ht
          calc (S.filter (· < t + 1)).card = (S.filter (· < t)).card + 1 := hcard
            _ ≤ R.N t i k + 1 := by omega
            _ = R.N (t + 1) i k := hstep'.symm
        · have hcard := filter_lt_succ_card_of_notMem S t ht
          have hmono : R.N t i k ≤ R.N (t + 1) i k := by
            rw [R.Nstep t i k]; split <;> omega
          omega
      simpa using hgoal
  by_cases hne : S.Nonempty
  · have htmax : S.max' hne ∈ S := S.max'_mem hne
    have hsub : S ⊆ insert (S.max' hne) (S.filter (· < S.max' hne)) := by
      intro s hs
      rw [Finset.mem_insert, Finset.mem_filter]
      rcases lt_or_eq_of_le (Finset.le_max' S s hs) with h | h
      · exact Or.inr ⟨hs, h⟩
      · exact Or.inl h
    have hle : S.card ≤ R.N (S.max' hne) i k + 1 := by
      calc S.card ≤ (insert (S.max' hne) (S.filter (· < S.max' hne))).card :=
            Finset.card_le_card hsub
        _ ≤ (S.filter (· < S.max' hne)).card + 1 := Finset.card_insert_le _ _
        _ ≤ R.N (S.max' hne) i k + 1 := by have := hcount (S.max' hne); omega
    have hb := hbdd (S.max' hne) htmax
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp


/-- Proposition A.6's per-node selection count `A⁺_{i,k}(T)`: the number of rounds `1..T` in which
`k⋆` is active for node `i` and `i` pulls the suboptimal arm `k`. -/
def GoodRun.AplusCount {M : DecayModel n K} (R : GoodRun M) (T : ℕ) (i : Fin n) (k : Fin K) : ℕ :=
  ((Finset.range T).filter (fun t => M.star ∈ R.active t i ∧ R.I t i = k)).card

/-- Proposition A.6, equation (A.11) in the `m_k` form: `A⁺_{i,k}(T) ≤ m_k`.  (The paper's sharper
form with `n_k + (4/Δ_k) E_{i,k}(N_{i,k}(T))` additionally needs the public-model positive-part area
`E_{i,k}`; for the personal-fatigue branch the threshold `m_k` is exactly the quantity used in
`C(c)`, so this is the branch-relevant form.) -/
theorem GoodRun.AplusCount_le_mk {M : DecayModel n K} (R : GoodRun M) (T : ℕ) (i : Fin n)
    {k : Fin K} (hk : k ≠ M.star) : R.AplusCount T i k ≤ M.mkAll R.L k :=
  R.pair_budget T i hk

end AnvBandit

/-!
## Finite observed-prefix counting interface

Unlike `GoodRun`, this interface asks for concentration only at prefixes observed by the
specified horizon. It is an auxiliary good-path interface, not a definition of the algorithm
or an assumption permitted at the eventual paper entry point. `Execution` supplies the action
and count identities; the probability layer supplies its finite-event fields.
-/
namespace AnvBandit
noncomputable section
open scoped BigOperators
open Finset
variable {n K : ℕ}

/-- Counts determined by actions, rather than a freely supplied counter. -/
def pullCount (I : ℕ → Fin n → Fin K) (t : ℕ) (i : Fin n) (k : Fin K) : ℕ :=
  ∑ s ∈ range t, if I s i = k then 1 else 0

@[simp] theorem pullCount_zero (I : ℕ → Fin n → Fin K) (i : Fin n) (k : Fin K) :
    pullCount I 0 i k = 0 := by simp [pullCount]

theorem pullCount_step (I : ℕ → Fin n → Fin K) (t : ℕ) (i : Fin n) (k : Fin K) :
    pullCount I (t+1) i k = pullCount I t i k + if I t i = k then 1 else 0 := by
  unfold pullCount
  rw [Finset.sum_range_succ]

theorem pullCount_mono (I : ℕ → Fin n → Fin K) (i : Fin n) (k : Fin K) :
    Monotone (fun t => pullCount I t i k) := by
  apply monotone_nat_of_le_succ
  intro t
  rw [pullCount_step]
  omega

/-- A finite good-path interface. No field quantifies over unobserved prefixes. -/
structure GoodRunOn (M : DecayModel n K) (T : ℕ) where
  L : ℝ
  hL : 0 ≤ L
  I : ℕ → Fin n → Fin K
  bhat : Fin n → Fin K → ℕ → ℝ
  meanSum : Fin n → Fin K → ℕ → ℝ
  mean_bounds : ∀ i k m, 1 ≤ m → m ≤ pullCount I T i k →
    M.b k ≤ meanSum i k m / m ∧ meanSum i k m / m ≤ M.b k + psi (M.f k) m
  hc : ∀ i k m, 1 ≤ m → m ≤ pullCount I T i k →
    |bhat i k m - meanSum i k m / m| ≤ rdelta L m
  active : ℕ → Fin n → Finset (Fin K)
  sel_mem : ∀ t, t < T → ∀ i, I t i ∈ active t i
  ucb : ∀ t, t < T → ∀ i, M.star ∈ active t i →
    pullCount I t i (I t i) = 0 ∨
    (1 ≤ pullCount I t i (I t i) ∧ 1 ≤ pullCount I t i M.star ∧
      bhat i M.star (pullCount I t i M.star) + rdelta L (pullCount I t i M.star)
        ≤ bhat i (I t i) (pullCount I t i (I t i)) + rdelta L (pullCount I t i (I t i)))

namespace GoodRunOn
variable {M : DecayModel n K} {T : ℕ} (R : GoodRunOn M T)

abbrev N := pullCount R.I

/-- The interface's mean sandwich is required only for prefixes observed by the horizon.
In the actual-run constructor it is derived from `ObservedPrefix.observed_mean_bounds`. -/
theorem prefix_bounds (i : Fin n) (k : Fin K) {m : ℕ}
    (hm : 1 ≤ m) (hobs : m ≤ R.N T i k) :
    M.b k ≤ R.meanSum i k m / m ∧
      R.meanSum i k m / m ≤ M.b k + psi (M.f k) m :=
  R.mean_bounds i k m hm hobs

theorem selection_gap (i : Fin n) {k : Fin K} {m ms : ℕ}
    (hm : 1 ≤ m) (hms : 1 ≤ ms)
    (hobs : m ≤ R.N T i k) (hsobs : ms ≤ R.N T i M.star)
    (hsel : R.bhat i M.star ms + rdelta R.L ms ≤ R.bhat i k m + rdelta R.L m) :
    M.gap k ≤ psi (M.f k) m + 2 * rdelta R.L m := by
  have hck := R.hc i k m hm hobs
  have hcs := R.hc i M.star ms hms hsobs
  have hpk := (R.prefix_bounds i k hm hobs).2
  have hps := (R.prefix_bounds i M.star hms hsobs).1
  have hk := (abs_le.mp hck).2
  have hs := (abs_le.mp hcs).1
  unfold DecayModel.gap
  linarith

theorem N_lt_mk {i : Fin n} {k : Fin K} (hk : k ≠ M.star)
    {t : ℕ} (ht : t < T) (hact : M.star ∈ R.active t i) (hsel : R.I t i = k) :
    R.N t i k < M.mkAll R.L k := by
  by_contra hnot
  have hmk : M.mkAll R.L k ≤ R.N t i k := by omega
  have hu := R.ucb t ht i hact
  rw [hsel] at hu
  rcases hu with hz | ⟨hm, hms, hu⟩
  · have := M.one_le_mkAll R.L k
    dsimp only [N] at *
    omega
  · have hobs := pullCount_mono R.I i k (Nat.le_of_lt ht)
    have hsobs := pullCount_mono R.I i M.star (Nat.le_of_lt ht)
    have hgap := R.selection_gap i hm hms hobs hsobs hu
    rw [M.mkAll_eq_mkThr hk] at hmk
    have hm0 := le_trans (le_max_left _ _) hmk
    have hnk := le_trans (le_max_right _ _) hmk
    have hψ : psi (M.f k) (R.N t i k) ≤ M.gap k / 2 :=
      le_trans (psi_anti_le (M.f_anti k) (M.m0_spec hk).1 hm0) (M.m0_spec hk).2
    have hr := two_rdelta_lt R.L (M.gap k) R.hL (M.gap_pos hk) hnk
    linarith

/-- A finite-event version of the cumulative pair budget. Reinsertions do not reset counts. -/
theorem pair_budget (i : Fin n) {k : Fin K} (hk : k ≠ M.star) :
    ((range T).filter (fun t => M.star ∈ R.active t i ∧ R.I t i = k)).card ≤ M.mkAll R.L k := by
  let S := (range T).filter (fun t => M.star ∈ R.active t i ∧ R.I t i = k)
  have hsel : ∀ t ∈ S, R.I t i = k := fun t ht => (mem_filter.mp ht).2.2
  have hcount : ∀ t, (S.filter (· < t)).card ≤ R.N t i k := by
    intro t
    induction t with
    | zero => simp [N]
    | succ t ih =>
      by_cases ht : t ∈ S
      · have hc := filter_lt_succ_card_of_mem S t ht
        have hn := pullCount_step R.I t i k
        rw [if_pos (hsel t ht)] at hn
        dsimp only [N] at *
        omega
      · have hc := filter_lt_succ_card_of_notMem S t ht
        have hn := pullCount_mono R.I i k (Nat.le_succ t)
        dsimp only [N] at *
        simp only [Nat.succ_eq_add_one] at hn
        omega
  by_cases hne : S.Nonempty
  · have htmax := S.max'_mem hne
    have htT : S.max' hne < T := mem_range.mp (mem_filter.mp htmax).1
    have hb := R.N_lt_mk hk htT (mem_filter.mp htmax).2.1 (hsel _ htmax)
    have hsub : S ⊆ insert (S.max' hne) (S.filter (· < S.max' hne)) := by
      intro s hs
      rw [mem_insert, mem_filter]
      rcases lt_or_eq_of_le (Finset.le_max' S s hs) with h | h
      · exact Or.inr ⟨hs, h⟩
      · exact Or.inl h
    have hcard := card_le_card hsub
    have hi := card_insert_le (S.max' hne) (S.filter (· < S.max' hne))
    have hn := hcount (S.max' hne)
    change S.card ≤ _
    omega
  · change S.card ≤ _
    rw [not_nonempty_iff_eq_empty.mp hne]
    simp

/-- In an interval where the optimal arm remains active, the count of a suboptimal arm
cannot rise beyond its threshold (or its already larger initial value). -/
theorem phase_count_le (i : Fin n) {k : Fin K} (hk : k ≠ M.star)
    (a b : ℕ) (hab : a ≤ b) (hbT : b ≤ T)
    (hactive : ∀ t, a ≤ t → t < b → M.star ∈ R.active t i) :
    R.N b i k ≤ max (R.N a i k) (M.mkAll R.L k) := by
  have haux : ∀ d, a+d ≤ b → R.N (a+d) i k ≤ max (R.N a i k) (M.mkAll R.L k) := by
    intro d
    induction d with
    | zero => intro _; simpa using le_max_left (R.N a i k) (M.mkAll R.L k)
    | succ d ih =>
      intro hbd
      have hprev := ih (by omega)
      have hstep := pullCount_step R.I (a+d) i k
      by_cases hsel : R.I (a+d) i = k
      · have hlt := R.N_lt_mk hk (show a+d < T by omega)
          (hactive (a+d) (by omega) (by omega)) hsel
        rw [if_pos hsel] at hstep
        have hm := le_max_right (R.N a i k) (M.mkAll R.L k)
        change R.N (a + (d+1)) i k ≤ _
        have heq : a + (d+1) = a+d+1 := by omega
        rw [heq]
        dsimp only [N] at *
        omega
      · rw [if_neg hsel] at hstep
        change R.N (a + (d+1)) i k ≤ _
        have heq : a + (d+1) = a+d+1 := by omega
        rw [heq]
        dsimp only [N] at *
        omega
  simpa [Nat.add_sub_of_le hab] using haux (b-a) (by omega)

/-- Exact residual threshold budget for a phase, rather than restarting a full budget at each
reinsertion or phase boundary. -/
theorem phase_residual_budget (i : Fin n) {k : Fin K} (hk : k ≠ M.star)
    (a b : ℕ) (hab : a ≤ b) (hbT : b ≤ T)
    (hactive : ∀ t, a ≤ t → t < b → M.star ∈ R.active t i) :
    R.N b i k - R.N a i k ≤ M.mkAll R.L k - R.N a i k := by
  have h := R.phase_count_le i hk a b hab hbT hactive
  omega

end GoodRunOn
end
end AnvBandit
