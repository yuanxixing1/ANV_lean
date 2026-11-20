import AnvBandit.Exponential

/-!
# Sequential greedy merging of non-increasing marginal sequences

This module constructs a policy, rather than defining its value as an optimum.
-/
noncomputable section
open scoped BigOperators
open Finset
namespace AnvBandit.Greedy
variable {K : ℕ}

/-- Choose a maximizer of the current marginal. Any tie resolution is optimal. -/
def pick (hK : 0 < K) (v : Fin K → ℕ → ℝ) : Fin K :=
  Classical.choose (Finset.exists_mem_eq_sup'
    (s := Finset.univ) ⟨⟨0, hK⟩, Finset.mem_univ _⟩ (fun k => v k 0))

lemma pick_max (hK : 0 < K) (v : Fin K → ℕ → ℝ) (k : Fin K) :
    v k 0 ≤ v (pick hK v) 0 := by
  have h := Classical.choose_spec (Finset.exists_mem_eq_sup'
    (s := Finset.univ) ⟨⟨0, hK⟩, Finset.mem_univ _⟩ (fun k => v k 0))
  unfold pick
  rw [← h.2]
  exact Finset.le_sup' (fun j => v j 0) (Finset.mem_univ k)

/-- Consume one marginal of arm `k`, leaving other sequences unchanged. -/
def shift (v : Fin K → ℕ → ℝ) (k : Fin K) (j : Fin K) (r : ℕ) : ℝ :=
  v j (r + if j = k then 1 else 0)

lemma shift_antitone (v : Fin K → ℕ → ℝ) (hv : ∀ k, Antitone (v k)) (k : Fin K) :
    ∀ j, Antitone (shift v k j) := by
  intro j r s hrs
  exact hv j (Nat.add_le_add_right hrs _)

/-- Actual recursive greedy arm sequence, using only current marginals. -/
def policy (hK : 0 < K) (v : Fin K → ℕ → ℝ) : ℕ → List (Fin K)
  | 0 => []
  | t+1 => pick hK v :: policy hK (shift v (pick hK v)) t

/-- Path payoff computed by consuming each selected arm's current marginal. -/
def payoff (v : Fin K → ℕ → ℝ) : List (Fin K) → ℝ
  | [] => 0
  | k :: ks => v k 0 + payoff (shift v k) ks

lemma policy_length (hK : 0 < K) (v : Fin K → ℕ → ℝ) (t : ℕ) :
    (policy hK v t).length = t := by
  induction t generalizing v with
  | zero => rfl
  | succ t ih => simp [policy, ih]

/-- Sum of the initial `q k` marginals of each arm. -/
def allocation (v : Fin K → ℕ → ℝ) (q : Fin K → ℕ) : ℝ :=
  ∑ k : Fin K, ∑ r ∈ Finset.range (q k), v k r

def remove (q : Fin K → ℕ) (k : Fin K) : Fin K → ℕ :=
  Function.update q k (q k - 1)

lemma remove_total (q : Fin K → ℕ) (k : Fin K) (hk : 0 < q k) :
    (∑ j : Fin K, remove q k j) + 1 = ∑ j : Fin K, q j := by
  classical
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k),
      ← Finset.sum_erase_add Finset.univ q (Finset.mem_univ k)]
  have he : (∑ j ∈ (Finset.univ.erase k), remove q k j) =
      ∑ j ∈ (Finset.univ.erase k), q j := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [remove, (Finset.mem_erase.mp hj).1]
  rw [he]
  simp only [remove, Function.update_self]
  omega

lemma allocation_remove_first (v : Fin K → ℕ → ℝ) (q : Fin K → ℕ)
    (k : Fin K) (hk : 0 < q k) :
    allocation v q = v k 0 + allocation (shift v k) (remove q k) := by
  classical
  unfold allocation
  rw [← Finset.sum_erase_add Finset.univ (fun j => ∑ r ∈ Finset.range (q j), v j r) (Finset.mem_univ k),
      ← Finset.sum_erase_add Finset.univ (fun j => ∑ r ∈ Finset.range (remove q k j), shift v k j r) (Finset.mem_univ k)]
  have he : (∑ j ∈ Finset.univ.erase k, ∑ r ∈ Finset.range (remove q k j), shift v k j r) =
      ∑ j ∈ Finset.univ.erase k, ∑ r ∈ Finset.range (q j), v j r := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [remove, shift, (Finset.mem_erase.mp hj).1]
  rw [he]
  have hq : q k = (q k - 1) + 1 := by omega
  conv_lhs => rw [hq]
  rw [Finset.sum_range_succ']
  simp only [remove, Function.update_self, shift, ↓reduceIte, Nat.add_comm]
  ring

lemma allocation_remove_last (v : Fin K → ℕ → ℝ) (q : Fin K → ℕ)
    (k : Fin K) (hk : 0 < q k) :
    allocation v q = allocation v (remove q k) + v k (q k - 1) := by
  classical
  unfold allocation
  rw [← Finset.sum_erase_add Finset.univ (fun j => ∑ r ∈ Finset.range (q j), v j r) (Finset.mem_univ k),
      ← Finset.sum_erase_add Finset.univ (fun j => ∑ r ∈ Finset.range (remove q k j), v j r) (Finset.mem_univ k)]
  have he : (∑ j ∈ Finset.univ.erase k, ∑ r ∈ Finset.range (remove q k j), v j r) =
      ∑ j ∈ Finset.univ.erase k, ∑ r ∈ Finset.range (q j), v j r := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [remove, (Finset.mem_erase.mp hj).1]
  rw [he]
  have hq : q k = (q k - 1) + 1 := by omega
  conv_lhs => rw [hq]
  rw [Finset.sum_range_succ]
  simp only [remove, Function.update_self]
  ring

lemma allocation_shift_of_zero (v : Fin K → ℕ → ℝ) (q : Fin K → ℕ)
    (k : Fin K) (hk : q k = 0) : allocation (shift v k) q = allocation v q := by
  classical
  unfold allocation
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : j = k
  · subst j; simp [hk]
  · simp [shift, h]

/-- Exchange one selected marginal against the largest currently available marginal. -/
lemma exchange (hK : 0 < K) (v : Fin K → ℕ → ℝ) (hv : ∀ k, Antitone (v k))
    (q : Fin K → ℕ) {t : ℕ} (hq : ∑ k, q k = t+1) :
    ∃ q' : Fin K → ℕ, (∑ k, q' k) = t ∧
      allocation v q ≤ v (pick hK v) 0 + allocation (shift v (pick hK v)) q' := by
  classical
  let k := pick hK v
  by_cases hk : 0 < q k
  · refine ⟨remove q k, by have := remove_total q k hk; omega, ?_⟩
    exact le_of_eq (allocation_remove_first v q k hk)
  · have hk0 : q k = 0 := by omega
    have hex : ∃ j : Fin K, 0 < q j := by
      by_contra h
      push_neg at h
      have hz : ∑ j : Fin K, q j = 0 := Finset.sum_eq_zero fun j _ => by have := h j; omega
      omega
    obtain ⟨j, hj⟩ := hex
    have hjk : j ≠ k := by intro h; subst j; omega
    refine ⟨remove q j, by have := remove_total q j hj; omega, ?_⟩
    have hz : remove q j k = 0 := by simp [remove, Ne.symm hjk, hk0]
    rw [allocation_shift_of_zero v (remove q j) k hz]
    rw [allocation_remove_last v q j hj]
    have hm := (hv j (Nat.zero_le (q j - 1))).trans (pick_max hK v j)
    linarith

/-- Recursive greedy dominates every count allocation with the same number of selections. -/
theorem allocation_le_greedy (hK : 0 < K) (v : Fin K → ℕ → ℝ)
    (hv : ∀ k, Antitone (v k)) (t : ℕ) (q : Fin K → ℕ) (hq : ∑ k, q k = t) :
    allocation v q ≤ payoff v (policy hK v t) := by
  induction t generalizing v q with
  | zero =>
    have hz (k : Fin K) : q k = 0 := by
      have := Finset.single_le_sum (f := q) (fun j _ => Nat.zero_le _) (Finset.mem_univ k)
      omega
    simp [allocation, hz, policy, payoff]
  | succ t ih =>
    obtain ⟨q', hq', hle⟩ := exchange hK v hv q hq
    have hi := ih (shift v (pick hK v)) (shift_antitone v hv _) q' hq'
    simp only [policy, payoff]
    linarith

def counts : List (Fin K) → Fin K → ℕ
  | [], _ => 0
  | j :: js, k => counts js k + if j = k then 1 else 0

lemma counts_total (ks : List (Fin K)) : ∑ k : Fin K, counts ks k = ks.length := by
  classical
  induction ks with
  | nil => simp [counts]
  | cons k ks ih => simp [counts, Finset.sum_add_distrib, ih]

lemma counts_remove_cons (k : Fin K) (ks : List (Fin K)) :
    remove (counts (k :: ks)) k = counts ks := by
  classical
  funext j
  by_cases h : j = k
  · subst j; simp [remove, counts]
  · simp [remove, counts, h, Ne.symm h]

lemma payoff_eq_allocation (v : Fin K → ℕ → ℝ) (ks : List (Fin K)) :
    payoff v ks = allocation v (counts ks) := by
  classical
  induction ks generalizing v with
  | nil => simp [payoff, allocation, counts]
  | cons k ks ih =>
    have hk : 0 < counts (k :: ks) k := by simp [counts]
    rw [allocation_remove_first v (counts (k :: ks)) k hk, counts_remove_cons,
      payoff, ih]

/-- The constructed greedy policy dominates every arm sequence of the same horizon. -/
theorem payoff_le_policy (hK : 0 < K) (v : Fin K → ℕ → ℝ)
    (hv : ∀ k, Antitone (v k)) (ks : List (Fin K)) :
    payoff v ks ≤ payoff v (policy hK v ks.length) := by
  rw [payoff_eq_allocation]
  exact allocation_le_greedy hK v hv ks.length (counts ks) (counts_total ks)

/-- Finite-horizon Bellman recursion over every legal next arm. -/
def dp (hK : 0 < K) (v : Fin K → ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | t+1 => Finset.univ.sup' ⟨⟨0, hK⟩, Finset.mem_univ _⟩
      (fun k => v k 0 + dp hK (shift v k) t)

/-- The Bellman recursion equals the value of the constructed greedy policy. -/
theorem dp_eq_policy (hK : 0 < K) (v : Fin K → ℕ → ℝ)
    (hv : ∀ k, Antitone (v k)) (t : ℕ) :
    dp hK v t = payoff v (policy hK v t) := by
  induction t generalizing v with
  | zero => rfl
  | succ t ih =>
    apply le_antisymm
    · unfold dp
      apply Finset.sup'_le
      intro k _
      rw [ih (shift v k) (shift_antitone v hv k)]
      have h := payoff_le_policy hK v hv (k :: policy hK (shift v k) t)
      simpa only [List.length_cons, policy_length, payoff] using h
    · rw [policy, payoff, ← ih (shift v (pick hK v)) (shift_antitone v hv _)]
      exact Finset.le_sup' (fun k => v k 0 + dp hK (shift v k) t)
        (Finset.mem_univ (pick hK v))

end AnvBandit.Greedy
