import AnvBandit.Exponential
import AnvBandit.Regret
import AnvBandit.Greedy

/-!
# Full joint-action exponential benchmark

Finite joint trajectories are represented recursively as lists. The first-round vertex reduction
uses convexity of each *fixed* continuation value, so it does not restrict the optimization domain.
-/

noncomputable section
open scoped BigOperators
open Finset

namespace AnvBandit.ExponentialDP

variable {n K : ℕ}

lemma exists_ofFn_length {α : Type*} (ks : List α) {t : ℕ} (h : ks.length = t) :
    ∃ v : Fin t → α, List.ofFn v = ks := by
  subst t
  exact ⟨ks.get, List.ofFn_get ks⟩

def g (b a eta : Fin K → ℝ) (k : Fin K) (x : ℝ) : ℝ :=
  b k + a k * Real.exp (-(eta k) * x)

/-- Real-valued count increment of a simultaneous joint action. -/
def count (u : Fin n → Fin K) (k : Fin K) : ℝ :=
  ∑ i : Fin n, if u i = k then 1 else 0

/-- Simultaneous reward at the pre-round state. -/
def reward (b a eta : Fin K → ℝ) (m : Fin K → ℝ) (u : Fin n → Fin K) : ℝ :=
  ∑ i : Fin n, g b a eta (u i) (m (u i))

/-- Value of all joint actions, with each trajectory evolving its own public state. -/
def value (b a eta : Fin K → ℝ) (m : Fin K → ℝ) : List (Fin n → Fin K) → ℝ
  | [] => 0
  | u :: us => reward b a eta m u + value b a eta (m + count u) us

lemma g_convex (b a eta : Fin K → ℝ) (ha : ∀ k, 0 ≤ a k) (k : Fin K) :
    ConvexOn ℝ Set.univ (g b a eta k) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ c d hc hd hcd
  have he := convexOn_exp.2 (Set.mem_univ (-(eta k) * x))
    (Set.mem_univ (-(eta k) * y)) hc hd hcd
  simp only [smul_eq_mul] at he ⊢
  have hid : -(eta k) * (c * x + d * y) = c * (-(eta k) * x) + d * (-(eta k) * y) := by ring
  unfold g
  rw [hid]
  have hb : b k = c * b k + d * b k := by
    nlinarith [congrArg (fun z : ℝ => z * b k) hcd]
  nlinarith [mul_le_mul_of_nonneg_left he (ha k), hb]

lemma reward_convex (b a eta : Fin K → ℝ) (ha : ∀ k, 0 ≤ a k)
    (u : Fin n → Fin K) : ConvexOn ℝ Set.univ (fun m => reward b a eta m u) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ c d hc hd hcd
  simp only [reward, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ i : Fin n, g b a eta (u i) (c * x (u i) + d * y (u i)))
      ≤ ∑ i : Fin n, (c * g b a eta (u i) (x (u i)) +
        d * g b a eta (u i) (y (u i))) := by
          apply Finset.sum_le_sum
          intro i _
          exact (g_convex b a eta ha (u i)).2 (Set.mem_univ _) (Set.mem_univ _) hc hd hcd
    _ = c * ∑ i : Fin n, g b a eta (u i) (x (u i)) +
        d * ∑ i : Fin n, g b a eta (u i) (y (u i)) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

lemma value_convex (b a eta : Fin K → ℝ) (ha : ∀ k, 0 ≤ a k)
    (us : List (Fin n → Fin K)) : ConvexOn ℝ Set.univ (fun m => value b a eta m us) := by
  induction us with
  | nil => simpa [value] using (convexOn_const (c := (0 : ℝ)) convex_univ)
  | cons u us ih =>
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ c d hc hd hcd
    have hr := (reward_convex b a eta ha u).2 (Set.mem_univ x) (Set.mem_univ y) hc hd hcd
    have hv := ih.2 (Set.mem_univ (x + count u)) (Set.mem_univ (y + count u)) hc hd hcd
    have hid : c • (x + count u) + d • (y + count u) =
        c • x + d • y + count u := by
      ext k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [congrArg (fun z : ℝ => z * count u k) hcd]
    rw [hid] at hv
    simp only [value, smul_eq_mul] at *
    linarith

/-- Joint action in which all agents use the same arm. -/
def pure (k : Fin K) : Fin n → Fin K := fun _ => k

lemma count_pure (k j : Fin K) : count (pure (n := n) k) j = if k = j then (n : ℝ) else 0 := by
  classical
  by_cases h : k = j <;> simp [count, pure, h]

lemma reward_pure (b a eta : Fin K → ℝ) (m : Fin K → ℝ) (k : Fin K) :
    reward b a eta m (pure (n := n) k) = n * g b a eta k (m k) := by
  simp [reward, pure]

lemma mean_pure_states (hn : 0 < n) (m : Fin K → ℝ) (u : Fin n → Fin K) :
    (∑ i : Fin n, (1 / (n : ℝ)) • (m + count (pure (n := n) (u i)))) = m + count u := by
  classical
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  ext k
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, count_pure]
  have he (i : Fin n) : (1 / (n : ℝ)) * (m k + if u i = k then (n : ℝ) else 0) =
      m k / n + if u i = k then 1 else 0 := by
    by_cases h : u i = k <;> simp [h] <;> field_simp [hn0] <;> ring
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hc : (n : ℝ) * (m k / n) = m k := by field_simp [hn0]
  rw [hc]
  rfl

lemma first_round_vertex (hn : 0 < n) (b a eta : Fin K → ℝ)
    (ha : ∀ k, 0 ≤ a k) (m : Fin K → ℝ) (u : Fin n → Fin K)
    (us : List (Fin n → Fin K)) :
    ∃ k : Fin K, value b a eta m (u :: us) ≤ value b a eta m (pure k :: us) := by
  classical
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  let F : Fin n → ℝ := fun i => value b a eta m (pure (u i) :: us)
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' hne F
  refine ⟨u i, ?_⟩
  have hJ := (value_convex b a eta ha us).map_sum_le
    (t := (Finset.univ : Finset (Fin n)))
    (w := fun _ => 1 / (n : ℝ))
    (p := fun j => m + count (pure (n := n) (u j)))
    (fun _ _ => by positivity)
    (by simp [hn0]) (fun _ _ => Set.mem_univ _)
  rw [mean_pure_states hn m u] at hJ
  simp only [smul_eq_mul] at hJ
  have havg : value b a eta m (u :: us) ≤ ∑ j : Fin n, (1 / (n : ℝ)) * F j := by
    calc
      value b a eta m (u :: us)
        ≤ reward b a eta m u + ∑ j : Fin n,
          (1 / (n : ℝ)) * value b a eta (m + count (pure (u j))) us := by
          simp only [value]
          exact add_le_add le_rfl hJ
      _ = ∑ j : Fin n, (1 / (n : ℝ)) * F j := by
        simp only [F, value, reward_pure, mul_add, Finset.sum_add_distrib]
        congr 1
        unfold reward
        apply Finset.sum_congr rfl
        intro j _
        field_simp
  have hmax : (∑ j : Fin n, (1 / (n : ℝ)) * F j) ≤ F i := by
    calc
      (∑ j : Fin n, (1 / (n : ℝ)) * F j) ≤ ∑ j : Fin n, (1 / (n : ℝ)) * F i := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [← hi]
        exact Finset.le_sup' F (Finset.mem_univ j)
      _ = F i := by simp [hn0]
  exact havg.trans hmax

/-- Every unrestricted joint path has an equally long synchronous path of at least its value. -/
theorem exists_synchronous_dominates (hn : 0 < n) (b a eta : Fin K → ℝ)
    (ha : ∀ k, 0 ≤ a k) (us : List (Fin n → Fin K)) (m : Fin K → ℝ) :
    ∃ ks : List (Fin K), ks.length = us.length ∧
      value b a eta m us ≤ value b a eta m (ks.map (pure (n := n))) := by
  induction us generalizing m with
  | nil => exact ⟨[], rfl, le_rfl⟩
  | cons u us ih =>
    obtain ⟨k, hk⟩ := first_round_vertex hn b a eta ha m u us
    obtain ⟨ks, hlen, hks⟩ := ih (m + count (pure k))
    refine ⟨k :: ks, by simpa using hlen, ?_⟩
    calc
      value b a eta m (u :: us) ≤ value b a eta m (pure k :: us) := hk
      _ ≤ value b a eta m ((k :: ks).map (pure (n := n))) := by
        simp only [List.map_cons, value]
        exact add_le_add le_rfl hks

/-- Cumulative real team count before a finite-indexed round. -/
def preCount {T : ℕ} (u : Fin T → Fin n → Fin K) (t : Fin T) (k : Fin K) : ℝ :=
  ∑ s : Fin T, if s < t then count (u s) k else 0

lemma preCount_zero {T : ℕ} (u : Fin (T+1) → Fin n → Fin K) : preCount u 0 = 0 := by
  ext k
  simp [preCount]

lemma preCount_succ {T : ℕ} (u : Fin (T+1) → Fin n → Fin K) (t : Fin T) :
    preCount u t.succ = count (u 0) + preCount (fun s => u s.succ) t := by
  ext k
  simp [preCount, Fin.sum_univ_succ]

lemma value_ofFn (b a eta : Fin K → ℝ) {T : ℕ}
    (u : Fin T → Fin n → Fin K) (m : Fin K → ℝ) :
    value b a eta m (List.ofFn u) =
      ∑ t : Fin T, reward b a eta (m + preCount u t) (u t) := by
  induction T generalizing m with
  | zero => simp [value]
  | succ T ih =>
    rw [List.ofFn_succ, value, Fin.sum_univ_succ, preCount_zero, add_zero, ih]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    rw [preCount_succ]
    simp only [add_assoc]

lemma preCount_eq_Nfin {T : ℕ} (u : Fin n → Fin T → Fin K) (t : Fin T) (k : Fin K) :
    preCount (fun s i => u i s) t k = ∑ i : Fin n, (Nfin u t i k : ℝ) := by
  classical
  unfold preCount count Nfin
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  by_cases h : s < t
  · simp [h]
  · simp [h]

/-- The recursive joint-path value equals the original paper trajectory value at zero state. -/
lemma value_eq_J1 {T : ℕ} (M : DecayModel n K) (a eta : Fin K → ℝ)
    (hexp : IsExponential M a eta) (u : Fin n → Fin T → Fin K) :
    value M.b a eta 0 (List.ofFn (fun t i => u i t)) = J1 M u := by
  rw [value_ofFn]
  unfold J1 reward
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro i _
  rw [show (0 + preCount (fun s i => u i s) t) (u i t) =
      preCount (fun s i => u i s) t (u i t) by simp]
  rw [preCount_eq_Nfin]
  unfold DecayModel.mean g qeff1
  rw [hexp.2.2 _ _ (by omega)]
  congr 3
  push_cast
  ring

lemma preCount_pure {T : ℕ} (u : Fin T → Fin K) (t : Fin T) :
    preCount (fun s => pure (n := n) (u s)) t (u t) = n * (occ u t : ℝ) := by
  change preCount (fun s (_ : Fin n) => u s) t (u t) = _
  rw [preCount_eq_Nfin (fun (_ : Fin n) s => u s)]
  simp [Nfin, occ]

lemma value_sync_ofFn (b a eta : Fin K → ℝ) {T : ℕ} (u : Fin T → Fin K) :
    value b a eta 0 ((List.ofFn u).map (pure (n := n))) = syncExpVal n b a eta u := by
  rw [List.map_ofFn, value_ofFn]
  unfold syncExpVal
  apply Finset.sum_congr rfl
  intro t _
  dsimp only [Function.comp_def]
  rw [reward_pure]
  simp only [Pi.add_apply, Pi.zero_apply, zero_add, preCount_pure, g, occ]

/-- Full policy-domain reduction: every original joint trajectory is dominated by a
synchronous trajectory, derived from exponential convexity rather than assumed. -/
theorem joint_le_synchronous {T : ℕ} (M : DecayModel n K) (a eta : Fin K → ℝ)
    (hexp : IsExponential M a eta) (u : Fin n → Fin T → Fin K) :
    ∃ v : Fin T → Fin K, J1 M u ≤ syncExpVal n M.b a eta v := by
  have hn : 0 < n := by have := M.two_le_n; omega
  obtain ⟨ks, hlen, hval⟩ := exists_synchronous_dominates hn M.b a eta hexp.1
    (List.ofFn (fun t i => u i t)) 0
  simp only [List.length_ofFn] at hlen
  have hv : ∃ v : Fin T → Fin K, List.ofFn v = ks := exists_ofFn_length ks hlen
  obtain ⟨v, hv⟩ := hv
  refine ⟨v, ?_⟩
  rw [← hv, value_eq_J1 M a eta hexp u, value_sync_ofFn] at hval
  exact hval

/-- The true unrestricted public-fatigue optimum equals the restricted synchronous optimum. -/
theorem Vstar1_eq_expBench {T : ℕ} (M : DecayModel n K) (a eta : Fin K → ℝ)
    (hexp : IsExponential M a eta) :
    Vstar1 (T := T) M = expBench n (by have := M.two_le_K; omega) M.b a eta T := by
  apply le_antisymm
  · unfold Vstar1
    apply Finset.sup'_le
    intro u _
    obtain ⟨v, hv⟩ := joint_le_synchronous M a eta hexp u
    exact hv.trans (Finset.le_sup' (syncExpVal n M.b a eta) (Finset.mem_univ v))
  · unfold expBench
    apply Finset.sup'_le
    intro v _
    have heq : J1 M (fun _ t => v t) = syncExpVal n M.b a eta v := by
      rw [← value_eq_J1 M a eta hexp]
      have hl : (List.ofFn v).map (pure (n := n)) =
          List.ofFn (fun t (_ : Fin n) => v t) := by
        rw [List.map_ofFn]
        rfl
      rw [← hl]
      exact value_sync_ofFn M.b a eta v
    rw [← heq]
    exact Finset.le_sup' (J1 M) (Finset.mem_univ _)

/-- Proposition A.4's full benchmark equality. The left side optimizes all joint actions. -/
theorem proposition_A_4_full {T : ℕ} (M : DecayModel n K) (a eta : Fin K → ℝ)
    (hexp : IsExponential M a eta) :
    Vstar1 (T := T) M = greedyVal n (by have := M.two_le_K; omega) M.b a eta T := by
  rw [Vstar1_eq_expBench M a eta hexp]
  exact AnvBandit.proposition_A_4 n _ M.b a eta hexp.1 hexp.2.1 T

/-- Current and future synchronous marginal sequence at state `m`. -/
def stateMarg (b a eta : Fin K → ℝ) (m : Fin K → ℝ) (k : Fin K) (r : ℕ) : ℝ :=
  (n : ℝ) * g b a eta k (m k + n * r)

lemma shift_stateMarg (b a eta : Fin K → ℝ) (m : Fin K → ℝ) (k : Fin K) :
    Greedy.shift (stateMarg (n := n) b a eta m) k =
      stateMarg (n := n) b a eta (m + count (pure (n := n) k)) := by
  classical
  funext j r
  by_cases h : j = k
  · subst j
    simp only [Greedy.shift, ↓reduceIte, stateMarg, Pi.add_apply, count_pure,
      Nat.cast_add, Nat.cast_one]
    congr 2
    ring
  · simp [Greedy.shift, stateMarg, count_pure, h, Ne.symm h]

lemma stateMarg_antitone (b a eta : Fin K → ℝ) (m : Fin K → ℝ)
    (ha : ∀ k, 0 ≤ a k) (heta : ∀ k, 0 < eta k) :
    ∀ k, Antitone (stateMarg (n := n) b a eta m k) := by
  intro k r s hrs
  unfold stateMarg g
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hcount : (n : ℝ) * r ≤ n * s := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hrs) hn
  have hexp : Real.exp (-(eta k) * (m k + n * s)) ≤
      Real.exp (-(eta k) * (m k + n * r)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [heta k]
  have hh := mul_le_mul_of_nonneg_left hexp (ha k)
  apply mul_le_mul_of_nonneg_left _ hn
  linarith

lemma value_sync_eq_payoff (b a eta : Fin K → ℝ) (m : Fin K → ℝ)
    (ks : List (Fin K)) :
    value b a eta m (ks.map (pure (n := n))) =
      Greedy.payoff (stateMarg (n := n) b a eta m) ks := by
  induction ks generalizing m with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.map_cons, value, Greedy.payoff, reward_pure, ih, shift_stateMarg]
    simp [stateMarg]

/-- The implemented choice maximizes the paper's current mean, not a look-ahead value. -/
lemma stateMarg_pick_max (hn : 0 < n) (hK : 0 < K) (b a eta : Fin K → ℝ)
    (m : Fin K → ℝ) (k : Fin K) :
    g b a eta k (m k) ≤
      g b a eta (Greedy.pick hK (stateMarg (n := n) b a eta m))
        (m (Greedy.pick hK (stateMarg (n := n) b a eta m))) := by
  have h := Greedy.pick_max hK (stateMarg (n := n) b a eta m) k
  simp only [stateMarg, Nat.cast_zero, mul_zero, add_zero] at h
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  nlinarith

/-- A recursively defined synchronous greedy policy attains the original full joint optimum.
At each step `Greedy.pick` compares only current marginals; future optimal values are not inputs. -/
theorem greedy_policy_attains {T : ℕ} (M : DecayModel n K) (a eta : Fin K → ℝ)
    (hexp : IsExponential M a eta) :
    Vstar1 (T := T) M = value M.b a eta 0
      ((Greedy.policy (by have := M.two_le_K; omega)
        (stateMarg (n := n) M.b a eta 0) T).map (pure (n := n))) := by
  classical
  let hK : 0 < K := by have := M.two_le_K; omega
  let ks := Greedy.policy hK (stateMarg (n := n) M.b a eta 0) T
  have hlen : ks.length = T := Greedy.policy_length hK _ T
  change Vstar1 (T := T) M = value M.b a eta 0 (ks.map (pure (n := n)))
  apply le_antisymm
  · unfold Vstar1
    apply Finset.sup'_le
    intro u _
    obtain ⟨v, hv⟩ := joint_le_synchronous M a eta hexp u
    rw [← value_sync_ofFn, value_sync_eq_payoff] at hv
    have hg := Greedy.payoff_le_policy hK (stateMarg (n := n) M.b a eta 0)
      (stateMarg_antitone M.b a eta 0 hexp.1 hexp.2.1) (List.ofFn v)
    simp only [List.length_ofFn] at hg
    rw [value_sync_eq_payoff]
    exact hv.trans hg
  · have hv : ∃ v : Fin T → Fin K, List.ofFn v = ks := exists_ofFn_length ks hlen
    obtain ⟨v, hv⟩ := hv
    rw [← hv, value_sync_ofFn]
    have heq : J1 M (fun _ t => v t) = syncExpVal n M.b a eta v := by
      rw [← value_eq_J1 M a eta hexp]
      have hl : (List.ofFn v).map (pure (n := n)) =
          List.ofFn (fun t (_ : Fin n) => v t) := by
        rw [List.map_ofFn]
        rfl
      rw [← hl]
      exact value_sync_ofFn M.b a eta v
    rw [← heq]
    exact Finset.le_sup' (J1 M) (Finset.mem_univ _)

end AnvBandit.ExponentialDP
