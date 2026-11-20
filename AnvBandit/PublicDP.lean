import AnvBandit.Benchmark

/-! # Exact public-fatigue Bellman recursion over all batch allocations -/
noncomputable section
open scoped BigOperators
open Finset
namespace AnvBandit.PublicDP
variable {n K : ℕ}

def count (u : Fin n → Fin K) (k : Fin K) : ℕ :=
  (Finset.univ.filter (fun i => u i = k)).card

def reward (M : DecayModel n K) (m : Fin K → ℕ) (u : Fin n → Fin K) : ℝ :=
  ∑ i, M.mean (u i) (1 + m (u i))

def path (M : DecayModel n K) (m : Fin K → ℕ) : List (Fin n → Fin K) → ℝ
  | [] => 0
  | u :: us => reward M m u + path M (m + count u) us

/-- Joint-action Bellman form; `W_batch` below proves precisely the paper's batch form. -/
def W (M : DecayModel n K) : ℕ → (Fin K → ℕ) → ℝ
  | 0, _ => 0
  | r+1, m => Finset.univ.sup' ⟨fun _ => M.star, Finset.mem_univ _⟩
      (fun u => reward M m u + W M r (m + count u))

lemma path_le_W (M : DecayModel n K) (us : List (Fin n → Fin K)) (m : Fin K → ℕ) :
    path M m us ≤ W M us.length m := by
  induction us generalizing m with
  | nil => exact le_rfl
  | cons u us ih =>
    have h := ih (m + count u)
    calc
      path M m (u :: us) ≤ reward M m u + W M us.length (m + count u) :=
        add_le_add le_rfl h
      _ ≤ W M (u :: us).length m :=
        Finset.le_sup' (fun u => reward M m u + W M us.length (m + count u)) (Finset.mem_univ u)

lemma W_attained (M : DecayModel n K) (r : ℕ) (m : Fin K → ℕ) :
    ∃ us : List (Fin n → Fin K), us.length = r ∧ path M m us = W M r m := by
  induction r generalizing m with
  | zero => exact ⟨[], rfl, rfl⟩
  | succ r ih =>
    obtain ⟨u, _, hu⟩ := Finset.exists_mem_eq_sup'
      (s := Finset.univ) ⟨fun _ => M.star, Finset.mem_univ _⟩
      (fun u => reward M m u + W M r (m + count u))
    obtain ⟨us, hlen, hv⟩ := ih (m + count u)
    refine ⟨u :: us, by simp [hlen], ?_⟩
    simp only [path, hv, W]
    exact hu.symm

def preCount {T : ℕ} (u : Fin T → Fin n → Fin K) (t : Fin T) (k : Fin K) : ℕ :=
  ∑ s : Fin T, if s < t then count (u s) k else 0

lemma preCount_zero {T : ℕ} (u : Fin (T+1) → Fin n → Fin K) : preCount u 0 = 0 := by
  ext k
  simp [preCount]

lemma preCount_succ {T : ℕ} (u : Fin (T+1) → Fin n → Fin K) (t : Fin T) :
    preCount u t.succ = count (u 0) + preCount (fun s => u s.succ) t := by
  ext k
  simp [preCount, Fin.sum_univ_succ]

lemma path_ofFn (M : DecayModel n K) {T : ℕ}
    (u : Fin T → Fin n → Fin K) (m : Fin K → ℕ) :
    path M m (List.ofFn u) = ∑ t : Fin T, reward M (m + preCount u t) (u t) := by
  induction T generalizing m with
  | zero => simp [path]
  | succ T ih =>
    rw [List.ofFn_succ, path, Fin.sum_univ_succ, preCount_zero, add_zero, ih]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    rw [preCount_succ]
    simp only [add_assoc]

lemma preCount_eq_Nfin {T : ℕ} (u : Fin n → Fin T → Fin K) (t : Fin T) (k : Fin K) :
    preCount (fun s i => u i s) t k = ∑ i : Fin n, Nfin u t i k := by
  classical
  unfold preCount count Nfin
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  by_cases h : s < t <;> simp [h]

lemma path_eq_J1 (M : DecayModel n K) {T : ℕ} (u : Fin n → Fin T → Fin K) :
    path M 0 (List.ofFn (fun t i => u i t)) = J1 M u := by
  rw [path_ofFn]
  unfold J1 reward qeff1
  simp only [Pi.add_apply, Pi.zero_apply, zero_add, preCount_eq_Nfin]

/-- The Bellman value is exactly the unrestricted finite-trajectory benchmark. -/
theorem W_eq_Vstar1 (M : DecayModel n K) (T : ℕ) : W M T 0 = Vstar1 (T := T) M := by
  classical
  apply le_antisymm
  · obtain ⟨us, hlen, hv⟩ := W_attained M T 0
    have hlist : ∃ v : Fin T → (Fin n → Fin K), List.ofFn v = us := by
      subst T
      exact ⟨us.get, List.ofFn_get us⟩
    obtain ⟨v, hvlist⟩ := hlist
    rw [← hv, ← hvlist, path_eq_J1 M (fun i t => v t i)]
    exact Finset.le_sup' (J1 M) (Finset.mem_univ _)
  · unfold Vstar1
    apply Finset.sup'_le
    intro u _
    rw [← path_eq_J1 M u]
    simpa only [List.length_ofFn] using path_le_W M (List.ofFn (fun t i => u i t)) 0

lemma count_total (u : Fin n → Fin K) : ∑ k : Fin K, count u k = n := by
  classical
  simp only [count, Finset.card_filter]
  rw [Finset.sum_comm]
  simp

lemma reward_eq_batch (M : DecayModel n K) (m : Fin K → ℕ) (u : Fin n → Fin K) :
    reward M m u = ∑ k : Fin K, (count u k : ℝ) * M.mean k (1 + m k) := by
  classical
  unfold reward
  rw [← Finset.sum_fiberwise_of_maps_to (g := u) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro k _
  rw [show (∑ i ∈ Finset.univ.filter (fun i => u i = k), M.mean (u i) (1 + m (u i))) =
      ∑ _i ∈ Finset.univ.filter (fun i => u i = k), M.mean k (1 + m k) by
    apply Finset.sum_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]]
  simp [count]

/-- Equation (A.3), with every nonnegative integer batch vector of total `n` allowed.
The `Fin (n+1)` representation is exact because the total constrains every coordinate. -/
theorem W_batch (M : DecayModel n K) (r : ℕ) (m : Fin K → ℕ) :
    W M (r+1) m = (comps K n).sup' (comps_nonempty M n)
      (fun x => (∑ k : Fin K, (x k : ℝ) * M.mean k (1 + m k)) +
        W M r (m + fun k => (x k : ℕ))) := by
  classical
  apply le_antisymm
  · change Finset.univ.sup' ⟨fun _ => M.star, Finset.mem_univ _⟩
      (fun u : Fin n → Fin K => reward M m u + W M r (m + count u)) ≤ _
    apply Finset.sup'_le
    intro u _
    have hb (k : Fin K) : count u k < n + 1 := by
      have h := Finset.single_le_sum (f := count u) (fun k _ => Nat.zero_le _) (Finset.mem_univ k)
      rw [count_total] at h
      omega
    let x : Fin K → Fin (n+1) := fun k => ⟨count u k, hb k⟩
    have hx : x ∈ comps K n := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, count_total u⟩
    rw [reward_eq_batch]
    simpa only [x] using (Finset.le_sup' (fun x : Fin K → Fin (n+1) =>
      (∑ k, (x k : ℝ) * M.mean k (1 + m k)) + W M r (m + fun k => (x k : ℕ))) hx)
  · apply Finset.sup'_le
    intro x hx
    obtain ⟨u, hu⟩ := exists_sched_with_counts (fun k => (x k : ℕ)) n (Finset.mem_filter.mp hx).2
    have hc : count u = fun k => (x k : ℕ) := funext hu
    have hv : reward M m u = ∑ k : Fin K, (x k : ℝ) * M.mean k (1 + m k) := by
      rw [reward_eq_batch, hc]
    rw [← hv, ← hc]
    exact Finset.le_sup' (fun u => reward M m u + W M r (m + count u)) (Finset.mem_univ u)

end AnvBandit.PublicDP
