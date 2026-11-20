import AnvBandit.Regret

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# The serial benchmark `V^ser` and the upper half of the Lemma A.3 sandwich

`V^ser(u)` is the best value of a *serial* allocation `m : Fin K → ℕ` with `∑_k m_k = u`
(equation (2.6)/(A.3)).  We define it as the maximum of `∑_k F_k(m_k)` over the finite set of
compositions of `u`, and prove

* `Vser_le`, `Vser_le_Fkstar_add_Db`: `V^ser(u) ≤ F_{k⋆}(u) + D_b` (Proposition A.5's serial bound);
* `Vser_le_serialAlloc`-free monotonicity for use below;
* `Vstar1_le_Vser`: `V^{⋆,1}_T ≤ V^ser(nT) + (n−1)A` — the upper half of the Lemma A.3 sandwich,
  via the zero-tolerant batching inequality `syncVal_sub_serialVal_le'`.
-/

noncomputable section
open scoped BigOperators
open Finset

namespace AnvBandit

variable {n K : ℕ}

/-- The finite set of compositions of `u` as functions `Fin K → Fin (u+1)`. -/
def comps (K u : ℕ) : Finset (Fin K → Fin (u + 1)) :=
  (Finset.univ : Finset (Fin K → Fin (u + 1))).filter (fun f => ∑ k, (f k : ℕ) = u)

lemma comps_nonempty (M : DecayModel n K) (u : ℕ) : (comps K u).Nonempty := by
  haveI : NeZero K := ⟨by have := M.two_le_K; omega⟩
  refine ⟨fun k => if k = 0 then ⟨u, Nat.lt_succ_self u⟩ else 0, ?_⟩
  rw [comps, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [Finset.sum_eq_single (0 : Fin K)]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ (0 : Fin K)) h

/-- `V^ser(u) = max{ ∑_k F_k(m_k) : ∑_k m_k = u }`. -/
def Vser (M : DecayModel n K) (u : ℕ) : ℝ :=
  (comps K u).sup' (comps_nonempty M u) (fun f => M.serialAlloc (fun k => (f k : ℕ)))

/-- Every serial allocation of total `u` is bounded by `V^ser(u)`. -/
lemma le_Vser (M : DecayModel n K) {u : ℕ} {m : Fin K → ℕ} (h : ∑ k, m k = u) :
    M.serialAlloc m ≤ Vser M u := by
  have hm : ∀ k, m k ≤ u := by
    intro k
    have := Finset.single_le_sum (f := m) (fun k _ => Nat.zero_le _) (Finset.mem_univ k)
    omega
  have hmem : (fun k => (⟨m k, by have := hm k; omega⟩ : Fin (u + 1))) ∈ comps K u := by
    rw [comps, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [Finset.mem_univ, true_and]
    rw [← h]
  have hle := Finset.le_sup' (s := comps K u)
    (f := fun f => M.serialAlloc (fun k => (f k : ℕ))) hmem
  rw [show (⟨_, hmem⟩ : (comps K u).Nonempty) = comps_nonempty M u from Subsingleton.elim _ _] at hle
  simpa [Vser] using hle

/-- `V^ser(u) ≤ F_{k⋆}(u) + D_b`. -/
lemma Vser_le_Fkstar_add_Db (M : DecayModel n K) (u : ℕ) :
    Vser M u ≤ M.Fk M.star u + M.Db := by
  unfold Vser
  refine Finset.sup'_le _ _ (fun f hf => ?_)
  rw [comps, Finset.mem_filter] at hf
  exact M.serialAlloc_le_Fkstar_add_Db (fun k => (f k : ℕ)) hf.2

namespace DecayModel

variable (M : DecayModel n K)

/-- Zero-tolerant batching error: `syncVal − serialVal ≤ (n−1)·v(c+1)`. -/
lemma syncVal_sub_serialVal_le' (v : ℕ → ℝ) (hv0 : ∀ s, 0 ≤ v s) (hvanti : Antitone v) (n : ℕ) :
    ∀ (l : List ℕ) (c : ℕ), (∀ x ∈ l, x ≤ n) →
      syncVal v c l - serialVal v c l ≤ (n - 1 : ℕ) * v (c + 1)
  | [], c, _ => by
    simp only [syncVal_nil, serialVal_nil, sub_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (hv0 (c + 1))
  | x :: xs, c, hxn => by
    have hxs : ∀ y ∈ xs, y ≤ n := fun y hy => hxn y (by simp [hy])
    rw [syncVal_cons, serialVal_cons]
    have hih := syncVal_sub_serialVal_le' v hv0 hvanti n xs (c + x) hxs
    rcases Nat.eq_zero_or_pos x with hx | hx
    · subst hx
      simp only [Nat.cast_zero, zero_mul, zero_add, Nat.add_zero, Finset.range_zero,
        Finset.sum_empty, add_zero, sub_zero]
      exact hih
    · have hb := batchErr_upper hv0 hvanti (c := c) hx
      have hxn' : x ≤ n := hxn x (by simp)
      have hcastx : ((x - 1 : ℕ) : ℝ) = (x : ℝ) - 1 := by rw [Nat.cast_sub hx]; norm_num
      have hcastn : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (le_trans hx hxn')]; norm_num
      have hnx : ((x - 1 : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
        have : x - 1 ≤ n - 1 := by omega
        exact_mod_cast this
      have h1 : v (c + x + 1) ≤ v (c + x) := hvanti (by omega)
      have h2 : v (c + x) ≤ v (c + 1) := hvanti (by omega)
      have h3 : 0 ≤ v (c + 1) - v (c + x) := by linarith
      have hx1 : (0:ℝ) ≤ (x:ℝ) - 1 := by
        have : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
        linarith
      nlinarith [hb, hih, h1, h2, h3, hv0 (c + x + 1), hv0 (c + 1), hcastx, hcastn, hnx,
        mul_nonneg hx1 h3]

/-- Zero-tolerant version of (A.2): `syncAlloc b − serialAlloc (counts) ≤ (n−1)·A`. -/
lemma syncAlloc_sub_serialAlloc_le' (b : Fin K → List ℕ)
    (hxn : ∀ k, ∀ x ∈ b k, x ≤ n) :
    M.syncAlloc b - M.serialAlloc (fun k => (b k).sum) ≤ (n - 1 : ℕ) * M.A := by
  rw [M.syncAlloc_sub_serialAlloc]
  calc ∑ k, (syncVal (M.f k) 0 (b k) - serialVal (M.f k) 0 (b k))
      ≤ ∑ _k : Fin K, (n - 1 : ℕ) * M.f _k 1 :=
        Finset.sum_le_sum fun k _ =>
          DecayModel.syncVal_sub_serialVal_le' (M.f k) (M.f_nonneg k) (M.f_anti k) n (b k) 0 (hxn k)
    _ = (n - 1 : ℕ) * M.A := by
        simp only [A, ak]; rw [Finset.mul_sum]

end DecayModel

/-- **Upper half of the Lemma A.3 sandwich**: `V^{⋆,1}_T ≤ V^ser(nT) + (n−1)·A`. -/
theorem Vstar1_le_Vser {T : ℕ} (M : DecayModel n K) :
    Vstar1 (T := T) M ≤ Vser M (n * T) + (n - 1 : ℕ) * M.A := by
  rw [Vstar1]
  refine Finset.sup'_le _ _ (fun u _ => ?_)
  rw [J1_eq_sync]
  have h1 : M.syncAlloc (fun k => blist u k)
      ≤ M.serialAlloc (fun k => (blist u k).sum) + (n - 1 : ℕ) * M.A := by
    have := M.syncAlloc_sub_serialAlloc_le' (fun k => blist u k) (fun k => blist_le u k)
    linarith
  have h2 : M.serialAlloc (fun k => (blist u k).sum) = M.serialAlloc (fun k => Mtot u k) := by
    exact Finset.sum_congr rfl fun k _ => by simp only [blist_sum]
  rw [h2] at h1
  have h3 : M.serialAlloc (fun k => Mtot u k) ≤ Vser M (n * T) :=
    le_Vser M (sum_Mtot u)
  linarith

end AnvBandit
