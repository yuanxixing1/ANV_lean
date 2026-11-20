import AnvBandit.Model

set_option linter.unusedVariables false

/-!
# The batch/serial comparison inequality (Lemma A.3, equation (A.4))

Under public fatigue the agents pull in synchronous batches (each round each arm is pulled by a
whole batch `x_j ≤ n` of agents).  For a nonnegative, nonincreasing value sequence `v`, the value
of a synchronous schedule (`syncVal`) and of the corresponding serial schedule (`serialVal`) differ
by at most `(n−1)·v(1)`:

  `0 ≤ syncVal v 0 xs − serialVal v 0 xs ≤ (n−1) * v (0+1)`.

This is the paper's inequality (A.4), the key ingredient of
`V^{⋆,1}_T ≤ V^ser(nT) + (n−1)A`.
-/

noncomputable section
open scoped BigOperators Topology
open Filter Finset

namespace AnvBandit

/-- Synchronous value: batches `x :: xs` chosen at counts `c, c+x, …`. -/
def syncVal (v : ℕ → ℝ) : ℕ → List ℕ → ℝ
  | _, [] => 0
  | c, x :: xs => (x : ℝ) * v (c + 1) + syncVal v (c + x) xs

/-- Serial value: `∑_{s=1}^{m} v(s)` where `m = xs.sum`, but starting from offset `c`. -/
def serialVal (v : ℕ → ℝ) (c : ℕ) (xs : List ℕ) : ℝ :=
  ∑ s ∈ Finset.range xs.sum, v (c + s + 1)

@[simp] lemma syncVal_nil (v : ℕ → ℝ) (c : ℕ) : syncVal v c [] = 0 := rfl

lemma syncVal_cons (v : ℕ → ℝ) (c x : ℕ) (xs : List ℕ) :
    syncVal v c (x :: xs) = (x : ℝ) * v (c + 1) + syncVal v (c + x) xs := rfl

@[simp] lemma serialVal_nil (v : ℕ → ℝ) (c : ℕ) : serialVal v c [] = 0 := by simp [serialVal]

lemma serialVal_cons (v : ℕ → ℝ) (c x : ℕ) (xs : List ℕ) :
    serialVal v c (x :: xs)
      = (∑ s ∈ Finset.range x, v (c + s + 1)) + serialVal v (c + x) xs := by
  simp only [serialVal, List.sum_cons]
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  omega

/-- Per-batch upper bound: a batch of size `x` at count `c` costs at most
`(x−1)·(v(c+1) − v(c+x))` relative to serial pulling. -/
lemma batchErr_upper {v : ℕ → ℝ} (hv0 : ∀ s, 0 ≤ v s) (hvanti : Antitone v)
    {c x : ℕ} (hx : 1 ≤ x) :
    (x : ℝ) * v (c + 1) - (∑ s ∈ Finset.range x, v (c + s + 1))
      ≤ (x - 1 : ℕ) * (v (c + 1) - v (c + x)) := by
  have hsum : v (c + 1) + (x - 1 : ℕ) * v (c + x) ≤ ∑ s ∈ Finset.range x, v (c + s + 1) := by
    have hsplit : ∑ s ∈ Finset.range x, v (c + s + 1)
        = v (c + 1) + ∑ s ∈ Finset.range (x - 1), v (c + (s + 1) + 1) := by
      have hx' : x = (x - 1) + 1 := (Nat.succ_pred_eq_of_pos (by omega : 0 < x)).symm
      conv_lhs => rw [hx']
      rw [Finset.sum_range_succ']
      simp only [Nat.add_zero]
      exact add_comm _ _
    rw [hsplit]
    gcongr
    calc ∑ s ∈ Finset.range (x - 1), v (c + (s + 1) + 1)
        ≥ ∑ _s ∈ Finset.range (x - 1), v (c + x) := by
          apply Finset.sum_le_sum; intro s hs
          have := Finset.mem_range.mp hs
          exact hvanti (by omega)
      _ = (x - 1 : ℕ) * v (c + x) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hcast : ((x - 1 : ℕ) : ℝ) = (x : ℝ) - 1 := by rw [Nat.cast_sub hx]; norm_num
  rw [hcast] at hsum
  rw [hcast]
  nlinarith [hsum]

/-- Lemma A.3: the serial value never exceeds the synchronous value. -/
lemma serialVal_le_syncVal {v : ℕ → ℝ} (hvanti : Antitone v) (c : ℕ) (xs : List ℕ) :
    serialVal v c xs ≤ syncVal v c xs := by
  induction xs generalizing c with
  | nil => simp
  | cons x xs ih =>
      rw [serialVal_cons, syncVal_cons]
      have h1 : (∑ s ∈ Finset.range x, v (c + s + 1)) ≤ (x : ℝ) * v (c + 1) := by
        calc ∑ s ∈ Finset.range x, v (c + s + 1)
            ≤ ∑ _s ∈ Finset.range x, v (c + 1) := by
              apply Finset.sum_le_sum; intro s _
              exact hvanti (by omega)
          _ = (x : ℝ) * v (c + 1) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have h2 := ih (c + x)
      linarith [h1, h2]

/-- Lemma A.3 / equation (A.4): the synchronous–serial difference is at most `(n−1)·v(c+1)`. -/
lemma syncVal_sub_serialVal_le {v : ℕ → ℝ} (hv0 : ∀ s, 0 ≤ v s) (hvanti : Antitone v)
    (n : ℕ) (c : ℕ) (xs : List ℕ) (hx1 : ∀ x ∈ xs, 1 ≤ x) (hxn : ∀ x ∈ xs, x ≤ n) :
    syncVal v c xs - serialVal v c xs ≤ (n - 1 : ℕ) * v (c + 1) := by
  induction xs generalizing c with
  | nil =>
      simp only [syncVal_nil, serialVal_nil, sub_zero]
      exact mul_nonneg (by positivity) (hv0 (c + 1))
  | cons x xs ih =>
      have hx1x : 1 ≤ x := hx1 x (by simp)
      have hxnx : x ≤ n := hxn x (by simp)
      have hx1s : ∀ y ∈ xs, 1 ≤ y := fun y hy => hx1 y (by simp [hy])
      have hxns : ∀ y ∈ xs, y ≤ n := fun y hy => hxn y (by simp [hy])
      rw [serialVal_cons, syncVal_cons]
      have hb := batchErr_upper hv0 hvanti hx1x (c := c) (x := x)
      have hih := ih (c + x) hx1s hxns
      have hxnR : (x : ℝ) ≤ n := by exact_mod_cast hxnx
      have hcastx : ((x - 1 : ℕ) : ℝ) = (x : ℝ) - 1 := by
        rw [Nat.cast_sub hx1x]; norm_num
      have hcastn : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (le_trans hx1x hxnx)]; norm_num
      have hmono1 : v (c + x) ≤ v (c + 1) := hvanti (by omega)
      have hmono2 : v (c + x + 1) ≤ v (c + x) := hvanti (by omega)
      have hnonneg : 0 ≤ v (c + 1) - v (c + x) := by linarith
      rw [hcastx] at hb
      rw [hcastn] at hih ⊢
      nlinarith [hb, hih, hxnR, hmono1, hmono2, hnonneg]

/-- Equation (A.4) with the paper's normalization: starting from round `0`, batches of size `≤ n`. -/
theorem batch_inequality {v : ℕ → ℝ} (hv0 : ∀ s, 0 ≤ v s) (hvanti : Antitone v)
    (n : ℕ) (xs : List ℕ) (hx1 : ∀ x ∈ xs, 1 ≤ x) (hxn : ∀ x ∈ xs, x ≤ n) :
    0 ≤ syncVal v 0 xs - serialVal v 0 xs ∧
      syncVal v 0 xs - serialVal v 0 xs ≤ (n - 1 : ℕ) * v (0 + 1) :=
  ⟨sub_nonneg.mpr (serialVal_le_syncVal hvanti 0 xs : serialVal v 0 xs ≤ syncVal v 0 xs),
   syncVal_sub_serialVal_le hv0 hvanti n 0 xs hx1 hxn⟩

end AnvBandit
