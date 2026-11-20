import AnvBandit.Batch
import AnvBandit.Model

/-!
# Serial benchmarks, synchronous traces and the batch comparison (A.2), (A.4)

This file formalises the deterministic content of Lemma A.3 and its use in Proposition A.5:

* `Fk` (`F_k(m) = m b_k + Φ_k(m)`), `serialAlloc` (its sum over arms),
* `serialVal v 0 xs = Phi v xs.sum`,
* `syncAlloc` for a per-arm batch structure and the identity
  `syncAlloc b − serialAlloc (fun k => (b k).sum) = ∑ k, (syncVal − serialVal)`,
* the per-trajectory bound `0 ≤ J^{(1)}(I) − ∑_k F_k(M_k) ≤ (n−1) A` (equation (A.2)),
* the optimal-value sandwich `V^ser(nT) ≤ V^{⋆,1}_T ≤ V^ser(nT) + (n−1) A`.
-/

noncomputable section
open scoped BigOperators
open Finset

namespace AnvBandit

variable {n K : ℕ}

namespace DecayModel

variable (M : DecayModel n K)

/-- `serialVal` from offset `0` is the accumulated added value `Φ`. -/
lemma serialVal_zero_eq_Phi (v : ℕ → ℝ) (xs : List ℕ) :
    serialVal v 0 xs = Phi v xs.sum := by
  simp only [serialVal, Phi, Nat.zero_add]

/-- `F_k(m) = m b_k + Φ_k(m)`. -/
def Fk (k : Fin K) (m : ℕ) : ℝ := (m : ℝ) * M.b k + Phi (M.f k) m

/-- Serial value of an allocation `m`: `∑_k F_k(m_k)`. -/
def serialAlloc (m : Fin K → ℕ) : ℝ := ∑ k, M.Fk k (m k)

/-- Synchronous value of a per-arm batch structure `b`: `∑_k M_k b_k + ∑_k syncVal`. -/
def syncAlloc (b : Fin K → List ℕ) : ℝ :=
  ∑ k, ((b k).sum : ℝ) * M.b k + ∑ k, syncVal (M.f k) 0 (b k)

lemma serialAlloc_eq_serial (b : Fin K → List ℕ) :
    M.serialAlloc (fun k => (b k).sum)
      = ∑ k, ((b k).sum : ℝ) * M.b k + ∑ k, serialVal (M.f k) 0 (b k) := by
  simp only [serialAlloc, Fk, serialVal_zero_eq_Phi, Finset.sum_add_distrib]

lemma syncAlloc_sub_serialAlloc (b : Fin K → List ℕ) :
    M.syncAlloc b - M.serialAlloc (fun k => (b k).sum)
      = ∑ k, (syncVal (M.f k) 0 (b k) - serialVal (M.f k) 0 (b k)) := by
  rw [syncAlloc, serialAlloc_eq_serial]
  rw [add_sub_add_left_eq_sub, Finset.sum_sub_distrib]

/-- Equation (A.2), upper half: the synchronous value exceeds the serial value of the final counts
by at most `(n−1)·A`. -/
lemma syncAlloc_sub_serialAlloc_le (b : Fin K → List ℕ)
    (hx1 : ∀ k, ∀ x ∈ b k, 1 ≤ x) (hxn : ∀ k, ∀ x ∈ b k, x ≤ n) :
    M.syncAlloc b - M.serialAlloc (fun k => (b k).sum) ≤ (n - 1 : ℕ) * M.A := by
  rw [syncAlloc_sub_serialAlloc]
  calc ∑ k, (syncVal (M.f k) 0 (b k) - serialVal (M.f k) 0 (b k))
      ≤ ∑ _k : Fin K, (n - 1 : ℕ) * M.f _k 1 :=
        Finset.sum_le_sum fun k _ =>
          syncVal_sub_serialVal_le (hv0 := M.f_nonneg k) (hvanti := M.f_anti k) n 0 (b k)
            (hx1 k) (hxn k)
    _ = (n - 1 : ℕ) * M.A := by
        simp only [A, ak]
        rw [Finset.mul_sum]

/-- Equation (A.2), lower half: the serial value never exceeds the synchronous value. -/
lemma serialAlloc_le_syncAlloc (b : Fin K → List ℕ) :
    M.serialAlloc (fun k => (b k).sum) ≤ M.syncAlloc b := by
  have h : (0 : ℝ) ≤ ∑ k, (syncVal (M.f k) 0 (b k) - serialVal (M.f k) 0 (b k)) :=
    Finset.sum_nonneg fun k _ =>
      sub_nonneg.mpr (serialVal_le_syncVal (M.f_anti k) 0 (b k))
  have hid := M.syncAlloc_sub_serialAlloc b
  linarith [hid, h]

end DecayModel

end AnvBandit
