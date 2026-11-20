import AnvBandit.Execution
import AnvBandit.Contact

/-!
# Deterministic communication facts for the actual executor

These local lemmas expose exactly the reliability premise still to be derived from the
finite good event and the stage budget. They are not an end-to-end propagation theorem.
No synthetic communication at the terminal horizon is introduced.
-/
noncomputable section
open Finset

namespace AnvBandit.Execution

variable {n K : ℕ}

def holders (k : Fin K) (s : State n K) : Finset (Fin n) :=
  univ.filter (fun i => k ∈ (s.nodes i).active)

@[simp] theorem mem_holders (k : Fin K) (s : State n K) (i : Fin n) :
    i ∈ holders k s ↔ k ∈ (s.nodes i).active := by simp [holders]

theorem holders_observe (p : Params n K) (k : Fin K) (s : State n K) (x : Fin n → ℝ) :
    holders k (observe p s x) = holders k s := rfl

/-- Once current holders recommend `k`, one actual simultaneous communication dominates
one ideal information step using exactly the same contact vector. -/
theorem infStep_subset_communicate_holders (k : Fin K) (s : State n K)
    (j : Fin n → Fin n)
    (hrec : ∀ i, i ∈ holders k s → (s.nodes i).cache = k) :
    infStep j (holders k s) ⊆ holders k (communicate s j) := by
  intro i hi
  rw [mem_holders]
  change k ∈ ((s.nodes i).receive ((s.nodes (j i)).cache)).active
  rcases Finset.mem_union.mp hi with hi | hi
  · have hkeep := (s.nodes i).cache_retained ((s.nodes (j i)).cache)
    simpa only [hrec i hi] using hkeep
  · have hj : j i ∈ holders k s := (Finset.mem_filter.mp hi).2
    have hget := (s.nodes i).received_mem ((s.nodes (j i)).cache)
    simpa only [hrec (j i) hj] using hget

/-- If all nodes already hold and recommend the same arm, receiving that arm changes
no replaceable set. This is stronger than merely retaining the distinguished arm. -/
theorem communicate_D_unchanged_of_all_reliable (k : Fin K) (s : State n K)
    (j : Fin n → Fin n) (hhold : ∀ i, k ∈ (s.nodes i).active)
    (hrec : ∀ i, (s.nodes i).cache = k) (i : Fin n) :
    ((communicate s j).nodes i).D = (s.nodes i).D := by
  simp [communicate, LocalState.receive, hrec, hhold]

theorem communicate_active_unchanged_of_all_reliable (k : Fin K) (s : State n K)
    (j : Fin n → Fin n) (hhold : ∀ i, k ∈ (s.nodes i).active)
    (hrec : ∀ i, (s.nodes i).cache = k) (i : Fin n) :
    ((communicate s j).nodes i).active = (s.nodes i).active := by
  unfold LocalState.active
  rw [communicate_D_unchanged_of_all_reliable k s j hhold hrec i]

/-- Irrespective of earlier incorrect recommendations, the original permanent holder
belongs to the actual holder set at every time. -/
theorem permanent_holder_mem (p : Params n K) (k : Fin K) (X J) (t : ℕ) :
    holder p k ∈ holders k (run p X J t) :=
  (mem_holders _ _ _).mpr (source_holds p X J t k)

end AnvBandit.Execution
