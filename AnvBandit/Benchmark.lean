import AnvBandit.Bench
import AnvBandit.Greedy

/-!
# Complete benchmark comparisons of Appendix A.3

The witnesses below range over the full joint action space and preserve each policy's own counts.
-/

noncomputable section
open scoped BigOperators
open Finset
namespace AnvBandit
variable {n K : ℕ}

/-- Personal fatigue separates into `n` exact serial planning problems. -/
theorem Vstar0_eq_n_Vser {T : ℕ} (M : DecayModel n K) :
    Vstar0 (T := T) M = (n : ℝ) * Vser M T := by
  classical
  apply le_antisymm
  · unfold Vstar0
    apply Finset.sup'_le
    intro u _
    rw [J0_eq_serial]
    calc
      (∑ i : Fin n, M.serialAlloc (fun k => Ntot u i k)) ≤ ∑ _i : Fin n, Vser M T :=
        Finset.sum_le_sum fun i _ => le_Vser M (sum_Ntot_eq u i)
      _ = (n : ℝ) * Vser M T := by simp
  · obtain ⟨q, hq, hmax⟩ := Finset.exists_mem_eq_sup' (comps_nonempty M T)
      (fun q => M.serialAlloc (fun k => (q k : ℕ)))
    have hsum : ∑ k : Fin K, (q k : ℕ) = T := (Finset.mem_filter.mp hq).2
    obtain ⟨v, hv⟩ := exists_sched_with_counts (fun k => (q k : ℕ)) T hsum
    have hval : J0 M (fun _i t => v t) = (n : ℝ) * Vser M T := by
      rw [J0_eq_serial]
      have hcnt (i : Fin n) : (fun k => Ntot (fun _i t => v t) i k) = fun k => (q k : ℕ) := by
        funext k
        exact hv k
      simp_rw [hcnt]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      congr 1
      exact hmax.symm
    rw [← hval]
    exact Finset.le_sup' (J0 M) (Finset.mem_univ _)

/-- Pack an arbitrary serial count allocation into a complete simultaneous joint trajectory. -/
lemma exists_joint_with_counts {T : ℕ} (q : Fin K → ℕ) (hq : ∑ k, q k = n * T) :
    ∃ u : Fin n → Fin T → Fin K, ∀ k, Mtot u k = q k := by
  classical
  obtain ⟨v, hv⟩ := exists_sched_with_counts q (n * T) hq
  refine ⟨fun i t => v (finProdFinEquiv (i,t)), ?_⟩
  intro k
  rw [← hv k]
  unfold Mtot Ntot
  simp only [Finset.card_filter]
  rw [← Fintype.sum_prod_type (fun p : Fin n × Fin T =>
    if v (finProdFinEquiv p) = k then (1 : ℕ) else 0)]
  exact Fintype.sum_equiv finProdFinEquiv _ _ (fun _ => rfl)

/-- Public fatigue dominates the serial optimum with the same total number of pulls. -/
theorem Vser_le_Vstar1 {T : ℕ} (M : DecayModel n K) :
    Vser M (n * T) ≤ Vstar1 (T := T) M := by
  classical
  unfold Vser
  apply Finset.sup'_le
  intro q hq
  have hsum : ∑ k : Fin K, (q k : ℕ) = n * T := (Finset.mem_filter.mp hq).2
  obtain ⟨u, hu⟩ := exists_joint_with_counts (fun k => (q k : ℕ)) hsum
  have heq : M.serialAlloc (fun k => (q k : ℕ)) = M.serialAlloc (Mtot u) := by
    congr 1
    funext k
    exact (hu k).symm
  rw [heq]
  exact (J1_ge_serial M u).trans (Finset.le_sup' (J1 M) (Finset.mem_univ u))

/-- Both sides of the public-fatigue benchmark sandwich, with the original joint domain. -/
theorem benchmark_public_sandwich {T : ℕ} (M : DecayModel n K) :
    Vser M (n * T) ≤ Vstar1 (T := T) M ∧
    Vstar1 (T := T) M ≤ Vser M (n * T) + (n - 1 : ℕ) * M.A :=
  ⟨Vser_le_Vstar1 M, Vstar1_le_Vser M⟩

/-- Serial marginal streams start at the first positive use index. -/
def serialMarg (M : DecayModel n K) (k : Fin K) (r : ℕ) : ℝ :=
  M.b k + M.f k (r + 1)

lemma serialMarg_antitone (M : DecayModel n K) : ∀ k, Antitone (serialMarg M k) := by
  intro k r s hrs
  have h := M.f_anti k (Nat.add_le_add_right hrs 1)
  unfold serialMarg
  linarith

lemma serialAlloc_eq_greedyAllocation (M : DecayModel n K) (q : Fin K → ℕ) :
    M.serialAlloc q = Greedy.allocation (serialMarg M) q := by
  unfold DecayModel.serialAlloc DecayModel.Fk Greedy.allocation serialMarg Phi
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The actual serial greedy policy attains the unrestricted serial allocation optimum. -/
theorem Vser_eq_greedy_policy (M : DecayModel n K) (t : ℕ) :
    Vser M t = Greedy.payoff (serialMarg M)
      (Greedy.policy (by have := M.two_le_K; omega) (serialMarg M) t) := by
  classical
  let hK : 0 < K := by have := M.two_le_K; omega
  apply le_antisymm
  · unfold Vser
    apply Finset.sup'_le
    intro q hq
    rw [serialAlloc_eq_greedyAllocation]
    exact Greedy.allocation_le_greedy hK (serialMarg M) (serialMarg_antitone M) t
      (fun k => (q k : ℕ)) (Finset.mem_filter.mp hq).2
  · rw [Greedy.payoff_eq_allocation, ← serialAlloc_eq_greedyAllocation]
    apply le_Vser
    rw [Greedy.counts_total, Greedy.policy_length]

/-- The original serial allocation optimum equals its all-actions Bellman recursion. -/
theorem Vser_eq_dp (M : DecayModel n K) (t : ℕ) :
    Vser M t = Greedy.dp (by have := M.two_le_K; omega) (serialMarg M) t := by
  rw [Greedy.dp_eq_policy _ _ (serialMarg_antitone M), Vser_eq_greedy_policy]

end AnvBandit
