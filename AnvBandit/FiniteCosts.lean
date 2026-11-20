import AnvBandit.Terminal

/-!
# Finite-event deterministic cost adapters

The combinatorial terminal budget is reused with GoodRunOn T, not an infinite-prefix
GoodRun. Stability is an explicit intermediate premise here; the actual propagation
proof must discharge it before this becomes an algorithm regret bound.
-/
noncomputable section
open scoped BigOperators
open Finset
namespace AnvBandit
variable {n K : ℕ}

theorem GoodRunOn.terminal_cost {M : DecayModel n K} {T : ℕ} (R : GoodRunOn M T) (hn : 0 < n) (c : Fin K → ℝ)
    (Tstart : ℕ) (i0 : Fin n) (D : Fin n → Finset (Fin K))
    (hc : ∀ k, 0 ≤ c k) (hstar : c M.star = 0)
    (hstab : ∀ t i, Tstart ≤ t → t < T → R.active t i = permSet n K i ∪ D i)
    (hstar_perm : M.star ∈ permSet n K i0)
    (hdisj : ∀ i, Disjoint (permSet n K i) (D i))
    (hDcard : ∀ i, (D i).card ≤ 2)
    (hstar_mem : ∀ i, M.star ∈ permSet n K i ∪ D i)
    (hSbound : ∀ i, (permSet n K i ∪ D i).card ≤ smax n K) :
    (∑ t ∈ (Finset.range T).filter (fun t => Tstart ≤ t), ∑ i, c (R.I t i)) ≤ M.Ccap c R.L := by
  rw [Finset.sum_comm]
  refine (Finset.sum_le_sum fun i _ => ?_).trans
    (terminal_budget hn c R.L hc hstar Finset.univ D i0 hstar_perm
      (fun i _ => hdisj i) (fun i _ => hDcard i) (fun i _ => hstar_mem i) (fun i _ => hSbound i))
  set Sr := (Finset.range T).filter (fun t => Tstart ≤ t) with hSr
  have hFi : ∀ t ∈ Sr, R.I t i ∈ (permSet n K i ∪ D i).erase M.star ∨ R.I t i = M.star := by
    intro t ht
    obtain ⟨htr, hTt⟩ := Finset.mem_filter.mp ht
    have hmem : R.I t i ∈ permSet n K i ∪ D i := by
      have hact := hstab t i hTt (Finset.mem_range.mp htr)
      rw [← hact]; exact R.sel_mem t (Finset.mem_range.mp htr) i
    by_cases hs : R.I t i = M.star
    · exact Or.inr hs
    · exact Or.inl (Finset.mem_erase.mpr ⟨hs, hmem⟩)
  have hpoint : ∀ t ∈ Sr, c (R.I t i)
      = ∑ k ∈ (permSet n K i ∪ D i).erase M.star, (if R.I t i = k then c k else 0) := by
    intro t ht
    rcases hFi t ht with h | h
    · rw [Finset.sum_eq_single (R.I t i) (fun k _ hk => by rw [if_neg (fun h' => hk h'.symm)])
          (fun hc' => absurd h hc'), if_pos rfl]
    · rw [h, hstar]
      exact (Finset.sum_eq_zero (fun k hk => by
        rw [if_neg (fun hk' => (Finset.mem_erase.mp hk).1 hk'.symm)])).symm
  have hcount : ∀ k, k ≠ M.star → (Sr.filter (fun t => R.I t i = k)).card ≤ M.mkAll R.L k := by
    intro k hk
    refine le_trans (Finset.card_le_card ?_) (R.pair_budget i hk)
    intro t ht
    simp only [Finset.mem_filter] at ht
    obtain ⟨htSr, hsel⟩ := ht
    obtain ⟨htr, hTt⟩ := Finset.mem_filter.mp htSr
    exact Finset.mem_filter.mpr ⟨htr, by
      rw [hstab t i hTt (Finset.mem_range.mp htr)]; exact hstar_mem i, hsel⟩
  rw [Finset.sum_congr rfl hpoint, Finset.sum_comm]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [sum_ite_const Sr (fun t => R.I t i = k) (c k), DecayModel.wk]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcount k (Finset.mem_erase.mp hk).1) (hc k)


/-- The actual loss during at most `S` waiting rounds is bounded without a good-event
or stability hypothesis. The horizon truncation is pathwise, before taking expectations. -/
theorem waiting_cost_le (I : ℕ → Fin n → Fin K) (c : Fin K → ℝ) (cmax : ℝ)
    (hcmax : ∀ k, c k ≤ cmax) (T S : ℕ) :
    (∑ t ∈ (range T).filter (fun t => t < S), ∑ i, c (I t i)) ≤
      (n : ℝ) * cmax * (min T S : ℕ) := by
  have hset : (range T).filter (fun t => t < S) = range (min T S) := by
    ext t
    simp only [mem_filter, mem_range, lt_min_iff]
  rw [hset]
  calc
    (∑ t ∈ range (min T S), ∑ i, c (I t i)) ≤
        ∑ _t ∈ range (min T S), (n : ℝ) * cmax := by
      apply sum_le_sum
      intro t ht
      calc (∑ i, c (I t i)) ≤ ∑ _i : Fin n, cmax :=
          sum_le_sum (fun i _ => hcmax (I t i))
        _ = (n : ℝ) * cmax := by simp
    _ = (n : ℝ) * cmax * (min T S : ℕ) := by simp; ring

/-- Exact finite loss decomposition at an arbitrary (possibly horizon-exceeding) cut. -/
theorem loss_split_at (I : ℕ → Fin n → Fin K) (c : Fin K → ℝ) (T S : ℕ) :
    (∑ t ∈ range T, ∑ i, c (I t i)) =
      (∑ t ∈ (range T).filter (fun t => t < S), ∑ i, c (I t i)) +
      (∑ t ∈ (range T).filter (fun t => S ≤ t), ∑ i, c (I t i)) := by
  simp only [sum_filter]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro t ht
  by_cases h : t < S
  · simp [h, Nat.not_le.mpr h]
  · simp [h, Nat.le_of_not_gt h]

/-- Finite-event global waiting adapter. All stability/terminal premises are explicit
intermediate obligations, to be generated from the actual propagation proof. -/
theorem GoodRunOn.global_wait_cost {M : DecayModel n K} {T : ℕ} (R : GoodRunOn M T)
    (hn : 0 < n) (c : Fin K → ℝ) (cmax : ℝ) (S : ℕ)
    (i0 : Fin n) (D : Fin n → Finset (Fin K))
    (hc : ∀ k, 0 ≤ c k) (hstar : c M.star = 0) (hcmax : ∀ k, c k ≤ cmax)
    (hstab : ∀ t i, S ≤ t → t < T → R.active t i = permSet n K i ∪ D i)
    (hstar_perm : M.star ∈ permSet n K i0)
    (hdisj : ∀ i, Disjoint (permSet n K i) (D i))
    (hDcard : ∀ i, (D i).card ≤ 2)
    (hstar_mem : ∀ i, M.star ∈ permSet n K i ∪ D i)
    (hSbound : ∀ i, (permSet n K i ∪ D i).card ≤ smax n K) :
    (∑ t ∈ range T, ∑ i, c (R.I t i)) ≤
      (n : ℝ) * cmax * (min T S : ℕ) + M.Ccap c R.L := by
  rw [loss_split_at R.I c T S]
  exact add_le_add (waiting_cost_le R.I c cmax hcmax T S)
    (R.terminal_cost hn c S i0 D hc hstar hstab hstar_perm hdisj hDcard hstar_mem hSbound)

end AnvBandit
