import AnvBandit.ActualNodeFiniteCost

/-! Finite grouping at node-specific arrival cuts. No exploration estimate is used here. -/
noncomputable section
open scoped BigOperators
open Finset
namespace AnvBandit
variable {n K : ℕ}

theorem GoodRunOn.node_cost_group {M : DecayModel n K} {T : ℕ} (R : GoodRunOn M T)
    (c : Fin K → ℝ) (hc : ∀ k, 0 ≤ c k) (hstar : c M.star = 0)
    (arr : Fin n → ℕ) (A : Fin n → Finset (Fin K))
    (hcover : ∀ i t, arr i < T → t ∈ (range T).filter (fun t => arr i ≤ t) →
      R.I t i = M.star ∨ R.I t i ∈ A i) :
    (∑ t ∈ range T, ∑ i, c (R.I t i)) ≤
      M.supOthers c * ((∑ i, min T (arr i) : ℕ) : ℝ) +
      ∑ i ∈ univ.filter (fun i => arr i < T), ∑ k ∈ A i,
        c k * (((range T).filter (fun t => arr i ≤ t)).filter (fun t => R.I t i = k)).card := by
  have hcmax : 0 ≤ M.supOthers c := by
    obtain ⟨k,hk⟩ := M.others_nonempty
    exact (hc k).trans (M.le_supOthers hk)
  have hc_le : ∀ t i, c (R.I t i) ≤ M.supOthers c := by
    intro t i
    by_cases hk : R.I t i = M.star
    · rw [hk, hstar]; exact hcmax
    · exact M.le_supOthers (by simp [DecayModel.others, hk])
  have hnode : ∀ i, (∑ t ∈ range T, c (R.I t i)) ≤
      M.supOthers c * (min T (arr i) : ℕ) +
      (if arr i < T then ∑ k ∈ A i,
        c k * (((range T).filter (fun t => arr i ≤ t)).filter (fun t => R.I t i = k)).card else 0) := by
    intro i
    let S := (range T).filter (fun t => arr i ≤ t)
    have hpre : (∑ t ∈ (range T).filter (fun t => ¬ arr i ≤ t), c (R.I t i)) ≤
        M.supOthers c * (min T (arr i) : ℕ) := by
      have he : (range T).filter (fun t => ¬ arr i ≤ t) = range (min T (arr i)) := by
        ext t; simp only [mem_filter, mem_range, not_le]; omega
      rw [he]
      calc
        _ ≤ ∑ _t ∈ range (min T (arr i)), M.supOthers c := sum_le_sum (fun t _ => hc_le t i)
        _ = _ := by simp [mul_comm]
    have hsplit := sum_filter_add_sum_filter_not (range T) (fun t => arr i ≤ t) (fun t => c (R.I t i))
    by_cases hai : arr i < T
    · have hgroup : (∑ t ∈ S, c (R.I t i)) =
          ∑ k ∈ A i, c k * (S.filter (fun t => R.I t i = k)).card := by
        rw [R.sum_by_arm S i c]
        have hrest : ∀ k ∈ (univ : Finset (Fin K)), k ∉ A i →
            (S.filter (fun t => R.I t i = k)).card * c k = 0 := by
          intro k _ hk
          by_cases hs : k = M.star
          · simp [hs, hstar]
          · have he : S.filter (fun t => R.I t i = k) = ∅ := by
              apply eq_empty_iff_forall_notMem.mpr
              intro t ht
              obtain ⟨htS, htk⟩ := mem_filter.mp ht
              rcases hcover i t hai htS with h | h
              · exact hs (htk.symm.trans h)
              · exact hk (htk ▸ h)
            simp [he]
        rw [← sum_subset (subset_univ (A i)) hrest]
        apply sum_congr rfl
        intro k _
        ring
      simp only [if_pos hai]
      change _ ≤ _ + ∑ k ∈ A i, c k * (S.filter (fun t => R.I t i = k)).card
      rw [← hgroup]
      dsimp [S] at *
      linarith
    · have he : S = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro t ht
        obtain ⟨ht, hat⟩ := mem_filter.mp ht
        have := mem_range.mp ht
        omega
      have hz : (∑ t ∈ S, c (R.I t i)) = 0 := by rw [he]; simp
      simp only [if_neg hai, add_zero]
      dsimp [S] at hz
      linarith
  rw [sum_comm]
  calc
    _ ≤ ∑ i, (M.supOthers c * (min T (arr i) : ℕ) +
      if arr i < T then ∑ k ∈ A i,
        c k * (((range T).filter (fun t => arr i ≤ t)).filter (fun t => R.I t i = k)).card else 0) :=
      sum_le_sum (fun i _ => hnode i)
    _ = _ := by rw [sum_add_distrib, ← mul_sum, ← Nat.cast_sum, sum_filter]

end AnvBandit
