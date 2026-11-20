import AnvBandit.Terminal

/-! Finite-prefix personal cost adapter, with terminal capacity applied only to arrived nodes.
The actual-arrival and elimination premises are discharged in the actual execution layer;
this combinatorial lemma is not itself an end-to-end algorithm bound. -/
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators
open Finset
namespace AnvBandit
variable {n K : ℕ}
namespace GoodRunOn
/-- Grouping a sum by the selected arm. -/
lemma sum_by_arm {M : DecayModel n K} {T : ℕ} (R : GoodRunOn M T) (S : Finset ℕ) (i : Fin n) (f : Fin K → ℝ) :
    (∑ t ∈ S, f (R.I t i)) = ∑ k, (S.filter (fun t => R.I t i = k)).card * f k := by
  have h1 : ∀ t ∈ S, f (R.I t i) = ∑ k, (if R.I t i = k then f k else 0) := by
    intro t _
    rw [Finset.sum_eq_single (R.I t i)]
    · simp
    · intro k _ hk; rw [if_neg (fun h => hk h.symm)]
    · intro h; exact absurd (Finset.mem_univ _) h
  calc ∑ t ∈ S, f (R.I t i) = ∑ t ∈ S, ∑ k, (if R.I t i = k then f k else 0) :=
        Finset.sum_congr rfl h1
    _ = ∑ k, ∑ t ∈ S, (if R.I t i = k then f k else 0) := Finset.sum_comm
    _ = ∑ k, (S.filter (fun t => R.I t i = k)).card * f k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

end GoodRunOn

/-- **(C.2)**, the per-trajectory per-node cost bound (personal-fatigue branch). -/
theorem GoodRunOn.node_cost_traj {M : DecayModel n K} {T : ℕ} (R : GoodRunOn M T) (c : Fin K → ℝ)
    (arr : Fin n → ℕ) (D : Fin n → Finset (Fin K)) (elim : Fin n → ℕ) (i0 : Fin n)
    (hc : ∀ k, 0 ≤ c k) (hstar : c M.star = 0)
    (hstar_perm : M.star ∈ permSet n K i0)
    (hdisj : ∀ i, Disjoint (permSet n K i) (D i))
    (hDcard : ∀ i, (D i).card ≤ 2)
    (hstar_mem : ∀ i, arr i < T → M.star ∈ permSet n K i ∪ D i)
    (hSbound : ∀ i, (permSet n K i ∪ D i).card ≤ smax n K)
    (harr : ∀ t i, arr i ≤ t → t < T → M.star ∈ R.active t i)
    (helim : ∀ i, ((Finset.univ : Finset (Fin K)).filter (fun k =>
        k ∉ permSet n K i ∪ D i ∧ ∃ t ∈ Finset.range T, arr i ≤ t ∧ R.I t i = k)).card ≤ elim i) :
    (∑ t ∈ Finset.range T, ∑ i, c (R.I t i))
      ≤ M.supOthers c * ((∑ i, min T (arr i) : ℕ) : ℝ)
        + M.Ccap c R.L + M.wmax c R.L * ((∑ i, elim i : ℕ) : ℝ) := by
  have hcmax : 0 ≤ M.supOthers c := by
    obtain ⟨k, hk⟩ := M.others_nonempty
    exact le_trans (hc k) (M.le_supOthers hk)
  have hwmax : 0 ≤ M.wmax c R.L := M.wmax_nonneg hc R.L
  rw [Finset.sum_comm]
  have hsplit : ∀ i, (∑ t ∈ Finset.range T, c (R.I t i))
      ≤ M.supOthers c * ((min T (arr i) : ℕ) : ℝ)
        + (if arr i < T then ∑ k ∈ (permSet n K i ∪ D i).erase M.star, M.wk c R.L k else 0)
        + M.wmax c R.L * (elim i : ℝ) := by
    intro i
    by_cases hai : arr i < T
    · simp only [if_pos hai]
      set S : Finset ℕ := (Finset.range T).filter (fun t => arr i ≤ t) with hS
      have hcardP : ((Finset.range T).filter (fun t => ¬ arr i ≤ t)).card = min T (arr i) := by
        have h : (Finset.range T).filter (fun t => ¬ arr i ≤ t) = Finset.range (min T (arr i)) := by
          ext t; simp only [Finset.mem_filter, Finset.mem_range, not_le]; omega
        rw [h, Finset.card_range]
      have hc_le : ∀ t, c (R.I t i) ≤ M.supOthers c := by
        intro t
        by_cases hk : R.I t i = M.star
        · rw [hk, hstar]; exact hcmax
        · exact M.le_supOthers (by rw [DecayModel.others, Finset.mem_erase]; exact ⟨hk, Finset.mem_univ _⟩)
      have hpre : (∑ t ∈ (Finset.range T).filter (fun t => ¬ arr i ≤ t), c (R.I t i))
          ≤ M.supOthers c * ((min T (arr i) : ℕ) : ℝ) := by
        calc (∑ t ∈ (Finset.range T).filter (fun t => ¬ arr i ≤ t), c (R.I t i))
            ≤ ∑ _t ∈ (Finset.range T).filter (fun t => ¬ arr i ≤ t), M.supOthers c :=
              Finset.sum_le_sum fun t _ => hc_le t
          _ = (((Finset.range T).filter (fun t => ¬ arr i ≤ t)).card : ℝ) * M.supOthers c := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ = M.supOthers c * ((min T (arr i) : ℕ) : ℝ) := by rw [hcardP]; ring
      have hpullcard : ∀ k, k ≠ M.star →
          (S.filter (fun t => R.I t i = k)).card ≤ M.mkAll R.L k := by
        intro k hk
        have hsub : S.filter (fun t => R.I t i = k)
            ⊆ (Finset.range T).filter (fun t => M.star ∈ R.active t i ∧ R.I t i = k) := by
          intro t ht
          rw [Finset.mem_filter] at ht ⊢
          obtain ⟨htS, htk⟩ := ht
          rw [hS, Finset.mem_filter] at htS
          exact ⟨htS.1, harr t i htS.2 (Finset.mem_range.mp htS.1), htk⟩
        exact le_trans (Finset.card_le_card hsub) (R.pair_budget i hk)
      have hmono : ∀ k, k ≠ M.star →
          (S.filter (fun t => R.I t i = k)).card * c k ≤ M.wk c R.L k := by
        intro k hk
        rw [DecayModel.wk]
        have hR : ((S.filter (fun t => R.I t i = k)).card : ℝ) ≤ (M.mkAll R.L k : ℝ) := by
          exact_mod_cast hpullcard k hk
        calc (S.filter (fun t => R.I t i = k)).card * c k
            = c k * (S.filter (fun t => R.I t i = k)).card := by ring
          _ ≤ c k * (M.mkAll R.L k : ℝ) := mul_le_mul_of_nonneg_left hR (hc k)
      have hgroup : (∑ t ∈ S, c (R.I t i)) = ∑ k, (S.filter (fun t => R.I t i = k)).card * c k :=
        GoodRunOn.sum_by_arm R S i c
      set A : Finset (Fin K) := (permSet n K i ∪ D i).erase M.star with hA
      set S0 : Finset (Fin K) := (Finset.univ : Finset (Fin K)) \ (permSet n K i ∪ D i) with hS0
      have hcomp : (Finset.univ : Finset (Fin K)) \ A = insert M.star S0 := by
        ext k
        by_cases hk : k = M.star
        · subst hk
          simp [Finset.mem_sdiff, Finset.mem_insert, hA, hS0, Finset.mem_erase, hstar_mem i hai]
        · simp [Finset.mem_sdiff, Finset.mem_insert, hA, hS0, Finset.mem_erase, hk]
      have hstar_notin : M.star ∉ S0 := by
        rw [hS0, Finset.mem_sdiff]; exact fun h => h.2 (hstar_mem i hai)
      have hbound : (∑ k, (S.filter (fun t => R.I t i = k)).card * c k)
          ≤ (∑ k ∈ A, M.wk c R.L k) + M.wmax c R.L * (elim i : ℝ) := by
        rw [← Finset.sum_sdiff (Finset.subset_univ A), hcomp, Finset.sum_insert hstar_notin]
        have hstar0 : (S.filter (fun t => R.I t i = M.star)).card * c M.star = 0 := by
          rw [hstar, mul_zero]
        rw [hstar0, zero_add]
        have hA' : (∑ k ∈ A, (S.filter (fun t => R.I t i = k)).card * c k)
            ≤ ∑ k ∈ A, M.wk c R.L k :=
          Finset.sum_le_sum fun k hk => hmono k (Finset.mem_erase.mp hk).1
        have hS0bound : (∑ k ∈ S0, (S.filter (fun t => R.I t i = k)).card * c k)
            ≤ M.wmax c R.L * (elim i : ℝ) := by
          have hred : (∑ k ∈ S0, (S.filter (fun t => R.I t i = k)).card * c k)
              = ∑ k ∈ S0.filter (fun k => (S.filter (fun t => R.I t i = k)).Nonempty),
                  (S.filter (fun t => R.I t i = k)).card * c k := by
            refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
            intro k hkS0 hknot
            have hemp : (S.filter (fun t => R.I t i = k)) = ∅ := by
              rw [← Finset.not_nonempty_iff_eq_empty]
              exact fun h => hknot (Finset.mem_filter.mpr ⟨hkS0, h⟩)
            rw [hemp]; simp
          rw [hred]
          have hterm : ∀ k ∈ S0.filter (fun k => (S.filter (fun t => R.I t i = k)).Nonempty),
              (S.filter (fun t => R.I t i = k)).card * c k ≤ M.wmax c R.L := by
            intro k hk
            rw [Finset.mem_filter] at hk
            have hkS0 : k ∈ S0 := hk.1
            rw [hS0, Finset.mem_sdiff] at hkS0
            have hkne : k ≠ M.star := fun h => hkS0.2 (h ▸ hstar_mem i hai)
            exact le_trans (hmono k hkne)
              (M.le_supOthers (by rw [DecayModel.others, Finset.mem_erase]; exact ⟨hkne, Finset.mem_univ k⟩))
          have hcount : ((S0.filter (fun k => (S.filter (fun t => R.I t i = k)).Nonempty)).card : ℝ)
              ≤ (elim i : ℝ) := by
            have hsub : (S0.filter (fun k => (S.filter (fun t => R.I t i = k)).Nonempty))
                ⊆ (Finset.univ : Finset (Fin K)).filter (fun k =>
                    k ∉ permSet n K i ∪ D i ∧ ∃ t ∈ Finset.range T, arr i ≤ t ∧ R.I t i = k) := by
              intro k hk
              rw [Finset.mem_filter] at hk ⊢
              obtain ⟨hkS0, hne⟩ := hk
              rw [hS0, Finset.mem_sdiff] at hkS0
              obtain ⟨t, ht⟩ := hne
              rw [Finset.mem_filter] at ht
              obtain ⟨htS, htk⟩ := ht
              rw [hS, Finset.mem_filter] at htS
              exact ⟨Finset.mem_univ k, hkS0.2, t, htS.1, htS.2, htk⟩
            exact_mod_cast le_trans (Finset.card_le_card hsub) (helim i)
          calc (∑ k ∈ S0.filter (fun k => (S.filter (fun t => R.I t i = k)).Nonempty),
                  (S.filter (fun t => R.I t i = k)).card * c k)
              ≤ ∑ _k ∈ S0.filter (fun k => (S.filter (fun t => R.I t i = k)).Nonempty), M.wmax c R.L :=
                Finset.sum_le_sum hterm
            _ = ((S0.filter (fun k => (S.filter (fun t => R.I t i = k)).Nonempty)).card : ℝ)
                  * M.wmax c R.L := by rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (elim i : ℝ) * M.wmax c R.L := mul_le_mul_of_nonneg_right hcount hwmax
            _ = M.wmax c R.L * (elim i : ℝ) := by ring
        linarith [hA', hS0bound]
      have hsum : (∑ t ∈ Finset.range T, c (R.I t i))
          = (∑ t ∈ (Finset.range T).filter (fun t => arr i ≤ t), c (R.I t i))
            + ∑ t ∈ (Finset.range T).filter (fun t => ¬ arr i ≤ t), c (R.I t i) :=
        (Finset.sum_filter_add_sum_filter_not (Finset.range T) (fun t => arr i ≤ t)
          (fun t => c (R.I t i))).symm
      rw [hsum]
      have hSeq : (∑ t ∈ (Finset.range T).filter (fun t => arr i ≤ t), c (R.I t i))
          = ∑ t ∈ S, c (R.I t i) := by rw [hS]
      rw [hSeq, hgroup]
      linarith [hpre, hbound]
    · have hm : min T (arr i) = T := min_eq_left (by omega)
      have hc_le : ∀ t, c (R.I t i) ≤ M.supOthers c := by
        intro t
        by_cases hk : R.I t i = M.star
        · rw [hk, hstar]; exact hcmax
        · exact M.le_supOthers (by simp [DecayModel.others, hk])
      have hpre : (∑ t ∈ range T, c (R.I t i)) ≤ M.supOthers c * (T : ℝ) := by
        calc
          _ ≤ ∑ _t ∈ range T, M.supOthers c := sum_le_sum (fun t _ => hc_le t)
          _ = M.supOthers c * (T : ℝ) := by simp [mul_comm]
      simp only [if_neg hai, hm, add_zero]
      exact hpre.trans (le_add_of_nonneg_right (mul_nonneg hwmax (Nat.cast_nonneg _)))
  calc (∑ i, ∑ t ∈ Finset.range T, c (R.I t i))
      ≤ ∑ i, (M.supOthers c * ((min T (arr i) : ℕ) : ℝ)
          + (if arr i < T then ∑ k ∈ (permSet n K i ∪ D i).erase M.star, M.wk c R.L k else 0)
          + M.wmax c R.L * (elim i : ℝ)) := Finset.sum_le_sum fun i _ => hsplit i
    _ = M.supOthers c * ((∑ i, min T (arr i) : ℕ) : ℝ)
        + (∑ i, if arr i < T then ∑ k ∈ (permSet n K i ∪ D i).erase M.star, M.wk c R.L k else 0)
        + M.wmax c R.L * ((∑ i, elim i : ℕ) : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          ← Nat.cast_sum, ← Nat.cast_sum]
    _ ≤ M.supOthers c * ((∑ i, min T (arr i) : ℕ) : ℝ)
        + M.Ccap c R.L + M.wmax c R.L * ((∑ i, elim i : ℕ) : ℝ) := by
        have htb : (∑ i, if arr i < T then ∑ k ∈ (permSet n K i ∪ D i).erase M.star, M.wk c R.L k else 0)
            ≤ M.Ccap c R.L := by
          have h := terminal_budget (M := M) (by have := M.two_le_n; omega : 0 < n) c R.L hc hstar
            (Finset.univ.filter (fun i => arr i < T)) D i0
            hstar_perm (fun i _ => hdisj i) (fun i _ => hDcard i)
            (fun i hi => hstar_mem i (Finset.mem_filter.mp hi).2)
            (fun i _ => hSbound i)
          simpa only [Finset.sum_filter] using h
        linarith [htb]


end AnvBandit
