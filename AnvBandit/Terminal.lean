import AnvBandit.AlgCount

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-!
# Terminal active-set counting (Appendix C.1)

This file formalises the counting argument at the heart of Lemma C.1.  The permanent sets are the
explicit sets of equation (3.1),

`S⁰_i = {k ∈ K : 1 + ((k−1) mod n) = i}`  (here `permSet i = {k : k.val % n = i.val}`),

which this file proves form a disjoint partition of `K`.  A terminal configuration records, for each
node `i` in a set `J` of arrived nodes, a replaceable set `D i` such that the active set
`S i = permSet i ∪ D i` contains `k⋆`, has size `≤ s_max`, and `D i` is disjoint from `permSet i`
with `|D i| ≤ 2`.

`terminal_budget` proves the weighted budget of the suboptimal arms in these terminal active sets is
at most `C(c) = min(n W_κ(c), W(c) + (n+1) w_max(c))`, matching Appendix C.1.

`lemma_C_1_count` combines this with `GoodRun.pair_budget` to bound the post-stabilisation weighted
exploration cost by `C_λ(c; 0)`.
-/

noncomputable section
open scoped BigOperators
open Finset

namespace AnvBandit

variable {n K : ℕ}

/-- The permanent set of node `i`, equation (3.1):
`S⁰_i = {k ∈ K : 1 + ((k−1) mod n) = i}`. -/
def permSet (n K : ℕ) (i : Fin n) : Finset (Fin K) :=
  Finset.univ.filter (fun k => k.val % n = i.val)

lemma mem_permSet {k : Fin K} {i : Fin n} : k ∈ permSet n K i ↔ k.val % n = i.val := by
  simp [permSet]

lemma permSet_disjoint (hn : 0 < n) (i j : Fin n) (h : i ≠ j) :
    Disjoint (permSet n K i) (permSet n K j) := by
  rw [Finset.disjoint_left]
  intro k hki hkj
  rw [mem_permSet] at hki hkj
  exact h (Fin.ext (by rw [← hki, hkj]))

lemma mem_permSet_iff (hn : 0 < n) (k : Fin K) :
    k ∈ permSet n K ⟨k.val % n, Nat.mod_lt k.val hn⟩ := by
  rw [mem_permSet]

lemma permSet_cover (hn : 0 < n) (k : Fin K) : ∃ i : Fin n, k ∈ permSet n K i :=
  ⟨⟨k.val % n, Nat.mod_lt k.val hn⟩, mem_permSet_iff hn k⟩

/-- Summing over the permanent partition recovers the total: `∑_i ∑_{k ∈ S⁰_i} f k = ∑_k f k`. -/
lemma sum_permSet (hn : 0 < n) (f : Fin K → ℝ) :
    ∑ i : Fin n, ∑ k ∈ permSet n K i, f k = ∑ k, f k := by
  simp only [permSet, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single ⟨k.val % n, Nat.mod_lt k.val hn⟩]
  · simp
  · intro i _ hi
    rw [if_neg]
    intro h; exact absurd (Fin.ext h.symm) hi
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `∑_{k ∈ F} w_k ≤ W_κ(c)` for any `F ⊆ K \ {k⋆}` of size `≤ κ`. -/
lemma sum_le_Wkappa {M : DecayModel n K} {c : Fin K → ℝ} (hc : ∀ k, 0 ≤ c k) {L : ℝ}
    {F : Finset (Fin K)} (hF : F ⊆ M.others) (hcard : F.card ≤ kappa n K) :
    ∑ k ∈ F, M.wk c L k ≤ M.Wkappa c L := by
  rw [DecayModel.Wkappa]
  split
  · rename_i hk
    obtain ⟨G, hFG, hGsub, hGcard⟩ :=
      Finset.exists_subsuperset_card_eq hF hcard hk
    have hGmem : G ∈ M.others.powersetCard (kappa n K) := by
      rw [Finset.mem_powersetCard]
      exact ⟨hGsub, hGcard⟩
    calc ∑ k ∈ F, M.wk c L k ≤ ∑ k ∈ G, M.wk c L k :=
          Finset.sum_le_sum_of_subset_of_nonneg hFG (fun k _ _ => M.wk_nonneg hc L k)
      _ ≤ (M.others.powersetCard (kappa n K)).sup' (Finset.powersetCard_nonempty_of_le hk)
            (fun F => ∑ k ∈ F, M.wk c L k) :=
          Finset.le_sup' (fun F => ∑ k ∈ F, M.wk c L k) hGmem
  · rename_i hk
    exact Finset.sum_le_sum_of_subset_of_nonneg hF (fun k _ _ => M.wk_nonneg hc L k)

/-- **Appendix C.1, terminal counting.** The weighted budget of the suboptimal arms carried by the
terminal active sets `permSet i ∪ D i` (`i ∈ J`) is at most `C(c)`. -/
theorem terminal_budget {M : DecayModel n K} (hn : 0 < n) (c : Fin K → ℝ) (L : ℝ)
    (hc : ∀ k, 0 ≤ c k) (hstar : c M.star = 0)
    (J : Finset (Fin n)) (D : Fin n → Finset (Fin K)) (i0 : Fin n)
    (hstar_perm : M.star ∈ permSet n K i0)
    (hdisj : ∀ i ∈ J, Disjoint (permSet n K i) (D i))
    (hDcard : ∀ i ∈ J, (D i).card ≤ 2)
    (hstar_mem : ∀ i ∈ J, M.star ∈ permSet n K i ∪ D i)
    (hSbound : ∀ i ∈ J, (permSet n K i ∪ D i).card ≤ smax n K) :
    (∑ i ∈ J, ∑ k ∈ (permSet n K i ∪ D i).erase M.star, M.wk c L k) ≤ M.Ccap c L := by
  refine le_min ?_ ?_
  · calc (∑ i ∈ J, ∑ k ∈ (permSet n K i ∪ D i).erase M.star, M.wk c L k)
        ≤ ∑ _i ∈ J, M.Wkappa c L := by
          refine Finset.sum_le_sum fun i hiJ => ?_
          refine sum_le_Wkappa hc ?_ ?_
          · intro k hk
            rw [Finset.mem_erase] at hk
            rw [DecayModel.others, Finset.mem_erase]
            exact ⟨hk.1, Finset.mem_univ k⟩
          · have hcard := Finset.card_erase_of_mem (hstar_mem i hiJ)
            have hs := hSbound i hiJ
            rw [kappa]; omega
      _ = (J.card : ℝ) * M.Wkappa c L := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ n * M.Wkappa c L := by
          refine mul_le_mul_of_nonneg_right ?_ (M.Wkappa_nonneg hc L)
          have h : J.card ≤ n := by
            calc J.card ≤ (Finset.univ : Finset (Fin n)).card :=
                  Finset.card_le_card (Finset.subset_univ J)
              _ = n := by simp
          exact_mod_cast h
  · have hsplit : (∑ i ∈ J, ∑ k ∈ (permSet n K i ∪ D i).erase M.star, M.wk c L k)
        = (∑ i ∈ J, ∑ k ∈ (permSet n K i).erase M.star, M.wk c L k)
          + (∑ i ∈ J, ∑ k ∈ (D i).erase M.star, M.wk c L k) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hiJ => ?_
      rw [Finset.erase_union_distrib,
        Finset.sum_union ((hdisj i hiJ).mono (Finset.erase_subset M.star (permSet n K i))
          (Finset.erase_subset M.star (D i)))]
    rw [hsplit]
    have hperm : (∑ i ∈ J, ∑ k ∈ (permSet n K i).erase M.star, M.wk c L k) ≤ M.Wsum c L := by
      have h1 : (∑ i ∈ J, ∑ k ∈ (permSet n K i).erase M.star, M.wk c L k)
          ≤ ∑ i : Fin n, ∑ k ∈ (permSet n K i).erase M.star, M.wk c L k :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J)
          (fun i _ _ => Finset.sum_nonneg fun k _ => M.wk_nonneg hc L k)
      refine h1.trans ?_
      have heq : ∀ i : Fin n, (∑ k ∈ (permSet n K i).erase M.star, M.wk c L k)
          = ∑ k ∈ permSet n K i, (if k = M.star then 0 else M.wk c L k) := by
        intro i
        rw [show (permSet n K i).erase M.star
              = (permSet n K i).filter (fun k => k ≠ M.star) from by
              ext k; simp [Finset.mem_erase, Finset.mem_filter, and_comm],
            Finset.sum_filter]
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases h : k = M.star <;> simp [h]
      rw [Finset.sum_congr rfl (fun i _ => heq i), sum_permSet hn]
      rw [DecayModel.Wsum, DecayModel.others]
      have hif : ∀ k, (if k = M.star then 0 else M.wk c L k)
          = (if k ≠ M.star then M.wk c L k else 0) := by
        intro k; by_cases h : k = M.star <;> simp [h]
      rw [Finset.sum_congr rfl (fun k _ => hif k)]
      rw [← Finset.sum_filter]
      have hset : (Finset.univ.filter (fun k => k ≠ M.star)) = Finset.univ.erase M.star := by
        ext k; simp [Finset.mem_erase]
      rw [hset]
    have hrep : (∑ i ∈ J, ∑ k ∈ (D i).erase M.star, M.wk c L k) ≤ (n + 1) * M.wmax c L := by
      have hterm : ∀ i ∈ J, (∑ k ∈ (D i).erase M.star, M.wk c L k)
          ≤ ((D i).erase M.star).card * M.wmax c L := by
        intro i hiJ
        calc (∑ k ∈ (D i).erase M.star, M.wk c L k)
            ≤ ∑ _k ∈ (D i).erase M.star, M.wmax c L := by
              refine Finset.sum_le_sum fun k hk => ?_
              refine M.le_supOthers ?_
              rw [Finset.mem_erase] at hk
              rw [DecayModel.others, Finset.mem_erase]
              exact ⟨hk.1, Finset.mem_univ k⟩
          _ = ((D i).erase M.star).card * M.wmax c L := by
              rw [Finset.sum_const, nsmul_eq_mul]
      refine (Finset.sum_le_sum hterm).trans ?_
      have hcard : ∀ i ∈ J, ((D i).erase M.star).card ≤ 1 + (if i = i0 then 1 else 0) := by
        intro i hiJ
        by_cases hi : i = i0
        · rw [if_pos hi]
          have h1 : ((D i).erase M.star).card ≤ (D i).card := Finset.card_erase_le
          have h2 := hDcard i hiJ
          omega
        · rw [if_neg hi, add_zero]
          have hsm : M.star ∈ D i := by
            rcases Finset.mem_union.mp (hstar_mem i hiJ) with h | h
            · exact absurd (Fin.ext ((mem_permSet.mp h).symm.trans (mem_permSet.mp hstar_perm))) hi
            · exact h
          rw [Finset.card_erase_of_mem hsm]
          have h2 := hDcard i hiJ
          omega
      have hsum : (∑ i ∈ J, ((D i).erase M.star).card) ≤ n + 1 := by
        have h1 : (∑ i ∈ J, ((D i).erase M.star).card)
            ≤ ∑ i ∈ J, (1 + (if i = i0 then 1 else 0)) := Finset.sum_le_sum hcard
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at h1
        have h2 : (∑ i ∈ J, (if i = i0 then 1 else 0)) ≤ 1 := by
          rw [Finset.sum_ite_eq' J i0 (fun _ => (1:ℕ))]; split <;> simp
        have h3 : J.card ≤ n := by
          calc J.card ≤ (Finset.univ : Finset (Fin n)).card :=
                Finset.card_le_card (Finset.subset_univ J)
            _ = n := by simp
        exact le_trans h1 (Nat.add_le_add h3 h2)
      calc (∑ i ∈ J, ((D i).erase M.star).card * M.wmax c L)
          = ((∑ i ∈ J, ((D i).erase M.star).card : ℕ) : ℝ) * M.wmax c L := by
            rw [← Finset.sum_mul, ← Nat.cast_sum]
        _ ≤ (n + 1) * M.wmax c L := by
            refine mul_le_mul_of_nonneg_right ?_ (M.wmax_nonneg hc L)
            exact_mod_cast hsum
    linarith

/-- `∑_{t∈S} (if p t then c else 0) = c · #{t ∈ S : p t}`. -/
lemma sum_ite_const (S : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] (c : ℝ) :
    (∑ t ∈ S, if p t then c else 0) = c * (S.filter p).card := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **Lemma C.1 (counting form).** After stabilisation (all active sets are of the form
`permSet i ∪ D i`, hence contain `k⋆` and no longer change), the weighted exploration cost of the
rounds `Tstart, …, T−1` is at most `C_λ(c; 0) = C(c)`. -/
theorem lemma_C_1_count {M : DecayModel n K} (R : GoodRun M) (hn : 0 < n) (c : Fin K → ℝ)
    (T Tstart : ℕ) (i0 : Fin n) (D : Fin n → Finset (Fin K))
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
      rw [← hact]; exact R.sel_mem t i
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
    refine le_trans (Finset.card_le_card ?_) (R.pair_budget T i hk)
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

end AnvBandit
