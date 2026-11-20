import AnvBandit.PublicBudget
import AnvBandit.BaselineBounds

/-! Finite, actual-public-fatigue positive-area accounting. Every count is an observed
round count; simultaneous pulls use the same pre-round public count. -/
noncomputable section
open scoped BigOperators
open Finset
set_option maxHeartbeats 1000000
namespace AnvBandit.BaselinePublicBudget
variable {n K : ℕ} {Ω : Type*}

def batch (I : ℕ → Fin n → Fin K) (t : ℕ) (k : Fin K) : ℕ :=
  ∑ i, if I t i = k then 1 else 0

def team (I : ℕ → Fin n → Fin K) (t : ℕ) (k : Fin K) : ℕ :=
  ∑ i, pullCount I t i k

def area (M : DecayModel n K) (I : ℕ → Fin n → Fin K)
    (T : ℕ) (i : Fin n) (k : Fin K) : ℝ :=
  ∑ t ∈ range T, if I t i = k then halfSeq M k (team I t k) else 0

lemma batch_le (I : ℕ → Fin n → Fin K) (t : ℕ) (k : Fin K) : batch I t k ≤ n := by
  calc batch I t k ≤ ∑ _i : Fin n, 1 := by
        apply sum_le_sum; intro i _; split <;> omega
    _ = n := by simp

lemma team_zero (I : ℕ → Fin n → Fin K) (k : Fin K) : team I 0 k = 0 := by
  simp [team, pullCount]

lemma team_succ (I : ℕ → Fin n → Fin K) (t : ℕ) (k : Fin K) :
    team I (t+1) k = team I t k + batch I t k := by
  simp only [team, pullCount_step, sum_add_distrib, batch]

lemma area_nonneg (M : DecayModel n K) (I : ℕ → Fin n → Fin K)
    (T : ℕ) (i : Fin n) (k : Fin K) : 0 ≤ area M I T i k := by
  apply sum_nonneg; intro t _; split
  · exact halfSeq_nonneg k _
  · exact le_rfl

lemma area_mono (M : DecayModel n K) (I : ℕ → Fin n → Fin K)
    (i : Fin n) (k : Fin K) : Monotone (fun T => area M I T i k) := by
  intro a b hab
  apply sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hab)
  intro t _ _; split
  · exact halfSeq_nonneg k _
  · exact le_rfl

lemma sum_area (M : DecayModel n K) (I : ℕ → Fin n → Fin K) (T : ℕ) (k : Fin K) :
    (∑ i, area M I T i k) = ∑ t ∈ range T, (batch I t k : ℝ) * halfSeq M k (team I t k) := by
  unfold area
  rw [sum_comm]
  apply sum_congr rfl; intro t _
  simp only [batch, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, sum_mul]
  apply sum_congr rfl; intro i _; split <;> simp_all

/-- The public excess is paid once by the whole team, not once per agent or phase. -/
theorem team_area_le (M : DecayModel n K) (I : ℕ → Fin n → Fin K)
    (T : ℕ) {k : Fin K} (hk : k ≠ M.star) :
    (∑ i, area M I T i k) ≤ M.Xi k := by
  rw [sum_area]
  have h := batch_divergence_le (halfSeq_antitone (M := M) k) (halfSeq_nonneg (M := M) k)
    (fun t => batch I t k) (fun t => team I t k) (team_zero I k)
    (fun t => team_succ I t k) (fun t => batch_le I t k) T
  apply le_trans h
  apply add_le_add
  · exact (summable_halfSeq hk).sum_le_tsum _ (fun s _ => halfSeq_nonneg k s)
  · exact le_rfl

lemma team_eq_actual (p : BaselineExecution.Params n K) (X : ℕ → Fin n → ℝ)
    (J : ℕ → Fin n → Fin n) (t : ℕ) (ht : t ≤ p.T) (k : Fin K) :
    team (BaselineExecution.I p X J) t k = BaselineExecution.teamCount p X J t k := by
  unfold team BaselineExecution.teamCount
  apply sum_congr rfl; intro i _
  exact BaselineExecution.pullCount_eq_N p X J t ht i k

/-- At the full observed count, capping does not remove any selected observation. -/
lemma sampleSum_count (sel : ℕ → Ω → Bool) (f : ℕ → Ω → ℝ) (T : ℕ) (ω : Ω) :
    ObservedPrefix.sampleSum sel f (ObservedPrefix.count sel T ω) T ω =
      ∑ t ∈ range T, if sel t ω then f t ω else 0 := by
  unfold ObservedPrefix.sampleSum
  apply sum_congr rfl; intro t ht
  by_cases hs : sel t ω = true
  · have hstep := ObservedPrefix.count_succ sel t ω
    have htT := mem_range.mp ht
    have hmono := ObservedPrefix.count_mono sel ω (show t+1 ≤ T by omega)
    dsimp only at hmono
    have hlt : ObservedPrefix.count sel t ω < ObservedPrefix.count sel T ω := by
      simp only [hs, Bool.true_eq, ite_true] at hstep
      omega
    simp [ObservedPrefix.capped, hs, hlt]
  · simp [ObservedPrefix.capped, hs]

open BaselineLaw BaselineBounds

lemma sampleSum_reward_at_count (p : BaselineExecution.Params n K)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n)
    (t : ℕ) (ht : t ≤ p.T) (ω : Ω) (i : Fin n) (k : Fin K) :
    ObservedPrefix.sampleSum (selected p X J i k) (reward X i k)
      (BaselineExecution.N p (realTape (X ω)) (J ω) t i k) t ω =
      BaselineExecution.Y p (realTape (X ω)) (J ω) t i k := by
  rw [← count_eq_N p X J i k t ht ω, sampleSum_count,
    BaselineExecution.Y_eq_sum p _ _ t ht]
  simp [selected, reward]

lemma public_meanSum_le (M : DecayModel n K) (p : BaselineExecution.Params n K)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n)
    (t : ℕ) (ht : t ≤ p.T) (ω : Ω) (i : Fin n) (k : Fin K) :
    ObservedPrefix.sampleSum (selected p X J i k) (mean M p 1 X J i k)
      (BaselineExecution.N p (realTape (X ω)) (J ω) t i k) t ω ≤
      (BaselineExecution.N p (realTape (X ω)) (J ω) t i k : ℝ) * (M.b k + M.gap k / 2) +
        area M (BaselineExecution.I p (realTape (X ω)) (J ω)) t i k := by
  rw [← count_eq_N p X J i k t ht ω, sampleSum_count, count_eq_N p X J i k t ht ω]
  have heq : (BaselineExecution.N p (realTape (X ω)) (J ω) t i k : ℝ) * (M.b k + M.gap k / 2) +
      area M (BaselineExecution.I p (realTape (X ω)) (J ω)) t i k =
      ∑ s ∈ range t, if BaselineExecution.I p (realTape (X ω)) (J ω) s i = k then
        M.b k + M.gap k / 2 + halfSeq M k (team (BaselineExecution.I p (realTape (X ω)) (J ω)) s k) else 0 := by
    rw [BaselineExecution.N_eq_sum p _ _ t ht, Nat.cast_sum, sum_mul, area, ← sum_add_distrib]
    apply sum_congr rfl; intro s _; split <;> simp_all
  rw [heq]
  apply sum_le_sum; intro s hs
  by_cases hk : BaselineExecution.I p (realTape (X ω)) (J ω) s i = k
  · simp only [selected, hk, decide_true, Bool.true_eq, ite_true]
    rw [team_eq_actual p _ _ s (by have := mem_range.mp hs; omega)]
    simp only [mean, actualMean, hk, DecayModel.mean, effectiveUse, Fin.isValue,
      show (1 : Fin 2) ≠ 0 by decide, if_false]
    have hp := le_max_left (M.f k (BaselineExecution.teamCount p (realTape (X ω)) (J ω) s k + 1) - M.gap k / 2) 0
    dsimp [halfSeq, posPart]
    rw [Nat.add_comm 1]
    linarith
  · simp [selected, hk]

/-- Selection-time mean comparison from the *current* observed prefix only. -/
theorem public_selection_core (M : DecayModel n K) (p : BaselineExecution.Params n K)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n)
    (ω : Ω) (t : ℕ) (ht : t < p.T) (i : Fin n) (k : Fin K)
    (hg : ω ∈ ObservedPrefix.good (selected p X J) (reward X) (mean M p 1 X J) t p.L)
    (hact : M.star ∈ ((BaselineExecution.run p (realTape (X ω)) (J ω) t).nodes i).active)
    (hsel : BaselineExecution.I p (realTape (X ω)) (J ω) t i = k)
    (hm : 1 ≤ BaselineExecution.N p (realTape (X ω)) (J ω) t i k) :
    (BaselineExecution.N p (realTape (X ω)) (J ω) t i k : ℝ) * M.gap k ≤
      (BaselineExecution.N p (realTape (X ω)) (J ω) t i k : ℝ) * (M.gap k / 2) +
      area M (BaselineExecution.I p (realTape (X ω)) (J ω)) t i k +
      2 * (BaselineExecution.N p (realTape (X ω)) (J ω) t i k : ℝ) *
        rdelta p.L (BaselineExecution.N p (realTape (X ω)) (J ω) t i k) := by
  let m := BaselineExecution.N p (realTape (X ω)) (J ω) t i k
  let ms := BaselineExecution.N p (realTape (X ω)) (J ω) t i M.star
  have hu := BaselineExecution.LocalState.choose_spec p ((BaselineExecution.run p (realTape (X ω)) (J ω) t).nodes i)
  change BaselineExecution.N p (realTape (X ω)) (J ω) t i (BaselineExecution.I p (realTape (X ω)) (J ω) t i) = 0 ∨
    (∀ a ∈ ((BaselineExecution.run p (realTape (X ω)) (J ω) t).nodes i).active,
      1 ≤ BaselineExecution.N p (realTape (X ω)) (J ω) t i a ∧
      BaselineExecution.Y p (realTape (X ω)) (J ω) t i a / BaselineExecution.N p (realTape (X ω)) (J ω) t i a +
        rdelta p.L (BaselineExecution.N p (realTape (X ω)) (J ω) t i a) ≤
      BaselineExecution.Y p (realTape (X ω)) (J ω) t i (BaselineExecution.I p (realTape (X ω)) (J ω) t i) /
        BaselineExecution.N p (realTape (X ω)) (J ω) t i (BaselineExecution.I p (realTape (X ω)) (J ω) t i) +
        rdelta p.L (BaselineExecution.N p (realTape (X ω)) (J ω) t i (BaselineExecution.I p (realTape (X ω)) (J ω) t i))) at hu
  rw [hsel] at hu
  obtain ⟨hms, hucb⟩ : 1 ≤ ms ∧
      BaselineExecution.Y p (realTape (X ω)) (J ω) t i M.star / ms + rdelta p.L ms ≤
      BaselineExecution.Y p (realTape (X ω)) (J ω) t i k / m + rdelta p.L m := by
    rcases hu with hz | hall
    · omega
    · have h := hall M.star hact
      exact h
  have hck := ObservedPrefix.good_empirical_mean (selected p X J) (reward X)
    (mean M p 1 X J) hg i k m hm (by rw [count_eq_N p X J i k t ht.le])
  have hcs := ObservedPrefix.good_empirical_mean (selected p X J) (reward X)
    (mean M p 1 X J) hg i M.star ms hms (by rw [count_eq_N p X J i M.star t ht.le])
  rw [sampleSum_reward_at_count p X J t ht.le ω i k] at hck
  rw [sampleSum_reward_at_count p X J t ht.le ω i M.star] at hcs
  have hlo : M.b M.star ≤
      ObservedPrefix.sampleSum (selected p X J i M.star) (mean M p 1 X J i M.star) ms t ω / ms := by
    apply (ObservedPrefix.observed_mean_bounds (selected p X J i M.star)
      (mean M p 1 X J i M.star) (M.b M.star) (M.f M.star) hms
      (by rw [count_eq_N p X J i M.star t ht.le]) ?_).1
    intro s hs hselS
    have hkS : BaselineExecution.I p (realTape (X ω)) (J ω) s i = M.star := by simpa [selected] using hselS
    have hlow := (actualMean_bounds M p 1 (X ω) (J ω) s i).1
    have hupp := actualMean_le_personal_envelope M p 1 (X ω) (J ω) s i
    rw [hkS] at hlow hupp
    rw [count_eq_N p X J i M.star s (by omega)]
    exact ⟨hlow, by simpa [mean, Nat.add_comm] using hupp⟩
  have hchain : M.b M.star ≤
      ObservedPrefix.sampleSum (selected p X J i k) (mean M p 1 X J i k) m t ω / m +
      2 * rdelta p.L m := by
    have hk' := (abs_le.mp hck).2
    have hs' := (abs_le.mp hcs).1
    linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmul := mul_le_mul_of_nonneg_left hchain hmR.le
  rw [mul_add, mul_div_cancel₀ _ hmR.ne'] at hmul
  have hpub := public_meanSum_le M p X J t ht.le ω i k
  change (m : ℝ) * M.gap k ≤ _
  dsimp only [m] at hmul
  unfold DecayModel.gap at hpub ⊢
  dsimp only [m]
  nlinarith

/-- Arbitrary trajectory-chosen rounds, each charged only when its already observed
prefix is good. No future good event and no permanent/infinite-prefix assumption is used. -/
theorem selected_times_bound (M : DecayModel n K) (p : BaselineExecution.Params n K)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n)
    (ω : Ω) (i : Fin n) (k : Fin K) (hk : k ≠ M.star) (S : Finset ℕ)
    (hS : ∀ t ∈ S, t < p.T ∧
      M.star ∈ ((BaselineExecution.run p (realTape (X ω)) (J ω) t).nodes i).active ∧
      BaselineExecution.I p (realTape (X ω)) (J ω) t i = k ∧
      ω ∈ ObservedPrefix.good (selected p X J) (reward X) (mean M p 1 X J) t p.L) :
    (S.card : ℝ) ≤ (M.nkAll p.L k : ℝ) + 4 / M.gap k *
      area M (BaselineExecution.I p (realTape (X ω)) (J ω)) p.T i k := by
  have hgap := M.gap_pos hk
  have hL : 0 < p.L := Ldelta_pos p.hn p.hK p.hT p.hδ.1 p.hδ.2
  have hb : 0 ≤ 4 / M.gap k := div_nonneg (by norm_num) hgap.le
  have hnk1 := M.one_le_nkAll p.L hL k
  have hE := area_nonneg M (BaselineExecution.I p (realTape (X ω)) (J ω)) p.T i k
  rcases S.eq_empty_or_nonempty with he | hn
  · rw [he]; simp only [card_empty, Nat.cast_zero]
    positivity
  · let t := S.max' hn
    have htmem : t ∈ S := S.max'_mem hn
    obtain ⟨htT, hact, hsel, hg⟩ := hS t htmem
    let m := BaselineExecution.N p (realTape (X ω)) (J ω) t i k
    have hcard : S.card ≤ m + 1 := by
      have hsub : S ⊆ (range (t+1)).filter (fun s => BaselineExecution.I p (realTape (X ω)) (J ω) s i = k) := by
        intro s hs
        exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (Finset.le_max' S s hs)), (hS s hs).2.2.1⟩
      have hc := card_le_card hsub
      have heq : ((range (t+1)).filter (fun s => BaselineExecution.I p (realTape (X ω)) (J ω) s i = k)).card =
          BaselineExecution.N p (realTape (X ω)) (J ω) (t+1) i k := by
        rw [BaselineExecution.N_eq_sum p _ _ (t+1) (by omega), ← sum_filter]
        simp
      rw [heq, BaselineExecution.N_step p _ _ htT i k, if_pos hsel] at hc
      exact hc
    have hcardR : (S.card : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hcard
    have hnkR : (1 : ℝ) ≤ (M.nkAll p.L k : ℝ) := by exact_mod_cast hnk1
    rcases lt_or_ge m (M.nkAll p.L k) with hsmall | hlarge
    · have hcn : S.card ≤ M.nkAll p.L k := by omega
      have hcr : (S.card : ℝ) ≤ (M.nkAll p.L k : ℝ) := by exact_mod_cast hcn
      nlinarith [mul_nonneg hb hE]
    · have hm : 1 ≤ m := le_trans hnk1 hlarge
      have hcore := public_selection_core M p X J ω t htT i k hg hact hsel hm
      have hnk : nk p.L (M.gap k) ≤ m := by simpa [DecayModel.nkAll, hk] using hlarge
      have hquarter := two_rdelta_le_quarter p.L (M.gap k) hL.le hgap hnk
      have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      have hel : (m : ℝ) * M.gap k / 4 ≤
          area M (BaselineExecution.I p (realTape (X ω)) (J ω)) t i k := by
        nlinarith [mul_le_mul_of_nonneg_left hquarter hmR]
      have hmon := area_mono M (BaselineExecution.I p (realTape (X ω)) (J ω)) i k htT.le
      have hmle : (m : ℝ) ≤ 4 / M.gap k * area M (BaselineExecution.I p (realTape (X ω)) (J ω)) p.T i k := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hgap]
        nlinarith
      nlinarith

/-- Any selected node-arm pairs share a single positive-part budget for each arm.
The pure statistical term is charged only to the chosen pairs. -/
theorem weighted_selected_pairs_bound (M : DecayModel n K) (p : BaselineExecution.Params n K)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n)
    (ω : Ω) (c : Fin K → ℝ) (hc : ∀ k, 0 ≤ c k)
    (P : Finset (Fin n × Fin K)) (hP : ∀ z ∈ P, z.2 ≠ M.star)
    (S : Fin n → Fin K → Finset ℕ)
    (hS : ∀ z ∈ P, ∀ t ∈ S z.1 z.2, t < p.T ∧
      M.star ∈ ((BaselineExecution.run p (realTape (X ω)) (J ω) t).nodes z.1).active ∧
      BaselineExecution.I p (realTape (X ω)) (J ω) t z.1 = z.2 ∧
      ω ∈ ObservedPrefix.good (selected p X J) (reward X) (mean M p 1 X J) t p.L) :
    (∑ z ∈ P, c z.2 * (S z.1 z.2).card) ≤
      (∑ z ∈ P, c z.2 * (M.nkAll p.L z.2 : ℝ)) + M.Bpub c := by
  have hpair : ∀ z ∈ P, c z.2 * (S z.1 z.2).card ≤
      c z.2 * (M.nkAll p.L z.2 : ℝ) +
      (4 * (c z.2 / M.gap z.2)) * area M (BaselineExecution.I p (realTape (X ω)) (J ω)) p.T z.1 z.2 := by
    intro z hz
    have h := mul_le_mul_of_nonneg_left
      (selected_times_bound M p X J ω z.1 z.2 (hP z hz) (S z.1 z.2) (hS z hz)) (hc z.2)
    calc c z.2 * (S z.1 z.2).card ≤ c z.2 * ((M.nkAll p.L z.2 : ℝ) +
          4 / M.gap z.2 * area M (BaselineExecution.I p (realTape (X ω)) (J ω)) p.T z.1 z.2) := h
      _ = _ := by ring
  have harea : (∑ z ∈ P, (4 * (c z.2 / M.gap z.2)) *
      area M (BaselineExecution.I p (realTape (X ω)) (J ω)) p.T z.1 z.2) ≤ M.Bpub c := by
    have hsub : P ⊆ univ ×ˢ M.others := by
      intro z hz
      exact mem_product.mpr ⟨mem_univ _, by simpa [DecayModel.others] using hP z hz⟩
    calc (∑ z ∈ P, (4 * (c z.2 / M.gap z.2)) *
          area M (BaselineExecution.I p (realTape (X ω)) (J ω)) p.T z.1 z.2)
        ≤ ∑ z ∈ univ ×ˢ M.others, (4 * (c z.2 / M.gap z.2)) *
          area M (BaselineExecution.I p (realTape (X ω)) (J ω)) p.T z.1 z.2 := by
            apply sum_le_sum_of_subset_of_nonneg hsub
            intro z hz _
            have hk : z.2 ≠ M.star := by simpa [DecayModel.others] using (mem_product.mp hz).2
            exact mul_nonneg (mul_nonneg (by norm_num) (div_nonneg (hc _) (M.gap_pos hk).le)) (area_nonneg M _ _ _ _)
      _ = ∑ k ∈ M.others, (4 * (c k / M.gap k)) *
          ∑ i, area M (BaselineExecution.I p (realTape (X ω)) (J ω)) p.T i k := by
            rw [sum_product, sum_comm]
            apply sum_congr rfl; intro k _
            rw [mul_sum]
      _ ≤ ∑ k ∈ M.others, (4 * (c k / M.gap k)) * M.Xi k := by
            apply sum_le_sum; intro k hk
            have hne : k ≠ M.star := by simpa [DecayModel.others] using hk
            exact mul_le_mul_of_nonneg_left (team_area_le M _ _ hne)
              (mul_nonneg (by norm_num) (div_nonneg (hc k) (M.gap_pos hne).le))
      _ = M.Bpub c := by unfold DecayModel.Bpub; rw [mul_sum]; apply sum_congr rfl; intro k _; ring
  have hsum := sum_le_sum hpair
  rw [sum_add_distrib] at hsum
  exact le_trans hsum (add_le_add_right harea _)

/-- The actual holding-selection set; arm reinsertion does not reset this set. -/
def holdingTimes (M : DecayModel n K) (p : BaselineExecution.Params n K)
    (X : ℕ → Fin n → Bool) (J : ℕ → Fin n → Fin n) (i : Fin n) (k : Fin K) : Finset ℕ :=
  (range p.T).filter (fun t => M.star ∈ ((BaselineExecution.run p (realTape X) J t).nodes i).active ∧
    BaselineExecution.I p (realTape X) J t i = k)

/-- Global holding cost, with the precise public/personal minimum `F₁(c)`. -/
theorem holding_cost_le_F1 (M : DecayModel n K) (p : BaselineExecution.Params n K)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n)
    (ω : Ω) (c : Fin K → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hg : ω ∈ ObservedPrefix.good (selected p X J) (reward X) (mean M p 1 X J) p.T p.L) :
    (∑ i, ∑ k ∈ M.others, c k * (holdingTimes M p (X ω) (J ω) i k).card) ≤ M.Flam c p.L 1 := by
  change _ ≤ min _ _
  apply le_min
  · let R := goodRunOn M p 1 X J ω hg
    have hpair : ∀ i k, k ∈ M.others →
        c k * (holdingTimes M p (X ω) (J ω) i k).card ≤ c k * (M.mkAll p.L k : ℝ) := by
      intro i k hk
      have hne : k ≠ M.star := by simpa [DecayModel.others] using hk
      have h := R.pair_budget i hne
      have hcN : (holdingTimes M p (X ω) (J ω) i k).card ≤ M.mkAll p.L k := h
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcN) (hc k)
    calc (∑ i, ∑ k ∈ M.others, c k * (holdingTimes M p (X ω) (J ω) i k).card)
        ≤ ∑ _i : Fin n, M.Wsum c p.L := by
          apply sum_le_sum; intro i _
          exact sum_le_sum (fun k hk => hpair i k hk)
      _ = n * M.Wsum c p.L := by simp
  · have hpub := weighted_selected_pairs_bound M p X J ω c hc (univ ×ˢ M.others)
      (by intro z hz; simpa [DecayModel.others] using (mem_product.mp hz).2)
      (holdingTimes M p (X ω) (J ω)) (by
        intro z hz t ht
        obtain ⟨htT, ha, hs⟩ := mem_filter.mp ht
        exact ⟨mem_range.mp htT, ha, hs,
          ObservedPrefix.good_prefix _ _ _ (mem_range.mp htT).le hg⟩)
    rw [sum_product, sum_product] at hpub
    have heq : (∑ i : Fin n, ∑ k ∈ M.others, c k * (M.nkAll p.L k : ℝ)) =
        n * M.WNsum c p.L := by simp [DecayModel.WNsum, DecayModel.wkN]
    rwa [heq] at hpub


end AnvBandit.BaselinePublicBudget
