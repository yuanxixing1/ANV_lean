import AnvBandit.Terminal

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-!
# Public positive-part budget and per-node selection counts (Proposition A.6)

This file closes Proposition A.6 of Appendix A.3 (equations (A.10)-(A.12)) genuinely, i.e. without
carrying the paper's key bounds as hypotheses.

The analytic core is the batch-comparison inequality (A.4): for a nonincreasing nonnegative sequence
`w` and a schedule whose `j`-th nonempty batch uses `x_j ∈ [1,n]` fresh samples starting from the
running count `c_j = ∑_{j'<j} x_{j'}`,
`0 ≤ ∑_j x_j w(c_j) − ∑_{s<c_J} w(s) ≤ (n−1) w(0)`.

Specialising `w` to `s ↦ [f_k(s) − Δ_k/2]_+` and reading the batches off a trajectory of Algorithm 1
turns this into the team positive-part budget (A.10) `∑_i E_{i,k}(N_{i,k}(T)) ≤ Ξ_k`; combining it
with the concentration comparison (A.13)/(A.14) yields the per-node selection-count bounds
(A.11)/(A.12).
-/

noncomputable section
open scoped BigOperators
open Finset

namespace AnvBandit

variable {n K : ℕ}

/-! ### (A.4) the batch-comparison inequality -/

/-- Per-batch divergence of (A.4): `E_w(c,x) = x·w(c) − ∑_{s<x} w(c+s)`. -/
def batchEv (w : ℕ → ℝ) (c x : ℕ) : ℝ :=
  (x : ℝ) * w c - ∑ s ∈ Finset.range x, w (c + s)

lemma batchEv_nonneg {w : ℕ → ℝ} (hw : Antitone w) (c x : ℕ) : 0 ≤ batchEv w c x := by
  have h : batchEv w c x = ∑ s ∈ Finset.range x, (w c - w (c + s)) := by
    rw [batchEv, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [h]
  exact Finset.sum_nonneg fun s _ => sub_nonneg.mpr (hw (Nat.le_add_right c s))

/-- Per-batch upper bound of (A.4): with `x ≥ 1` samples sharing the same usage `c+1`,
`E_w(c,x) ≤ (x−1)(w(c) − w(c+x−1))`. -/
lemma batchEv_le {w : ℕ → ℝ} (hw : Antitone w) (c x : ℕ) :
    batchEv w c x ≤ ((x - 1 : ℕ) : ℝ) * (w c - w (c + x - 1)) := by
  rcases Nat.eq_zero_or_pos x with hx | hx
  · subst hx
    simp [batchEv]
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, (Nat.succ_pred_eq_of_pos hx).symm⟩
  have hsplit : (∑ s ∈ Finset.range (y + 1), w (c + s))
      = w c + ∑ s ∈ Finset.range y, w (c + (s + 1)) := by
    rw [Finset.sum_range_succ']
    ring_nf
  have hy0 : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg y
  have hge : (y : ℝ) * w (c + (y + 1) - 1) ≤ ∑ s ∈ Finset.range y, w (c + (s + 1)) := by
    rw [show (y : ℝ) * w (c + (y + 1) - 1)
          = ∑ _s ∈ Finset.range y, w (c + (y + 1) - 1) by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]]
    refine Finset.sum_le_sum fun s hs => ?_
    rw [Finset.mem_range] at hs
    refine hw ?_
    omega
  have hstep : batchEv w c (y + 1) = (y : ℝ) * w c - ∑ s ∈ Finset.range y, w (c + (s + 1)) := by
    rw [batchEv, hsplit, Nat.cast_add, Nat.cast_one]
    ring
  have hcast : ((y + 1 - 1 : ℕ) : ℝ) = (y : ℝ) := by simp
  rw [hcast, hstep]
  have : (y : ℝ) * w c - ∑ s ∈ Finset.range y, w (c + (s + 1))
      ≤ (y : ℝ) * w c - (y : ℝ) * w (c + (y + 1) - 1) := by linarith [hge]
  calc (y : ℝ) * w c - ∑ s ∈ Finset.range y, w (c + (s + 1))
      ≤ (y : ℝ) * w c - (y : ℝ) * w (c + (y + 1) - 1) := this
    _ = (y : ℝ) * (w c - w (c + (y + 1) - 1)) := by ring

/-- Identity underlying (A.4): the divergence `∑_j x_j w(c_j) − ∑_{s<c_J} w(s)` is the sum of the
per-batch divergences. -/
lemma batch_divergence_eq {w : ℕ → ℝ} (x c : ℕ → ℕ) (hc0 : c 0 = 0)
    (hstep : ∀ t, c (t + 1) = c t + x t) (T : ℕ) :
    (∑ t ∈ Finset.range T, (x t : ℝ) * w (c t)) - (∑ s ∈ Finset.range (c T), w s)
      = ∑ t ∈ Finset.range T, batchEv w (c t) (x t) := by
  induction T with
  | zero => simp [hc0, batchEv]
  | succ T ih =>
    rw [hstep T,
      Finset.sum_range_succ (f := fun t => (x t : ℝ) * w (c t)),
      Finset.sum_range_succ (f := fun t => batchEv w (c t) (x t)),
      Finset.sum_range_add, ← ih, batchEv]
    ring

/-- (A.4), lower bound: the batch sum dominates the plain running sum. -/
theorem batch_divergence_ge {w : ℕ → ℝ} (hw : Antitone w)
    (x c : ℕ → ℕ) (hc0 : c 0 = 0) (hstep : ∀ t, c (t + 1) = c t + x t) (T : ℕ) :
    (∑ s ∈ Finset.range (c T), w s) ≤ ∑ t ∈ Finset.range T, (x t : ℝ) * w (c t) := by
  have h := batch_divergence_eq (w := w) x c hc0 hstep T
  have hnn : 0 ≤ ∑ t ∈ Finset.range T, batchEv w (c t) (x t) :=
    Finset.sum_nonneg fun t _ => batchEv_nonneg hw (c t) (x t)
  linarith [h ▸ hnn]

/-- (A.4), upper bound: with batch sizes `x_t ≤ n`, the batch sum exceeds the plain running sum by
at most `(n−1) w(0)`. -/
theorem batch_divergence_le {w : ℕ → ℝ} (hw : Antitone w) (hwpos : ∀ s, 0 ≤ w s)
    (x c : ℕ → ℕ) (hc0 : c 0 = 0) (hstep : ∀ t, c (t + 1) = c t + x t)
    (hx : ∀ t, x t ≤ n) (T : ℕ) :
    (∑ t ∈ Finset.range T, (x t : ℝ) * w (c t))
      ≤ (∑ s ∈ Finset.range (c T), w s) + ((n - 1 : ℕ) : ℝ) * w 0 := by
  have key : ∀ T, (∑ t ∈ Finset.range T, (x t : ℝ) * w (c t)) - (∑ s ∈ Finset.range (c T), w s)
      ≤ ((n - 1 : ℕ) : ℝ) * (w 0 - w (c T - 1)) := by
    intro T
    induction T with
    | zero => simp [hc0]
    | succ T ih =>
      have hdiff : (∑ t ∈ Finset.range (T + 1), (x t : ℝ) * w (c t))
          - (∑ s ∈ Finset.range (c (T + 1)), w s)
          = ((∑ t ∈ Finset.range T, (x t : ℝ) * w (c t)) - (∑ s ∈ Finset.range (c T), w s))
            + batchEv w (c T) (x T) := by
        rw [hstep T,
          Finset.sum_range_succ (f := fun t => (x t : ℝ) * w (c t)),
          Finset.sum_range_add, batchEv]
        ring
      rw [hdiff]
      rcases Nat.eq_zero_or_pos (x T) with hx0 | hxT
      · have hb : batchEv w (c T) (x T) = 0 := by rw [hx0, batchEv]; simp
        rw [hb, add_zero]
        have hcT : c (T + 1) = c T := by rw [hstep T, hx0, Nat.add_zero]
        rw [hcT]
        exact ih
      · have hb := batchEv_le hw (c T) (x T)
        have hxc : ((x T - 1 : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.sub_le_sub_right (hx T) 1
        have hnonneg : 0 ≤ w (c T) - w (c T + x T - 1) :=
          sub_nonneg.mpr (hw (by omega))
        have h1 : batchEv w (c T) (x T)
            ≤ ((n - 1 : ℕ) : ℝ) * (w (c T) - w (c (T + 1) - 1)) := by
          have hcx : c T + x T - 1 = c (T + 1) - 1 := by rw [hstep T]
          rw [hcx] at hb hnonneg
          refine le_trans hb ?_
          exact mul_le_mul_of_nonneg_right hxc hnonneg
        have h2 : w (c T) - w (c (T + 1) - 1) ≤ w (c T - 1) - w (c (T + 1) - 1) := by
          have := hw (show c T - 1 ≤ c T by omega)
          linarith
        have hN : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        calc ((∑ t ∈ Finset.range T, (x t : ℝ) * w (c t)) - (∑ s ∈ Finset.range (c T), w s))
              + batchEv w (c T) (x T)
            ≤ ((n - 1 : ℕ) : ℝ) * (w 0 - w (c T - 1))
              + ((n - 1 : ℕ) : ℝ) * (w (c T) - w (c (T + 1) - 1)) := add_le_add ih h1
          _ ≤ ((n - 1 : ℕ) : ℝ) * (w 0 - w (c T - 1))
              + ((n - 1 : ℕ) : ℝ) * (w (c T - 1) - w (c (T + 1) - 1)) :=
              add_le_add le_rfl (mul_le_mul_of_nonneg_left h2 hN)
          _ = ((n - 1 : ℕ) : ℝ) * (w 0 - w (c (T + 1) - 1)) := by ring
  have hk := key T
  have hfin : ((n - 1 : ℕ) : ℝ) * (w 0 - w (c T - 1)) ≤ ((n - 1 : ℕ) : ℝ) * w 0 := by
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    linarith [hwpos (c T - 1)]
  linarith [hk, hfin]

/-! ### The public effective-usage sequence and (A.10) -/

/-- The half-threshold sequence `s ↦ [f_k(s+1) − Δ_k/2]_+` whose partial sums are `E_{i,k}`. -/
def halfSeq {n K : ℕ} (M : DecayModel n K) (k : Fin K) : ℕ → ℝ :=
  fun s => posPart (M.f k (s + 1) - M.gap k / 2)

/-- The statistical threshold controls the radius by `Δ/4`: for `m ≥ n_k`, `2 r_δ(m) ≤ Δ/4`. -/
lemma two_rdelta_le_quarter (L Δ : ℝ) (hL : 0 ≤ L) (hΔ : 0 < Δ) {m : ℕ}
    (hm : nk L Δ ≤ m) : 2 * rdelta L m ≤ Δ / 4 := by
  have hceil : 32 * L / Δ ^ 2 ≤ (nk L Δ : ℝ) := Nat.le_ceil _
  have hmR : 32 * L / Δ ^ 2 ≤ (m : ℝ) := le_trans hceil (by exact_mod_cast hm)
  have hΔ2 : 0 < Δ ^ 2 := pow_pos hΔ 2
  have h32 : 32 * L ≤ Δ ^ 2 * m := by rw [div_le_iff₀ hΔ2] at hmR; linarith
  have hfrac : L / (2 * m) ≤ Δ ^ 2 / 64 := by
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0
      rw [Nat.cast_zero, mul_zero, div_zero]; positivity
    · have hmR0 : (0 : ℝ) < m := by exact_mod_cast hm0
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * m)]
      nlinarith [h32, hL, hmR0]
  have hsqrt : rdelta L m ≤ Δ / 8 := by
    rw [rdelta]
    have := Real.sqrt_le_sqrt hfrac
    have hs : Real.sqrt (Δ ^ 2 / 64) = Δ / 8 := by
      rw [Real.sqrt_div (by positivity), Real.sqrt_sq_eq_abs, abs_of_pos hΔ]; norm_num
    rwa [hs] at this
  linarith

namespace DecayModel
variable {n K : ℕ} (M : DecayModel n K)

/-- The statistical threshold is at least `1` once `L > 0`. -/
lemma one_le_nkAll (L : ℝ) (hL : 0 < L) (k : Fin K) : 1 ≤ M.nkAll L k := by
  rw [nkAll]
  split
  · exact le_refl 1
  · rename_i hk
    have hg : 0 < M.gap k := M.gap_pos hk
    have hx : 0 < 32 * L / M.gap k ^ 2 := by positivity
    have hc : 32 * L / M.gap k ^ 2 ≤ ((nk L (M.gap k) : ℕ) : ℝ) := Nat.le_ceil _
    have hne : (nk L (M.gap k) : ℕ) ≠ 0 := by
      intro h0; rw [h0] at hc; simp at hc; linarith
    omega

end DecayModel

lemma halfSeq_nonneg {M : DecayModel n K} (k : Fin K) : ∀ s, 0 ≤ halfSeq M k s :=
  fun s => posPart_nonneg _

lemma halfSeq_antitone {M : DecayModel n K} (k : Fin K) : Antitone (halfSeq M k) := by
  intro a b hab
  refine max_le_max ?_ le_rfl
  exact sub_le_sub_right (M.f_anti k (Nat.add_le_add_right hab 1)) _

lemma halfSeq_zero {M : DecayModel n K} (k : Fin K) : halfSeq M k 0 = M.Ahalf k := rfl

lemma summable_halfSeq {M : DecayModel n K} {k : Fin K} (hk : k ≠ M.star) :
    Summable (halfSeq M k) := by
  have hg : 0 < M.gap k / 2 := by have := M.gap_pos hk; linarith
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (M.f_tendsto k) (M.gap k / 2) hg
  apply summable_of_ne_finset_zero (s := Finset.range N)
  intro s hs
  have hsN : N ≤ s := by simpa [Finset.mem_range, not_lt] using hs
  have hlt : M.f k (s + 1) < M.gap k / 2 := by
    have := hN (s + 1) (le_trans hsN (Nat.le_succ s))
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (M.f_nonneg k (s + 1))] at this
  rw [halfSeq]
  exact posPart_eq_zero_of_nonpos (by linarith : M.f k (s + 1) - M.gap k / 2 ≤ 0)

lemma tsum_halfSeq {M : DecayModel n K} (k : Fin K) : ∑' s, halfSeq M k s = M.Dhalf k := rfl

namespace GoodRun

variable {M : DecayModel n K}

/-- Number of nodes pulling arm `k` in round `t+1`. -/
def pullCnt (R : GoodRun M) (t : ℕ) (k : Fin K) : ℕ :=
  (Finset.univ.filter (fun i => R.I t i = k)).card

/-- Total number of team pulls of arm `k` among rounds `1..T`. -/
def teamCount (R : GoodRun M) (T : ℕ) (k : Fin K) : ℕ :=
  ∑ t ∈ Finset.range T, R.pullCnt t k

lemma pullCnt_le (R : GoodRun M) (t : ℕ) (k : Fin K) : R.pullCnt t k ≤ n := by
  rw [pullCnt]
  calc (Finset.univ.filter (fun i => R.I t i = k)).card ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = n := by rw [Finset.card_univ, Fintype.card_fin]

lemma teamCount_zero (R : GoodRun M) (k : Fin K) : R.teamCount 0 k = 0 := by
  simp [teamCount]

lemma teamCount_succ (R : GoodRun M) (k : Fin K) (T : ℕ) :
    R.teamCount (T + 1) k = R.teamCount T k + R.pullCnt T k := by
  simp [teamCount, Finset.sum_range_succ]

lemma teamCount_eq_sum_N (R : GoodRun M) (T : ℕ) (k : Fin K) :
    R.teamCount T k = ∑ i, R.N T i k := by
  have hN : ∀ T, (∑ i, R.N T i k)
      = ∑ t ∈ Finset.range T, R.pullCnt t k := by
    intro T
    induction T with
    | zero => simp [R.Nzero]
    | succ T ih =>
      have hstep : (∑ i, R.N (T + 1) i k) = (∑ i, R.N T i k) + R.pullCnt T k := by
        calc (∑ i, R.N (T + 1) i k)
            = ∑ i, (R.N T i k + if R.I T i = k then 1 else 0) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [R.Nstep T i k]
          _ = (∑ i, R.N T i k) + ∑ i, (if R.I T i = k then 1 else 0) :=
              Finset.sum_add_distrib
          _ = (∑ i, R.N T i k) + R.pullCnt T k := by
              congr 1
              rw [pullCnt, ← Finset.sum_filter]
              simp
      rw [hstep, ih, Finset.sum_range_succ]
  rw [teamCount, hN]

/-- The public positive-part area `E_{i,k}(N_{i,k}(T))`: each pull in round `t+1` uses the effective
public count `teamCount t k + 1`, so its contribution is `[f_k(teamCount t k + 1) − Δ_k/2]_+`. -/
def EikRound (R : GoodRun M) (T : ℕ) (i : Fin n) (k : Fin K) : ℝ :=
  ∑ t ∈ (Finset.range T).filter (fun t => R.I t i = k), halfSeq M k (R.teamCount t k)

/-- Regrouping the team positive-part area by rounds (equation (A.10)'s identity). -/
lemma sum_EikRound (R : GoodRun M) (T : ℕ) (k : Fin K) :
    (∑ i, R.EikRound T i k)
      = ∑ t ∈ Finset.range T, (R.pullCnt t k : ℝ) * halfSeq M k (R.teamCount t k) := by
  have h1 : ∀ i, R.EikRound T i k
      = ∑ t ∈ Finset.range T, (if R.I t i = k then halfSeq M k (R.teamCount t k) else 0) := by
    intro i
    rw [EikRound, Finset.sum_filter]
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [pullCnt, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- **(A.10), the team positive-part budget.** `∑_i E_{i,k}(N_{i,k}(T)) ≤ Ξ_k`. -/
theorem team_pos_budget (R : GoodRun M) (T : ℕ) {k : Fin K} (hk : k ≠ M.star) :
    (∑ i, R.EikRound T i k) ≤ M.Xi k := by
  rw [R.sum_EikRound T k]
  have hbd := batch_divergence_le (w := halfSeq M k) (halfSeq_antitone (M := M) k)
    (halfSeq_nonneg (M := M) k)
    (fun t => R.pullCnt t k) (fun t => R.teamCount t k)
    (R.teamCount_zero k) (fun t => R.teamCount_succ k t) (fun t => R.pullCnt_le t k) T
  refine le_trans hbd ?_
  have hpart : (∑ s ∈ Finset.range (R.teamCount T k), halfSeq M k s) ≤ M.Dhalf k := by
    have h := (summable_halfSeq hk).sum_le_tsum (Finset.range (R.teamCount T k))
      (fun s _ => halfSeq_nonneg (M := M) k s)
    rwa [tsum_halfSeq (M := M) k] at h
  have hfin : (∑ s ∈ Finset.range (R.teamCount T k), halfSeq M k s)
        + ((n - 1 : ℕ) : ℝ) * halfSeq M k 0
      ≤ M.Dhalf k + ((n - 1 : ℕ) : ℝ) * M.Ahalf k :=
    add_le_add hpart (le_of_eq (by rw [halfSeq_zero]))
  refine le_trans hfin (le_of_eq ?_)
  rw [DecayModel.Xi]

/-- The personal count as an indicator sum: `N T i k = ∑_{t<T} [I_t(i) = k]`. -/
lemma N_eq_sum (R : GoodRun M) (i : Fin n) (k : Fin K) (T : ℕ) :
    R.N T i k = ∑ t ∈ Finset.range T, (if R.I t i = k then 1 else 0) := by
  induction T with
  | zero => rw [R.Nzero, Finset.sum_range_zero]
  | succ T ih => rw [R.Nstep T i k, ih, Finset.sum_range_succ]

lemma N_eq_card (R : GoodRun M) (i : Fin n) (k : Fin K) (T : ℕ) :
    R.N T i k = ((Finset.range T).filter (fun t => R.I t i = k)).card := by
  rw [R.N_eq_sum i k T, ← Finset.sum_filter]
  simp

/-- The personal public positive-part area `E_{i,k}(N_{i,k}(T))`, using the effective usage
sequence `q`: the `s`-th personal pull of `k` contributes `[f_k(q_{i,k,s}) − Δ_k/2]_+`. -/
def EikPers (R : GoodRun M) (q : Fin n → Fin K → ℕ → ℕ) (T : ℕ) (i : Fin n) (k : Fin K) : ℝ :=
  ∑ s ∈ Finset.range (R.N T i k), halfSeq M k (q i k (s + 1) - 1)

lemma EikPers_nonneg (R : GoodRun M) (q : Fin n → Fin K → ℕ → ℕ) (T : ℕ) (i : Fin n)
    (k : Fin K) : 0 ≤ R.EikPers q T i k :=
  Finset.sum_nonneg fun s _ => halfSeq_nonneg (M := M) k _

/-- Consistency of the two descriptions of `E_{i,k}`: if the `s`-th pull of `k` by `i` in round
`t+1` uses public count `teamCount t k + 1`, the personal and round descriptions agree. -/
lemma EikPers_eq_EikRound (R : GoodRun M) (q : Fin n → Fin K → ℕ → ℕ)
    (hqteam : ∀ t i k, R.I t i = k → q i k (R.N t i k + 1) = R.teamCount t k + 1)
    (T : ℕ) (i : Fin n) (k : Fin K) :
    R.EikPers q T i k = R.EikRound T i k := by
  have key : ∀ T, (∑ s ∈ Finset.range (R.N T i k), halfSeq M k (q i k (s + 1) - 1))
      = ∑ t ∈ Finset.range T, (if R.I t i = k then halfSeq M k (R.teamCount t k) else 0) := by
    intro T
    induction T with
    | zero => rw [R.Nzero]; simp
    | succ T ih =>
      rw [R.Nstep T i k]
      by_cases hIk : R.I T i = k
      · rw [if_pos hIk,
          Finset.sum_range_succ (f := fun s => halfSeq M k (q i k (s + 1) - 1)),
          Finset.sum_range_succ (f := fun t =>
            (if R.I t i = k then halfSeq M k (R.teamCount t k) else 0)),
          if_pos hIk, ih, hqteam T i k hIk]
        simp
      · rw [if_neg hIk, add_zero,
          Finset.sum_range_succ (f := fun t =>
            (if R.I t i = k then halfSeq M k (R.teamCount t k) else 0)),
          if_neg hIk, add_zero, ih]
  rw [EikPers, EikRound, Finset.sum_filter]
  exact key T

end GoodRun

/-- **(A.13) core.** On the concentration event, if `k⋆` is active and the suboptimal arm `k` has
`m ≥ 1` prior personal pulls, then `m·Δ_k ≤ ∑_{s<m} f_k(q_{i,k,s}) + 2m r_δ(m)`. -/
theorem selection_gap_core {M : DecayModel n K} (R : GoodRun M)
    (q : Fin n → Fin K → ℕ → ℕ)
    (hpq : ∀ i k s, 1 ≤ s → R.p i k s = M.b k + M.f k (q i k s))
    {i : Fin n} {k : Fin K} (hk : k ≠ M.star) {t : ℕ}
    (hact : M.star ∈ R.active t i) (hsel : R.I t i = k) (hm : 1 ≤ R.N t i k) :
    (R.N t i k : ℝ) * M.gap k
      ≤ (∑ s ∈ Finset.range (R.N t i k), M.f k (q i k (s + 1)))
        + 2 * (R.N t i k : ℝ) * rdelta R.L (R.N t i k) := by
  have hm0R : (0 : ℝ) < (R.N t i k : ℝ) := by exact_mod_cast hm
  have hucb := R.ucb t i hact
  rw [hsel] at hucb
  obtain ⟨hms, hineq⟩ : 1 ≤ R.N t i M.star ∧
      R.bhat i M.star (R.N t i M.star) + rdelta R.L (R.N t i M.star)
        ≤ R.bhat i k (R.N t i k) + rdelta R.L (R.N t i k) := by
    rcases hucb with h | h
    · rw [h] at hm; omega
    · exact ⟨h.2.1, h.2.2⟩
  have hcK := R.hc i k (R.N t i k) hm
  have hcS := R.hc i M.star (R.N t i M.star) hms
  have hbstar : M.b M.star ≤ R.bhat i M.star (R.N t i M.star) + rdelta R.L (R.N t i M.star) := by
    have h2 : (∑ s ∈ Finset.range (R.N t i M.star), R.p i M.star (s + 1)) / (R.N t i M.star)
        ≤ R.bhat i M.star (R.N t i M.star) + rdelta R.L (R.N t i M.star) := by
      have := (abs_le.mp hcS).1; linarith
    have h3 := (M.prefix_bounds (R.hp i) (k := M.star) hms).1
    linarith
  have hFid : (∑ s ∈ Finset.range (R.N t i k), R.p i k (s + 1))
      = (R.N t i k : ℝ) * M.b k + ∑ s ∈ Finset.range (R.N t i k), M.f k (q i k (s + 1)) := by
    rw [Finset.sum_congr rfl (fun s hs => hpq i k (s + 1) (by
          rw [Finset.mem_range] at hs; omega)),
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hUk : R.bhat i k (R.N t i k) ≤ M.b k
      + (∑ s ∈ Finset.range (R.N t i k), M.f k (q i k (s + 1))) / (R.N t i k)
      + rdelta R.L (R.N t i k) := by
    have h2 := (abs_le.mp hcK).2
    have heq2 : (∑ s ∈ Finset.range (R.N t i k), R.p i k (s + 1)) / (R.N t i k)
        = M.b k + (∑ s ∈ Finset.range (R.N t i k), M.f k (q i k (s + 1))) / (R.N t i k) := by
      rw [hFid, add_div, mul_div_cancel_left₀ _ hm0R.ne']
    linarith [h2, heq2]
  have hchain : M.b M.star ≤ M.b k
      + (∑ s ∈ Finset.range (R.N t i k), M.f k (q i k (s + 1))) / (R.N t i k)
      + 2 * rdelta R.L (R.N t i k) := by linarith [hbstar, hineq, hUk]
  rw [DecayModel.gap]
  have hkey : M.b M.star - M.b k
      ≤ (∑ s ∈ Finset.range (R.N t i k), M.f k (q i k (s + 1))) / (R.N t i k)
        + 2 * rdelta R.L (R.N t i k) := by linarith [hchain]
  have hmul := mul_le_mul_of_nonneg_left hkey hm0R.le
  have heq : (R.N t i k : ℝ) *
        ((∑ s ∈ Finset.range (R.N t i k), M.f k (q i k (s + 1))) / (R.N t i k)
          + 2 * rdelta R.L (R.N t i k))
      = (∑ s ∈ Finset.range (R.N t i k), M.f k (q i k (s + 1)))
        + 2 * (R.N t i k : ℝ) * rdelta R.L (R.N t i k) := by
    rw [mul_add, mul_div_cancel₀ _ hm0R.ne']; ring
  rw [heq] at hmul
  linarith [hmul]

/-- **(A.11).** On `E_δ`, `A⁺_{i,k}(T) ≤ n_k + (4/Δ_k) E_{i,k}(N_{i,k}(T))`. -/
theorem node_selection_bound {M : DecayModel n K} (R : GoodRun M)
    (q : Fin n → Fin K → ℕ → ℕ)
    (hpq : ∀ i k s, 1 ≤ s → R.p i k s = M.b k + M.f k (q i k s))
    (hqge : ∀ i k s, 1 ≤ s → s ≤ q i k s) (hL : 0 < R.L)
    (T : ℕ) {i : Fin n} {k : Fin K} (hk : k ≠ M.star) :
    (R.AplusCount T i k : ℝ) ≤ (M.nkAll R.L k : ℝ) + 4 / M.gap k * R.EikPers q T i k := by
  have hgap := M.gap_pos hk
  have hb0 : 0 ≤ 4 / M.gap k := div_nonneg (by norm_num) hgap.le
  have hnk1 : (1 : ℝ) ≤ (M.nkAll R.L k : ℝ) :=
    by exact_mod_cast DecayModel.one_le_nkAll (M := M) R.L hL k
  set S : Finset ℕ := (Finset.range T).filter (fun t => M.star ∈ R.active t i ∧ R.I t i = k)
    with hS
  have hAplus : R.AplusCount T i k = S.card := rfl
  have hE0 : 0 ≤ R.EikPers q T i k := R.EikPers_nonneg q T i k
  rcases S.eq_empty_or_nonempty with hE | hNE
  · rw [hAplus, hE]
    simp only [Finset.card_empty, Nat.cast_zero]
    have hn0 : (0 : ℝ) ≤ (M.nkAll R.L k : ℝ) := Nat.cast_nonneg _
    nlinarith [hn0, hE0, hb0]
  · obtain ⟨t', ht'mem, ht'max⟩ : ∃ t' ∈ S, ∀ s ∈ S, s ≤ t' :=
      ⟨S.max' hNE, S.max'_mem hNE, fun s hs => Finset.le_max' S s hs⟩
    have hmem := Finset.mem_filter.mp ht'mem
    have hselk : R.I t' i = k := hmem.2.2
    have hact : M.star ∈ R.active t' i := hmem.2.1
    have ht'T : t' < T := Finset.mem_range.mp hmem.1
    have hcard_le : S.card ≤ R.N (t' + 1) i k := by
      rw [R.N_eq_card i k (t' + 1)]
      refine Finset.card_le_card ?_
      intro s hs
      rw [Finset.mem_filter]
      have hsS := Finset.mem_filter.mp (hS ▸ hs)
      exact ⟨Finset.mem_range.mpr (lt_of_le_of_lt (ht'max s hs) (Nat.lt_succ_self t')), hsS.2.2⟩
    have hstep : R.N (t' + 1) i k = R.N t' i k + 1 := by rw [R.Nstep, if_pos hselk]
    have hAle : (S.card : ℝ) ≤ (R.N t' i k : ℝ) + 1 := by
      have h1 : S.card ≤ R.N t' i k + 1 := le_trans hcard_le (le_of_eq hstep)
      exact_mod_cast h1
    rcases Nat.eq_zero_or_pos (R.N t' i k) with hm0 | hmpos
    · rw [hAplus]
      have hm0R : (R.N t' i k : ℝ) = 0 := by rw [hm0]; norm_num
      nlinarith [hnk1, hAle, hm0R, hb0, hE0]
    · have hcore := selection_gap_core R q hpq hk hact hselk hmpos
      have hmT : R.N t' i k ≤ R.N T i k := R.N_mono i k (le_of_lt ht'T)
      have hEm_le : (∑ s ∈ Finset.range (R.N t' i k), halfSeq M k (q i k (s + 1) - 1))
          ≤ R.EikPers q T i k := by
        rw [GoodRun.EikPers]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hmT)
          (fun s _ _ => halfSeq_nonneg (M := M) k _)
      have hhE : (∑ s ∈ Finset.range (R.N t' i k), halfSeq M k (q i k (s + 1) - 1))
          = ∑ s ∈ Finset.range (R.N t' i k), posPart (M.f k (q i k (s + 1)) - M.gap k / 2) := by
        refine Finset.sum_congr rfl fun s hs => ?_
        rw [halfSeq, Nat.sub_add_cancel (le_trans (by omega) (hqge i k (s + 1) (by omega)))]
      rcases Nat.lt_or_ge (R.N t' i k) (M.nkAll R.L k) with hmlt | hmnk
      · -- m < n_k
        rw [hAplus]
        have h1 : S.card ≤ M.nkAll R.L k := by omega
        have h1R : (S.card : ℝ) ≤ (M.nkAll R.L k : ℝ) := by exact_mod_cast h1
        nlinarith [h1R, hb0, hE0]
      · -- m ≥ n_k
        have hmnk' : nk R.L (M.gap k) ≤ R.N t' i k := by
          have h := hmnk
          rw [DecayModel.nkAll] at h
          rwa [dif_neg hk] at h
        have hquarter : 2 * rdelta R.L (R.N t' i k) ≤ M.gap k / 4 :=
          two_rdelta_le_quarter R.L (M.gap k) hL.le hgap hmnk'
        have hmR : (0 : ℝ) ≤ (R.N t' i k : ℝ) := Nat.cast_nonneg _
        have hFgear : 3 * ((R.N t' i k : ℝ) * M.gap k) / 4
            ≤ ∑ s ∈ Finset.range (R.N t' i k), M.f k (q i k (s + 1)) := by
          nlinarith [hcore, mul_le_mul_of_nonneg_left hquarter hmR]
        have hElb : (R.N t' i k : ℝ) * M.gap k / 4
            ≤ ∑ s ∈ Finset.range (R.N t' i k), halfSeq M k (q i k (s + 1) - 1) := by
          rw [hhE]
          have h1 : (∑ s ∈ Finset.range (R.N t' i k),
                (M.f k (q i k (s + 1)) - M.gap k / 2))
              ≤ ∑ s ∈ Finset.range (R.N t' i k), posPart (M.f k (q i k (s + 1)) - M.gap k / 2) :=
            Finset.sum_le_sum fun s _ => le_max_left _ _
          have h2 : (∑ s ∈ Finset.range (R.N t' i k), (M.f k (q i k (s + 1)) - M.gap k / 2))
              = (∑ s ∈ Finset.range (R.N t' i k), M.f k (q i k (s + 1)))
                - (R.N t' i k : ℝ) * (M.gap k / 2) := by
            rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          nlinarith [h1, h2, hFgear]
        have hm_le : (R.N t' i k : ℝ) ≤ 4 / M.gap k
            * (∑ s ∈ Finset.range (R.N t' i k), halfSeq M k (q i k (s + 1) - 1)) := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hgap]
          nlinarith [hElb]
        have h4 : 4 / M.gap k * (∑ s ∈ Finset.range (R.N t' i k), halfSeq M k (q i k (s + 1) - 1))
            ≤ 4 / M.gap k * R.EikPers q T i k := mul_le_mul_of_nonneg_left hEm_le hb0
        rw [hAplus]
        nlinarith [hAle, hm_le, h4, hnk1]

/-- **(A.12).** For any node subset `J`, `∑_{i∈J} A⁺_{i,k}(T) ≤ |J| n_k + 4 Ξ_k/Δ_k`. -/
theorem subset_selection_bound {M : DecayModel n K} (R : GoodRun M)
    (q : Fin n → Fin K → ℕ → ℕ)
    (hpq : ∀ i k s, 1 ≤ s → R.p i k s = M.b k + M.f k (q i k s))
    (hqge : ∀ i k s, 1 ≤ s → s ≤ q i k s)
    (hqteam : ∀ t i k, R.I t i = k → q i k (R.N t i k + 1) = R.teamCount t k + 1)
    (hL : 0 < R.L) (T : ℕ) {k : Fin K} (hk : k ≠ M.star) (J : Finset (Fin n)) :
    (∑ i ∈ J, (R.AplusCount T i k : ℝ))
      ≤ (J.card : ℝ) * (M.nkAll R.L k : ℝ) + 4 / M.gap k * M.Xi k := by
  have hgap := M.gap_pos hk
  have hb0 : 0 ≤ 4 / M.gap k := div_nonneg (by norm_num) hgap.le
  have hnode : ∀ i, (R.AplusCount T i k : ℝ)
      ≤ (M.nkAll R.L k : ℝ) + 4 / M.gap k * R.EikPers q T i k :=
    fun i => node_selection_bound R q hpq hqge hL T hk
  have hteam : (∑ i, R.EikPers q T i k) ≤ M.Xi k := by
    have h1 : (∑ i, R.EikPers q T i k) = ∑ i, R.EikRound T i k := by
      refine Finset.sum_congr rfl fun i _ => ?_
      exact R.EikPers_eq_EikRound q hqteam T i k
    rw [h1]; exact R.team_pos_budget T hk
  calc (∑ i ∈ J, (R.AplusCount T i k : ℝ))
      ≤ ∑ i ∈ J, ((M.nkAll R.L k : ℝ) + 4 / M.gap k * R.EikPers q T i k) :=
        Finset.sum_le_sum fun i _ => hnode i
    _ = (J.card : ℝ) * (M.nkAll R.L k : ℝ) + 4 / M.gap k * ∑ i ∈ J, R.EikPers q T i k := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    _ ≤ (J.card : ℝ) * (M.nkAll R.L k : ℝ) + 4 / M.gap k * M.Xi k := by
        refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hb0)
        exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J)
          (fun i _ _ => R.EikPers_nonneg q T i k)) hteam

end AnvBandit
