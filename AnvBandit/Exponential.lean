import AnvBandit.Model

/-!
# Proposition A.4: the exact exponential benchmark

For an exponential instance `f_k(s) = a_k e^{−η_k (s−1)}` (with `a_k ≥ 0`, `η_k > 0`) the paper's
Proposition A.4 states that the joint optimum `V^{⋆,1}_t` of the public-fatigue benchmark equals
the sum of the `t` largest elements of the merged, non-increasing marginal sequences
`n (b_k + a_k e^{−η_k n q})`, `q = 0, 1, 2, …`, attained by the synchronous greedy policy (each
round all `n` agents pull the current population-best arm).

The helper `proposition_A_4` proves only `expBench = greedyVal`, i.e. the maximum synchronous
value over all batch schedules equals that top-`t` sum. The full-domain bridge is in
`ExponentialDP`; recursive greedy-policy realization is a separate obligation.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section
open scoped BigOperators
open Finset

namespace AnvBandit

variable {n K : ℕ}

/-- The exponential instance `f_k(s) = a_k e^{−η_k (s−1)}`. -/
def IsExponential {n K : ℕ} (M : DecayModel n K) (a eta : Fin K → ℝ) : Prop :=
  (∀ k, 0 ≤ a k) ∧ (∀ k, 0 < eta k) ∧ ∀ k (s : ℕ), 1 ≤ s →
    M.f k s = a k * Real.exp (-(eta k) * ((s : ℝ) - 1))

/-- Merged marginal value `n (b_k + a_k e^{−η_k n j})` at the merged index `(k, j)`. -/
def margVal (n : ℕ) {K : ℕ} (b a eta : Fin K → ℝ) (x : Fin K × ℕ) : ℝ :=
  n * (b x.1 + a x.1 * Real.exp (-(eta x.1) * (n * (x.2 : ℝ))))

/-- Synchronous value of a public-fatigue batch schedule `u : Fin t → Fin K` for the exponential
instance: round `r` has all `n` agents pull arm `u r`, so the count of arm `u r` before round `r`
is `n · #{s < r : u s = u r}`. -/
def syncExpVal (n : ℕ) {K : ℕ} (b a eta : Fin K → ℝ) {t : ℕ} (u : Fin t → Fin K) : ℝ :=
  ∑ r : Fin t, n * (b (u r) + a (u r) *
    Real.exp (-(eta (u r)) * (n * ((Finset.univ.filter (fun s : Fin t => s < r ∧ u s = u r)).card))))

/-- Restricted synchronous benchmark: maximum of `syncExpVal` over schedules where all agents
use one common arm in each round. Equality to the full joint benchmark is proved separately. -/
def expBench (n : ℕ) {K : ℕ} (hK : 0 < K) (b a eta : Fin K → ℝ) (t : ℕ) : ℝ :=
  (Finset.univ : Finset (Fin t → Fin K)).sup'
    ⟨fun _ => ⟨0, hK⟩, Finset.mem_univ _⟩ (syncExpVal n b a eta)

/-- The top-marginal value appearing in Proposition A.4: maximum size-`t` subset sum of
`n (b_k + a_k e^{−η_k n q})`, `q ≥ 0`. Identification with a recursively implemented greedy
policy requires a separate realization proof; it is not built into this definition. -/
def greedyVal (n : ℕ) {K : ℕ} (hK : 0 < K) (b a eta : Fin K → ℝ) (t : ℕ) : ℝ :=
  ((Finset.univ : Finset (Fin K × Fin t)).powersetCard t).sup'
    (Finset.powersetCard_nonempty.mpr
      (by rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
          exact Nat.le_mul_of_pos_left t hK))
    (fun S => ∑ x ∈ S, margVal n b a eta (x.1, (x.2 : ℕ)))

/-- Number of earlier rounds with the same arm as round `r`. -/
def occ {t : ℕ} (u : Fin t → Fin K) (r : Fin t) : ℕ :=
  (Finset.univ.filter (fun s : Fin t => s < r ∧ u s = u r)).card

lemma occ_lt {t : ℕ} (u : Fin t → Fin K) (r : Fin t) : occ u r < t := by
  have hsub : (Finset.univ.filter (fun s : Fin t => s < r ∧ u s = u r)) ⊆
      Finset.univ.filter (fun s : Fin t => s < r) := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact hs.1
  calc occ u r ≤ (Finset.univ.filter (fun s : Fin t => s < r)).card := Finset.card_le_card hsub
    _ = r.val := by
        rw [show (Finset.univ.filter (fun s : Fin t => s < r)) = Finset.Iio r from by ext s; simp,
            Fin.card_Iio]
    _ < t := r.isLt

lemma occ_strict {t : ℕ} (u : Fin t → Fin K) {r r' : Fin t} (h : r < r') (huk : u r = u r') :
    occ u r < occ u r' := by
  have hsub : (Finset.univ.filter (fun s : Fin t => s < r ∧ u s = u r)) ⊆
      (Finset.univ.filter (fun s : Fin t => s < r' ∧ u s = u r')) := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact ⟨lt_trans hs.1 h, by rw [hs.2, huk]⟩
  have hmem : r ∈ (Finset.univ.filter (fun s : Fin t => s < r' ∧ u s = u r')) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨h, huk⟩
  have hnot : r ∉ (Finset.univ.filter (fun s : Fin t => s < r ∧ u s = u r)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and]
    exact fun hr => absurd hr (lt_irrefl r)
  exact Finset.card_lt_card ⟨hsub, fun ht => hnot (ht hmem)⟩

lemma occ_pair_inj {t : ℕ} (u : Fin t → Fin K) :
    Set.InjOn (fun r : Fin t => (u r, (⟨occ u r, occ_lt u r⟩ : Fin t)))
      (↑(Finset.univ : Finset (Fin t))) := by
  intro r _ r' _ heq
  have hu : u r = u r' := congrArg Prod.fst heq
  have ho : occ u r = occ u r' := by
    have h := congrArg (fun x : Fin K × Fin t => (x.2 : ℕ)) heq
    simpa using h
  rcases lt_trichotomy r r' with h | h | h
  · exact absurd ho (ne_of_lt (occ_strict u h hu))
  · exact h
  · exact absurd ho (ne_of_gt (occ_strict u h hu.symm))

/-- Direction (≤): every schedule value is the sum over a size-`t` subset of the merged
marginals, hence at most `greedyVal`. -/
theorem expBench_le_greedyVal (n : ℕ) {K : ℕ} (hK : 0 < K) (b a eta : Fin K → ℝ) (t : ℕ) :
    expBench n hK b a eta t ≤ greedyVal n hK b a eta t := by
  rw [expBench, greedyVal]
  refine (Finset.sup'_le_iff _ _).mpr (fun u _ => ?_)
  let f : Fin t → Fin K × Fin t := fun r => (u r, ⟨occ u r, occ_lt u r⟩)
  have hinj : Set.InjOn f (↑(Finset.univ : Finset (Fin t))) := occ_pair_inj u
  have himgcard : (Finset.univ.image f).card = t := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_univ, Fintype.card_fin]
  have hmem : (Finset.univ.image f)
      ∈ (Finset.univ : Finset (Fin K × Fin t)).powersetCard t := by
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, himgcard⟩
  have hsum : syncExpVal n b a eta u
      = ∑ x ∈ (Finset.univ.image f), margVal n b a eta (x.1, (x.2 : ℕ)) := by
    rw [Finset.sum_image (f := fun x : Fin K × Fin t => margVal n b a eta (x.1, (x.2 : ℕ))) hinj]
    rw [syncExpVal]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    simp only [f, occ, margVal]
  rw [hsum]
  exact Finset.le_sup' (f := fun S => ∑ x ∈ S, margVal n b a eta (x.1, (x.2 : ℕ))) hmem


/-! ### Direction (≥): the greedy top-`t` sum is achieved by a schedule -/

/-- A schedule `u : Fin t → Fin K` with prescribed counts `q`. -/
lemma exists_sched_with_counts {K : ℕ} (q : Fin K → ℕ) (t : ℕ) (hq : ∑ k, q k = t) :
    ∃ u : Fin t → Fin K, ∀ k, (Finset.univ.filter (fun r : Fin t => u r = k)).card = q k := by
  classical
  have sigma_mk_eq_iff : ∀ (k : Fin K) (j : ℕ) (p : Σ _ : Fin K, ℕ),
      (⟨k, j⟩ : Σ _ : Fin K, ℕ) = p ↔ k = p.1 ∧ j = p.2 := by
    intro k j p
    obtain ⟨a, b⟩ := p
    simp
  set P : Finset (Σ _ : Fin K, ℕ) := (Finset.univ : Finset (Fin K)).sigma
    (fun k => Finset.range (q k)) with hP
  have hcardP : P.card = t := by
    rw [hP, Finset.card_sigma]; simp only [Finset.card_range]; exact hq
  set e : (↥P) ≃ Fin t := Finset.equivFinOfCardEq hcardP with he
  refine ⟨fun r => ((e.symm r : ↥P) : Σ _ : Fin K, ℕ).1, fun k => ?_⟩
  have hPk : (P.filter (fun p : Σ _ : Fin K, ℕ => p.1 = k))
      = (Finset.range (q k)).image (fun j => (⟨k, j⟩ : Σ _ : Fin K, ℕ)) := by
    ext p
    rw [Finset.mem_filter, Finset.mem_image, hP, Finset.mem_sigma]
    simp only [Finset.mem_univ, true_and, Finset.mem_range, sigma_mk_eq_iff]
    constructor
    · rintro ⟨hb, hp1⟩
      exact ⟨p.2, by rwa [← hp1], hp1.symm, rfl⟩
    · rintro ⟨j, hj, hk1, hj2⟩
      exact ⟨by rw [← hj2, ← hk1]; exact hj, hk1.symm⟩
  have hcardPk : (P.filter (fun p : Σ _ : Fin K, ℕ => p.1 = k)).card = q k := by
    rw [hPk, Finset.card_image_of_injOn]
    · simp
    · intro a _ b _ hab
      exact (sigma_mk_eq_iff k a _).mp hab |>.2
  have hmain : (Finset.univ.filter (fun r : Fin t =>
        ((e.symm r : ↥P) : Σ _ : Fin K, ℕ).1 = k)).card
      = (P.filter (fun p : Σ _ : Fin K, ℕ => p.1 = k)).card := by
    refine Finset.card_bij
      (fun (r : Fin t) (_ : r ∈ Finset.univ.filter (fun r : Fin t =>
          ((e.symm r : ↥P) : Σ _ : Fin K, ℕ).1 = k))
        => ((e.symm r : ↥P) : Σ _ : Fin K, ℕ)) ?_ ?_ ?_
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      exact ⟨(e.symm r).2, hr⟩
    · intro r1 _ r2 _ heq
      have h1 : (e.symm r1 : ↥P) = (e.symm r2 : ↥P) := Subtype.val_injective heq
      exact e.symm.injective h1
    · intro p hp
      simp only [Finset.mem_filter] at hp
      refine ⟨e ⟨p, hp.1⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [e.symm_apply_apply]; exact hp.2
      · rw [e.symm_apply_apply]
  rw [hmain, hcardPk]

/-- The merged marginal sequence `j ↦ n (b_k + a_k e^{−η_k n j})` is non-increasing. -/
lemma margVal_antitone (n : ℕ) (b a eta : Fin K → ℝ) (k : Fin K)
    (ha : 0 ≤ a k) (heta : 0 < eta k) :
    Antitone (fun j : ℕ => margVal n b a eta (k, j)) := by
  intro j j' hjj
  simp only [margVal]
  have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg _
  have hexp : Real.exp (-(eta k) * (n * (j' : ℝ))) ≤ Real.exp (-(eta k) * (n * (j : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have hnj : (n:ℝ) * (j:ℝ) ≤ (n:ℝ) * (j':ℝ) :=
      mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hjj) hn
    nlinarith [hnj, heta]
  have hna : (0:ℝ) ≤ (n:ℝ) * a k := mul_nonneg hn ha
  nlinarith [hna, hexp]

/-- For an order embedding `e : Fin q ↪o Fin t`, the `i`-th value is at least `i`. -/
lemma orderEmb_self_le {q t : ℕ} (e : Fin q ↪o Fin t) (i : Fin q) : (i : ℕ) ≤ (e i : ℕ) := by
  have key : ∀ n (hn : n < q), n ≤ ((e ⟨n, hn⟩ : Fin t) : ℕ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0; exact Nat.zero_le _
      · have hpred : n - 1 < n := Nat.sub_one_lt (Nat.pos_iff_ne_zero.mp hpos)
        have hpredq : n - 1 < q := by omega
        have hlt : (⟨n-1, hpredq⟩ : Fin q) < ⟨n, hn⟩ := by simp only [Fin.lt_def]; omega
        have hstrict := e.strictMono hlt
        simp only [Fin.lt_def] at hstrict
        have hih := ih (n-1) hpred hpredq
        omega
  exact key i.val i.isLt

/-- Prefix domination: for an antitone `v`, the sum over any `q`-element subset is at most the sum
over the initial segment `{0, …, q−1}`. -/
lemma prefix_dom {t : ℕ} (v : Fin t → ℝ) (hv : Antitone v) (T : Finset (Fin t)) (q : ℕ)
    (hcard : T.card = q) (hle : q ≤ t) :
    ∑ j ∈ T, v j ≤ ∑ i : Fin q, v (Fin.castLE hle i) := by
  rw [← Finset.map_orderEmbOfFin_univ T hcard]
  rw [Finset.sum_map]
  refine Finset.sum_le_sum (fun i _ => hv ?_)
  have hthis := orderEmb_self_le (T.orderEmbOfFin hcard) i
  simp only [Fin.le_def, Fin.val_castLE]
  simpa using hthis

/-- Count of earlier rounds with the same arm is strictly below the total number of rounds using
that arm. -/
lemma occ_lt_card_fiber {t : ℕ} (u : Fin t → Fin K) (r : Fin t) :
    occ u r < (Finset.univ.filter (fun s : Fin t => u s = u r)).card := by
  have hsub : (Finset.univ.filter (fun s : Fin t => s < r ∧ u s = u r)) ⊆
      (Finset.univ.filter (fun s : Fin t => u s = u r)) := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact hs.2
  have hmem : r ∈ (Finset.univ.filter (fun s : Fin t => u s = u r)) := by simp
  have hnot : r ∉ (Finset.univ.filter (fun s : Fin t => s < r ∧ u s = u r)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and]
    exact fun h => absurd h (lt_irrefl r)
  exact Finset.card_lt_card ⟨hsub, fun ht => hnot (ht hmem)⟩

/-- On the occurrences of a fixed arm `k`, the earlier-count map `occ u` is injective. -/
lemma occ_injOn {t : ℕ} (u : Fin t → Fin K) (k : Fin K) :
    Set.InjOn (occ u) (↑(Finset.univ.filter (fun r : Fin t => u r = k))) := by
  intro r hr r' hr' heq
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hr hr'
  have hk : u r = u r' := by rw [hr, hr']
  rcases lt_trichotomy r r' with h | h | h
  · exact absurd heq (ne_of_lt (occ_strict u h hk))
  · exact h
  · exact absurd heq (ne_of_gt (occ_strict u h hk.symm))

/-- On the occurrences of a fixed arm `k`, the earlier-count map `occ u` has image exactly
`{0, …, (#occurrences − 1)}`. -/
lemma occ_image_eq_range {t : ℕ} (u : Fin t → Fin K) (k : Fin K) :
    (Finset.univ.filter (fun r : Fin t => u r = k)).image (occ u)
      = Finset.range ((Finset.univ.filter (fun r : Fin t => u r = k)).card) := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨r, hr, rfl⟩ := hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    rw [Finset.mem_range]
    rw [← hr]
    exact occ_lt_card_fiber u r
  · rw [Finset.card_image_of_injOn (occ_injOn u k)]; simp

/-- The synchronous value of a schedule is the sum, over arms, of the merged marginals indexed by
the occurrences of that arm. -/
lemma syncExpVal_eq_sum (n : ℕ) (b a eta : Fin K → ℝ) {t : ℕ} (u : Fin t → Fin K) :
    syncExpVal n b a eta u
      = ∑ k : Fin K, ∑ j ∈ Finset.range ((Finset.univ.filter (fun r : Fin t => u r = k)).card),
          margVal n b a eta (k, j) := by
  rw [syncExpVal]
  have h1 : (∑ r : Fin t, n * (b (u r) + a (u r) *
        Real.exp (-(eta (u r)) * (n * ((Finset.univ.filter (fun s : Fin t =>
          s < r ∧ u s = u r)).card)))))
      = ∑ r : Fin t, margVal n b a eta (u r, occ u r) := by
    refine Finset.sum_congr rfl (fun r _ => ?_)
    simp only [occ, margVal]
  rw [h1]
  rw [← Finset.sum_fiberwise_of_maps_to (g := u) (fun r _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hcongr : (∑ r ∈ (Finset.univ.filter (fun r : Fin t => u r = k)),
        margVal n b a eta (u r, occ u r))
      = ∑ r ∈ (Finset.univ.filter (fun r : Fin t => u r = k)), margVal n b a eta (k, occ u r) :=
    Finset.sum_congr rfl (fun r hr => by rw [(Finset.mem_filter.mp hr).2])
  rw [hcongr, ← Finset.sum_image (f := fun j : ℕ => margVal n b a eta (k, j)) (occ_injOn u k),
    occ_image_eq_range]

/-- Direction (≥): the top-`t` sum `greedyVal` is achieved by a batch schedule, hence at most
`expBench`. -/
theorem greedyVal_le_expBench (n : ℕ) {K : ℕ} (hK : 0 < K) (b a eta : Fin K → ℝ) (t : ℕ)
    (ha : ∀ k, 0 ≤ a k) (heta : ∀ k, 0 < eta k) :
    greedyVal n hK b a eta t ≤ expBench n hK b a eta t := by
  classical
  rw [greedyVal, expBench]
  refine (Finset.sup'_le_iff _ _).mpr (fun S hS => ?_)
  have hcardS : S.card = t := (Finset.mem_powersetCard.mp hS).2
  set q : Fin K → ℕ := fun k => (S.filter (fun x : Fin K × Fin t => x.1 = k)).card with hqdef
  have hqsum : ∑ k, q k = t := by
    have h := Finset.card_eq_sum_card_fiberwise
      (f := (Prod.fst : Fin K × Fin t → Fin K)) (s := S) (t := Finset.univ)
      (fun x _ => Finset.mem_univ _)
    rw [hqdef]
    rw [← h, hcardS]
  obtain ⟨u, hu⟩ := exists_sched_with_counts q t hqsum
  have hsync : syncExpVal n b a eta u
      = ∑ k, ∑ j ∈ Finset.range (q k), margVal n b a eta (k, j) := by
    rw [syncExpVal_eq_sum]
    refine Finset.sum_congr rfl (fun k _ => by rw [hu k])
  have hSle : (∑ x ∈ S, margVal n b a eta (x.1, (x.2 : ℕ)))
      ≤ ∑ k, ∑ j ∈ Finset.range (q k), margVal n b a eta (k, j) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := (Prod.fst : Fin K × Fin t → Fin K))
      (fun x _ => Finset.mem_univ _) (f := fun x : Fin K × Fin t => margVal n b a eta (x.1, (x.2 : ℕ)))]
    refine Finset.sum_le_sum (fun k _ => ?_)
    have hinj : Set.InjOn (fun x : Fin K × Fin t => (x.2 : Fin t))
        (↑(S.filter (fun x : Fin K × Fin t => x.1 = k))) := by
      intro x hx x' hx' heq
      simp only [Finset.mem_coe, Finset.mem_filter] at hx hx'
      exact Prod.ext (by rw [hx.2, hx'.2]) heq
    have hcardT : ((S.filter (fun x : Fin K × Fin t => x.1 = k)).image
        (fun x : Fin K × Fin t => (x.2 : Fin t))).card = q k := by
      rw [hqdef, Finset.card_image_of_injOn hinj]
    have hle : q k ≤ t := by
      rw [hqdef]; exact (Finset.card_filter_le S _).trans_eq hcardS
    have hv : Antitone (fun j : Fin t => margVal n b a eta (k, (j : ℕ))) :=
      fun j j' h => margVal_antitone n b a eta k (ha k) (heta k) h
    calc (∑ x ∈ (S.filter (fun x : Fin K × Fin t => x.1 = k)), margVal n b a eta (x.1, (x.2 : ℕ)))
        = ∑ x ∈ (S.filter (fun x : Fin K × Fin t => x.1 = k)),
            margVal n b a eta (k, (x.2 : ℕ)) :=
          Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2])
      _ = ∑ j ∈ (S.filter (fun x : Fin K × Fin t => x.1 = k)).image (fun x : Fin K × Fin t => (x.2 : Fin t)),
            margVal n b a eta (k, (j : ℕ)) := by
          rw [Finset.sum_image (f := fun j : Fin t => margVal n b a eta (k, (j : ℕ))) hinj]
      _ ≤ ∑ i : Fin (q k), margVal n b a eta (k, (Fin.castLE hle i : ℕ)) :=
          prefix_dom (fun j : Fin t => margVal n b a eta (k, (j : ℕ))) hv _ (q k) hcardT hle
      _ = ∑ j ∈ Finset.range (q k), margVal n b a eta (k, j) := by
          simp only [Fin.val_castLE]
          exact Fin.sum_univ_eq_sum_range (fun j => margVal n b a eta (k, j)) (q k)
  calc ∑ x ∈ S, margVal n b a eta (x.1, (x.2 : ℕ))
      ≤ ∑ k, ∑ j ∈ Finset.range (q k), margVal n b a eta (k, j) := hSle
    _ = syncExpVal n b a eta u := hsync.symm
    _ ≤ (Finset.univ : Finset (Fin t → Fin K)).sup'
          ⟨fun _ => ⟨0, hK⟩, Finset.mem_univ _⟩ (syncExpVal n b a eta) :=
        Finset.le_sup' (f := syncExpVal n b a eta) (Finset.mem_univ u)

/-- Restricted synchronous benchmark equals the top-marginal sum. This combinatorial helper
does not by itself identify the full joint-action benchmark or a recursive greedy algorithm. -/
theorem proposition_A_4 (n : ℕ) {K : ℕ} (hK : 0 < K) (b a eta : Fin K → ℝ)
    (ha : ∀ k, 0 ≤ a k) (heta : ∀ k, 0 < eta k) (t : ℕ) :
    expBench n hK b a eta t = greedyVal n hK b a eta t :=
  le_antisymm (expBench_le_greedyVal n hK b a eta t)
    (greedyVal_le_expBench n hK b a eta t ha heta)

end AnvBandit
