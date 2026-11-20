import AnvBandit.Moments

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# The propagation potential `V(A)` (Appendix C.2, equations (C.6)-(C.7))

The potential-function proof of Lemma C.3 rests on two structural facts about the ideal
propagation started from an informed set `A ∋ i⋆`:

* **(C.6)** `|V \ A| ≤ V(A) ≤ M_1`, with `V({i⋆}) = M_1` and `V(V) = 0`, and `V` antitone;
* **(C.7)** the one-step recursion `V(A) = |V \ A| + E_J V(T(A, J))`.

Here `T(A, J) = infStep J A` and the expectation is over a fresh contact `J`.  This file builds the
potential as the integral of the summed propagation delays, `V(A) = ∑_i E_A σ^A_i` (`Vpot`), proves
the *almost-sure completion* of the ideal propagation, and then establishes (C.6).
-/

noncomputable section
open scoped BigOperators ENNReal
open Finset MeasureTheory Filter

namespace AnvBandit

variable {n : ℕ}

/-! ## 1. Almost-sure completion of the ideal propagation -/

/-- Completion event of the ideal propagation started from `{i0}`. -/
def Complete {n : ℕ} (hd : 0 < n - 1) (ω : ℕ → Fin (n - 1) → Fin n → Fin n) (i0 : Fin n) : Prop :=
  ∃ t, Inform (unblock hd ω) ({i0} : Finset (Fin n)) t = Finset.univ

lemma measurableSet_Complete {n : ℕ} (hd : 0 < n - 1) (i0 : Fin n) :
    MeasurableSet {ω : ℕ → Fin (n - 1) → Fin n → Fin n | Complete hd ω i0} := by
  have h : {ω : ℕ → Fin (n - 1) → Fin n → Fin n | Complete hd ω i0} =
      ⋃ t, {ω | Inform (unblock hd ω) ({i0} : Finset (Fin n)) t = Finset.univ} := by
    ext ω; simp only [Complete, Set.mem_setOf_eq, Set.mem_iUnion]
  rw [h]
  exact MeasurableSet.iUnion fun t => measurable_inform_eq hd {i0} _ t

/-- The completion time vanishes on the non-completion event. -/
lemma tau_eq_zero_of_not_complete {hd : 0 < n - 1} {ω} {i0 : Fin n}
    (hC : ¬ Complete hd ω i0) : tau hd ω i0 = 0 := by
  unfold tau
  rw [show {t | Inform (unblock hd ω) ({i0} : Finset (Fin n)) t = Finset.univ} = ∅ from by
    ext t; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun h => hC ⟨t, h⟩]
  exact Nat.sInf_empty

/-- **Almost-sure completion**, null-complement form. -/
theorem measure_Complete_compl_eq_zero {n : ℕ} (hn : 2 ≤ n) (C : ContactMatrix n) {i0 : Fin n}
    (R : ReachData C.P i0) :
    procMeasure C (n - 1)
      {ω : ℕ → Fin (n - 1) → Fin n → Fin n | ¬ Complete (by omega : 0 < n - 1) ω i0} = 0 := by
  have hd : 0 < n - 1 := by omega
  have hb : ∀ m, procMeasure C (n - 1)
      {ω : ℕ → Fin (n - 1) → Fin n → Fin n | ¬ Complete hd ω i0}
      ≤ ENNReal.ofReal ((1 - epsP C) ^ m) := by
    intro m
    refine (measure_mono ?_).trans (measure_complete_gt_le (C := C) (i0 := i0) R m)
    intro ω hω
    simp only [Set.mem_setOf_eq, Complete, not_exists] at hω ⊢
    intro hcomp
    exact hω (m * (n - 1)) (by rw [Inform_unblock hd ω {i0} m]; exact hcomp)
  have htend : Tendsto (fun m : ℕ => ENNReal.ofReal ((1 - epsP C) ^ m)) atTop (nhds 0) := by
    have hbase : Tendsto (fun m : ℕ => (1 - epsP C) ^ m) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by have := epsP_le_one C i0; linarith)
        (by have := epsP_pos C; linarith)
    have hcont := ENNReal.continuous_ofReal.tendsto 0
    rw [ENNReal.ofReal_zero] at hcont
    exact hcont.comp hbase
  exact le_antisymm (ge_of_tendsto' htend hb) bot_le

/-- **Almost-sure completion**, measure-one form. -/
theorem measure_Complete_eq_one {n : ℕ} (hn : 2 ≤ n) (C : ContactMatrix n) {i0 : Fin n}
    (R : ReachData C.P i0) :
    procMeasure C (n - 1)
      {ω : ℕ → Fin (n - 1) → Fin n → Fin n | Complete (by omega : 0 < n - 1) ω i0} = 1 := by
  have hd : 0 < n - 1 := by omega
  have hm : (procMeasure C (n - 1)) ({ω | Complete hd ω i0} : Set _)ᶜ = 0 :=
    measure_Complete_compl_eq_zero hn C R
  rw [← compl_compl ({ω | Complete hd ω i0} : Set _),
    measure_compl (measurableSet_Complete hd i0).compl (measure_ne_top _ _), measure_univ, hm,
    tsub_zero]

/-! ## 2. The propagation delay and its properties -/

/-- Propagation delay of node `i` from the informed set `A`. -/
def sigmaFrom {n : ℕ} (hd : 0 < n - 1) (ω : ℕ → Fin (n - 1) → Fin n → Fin n)
    (A : Finset (Fin n)) (i : Fin n) : ℕ :=
  sInf {t | i ∈ Inform (unblock hd ω) A t}

lemma sigmaFrom_eq_sigmaStep {hd : 0 < n - 1} (ω) (i0 i : Fin n) :
    sigmaFrom hd ω {i0} i = sigmaStep (unblock hd ω) i0 i := rfl

/-- `σ^A_i = 0` when `i ∈ A`. -/
lemma sigmaFrom_mem {hd : 0 < n - 1} (ω) {A : Finset (Fin n)} {i : Fin n} (hA : i ∈ A) :
    sigmaFrom hd ω A i = 0 :=
  le_antisymm (Nat.sInf_le (by
    show i ∈ Inform (unblock hd ω) A 0
    rw [Inform_zero]; exact hA)) (Nat.zero_le _)

/-- Unfolding of `tau` into its defining `sInf` (definitional equality). -/
lemma tau_def_eq {hd : 0 < n - 1} (ω) (i0 : Fin n) :
    tau hd ω i0
      = sInf {t | Inform (unblock hd ω) ({i0} : Finset (Fin n)) t = Finset.univ} := rfl

/-- On the completion event, `τ` is attained (`sInf` form). -/
lemma Inform_Sinf_tau_eq_univ {hd : 0 < n - 1} {ω} {i0 : Fin n} (hC : Complete hd ω i0) :
    Inform (unblock hd ω) ({i0} : Finset (Fin n))
      (sInf {t | Inform (unblock hd ω) ({i0} : Finset (Fin n)) t = Finset.univ}) = Finset.univ :=
  Nat.sInf_mem hC

/-- On the completion event, `τ` is attained. -/
lemma Inform_tau_eq_univ {hd : 0 < n - 1} {ω} {i0 : Fin n} (hC : Complete hd ω i0) :
    Inform (unblock hd ω) ({i0} : Finset (Fin n)) (tau hd ω i0) = Finset.univ :=
  Inform_Sinf_tau_eq_univ hC

lemma sigmaStep_le_tau {hd : 0 < n - 1} {ω} {i0 i : Fin n} (hC : Complete hd ω i0) :
    sigmaStep (unblock hd ω) i0 i ≤ tau hd ω i0 := by
  unfold sigmaStep
  refine Nat.sInf_le ?_
  show i ∈ Inform (unblock hd ω) ({i0} : Finset (Fin n)) (tau hd ω i0)
  rw [Inform_tau_eq_univ hC]; exact Finset.mem_univ i

/-- **Capped monotonicity of the delay in the source set.** For `A ∋ i⋆` and `A ⊆ B`,
`min(σ^B_i, τ) ≤ min(σ^A_i, τ)` *everywhere*. -/
lemma min_sigmaFrom_anti {hd : 0 < n - 1} (ω) {A B : Finset (Fin n)} {i0 : Fin n}
    (hA : i0 ∈ A) (hAB : A ⊆ B) (i : Fin n) :
    min (sigmaFrom hd ω B i) (tau hd ω i0) ≤ min (sigmaFrom hd ω A i) (tau hd ω i0) := by
  rcases Set.eq_empty_or_nonempty {t | i ∈ Inform (unblock hd ω) A t} with h | h
  · have hnc : ¬ Complete hd ω i0 := by
      rintro ⟨t, ht⟩
      have hmem : i ∈ Inform (unblock hd ω) A t :=
        Inform_mono (unblock hd ω) (Finset.singleton_subset_iff.mpr hA) t
          (by rw [ht]; exact Finset.mem_univ i)
      have : t ∈ {t | i ∈ Inform (unblock hd ω) A t} := hmem
      rw [h] at this
      exact this
    rw [show sigmaFrom hd ω A i = 0 from by rw [sigmaFrom, h, Nat.sInf_empty],
      tau_eq_zero_of_not_complete hnc, min_eq_right (Nat.zero_le _), min_eq_right (Nat.zero_le _)]
  · have hmem := Nat.sInf_mem h
    exact min_le_min (Nat.sInf_le (Inform_mono (unblock hd ω) hAB _ hmem)) le_rfl

/-- On the completion event, `σ^A_i ≤ σ^{{i⋆}}_i` for `A ∋ i⋆`. -/
lemma sigmaFrom_le_sigmaStep {hd : 0 < n - 1} {ω} {A : Finset (Fin n)} {i0 i : Fin n}
    (hA : i0 ∈ A) (hC : Complete hd ω i0) :
    sigmaFrom hd ω A i ≤ sigmaStep (unblock hd ω) i0 i := by
  unfold sigmaFrom sigmaStep
  have hne : ({t | i ∈ Inform (unblock hd ω) ({i0} : Finset (Fin n)) t} : Set ℕ).Nonempty :=
    ⟨tau hd ω i0, by
      show i ∈ Inform (unblock hd ω) ({i0} : Finset (Fin n)) (tau hd ω i0)
      rw [Inform_tau_eq_univ hC]; exact Finset.mem_univ i⟩
  exact Nat.sInf_le (Inform_mono (unblock hd ω) (Finset.singleton_subset_iff.mpr hA) _
    (Nat.sInf_mem hne))

/-- On the completion event, `σ^A_i ≤ τ` for `A ∋ i0`. -/
lemma sigmaFrom_le_tau {hd : 0 < n - 1} {ω} {A : Finset (Fin n)} {i0 i : Fin n}
    (hA : i0 ∈ A) (hC : Complete hd ω i0) : sigmaFrom hd ω A i ≤ tau hd ω i0 := by
  unfold sigmaFrom
  refine Nat.sInf_le ?_
  show i ∈ Inform (unblock hd ω) A (tau hd ω i0)
  rw [show Inform (unblock hd ω) A (tau hd ω i0) = Finset.univ from ?_]
  exact Finset.mem_univ i
  have h := Inform_mono (unblock hd ω) (Finset.singleton_subset_iff.mpr hA) (tau hd ω i0)
  rw [Inform_tau_eq_univ hC] at h
  exact Finset.Subset.antisymm (Finset.subset_univ _) h

/-- **Capped upper comparison with the single-source delay.** For `A ∋ i⋆`,
`min(σ^A_i, τ) ≤ min(σ^{{i⋆}}_i, τ)` everywhere. -/
lemma min_sigmaFrom_le_min_sigmaStep {hd : 0 < n - 1} (ω) {A : Finset (Fin n)} {i0 i : Fin n}
    (hA : i0 ∈ A) :
    min (sigmaFrom hd ω A i) (tau hd ω i0)
      ≤ min (sigmaStep (unblock hd ω) i0 i) (tau hd ω i0) := by
  by_cases hC : Complete hd ω i0
  · have h1 : sigmaFrom hd ω A i ≤ sigmaStep (unblock hd ω) i0 i := sigmaFrom_le_sigmaStep hA hC
    have h2 : sigmaStep (unblock hd ω) i0 i ≤ tau hd ω i0 := sigmaStep_le_tau hC
    rw [min_eq_left h2]
    exact le_trans (min_le_left _ _) h1
  · rw [tau_eq_zero_of_not_complete hC,
      min_eq_right (Nat.zero_le _), min_eq_right (Nat.zero_le _)]

/-- On the completion event, a node outside `A ∋ i⋆` is informed later than step `0`. -/
lemma one_le_sigmaFrom {hd : 0 < n - 1} {ω} {A : Finset (Fin n)} {i0 i : Fin n}
    (hA : i0 ∈ A) (hC : Complete hd ω i0) (hi : i ∉ A) : 1 ≤ sigmaFrom hd ω A i := by
  have hmemAll : Inform (unblock hd ω) A (tau hd ω i0) = Finset.univ := by
    have h := Inform_mono (unblock hd ω) (Finset.singleton_subset_iff.mpr hA) (tau hd ω i0)
    rw [Inform_tau_eq_univ hC] at h
    exact Finset.Subset.antisymm (Finset.subset_univ _) h
  have hne : ({t | i ∈ Inform (unblock hd ω) A t} : Set ℕ).Nonempty :=
    ⟨tau hd ω i0, by
      show i ∈ Inform (unblock hd ω) A (tau hd ω i0)
      rw [hmemAll]; exact Finset.mem_univ i⟩
  have h0 : (0 : ℕ) ∉ {t | i ∈ Inform (unblock hd ω) A t} := by
    simp only [Set.mem_setOf_eq, Inform_zero]; exact hi
  unfold sigmaFrom
  have hne0 : sInf {t | i ∈ Inform (unblock hd ω) A t} ≠ 0 := by
    intro h0eq
    have hmemS := Nat.sInf_mem hne
    rw [h0eq] at hmemS
    exact h0 hmemS
  omega

/-! ## 3. The potential `V(A)` and (C.6) -/

/-- **(C.6)** The propagation potential `V(A) = ∑_i E_A σ^A_i`, capped by the completion time so
the quantity is well-defined for every finite node set. -/
noncomputable def Vpot {n : ℕ} (hd : 0 < n - 1) (C : ContactMatrix n) (i0 : Fin n)
    (A : Finset (Fin n)) : ℝ :=
  ∑ i : Fin n,
    (∫⁻ ω, ENNReal.ofReal ((min (sigmaFrom hd ω A i) (tau hd ω i0) : ℕ) : ℝ)
      ∂procMeasure C (n - 1)).toReal

lemma lintegral_tauR_ne_top {n : ℕ} (hn : 2 ≤ n) (C : ContactMatrix n) {i0 : Fin n}
    (R : ReachData C.P i0) :
    ∫⁻ ω, ENNReal.ofReal ((tau (by omega : 0 < n - 1) ω i0 : ℕ) : ℝ) ∂procMeasure C (n - 1)
      ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (by have h := integral_rpow_tau_le hn C R (β := 1) le_rfl; simpa using h)

variable {hd : 0 < n - 1}

lemma lintegral_min_ne_top (hn : 2 ≤ n) (C : ContactMatrix n) {i0 : Fin n}
    (R : ReachData C.P i0) (A : Finset (Fin n)) (i : Fin n) :
    ∫⁻ ω, ENNReal.ofReal ((min (sigmaFrom hd ω A i) (tau hd ω i0) : ℕ) : ℝ)
      ∂procMeasure C (n - 1) ≠ ⊤ :=
  ne_top_of_le_ne_top (lintegral_tauR_ne_top hn C R)
    (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (by exact_mod_cast min_le_right _ _))

lemma lintegral_sigmaR_ne_top (hn : 2 ≤ n) (C : ContactMatrix n) {i0 : Fin n}
    (R : ReachData C.P i0) (i : Fin n) :
    ∫⁻ ω, ENNReal.ofReal (sigmaR hd ω i0 i) ∂procMeasure C (n - 1) ≠ ⊤ :=
  ne_top_of_le_ne_top (lintegral_tauR_ne_top hn C R)
    (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (by
      simp only [sigmaR, sigma]; exact_mod_cast min_le_right _ _))

/-- **(C.6), anchor.** `V({i⋆}) = M_1`. -/
theorem Vpot_singleton (C : ContactMatrix n) (i0 : Fin n) :
    Vpot hd C i0 {i0} = M1 hd C i0 := by
  unfold Vpot M1 sigmaR sigma
  refine Finset.sum_congr rfl fun i _ => ?_
  have hfun : (fun ω => ENNReal.ofReal ((min (sigmaFrom hd ω {i0} i) (tau hd ω i0) : ℕ) : ℝ))
      = fun ω => ENNReal.ofReal ((min (sigmaStep (unblock hd ω) i0 i) (tau hd ω i0) : ℕ) : ℝ) := by
    funext ω; simp only [sigmaFrom, sigmaStep]
  rw [hfun]

/-- **(C.6), empty.** `V(V) = 0`. -/
theorem Vpot_univ (C : ContactMatrix n) (i0 : Fin n) :
    Vpot hd C i0 Finset.univ = 0 := by
  unfold Vpot
  refine Finset.sum_eq_zero fun i _ => ?_
  have hz : ∀ ω, min (sigmaFrom hd ω Finset.univ i) (tau hd ω i0) = 0 := by
    intro ω
    rw [sigmaFrom_mem ω (Finset.mem_univ i)]; exact min_eq_left (Nat.zero_le _)
  have hzero : (fun ω => ENNReal.ofReal
      ((min (sigmaFrom hd ω Finset.univ i) (tau hd ω i0) : ℕ) : ℝ)) = fun _ => (0:ℝ≥0∞) := by
    funext ω; rw [hz ω]; simp
  rw [hzero, lintegral_zero, ENNReal.toReal_zero]

/-- **(C.6), upper bound.** `V(A) ≤ M_1` for `A ∋ i⋆`. -/
theorem Vpot_le_M1 (hn : 2 ≤ n) (C : ContactMatrix n) {i0 : Fin n}
    (R : ReachData C.P i0) {A : Finset (Fin n)} (hA : i0 ∈ A) :
    Vpot hd C i0 A ≤ M1 hd C i0 := by
  unfold Vpot M1
  refine Finset.sum_le_sum fun i _ => ENNReal.toReal_mono (lintegral_sigmaR_ne_top (hd := hd) hn C R i) ?_
  refine lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_
  simp only [sigmaR, sigma]
  exact_mod_cast min_sigmaFrom_le_min_sigmaStep ω hA

/-- **(C.6), antitone.** `A ⊆ B → V(B) ≤ V(A)` for `A ∋ i⋆`. -/
theorem Vpot_anti (hn : 2 ≤ n) (C : ContactMatrix n) {i0 : Fin n}
    (R : ReachData C.P i0) {A B : Finset (Fin n)} (hA : i0 ∈ A) (hAB : A ⊆ B) :
    Vpot hd C i0 B ≤ Vpot hd C i0 A := by
  unfold Vpot
  refine Finset.sum_le_sum fun i _ => ENNReal.toReal_mono (lintegral_min_ne_top (hd := hd) hn C R A i) ?_
  exact lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (by exact_mod_cast min_sigmaFrom_anti ω hA hAB i)

/-- **(C.6), lower bound.** `|V \ A| ≤ V(A)` for `A ∋ i⋆`. -/
theorem card_sdiff_le_Vpot (hn : 2 ≤ n) (C : ContactMatrix n) {i0 : Fin n}
    (R : ReachData C.P i0) {A : Finset (Fin n)} (hA : i0 ∈ A) :
    ((Finset.univ \ A).card : ℝ) ≤ Vpot (n := n) hd C i0 A := by
  have hfin := lintegral_tauR_ne_top hn C R
  have hmeasC := measurableSet_Complete hd i0
  have hterm : ∀ i ∈ (Finset.univ \ A),
      (1:ℝ) ≤ (∫⁻ ω, ENNReal.ofReal
        ((min (sigmaFrom hd ω A i) (tau hd ω i0) : ℕ) : ℝ) ∂procMeasure C (n - 1)).toReal := by
    intro i hi
    have hiA : i ∉ A := (Finset.mem_sdiff.mp hi).2
    have hpt : Set.indicator {ω | Complete hd ω i0} (fun _ : _ => (1 : ℝ≥0∞))
        ≤ fun ω => ENNReal.ofReal ((min (sigmaFrom hd ω A i) (tau hd ω i0) : ℕ) : ℝ) := by
      intro ω
      by_cases hω : Complete hd ω i0
      · rw [Set.indicator_of_mem (show ω ∈ {ω | Complete hd ω i0} from hω)]
        change (1:ℝ≥0∞) ≤ ENNReal.ofReal ((min (sigmaFrom hd ω A i) (tau hd ω i0) : ℕ) : ℝ)
        have h1 := one_le_sigmaFrom hA hω hiA
        have h2 : sigmaFrom hd ω A i ≤ tau hd ω i0 := sigmaFrom_le_tau hA hω
        have hmin : min (sigmaFrom hd ω A i) (tau hd ω i0) = sigmaFrom hd ω A i := min_eq_left h2
        rw [hmin, ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (by exact_mod_cast h1)
      · rw [Set.indicator_of_notMem (show ω ∉ {ω | Complete hd ω i0} from hω)]; exact bot_le
    have hInt : (1 : ℝ≥0∞) ≤ ∫⁻ ω, ENNReal.ofReal
        ((min (sigmaFrom hd ω A i) (tau hd ω i0) : ℕ) : ℝ) ∂procMeasure C (n - 1) := by
      have hmono := lintegral_mono (μ := procMeasure C (n - 1)) hpt
      have hcomp : (∫⁻ a, {ω | Complete hd ω i0}.indicator (fun _ => (1:ℝ≥0∞)) a
          ∂procMeasure C (n - 1)) = 1 := by
        change (∫⁻ a, {ω | Complete hd ω i0}.indicator
          (1 : (ℕ → Fin (n - 1) → Fin n → Fin n) → ℝ≥0∞) a
          ∂procMeasure C (n - 1)) = 1
        rw [lintegral_indicator_one hmeasC, measure_Complete_eq_one hn C R]
      rw [hcomp] at hmono
      simpa using hmono
    have hf := lintegral_min_ne_top (hd := hd) hn C R A i
    calc (1:ℝ) = (1:ℝ≥0∞).toReal := by simp
      _ ≤ _ := ENNReal.toReal_mono hf hInt
  rw [show ((Finset.univ \ A).card : ℝ) = ∑ _i ∈ (Finset.univ \ A), (1:ℝ) from by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
    (fun i _ _ => ENNReal.toReal_nonneg)

end AnvBandit
