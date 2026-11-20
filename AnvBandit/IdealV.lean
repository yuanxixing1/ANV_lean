import AnvBandit.HeadTail
import AnvBandit.PotentialFn

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Finset Filter

namespace AnvBandit
variable {n : ℕ}

/-! ## Step-level completion and delays -/

/-- Completion of the step-level ideal propagation started from `{i0}`. -/
def CompleteStep (R : ℕ → Fin n → Fin n) (i0 : Fin n) : Prop :=
  ∃ t, Inform R ({i0} : Finset (Fin n)) t = Finset.univ

lemma measurableSet_informStep (A S : Finset (Fin n)) (t : ℕ) :
    MeasurableSet {R : ℕ → Fin n → Fin n | Inform R A t = S} := by
  induction t generalizing S with
  | zero =>
    by_cases h : A = S
    · rw [show {R : ℕ → Fin n → Fin n | Inform R A 0 = S} = Set.univ from by
        ext R; simp [Inform_zero, h]]
      exact MeasurableSet.univ
    · rw [show {R : ℕ → Fin n → Fin n | Inform R A 0 = S} = ∅ from by
        ext R; simp [Inform_zero, h]]
      exact MeasurableSet.empty
  | succ t ih =>
    have hset : {R : ℕ → Fin n → Fin n | Inform R A (t + 1) = S} =
        ⋃ S' : Finset (Fin n), ({R | Inform R A t = S'} ∩ {R | infStep (R t) S' = S}) := by
      ext R; simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Inform_succ]
      constructor
      · intro h; exact ⟨Inform R A t, rfl, h⟩
      · rintro ⟨S', h1, h2⟩; rw [h1]; exact h2
    rw [hset]
    refine MeasurableSet.iUnion fun S' => (ih S').inter ?_
    have hpre : {R : ℕ → Fin n → Fin n | infStep (R t) S' = S} =
        (fun R => R t) ⁻¹'
          ((Finset.univ.filter (fun w : Fin n → Fin n => infStep w S' = S) : Set _)) := by
      ext R; simp [Finset.mem_filter]
    rw [hpre]
    exact (measurable_pi_apply t) (Finset.measurableSet _)

lemma measurableSet_inform_mem (A : Finset (Fin n)) (i : Fin n) (t : ℕ) :
    MeasurableSet {R : ℕ → Fin n → Fin n | i ∈ Inform R A t} := by
  rw [show {R : ℕ → Fin n → Fin n | i ∈ Inform R A t} =
      ⋃ S : {S : Finset (Fin n) // i ∈ S}, {R | Inform R A t = S.1} from by
    ext R; simp only [Set.mem_setOf_eq, Set.mem_iUnion, Subtype.exists, exists_prop]
    constructor
    · intro h; exact ⟨Inform R A t, h, rfl⟩
    · rintro ⟨S, hS, rfl⟩; exact hS]
  exact MeasurableSet.iUnion fun S => measurableSet_informStep A S.1 t

lemma stepMeasure_complete_compl_eq_zero (hn : 2 ≤ n) (C : ContactMatrix n) {i0 : Fin n}
    (R0 : ReachData C.P i0) :
    stepMeasure C {R : ℕ → Fin n → Fin n | ¬ CompleteStep R i0} = 0 := by
  have hd : 0 < n - 1 := by omega
  have hmeas : MeasurableSet {R : ℕ → Fin n → Fin n | ¬ CompleteStep R i0} := by
    rw [show {R : ℕ → Fin n → Fin n | ¬ CompleteStep R i0} =
        (⋃ t, {R | Inform R ({i0} : Finset (Fin n)) t = Finset.univ})ᶜ from by
      ext R; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists, CompleteStep]]
    exact (MeasurableSet.iUnion fun t => measurableSet_informStep _ _ t).compl
  rw [← unblock_measure hd C, Measure.map_apply (measurable_unblock hd) hmeas]
  rw [show unblock (n := n) hd ⁻¹' {R : ℕ → Fin n → Fin n | ¬ CompleteStep R i0}
      = {ω | ¬ Complete hd ω i0} from rfl]
  exact measure_Complete_compl_eq_zero hn C R0

lemma stepMeasure_completeStep_ae (hn : 2 ≤ n) (C : ContactMatrix n) {i0 : Fin n}
    (R0 : ReachData C.P i0) :
    ∀ᵐ R ∂(stepMeasure C), CompleteStep R i0 := by
  rw [ae_iff]
  exact stepMeasure_complete_compl_eq_zero hn C R0

/-- Step-level propagation delay, as an extended nonnegative real (`⊤` if never informed). -/
def sigmaAllE (R : ℕ → Fin n → Fin n) (A : Finset (Fin n)) (i : Fin n) : ℝ≥0∞ :=
  ⨅ t : ℕ, if i ∈ Inform R A t then (t : ℝ≥0∞) else ⊤

lemma measurable_sigmaAllE (A : Finset (Fin n)) (i : Fin n) :
    Measurable (fun R => sigmaAllE R A i) := by
  refine Measurable.iInf fun t => ?_
  exact Measurable.ite (measurableSet_inform_mem A i t) measurable_const measurable_const

/-- The informed-time as a natural number (`0` when never informed). -/
def sigmaAll (R : ℕ → Fin n → Fin n) (A : Finset (Fin n)) (i : Fin n) : ℕ :=
  sInf {t | i ∈ Inform R A t}

lemma sigmaAll_mem {R : ℕ → Fin n → Fin n} {A : Finset (Fin n)} {i : Fin n} (hA : i ∈ A) :
    sigmaAll R A i = 0 :=
  le_antisymm (Nat.sInf_le (show i ∈ Inform R A 0 by rw [Inform_zero]; exact hA)) (Nat.zero_le _)

lemma sigmaAllE_of_nonempty {R : ℕ → Fin n → Fin n} {A : Finset (Fin n)} {i : Fin n}
    (hS : ∃ t, i ∈ Inform R A t) :
    sigmaAllE R A i = (sigmaAll R A i : ℝ≥0∞) := by
  have hm : sigmaAll R A i ∈ {t | i ∈ Inform R A t} := Nat.sInf_mem hS
  refine le_antisymm ?_ ?_
  · calc sigmaAllE R A i
        ≤ (if i ∈ Inform R A (sigmaAll R A i) then ((sigmaAll R A i : ℕ) : ℝ≥0∞) else ⊤) :=
          iInf_le (fun t : ℕ => if i ∈ Inform R A t then (t : ℝ≥0∞) else ⊤) (sigmaAll R A i)
      _ = (sigmaAll R A i : ℝ≥0∞) := by rw [if_pos (show i ∈ Inform R A (sigmaAll R A i) from hm)]
  · refine le_iInf fun t => ?_
    by_cases ht : i ∈ Inform R A t
    · rw [if_pos ht]; exact_mod_cast Nat.sInf_le ht
    · rw [if_neg ht]; exact le_top

/-- Split an `iInf` over `ℕ` at its first term. -/
lemma iInf_nat_succ {α : Type*} [CompleteLattice α] (f : ℕ → α) :
    ⨅ t : ℕ, f t = f 0 ⊓ ⨅ t : ℕ, f (t + 1) := by
  refine le_antisymm (le_inf (iInf_le f 0) (le_iInf fun t => iInf_le f (t + 1))) ?_
  refine le_iInf fun t => ?_
  cases t with
  | zero => exact inf_le_left
  | succ t => exact inf_le_right.trans (iInf_le (fun t => f (t + 1)) t)

/-- `Inform` after one step is a single propagation step. -/
lemma Inform_one (R : ℕ → Fin n → Fin n) (A : Finset (Fin n)) :
    Inform R A 1 = infStep (R 0) A := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, Inform_succ, Inform_zero]

lemma Nat.sInf_succ_shift {P Q : ℕ → Prop} (h : ∀ t, P (t + 1) ↔ Q t) (h0 : ¬ P 0)
    (hne : ∃ t, P t) : sInf {t | P t} = 1 + sInf {t | Q t} := by
  obtain ⟨t1, ht1⟩ := hne
  have ht10 : t1 ≠ 0 := fun hh => h0 (hh ▸ ht1)
  have hQ : ∃ t, Q t := ⟨t1 - 1, by
    rw [← h]; rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero ht10)]⟩
  have hmQ : Q (sInf {t | Q t}) := Nat.sInf_mem hQ
  have hpne : ({t | P t}).Nonempty := ⟨sInf {t | Q t} + 1, (h _).mpr hmQ⟩
  refine le_antisymm ?_ ?_
  · refine Nat.sInf_le (show P (1 + sInf {t | Q t}) from ?_)
    rw [Nat.add_comm]; exact (h _).mpr hmQ
  · have hsp := Nat.sInf_mem hpne
    have ht0 : sInf {t | P t} ≠ 0 := fun hh => h0 (hh ▸ hsp)
    have hq : Q (sInf {t | P t} - 1) := by
      rw [← h]; rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero ht0)]
    have hle := Nat.add_le_add_right (Nat.sInf_le hq) 1
    rw [Nat.sub_add_cancel (show 1 ≤ sInf {t | P t} from Nat.pos_of_ne_zero ht0)] at hle
    calc 1 + sInf {t | Q t} = sInf {t | Q t} + 1 := Nat.add_comm _ _
      _ ≤ sInf {t | P t} := hle

lemma sigmaAll_stepE {R : ℕ → Fin n → Fin n} {A : Finset (Fin n)} {i : Fin n} (hi : i ∉ A) :
    sigmaAllE R A i = 1 + sigmaAllE (fun t => R (t + 1)) (infStep (R 0) A) i := by
  have hstep : ∀ t, (i ∈ Inform R A (t + 1)) ↔
      (i ∈ Inform (fun s => R (s + 1)) (infStep (R 0) A) t) := by
    intro t
    rw [show t + 1 = 1 + t from Nat.add_comm t 1, Inform_shift R A 1 t, Inform_one R A,
      show (fun s => R (1 + s)) = (fun s => R (s + 1)) from
        funext (fun s => by rw [Nat.add_comm])]
  have hf : ∀ t, (if i ∈ Inform R A (t + 1) then ((t + 1 : ℕ) : ℝ≥0∞) else ⊤)
      = (if i ∈ Inform (fun s => R (s + 1)) (infStep (R 0) A) t then (t : ℝ≥0∞) else ⊤) + 1 := by
    intro t
    rw [if_congr (hstep t) rfl rfl]
    by_cases h : i ∈ Inform (fun s => R (s + 1)) (infStep (R 0) A) t
    · rw [if_pos h, if_pos h]; simp only [Nat.cast_add, Nat.cast_one]
    · rw [if_neg h, if_neg h]; simp
  unfold sigmaAllE
  rw [iInf_nat_succ]
  have hf0 : (if i ∈ Inform R A 0 then ((0 : ℕ) : ℝ≥0∞) else ⊤) = ⊤ := by
    rw [if_neg (show i ∉ Inform R A 0 by rw [Inform_zero]; exact hi)]
  rw [hf0, top_inf_eq]
  rw [show (⨅ t : ℕ, (if i ∈ Inform R A (t + 1) then ((t + 1 : ℕ) : ℝ≥0∞) else ⊤))
      = ⨅ t : ℕ, ((if i ∈ Inform (fun s => R (s + 1)) (infStep (R 0) A) t
          then (t : ℝ≥0∞) else ⊤) + 1) from iInf_congr hf]
  rw [← ENNReal.iInf_add (f := fun t : ℕ =>
      if i ∈ Inform (fun s => R (s + 1)) (infStep (R 0) A) t then (t : ℝ≥0∞) else ⊤) (a := 1)]
  exact add_comm _ _

/-! ## The propagation potential `V(A)` and its one-step recursion (C.7) -/

/-- **(C.7)-layer potential.** `V(A) = ∑_i ∫ σ^A_i`, the summed expected propagation delay
from the informed set `A`, as an extended nonnegative real. -/
noncomputable def VpotE (C : ContactMatrix n) (A : Finset (Fin n)) : ℝ≥0∞ :=
  ∑ i : Fin n, ∫⁻ R, sigmaAllE R A i ∂(stepMeasure C)

lemma sigmaAllE_mem' {R : ℕ → Fin n → Fin n} {A : Finset (Fin n)} {i : Fin n} (hA : i ∈ A) :
    sigmaAllE R A i = 0 := by
  rw [sigmaAllE_of_nonempty (R := R) (A := A) (i := i)
    ⟨0, by rw [Inform_zero]; exact hA⟩, sigmaAll_mem hA]
  simp

lemma measurable_headTail : Measurable (fun R : ℕ → Fin n → Fin n => (R 0, fun t => R (t + 1))) :=
  Measurable.prodMk (measurable_pi_apply 0)
    (measurable_pi_iff.mpr (fun t => measurable_pi_apply (t + 1)))

lemma measurable_sigmaAllE_shift (A : Finset (Fin n)) (i : Fin n) :
    Measurable (fun R : ℕ → Fin n → Fin n =>
      sigmaAllE (fun t => R (t + 1)) (infStep (R 0) A) i) := by
  have hsh : Measurable (fun R : ℕ → Fin n → Fin n => fun t => R (t + 1)) :=
    measurable_pi_iff.mpr (fun t => measurable_pi_apply (t + 1))
  have hcongr : (fun R : ℕ → Fin n → Fin n =>
        ∑ B ∈ (Finset.univ : Finset (Fin n → Fin n)).image (fun w => infStep w A),
          (if infStep (R 0) A = B then sigmaAllE (fun t => R (t + 1)) B i else 0))
      = fun R => sigmaAllE (fun t => R (t + 1)) (infStep (R 0) A) i := by
    funext R
    exact (Finset.sum_eq_single
      (a := infStep (R 0) A)
      (f := fun B => if infStep (R 0) A = B then sigmaAllE (fun t => R (t + 1)) B i else 0)
      (fun B _ hB => by rw [if_neg (fun h => hB h.symm)])
      (fun h => absurd (Finset.mem_image.mpr ⟨R 0, Finset.mem_univ _, rfl⟩) h)).trans
        (by simp)
  rw [← hcongr]
  refine Finset.measurable_sum _ (fun B _ => ?_)
  refine Measurable.ite ?_ ((measurable_sigmaAllE B i).comp hsh) measurable_const
  rw [show {R : ℕ → Fin n → Fin n | infStep (R 0) A = B}
      = (fun R => R 0) ⁻¹'
        ((Finset.univ.filter (fun w : Fin n → Fin n => infStep w A = B) : Set _)) from by
    ext R; simp [Finset.mem_filter]]
  exact (measurable_pi_apply 0) (Finset.measurableSet _)

lemma measurable_sigmaAllE_joint (A : Finset (Fin n)) (i : Fin n) :
    Measurable (fun z : (Fin n → Fin n) × (ℕ → Fin n → Fin n) =>
      sigmaAllE z.2 (infStep z.1 A) i) := by
  have hcongr : (fun z : (Fin n → Fin n) × (ℕ → Fin n → Fin n) =>
        ∑ B ∈ (Finset.univ : Finset (Fin n → Fin n)).image (fun w => infStep w A),
          (if infStep z.1 A = B then sigmaAllE z.2 B i else 0))
      = fun z => sigmaAllE z.2 (infStep z.1 A) i := by
    funext z
    exact (Finset.sum_eq_single
      (a := infStep z.1 A)
      (f := fun B => if infStep z.1 A = B then sigmaAllE z.2 B i else 0)
      (fun B _ hB => by rw [if_neg (fun h => hB h.symm)])
      (fun h => absurd (Finset.mem_image.mpr ⟨z.1, Finset.mem_univ _, rfl⟩) h)).trans
        (by simp)
  rw [← hcongr]
  refine Finset.measurable_sum _ (fun B _ => ?_)
  refine Measurable.ite ?_ ((measurable_sigmaAllE B i).comp measurable_snd) measurable_const
  rw [show {z : (Fin n → Fin n) × (ℕ → Fin n → Fin n) | infStep z.1 A = B}
      = (fun z => z.1) ⁻¹'
        ((Finset.univ.filter (fun w : Fin n → Fin n => infStep w A = B) : Set _)) from by
    ext z; simp [Finset.mem_filter]]
  exact measurable_fst (Finset.measurableSet _)

/-- **Equation (C.7).** The one-step recursion `V(A) = |V \ A| + E_J V(T(A, J))`, with
`T(A, J) = infStep J A` and `J` a fresh contact. -/
theorem VpotE_recursion (C : ContactMatrix n) {A : Finset (Fin n)} :
    VpotE C A = ((Finset.univ \ A).card : ℝ≥0∞) + ∫⁻ J, VpotE C (infStep J A) ∂(stepDist C) := by
  have hterm : ∀ i : Fin n, ∫⁻ R, sigmaAllE R A i ∂(stepMeasure C)
      = (if i ∈ A then (0 : ℝ≥0∞) else 1)
        + ∫⁻ R, sigmaAllE (fun t => R (t + 1)) (infStep (R 0) A) i ∂(stepMeasure C) := by
    intro i
    by_cases hi : i ∈ A
    · rw [if_pos hi]
      have hz : (fun R : ℕ → Fin n → Fin n => sigmaAllE R A i) = fun _ => 0 :=
        funext fun R => sigmaAllE_mem' hi
      have hz2 : (fun R : ℕ → Fin n → Fin n =>
          sigmaAllE (fun t => R (t + 1)) (infStep (R 0) A) i) = fun _ => 0 :=
        funext fun R => sigmaAllE_mem' (subset_infStep (R 0) A hi)
      rw [hz, hz2]; simp
    · rw [if_neg hi]
      simp_rw [sigmaAll_stepE hi]
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
  have hcard : (∑ i : Fin n, (if i ∈ A then (0 : ℝ≥0∞) else 1))
      = ((Finset.univ \ A).card : ℝ≥0∞) := by
    rw [show (∑ i : Fin n, (if i ∈ A then (0 : ℝ≥0∞) else 1))
        = ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => i ∉ A), (1 : ℝ≥0∞) from by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases h : i ∈ A <;> simp [h]]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one,
      show (Finset.univ : Finset (Fin n)).filter (fun i => i ∉ A) = Finset.univ \ A from by
        ext i; simp [Finset.mem_sdiff]]
  have hdouble : (∑ i : Fin n, ∫⁻ R,
        sigmaAllE (fun t => R (t + 1)) (infStep (R 0) A) i ∂(stepMeasure C))
      = ∫⁻ J, VpotE C (infStep J A) ∂(stepDist C) := by
    rw [← lintegral_finsetSum _ (fun i _ => measurable_sigmaAllE_shift A i)]
    have hG : Measurable (fun z : (Fin n → Fin n) × (ℕ → Fin n → Fin n) =>
        ∑ i : Fin n, sigmaAllE z.2 (infStep z.1 A) i) :=
      Finset.measurable_sum _ (fun i _ => measurable_sigmaAllE_joint A i)
    have hfun : (fun R : ℕ → Fin n → Fin n =>
          ∑ i : Fin n, sigmaAllE (fun t => R (t + 1)) (infStep (R 0) A) i)
        = fun R => (fun z : (Fin n → Fin n) × (ℕ → Fin n → Fin n) =>
            ∑ i : Fin n, sigmaAllE z.2 (infStep z.1 A) i) (R 0, fun t => R (t + 1)) := rfl
    rw [hfun, ← lintegral_map (f := fun z : (Fin n → Fin n) × (ℕ → Fin n → Fin n) =>
          ∑ i : Fin n, sigmaAllE z.2 (infStep z.1 A) i)
        (g := fun R : ℕ → Fin n → Fin n => (R 0, fun t => R (t + 1))) hG measurable_headTail,
      stepMeasure_headTail,
      lintegral_prod (f := fun z : (Fin n → Fin n) × (ℕ → Fin n → Fin n) =>
          ∑ i : Fin n, sigmaAllE z.2 (infStep z.1 A) i) hG.aemeasurable]
    refine lintegral_congr fun a => ?_
    rw [show (∫⁻ s, ∑ i : Fin n, sigmaAllE s (infStep a A) i ∂(stepMeasure C))
        = ∑ i : Fin n, ∫⁻ s, sigmaAllE s (infStep a A) i ∂(stepMeasure C) from
      lintegral_finsetSum _ (fun i _ => measurable_sigmaAllE (infStep a A) i)]
    rfl
  calc VpotE C A
      = ∑ i : Fin n, ∫⁻ R, sigmaAllE R A i ∂(stepMeasure C) := rfl
    _ = ∑ i : Fin n, ((if i ∈ A then (0 : ℝ≥0∞) else 1)
          + ∫⁻ R, sigmaAllE (fun t => R (t + 1)) (infStep (R 0) A) i ∂(stepMeasure C)) :=
        Finset.sum_congr rfl (fun i _ => hterm i)
    _ = (∑ i : Fin n, (if i ∈ A then (0 : ℝ≥0∞) else 1))
          + ∑ i : Fin n, ∫⁻ R, sigmaAllE (fun t => R (t + 1)) (infStep (R 0) A) i ∂(stepMeasure C) :=
        Finset.sum_add_distrib
    _ = ((Finset.univ \ A).card : ℝ≥0∞) + ∫⁻ J, VpotE C (infStep J A) ∂(stepDist C) := by
        rw [hcard, hdouble]

end AnvBandit
