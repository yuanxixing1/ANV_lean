import AnvBandit.PotentialBridge

/-! Exact remaining waiting times for the original ideal contact process. -/
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Finset Filter
namespace AnvBandit
variable {n : ℕ}

lemma measurable_inform_function {α : Type*} [MeasurableSpace α]
    (f : Finset (Fin n) → α) (A : Finset (Fin n)) (j : ℕ) :
    Measurable (fun R : ℕ → Fin n → Fin n => f (Inform R A j)) := by
  letI : MeasurableSpace (Finset (Fin n)) := ⊤
  have hm : Measurable (fun R : ℕ → Fin n → Fin n => Inform R A j) :=
    measurable_to_countable' fun S => measurableSet_informStep A S j
  exact (measurable_of_countable f).comp hm

lemma lintegral_step_headTail (C : ContactMatrix n)
    (f : (Fin n → Fin n) → (ℕ → Fin n → Fin n) → ℝ≥0∞)
    (hf : ∀ J, Measurable (f J)) :
    (∫⁻ R, f (R 0) (fun t => R (t+1)) ∂stepMeasure C) =
      ∫⁻ J, ∫⁻ R, f J R ∂stepMeasure C ∂stepDist C := by
  have hm : Measurable (fun z : (Fin n → Fin n) × (ℕ → Fin n → Fin n) => f z.1 z.2) :=
    measurable_from_prod_countable_right hf
  rw [← lintegral_map hm measurable_headTail, stepMeasure_headTail,
    lintegral_prod _ hm.aemeasurable]

lemma sigmaAllE_remaining_succ (R : ℕ → Fin n → Fin n)
    (A : Finset (Fin n)) (i : Fin n) (j : ℕ) :
    sigmaAllE R A i - (j+1 : ℕ) =
      sigmaAllE (fun t => R (t+1)) (infStep (R 0) A) i - j := by
  by_cases hi : i ∈ A
  · rw [sigmaAllE_mem' hi, sigmaAllE_mem' (subset_infStep _ _ hi)]
    simp
  · rw [sigmaAll_stepE hi, Nat.cast_add, Nat.cast_one, add_comm (j : ℝ≥0∞) 1,
      ENNReal.add_sub_add_eq_sub_left]

/-- C.11 before real conversion; valid even for noncompleting initial sets.
The proof uses the actual product contact law, not an assumed potential bound. -/
theorem lintegral_VpotE_inform (C : ContactMatrix n) (A : Finset (Fin n)) (j : ℕ) :
    (∫⁻ R, VpotE C (Inform R A j) ∂stepMeasure C) =
      ∑ i : Fin n, ∫⁻ R, (sigmaAllE R A i - j) ∂stepMeasure C := by
  induction j generalizing A with
  | zero => simp [Inform_zero, VpotE]
  | succ j ih =>
    have hshift (R : ℕ → Fin n → Fin n) :
        Inform R A (j+1) = Inform (fun t => R (t+1)) (infStep (R 0) A) j := by
      rw [Nat.add_comm j 1, Inform_shift, Inform_one]
      congr 1
      funext t
      rw [Nat.add_comm]
    simp_rw [hshift]
    rw [lintegral_step_headTail C (fun J R => VpotE C (Inform R (infStep J A) j))
      (fun J => measurable_inform_function (VpotE C) (infStep J A) j)]
    simp_rw [ih]
    rw [lintegral_finsetSum _ (fun i _ => by
      apply Measurable.of_discrete)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← lintegral_step_headTail C (fun J R => sigmaAllE R (infStep J A) i - j)
      (fun J => (measurable_sigmaAllE (infStep J A) i).sub measurable_const)]
    exact lintegral_congr fun R => (sigmaAllE_remaining_succ R A i j).symm

/-- The paper's `v_j`, with the positive part taken before expectation. -/
def remainingV (hd : 0 < n-1) (C : ContactMatrix n) (i0 : Fin n) (j : ℕ) : ℝ :=
  ∑ i : Fin n, (∫⁻ ω, ENNReal.ofReal (max (sigmaR hd ω i0 i - j) 0)
    ∂procMeasure C (n-1)).toReal

lemma remainingV_nonneg (hd : 0 < n-1) (C : ContactMatrix n) (i0 : Fin n) (j : ℕ) :
    0 ≤ remainingV hd C i0 j :=
  Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg

lemma remainingV_zero (hd : 0 < n-1) (C : ContactMatrix n) (i0 : Fin n) :
    remainingV hd C i0 0 = M1 hd C i0 := by
  simp only [remainingV, M1, Nat.cast_zero, sub_zero,
    max_eq_left (sigmaR_nonneg hd _ _ _)]

end AnvBandit
