import AnvBandit.RemainingWaitTail
import AnvBandit.Potential

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Finset Filter
namespace AnvBandit
variable {n : ℕ}

/-- The actual rounded schedule increments from C.3 (including d₀=0). -/
def scheduleOmega (H β : ℝ) (ℓ : ℕ) : ℝ :=
  posPart (dEll H β ℓ - dEll H β (ℓ-1))

lemma scheduleOmega_nonneg (H β : ℝ) (ℓ : ℕ) : 0 ≤ scheduleOmega H β ℓ :=
  le_max_right _ _

lemma dEll_nonneg_real {H β : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β) (ℓ : ℕ) :
    0 ≤ dEll H β ℓ := by
  apply sub_nonneg.mpr
  apply mul_le_mul_of_nonneg_left _ hH
  exact_mod_cast Nat.ceil_mono (Real.rpow_le_rpow (Nat.cast_nonneg _) (by
    exact_mod_cast Nat.sub_le ℓ 1) hβ)

/-- A coarse polynomial envelope; its integer degree dominates an arbitrary real β.
No restriction of the paper's real exponent to integers is made. -/
lemma scheduleOmega_le_polynomial {H β : ℝ} (hH : 0 ≤ H) (hβ : 1 < β) (ℓ : ℕ) :
    scheduleOmega H β ℓ ≤ (2*H) * (ℓ : ℝ)^⌈β⌉₊ := by
  by_cases hℓ : ℓ = 0
  · subst ℓ
    simp only [scheduleOmega, Nat.zero_sub, sub_self, posPart, max_self]
    positivity
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hℓ
  have hp1 : 1 ≤ (ℓ : ℝ)^⌈β⌉₊ := one_le_pow₀ hℓ1
  have hpow : (ℓ : ℝ)^β ≤ (ℓ : ℝ)^⌈β⌉₊ := by
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le hℓ1 (Nat.le_ceil β)
  have hceil : (⌈(ℓ : ℝ)^β⌉₊ : ℝ) ≤ 2 * (ℓ : ℝ)^⌈β⌉₊ := by
    have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg ℓ) β)
    linarith
  have hd := dEll_nonneg_real hH (le_of_lt (lt_trans zero_lt_one hβ)) (ℓ-1)
  have ht : 0 ≤ tEll H β (ℓ-1) := mul_nonneg hH (Nat.cast_nonneg _)
  have hw : scheduleOmega H β ℓ ≤ tEll H β ℓ := by
    apply max_le
    · dsimp [dEll] at *
      linarith
    · exact mul_nonneg hH (Nat.cast_nonneg _)
  calc
    scheduleOmega H β ℓ ≤ tEll H β ℓ := hw
    _ ≤ H * (2 * (ℓ : ℝ)^⌈β⌉₊) := mul_le_mul_of_nonneg_left hceil hH
    _ = _ := by ring

/-- Concrete C.4 constant: schedule and waiting times are both the paper's objects. -/
def concreteKbeta (hd : 0 < n-1) (C : ContactMatrix n) (i0 : Fin n)
    (H β : ℝ) (r : ℕ) : ℝ := Kbeta (scheduleOmega H β) (remainingV hd C i0) r

lemma remainingV_geometric (hn : 2 ≤ n) (C : ContactMatrix n) (i0 : Fin n) (j : ℕ) :
    remainingV (by omega) C i0 j ≤ (M1 (by omega) C i0 * Real.exp 1) *
      (Real.exp (-(epsP C / ((n : ℝ)-1))))^j := by
  have h := remainingV_le_completion_tail (hd := by omega) hn C i0 j
  have he : Real.exp (-(epsP C * ((j : ℝ) / ((n : ℝ)-1)))) =
      (Real.exp (-(epsP C / ((n : ℝ)-1))))^j := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rwa [he] at h

/-- C.4 summability for every original irreducible contact matrix and every real β>1.
All concentration, budget and regret assumptions are absent from this independent fact. -/
theorem concreteKbeta_summable (hn : 2 ≤ n) (C : ContactMatrix n) (i0 : Fin n)
    {H β : ℝ} (hH : 0 ≤ H) (hβ : 1 < β) (r : ℕ) :
    Summable (fun ℓ => scheduleOmega H β (ℓ+1) * remainingV (by omega) C i0 (ℓ-r)) := by
  have hd : (0 : ℝ) < (n : ℝ)-1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  apply Kbeta_summable (A := 2*H) (C := M1 (by omega) C i0 * Real.exp 1)
    (ρ := Real.exp (-(epsP C / ((n : ℝ)-1)))) (by positivity) (by
      apply mul_nonneg _ (Real.exp_pos _).le
      unfold M1
      exact Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)
    (scheduleOmega_nonneg H β) (remainingV_nonneg (by omega) C i0)
    (Real.exp_pos _) ((Real.exp_lt_one_iff).mpr (neg_neg_of_pos (div_pos (epsP_pos C) hd)))
    ⌈β⌉₊ (scheduleOmega_le_polynomial hH hβ)
    (remainingV_geometric hn C i0) r

end AnvBandit
