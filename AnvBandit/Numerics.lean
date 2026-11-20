import Mathlib

set_option maxHeartbeats 1000000

/-!
# Appendix D: numerical relations of the experiments

The experiments themselves (Monte-Carlo regret values, figures, tables) are numerical and cannot be
reproduced inside Lean.  This file formalises the *deterministic mathematical relations* that
underlie the reported numbers:

* the EFF-FEWA screening threshold `d_F(w,t) = √(2(log K + 5 log t)/w)` (equation (D.2));
* the reported comparison `d_F(2048, 3·10⁵) > 0.1` (the screening threshold exceeds the gap);
* the "predicted per-round loss" arithmetic `0.1·(1−p)`;
* the conflict-marker ratio `(24/25)·0.1 = 0.096`;
* the `t`-critical value `2.021076` used for the `df ≈ 40` interval.
-/

noncomputable section
open scoped BigOperators

namespace AnvBandit

/-- EFF-FEWA screening threshold (equation (D.2)):
`d_F(w,t) = √(8σ_F² log(1/δ_{F,t})/w) = √(2(log K + 5 log t)/w)` with `σ_F² = 1/4`,
`δ_{F,t} = 1/(K t⁵)`. -/
def dF (K w t : ℕ) : ℝ := Real.sqrt (2 * (Real.log K + 5 * Real.log t) / w)

lemma dF_nonneg (K w t : ℕ) : 0 ≤ dF K w t := Real.sqrt_nonneg _

/-- The screening threshold is antitone in the window size `w`, on the region where the radicand is
nonnegative. -/
lemma dF_anti_w {K t : ℕ} {w₁ w₂ : ℕ}
    (h : w₁ ≤ w₂) (hK : 0 ≤ Real.log K + 5 * Real.log t) (hw₁ : 0 < w₁) :
    dF K w₂ t ≤ dF K w₁ t := by
  rw [dF, dF]
  apply Real.sqrt_le_sqrt
  rw [div_le_div_iff₀ (by exact_mod_cast (lt_of_lt_of_le hw₁ h) : (0:ℝ) < w₂)
    (by exact_mod_cast hw₁ : (0:ℝ) < w₁)]
  have hX : (0:ℝ) ≤ 2 * (Real.log K + 5 * Real.log t) := by linarith
  have hw : ((w₁ : ℕ) : ℝ) ≤ w₂ := by exact_mod_cast h
  nlinarith [hX, hw]

/-- `4 < log 300000`, used by the threshold comparison. -/
lemma log_300000_gt_four : (4:ℝ) < Real.log 300000 := by
  rw [← Real.log_exp 4]
  apply Real.log_lt_log (Real.exp_pos 4)
  have h3 : Real.exp 4 = (Real.exp 1) ^ 4 := by
    rw [show (4:ℝ) = ((4:ℕ):ℝ) * 1 by norm_num, Real.exp_nat_mul]
  have h2 : (Real.exp 1) ^ 4 < (3:ℝ) ^ 4 :=
    pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le (by norm_num : 4 ≠ 0)
  rw [h3]; linarith [h2]

/-- The main reported comparison (Appendix D.2): with `K = 25` arms, window `w = 2048` and horizon
`T = 3·10⁵`, the screening threshold exceeds the gap `0.1`. -/
theorem dF_gt_point_one : 0.1 < dF 25 2048 300000 := by
  have hlog300 := log_300000_gt_four
  have hlog25 : (0:ℝ) < Real.log 25 := Real.log_pos (by norm_num)
  have harg : (0.1:ℝ) ^ 2 < 2 * (Real.log 25 + 5 * Real.log 300000) / 2048 := by
    rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 2048)]
    nlinarith [hlog300, hlog25]
  rw [dF, ← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 0.1)]
  exact Real.sqrt_lt_sqrt (sq_nonneg 0.1) harg

/-- The predicted per-round base-value loss when the optimal arm is selected with ratio `p` is
`0.1·(1−p)` (Appendix D.2). -/
lemma predicted_loss (p : ℝ) : (1/10) * (1 - p) = 1/10 - 1/10 * p := by ring

lemma predicted_loss_01 : (1/10:ℝ) * (1 - 1/100) = 99/1000 := by norm_num
lemma predicted_loss_04 : (1/10:ℝ) * (1 - 4/100) = 96/1000 := by norm_num

/-- The conflict-marker selection ratio: `(24/25)·0.1 = 0.096` (Appendix D.1). -/
lemma ratio_24_25 : (24:ℝ) / 25 * (1/10) = 96/1000 := by norm_num

/-- The `t`-critical value used for the approximate 95% interval (Appendix D.2), taken from the
smaller degree of freedom `df = 40` and therefore slightly larger than the exact `df = 49` value. -/
def tCrit : ℝ := 2.021076

lemma tCrit_bounds : 2.02 ≤ tCrit ∧ tCrit ≤ 2.03 := by
  constructor <;> norm_num [tCrit]

end AnvBandit
