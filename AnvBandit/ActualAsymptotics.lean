import AnvBandit.ActualExplicitRegret

noncomputable section
open scoped Topology
open Filter
namespace AnvBandit.ActualExplicitRegret
open Execution TrajectoryExpectation
variable {n K : ℕ}

/-- Equation (4.7), uniformly in the communication primitive `h`, for the actual
algorithm. The constant is fixed before either `T` or `h` is chosen. -/
theorem actual_Hxi_order (M : DecayModel n K) (C : ContactMatrix n) (lam : Fin 2)
    (ξ β : ℝ) (hξ : 0 < ξ) (hβ : 1 < β) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ T h : ℕ, ∀ (hT : 1 ≤ T) (hh : 1 ≤ h),
      teamRegret M (explicitParams M T h ξ β hT hh hξ hβ) C lam ≤
      A * ((h : ℝ) + Real.log (T + 1)) := by
  let ch := Ch n (M.rhoMax lam) (M.Abetaxi ξ β (epsP C))
  let cl := Clog ξ ch (M.Jlam lam)
  let c0 := C0 (M.Gamma lam) (M.Dlam lam) (n * M.rhoMax lam) cl (n * K)
  have hn : 1 ≤ n := by have := M.two_le_n; omega
  have hK : 1 ≤ K := by have := M.two_le_K; omega
  have hch : 0 ≤ ch := by
    dsimp [ch, Ch]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (M.rhoMax_nonneg lam))
      (M.Abetaxi_nonneg hn (by linarith) (epsP_pos C))
  have hcl : 0 ≤ cl := by
    dsimp [cl, Clog]
    exact mul_nonneg (by norm_num) (add_nonneg (mul_nonneg hξ.le hch) (M.Jlam_nonneg hn hK lam))
  refine ⟨|c0| + ch + cl, by positivity, fun T h hT hh => ?_⟩
  have hb := (actual_explicit M C lam T h ξ β hT hh hξ hβ).trans (min_le_right _ _)
  change _ ≤ c0 + ch * (h : ℝ) + cl * Real.log (T + 1) at hb
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hlog : 0 ≤ Real.log (T + 1) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ T + 1 by omega))
  have hconstant : c0 ≤ |c0| * (h : ℝ) := (le_abs_self c0).trans
    (by nlinarith [abs_nonneg c0])
  nlinarith [mul_nonneg (abs_nonneg c0) hlog, mul_nonneg hch hlog,
    mul_nonneg hcl (show (0 : ℝ) ≤ h by positivity)]



/-- For fixed legal communication primitive, equation (4.7) is logarithmic in T. -/
theorem actual_fixed_h_log_order (M : DecayModel n K) (C : ContactMatrix n) (lam : Fin 2)
    (ξ β : ℝ) (hξ : 0 < ξ) (hβ : 1 < β) (h : ℕ) (hh : 1 ≤ h) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ T : ℕ, ∀ (hT : 1 ≤ T),
      teamRegret M (explicitParams M T h ξ β hT hh hξ hβ) C lam ≤
      B * Real.log (T + 1) := by
  obtain ⟨A, hA, hb⟩ := actual_Hxi_order M C lam ξ β hξ hβ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨A * ((h : ℝ) / Real.log 2 + 1), by positivity, fun T hT => ?_⟩
  have hl : Real.log 2 ≤ Real.log (T + 1) := Real.log_le_log (by norm_num)
    (by exact_mod_cast (show 2 ≤ T + 1 by omega))
  have hhlog : (h : ℝ) ≤ ((h : ℝ) / Real.log 2) * Real.log (T + 1) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    exact mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg h)
  have he := mul_le_mul_of_nonneg_left (add_le_add_left hhlog (Real.log (T + 1))) hA
  have hmain := hb T h hT hh
  nlinarith

end AnvBandit.ActualExplicitRegret
