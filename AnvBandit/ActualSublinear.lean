import AnvBandit.ActualExplicitCanonical

noncomputable section
open scoped Topology
open Filter
namespace AnvBandit.ActualExplicitRegret
open Execution TrajectoryExpectation
variable {n K : ℕ}

lemma horizon_log_ratio :
    Tendsto (fun T : ℕ => Real.log ((T : ℝ) + 2) / ((T : ℝ) + 1)) atTop (𝓝 0) := by
  have hx : Tendsto (fun T : ℕ => (T : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp hx
  simpa only [Function.comp_def, pow_one, one_mul,
    show ∀ t : ℕ, (t : ℝ) + 2 + -1 = (t : ℝ) + 1 by intro t; ring] using h

/-- The last sentence of the paper's time-order proof: if the legal communication
primitive satisfies h(T)=o(T), actual team regret divided by nT tends to zero.
The sequence uses horizon T+1 so that every execution, including its first term, is legal. -/
theorem actual_sublinear (M : DecayModel n K) (C : ContactMatrix n) (lam : Fin 2)
    (ξ β : ℝ) (hξ : 0 < ξ) (hβ : 1 < β) (h : ℕ → ℕ)
    (hh : ∀ T : ℕ, 1 ≤ h (T + 1))
    (hsub : (fun T : ℕ => (h T : ℝ)) =o[atTop] (fun T : ℕ => (T : ℝ))) :
    Tendsto (fun T : ℕ =>
      teamRegret M (explicitParams M (T + 1) (h (T + 1)) ξ β (by omega) (hh T) hξ hβ) C lam /
        ((n : ℝ) * ((T : ℝ) + 1))) atTop (𝓝 0) := by
  obtain ⟨A, hA, hbound⟩ := actual_Hxi_order M C lam ξ β hξ hβ
  have hhlim : Tendsto (fun T : ℕ => (h (T + 1) : ℝ) / ((T : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      hsub.tendsto_div_nhds_zero.comp (tendsto_add_atTop_nat 1)
  have hlim : Tendsto (fun T : ℕ => (A / (n : ℝ)) *
      ((h (T + 1) : ℝ) / ((T : ℝ) + 1) + Real.log ((T : ℝ) + 2) / ((T : ℝ) + 1)))
      atTop (𝓝 0) := by
    simpa only [add_zero, mul_zero] using (hhlim.add horizon_log_ratio).const_mul (A / (n : ℝ))
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := M.two_le_n; omega)
  apply squeeze_zero (fun T => div_nonneg (teamRegret_nonneg M _ C lam) (by positivity)) _ hlim
  intro T
  have hb := div_le_div_of_nonneg_right (hbound (T + 1) (h (T + 1)) (by omega) (hh T))
    (show (0 : ℝ) ≤ (n : ℝ) * ((T : ℝ) + 1) by positivity)
  refine hb.trans_eq ?_
  push_cast
  rw [show (T : ℝ) + 1 + 1 = (T : ℝ) + 2 by ring]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end AnvBandit.ActualExplicitRegret
