import AnvBandit.ActualCostCoefficients

noncomputable section
namespace AnvBandit
variable {n K : ℕ}
namespace DecayModel
variable (M : DecayModel n K)

/-- C.24 derives the propagation moment coefficient from the original irreducible
contact matrix and the exact preparation budget. -/
lemma Pbeta_Hxi_le {L ξ β : ℝ} {h : ℕ} (C : ContactMatrix n) (i0 : Fin n)
    (hh : 1 ≤ h) (hξ : 0 < ξ) (hβ : 1 < β) (hL : Lstar n K ≤ L) :
    Pbeta (by have := M.two_le_n; omega) C i0 (Hxi h ξ L)
      (lastShortPhase (Hxi h ξ L) β (M.Bschedule L)) β ≤
      M.Abetaxi ξ β (epsP C) * (h + ξ * L) := by
  have hn : 1 ≤ n := by have := M.two_le_n; omega
  have hLp : 0 < L := lt_of_lt_of_le (Lstar_pos hn
    (by have := M.two_le_K; omega)) hL
  have hH : (0 : ℝ) ≤ Hxi h ξ L := Nat.cast_nonneg _
  have hb := Pbeta_le M.two_le_n C (ReachData.ofIrreducible C.irreducible i0)
    (rH := (lastShortPhase (Hxi h ξ L) β (M.Bschedule L) : ℝ)) hH
    (Nat.cast_nonneg _) hβ.le
  have hr : (lastShortPhase (Hxi h ξ L) β (M.Bschedule L) : ℝ) ≤ M.rcoef ξ β := by
    exact_mod_cast M.lastShortPhase_Hxi_le_rcoef hh hξ hβ hL
  have hrpow := Real.rpow_le_rpow (Nat.cast_nonneg _) hr (by linarith : 0 ≤ β)
  have hA : 0 ≤ M.Abetaxi ξ β (epsP C) := M.Abetaxi_nonneg hn (by linarith) (epsP_pos C)
  have hcoef : 1 + 2 ^ (β - 1) *
      ((lastShortPhase (Hxi h ξ L) β (M.Bschedule L) : ℝ) ^ β +
        Real.exp 1 * Real.Gamma (β + 1) * (((n : ℝ) - 1) / epsP C) ^ β) ≤
      M.Abetaxi ξ β (epsP C) := by
    unfold Abetaxi
    exact add_le_add_right (mul_le_mul_of_nonneg_left (add_le_add_left hrpow _)
      (Real.rpow_nonneg (by norm_num) _)) 1
  calc _ ≤ (Hxi h ξ L : ℝ) * M.Abetaxi ξ β (epsP C) :=
           hb.trans (mul_le_mul_of_nonneg_left hcoef hH)
       _ ≤ M.Abetaxi ξ β (epsP C) * (h + ξ * L) := by
         have hhx := (Hxi_lt h (by omega) (ξ := ξ) (L := L) (mul_pos hξ hLp).le).le
         nlinarith [mul_le_mul_of_nonneg_right hhx hA]

end DecayModel
end AnvBandit
