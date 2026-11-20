import AnvBandit.Explicit
import AnvBandit.ScheduleLower
import AnvBandit.Moments

/-! Analytic coefficients of C.22–C.26. These lemmas derive threshold bounds from
original parameters; they do not assume exploration or regret conclusions. -/
noncomputable section
open scoped BigOperators
namespace AnvBandit
variable {n K : ℕ}

lemma Lstar_le_LdeltaStar (hn : 1 ≤ n) (hK : 1 ≤ K) {T : ℕ} (hT : 1 ≤ T) :
    Lstar n K ≤ LdeltaStar n K T := by
  unfold Lstar LdeltaStar
  apply Real.log_le_log
  · positivity
  · have ht : (1 : ℝ) ≤ T := by exact_mod_cast hT
    have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hk' : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    push_cast
    have hprod : (4 : ℝ) ≤ (T : ℝ) * ((T : ℝ) + 1)^2 := by nlinarith
    nlinarith [mul_nonneg hn' hk', mul_nonneg (mul_nonneg hn' hk') (sub_nonneg.mpr hprod)]

lemma nk_le_thetaN_mul {L Δ : ℝ} (hn : 1 ≤ n) (hK : 1 ≤ K)
    (hL : Lstar n K ≤ L) : (nk L Δ : ℝ) ≤ thetaN n K Δ * L := by
  have hp := Lstar_pos hn hK
  have hL0 : 0 ≤ L := le_trans hp.le hL
  have hceil := (Nat.ceil_lt_add_one (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 32) hL0)
    (sq_nonneg Δ))).le
  have hunit : (1 : ℝ) ≤ L / Lstar n K := (le_div_iff₀ hp).mpr (by simpa using hL)
  change (⌈32 * L / Δ ^ 2⌉₊ : ℝ) ≤ _
  calc _ ≤ 32 * L / Δ ^ 2 + 1 := hceil
    _ ≤ thetaN n K Δ * L := by
      unfold thetaN
      rw [show (32 / Δ ^ 2 + 1 / Lstar n K) * L =
        32 * L / Δ ^ 2 + L / Lstar n K by ring]
      linarith

namespace DecayModel
variable (M : DecayModel n K)

lemma mkAll_le_thetaM_mul {L : ℝ} (hL : Lstar n K ≤ L) {k : Fin K}
    (hk : k ∈ M.others) : (M.mkAll L k : ℝ) ≤ M.thetaM k * L := by
  have hn : 1 ≤ n := by have := M.two_le_n; omega
  have hK : 1 ≤ K := by have := M.two_le_K; omega
  have hp := Lstar_pos hn hK
  have hL0 : 0 ≤ L := le_trans hp.le hL
  have hk' : k ≠ M.star := (Finset.mem_erase.mp hk).1
  rw [mkAll_eq_mkThr M hk', mkThr, Nat.cast_max, thetaM, dif_neg hk']
  apply max_le
  · calc (M.m0 k hk' : ℝ) = ((M.m0 k hk' : ℝ) / Lstar n K) * Lstar n K := by field_simp [ne_of_gt hp]
         _ ≤ ((M.m0 k hk' : ℝ) / Lstar n K) * L :=
           mul_le_mul_of_nonneg_left hL (div_nonneg (Nat.cast_nonneg _) hp.le)
         _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hL0
  · exact (nk_le_thetaN_mul hn hK hL).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hL0)

lemma mMax_le_thetaM_mul {L : ℝ} (hL : Lstar n K ≤ L) :
    (M.mMax L : ℝ) ≤ M.supOthers M.thetaM * L := by
  obtain ⟨k, hk, heq⟩ := Finset.exists_mem_eq_sup' M.others_nonempty (fun k => M.mkAll L k)
  change ((M.others.sup' M.others_nonempty (fun k => M.mkAll L k) : ℕ) : ℝ) ≤ _
  rw [heq]
  exact (M.mkAll_le_thetaM_mul hL hk).trans (mul_le_mul_of_nonneg_right
    (M.le_supOthers hk) (le_trans (Lstar_pos (by have := M.two_le_n; omega)
      (by have := M.two_le_K; omega)).le hL))

lemma Bschedule_le_Bcoef_mul {L : ℝ} (hL : Lstar n K ≤ L) :
    (M.Bschedule L : ℝ) ≤ M.Bcoef * L := by
  have hb : (M.Bschedule L : ℝ) ≤ ((kappa n K : ℝ) + 1) * (M.mMax L : ℝ) := by
    exact_mod_cast M.Bschedule_le_coarse L
  apply hb.trans
  simpa [Bcoef, mul_assoc] using
    (mul_le_mul_of_nonneg_left (M.mMax_le_thetaM_mul hL)
      (show (0 : ℝ) ≤ (kappa n K : ℝ) + 1 by positivity))

lemma Bcoef_nonneg : 0 ≤ M.Bcoef := by
  unfold Bcoef
  apply mul_nonneg (by positivity)
  exact M.supOthers_nonneg fun k _ => M.thetaM_nonneg
    (by have := M.two_le_n; omega) (by have := M.two_le_K; omega) k

lemma lastShortPhase_Hxi_le_rcoef {L ξ β : ℝ} {h : ℕ}
    (hh : 1 ≤ h) (hξ : 0 < ξ) (hβ : 1 < β) (hL : Lstar n K ≤ L) :
    lastShortPhase (Hxi h ξ L) β (M.Bschedule L) ≤ M.rcoef ξ β := by
  have hLp : 0 < L := lt_of_lt_of_le (Lstar_pos
    (by have := M.two_le_n; omega) (by have := M.two_le_K; omega)) hL
  have hH : (0 : ℝ) < Hxi h ξ L := by
    exact lt_of_lt_of_le (mul_pos hξ hLp) (Hxi_ge h (by omega) ξ L)
  have hratio : (M.Bschedule L : ℝ) / Hxi h ξ L ≤ M.Bcoef / ξ := by
    apply (div_le_div_iff₀ hH hξ).mpr
    calc (M.Bschedule L : ℝ) * ξ ≤ M.Bcoef * L * ξ :=
           mul_le_mul_of_nonneg_right (M.Bschedule_le_Bcoef_mul hL) hξ.le
         _ = M.Bcoef * (ξ * L) := by ring
         _ ≤ M.Bcoef * Hxi h ξ L := mul_le_mul_of_nonneg_left
           (Hxi_ge h (by omega) ξ L) M.Bcoef_nonneg
  rw [← rH_eq_last_short_phase hH hβ (Nat.cast_nonneg _) rfl]
  apply (lemma_B_3 hH hβ (Nat.cast_nonneg _) rfl).1.trans
  apply Nat.ceil_mono
  apply Real.rpow_le_rpow
  · positivity
  · exact div_le_div_of_nonneg_right (add_le_add_left hratio 2) (by linarith)
  · positivity

lemma rho_le_rhoConst {T : ℕ} (hT : 1 ≤ T) (lam : Fin 2) (k : Fin K) :
    M.rho T lam k ≤ M.rhoConst lam k := by
  unfold rho rhoConst
  split
  · rfl
  · apply add_le_add_right
    apply psi_anti_le (M.f_anti M.star)
    · have hn : 1 ≤ n := by have := M.two_le_n; omega
      exact one_le_pow₀ hn
    · exact Nat.le_mul_of_pos_right _ (by omega)

end DecayModel
end AnvBandit
