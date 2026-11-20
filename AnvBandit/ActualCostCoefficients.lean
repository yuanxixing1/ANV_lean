import AnvBandit.ActualExplicit

noncomputable section
open scoped BigOperators
namespace AnvBandit.DecayModel
variable {n K : ℕ} (M : DecayModel n K)

/-- The exact subset budget scales with a pointwise coefficient bound. -/
lemma terminal_coefficient_bound {w a : Fin K → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hw : ∀ k ∈ M.others, w k ≤ a k * L) :
    min (n * (M.others.powersetCard (kappa n K)).sup'
      (Finset.powersetCard_nonempty_of_le M.kappa_le_others_card) (fun F => ∑ k ∈ F, w k))
      ((∑ k ∈ M.others, w k) + (n + 1) * M.supOthers w) ≤
    min (n * (kappa n K : ℝ) * M.supOthers a)
      ((∑ k ∈ M.others, a k) + (n + 1) * M.supOthers a) * L := by
  have hmax : M.supOthers w ≤ M.supOthers a * L := M.supOthers_le fun k hk =>
    (hw k hk).trans (mul_le_mul_of_nonneg_right (M.le_supOthers hk) hL)
  have hsum : (∑ k ∈ M.others, w k) ≤ (∑ k ∈ M.others, a k) * L := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum hw
  have hsub : (M.others.powersetCard (kappa n K)).sup'
      (Finset.powersetCard_nonempty_of_le M.kappa_le_others_card) (fun F => ∑ k ∈ F, w k)
      ≤ (kappa n K : ℝ) * M.supOthers a * L := by
    apply Finset.sup'_le
    intro F hF
    obtain ⟨hFsub, hFcard⟩ := Finset.mem_powersetCard.mp hF
    calc ∑ k ∈ F, w k ≤ ∑ _k ∈ F, M.supOthers a * L :=
           Finset.sum_le_sum fun k hk => (hw k (hFsub hk)).trans
             (mul_le_mul_of_nonneg_right (M.le_supOthers (hFsub hk)) hL)
         _ = _ := by simp [hFcard, mul_assoc]
  have hleft := mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hright := add_le_add hsum (mul_le_mul_of_nonneg_left hmax
    (show (0 : ℝ) ≤ n + 1 by positivity))
  by_cases hc : n * (kappa n K : ℝ) * M.supOthers a ≤
      (∑ k ∈ M.others, a k) + (n + 1) * M.supOthers a
  · rw [min_eq_left hc]
    exact (min_le_left _ _).trans (by simpa [mul_assoc] using hleft)
  · rw [min_eq_right (le_of_not_ge hc)]
    exact (min_le_right _ _).trans (by nlinarith [hright])

lemma Ccap_rhoConst_le {L : ℝ} (hL : Lstar n K ≤ L) :
    M.Ccap (M.rhoConst 0) L ≤ M.Jlam 0 * L := by
  have hL0 : 0 ≤ L := le_trans (Lstar_pos (by have := M.two_le_n; omega)
    (by have := M.two_le_K; omega)).le hL
  have hb := M.terminal_coefficient_bound (w := M.wk (M.rhoConst 0) L)
    (a := fun k => M.rhoConst 0 k * M.thetaM k) hL0 (fun k hk => by
      simpa [wk, mul_assoc] using mul_le_mul_of_nonneg_left
        (M.mkAll_le_thetaM_mul hL hk) (M.rhoConst_nonneg 0 k))
  simpa [Ccap, Wkappa, dif_pos M.kappa_le_others_card, Wsum, wmax, Jlam, thetaLam] using hb

lemma CNcap_rhoConst_le {L : ℝ} (hL : Lstar n K ≤ L) :
    M.CNcap (M.rhoConst 1) L ≤ M.Jlam 1 * L := by
  have hn : 1 ≤ n := by have := M.two_le_n; omega
  have hK : 1 ≤ K := by have := M.two_le_K; omega
  have hL0 : 0 ≤ L := le_trans (Lstar_pos hn hK).le hL
  have hb := M.terminal_coefficient_bound (w := M.wkN (M.rhoConst 1) L)
    (a := fun k => M.rhoConst 1 k * thetaN n K (M.gap k)) hL0 (fun k hk => by
      have hk' : k ≠ M.star := (Finset.mem_erase.mp hk).1
      simpa [wkN, nkAll, hk', mul_assoc] using mul_le_mul_of_nonneg_left
        (nk_le_thetaN_mul hn hK (Δ := M.gap k) hL) (M.rhoConst_nonneg 1 k))
  simpa [CNcap, WNkappa, dif_pos M.kappa_le_others_card, WNsum, wNmax, Jlam, thetaLam] using hb

/-- C.26, with one team-wide public fatigue budget, not one copy per agent. -/
lemma Clam_rhoConst_le {L : ℝ} (hL : Lstar n K ≤ L) (lam : Fin 2) :
    M.Clam (M.rhoConst lam) L 0 lam ≤ M.Jlam lam * L + M.Dlam lam := by
  fin_cases lam
  · simpa [Clam, Dlam] using M.Ccap_rhoConst_le hL
  · simp only [Clam, zero_mul, add_zero, Dlam, show (1 : Fin 2) ≠ 0 by decide, if_false]
    exact (min_le_right _ _).trans (add_le_add_left (M.CNcap_rhoConst_le hL) _)
end AnvBandit.DecayModel
