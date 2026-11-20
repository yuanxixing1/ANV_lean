import AnvBandit.Statements

/-!
# The explicit constant bound (4.4)–(4.5) of Theorem 4.1

This file proves `theorem_4_1_explicit`, the explicit finite-horizon bound

  `R^{(λ)}_{team}(T) ≤ min{ nT, C_{0,λ} + C_{h,λ} h + C_{log,λ} log(T+1) }`

with the coefficients of (4.5).  The global-waiting estimate `E_λ ≤ n ρ_max A_{β,ξ}(h + ξ L_δ)
+ D_λ + J_λ L_δ` (Appendix C.3) is taken as the hypothesis `hE` produced by the contact-process
analysis; everything else — the round-off by `δ = (T+1)^{-2}` (`δ n ρ_max T ≤ n ρ_max / 4`), the
splitting `L_δ = log(2nK) + log T + 2 log(T+1)`, and the algebra of the coefficients — is proved
here.
-/

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

noncomputable section
open scoped BigOperators Topology
open Filter Finset

namespace AnvBandit

variable {n K : ℕ}

/-- `L_* = log(8nK) > 0`. -/
lemma Lstar_pos (hn : 1 ≤ n) (hK : 1 ≤ K) : 0 < Lstar n K := by
  rw [Lstar]
  apply Real.log_pos
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hK1 : (1:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK
  nlinarith [hn1, hK1]

/-- `θ^N_k = 32/Δ² + 1/L_* ≥ 0`. -/
lemma thetaN_nonneg (hn : 1 ≤ n) (hK : 1 ≤ K) (Δ : ℝ) : 0 ≤ thetaN n K Δ := by
  rw [thetaN]
  have hL := Lstar_pos hn hK
  have h1 : 0 ≤ 1 / Lstar n K := div_nonneg zero_le_one hL.le
  have h2 : 0 ≤ 32 / Δ ^ 2 := div_nonneg (by norm_num) (sq_nonneg Δ)
  linarith

/-- Splitting of the analysis-time horizon: `L_δ = log(2nK) + log T + 2 log(T+1)`. -/
lemma LdeltaStar_eq (n K T : ℕ) (hn : 0 < n) (hK : 0 < K) (hT : 0 < T) :
    LdeltaStar n K T = Real.log (2 * ((n : ℝ) * K)) + Real.log T + 2 * Real.log (T + 1) := by
  unfold LdeltaStar
  have hT0 : (0:ℝ) < (T:ℝ) := by exact_mod_cast hT
  have hT1 : (0:ℝ) < (T:ℝ) + 1 := by positivity
  rw [show (2 * ((n * K : ℕ) : ℝ) * (T:ℝ) * ((T:ℝ)+1)^2)
        = (2 * ((n : ℝ) * K)) * ((T:ℝ) * ((T:ℝ)+1)^2) by push_cast; ring]
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hT0.ne' (by positivity),
      Real.log_pow]
  ring

namespace DecayModel

variable (M : DecayModel n K)

/-- `sup_{k ≠ ⋆} f ≥ 0` when `f ≥ 0` on the suboptimal arms. -/
lemma supOthers_nonneg {f : Fin K → ℝ} (hf : ∀ k ∈ M.others, 0 ≤ f k) : 0 ≤ M.supOthers f := by
  obtain ⟨k, hk⟩ := M.others_nonempty
  exact le_trans (hf k hk) (M.le_supOthers hk)

/-- `ρ^{(λ)}_k ≥ 0`. -/
lemma rhoConst_nonneg (lam : Fin 2) (k : Fin K) : 0 ≤ M.rhoConst lam k := by
  rw [rhoConst]; split
  · rfl
  · exact add_nonneg (M.gap_nonneg k) (psi_nonneg (fun s _ => M.f_nonneg M.star s) _)

/-- `θ^M_k ≥ 0`. -/
lemma thetaM_nonneg (hn : 1 ≤ n) (hK : 1 ≤ K) (k : Fin K) : 0 ≤ M.thetaM k := by
  rw [thetaM]; split
  · norm_num
  · exact le_max_iff.mpr (Or.inl (div_nonneg (Nat.cast_nonneg _) (Lstar_pos hn hK).le))

/-- `θ^{(λ)}_k ≥ 0`. -/
lemma thetaLam_nonneg (hn : 1 ≤ n) (hK : 1 ≤ K) (lam : Fin 2) (k : Fin K) :
    0 ≤ M.thetaLam lam k := by
  rw [thetaLam]; split
  · exact M.thetaM_nonneg hn hK k
  · exact thetaN_nonneg hn hK (M.gap k)

/-- `J_λ ≥ 0`. -/
lemma Jlam_nonneg (hn : 1 ≤ n) (hK : 1 ≤ K) (lam : Fin 2) : 0 ≤ M.Jlam lam := by
  rw [Jlam]
  apply le_min
  · have hsup : 0 ≤ M.supOthers (fun k => M.rhoConst lam k * M.thetaLam lam k) :=
      M.supOthers_nonneg (fun k _ => mul_nonneg (M.rhoConst_nonneg lam k)
        (M.thetaLam_nonneg hn hK lam k))
    exact mul_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg _)) hsup
  · apply add_nonneg
    · exact Finset.sum_nonneg (fun k _ => mul_nonneg (M.rhoConst_nonneg lam k)
        (M.thetaLam_nonneg hn hK lam k))
    · exact mul_nonneg (by positivity)
        (M.supOthers_nonneg (fun k _ => mul_nonneg (M.rhoConst_nonneg lam k)
          (M.thetaLam_nonneg hn hK lam k)))

/-- `ρ^{(λ)}_max ≥ 0`. -/
lemma rhoMax_nonneg (lam : Fin 2) : 0 ≤ M.rhoMax lam :=
  M.supOthers_nonneg (fun k _ => M.rhoConst_nonneg lam k)

/-- `A_{β,ξ} ≥ 0`. -/
lemma Abetaxi_nonneg {ξ β εP : ℝ} (hn : 1 ≤ n) (hβ : 0 < β) (hεP : 0 < εP) :
    0 ≤ M.Abetaxi ξ β εP := by
  rw [Abetaxi]
  have h1 : 0 ≤ (2:ℝ) ^ (β - 1) := Real.rpow_nonneg (by norm_num) _
  have h2 : 0 ≤ ((M.rcoef ξ β : ℝ)) ^ β := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hr : 0 ≤ ((n:ℝ) - 1) / εP := div_nonneg (by linarith) hεP.le
  have h3 : 0 ≤ Real.exp 1 * Real.Gamma (β + 1) * (((n:ℝ) - 1) / εP) ^ β :=
    mul_nonneg (mul_nonneg (Real.exp_pos 1).le (Real.Gamma_pos_of_pos (by linarith)).le)
      (Real.rpow_nonneg hr _)
  have := mul_nonneg h1 (add_nonneg h2 h3)
  linarith

/-- Round-off by `δ = (T+1)^{-2}`: `δ · n ρ_max T ≤ n ρ_max / 4`. -/
lemma deltaStar_mul_le (T : ℕ) (lam : Fin 2) (hT : 1 ≤ T) :
    deltaStar T * (n * M.rhoMax lam * T) ≤ n * M.rhoMax lam / 4 := by
  have hρ : 0 ≤ M.rhoMax lam := M.rhoMax_nonneg lam
  have hsq : (0:ℝ) < ((T:ℝ)+1)^2 := by positivity
  have hfrac : (T:ℝ) / ((T:ℝ)+1)^2 ≤ 1/4 := by
    rw [div_le_iff₀ hsq]
    nlinarith [sq_nonneg ((T:ℝ) - 1)]
  have hds : deltaStar T = (((T:ℝ)+1)^2)⁻¹ := by
    rw [deltaStar]; simp only [zpow_neg, zpow_ofNat]
  rw [hds]
  rw [show (((T:ℝ)+1)^2)⁻¹ * (n * M.rhoMax lam * T)
        = (n * M.rhoMax lam) * ((T:ℝ) * (((T:ℝ)+1)^2)⁻¹) by ring]
  rw [show (T:ℝ) * (((T:ℝ)+1)^2)⁻¹ = (T:ℝ) / ((T:ℝ)+1)^2 by rw [div_eq_mul_inv]]
  calc (n * M.rhoMax lam) * ((T:ℝ) / ((T:ℝ)+1)^2)
      ≤ (n * M.rhoMax lam) * (1/4) := by
        apply mul_le_mul_of_nonneg_left hfrac; positivity
    _ = n * M.rhoMax lam / 4 := by ring

/-- Theorem 4.1, equations (4.4)–(4.5): given the global-waiting estimate `hE` (Appendix C.3) and
the combined bound `hR` of (4.3), the team regret obeys the explicit bound `explicitBound`. -/
theorem theorem_4_1_explicit (T h : ℕ) (ξ β εP : ℝ) (lam : Fin 2)
    (hT : 1 ≤ T) (hξ : 0 ≤ ξ) (hβ : 1 < β) (hεP : 0 < εP) (E R : ℝ)
    (hE : E ≤ n * M.rhoMax lam * M.Abetaxi ξ β εP * (h + ξ * LdeltaStar n K T)
            + M.Dlam lam + M.Jlam lam * LdeltaStar n K T)
    (hR : R ≤ Uco ((n : ℝ) * T) (M.Gamma lam) (n * M.rhoMax lam * T) E
            (deltaStar T * (n * M.rhoMax lam * T))) :
    R ≤ explicitBound M T h ξ β εP lam := by
  have hn : 1 ≤ n := le_trans (by norm_num) M.two_le_n
  have hK : 1 ≤ K := le_trans (by norm_num) M.two_le_K
  have hρ : 0 ≤ M.rhoMax lam := M.rhoMax_nonneg lam
  have hAβ : 0 ≤ M.Abetaxi ξ β εP := M.Abetaxi_nonneg hn (by linarith) hεP
  have hCh : 0 ≤ (↑n * M.rhoMax lam * M.Abetaxi ξ β εP) :=
    mul_nonneg (mul_nonneg (by positivity) hρ) hAβ
  have hJ : 0 ≤ M.Jlam lam := M.Jlam_nonneg hn hK lam
  have hCh' : 0 ≤ Ch n (M.rhoMax lam) (M.Abetaxi ξ β εP) := by rw [Ch]; exact hCh
  have hCle : 0 ≤ Clog ξ (Ch n (M.rhoMax lam) (M.Abetaxi ξ β εP)) (M.Jlam lam) := by
    rw [Clog]; nlinarith [mul_nonneg hξ hCh', hJ]
  have hL : LdeltaStar n K T
      = Real.log (2 * ((n : ℝ) * K)) + Real.log T + 2 * Real.log (T + 1) :=
    LdeltaStar_eq n K T (by omega) (by omega) (by omega)
  have hδ : deltaStar T * (n * M.rhoMax lam * T) ≤ n * M.rhoMax lam / 4 :=
    M.deltaStar_mul_le T lam hT
  have hlogT : Real.log T ≤ Real.log (T + 1) :=
    Real.log_le_log (by positivity) (by linarith [show (1:ℝ) ≤ T by exact_mod_cast hT])
  have hE' := hE
  rw [hL] at hE'
  have hmain : M.Gamma lam + E + deltaStar T * (n * M.rhoMax lam * T)
      ≤ C0 (M.Gamma lam) (M.Dlam lam) (n * M.rhoMax lam)
          (Clog ξ (Ch n (M.rhoMax lam) (M.Abetaxi ξ β εP)) (M.Jlam lam)) (n * K)
        + Ch n (M.rhoMax lam) (M.Abetaxi ξ β εP) * h
        + Clog ξ (Ch n (M.rhoMax lam) (M.Abetaxi ξ β εP)) (M.Jlam lam) * Real.log (T + 1) := by
    simp only [C0, Clog, Ch]
    nlinarith [hE', hδ, hlogT, hCh, hJ, hρ, hξ, mul_nonneg hξ hCh,
      add_nonneg (mul_nonneg hξ hCh) hJ]
  refine le_trans hR ?_
  rw [explicitBound, Uco]
  apply le_min
  · exact min_le_left _ _
  · have h2 : M.Gamma lam + min (↑n * M.rhoMax lam * ↑T)
          (E + deltaStar T * (↑n * M.rhoMax lam * ↑T))
        ≤ M.Gamma lam + E + deltaStar T * (↑n * M.rhoMax lam * ↑T) := by
      have hmr := min_le_right (↑n * M.rhoMax lam * ↑T) (E + deltaStar T * (↑n * M.rhoMax lam * ↑T))
      linarith
    exact le_trans (le_trans (min_le_right _ _) h2) hmain

end DecayModel

end AnvBandit
