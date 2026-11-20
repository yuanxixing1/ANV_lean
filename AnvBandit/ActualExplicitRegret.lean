import AnvBandit.TrajectoryExpectation
import AnvBandit.TimeBounds
import AnvBandit.ExplicitParameters
import AnvBandit.GeneralTimeBounds

/-! Explicit and time-order bounds for the constructed actual execution. -/
noncomputable section
open scoped BigOperators
open Finset MeasureTheory
namespace AnvBandit.ActualExplicitRegret
open Execution ExecutionLaw ActualPropagation GlobalRegret TrajectoryExpectation
variable {n K : ℕ}

lemma rhoConst_le_max (M : DecayModel n K) (lam : Fin 2) (k : Fin K) :
    M.rhoConst lam k ≤ M.rhoMax lam :=
  weight_le_sup M (M.rhoConst lam) (M.rhoConst_nonneg lam)
    (by simp [DecayModel.rhoConst]) k

lemma weightedLoss_rho_le_const (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) :
    weightedLoss M p C lam (M.rho p.T lam) ≤ weightedLoss M p C lam (M.rhoConst lam) := by
  have hcmax (k : Fin K) : M.rho p.T lam k ≤ M.rhoMax lam :=
    (M.rho_le_rhoConst p.hT lam k).trans (rhoConst_le_max M lam k)
  apply integral_mono (pathCost_integrable M p C lam _ _ (M.rho_nonneg p.T lam) hcmax)
    (pathCost_integrable M p C lam _ _ (M.rhoConst_nonneg lam) (rhoConst_le_max M lam))
  intro ω
  apply Finset.sum_le_sum
  intro t ht
  exact Finset.sum_le_sum fun i hi => M.rho_le_rhoConst p.hT lam _

lemma weightedLoss_const_trivial (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) :
    weightedLoss M p C lam (M.rhoConst lam) ≤ (n : ℝ) * M.rhoMax lam * p.T := by
  have h := integral_mono (pathCost_integrable M p C lam _ _
    (M.rhoConst_nonneg lam) (rhoConst_le_max M lam))
    (integrable_const ((n : ℝ) * M.rhoMax lam * p.T))
    (pathCost_le p _ _ (rhoConst_le_max M lam))
  simpa [weightedLoss] using h

/-- The global branch for actual regret and constant weights, without supplied loss hypotheses. -/
lemma teamRegret_global_const (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) :
    teamRegret M p C lam ≤ Uco ((n : ℝ) * p.T) (M.Gamma lam)
      (n * M.rhoMax lam * p.T)
      (n * M.rhoMax lam * Pbeta (by have := p.hn; omega) C
        (holder p M.star) p.H (preparation M p) p.β + M.Clam (M.rhoConst lam) p.L 0 lam)
      (p.δ * (n * M.rhoMax lam * p.T)) := by
  have hconv := (teamRegret_conversion M p C lam).trans
    (add_le_add_right (weightedLoss_rho_le_const M p C lam) (M.Gamma lam))
  have hg := goodLoss_global_paper M p C lam (M.rhoConst lam) (M.rhoMax lam)
    (M.rhoConst_nonneg lam) (by simp [DecayModel.rhoConst]) (rhoConst_le_max M lam)
  have hf := weightedLoss_le_goodLoss_add_failure M p C lam (M.rhoConst lam) (M.rhoMax lam)
    (M.rhoConst_nonneg lam) (rhoConst_le_max M lam)
  have hmin := mul_le_mul_of_nonneg_left
    (min_le_right (p.T : ℝ) (Pbeta (by have := p.hn; omega) C (holder p M.star)
      p.H (preparation M p) p.β))
    (mul_nonneg (Nat.cast_nonneg n) (M.rhoMax_nonneg lam))
  unfold Uco
  apply le_min (teamRegret_trivial M p C lam)
  rw [add_min]
  apply le_min
  · linarith [weightedLoss_const_trivial M p C lam]
  · linarith

/-- Equations (4.4)–(4.5) for the actual algorithm and the original full joint oracle.
Every probability, exploration, reliability, and propagation premise is discharged upstream. -/
theorem actual_explicit (M : DecayModel n K) (C : ContactMatrix n) (lam : Fin 2)
    (T h : ℕ) (ξ β : ℝ) (hT : 1 ≤ T) (hh : 1 ≤ h) (hξ : 0 < ξ) (hβ : 1 < β) :
    teamRegret M (explicitParams M T h ξ β hT hh hξ hβ) C lam ≤
      explicitBound M T h ξ β (epsP C) lam := by
  let p := explicitParams M T h ξ β hT hh hξ hβ
  let E := n * M.rhoMax lam * Pbeta (by have := p.hn; omega) C
    (holder p M.star) p.H (preparation M p) p.β + M.Clam (M.rhoConst lam) p.L 0 lam
  apply M.theorem_4_1_explicit T h ξ β (epsP C) lam hT hξ.le hβ (epsP_pos C) E
  · have hL := Lstar_le_LdeltaStar (n := n) (K := K) (by have := M.two_le_n; omega)
      (by have := M.two_le_K; omega) hT
    have hp := M.Pbeta_Hxi_le C (holder p M.star) hh hξ hβ hL
    have hc := M.Clam_rhoConst_le hL lam
    have hm := mul_le_mul_of_nonneg_left hp
      (mul_nonneg (Nat.cast_nonneg n) (M.rhoMax_nonneg lam))
    simp only [E, preparation,
      show p.H = Hxi h ξ (LdeltaStar n K T) from rfl, show p.β = β from rfl,
      show p.L = LdeltaStar n K T from explicitParams_L M T h ξ β hT hh hξ hβ]
    nlinarith [hc, hm]
  · simpa [E, p, explicitParams, confidenceParams] using teamRegret_global_const M p C lam


/-- A fixed-instance propagation coefficient; it contains neither horizon nor scale. -/
def timePropagationCoefficient (M : DecayModel n K) (C : ContactMatrix n) (lam : Fin 2) (β : ℝ) : ℝ :=
  n * M.rhoMax lam * (propagationMomentCoefficient n β (epsP C) *
    max 1 ((M.Bcoef * logConfidenceCoefficient n K) ^ (β / (β - 1))))

lemma timePropagationCoefficient_nonneg (M : DecayModel n K) (C : ContactMatrix n)
    (lam : Fin 2) {β : ℝ} (hβ : 1 < β) : 0 ≤ timePropagationCoefficient M C lam β := by
  unfold timePropagationCoefficient
  apply mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (M.rhoMax_nonneg lam))
  apply mul_nonneg
  · exact propagationMomentCoefficient_nonneg (by have := M.two_le_n; omega) hβ (epsP_pos C)
  · exact le_trans (by norm_num) (le_max_left _ _)

lemma actual_general_budget (M : DecayModel n K) (C : ContactMatrix n) (lam : Fin 2)
    (T h H : ℕ) (β : ℝ) (hT : 1 ≤ T) (hh : 1 ≤ h) (hH : 1 ≤ H)
    (hdiv : h ∣ H) (hβ : 1 < β) :
    teamRegret M (confidenceParams M T h H β hT hh hH hdiv hβ) C lam ≤
      M.Gamma lam + M.Dlam lam + n * M.rhoMax lam / 4 +
      timePropagationCoefficient M C lam β *
        ((H : ℝ) + Real.log (T + 1) ^ (β / (β - 1)) / (H : ℝ) ^ (β / (β - 1) - 1)) +
      (M.Jlam lam * logConfidenceCoefficient n K) * Real.log (T + 1) := by
  let p := confidenceParams M T h H β hT hh hH hdiv hβ
  have hb := teamRegret_global_const M p C lam
  have hb' : teamRegret M p C lam ≤ M.Gamma lam +
      (n * M.rhoMax lam * Pbeta (by have := p.hn; omega) C (holder p M.star)
        p.H (preparation M p) p.β + M.Clam (M.rhoConst lam) p.L 0 lam) +
      p.δ * (n * M.rhoMax lam * p.T) := by
    exact hb.trans ((min_le_right _ _).trans (by
      have hm := min_le_right (n * M.rhoMax lam * p.T)
        ((n * M.rhoMax lam * Pbeta (by have := p.hn; omega) C (holder p M.star)
          p.H (preparation M p) p.β + M.Clam (M.rhoConst lam) p.L 0 lam) +
          p.δ * (n * M.rhoMax lam * p.T))
      linarith))
  have hn : 1 ≤ n := by have := M.two_le_n; omega
  have hK : 1 ≤ K := by have := M.two_le_K; omega
  have hL := Lstar_le_LdeltaStar hn hK hT
  have hp := M.Pbeta_general_horizon C (holder p M.star) hT hH hβ
  have hp' := mul_le_mul_of_nonneg_left hp
    (mul_nonneg (Nat.cast_nonneg n) (M.rhoMax_nonneg lam))
  have hc := M.Clam_rhoConst_le hL lam
  have hc' := mul_le_mul_of_nonneg_left (LdeltaStar_le_logCoefficient hn hK hT)
    (M.Jlam_nonneg hn hK lam)
  have hd := M.deltaStar_mul_le T lam hT
  change teamRegret M p C lam ≤ _
  change teamRegret M p C lam ≤ M.Gamma lam +
    (n * M.rhoMax lam * Pbeta (by have := M.two_le_n; omega) C (holder p M.star)
      H (lastShortPhase H β (M.Bschedule p.L)) β + M.Clam (M.rhoConst lam) p.L 0 lam) +
    deltaStar T * (n * M.rhoMax lam * T) at hb'
  rw [show p.L = LdeltaStar n K T from confidenceParams_L M T h H β hT hh hH hdiv hβ] at hb'
  unfold timePropagationCoefficient
  nlinarith [hb', hp', hc, hc', hd]

/-- Equation (4.6) for every original legal schedule. The constant is chosen before
`T,h,H` and the divisibility proof; no restriction between `T` and `H` occurs. -/
theorem actual_time_order (M : DecayModel n K) (C : ContactMatrix n) (lam : Fin 2)
    (β : ℝ) (hβ : 1 < β) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ T h H : ℕ, ∀ (hT : 1 ≤ T) (hh : 1 ≤ h) (hH : 1 ≤ H)
      (hdiv : h ∣ H),
      teamRegret M (confidenceParams M T h H β hT hh hH hdiv hβ) C lam ≤
      A * ((H : ℝ) + Real.log (T + 1) ^ (β / (β - 1)) / (H : ℝ) ^ (β / (β - 1) - 1) +
        Real.log (T + 1) + 1) := by
  let a := |M.Gamma lam| + |M.Dlam lam| + n * M.rhoMax lam / 4
  let b := timePropagationCoefficient M C lam β
  let c := M.Jlam lam * logConfidenceCoefficient n K
  have hn : 1 ≤ n := by have := M.two_le_n; omega
  have hK : 1 ≤ K := by have := M.two_le_K; omega
  have ha : 0 ≤ a := by
    have hρ := M.rhoMax_nonneg lam
    dsimp [a]
    positivity
  have hb : 0 ≤ b := timePropagationCoefficient_nonneg M C lam hβ
  have hc : 0 ≤ c := mul_nonneg (M.Jlam_nonneg hn hK lam) (logConfidenceCoefficient_nonneg hn hK)
  refine ⟨a + b + c, by positivity, fun T h H hT hh hH hdiv => ?_⟩
  have hbudget := actual_general_budget M C lam T h H β hT hh hH hdiv hβ
  have hlog : 0 ≤ Real.log (T + 1) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ T + 1 by omega))
  have hq : 0 ≤ (H : ℝ) + Real.log (T + 1) ^ (β / (β - 1)) / (H : ℝ) ^ (β / (β - 1) - 1) := by positivity
  have h0 : M.Gamma lam + M.Dlam lam + n * M.rhoMax lam / 4 ≤ a :=
    by dsimp [a]; linarith [le_abs_self (M.Gamma lam), le_abs_self (M.Dlam lam)]
  change _ ≤ (a + b + c) * _
  change _ ≤ M.Gamma lam + M.Dlam lam + n * M.rhoMax lam / 4 + b * _ + c * _ at hbudget
  nlinarith [mul_nonneg ha hq, mul_nonneg ha hlog, mul_nonneg hb hlog,
    mul_nonneg hc hq]

end AnvBandit.ActualExplicitRegret
