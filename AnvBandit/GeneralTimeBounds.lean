import AnvBandit.ActualExplicit

/-! Uniform analytic scheduling bounds. The scale `H` is any positive real:
no comparison of the horizon with the public scale is imposed. -/
noncomputable section
namespace AnvBandit

def phaseMomentCoefficient (β : ℝ) : ℝ :=
  2 ^ (β - 1) * (2 ^ (β / (β - 1) - 1) * (1 + 2 ^ (β / (β - 1))) + 1)

lemma phaseMomentCoefficient_nonneg (β : ℝ) : 0 ≤ phaseMomentCoefficient β := by
  unfold phaseMomentCoefficient
  positivity

/-- Rounded last-short-phase moment with constants uniform over every `H>0`. -/
lemma lastShortPhase_rpow_le {H B β : ℝ} (hH : 0 < H) (hB : 0 ≤ B) (hβ : 1 < β) :
    (lastShortPhase H β B : ℝ) ^ β ≤
      phaseMomentCoefficient β * (1 + (B / H) ^ (β / (β - 1))) := by
  let γ := β / (β - 1)
  let u := ((B / H + 2) / β) ^ (1 / (β - 1))
  have hb : 0 ≤ B / H := div_nonneg hB hH.le
  have hβ0 : 0 < β := by linarith
  have hγ : 1 ≤ γ := by dsimp [γ]; apply (le_div_iff₀ (by linarith)).mpr; linarith
  have hbase : 0 ≤ (B / H + 2) / β := by positivity
  have hu : 0 ≤ u := Real.rpow_nonneg hbase _
  have hr : (lastShortPhase H β B : ℝ) ≤ u + 1 := by
    have hrnat : lastShortPhase H β B ≤ ⌈u⌉₊ := by
      rw [← rH_eq_last_short_phase hH hβ hB (show u = _ from rfl)]
      exact (lemma_B_3 hH hβ hB rfl).1
    exact (Nat.cast_le.mpr hrnat).trans (Nat.ceil_lt_add_one hu).le
  have hupow : u ^ β ≤ (B / H + 2) ^ γ := by
    dsimp [u]
    rw [← Real.rpow_mul hbase]
    have he : 1 / (β - 1) * β = γ := by dsimp [γ]; ring
    rw [he]
    exact Real.rpow_le_rpow hbase (div_le_self (by positivity) hβ.le) (by linarith)
  have hsum := rpow_add_le_mul_rpow_add_rpow_real hb (by norm_num : (0 : ℝ) ≤ 2) hγ
  have hceilpow := (Real.rpow_le_rpow (Nat.cast_nonneg _) hr hβ0.le).trans
    (rpow_add_le_mul_rpow_add_rpow_real hu (by norm_num : (0 : ℝ) ≤ 1) hβ.le)
  simp only [Real.one_rpow] at hceilpow
  have htwo : (0 : ℝ) ≤ 2 ^ (β - 1) := Real.rpow_nonneg (by norm_num) _
  have htwoγ : (0 : ℝ) ≤ 2 ^ (γ - 1) := Real.rpow_nonneg (by norm_num) _
  have hx : 0 ≤ (B / H) ^ γ := Real.rpow_nonneg hb _
  have htwopow : (0 : ℝ) ≤ 2 ^ γ := Real.rpow_nonneg (by norm_num) _
  have h1 := mul_le_mul_of_nonneg_left hupow htwo
  have h2 := mul_le_mul_of_nonneg_left hsum htwo
  change _ ≤ 2 ^ (β - 1) * (2 ^ (γ - 1) * (1 + 2 ^ γ) + 1) * (1 + (B / H) ^ γ)
  nlinarith [mul_nonneg (mul_nonneg htwo htwoγ) (mul_nonneg htwopow hx), mul_nonneg htwo hx]

lemma scale_rpow_ratio {H B γ : ℝ} (hH : 0 < H) (hB : 0 ≤ B) :
    H * (B / H) ^ γ = B ^ γ / H ^ (γ - 1) := by
  rw [Real.div_rpow hB hH.le, Real.rpow_sub_one hH.ne']
  field_simp [hH.ne', (Real.rpow_pos_of_pos hH γ).ne']

def propagationMomentCoefficient (n : ℕ) (β εP : ℝ) : ℝ :=
  1 + 2 ^ (β - 1) * (phaseMomentCoefficient β +
    Real.exp 1 * Real.Gamma (β + 1) * (((n : ℝ) - 1) / εP) ^ β)

/-- The full propagation waiting moment has the original all-positive-scale order. -/
lemma Pbeta_general_scale {n : ℕ} (hn : 2 ≤ n) (C : ContactMatrix n) (i0 : Fin n)
    {H B β : ℝ} (hH : 0 < H) (hB : 0 ≤ B) (hβ : 1 < β) :
    Pbeta (by omega) C i0 H (lastShortPhase H β B) β ≤
        propagationMomentCoefficient n β (epsP C) * (H + B ^ (β / (β - 1)) / H ^ (β / (β - 1) - 1)) := by
  let q := phaseMomentCoefficient β
  let m := Real.exp 1 * Real.Gamma (β + 1) * (((n : ℝ) - 1) / epsP C) ^ β
  let a : ℝ := 2 ^ (β - 1)
  have hq : 0 ≤ q := phaseMomentCoefficient_nonneg β
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hm : 0 ≤ m := by
    dsimp [m]
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.Gamma_pos_of_pos (by linarith)).le)
      (Real.rpow_nonneg (div_nonneg (by linarith)
        (epsP_nonneg C)) _)
  have ha : 0 ≤ a := Real.rpow_nonneg (by norm_num) _
  have hp := Pbeta_le hn C (ReachData.ofIrreducible C.irreducible i0) hH.le
    (Nat.cast_nonneg (lastShortPhase H β B)) hβ.le
  have hr := lastShortPhase_rpow_le hH hB hβ
  have hx : 0 ≤ (B / H) ^ (β / (β - 1)) := Real.rpow_nonneg (div_nonneg hB hH.le) _
  have hratio := scale_rpow_ratio (γ := β / (β - 1)) hH hB
  change _ ≤ (1 + a * (q + m)) * _
  change _ ≤ H * (1 + a * ((lastShortPhase H β B : ℝ) ^ β + m)) at hp
  have hinner : 1 + a * ((lastShortPhase H β B : ℝ) ^ β + m) ≤
      (1 + a * (q + m)) * (1 + (B / H) ^ (β / (β - 1))) := by
    change (lastShortPhase H β B : ℝ) ^ β ≤ q * (1 + _) at hr
    nlinarith [mul_le_mul_of_nonneg_left hr ha, mul_nonneg (mul_nonneg ha hm) hx]
  have hscaled := mul_le_mul_of_nonneg_left hinner hH.le
  refine (hp.trans hscaled).trans_eq ?_
  rw [← hratio]
  ring


def logConfidenceCoefficient (n K : ℕ) : ℝ := Real.log (2 * ((n : ℝ) * K)) / Real.log 2 + 3

lemma logConfidenceCoefficient_nonneg {n K : ℕ} (hn : 1 ≤ n) (hK : 1 ≤ K) :
    0 ≤ logConfidenceCoefficient n K := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hk' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have harg : (1 : ℝ) ≤ 2 * ((n : ℝ) * K) := by nlinarith
  unfold logConfidenceCoefficient
  exact add_nonneg (div_nonneg (Real.log_nonneg harg) (Real.log_pos (by norm_num)).le) (by norm_num)

lemma LdeltaStar_le_logCoefficient {n K T : ℕ} (hn : 1 ≤ n) (hK : 1 ≤ K) (hT : 1 ≤ T) :
    LdeltaStar n K T ≤ logConfidenceCoefficient n K * Real.log (T + 1) := by
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2 : Real.log 2 ≤ Real.log (T + 1) := Real.log_le_log (by norm_num)
    (by exact_mod_cast (show 2 ≤ T + 1 by omega))
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hk' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have harg : (1 : ℝ) ≤ 2 * ((n : ℝ) * K) := by nlinarith
  have hc : 0 ≤ Real.log (2 * ((n : ℝ) * K)) := Real.log_nonneg harg
  have hconstant : Real.log (2 * ((n : ℝ) * K)) ≤
      (Real.log (2 * ((n : ℝ) * K)) / Real.log 2) * Real.log (T + 1) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hp]
    exact mul_le_mul_of_nonneg_left hlog2 hc
  have ht : Real.log (T : ℝ) ≤ Real.log ((T : ℝ) + 1) :=
    Real.log_le_log (by exact_mod_cast (show 0 < T by omega)) (by linarith)
  rw [LdeltaStar_eq n K T (by omega) (by omega) (by omega)]
  unfold logConfidenceCoefficient
  nlinarith

lemma propagationMomentCoefficient_nonneg {n : ℕ} {β εP : ℝ}
    (hn : 1 ≤ n) (hβ : 1 < β) (hε : 0 < εP) :
    0 ≤ propagationMomentCoefficient n β εP := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold propagationMomentCoefficient
  have hg := (Real.Gamma_pos_of_pos (by linarith : 0 < β + 1)).le
  have hq := phaseMomentCoefficient_nonneg β
  positivity

namespace DecayModel
variable {n K : ℕ} (M : DecayModel n K)

/-- Uniform-in-horizon and uniform-in-scale bound, with the coefficient written explicitly.
In particular the quantified domain includes `H<T`. -/
lemma Pbeta_general_horizon (C : ContactMatrix n) (i0 : Fin n)
    {T H : ℕ} {β : ℝ} (hT : 1 ≤ T) (hH : 1 ≤ H) (hβ : 1 < β) :
    Pbeta (by have := M.two_le_n; omega) C i0 H
      (lastShortPhase H β (M.Bschedule (LdeltaStar n K T))) β ≤
      (propagationMomentCoefficient n β (epsP C) *
        max 1 ((M.Bcoef * logConfidenceCoefficient n K) ^ (β / (β - 1)))) *
        ((H : ℝ) + Real.log (T + 1) ^ (β / (β - 1)) / (H : ℝ) ^ (β / (β - 1) - 1)) := by
  have hn : 1 ≤ n := by have := M.two_le_n; omega
  have hK : 1 ≤ K := by have := M.two_le_K; omega
  have hHp : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hL := Lstar_le_LdeltaStar hn hK hT
  have hD : 0 ≤ M.Bcoef * logConfidenceCoefficient n K :=
    mul_nonneg M.Bcoef_nonneg (logConfidenceCoefficient_nonneg hn hK)
  have hlog : 0 ≤ Real.log (T + 1) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ T + 1 by omega))
  have hγ : 0 ≤ β / (β - 1) := div_nonneg (by linarith) (by linarith)
  have hB : (M.Bschedule (LdeltaStar n K T) : ℝ) ≤
      (M.Bcoef * logConfidenceCoefficient n K) * Real.log (T + 1) := by
    apply (M.Bschedule_le_Bcoef_mul hL).trans
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_left (LdeltaStar_le_logCoefficient hn hK hT) M.Bcoef_nonneg)
  have hp := Pbeta_general_scale M.two_le_n C i0 hHp
    (Nat.cast_nonneg (M.Bschedule (LdeltaStar n K T))) hβ
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg _) hB hγ
  rw [Real.mul_rpow hD hlog] at hpow
  have hden : 0 < (H : ℝ) ^ (β / (β - 1) - 1) := Real.rpow_pos_of_pos hHp _
  have hratio := div_le_div_of_nonneg_right hpow hden.le
  have hQ : 0 ≤ Real.log (T + 1) ^ (β / (β - 1)) / (H : ℝ) ^ (β / (β - 1) - 1) := by positivity
  have hmax1 := le_max_left (1 : ℝ) ((M.Bcoef * logConfidenceCoefficient n K) ^ (β / (β - 1)))
  have hmaxD := le_max_right (1 : ℝ) ((M.Bcoef * logConfidenceCoefficient n K) ^ (β / (β - 1)))
  have hinner : (H : ℝ) + (M.Bschedule (LdeltaStar n K T) : ℝ) ^ (β / (β - 1)) /
      (H : ℝ) ^ (β / (β - 1) - 1) ≤
      max 1 ((M.Bcoef * logConfidenceCoefficient n K) ^ (β / (β - 1))) *
      ((H : ℝ) + Real.log (T + 1) ^ (β / (β - 1)) / (H : ℝ) ^ (β / (β - 1) - 1)) := by
    rw [mul_div_assoc] at hratio
    nlinarith [mul_le_mul_of_nonneg_right hmax1 hHp.le, mul_le_mul_of_nonneg_right hmaxD hQ]
  apply hp.trans
  simpa [mul_assoc] using (mul_le_mul_of_nonneg_left hinner
    (propagationMomentCoefficient_nonneg hn hβ (epsP_pos C)))

end DecayModel
end AnvBandit
