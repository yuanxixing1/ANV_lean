import AnvBandit.NodeCost

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-!
# The schedule-potential telescope (Lemma C.3, equations (C.3)-(C.5), (C.10), (C.13))

The rounding of the phase lengths `d_ℓ` may decrease, so the paper introduces `ω_ℓ = [d_ℓ − d_{ℓ−1}]₊`
(equation (C.3)).  The telescoping bound (C.10)
`E ∑_ℓ d_ℓ |V \ Z_ℓ| ≤ ∑_ℓ ω_ℓ u_ℓ + 2 M_1 F_λ(c^∘)`
rests on the Abel-summation identity `∑_ℓ d_ℓ (u_ℓ − u_{ℓ+1}) ≤ ∑_ℓ ω_ℓ u_ℓ`, proved here as
`abel_bound`.  Its combination with the potential bound `∑_ℓ ω_ℓ u_ℓ ≤ K_β(H)` (C.13) yields (C.5).
-/

noncomputable section
open scoped BigOperators
open Finset

namespace AnvBandit

variable {n K : ℕ}

/-- The Abel-summation tuning-fork on the phase lengths (equation (C.10)): for nonnegative `d` and
`u` with `d 0 = 0`, the decreasing differences of `u` weighted by `d` are dominated by the positive
increments `ω_ℓ = [d_ℓ − d_{ℓ−1}]₊` of `d` weighted by `u`. -/
lemma abel_bound {d u : ℕ → ℝ} (hd0 : d 0 = 0) (hd : ∀ ℓ, 0 ≤ d ℓ) (hu : ∀ ℓ, 0 ≤ u ℓ)
    (Ph : ℕ) :
    ∑ ℓ ∈ Finset.range Ph, d (ℓ + 1) * (u (ℓ + 1) - u (ℓ + 2))
      ≤ ∑ ℓ ∈ Finset.range Ph, posPart (d (ℓ + 1) - d ℓ) * u (ℓ + 1) := by
  have hid : ∀ Ph, ∑ ℓ ∈ Finset.range Ph, d (ℓ + 1) * (u (ℓ + 1) - u (ℓ + 2))
      = (∑ ℓ ∈ Finset.range Ph, (d (ℓ + 1) - d ℓ) * u (ℓ + 1)) - d Ph * u (Ph + 1) := by
    intro Ph
    induction Ph with
    | zero => simp [hd0]
    | succ Ph ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      ring
  rw [hid Ph]
  have hdrop : 0 ≤ d Ph * u (Ph + 1) := mul_nonneg (hd Ph) (hu (Ph + 1))
  have hpos : ∑ ℓ ∈ Finset.range Ph, (d (ℓ + 1) - d ℓ) * u (ℓ + 1)
      ≤ ∑ ℓ ∈ Finset.range Ph, posPart (d (ℓ + 1) - d ℓ) * u (ℓ + 1) :=
    Finset.sum_le_sum fun ℓ _ => mul_le_mul_of_nonneg_right (le_max_left _ _) (hu (ℓ + 1))
  linarith [hdrop, hpos]

/-! ### (C.4) summability of the schedule-weighted propagation series `K_β(H)` -/

/-- A polynomially weighted geometric series (shifted by `1`) is summable. -/
lemma summable_shifted_pow_geometric {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (k : ℕ) :
    Summable (fun ℓ : ℕ => ((ℓ + 1 : ℕ) : ℝ) ^ k * ρ ^ ℓ) := by
  have h : Summable (fun n : ℕ => (n : ℝ) ^ k * ρ ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one k (by rw [Real.norm_eq_abs, abs_of_pos hρ0]; exact hρ1)
  have hcomp : Summable (fun ℓ : ℕ => ((ℓ + 1 : ℕ) : ℝ) ^ k * ρ ^ (ℓ + 1)) :=
    h.comp_injective (fun a b hab => by simpa using hab)
  have hmul := hcomp.mul_left (1 / ρ)
  have heq : (fun ℓ : ℕ => (1 / ρ) * (((ℓ + 1 : ℕ) : ℝ) ^ k * ρ ^ (ℓ + 1)))
      = fun ℓ : ℕ => ((ℓ + 1 : ℕ) : ℝ) ^ k * ρ ^ ℓ := by
    funext ℓ
    rw [pow_succ]
    field_simp
  rwa [heq] at hmul

/-- **(C.4)**, series form: `K_β(H) = ∑_{ℓ≥1} ω_ℓ v_{(ℓ−r_H−1)_+}`. -/
def Kbeta (w v : ℕ → ℝ) (rH : ℕ) : ℝ := ∑' ℓ, w (ℓ + 1) * v (ℓ - rH)

/-- **(C.4)**, finiteness: if `ω_ℓ ≤ A ℓ^k` and `v_j ≤ C ρ^j` with `0 ≤ ρ < 1`, the schedule-weighted
propagation series `K_β(H)` is summable (Appendix C.2 tail bound `v_j ≤ (ne/(1−e^{−ζ_P})) e^{−ζ_P j}`). -/
theorem Kbeta_summable {w v : ℕ → ℝ} {A C ρ : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hw0 : ∀ ℓ, 0 ≤ w ℓ) (hv0 : ∀ j, 0 ≤ v j)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (k : ℕ)
    (hw : ∀ ℓ, w ℓ ≤ A * (ℓ : ℝ) ^ k) (hv : ∀ j, v j ≤ C * ρ ^ j) (rH : ℕ) :
    Summable (fun ℓ => w (ℓ + 1) * v (ℓ - rH)) := by
  have hshift : ∀ ℓ, v (ℓ - rH) ≤ C * ((1 / ρ) ^ rH * ρ ^ ℓ) := by
    intro ℓ
    have hmax : ℓ - rH = max ℓ rH - rH := by omega
    have hexp : (ℓ - rH) + rH = max ℓ rH := by
      rw [hmax, Nat.sub_add_cancel (le_max_right ℓ rH)]
    have hpow : ρ ^ (max ℓ rH) ≤ ρ ^ ℓ := pow_le_pow_of_le_one hρ0.le hρ1.le (le_max_left ℓ rH)
    have hsplit : ρ ^ (max ℓ rH) = ρ ^ (ℓ - rH) * ρ ^ rH := by rw [← pow_add, hexp]
    rw [hsplit] at hpow
    have hpr : 0 < ρ ^ rH := pow_pos hρ0 rH
    have hge : ρ ^ (ℓ - rH) ≤ ρ ^ ℓ / ρ ^ rH := (le_div_iff₀ hpr).mpr hpow
    have hge' : ρ ^ (ℓ - rH) ≤ (1 / ρ) ^ rH * ρ ^ ℓ := by
      have hconv : (1 / ρ) ^ rH * ρ ^ ℓ = ρ ^ ℓ * (ρ ^ rH)⁻¹ := by
        rw [one_div, inv_pow, mul_comm]
      rw [hconv]; exact hge
    calc v (ℓ - rH) ≤ C * ρ ^ (ℓ - rH) := hv _
      _ ≤ C * ((1 / ρ) ^ rH * ρ ^ ℓ) := mul_le_mul_of_nonneg_left hge' hC
  have hdom : ∀ ℓ, w (ℓ + 1) * v (ℓ - rH)
      ≤ (A * C * (1 / ρ) ^ rH) * (((ℓ + 1 : ℕ) : ℝ) ^ k * ρ ^ ℓ) := by
    intro ℓ
    have h1 : w (ℓ + 1) ≤ A * ((ℓ + 1 : ℕ) : ℝ) ^ k := hw (ℓ + 1)
    have h2 := hshift ℓ
    have hnn : 0 ≤ ((ℓ + 1 : ℕ) : ℝ) ^ k := by positivity
    calc w (ℓ + 1) * v (ℓ - rH)
        ≤ (A * ((ℓ + 1 : ℕ) : ℝ) ^ k) * (C * ((1 / ρ) ^ rH * ρ ^ ℓ)) :=
          mul_le_mul h1 h2 (hv0 _) (mul_nonneg hA hnn)
      _ = (A * C * (1 / ρ) ^ rH) * (((ℓ + 1 : ℕ) : ℝ) ^ k * ρ ^ ℓ) := by ring
  have hnn : ∀ ℓ, 0 ≤ w (ℓ + 1) * v (ℓ - rH) := fun ℓ => mul_nonneg (hw0 _) (hv0 _)
  have hsum := (summable_shifted_pow_geometric hρ0 hρ1 k).mul_left (A * C * (1 / ρ) ^ rH)
  exact Summable.of_nonneg_of_le hnn hdom hsum

/-- **(C.5)/(C.13).**  Combining the potential telescope `abel_bound` (C.10) with the potential bound
`∑_ℓ ω_ℓ u_ℓ ≤ K_β(H)`, the weighted exploration cost is at most
`F_λ(c) + c_max (2 M_1 F_λ(c^∘) + K_β(H))`, where `c^∘ = 1{k ≠ ⋆}`. -/
theorem lemma_C_3 {n K : ℕ} (M : DecayModel n K) (c : Fin K → ℝ) (L : ℝ) (lam : Fin 2)
    (Ph : ℕ) (d u : ℕ → ℝ) (M1 Kbeta Eloss : ℝ)
    (hc : ∀ k, 0 ≤ c k) (hM1 : 0 ≤ M1)
    (hd0 : d 0 = 0) (hd : ∀ ℓ, 0 ≤ d ℓ) (hu : ∀ ℓ, 0 ≤ u ℓ)
    (hpcost : Eloss ≤ M.Flam c L lam + M.supOthers c
      * (2 * M1 * M.Flam (fun k => if k = M.star then 0 else 1) L lam
        + ∑ ℓ ∈ Finset.range Ph, d (ℓ + 1) * (u (ℓ + 1) - u (ℓ + 2))))
    (hpot : (∑ ℓ ∈ Finset.range Ph, posPart (d (ℓ + 1) - d ℓ) * u (ℓ + 1)) ≤ Kbeta) :
    Eloss ≤ M.Flam c L lam
      + M.supOthers c * (2 * M1 * M.Flam (fun k => if k = M.star then 0 else 1) L lam + Kbeta) := by
  have hcmax : 0 ≤ M.supOthers c := by
    obtain ⟨k, hk⟩ := M.others_nonempty
    exact le_trans (hc k) (M.le_supOthers hk)
  have htel := abel_bound hd0 hd hu Ph
  have hsum : (∑ ℓ ∈ Finset.range Ph, d (ℓ + 1) * (u (ℓ + 1) - u (ℓ + 2)))
      ≤ Kbeta := le_trans htel hpot
  have hfin : M.supOthers c * (2 * M1 * M.Flam (fun k => if k = M.star then 0 else 1) L lam
        + ∑ ℓ ∈ Finset.range Ph, d (ℓ + 1) * (u (ℓ + 1) - u (ℓ + 2)))
      ≤ M.supOthers c * (2 * M1 * M.Flam (fun k => if k = M.star then 0 else 1) L lam + Kbeta) :=
    mul_le_mul_of_nonneg_left (add_le_add le_rfl hsum) hcmax
  linarith [hpcost, hfin]

end AnvBandit
