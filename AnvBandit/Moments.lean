import AnvBandit.Propagation

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-!
# Propagation moments and arrival quantities (Appendix B.2)

Building on the product probability space `procMeasure` of `AnvBandit.Propagation`, this file
formalises the propagation moments of equations (B.4)-(B.7):

* `sigma i` is the capped informed-time `σ_i` of node `i` (equal to the first informed step on the
  almost-sure completion event, and forced to be `≤ τ` so that all inequalities hold everywhere);
* `M1 = ∑_i E σ_i` is the summed waiting time and `DP = n μ_1 - M1 = ∑_i E(τ - σ_i)` the residual
  propagation delay, with `μ_1 = E τ`;
* `S = H⌈(r_H + τ)^β⌉` and `A_i = H⌈(r_H + σ_i)^β⌉` are the scheduling images of the propagation,
  with `P_β(H) = E S` and `A_β(H,T) = ∑_i E min{T, A_i}`.

The bounds are proved from Lemma B.4 (`integral_rpow_tau_le`):
`M1 ≤ n E τ ≤ n e (n-1)/ε_P`, `0 ≤ DP ≤ n e (n-1)/ε_P`, and (B.7)
`P_β(H) ≤ H (1 + 2^{β-1} (r_H^β + E τ^β))`.
-/

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Filter Finset

namespace AnvBandit

variable {n : ℕ}

/-! ## 1. The capped propagation delay `σ_i` -/

/-- Capped propagation delay of node `i` from `{i0}`.  On the almost-sure completion event
`{Inform (unblock hd ω) {i0} (tau hd ω i0) = univ}` this is the paper's `σ_i` (the first step at
which `i` is informed); the `min` with `τ` makes the inequality `σ_i ≤ τ` hold everywhere. -/
def sigma (hd : 0 < n - 1) (ω : ℕ → Fin (n - 1) → Fin n → Fin n) (i0 i : Fin n) : ℕ :=
  min (sigmaStep (unblock hd ω) i0 i) (tau hd ω i0)

lemma sigma_le_tau {hd : 0 < n - 1} (ω : ℕ → Fin (n - 1) → Fin n → Fin n) (i0 i : Fin n) :
    sigma hd ω i0 i ≤ tau hd ω i0 := min_le_right _ _

/-- The source node is informed at step `0`. -/
lemma sigma_self {hd : 0 < n - 1} (ω : ℕ → Fin (n - 1) → Fin n → Fin n) (i0 : Fin n) :
    sigma hd ω i0 i0 = 0 := by
  have h0 : sigmaStep (unblock hd ω) i0 i0 = 0 := by
    refine le_antisymm (Nat.sInf_le ?_) (Nat.zero_le _)
    simp [Inform_zero]
  simp [sigma, h0]

/-- Real-valued capped propagation delay. -/
def sigmaR {n : ℕ} (hd : 0 < n - 1) (ω : ℕ → Fin (n - 1) → Fin n → Fin n) (i0 i : Fin n) : ℝ :=
  (sigma hd ω i0 i : ℝ)

/-- Real-valued completion time `τ`. -/
def tauR {n : ℕ} (hd : 0 < n - 1) (ω : ℕ → Fin (n - 1) → Fin n → Fin n) (i0 : Fin n) : ℝ :=
  (tau hd ω i0 : ℝ)

lemma sigmaR_le_tauR {hd : 0 < n - 1} (ω : ℕ → Fin (n - 1) → Fin n → Fin n) (i0 i : Fin n) :
    sigmaR hd ω i0 i ≤ tauR hd ω i0 := by
  unfold sigmaR tauR
  exact_mod_cast sigma_le_tau ω i0 i

lemma sigmaR_nonneg (hd : 0 < n - 1) (ω) (i0 i : Fin n) : 0 ≤ sigmaR hd ω i0 i :=
  Nat.cast_nonneg _

lemma tauR_nonneg (hd : 0 < n - 1) (ω) (i0 : Fin n) : 0 ≤ tauR hd ω i0 := Nat.cast_nonneg _

/-! ## 2. Generalised convexity `(a+b)^β ≤ 2^{β-1}(a^β + b^β)` -/

theorem rpow_add_le_mul_rpow_add_rpow_real {a b β : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hβ : 1 ≤ β) :
    (a + b) ^ β ≤ 2 ^ (β - 1) * (a ^ β + b ^ β) := by
  lift a to NNReal using ha
  lift b to NNReal using hb
  have h := NNReal.rpow_add_le_mul_rpow_add_rpow a b hβ
  have h1 : ((a + b : NNReal) : ℝ) = ((a : ℝ) + (b : ℝ)) := by push_cast; rfl
  calc ((a:ℝ) + (b:ℝ)) ^ β = (((a + b : NNReal) : ℝ)) ^ β := by rw [h1]
    _ = (((a + b : NNReal) ^ β : NNReal) : ℝ) := by rw [NNReal.coe_rpow]
    _ ≤ (((2 : NNReal) ^ (β - 1) * (a ^ β + b ^ β) : NNReal) : ℝ) := by exact_mod_cast h
    _ = 2 ^ (β - 1) * ((a:ℝ) ^ β + (b:ℝ) ^ β) := by push_cast; norm_num

lemma Gamma_two_alt : Real.Gamma ((1:ℝ) + 1) = 1 := by norm_num [Real.Gamma_two]

/-! ## 3. The moments `μ_1, M_1, D_P` (equation (B.4)) -/

/-- `E τ^β`, the `β`-th moment of the completion time. -/
def EtauPow {n : ℕ} (hd : 0 < n - 1) (C : ContactMatrix n) (i0 : Fin n) (β : ℝ) : ℝ :=
  (∫⁻ ω, ENNReal.ofReal ((tauR hd ω i0) ^ β) ∂procMeasure C (n - 1)).toReal

/-- `μ_1 = E τ`. -/
def mu1 {n : ℕ} (hd : 0 < n - 1) (hn : 2 ≤ n) (C : ContactMatrix n) (i0 : Fin n) : ℝ :=
  EtauPow hd C i0 1

/-- `M_1 = ∑_i E σ_i`. -/
def M1 {n : ℕ} (hd : 0 < n - 1) (C : ContactMatrix n) (i0 : Fin n) : ℝ :=
  ∑ i : Fin n, (∫⁻ ω, ENNReal.ofReal (sigmaR hd ω i0 i) ∂procMeasure C (n - 1)).toReal

/-- `D_P = n μ_1 - M_1 = ∑_i E(τ - σ_i)`. -/
def DP {n : ℕ} (hd : 0 < n - 1) (hn : 2 ≤ n) (C : ContactMatrix n) (i0 : Fin n) : ℝ :=
  n * mu1 hd hn C i0 - M1 hd C i0

/-- Lemma B.4 in the form used below: `E τ^β ≤ e Γ(β+1) ((n-1)/ε_P)^β`. -/
theorem EtauPow_le {n : ℕ} (hn : 2 ≤ n) (C : ContactMatrix n) {i0 : Fin n}
    (R : ReachData C.P i0) {β : ℝ} (hβ : 1 ≤ β) :
    EtauPow (by omega : 0 < n - 1) C i0 β ≤
      Real.exp 1 * Real.Gamma (β + 1) * (((n : ℝ) - 1) / epsP C) ^ β := by
  have hG : 0 < Real.Gamma (β + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hbase : 0 ≤ ((n : ℝ) - 1) / epsP C :=
    div_nonneg (by have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
                   linarith)
      (epsP_nonneg C)
  have hB : 0 ≤ Real.exp 1 * Real.Gamma (β + 1) * (((n : ℝ) - 1) / epsP C) ^ β :=
    mul_nonneg (mul_nonneg (Real.exp_pos 1).le hG.le) (Real.rpow_nonneg hbase β)
  have h := integral_rpow_tau_le hn C R hβ
  unfold EtauPow
  exact ENNReal.toReal_le_of_le_ofReal hB h

lemma EtauPow_nonneg (hd : 0 < n - 1) (C : ContactMatrix n) (i0 : Fin n) (β : ℝ) :
    0 ≤ EtauPow hd C i0 β := ENNReal.toReal_nonneg

/-- `μ_1 = E τ ≤ e (n-1)/ε_P`. -/
theorem mu1_le {n : ℕ} (hn : 2 ≤ n) (C : ContactMatrix n) {i0 : Fin n}
    (R : ReachData C.P i0) :
    mu1 (by omega : 0 < n - 1) hn C i0 ≤ Real.exp 1 * (((n : ℝ) - 1) / epsP C) := by
  unfold mu1
  have h := EtauPow_le hn C R (β := 1) le_rfl
  rwa [Real.rpow_one, Gamma_two_alt, mul_one] at h

/-! ## 4. Bounds on `M_1` and `D_P` -/

/-- `E σ_i ≤ E τ`. -/
theorem Esigma_le_Etau {n : ℕ} (hn : 2 ≤ n) (C : ContactMatrix n) {i0 : Fin n}
    (R : ReachData C.P i0) (i : Fin n) :
    (∫⁻ ω, ENNReal.ofReal (sigmaR (by omega : 0 < n - 1) ω i0 i) ∂procMeasure C (n - 1)).toReal ≤
      EtauPow (by omega : 0 < n - 1) C i0 1 := by
  have hd : 0 < n - 1 := by omega
  have hmono : ∫⁻ ω, ENNReal.ofReal (sigmaR hd ω i0 i) ∂procMeasure C (n - 1) ≤
      ∫⁻ ω, ENNReal.ofReal ((tauR hd ω i0) ^ (1:ℝ)) ∂procMeasure C (n - 1) := by
    refine lintegral_mono (fun ω => ?_)
    rw [Real.rpow_one]
    exact ENNReal.ofReal_le_ofReal (sigmaR_le_tauR ω i0 i)
  have htop : ∫⁻ ω, ENNReal.ofReal ((tauR hd ω i0) ^ (1:ℝ)) ∂procMeasure C (n - 1) ≠ ⊤ :=
    (lt_of_le_of_lt (integral_rpow_tau_le hn C R (β := 1) le_rfl) ENNReal.ofReal_lt_top).ne
  rw [EtauPow]
  exact ENNReal.toReal_mono htop hmono

/-- `M_1 ≤ n μ_1`. -/
theorem M1_le_n_mu1 {n : ℕ} (hn : 2 ≤ n) (C : ContactMatrix n) {i0 : Fin n}
    (R : ReachData C.P i0) :
    M1 (by omega : 0 < n - 1) C i0 ≤ (n : ℝ) * mu1 (by omega : 0 < n - 1) hn C i0 := by
  have hd : 0 < n - 1 := by omega
  calc M1 hd C i0 ≤ ∑ _i : Fin n, EtauPow hd C i0 1 :=
        Finset.sum_le_sum fun i _ => Esigma_le_Etau hn C R i
    _ = (n : ℝ) * EtauPow hd C i0 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (n : ℝ) * mu1 hd hn C i0 := rfl

/-- `M_1 ≤ n E τ ≤ n e (n-1)/ε_P`. -/
theorem M1_le {n : ℕ} (hn : 2 ≤ n) (C : ContactMatrix n) {i0 : Fin n}
    (R : ReachData C.P i0) :
    M1 (by omega : 0 < n - 1) C i0 ≤
      (n : ℝ) * (Real.exp 1 * (((n : ℝ) - 1) / epsP C)) := by
  have hd : 0 < n - 1 := by omega
  calc M1 hd C i0 ≤ (n : ℝ) * mu1 hd hn C i0 := M1_le_n_mu1 hn C R
    _ ≤ (n : ℝ) * (Real.exp 1 * (((n : ℝ) - 1) / epsP C)) :=
        mul_le_mul_of_nonneg_left (mu1_le hn C R) (Nat.cast_nonneg _)

/-- `0 ≤ D_P ≤ n e (n-1)/ε_P`. -/
theorem DP_bounds {n : ℕ} (hn : 2 ≤ n) (C : ContactMatrix n) {i0 : Fin n}
    (R : ReachData C.P i0) :
    0 ≤ DP (by omega : 0 < n - 1) hn C i0 ∧
      DP (by omega : 0 < n - 1) hn C i0 ≤
        (n : ℝ) * (Real.exp 1 * (((n : ℝ) - 1) / epsP C)) := by
  have hd : 0 < n - 1 := by omega
  have hMu := M1_le_n_mu1 hn C R
  have hM0 : 0 ≤ M1 hd C i0 := Finset.sum_nonneg fun i _ => ENNReal.toReal_nonneg
  constructor
  · unfold DP; linarith
  · unfold DP
    calc n * mu1 hd hn C i0 - M1 hd C i0 ≤ n * mu1 hd hn C i0 := by linarith
      _ ≤ n * (Real.exp 1 * (((n : ℝ) - 1) / epsP C)) :=
          mul_le_mul_of_nonneg_left (mu1_le hn C R) (Nat.cast_nonneg _)

/-! ## 5. The scheduling images `S`, `A_i` and `P_β`, `A_β` (equations (B.5)-(B.6)) -/

/-- `S = H⌈(r_H + τ)^β⌉`. -/
def Sglob {n : ℕ} (hd : 0 < n - 1) (H rH β : ℝ)
    (ω : ℕ → Fin (n - 1) → Fin n → Fin n) (i0 : Fin n) : ℝ :=
  H * (Nat.ceil ((rH + tauR hd ω i0) ^ β) : ℝ)

/-- `A_i = H⌈(r_H + σ_i)^β⌉`. -/
def Anode {n : ℕ} (hd : 0 < n - 1) (H rH β : ℝ)
    (ω : ℕ → Fin (n - 1) → Fin n → Fin n) (i0 i : Fin n) : ℝ :=
  H * (Nat.ceil ((rH + sigmaR hd ω i0 i) ^ β) : ℝ)

/-- `P_β(H) = E S`. -/
def Pbeta {n : ℕ} (hd : 0 < n - 1) (C : ContactMatrix n) (i0 : Fin n) (H rH β : ℝ) : ℝ :=
  (∫⁻ ω, ENNReal.ofReal (Sglob hd H rH β ω i0) ∂procMeasure C (n - 1)).toReal

/-- `A_β(H,T) = ∑_i E min{T, A_i}`. -/
def Abeta {n : ℕ} (hd : 0 < n - 1) (C : ContactMatrix n) (i0 : Fin n) (H rH β T : ℝ) : ℝ :=
  ∑ i : Fin n,
    (∫⁻ ω, ENNReal.ofReal (min T (Anode hd H rH β ω i0 i)) ∂procMeasure C (n - 1)).toReal

/-- Pointwise bound `S ≤ H(1 + (r_H+τ)^β)`. -/
lemma Sglob_le (hd : 0 < n - 1) {H rH β : ℝ} (hH : 0 ≤ H) (hrH : 0 ≤ rH)
    (ω : ℕ → Fin (n - 1) → Fin n → Fin n) (i0 : Fin n) :
    Sglob hd H rH β ω i0 ≤ H * (1 + (rH + tauR hd ω i0) ^ β) := by
  unfold Sglob
  have hnn : (0:ℝ) ≤ (rH + tauR hd ω i0) ^ β :=
    Real.rpow_nonneg (by linarith [hrH, tauR_nonneg hd ω i0]) β
  have hceil : (Nat.ceil ((rH + tauR hd ω i0) ^ β) : ℝ) ≤ (rH + tauR hd ω i0) ^ β + 1 :=
    le_of_lt (Nat.ceil_lt_add_one hnn)
  calc H * (Nat.ceil ((rH + tauR hd ω i0) ^ β) : ℝ) ≤ H * ((rH + tauR hd ω i0) ^ β + 1) :=
        mul_le_mul_of_nonneg_left hceil hH
    _ = H * (1 + (rH + tauR hd ω i0) ^ β) := by ring

/-- Pointwise bound `S ≤ H(1 + 2^{β-1}(r_H^β + τ^β))`. -/
lemma Sglob_le' (hd : 0 < n - 1) {H rH β : ℝ} (hH : 0 ≤ H) (hrH : 0 ≤ rH) (hβ : 1 ≤ β)
    (ω : ℕ → Fin (n - 1) → Fin n → Fin n) (i0 : Fin n) :
    Sglob hd H rH β ω i0 ≤
      H * (1 + 2 ^ (β - 1) * (rH ^ β + tauR hd ω i0 ^ β)) := by
  refine (Sglob_le hd hH hrH ω i0).trans ?_
  have hconv := rpow_add_le_mul_rpow_add_rpow_real hrH (tauR_nonneg hd ω i0) hβ
  have h2 : (0:ℝ) ≤ 2 ^ (β - 1) := Real.rpow_nonneg (by norm_num) _
  nlinarith [hconv, hH, Real.rpow_nonneg hrH β, Real.rpow_nonneg (tauR_nonneg hd ω i0) β]

/-! ## 6. Equations (B.5)-(B.7): the moment bounds on `P_β(H)` -/

/-- The lintegral form of (B.7): `∫⁻ S ≤ H(1 + 2^{β-1}(r_H^β + E τ^β))`. -/
theorem Sglob_lintegral_le {n : ℕ} (hn : 2 ≤ n) (C : ContactMatrix n) {i0 : Fin n}
    (R : ReachData C.P i0) {H rH β : ℝ} (hH : 0 ≤ H) (hrH : 0 ≤ rH) (hβ : 1 ≤ β) :
    ∫⁻ ω, ENNReal.ofReal (Sglob (by omega : 0 < n - 1) H rH β ω i0) ∂procMeasure C (n - 1) ≤
      ENNReal.ofReal (H * (1 + 2 ^ (β - 1) *
        (rH ^ β + Real.exp 1 * Real.Gamma (β + 1) * (((n : ℝ) - 1) / epsP C) ^ β))) := by
  have hd : 0 < n - 1 := by omega
  have h2b : (0:ℝ) ≤ 2 ^ (β - 1) := Real.rpow_nonneg (by norm_num) _
  have hrpow : 0 ≤ rH ^ β := Real.rpow_nonneg hrH β
  have hG : 0 < Real.Gamma (β + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hbase : 0 ≤ ((n : ℝ) - 1) / epsP C :=
    div_nonneg (by have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
                   linarith)
      (epsP_nonneg C)
  have hB : 0 ≤ Real.exp 1 * Real.Gamma (β + 1) * (((n : ℝ) - 1) / epsP C) ^ β :=
    mul_nonneg (mul_nonneg (Real.exp_pos 1).le hG.le) (Real.rpow_nonneg hbase β)
  have hmeas : Measurable (fun ω : ℕ → Fin (n - 1) → Fin n → Fin n =>
      ENNReal.ofReal ((tauR hd ω i0) ^ β)) :=
    ENNReal.measurable_ofReal.comp ((measurable_tau_real hd i0).pow_const β)
  have hpt : ∀ ω : ℕ → Fin (n - 1) → Fin n → Fin n,
      ENNReal.ofReal (Sglob hd H rH β ω i0) ≤
        ENNReal.ofReal (H * (1 + 2 ^ (β - 1) * rH ^ β)) +
          ENNReal.ofReal (H * 2 ^ (β - 1)) * ENNReal.ofReal ((tauR hd ω i0) ^ β) := by
    intro ω
    have h1 := Sglob_le' hd hH hrH hβ ω i0
    have h2 : H * (1 + 2 ^ (β - 1) * (rH ^ β + tauR hd ω i0 ^ β)) =
        H * (1 + 2 ^ (β - 1) * rH ^ β) + (H * 2 ^ (β - 1)) * tauR hd ω i0 ^ β := by ring
    rw [h2] at h1
    have ha : 0 ≤ H * (1 + 2 ^ (β - 1) * rH ^ β) :=
      mul_nonneg hH (by nlinarith [h2b, hrpow])
    have hb : 0 ≤ (H * 2 ^ (β - 1)) * tauR hd ω i0 ^ β :=
      mul_nonneg (mul_nonneg hH h2b) (Real.rpow_nonneg (tauR_nonneg hd ω i0) β)
    calc ENNReal.ofReal (Sglob hd H rH β ω i0)
        ≤ ENNReal.ofReal (H * (1 + 2 ^ (β - 1) * rH ^ β) +
            (H * 2 ^ (β - 1)) * tauR hd ω i0 ^ β) := ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal (H * (1 + 2 ^ (β - 1) * rH ^ β)) +
            ENNReal.ofReal ((H * 2 ^ (β - 1)) * tauR hd ω i0 ^ β) :=
          ENNReal.ofReal_add ha hb
      _ = ENNReal.ofReal (H * (1 + 2 ^ (β - 1) * rH ^ β)) +
            ENNReal.ofReal (H * 2 ^ (β - 1)) * ENNReal.ofReal (tauR hd ω i0 ^ β) := by
          rw [ENNReal.ofReal_mul (mul_nonneg hH h2b)]
  calc ∫⁻ ω, ENNReal.ofReal (Sglob hd H rH β ω i0) ∂procMeasure C (n - 1)
      ≤ ∫⁻ ω, (ENNReal.ofReal (H * (1 + 2 ^ (β - 1) * rH ^ β)) +
          ENNReal.ofReal (H * 2 ^ (β - 1)) * ENNReal.ofReal ((tauR hd ω i0) ^ β))
          ∂procMeasure C (n - 1) := lintegral_mono hpt
    _ = ENNReal.ofReal (H * (1 + 2 ^ (β - 1) * rH ^ β)) * (procMeasure C (n - 1)) Set.univ +
          ENNReal.ofReal (H * 2 ^ (β - 1)) *
            ∫⁻ ω, ENNReal.ofReal ((tauR hd ω i0) ^ β) ∂procMeasure C (n - 1) := by
        rw [lintegral_add_left' measurable_const.aemeasurable, lintegral_const,
          lintegral_const_mul'' (ENNReal.ofReal (H * 2 ^ (β - 1))) hmeas.aemeasurable]
    _ = ENNReal.ofReal (H * (1 + 2 ^ (β - 1) * rH ^ β)) +
          ENNReal.ofReal (H * 2 ^ (β - 1)) *
            ∫⁻ ω, ENNReal.ofReal ((tauR hd ω i0) ^ β) ∂procMeasure C (n - 1) := by
        rw [measure_univ, mul_one]
    _ ≤ ENNReal.ofReal (H * (1 + 2 ^ (β - 1) * rH ^ β)) +
          ENNReal.ofReal (H * 2 ^ (β - 1)) * ENNReal.ofReal
            (Real.exp 1 * Real.Gamma (β + 1) * (((n : ℝ) - 1) / epsP C) ^ β) := by
        gcongr
        exact integral_rpow_tau_le hn C R hβ
    _ = ENNReal.ofReal (H * (1 + 2 ^ (β - 1) * (rH ^ β +
          Real.exp 1 * Real.Gamma (β + 1) * (((n : ℝ) - 1) / epsP C) ^ β))) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hH h2b),
          ← ENNReal.ofReal_add (mul_nonneg hH (by nlinarith [h2b, hrpow]))
            (mul_nonneg (mul_nonneg hH h2b) hB)]
        congr 1; ring

/-- **Lemma B.5, equation (B.7) (moment part).**
`P_β(H) = E S ≤ H(1 + 2^{β-1}(r_H^β + E τ^β)) ≤ H(1 + 2^{β-1}(r_H^β + eΓ(β+1)((n-1)/ε_P)^β))`. -/
theorem Pbeta_le {n : ℕ} (hn : 2 ≤ n) (C : ContactMatrix n) {i0 : Fin n}
    (R : ReachData C.P i0) {H rH β : ℝ} (hH : 0 ≤ H) (hrH : 0 ≤ rH) (hβ : 1 ≤ β) :
    Pbeta (by omega : 0 < n - 1) C i0 H rH β ≤
      H * (1 + 2 ^ (β - 1) *
        (rH ^ β + Real.exp 1 * Real.Gamma (β + 1) * (((n : ℝ) - 1) / epsP C) ^ β)) := by
  have hB := Sglob_lintegral_le hn C R hH hrH hβ
  have h2b : (0:ℝ) ≤ 2 ^ (β - 1) := Real.rpow_nonneg (by norm_num) _
  have hrpow : 0 ≤ rH ^ β := Real.rpow_nonneg hrH β
  have hG : 0 < Real.Gamma (β + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hBp : 0 ≤ Real.exp 1 * Real.Gamma (β + 1) * (((n : ℝ) - 1) / epsP C) ^ β :=
    mul_nonneg (mul_nonneg (Real.exp_pos 1).le hG.le)
      (Real.rpow_nonneg (div_nonneg (by
        have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
        linarith) (epsP_nonneg C)) β)
  rw [Pbeta]
  exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hH (by nlinarith [h2b, hrpow, hBp])) hB

/-- `E min{T,S}`. -/
def EminTS {n : ℕ} (hd : 0 < n - 1) (C : ContactMatrix n) (i0 : Fin n) (H rH β T : ℝ) : ℝ :=
  (∫⁻ ω, ENNReal.ofReal (min T (Sglob hd H rH β ω i0)) ∂procMeasure C (n - 1)).toReal

/-- Equation (B.7), first inequality: `E min{T,S} ≤ P_β(H)`. -/
theorem EminTS_le_Pbeta {n : ℕ} (hn : 2 ≤ n) (C : ContactMatrix n) {i0 : Fin n}
    (R : ReachData C.P i0) {H rH β T : ℝ} (hH : 0 ≤ H) (hrH : 0 ≤ rH) (hβ : 1 ≤ β) :
    EminTS (by omega : 0 < n - 1) C i0 H rH β T ≤ Pbeta (by omega : 0 < n - 1) C i0 H rH β := by
  have hd : 0 < n - 1 := by omega
  have hne : ∫⁻ ω, ENNReal.ofReal (Sglob hd H rH β ω i0) ∂procMeasure C (n - 1) ≠ ⊤ :=
    (lt_of_le_of_lt (Sglob_lintegral_le hn C R hH hrH hβ) ENNReal.ofReal_lt_top).ne
  exact ENNReal.toReal_mono hne
    (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (min_le_right _ _))

/-- `A_β(H,T) ≤ n T`: the trivial bound on the per-node arrival quantity. -/
theorem Abeta_le {n : ℕ} (hd : 0 < n - 1) (C : ContactMatrix n) (i0 : Fin n)
    {H rH β T : ℝ} (hT : 0 ≤ T) :
    Abeta hd C i0 H rH β T ≤ (n : ℝ) * T := by
  have hterm : ∀ i : Fin n,
      (∫⁻ ω, ENNReal.ofReal (min T (Anode hd H rH β ω i0 i)) ∂procMeasure C (n - 1)).toReal ≤ T := by
    intro i
    refine ENNReal.toReal_le_of_le_ofReal hT ?_
    calc ∫⁻ ω, ENNReal.ofReal (min T (Anode hd H rH β ω i0 i)) ∂procMeasure C (n - 1)
        ≤ ∫⁻ _ω, ENNReal.ofReal T ∂procMeasure C (n - 1) :=
          lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (min_le_left _ _)
      _ = ENNReal.ofReal T * (procMeasure C (n - 1)) Set.univ := by
            rw [lintegral_const]
      _ = ENNReal.ofReal T := by rw [measure_univ, mul_one]
  calc Abeta hd C i0 H rH β T ≤ ∑ _i : Fin n, T := Finset.sum_le_sum fun i _ => hterm i
    _ = (n : ℝ) * T := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end AnvBandit
