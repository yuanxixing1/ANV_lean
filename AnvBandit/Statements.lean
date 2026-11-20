import AnvBandit.Constants
import AnvBandit.Exponential
import AnvBandit.Regret
import AnvBandit.ScheduleLower
import AnvBandit.Propagation
import AnvBandit.Moments
import AnvBandit.Terminal
import AnvBandit.PublicBudget
import AnvBandit.NodeCost
import AnvBandit.Potential
import AnvBandit.AlgLine

set_option linter.unusedVariables false

/-!
# Cost functionals and the main theorems (Sections 4.2-4.3, Appendices B-C)

Defines the cost functionals (4.1)-(4.2), the combined bound (4.3), the explicit coefficients
(4.5), and states Theorem 4.1 ((4.3)-(4.7)), Corollary 4.2 and Propositions A.5, A.6, B.1-B.5,
C.1-C.5, and Theorem 4.1's explicit bound (4.4)-(4.5).

Status: these declarations are conditional combination tools unless explicitly stated otherwise.
Their theorem signatures may still receive the loss, concentration, exploration, stability,
and branch estimates as inputs. Such inputs are not proofs that the actual algorithm satisfies
those estimates. The final paper entry points must derive them from the original model and run.
`combine_timeorder_bounds` is purely algebraic and covers all positive `T,H`.
`Exponential.proposition_A_4` in the imported legacy layer compares the restricted synchronous
benchmark with a largest-marginals value; it does not yet identify the full joint-action optimum.
See the current audit/status documents for end-to-end completion, not these historical names.
-/

noncomputable section
open scoped BigOperators Topology
open Filter Finset

namespace AnvBandit

/-- Schedule- and propagation-level quantities of Appendices B.2, C.1-C.2. -/
structure Props where
  Pβ : ℝ
  Aβ : ℝ
  M1 : ℝ
  DP : ℝ
  Kβ : ℝ

/-- Equation (4.1a): global-waiting branch `E^{(λ)}_glob(c;H)`. -/
def Eglob (n : ℕ) (cmax Pβ Clam0 : ℝ) : ℝ := n * cmax * Pβ + Clam0

/-- Equation (4.1b): per-node-arrival branch `E^{(λ)}_node(c;H)`. -/
def Enode (cmax Aβ ClamDP : ℝ) : ℝ := cmax * Aβ + ClamDP

/-- Equation (4.1c): potential branch `E^{(λ)}_pot(c;H)`. -/
def Epot (Flam cmax M1 Flamc Kβ : ℝ) : ℝ := Flam + cmax * (2 * M1 * Flamc + Kβ)

/-- Equation (4.2): `E_λ(c;H) = min` over the three branches. -/
def Ecost (eglob enode epot : ℝ) : ℝ := min eglob (min enode epot)

/-- Equation (4.3): `U^co_λ(T;H)`. -/
def Uco (nT Γ nρmaxT Elam δnρmaxT : ℝ) : ℝ := min nT (Γ + min nρmaxT (Elam + δnρmaxT))

/-- Equation (4.8): communication-free baseline bound `U^ind_λ(T)`. -/
def Uind (nT Γ ncmaxT Flamc δncmaxT : ℝ) : ℝ := min nT (Γ + min ncmaxT (Flamc + δncmaxT))

/-- Equation (4.5a): `C_{h,λ}`. -/
def Ch (n ρmax Aβξ : ℝ) : ℝ := n * ρmax * Aβξ

/-- Equation (4.5b): `C_{log,λ}`. -/
def Clog (ξ Ch Jlam : ℝ) : ℝ := 3 * (ξ * Ch + Jlam)

/-- Equation (4.5c): `C_{0,λ}`. -/
def C0 (Γ D nρmax Clog nK : ℝ) : ℝ := Γ + D + nρmax / 4 + Clog / 3 * Real.log (2 * nK)

/-- Theorem 4.1, equation (4.3): `min`-combination step. -/
theorem theorem_4_1 {n K : ℕ} (M : DecayModel n K) (T : ℕ) (δ : ℝ) (lam : Fin 2)
    (caps : Props) (Flam Clam0 ClamDP Flamc ρmax Rteam : ℝ)
    (htriv : Rteam ≤ (n : ℝ) * T)
    (hcrude : Rteam ≤ M.Gamma lam + n * ρmax * T)
    (hglob : Rteam ≤ M.Gamma lam + Eglob n ρmax caps.Pβ Clam0 + δ * (n * ρmax * T))
    (hnode : Rteam ≤ M.Gamma lam + Enode ρmax caps.Aβ ClamDP + δ * (n * ρmax * T))
    (hpot : Rteam ≤ M.Gamma lam + Epot Flam ρmax caps.M1 Flamc caps.Kβ + δ * (n * ρmax * T)) :
    Rteam ≤ Uco ((n : ℝ) * T) (M.Gamma lam) (n * ρmax * T)
      (Ecost (Eglob n ρmax caps.Pβ Clam0) (Enode ρmax caps.Aβ ClamDP)
        (Epot Flam ρmax caps.M1 Flamc caps.Kβ)) (δ * (n * ρmax * T)) := by
  have hb : Rteam ≤ M.Gamma lam
      + (Ecost (Eglob n ρmax caps.Pβ Clam0) (Enode ρmax caps.Aβ ClamDP)
        (Epot Flam ρmax caps.M1 Flamc caps.Kβ) + δ * (n * ρmax * T)) := by
    have h2 := le_min hglob (le_min hnode hpot)
    have heq : min (M.Gamma lam + Eglob n ρmax caps.Pβ Clam0 + δ * (n * ρmax * T))
          (min (M.Gamma lam + Enode ρmax caps.Aβ ClamDP + δ * (n * ρmax * T))
            (M.Gamma lam + Epot Flam ρmax caps.M1 Flamc caps.Kβ + δ * (n * ρmax * T)))
        = M.Gamma lam + (Ecost (Eglob n ρmax caps.Pβ Clam0) (Enode ρmax caps.Aβ ClamDP)
            (Epot Flam ρmax caps.M1 Flamc caps.Kβ) + δ * (n * ρmax * T)) := by
      simp only [Ecost]
      rw [min_add_add_right, min_add_add_right, min_add_add_left, min_add_add_left]
      ring
    exact le_trans h2 (le_of_eq heq)
  refine le_min htriv ?_
  have h2 := le_min hcrude hb
  rwa [min_add_add_left] at h2

/-- `δ = (T+1)^{-2}` (analysis time scale, Section 4.2). -/
def deltaStar (T : ℕ) : ℝ := ((T : ℝ) + 1) ^ (-2 : ℤ)

/-- `L_δ = log(2nKT/δ)` at `δ = (T+1)^{-2}`, i.e. `log(2nK·T·(T+1)^2)` (Appendix C.3). -/
def LdeltaStar (n K T : ℕ) : ℝ :=
  Real.log (2 * ((n * K : ℕ) : ℝ) * (T : ℝ) * ((T : ℝ) + 1) ^ 2)

/-- The explicit bound of equations (4.4)-(4.5):
`min{ nT, C_{0,λ} + C_{h,λ}·h + C_{log,λ}·log(T+1) }`. -/
def explicitBound {n K : ℕ} (M : DecayModel n K) (T h : ℕ) (ξ β εP : ℝ) (lam : Fin 2) : ℝ :=
  min ((n : ℝ) * T)
    (C0 (M.Gamma lam) (M.Dlam lam) (n * M.rhoMax lam)
        (Clog ξ (Ch n (M.rhoMax lam) (M.Abetaxi ξ β εP)) (M.Jlam lam)) (n * K)
      + Ch n (M.rhoMax lam) (M.Abetaxi ξ β εP) * h
      + Clog ξ (Ch n (M.rhoMax lam) (M.Abetaxi ξ β εP)) (M.Jlam lam) * Real.log (T + 1))

-- Theorem 4.1, equations (4.4)-(4.5): see `AnvBandit.Explicit` for the proved version.

/-- The time-order benchmark of (4.6): `H + (log(T+1))^γ / H^{γ-1} + log(T+1) + 1`, where
`γ = β/(β-1)`. -/
def TimeOrder (β : ℝ) (R : ℕ → ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ T H : ℕ, 1 ≤ T → 1 ≤ H →
    R T H ≤ C * ((H : ℝ) + (Real.log (T + 1)) ^ (β / (β - 1))
      / ((H : ℝ) ^ (β / (β - 1) - 1)) + Real.log (T + 1) + 1)

/-- Pure arithmetic combination of supplied budget estimates on all positive `T,H`.
This is not an end-to-end theorem about the paper's algorithm: its budget inputs still
require separate proofs for the actual run. The domain includes `H<T`, `H=T`, and `H>T`. -/
theorem combine_timeorder_bounds {β : ℝ} (_hβ : 1 < β) (R K : ℕ → ℕ → ℝ)
    (C0 C1 CK : ℝ) (h0 : 0 ≤ C0) (h1 : 0 ≤ C1) (hK : 0 ≤ CK)
    (hbudget : ∀ T H : ℕ, 1 ≤ T → 1 ≤ H → R T H ≤ C0 + C1 * K T H + C1 * Real.log (T + 1))
    (hKbd : ∀ T H : ℕ, 1 ≤ T → 1 ≤ H →
      K T H ≤ CK * ((H : ℝ) + (Real.log (T + 1)) ^ (β / (β - 1))
        / ((H : ℝ) ^ (β / (β - 1) - 1)))) :
    TimeOrder β R := by
  refine ⟨C0 + C1 * CK + C1, by positivity, fun T H hT hH => ?_⟩
  have hlogT : 0 ≤ Real.log (T + 1) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ T + 1 by omega))
  have hQ0 : 0 ≤ (Real.log (T + 1)) ^ (β / (β - 1)) / ((H : ℝ) ^ (β / (β - 1) - 1)) :=
    div_nonneg (Real.rpow_nonneg hlogT _) (Real.rpow_nonneg (by positivity) _)
  have h1' := hbudget T H hT hH
  have h2' := hKbd T H hT hH
  have hbnd : (1:ℝ) ≤ (H:ℝ) + (Real.log (T + 1)) ^ (β / (β - 1))
      / ((H : ℝ) ^ (β / (β - 1) - 1)) + Real.log (T + 1) + 1 := by linarith
  have hb2 : (H:ℝ) + (Real.log (T + 1)) ^ (β / (β - 1)) / ((H : ℝ) ^ (β / (β - 1) - 1))
      ≤ (H:ℝ) + (Real.log (T + 1)) ^ (β / (β - 1)) / ((H : ℝ) ^ (β / (β - 1) - 1))
        + Real.log (T + 1) + 1 := by linarith
  have hb3 : Real.log (T + 1)
      ≤ (H:ℝ) + (Real.log (T + 1)) ^ (β / (β - 1)) / ((H : ℝ) ^ (β / (β - 1) - 1))
        + Real.log (T + 1) + 1 := by linarith
  nlinarith [h1', h2', h0, h1, hK, hbnd, hb2, hb3, hQ0, mul_nonneg h1 hK]

/-- Theorem 4.1, equation (4.7): with the public scale `H = H_ξ`, the team regret is
`O(h + log(T+1))`. -/
theorem theorem_4_1_timeorder_Hxi (ξ : ℝ) (hξ : 0 < ξ) (R : ℕ → ℝ) (h : ℕ)
    (hbound : ∃ C0 Ch Clog : ℝ, 0 ≤ C0 ∧ 0 ≤ Ch ∧ 0 ≤ Clog ∧ ∀ T : ℕ,
      R T ≤ C0 + Ch * h + Clog * Real.log (T + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ T ≥ N, R T ≤ C * (h + Real.log (T + 1)) := by
  obtain ⟨C0, Ch, Clog, h0, hh0, hl0, hb⟩ := hbound
  refine ⟨C0 + Ch + Clog + 1 + C0 / Real.log 2, by positivity, 1, fun T hT => ?_⟩
  have hLpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL2 : Real.log 2 ≤ Real.log (T + 1) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ T + 1 by omega))
  have hlog : 0 ≤ Real.log (T + 1) := le_trans (le_of_lt hLpos) hL2
  have hh : 0 ≤ (h : ℝ) := by positivity
  have hCL : C0 ≤ C0 / Real.log 2 * Real.log (T + 1) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hLpos]
    nlinarith [hL2, h0]
  have hCh2 : Ch * h ≤ (C0 + Ch + Clog + 1 + C0 / Real.log 2) * h :=
    mul_le_mul_of_nonneg_right (by
      have : 0 ≤ C0 / Real.log 2 := div_nonneg h0 (le_of_lt hLpos); linarith) hh
  have hCL2 : Clog * Real.log (T + 1) ≤
      (C0 + Ch + Clog + 1 + C0 / Real.log 2) * Real.log (T + 1) :=
    mul_le_mul_of_nonneg_right (by
      have : 0 ≤ C0 / Real.log 2 := div_nonneg h0 (le_of_lt hLpos); linarith) hlog
  have := hb T
  nlinarith [this, hCL, hCh2, hCL2, hlog, hh]

/-- Corollary 4.2 (sufficient condition for strict improvement of the cooperative displayed bound):
if the cooperative cost is smaller than the independent exploration cost and the truncations do not
invalidate the strict comparison, then `U^co_λ(T;H) < U^ind_λ(T)`. -/
theorem corollary_4_2 {n : ℕ} (T : ℕ) (Γ ncmaxT Flamc Eco δ : ℝ)
    (hEco : Eco < Flamc)
    (hFT : Eco + δ * ncmaxT < min ncmaxT ((n : ℝ) * T - Γ)) :
    Uco ((n : ℝ) * T) Γ ncmaxT Eco (δ * ncmaxT)
      < Uind ((n : ℝ) * T) Γ ncmaxT Flamc (δ * ncmaxT) := by
  have hFT1 : Eco + δ * ncmaxT < ncmaxT := lt_of_lt_of_le hFT (min_le_left _ _)
  have hFT2 : Eco + δ * ncmaxT < (n : ℝ) * T - Γ := lt_of_lt_of_le hFT (min_le_right _ _)
  have hmin1 : min ncmaxT (Eco + δ * ncmaxT) = Eco + δ * ncmaxT := min_eq_right (le_of_lt hFT1)
  have hUco : Uco ((n : ℝ) * T) Γ ncmaxT Eco (δ * ncmaxT) = Γ + (Eco + δ * ncmaxT) := by
    rw [Uco, hmin1, min_eq_right]; linarith
  have hstrict : Γ + (Eco + δ * ncmaxT) < Γ + min ncmaxT (Flamc + δ * ncmaxT) := by
    have : Eco + δ * ncmaxT < min ncmaxT (Flamc + δ * ncmaxT) := lt_min hFT1 (by linarith)
    linarith
  have hUind : Γ + (Eco + δ * ncmaxT) < Uind ((n : ℝ) * T) Γ ncmaxT Flamc (δ * ncmaxT) := by
    rw [Uind]
    exact lt_min (by linarith) hstrict
  rw [hUco]; exact hUind

/-- Proposition A.5: end-point regret conversion.  Given the trajectory conversion
`R_team ≤ Γ_λ + ∑_k ρ^{(λ)}_k E M_k` (from (A.7)/(A.8), built on (A.2)) and
`R_b = ∑_k Δ_k E M_k`, one obtains the multiplicative form `(1 + ε_λ/Δ_b)`. -/
theorem proposition_A_5 {n K : ℕ} (M : DecayModel n K) (T : ℕ) (lam : Fin 2)
    (Rteam Rb : ℝ) (EMk : Fin K → ℝ)
    (hEM : ∀ k ∈ M.others, 0 ≤ EMk k)
    (hconv : Rteam ≤ M.Gamma lam + ∑ k ∈ M.others, M.rho T lam k * EMk k)
    (hRb : Rb = ∑ k ∈ M.others, M.gap k * EMk k) :
    Rteam ≤ M.Gamma lam + (1 + M.eps T lam / M.DeltaMin) * Rb := by
  refine le_trans hconv ?_
  refine add_le_add le_rfl ?_
  have hterm : ∀ k ∈ M.others, M.rho T lam k * EMk k
      ≤ (1 + M.eps T lam / M.DeltaMin) * (M.gap k * EMk k) := by
    intro k hk
    have hkne : k ≠ M.star := (Finset.mem_erase.mp hk).1
    have hgap := M.DeltaMin_le hk
    have hpos := M.DeltaMin_pos
    have heps : 0 ≤ M.eps T lam := psi_nonneg (fun s _ => M.f_nonneg M.star s) _
    have hρ : M.rho T lam k = M.gap k + M.eps T lam := by simp [DecayModel.rho, hkne]
    have h1 : 1 ≤ M.gap k / M.DeltaMin := by
      rw [le_div_iff₀ hpos]; linarith
    have hle : M.eps T lam ≤ M.eps T lam / M.DeltaMin * M.gap k := by
      calc M.eps T lam = M.eps T lam * 1 := (mul_one _).symm
        _ ≤ M.eps T lam * (M.gap k / M.DeltaMin) := mul_le_mul_of_nonneg_left h1 heps
        _ = M.eps T lam / M.DeltaMin * M.gap k := by ring
    have hmul : (1 + M.eps T lam / M.DeltaMin) * (M.gap k * EMk k)
        = M.gap k * EMk k + M.eps T lam / M.DeltaMin * M.gap k * EMk k := by ring
    rw [hρ]
    nlinarith [hle, hEM k hk, heps, hmul, mul_nonneg heps (hEM k hk)]
  calc ∑ k ∈ M.others, M.rho T lam k * EMk k
      ≤ ∑ k ∈ M.others, (1 + M.eps T lam / M.DeltaMin) * (M.gap k * EMk k) :=
        Finset.sum_le_sum hterm
    _ = (1 + M.eps T lam / M.DeltaMin) * ∑ k ∈ M.others, M.gap k * EMk k := by
        rw [Finset.mul_sum]
    _ = (1 + M.eps T lam / M.DeltaMin) * Rb := by rw [hRb]

/-- **Proposition A.6 (public positive-part budget and per-node selection counts)**, now proved
genuinely from the trajectory model (`AnvBandit.PublicBudget`):
(A.10) `∑_i E_{i,k}(N_{i,k}(T)) ≤ Ξ_k`;
(A.11) on `E_δ`, `A⁺_{i,k}(T) ≤ n_k + (4/Δ_k) E_{i,k}(N_{i,k}(T))` for each node `i`;
(A.12) for any node subset `J`, `∑_{i∈J} A⁺_{i,k}(T) ≤ |J| n_k + 4 Ξ_k/Δ_k`. -/
theorem proposition_A_6 {n K : ℕ} (M : DecayModel n K) (R : GoodRun M)
    (q : Fin n → Fin K → ℕ → ℕ)
    (hpq : ∀ i k s, 1 ≤ s → R.p i k s = M.b k + M.f k (q i k s))
    (hqge : ∀ i k s, 1 ≤ s → s ≤ q i k s)
    (hqteam : ∀ t i k, R.I t i = k → q i k (R.N t i k + 1) = R.teamCount t k + 1)
    (hL : 0 < R.L) (T : ℕ) {k : Fin K} (hk : k ≠ M.star) :
    (∑ i, R.EikPers q T i k) ≤ M.Xi k ∧
    (∀ i, (R.AplusCount T i k : ℝ) ≤ (M.nkAll R.L k : ℝ) + 4 / M.gap k * R.EikPers q T i k) ∧
    (∀ J : Finset (Fin n), (∑ i ∈ J, (R.AplusCount T i k : ℝ))
      ≤ (J.card : ℝ) * (M.nkAll R.L k : ℝ) + 4 / M.gap k * M.Xi k) :=
  ⟨by
     have h1 : (∑ i, R.EikPers q T i k) = ∑ i, R.EikRound T i k :=
       Finset.sum_congr rfl fun i _ => R.EikPers_eq_EikRound q hqteam T i k
     rw [h1]; exact R.team_pos_budget T hk,
   fun i => node_selection_bound R q hpq hqge hL T hk,
   fun J => subset_selection_bound R q hpq hqge hqteam hL T hk J⟩

/-- Replaceable-set update (equation (3.8)): if the received arm `o` is already active the set is
unchanged; otherwise it becomes `{Top_i(D_i), o}` (the cached top arm together with the newcomer). -/
def updateD {K : ℕ} (S D : Finset (Fin K)) (top o : Fin K) : Finset (Fin K) :=
  if o ∈ S then D else {top, o}

/-- Proposition B.1 (execution feasibility): the update rule (3.8) preserves both the nonemptiness
and the cardinality bound `|D| ≤ 2` of the replaceable set, so a valid `Top_i(D_i)` always exists
at the next phase. -/
theorem proposition_B_1 {K : ℕ} (S D : Finset (Fin K)) (top o : Fin K)
    (hD : D.Nonempty) (hcard : D.card ≤ 2) :
    (updateD S D top o).Nonempty ∧ (updateD S D top o).card ≤ 2 := by
  unfold updateD
  split
  · exact ⟨hD, hcard⟩
  · refine ⟨⟨top, Finset.mem_insert_self top _⟩, ?_⟩
    calc ({top, o} : Finset (Fin K)).card ≤ ({o} : Finset (Fin K)).card + 1 :=
          Finset.card_insert_le top {o}
      _ = 2 := by simp

/-- Lemma B.2 (phase residual exploration and correct recommendation): under `E_δ`, in a complete
phase containing `k⋆` and with residual budgets `z_k`, if the stage length strictly exceeds
`∑_k z_k + max_k z_k`, then no suboptimal arm can have the strictly largest phase count. -/
theorem lemma_B_2 {n K : ℕ} (M : DecayModel n K) (z : Fin K → ℝ) (d : ℝ)
    (hz : ∀ k ∈ M.others, 0 ≤ z k)
    (hlen : d > ∑ k ∈ M.others, z k + M.supOthers z) (dstar : ℝ)
    (hdstar : dstar ≥ d - ∑ k ∈ M.others, z k) :
    ∀ k ∈ M.others, z k < dstar := by
  intro k hk
  have h1 : z k ≤ M.supOthers z := M.le_supOthers hk
  have h2 : M.supOthers z ≤ ∑ k ∈ M.others, z k + M.supOthers z :=
    le_add_of_nonneg_left (Finset.sum_nonneg (fun k hk => hz k hk))
  linarith

/-- Lemma B.4 (propagation tail bound and moments), proved from the contact process
(`AnvBandit.Propagation`): with `ε_P = p_min^{n−1}`,
`P{τ(i₀) > m(n−1)} ≤ (1−ε_P)^m` and `E τ(i₀)^β ≤ e Γ(β+1) ((n−1)/ε_P)^β`. -/
theorem lemma_B_4 {n : ℕ} (hn : 2 ≤ n) (C : ContactMatrix n) {i0 : Fin n}
    (R : ReachData C.P i0) (β : ℝ) (hβ : 1 < β) (m : ℕ) :
    procMeasure C (n - 1) {ω | m * (n - 1) < tau (by omega : 0 < n - 1) ω i0} ≤
        ENNReal.ofReal ((1 - epsP C) ^ m) ∧
      ∫⁻ ω, ENNReal.ofReal ((tau (by omega : 0 < n - 1) ω i0 : ℝ) ^ β)
          ∂procMeasure C (n - 1) ≤
        ENNReal.ofReal (Real.exp 1 * Real.Gamma (β + 1) * (((n : ℝ) - 1) / epsP C) ^ β) :=
  ⟨measure_tau_gt_le hn C R m, integral_rpow_tau_le hn C R hβ.le⟩

/-- Lemma B.5, equation (B.7) (propagation moment part), *proved* from the contact process:
`E min{T,S} ≤ P_β(H) ≤ H(1 + 2^{β−1}(r_H^β + Eτ^β))`.  This is now a genuine theorem rather than a
conditional combination step. -/
theorem lemma_B_5 {n : ℕ} (hn : 2 ≤ n) (C : ContactMatrix n) {i0 : Fin n}
    (R : ReachData C.P i0) {H rH β T : ℝ} (hH : 0 ≤ H) (hrH : 0 ≤ rH) (hβ : 1 ≤ β) :
    EminTS (by omega : 0 < n - 1) C i0 H rH β T ≤
      H * (1 + 2 ^ (β - 1) *
        (rH ^ β + Real.exp 1 * Real.Gamma (β + 1) * (((n : ℝ) - 1) / epsP C) ^ β)) :=
  le_trans (EminTS_le_Pbeta hn C R hH hrH hβ) (Pbeta_le hn C R hH hrH hβ)

/-- Lemma C.1 (post-stabilisation exploration cost), *proved* from the algorithm-trace counting:
after stabilisation the weighted exploration cost of the rounds `Tstart, …, T−1` is at most
`C_λ(c; 0)`.  For the personal-fatigue branch (`λ = 0`) this is `C(c)`; the public branch follows
by the second candidate `CN(c) + B_pub(c)`.  This replaces the previous conditional combination
step. -/
theorem lemma_C_1 {n K : ℕ} {M : DecayModel n K} (R : GoodRun M) (hn : 0 < n) (c : Fin K → ℝ)
    (T Tstart : ℕ) (i0 : Fin n) (D : Fin n → Finset (Fin K)) (hc : ∀ k, 0 ≤ c k)
    (hstar : c M.star = 0)
    (hstab : ∀ t i, Tstart ≤ t → t < T → R.active t i = permSet n K i ∪ D i)
    (hstar_perm : M.star ∈ permSet n K i0)
    (hdisj : ∀ i, Disjoint (permSet n K i) (D i))
    (hDcard : ∀ i, (D i).card ≤ 2)
    (hstar_mem : ∀ i, M.star ∈ permSet n K i ∪ D i)
    (hSbound : ∀ i, (permSet n K i ∪ D i).card ≤ smax n K) :
    (∑ t ∈ (Finset.range T).filter (fun t => Tstart ≤ t), ∑ i, c (R.I t i))
      ≤ M.Clam c R.L 0 0 := by
  refine le_trans (lemma_C_1_count R hn c T Tstart i0 D hc hstar hstab hstar_perm hdisj
    hDcard hstar_mem hSbound) ?_
  simp [DecayModel.Clam]

/- Lemma C.3 (general-schedule budget and propagation potential), equation (C.5), together with the
Abel-summation telescope `abel_bound` of (C.10), are proved in `AnvBandit/Potential.lean`. -/

/-- Theorem C.4 (complete finite-horizon bound for general weights), equation (C.14):
`L_c(T) ≤ min{n c_max T, E_λ(c;H) + δ n c_max T}`; in particular `R_b(T) ≤ U^H_{Δ,λ}(T)`. -/
theorem theorem_C_4 {n K : ℕ} (M : DecayModel n K) (T h : ℕ) (δ : ℝ) (β : ℝ) (hβ : 1 < β)
    (c : Fin K → ℝ) (L : ℝ) (lam : Fin 2) (hc : ∀ k, 0 ≤ c k)
    (Lc Elam : ℝ) (hcrude : Lc ≤ n * M.supOthers (fun k => c k) * T)
    (hE : Lc ≤ Elam + δ * n * M.supOthers (fun k => c k) * T) :
    Lc ≤ min (n * M.supOthers (fun k => c k) * T)
      (Elam + δ * n * M.supOthers (fun k => c k) * T) :=
  le_min hcrude hE

/-- Proposition C.5 (general-weight bound for the communication-free baseline), equation (C.15):
`L^ind_c(T) ≤ min{n c_max T, F_λ(c) + δ n c_max T}`. -/
theorem proposition_C_5 {n K : ℕ} (M : DecayModel n K) (T : ℕ) (δ : ℝ) (c : Fin K → ℝ)
    (L : ℝ) (lam : Fin 2) (hc : ∀ k, 0 ≤ c k)
    (Lind : ℝ) (hcrude : Lind ≤ n * M.supOthers (fun k => c k) * T)
    (hE : Lind ≤ M.Flam c L lam + δ * n * M.supOthers (fun k => c k) * T) :
    Lind ≤ min (n * M.supOthers (fun k => c k) * T)
      (M.Flam c L lam + δ * n * M.supOthers (fun k => c k) * T) :=
  le_min hcrude hE


/-- The multiplicative step of Proposition A.5, factored out:
`∑_{k≠⋆} ρ^{(λ)}_k E M_k ≤ (1 + ε_λ/Δ_b) ∑_{k≠⋆} Δ_k E M_k` (for nonnegative `E M_k`). -/
theorem rho_sum_le {n K : ℕ} (M : DecayModel n K) (T : ℕ) (lam : Fin 2) (EMk : Fin K → ℝ)
    (hEM : ∀ k ∈ M.others, 0 ≤ EMk k) :
    ∑ k ∈ M.others, M.rho T lam k * EMk k
      ≤ (1 + M.eps T lam / M.DeltaMin) * ∑ k ∈ M.others, M.gap k * EMk k := by
  have hterm : ∀ k ∈ M.others, M.rho T lam k * EMk k
      ≤ (1 + M.eps T lam / M.DeltaMin) * (M.gap k * EMk k) := by
    intro k hk
    have hkne : k ≠ M.star := (Finset.mem_erase.mp hk).1
    have hgap := M.DeltaMin_le hk
    have hpos := M.DeltaMin_pos
    have heps : 0 ≤ M.eps T lam := psi_nonneg (fun s _ => M.f_nonneg M.star s) _
    have hρ : M.rho T lam k = M.gap k + M.eps T lam := by
      simp [DecayModel.rho, hkne]
    have h1 : 1 ≤ M.gap k / M.DeltaMin := by rw [le_div_iff₀ hpos]; linarith
    have hle : M.eps T lam ≤ M.eps T lam / M.DeltaMin * M.gap k := by
      calc M.eps T lam = M.eps T lam * 1 := (mul_one _).symm
        _ ≤ M.eps T lam * (M.gap k / M.DeltaMin) := mul_le_mul_of_nonneg_left h1 heps
        _ = M.eps T lam / M.DeltaMin * M.gap k := by ring
    have hmul : (1 + M.eps T lam / M.DeltaMin) * (M.gap k * EMk k)
        = M.gap k * EMk k + M.eps T lam / M.DeltaMin * M.gap k * EMk k := by ring
    rw [hρ]
    nlinarith [hle, hEM k hk, heps, hmul, mul_nonneg heps (hEM k hk)]
  calc ∑ k ∈ M.others, M.rho T lam k * EMk k
      ≤ ∑ k ∈ M.others, (1 + M.eps T lam / M.DeltaMin) * (M.gap k * EMk k) :=
        Finset.sum_le_sum hterm
    _ = (1 + M.eps T lam / M.DeltaMin) * ∑ k ∈ M.others, M.gap k * EMk k := by
        rw [Finset.mul_sum]

/-- **Proposition A.5, personal-fatigue trajectory form** (derived from (A.7)). -/
theorem proposition_A_5_traj0 {n K : ℕ} {T : ℕ} (hT : 1 ≤ T) (M : DecayModel n K)
    (u : Fin n → Fin T → Fin K) :
    Vstar0 (T := T) M - J0 M u ≤ M.Gamma 0
      + (1 + M.eps T 0 / M.DeltaMin) * (∑ k ∈ M.others, M.gap k * (Mtot u k : ℝ)) := by
  refine le_trans (regret_conversion_lambda0 hT M u) ?_
  exact add_le_add le_rfl (rho_sum_le M T 0 (fun k => Mtot u k) (fun k _ => Nat.cast_nonneg _))

/-- **Proposition A.5, public-fatigue trajectory form** (derived from (A.8)). -/
theorem proposition_A_5_traj1 {n K : ℕ} {T : ℕ} (hT : 1 ≤ T) (M : DecayModel n K)
    (u : Fin n → Fin T → Fin K) :
    Vstar1 (T := T) M - J1 M u ≤ M.Gamma 1
      + (1 + M.eps T 1 / M.DeltaMin) * (∑ k ∈ M.others, M.gap k * (Mtot u k : ℝ)) := by
  refine le_trans (regret_conversion_lambda1 hT M u) ?_
  exact add_le_add le_rfl (rho_sum_le M T 1 (fun k => Mtot u k) (fun k _ => Nat.cast_nonneg _))


end AnvBandit
