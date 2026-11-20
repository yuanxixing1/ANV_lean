import AnvBandit.Batch

set_option linter.unusedVariables false

/-!
# Schedule scale, confidence radius, thresholds, and Lemma A.2

* `Ldelta` (`L_δ = log(2nKT/δ)`), `rdelta` (`r_δ(m) = √(L_δ/2m)`),
* `Hxi` (`H_ξ = h⌈ξL_δ/h⌉`) with the bracket property `ξL_δ ≤ H_ξ < ξL_δ + h`,
* the thresholds `m0` (`m⁰_k`), `nk` (`n_k = ⌈32L_δ/Δ_k²⌉`) and `mk = max m⁰_k n_k`,
* Lemma A.2: on the good event, a selected suboptimal arm with `m` prior pulls satisfies
  `Δ_k ≤ ψ_k(m) + 2 r_δ(m)`; and once `m ≥ m_k` it is never selected (strict form).
-/

noncomputable section
open scoped BigOperators Topology
open Filter Finset

namespace AnvBandit

/-- Stage endpoint `t_ℓ = H ⌈ℓ^β⌉` (equation (3.5)). -/
def tEll (H β : ℝ) (ℓ : ℕ) : ℝ := H * ⌈(ℓ : ℝ) ^ β⌉₊

/-- Stage length `d_ℓ = t_ℓ − t_{ℓ−1}` (equation (3.5)). -/
def dEll (H β : ℝ) (ℓ : ℕ) : ℝ := tEll H β ℓ - tEll H β (ℓ - 1)

/-- `L_δ = log(2nKT/δ)`. -/
def Ldelta (n K T : ℕ) (δ : ℝ) : ℝ := Real.log (2 * n * K * T / δ)

/-- `r_δ(m) = √(L_δ /(2m))`. -/
def rdelta (L : ℝ) (m : ℕ) : ℝ := Real.sqrt (L / (2 * m))

/-- `H_ξ = h⌈ξL_δ/h⌉` (schedule scale, equation (3.6)). -/
def Hxi (h : ℕ) (ξ L : ℝ) : ℕ := h * ⌈(ξ * L) / h⌉₊

/-- `n_k = ⌈32L_δ/Δ_k²⌉` (statistical-error threshold). -/
def nk (L Δ : ℝ) : ℕ := ⌈32 * L / Δ ^ 2⌉₊

lemma rdelta_nonneg (L : ℝ) (m : ℕ) : 0 ≤ rdelta L m := Real.sqrt_nonneg _

lemma Hxi_ge (h : ℕ) (hh : 0 < h) (ξ L : ℝ) : ξ * L ≤ (Hxi h ξ L : ℝ) := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hceil : (ξ * L) / (h : ℝ) ≤ (⌈(ξ * L) / (h : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (h : ℝ) * ((ξ * L) / (h : ℝ)) ≤ (h : ℝ) * (⌈(ξ * L) / (h : ℝ)⌉₊ : ℝ) :=
    mul_le_mul_of_nonneg_left hceil (le_of_lt hhR)
  have hcast : ((Hxi h ξ L : ℕ) : ℝ) = (h : ℝ) * (⌈(ξ * L) / (h : ℝ)⌉₊ : ℝ) := by
    simp only [Hxi]; push_cast; ring
  rw [hcast]
  rwa [mul_div_cancel₀ _ hhR.ne'] at h2

lemma Hxi_lt (h : ℕ) (hh : 0 < h) {ξ L : ℝ} (hx : 0 ≤ ξ * L) :
    (Hxi h ξ L : ℝ) < ξ * L + h := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hnonneg : 0 ≤ (ξ * L) / (h : ℝ) := div_nonneg hx (by positivity)
  have hceil : (⌈(ξ * L) / (h : ℝ)⌉₊ : ℝ) < (ξ * L) / (h : ℝ) + 1 := Nat.ceil_lt_add_one hnonneg
  have hcast : ((Hxi h ξ L : ℕ) : ℝ) = (h : ℝ) * (⌈(ξ * L) / (h : ℝ)⌉₊ : ℝ) := by
    simp only [Hxi]; push_cast; ring
  rw [hcast]
  calc (h : ℝ) * (⌈(ξ * L) / (h : ℝ)⌉₊ : ℝ) < (h : ℝ) * ((ξ * L) / (h : ℝ) + 1) :=
        mul_lt_mul_of_pos_left hceil hhR
    _ = ξ * L + h := by rw [mul_add, mul_div_cancel₀ _ hhR.ne', mul_one]

/-- Equation (3.6) bracket: `ξL_δ ≤ H_ξ < ξL_δ + h`. -/
theorem Hxi_bracket (h : ℕ) (hh : 0 < h) {ξ L : ℝ} (hx : 0 ≤ ξ * L) :
    ξ * L ≤ (Hxi h ξ L : ℝ) ∧ (Hxi h ξ L : ℝ) < ξ * L + h :=
  ⟨Hxi_ge h hh ξ L, Hxi_lt h hh hx⟩

/-- The statistical threshold controls the radius strictly: `m ≥ n_k` gives `2r_δ(m) < Δ/2`. -/
lemma two_rdelta_lt (L Δ : ℝ) (hL : 0 ≤ L) (hΔ : 0 < Δ) {m : ℕ} (hm : nk L Δ ≤ m) :
    2 * rdelta L m < Δ / 2 := by
  have hceil : 32 * L / Δ ^ 2 ≤ (nk L Δ : ℝ) := Nat.le_ceil _
  have hmR : 32 * L / Δ ^ 2 ≤ (m : ℝ) := le_trans hceil (by exact_mod_cast hm)
  have hΔ2 : 0 < Δ ^ 2 := pow_pos hΔ 2
  have h32 : 32 * L ≤ Δ ^ 2 * m := by
    rw [div_le_iff₀ hΔ2] at hmR; linarith
  have hfrac : L / (2 * m) ≤ Δ ^ 2 / 64 := by
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0
      rw [Nat.cast_zero, mul_zero, div_zero]
      positivity
    · have hmR0 : (0 : ℝ) < m := by exact_mod_cast hm0
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * m)]
      nlinarith [h32, hL, hmR0]
  have hsqrt : rdelta L m ≤ Δ / 8 := by
    rw [rdelta]
    have := Real.sqrt_le_sqrt hfrac
    have hs : Real.sqrt (Δ ^ 2 / 64) = Δ / 8 := by
      rw [Real.sqrt_div (by positivity), Real.sqrt_sq_eq_abs, abs_of_pos hΔ]
      norm_num
    rwa [hs] at this
  linarith

namespace DecayModel

variable (M : DecayModel n K)

/-- The concentration event `E_δ` (Lemma A.1): the empirical mean of the first `m` personal pulls of
arm `k` is within `r_δ(m)` of the average of the corresponding conditional means. -/
def ConcEvent (L : ℝ) (bhat : Fin K → ℕ → ℝ) (p : Fin K → ℕ → ℝ) : Prop :=
  ∀ k m, 1 ≤ m →
    |bhat k m - (∑ s ∈ Finset.range m, p k (s + 1)) / m| ≤ rdelta L m

/-- `m⁰_k` exists: the average added value eventually drops below `Δ_k/2`. -/
lemma exists_psi_le_half {k : Fin K} (hk : k ≠ M.star) :
    ∃ m : ℕ, 1 ≤ m ∧ psi (M.f k) m ≤ M.gap k / 2 := by
  have hΔ : 0 < M.gap k / 2 := by have := M.gap_pos hk; linarith
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (psi_tendsto (M.f_tendsto k)) (M.gap k / 2) hΔ
  refine ⟨max N 1, le_max_right _ _, ?_⟩
  have hlt := hN (max N 1) (le_max_left _ _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (psi_nonneg (fun s _ => M.f_nonneg k s) _)] at hlt
  exact le_of_lt hlt

/-- Threshold `m⁰_k = min{m ≥ 1 : ψ_k(m) ≤ Δ_k/2}`. -/
def m0 (k : Fin K) (hk : k ≠ M.star) : ℕ := Nat.find (M.exists_psi_le_half hk)

lemma m0_spec {k : Fin K} (hk : k ≠ M.star) :
    1 ≤ M.m0 k hk ∧ psi (M.f k) (M.m0 k hk) ≤ M.gap k / 2 :=
  Nat.find_spec (M.exists_psi_le_half hk)

/-- Threshold `m_k = max m⁰_k n_k`. -/
def mkThr (L : ℝ) (k : Fin K) (hk : k ≠ M.star) : ℕ := max (M.m0 k hk) (nk L (M.gap k))

/-- Lemma A.2, core inequality: on `E_δ`, if arm `k⋆` is available and the suboptimal arm `k` is
selected after `m` prior pulls (with `m_s` prior pulls of `k⋆`), then
`Δ_k ≤ ψ_k(m) + 2 r_δ(m)`. -/
theorem lemma_A2 {L : ℝ} {bhat : Fin K → ℕ → ℝ} {p : Fin K → ℕ → ℝ}
    (hp : M.AdaptMeanInGap p) (hc : ConcEvent L bhat p)
    {k : Fin K} {m ms : ℕ} (hm : 1 ≤ m) (hms : 1 ≤ ms)
    (hsel : bhat M.star ms + rdelta L ms ≤ bhat k m + rdelta L m) :
    M.gap k ≤ psi (M.f k) m + 2 * rdelta L m := by
  have hUk : bhat k m + rdelta L m ≤ M.b k + psi (M.f k) m + 2 * rdelta L m := by
    have h1 := (abs_le.mp (hc k m hm)).2
    have h2 : (∑ s ∈ Finset.range m, p k (s + 1)) / m ≤ M.b k + psi (M.f k) m :=
      (prefix_bounds M hp (k := k) hm).2
    linarith
  have hUs : M.b M.star ≤ bhat M.star ms + rdelta L ms := by
    have h1 := (abs_le.mp (hc M.star ms hms)).1
    have h2 : M.b M.star ≤ (∑ s ∈ Finset.range ms, p M.star (s + 1)) / ms :=
      (prefix_bounds M hp (k := M.star) hms).1
    linarith
  have hmid : M.b M.star ≤ M.b k + psi (M.f k) m + 2 * rdelta L m :=
    le_trans hUs (le_trans hsel hUk)
  rw [gap]
  linarith

/-- Lemma A.2, threshold form: on `E_δ`, once `m ≥ m_k` the suboptimal arm `k ≠ k⋆` is never
selected (the selection inequality is contradicted in the strict sense). -/
theorem not_selected_of_ge_mk {L : ℝ} {bhat : Fin K → ℕ → ℝ} {p : Fin K → ℕ → ℝ}
    (hp : M.AdaptMeanInGap p) (hc : ConcEvent L bhat p) (hL : 0 ≤ L)
    {k : Fin K} (hk : k ≠ M.star) {m ms : ℕ} (hm : 1 ≤ m) (hms : 1 ≤ ms)
    (hmk : M.mkThr L k hk ≤ m)
    (hsel : bhat M.star ms + rdelta L ms ≤ bhat k m + rdelta L m) : False := by
  have hcore := M.lemma_A2 hp hc hm hms hsel
  have hm0 : M.m0 k hk ≤ m := le_trans (le_max_left _ _) hmk
  have hnk : nk L (M.gap k) ≤ m := le_trans (le_max_right _ _) hmk
  have h1 : psi (M.f k) m ≤ M.gap k / 2 := by
    exact le_trans (psi_anti_le (M.f_anti k) (M.m0_spec hk).1 hm0) (M.m0_spec hk).2
  have h2 : 2 * rdelta L m < M.gap k / 2 := two_rdelta_lt L (M.gap k) hL (M.gap_pos hk) hnk
  linarith

end DecayModel

end AnvBandit
