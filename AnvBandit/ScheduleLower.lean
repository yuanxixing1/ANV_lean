import AnvBandit.Constants

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.deprecated false

/-!
# Lemma B.3: the uniform reliable phase (deterministic schedule bound)

The schedule scale `H ∈ h·ℕ` gives stage endpoints `t_ℓ = H⌈ℓ^β⌉` (equation (3.5)) and lengths
`d_ℓ = t_ℓ − t_{ℓ−1}`.  This file proves Lemma B.3 genuinely:

* `rpow_sub_ge`: the mean-value bound `p a^{p−1}(b−a) ≤ b^p − a^p` for `a,b ≥ 0`, `p ≥ 1`;
* `nat_ceil_sub_ge`: the ceiling error bound `x − y − 1 ≤ ⌈x⌉₊ − ⌈y⌉₊` for `0 ≤ y ≤ x`;
* `dEll_lower`: `d_ℓ ≥ H(β(ℓ−1)^{β−1} − 1)`;
* `rH`: the last stage with `d_ℓ ≤ B` (bounded by `⌈u_H⌉`), and
* `lemma_B_3`: `rH H β B u_H ≤ ⌈u_H⌉` and `d_ℓ > B` for every `ℓ > rH`,
  where `u_H = ((B/H + 2)/β)^{1/(β−1)}`.
-/

noncomputable section
open scoped BigOperators Topology
open Filter Finset

namespace AnvBandit

/-- Mean-value lower bound for `x^p` on nonnegative reals: `p a^{p−1}(b−a) ≤ b^p − a^p`. -/
lemma rpow_sub_ge {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 1 ≤ p) :
    p * a ^ (p - 1) * (b - a) ≤ b ^ p - a ^ p := by
  rcases lt_trichotomy b a with hba | heq | hab
  · have hcont : ContinuousOn (fun x : ℝ => x ^ p) (Set.Icc b a) := fun x hx =>
      (continuousAt_id.rpow_const (Or.inr (by linarith : (0:ℝ) ≤ p))).continuousWithinAt
    have hdiff : DifferentiableOn ℝ (fun x : ℝ => x ^ p) (Set.Ioo b a) := fun x hx =>
      (DifferentiableAt.rpow_const differentiableAt_id (Or.inr hp)).differentiableWithinAt
    obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope (fun x : ℝ => x ^ p) hba hcont hdiff
    rw [Real.deriv_rpow_const] at hcd
    have hcp : c ^ (p - 1) ≤ a ^ (p - 1) :=
      Real.rpow_le_rpow (le_trans hb hc.1.le) hc.2.le (by linarith)
    have hab' : 0 < a - b := by linarith
    have h3 : p * c ^ (p - 1) * (a - b) = a ^ p - b ^ p := (eq_div_iff hab'.ne').mp hcd
    have hpa : 0 < p * (a - b) := by positivity
    have h4 : p * c ^ (p - 1) * (a - b) ≤ p * a ^ (p - 1) * (a - b) := by
      have := mul_le_mul_of_nonneg_right hcp hpa.le; linarith
    nlinarith [h3, h4, hpa, Real.rpow_nonneg ha (p - 1)]
  · subst heq; simp
  · have hcont : ContinuousOn (fun x : ℝ => x ^ p) (Set.Icc a b) := fun x hx =>
      (continuousAt_id.rpow_const (Or.inr (by linarith : (0:ℝ) ≤ p))).continuousWithinAt
    have hdiff : DifferentiableOn ℝ (fun x : ℝ => x ^ p) (Set.Ioo a b) := fun x hx =>
      (DifferentiableAt.rpow_const differentiableAt_id (Or.inr hp)).differentiableWithinAt
    obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope (fun x : ℝ => x ^ p) hab hcont hdiff
    rw [Real.deriv_rpow_const] at hcd
    have hcp : a ^ (p - 1) ≤ c ^ (p - 1) := Real.rpow_le_rpow ha hc.1.le (by linarith)
    have hba' : 0 < b - a := by linarith
    have h3 : p * c ^ (p - 1) * (b - a) = b ^ p - a ^ p := (eq_div_iff hba'.ne').mp hcd
    rw [← h3]
    have hpa : 0 < p * (b - a) := by positivity
    nlinarith [hcp, hpa, Real.rpow_nonneg ha (p - 1)]

/-- Ceiling error bound: `x − y − 1 ≤ ⌈x⌉₊ − ⌈y⌉₊` for `0 ≤ y ≤ x`. -/
lemma nat_ceil_sub_ge {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) :
    x - y - 1 ≤ (⌈x⌉₊ : ℝ) - ⌈y⌉₊ := by
  have h1 : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have h2 : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one hy
  linarith

/-- Stage-length lower bound `d_ℓ ≥ H(β(ℓ−1)^{β−1} − 1)`. -/
lemma dEll_lower {H β : ℝ} (hH : 0 < H) (hβ : 1 < β) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    H * (β * ((ℓ - 1 : ℕ) : ℝ) ^ (β - 1) - 1) ≤ dEll H β ℓ := by
  have hy : 0 ≤ ((ℓ - 1 : ℕ) : ℝ) ^ β := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hxy : ((ℓ - 1 : ℕ) : ℝ) ^ β ≤ (ℓ : ℝ) ^ β :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (show ℓ - 1 ≤ ℓ by omega)) (by linarith)
  have hceil := nat_ceil_sub_ge hy hxy
  have hrp := rpow_sub_ge (a := ((ℓ - 1 : ℕ) : ℝ)) (b := (ℓ : ℝ)) (p := β)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hβ.le
  have hcast : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by rw [Nat.cast_sub hℓ]; norm_num
  have hsub : ((ℓ : ℝ) - ((ℓ - 1 : ℕ) : ℝ)) = 1 := by rw [hcast]; ring
  rw [dEll, tEll, tEll]
  have hsplit : H * (⌈(ℓ : ℝ) ^ β⌉₊ : ℝ) - H * (⌈((ℓ - 1 : ℕ) : ℝ) ^ β⌉₊ : ℝ)
      = H * ((⌈(ℓ : ℝ) ^ β⌉₊ : ℝ) - ⌈((ℓ - 1 : ℕ) : ℝ) ^ β⌉₊) := by ring
  rw [hsplit]
  have hstep1 : (ℓ : ℝ) ^ β - ((ℓ - 1 : ℕ) : ℝ) ^ β - 1
      ≤ (⌈(ℓ : ℝ) ^ β⌉₊ : ℝ) - ⌈((ℓ - 1 : ℕ) : ℝ) ^ β⌉₊ := hceil
  have hstep2 : β * ((ℓ - 1 : ℕ) : ℝ) ^ (β - 1) ≤ (ℓ : ℝ) ^ β - ((ℓ - 1 : ℕ) : ℝ) ^ β := by
    have := hrp
    rwa [hsub, mul_one] at this
  nlinarith [hH, hstep1, hstep2]

/-- `rH`: the last stage index `ℓ ∈ [1, ⌈u_H⌉]` with `d_ℓ ≤ B` (zero if there is none). -/
def rH (H β B uH : ℝ) : ℕ :=
  ((Finset.Icc 1 ⌈uH⌉₊).filter (fun ℓ => dEll H β ℓ ≤ B)).sup (fun ℓ => ℓ)

/-- **Lemma B.3** (uniform reliable phase): with `u_H = ((B/H + 2)/β)^{1/(β−1)}`, the last failing
stage satisfies `rH ≤ ⌈u_H⌉`, and every stage `ℓ > rH` has `d_ℓ > B`. -/
theorem lemma_B_3 {H β B uH : ℝ} (hH : 0 < H) (hβ : 1 < β) (hB : 0 ≤ B)
    (huH : uH = ((B / H + 2) / β) ^ (1 / (β - 1))) :
    rH H β B uH ≤ ⌈uH⌉₊ ∧ ∀ ℓ : ℕ, rH H β B uH < ℓ → B < dEll H β ℓ := by
  have hBe : 0 ≤ B / H + 2 := by
    have : 0 ≤ B / H := div_nonneg hB hH.le; linarith
  have hβpos : 0 < β := by linarith
  have hbase : 0 ≤ (B / H + 2) / β := div_nonneg hBe hβpos.le
  have huHnn : 0 ≤ uH := by rw [huH]; exact Real.rpow_nonneg hbase _
  have huHpow : uH ^ (β - 1) = (B / H + 2) / β := by
    rw [huH, ← Real.rpow_mul hbase]
    have hβ1 : β - 1 ≠ 0 := by linarith
    rw [one_div, inv_mul_cancel₀ hβ1, Real.rpow_one]
  constructor
  · -- `rH ≤ ⌈uH⌉`
    unfold rH
    apply Finset.sup_le
    intro ℓ hℓ
    exact (Finset.mem_Icc.mp (Finset.mem_of_mem_filter ℓ hℓ)).2
  · intro ℓ hℓgt
    by_contra hcon
    push_neg at hcon
    rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
    · subst h0; omega
    · -- ℓ ≥ 1: split on ℓ ≤ ⌈uH⌉
      by_cases hcase : ℓ ≤ ⌈uH⌉₊
      · -- ℓ ∈ [1, ⌈uH⌉] with d_ℓ ≤ B, so ℓ ≤ rH
        have hmem : ℓ ∈ (Finset.Icc 1 ⌈uH⌉₊).filter (fun ℓ => dEll H β ℓ ≤ B) := by
          rw [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨hpos, hcase⟩, hcon⟩
        have : ℓ ≤ rH H β B uH := by
          unfold rH
          exact Finset.le_sup (f := fun ℓ => ℓ) hmem
        omega
      · -- ℓ > ⌈uH⌉: use the analytic lower bound
        have hlt : ⌈uH⌉₊ < ℓ := by omega
        have hge : uH ≤ ((ℓ - 1 : ℕ) : ℝ) := by
          have h1 : uH ≤ (⌈uH⌉₊ : ℝ) := Nat.le_ceil uH
          have h2 : (⌈uH⌉₊ : ℝ) ≤ ((ℓ - 1 : ℕ) : ℝ) := by
            have : ⌈uH⌉₊ ≤ ℓ - 1 := by omega
            exact_mod_cast this
          linarith
        have hrpow : uH ^ (β - 1) ≤ ((ℓ - 1 : ℕ) : ℝ) ^ (β - 1) :=
          Real.rpow_le_rpow huHnn hge (by linarith)
        have hlow := dEll_lower hH hβ hpos
        have hkey : B < H * (β * uH ^ (β - 1) - 1) := by
          rw [huHpow]
          have : β * ((B / H + 2) / β) = B / H + 2 := by field_simp
          rw [this]
          have : H * (B / H + 2 - 1) = B + H := by field_simp; ring
          rw [this]; linarith
        have hmono : H * (β * uH ^ (β - 1) - 1) ≤ H * (β * ((ℓ - 1 : ℕ) : ℝ) ^ (β - 1) - 1) := by
          have := mul_le_mul_of_nonneg_left hrpow hβpos.le
          nlinarith [hH]
        linarith [hlow, hkey, hmono]

/-- Paper definition of the last short phase, including zero when no positive phase fails. -/
def lastShortPhase (H β B : ℝ) : ℕ :=
  sSup {ℓ : ℕ | ℓ = 0 ∨ (1 ≤ ℓ ∧ dEll H β ℓ ≤ B)}

/-- The finite search is exactly the paper's unbounded last-short-phase definition.
The analytic tail estimate, not an assumed monotonicity of rounded phase lengths, closes the tail. -/
theorem rH_eq_last_short_phase {H β B uH : ℝ}
    (hH : 0 < H) (hβ : 1 < β) (hB : 0 ≤ B)
    (huH : uH = ((B / H + 2) / β) ^ (1 / (β - 1))) :
    rH H β B uH = lastShortPhase H β B := by
  have hrel := (lemma_B_3 hH hβ hB huH).2
  have hupper : ∀ ℓ ∈ {ℓ : ℕ | ℓ = 0 ∨ (1 ≤ ℓ ∧ dEll H β ℓ ≤ B)},
      ℓ ≤ rH H β B uH := by
    intro ℓ hℓ
    rcases hℓ with hzero | ⟨_, hshort⟩
    · subst ℓ; exact Nat.zero_le _
    · by_contra hnot
      exact (not_lt_of_ge hshort) (hrel ℓ (Nat.lt_of_not_ge hnot))
  have hbounded : BddAbove {ℓ : ℕ | ℓ = 0 ∨ (1 ≤ ℓ ∧ dEll H β ℓ ≤ B)} :=
    ⟨rH H β B uH, hupper⟩
  apply le_antisymm
  · unfold rH
    apply Finset.sup_le
    intro ℓ hℓ
    obtain ⟨hIcc, hshort⟩ := Finset.mem_filter.mp hℓ
    exact le_csSup hbounded (Or.inr ⟨(Finset.mem_Icc.mp hIcc).1, hshort⟩)
  · exact csSup_le ⟨0, Or.inl rfl⟩ hupper

/-- The reliable-phase lemma with the exact subset budget, not its coarse maximum-arm bound. -/
theorem reliable_phase_exact_budget {n K : ℕ} (M : DecayModel n K) (L : ℝ)
    {H β : ℝ} (hH : 0 < H) (hβ : 1 < β) :
    let B : ℝ := M.Bschedule L
    let u := ((B / H + 2) / β) ^ (1 / (β - 1))
    rH H β B u = lastShortPhase H β B ∧
      rH H β B u ≤ ⌈u⌉₊ ∧ ∀ ℓ, rH H β B u < ℓ → B < dEll H β ℓ := by
  dsimp
  exact ⟨rH_eq_last_short_phase hH hβ (Nat.cast_nonneg _) rfl,
    lemma_B_3 hH hβ (Nat.cast_nonneg _) rfl⟩

end AnvBandit
