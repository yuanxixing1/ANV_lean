import Mathlib

/-!
# Deterministic prefix averages (Lemma A.1, deterministic part)

For a nonnegative, nonincreasing sequence `f : ℕ → ℝ` (with `f s` the value at the `s`-th use,
`s ≥ 1`) define

* `Phi f m = ∑_{s=1}^{m} f s`  (accumulated added value, paper's `Φ_k(m)`),
* `psi f m = Phi f m / m`      (average added value, paper's `ψ_k(m)`).

This file proves the deterministic content of Lemma A.1: `psi f` is nonnegative, nonincreasing,
bounded by `f 1`, and tends to `0`.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace AnvBandit

/-- Accumulated added value `Φ_f(m) = ∑_{s=1}^{m} f s`. -/
def Phi (f : ℕ → ℝ) (m : ℕ) : ℝ := ∑ s ∈ Finset.range m, f (s + 1)

/-- Average added value `ψ_f(m) = Φ_f(m) / m`. -/
def psi (f : ℕ → ℝ) (m : ℕ) : ℝ := Phi f m / m

@[simp] lemma Phi_zero (f : ℕ → ℝ) : Phi f 0 = 0 := by simp [Phi]

lemma Phi_succ (f : ℕ → ℝ) (m : ℕ) : Phi f (m + 1) = Phi f m + f (m + 1) := by
  simp [Phi, Finset.sum_range_succ]

lemma Phi_nonneg {f : ℕ → ℝ} (hf : ∀ s, 1 ≤ s → 0 ≤ f s) (m : ℕ) : 0 ≤ Phi f m :=
  Finset.sum_nonneg fun s _ => hf (s + 1) (by omega)

lemma psi_nonneg {f : ℕ → ℝ} (hf : ∀ s, 1 ≤ s → 0 ≤ f s) (m : ℕ) : 0 ≤ psi f m := by
  rw [psi]
  exact div_nonneg (Phi_nonneg hf m) (by positivity)

lemma psi_le_first {f : ℕ → ℝ} (hanti : Antitone f) (hf0 : 0 ≤ f 1) (m : ℕ) :
    psi f m ≤ f 1 := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [psi, Phi, Finset.range_zero, Finset.sum_empty, zero_div]
    exact hf0
  · rw [psi, div_le_iff₀ (by exact_mod_cast hm)]
    calc Phi f m = ∑ s ∈ Finset.range m, f (s + 1) := rfl
      _ ≤ ∑ _s ∈ Finset.range m, f 1 := by
            apply Finset.sum_le_sum; intro s _
            exact hanti (by omega)
      _ = f 1 * (m : ℝ) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- `ψ_f` is nonincreasing (Lemma A.1: `ψ_k(m+1) ≤ ψ_k(m)`). -/
lemma psi_anti {f : ℕ → ℝ} (hanti : Antitone f) :
    ∀ m, 1 ≤ m → psi f (m + 1) ≤ psi f m := by
  intro m hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hle : f (m + 1) ≤ psi f m := by
    have hmul : (m : ℝ) * f (m + 1) ≤ Phi f m := by
      calc (m : ℝ) * f (m + 1) = ∑ _s ∈ Finset.range m, f (m + 1) := by
              simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ s ∈ Finset.range m, f (s + 1) := by
              apply Finset.sum_le_sum; intro s hs
              exact hanti (by have := Finset.mem_range.mp hs; omega)
        _ = Phi f m := rfl
    rw [psi, le_div_iff₀ hmpos]
    nlinarith [hmul]
  have hPhi : Phi f m = (m : ℝ) * psi f m := by
    rw [psi, mul_div_cancel₀ _ hmpos.ne']
  have hden : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  calc psi f (m + 1) = (Phi f m + f (m + 1)) / ((m : ℝ) + 1) := by
          rw [psi, Phi_succ, hden]
    _ ≤ (Phi f m + psi f m) / ((m : ℝ) + 1) := by
          apply div_le_div_of_nonneg_right _ (by positivity); linarith
    _ = psi f m := by
          rw [hPhi]; field_simp; try ring

/-- `ψ_f → 0` (Lemma A.1). -/
lemma psi_tendsto {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0)) :
    Tendsto (psi f) atTop (𝓝 0) := by
  have hg : Tendsto (fun i => f (i + 1)) atTop (𝓝 0) := hf.comp (tendsto_add_atTop_nat 1)
  have hc := hg.cesaro
  change Tendsto (fun m => Phi f m / m) atTop (𝓝 0)
  simp only [Phi]
  simpa [div_eq_inv_mul] using hc

/-- `ψ_f` is nonincreasing on the index cutoff: `m ≤ u`, `m ≥ 1` gives `ψ_f(u) ≤ ψ_f(m)`. -/
lemma psi_anti_le {f : ℕ → ℝ} (hanti : Antitone f) {m u : ℕ} (hm : 1 ≤ m) (hmu : m ≤ u) :
    psi f u ≤ psi f m := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmu
  induction j with
  | zero => simp
  | succ j ih =>
      rw [show m + (j + 1) = (m + j) + 1 by omega]
      exact le_trans (psi_anti hanti (m + j) (by omega)) (ih (by omega))

end AnvBandit
