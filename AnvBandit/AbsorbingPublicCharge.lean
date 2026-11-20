import AnvBandit.AbsorbingCharge
import AnvBandit.ActualPublicBudget

/-! Public-error charging uses the shared positive-part area once, across all
charged phases and nodes; the endpoint event is chosen before first failure. -/
noncomputable section
open scoped BigOperators Classical
open Finset
namespace AnvBandit.Absorbing
open Execution ExecutionLaw ExecutionBounds
variable {n K : ℕ} {Ω : Type*}

def unitCost (M : DecayModel n K) (k : Fin K) : ℝ := if k = M.star then 0 else 1

lemma unitCost_nonneg (M : DecayModel n K) (k : Fin K) : 0 ≤ unitCost M k := by
  unfold unitCost
  split_ifs <;> norm_num

lemma unitCost_others (M : DecayModel n K) {k : Fin K} (hk : k ∈ M.others) : unitCost M k = 1 := by
  have hne : k ≠ M.star := by simpa [DecayModel.others] using hk
  simp [unitCost, hne]

/-- C.9 with the personal budget, in the exact paper's real-valued constants. -/
theorem actual_error_budget_personal_real (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n)
    (ω : Ω) (Ph : ℕ) :
    (∑ ℓ ∈ erroneousPhases M p lam X J ω Ph, (p.phaseEnd ℓ-p.phaseEnd (ℓ-1) : ℕ) : ℝ) ≤
      2 * (n * M.Wsum (unitCost M) p.L) := by
  have h := actual_error_budget_personal M p lam X J ω Ph
  have he : M.Wsum (unitCost M) p.L = ∑ k ∈ M.others, (M.mkAll p.L k : ℝ) := by
    unfold DecayModel.Wsum DecayModel.wk
    apply sum_congr rfl
    intro k hk
    rw [unitCost_others M hk, one_mul]
  rw [he]
  have h' : (∑ ℓ ∈ erroneousPhases M p lam X J ω Ph, (p.phaseEnd ℓ-p.phaseEnd (ℓ-1))) ≤
      2 * (n * ∑ k ∈ M.others, M.mkAll p.L k) := by simpa [Nat.mul_assoc] using h
  exact_mod_cast h'

/-- Public C.9, on every path: both the personal and public alternatives are
proved, hence their exact minimum is preserved. -/
theorem actual_error_budget_public (M : DecayModel n K) (p : Params n K)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n)
    (ω : Ω) (Ph : ℕ) :
    (∑ ℓ ∈ erroneousPhases M p 1 X J ω Ph, (p.phaseEnd ℓ-p.phaseEnd (ℓ-1) : ℕ) : ℝ) ≤
      2 * M.Flam (unitCost M) p.L 1 := by
  let F := erroneousPhases M p 1 X J ω Ph
  have hpos : ∀ ℓ ∈ F, 1 ≤ ℓ := fun ℓ hℓ => (mem_filter.mp hℓ).2.1
  have hlive : ∀ ℓ ∈ F, live M p 1 X J ℓ ω := fun ℓ hℓ => (mem_filter.mp hℓ).2.2.1
  have hwrong : ∀ ℓ ∈ F, wrong M.star (preBoundary p (realTape (X ω)) (J ω) ℓ) :=
    fun ℓ hℓ => (mem_filter.mp hℓ).2.2.2
  have hc := erroneous_phases_charge M p (realTape (X ω)) (J ω) F hpos
    (fun ℓ hℓ => (hlive ℓ hℓ).1.le) hwrong
  have hpub := ActualPublicBudget.weighted_selected_pairs_bound M p X J ω (unitCost M)
    (unitCost_nonneg M) (univ ×ˢ M.others)
    (by intro z hz; simpa [DecayModel.others] using (mem_product.mp hz).2)
    (chargedTimes M p (realTape (X ω)) (J ω) F)
    (by intro z hz t ht; exact chargedTimes_spec M p 1 X J ω F hpos hlive z.1 z.2 t ht)
  rw [sum_product, sum_product] at hpub
  have heq : (∑ i : Fin n, ∑ k ∈ M.others,
      unitCost M k * (M.nkAll p.L k : ℝ)) = n * M.WNsum (unitCost M) p.L := by
    simp [DecayModel.WNsum, DecayModel.wkN]
  rw [heq] at hpub
  have hsum : (∑ i : Fin n, ∑ k ∈ M.others,
      unitCost M k * ((chargedTimes M p (realTape (X ω)) (J ω) F i k).card : ℝ)) =
      ∑ i : Fin n, ∑ k ∈ M.others,
        ((chargedTimes M p (realTape (X ω)) (J ω) F i k).card : ℝ) := by
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro k hk
    rw [unitCost_others M hk, one_mul]
  rw [hsum] at hpub
  have hcR : (∑ ℓ ∈ F, (p.phaseEnd ℓ-p.phaseEnd (ℓ-1) : ℕ) : ℝ) ≤
      2 * ∑ i : Fin n, ∑ k ∈ M.others,
        ((chargedTimes M p (realTape (X ω)) (J ω) F i k).card : ℝ) := by exact_mod_cast hc
  have hp := actual_error_budget_personal_real M p 1 X J ω Ph
  change _ ≤ 2 * min _ _
  have hb := hcR.trans (mul_le_mul_of_nonneg_left hpub (by norm_num : (0:ℝ) ≤ 2))
  rcases le_total ((n : ℝ) * M.Wsum (unitCost M) p.L)
    ((n : ℝ) * M.WNsum (unitCost M) p.L + M.Bpub (unitCost M)) with hle | hle
  · rw [min_eq_left hle]
    exact hp
  · rw [min_eq_right hle]
    exact hb

end AnvBandit.Absorbing
