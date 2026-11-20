import AnvBandit.ActualExplicit
import AnvBandit.Execution

noncomputable section
namespace AnvBandit

lemma deltaStar_legal {T : ℕ} (hT : 1 ≤ T) : 0 < deltaStar T ∧ deltaStar T < 1 := by
  have ht : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have he : deltaStar T = (((T : ℝ) + 1)^2)⁻¹ := by
    simp [deltaStar, zpow_neg, zpow_ofNat]
  rw [he]
  constructor
  · positivity
  · exact (inv_lt_one₀ (by positivity)).mpr (by nlinarith)

lemma Ldelta_deltaStar_eq (n K T : ℕ) : Ldelta n K T (deltaStar T) = LdeltaStar n K T := by
  unfold Ldelta LdeltaStar deltaStar
  simp only [zpow_neg, zpow_ofNat, div_inv_eq_mul, Nat.cast_mul]
  congr 1
  ring

namespace Execution
variable {n K : ℕ}

/-- The paper's horizon-dependent confidence parameter with an arbitrary legal scale. -/
def confidenceParams (M : DecayModel n K) (T h H : ℕ) (β : ℝ)
    (hT : 1 ≤ T) (hh : 1 ≤ h) (hH : 1 ≤ H) (hdiv : h ∣ H) (hβ : 1 < β) : Params n K where
  hn := M.two_le_n
  hK := M.two_le_K
  T := T
  hT := hT
  h := h
  hh := hh
  H := H
  hH := hH
  hdiv := hdiv
  δ := deltaStar T
  hδ := deltaStar_legal hT
  β := β
  hβ := hβ

@[simp] lemma confidenceParams_L (M : DecayModel n K) (T h H : ℕ) (β : ℝ)
    (hT : 1 ≤ T) (hh : 1 ≤ h) (hH : 1 ≤ H) (hdiv : h ∣ H) (hβ : 1 < β) :
    (confidenceParams M T h H β hT hh hH hdiv hβ).L = LdeltaStar n K T :=
  Ldelta_deltaStar_eq n K T

/-- The exact proposed `Hξ` is legal without any restriction `H≤T` or `T≤H`. -/
def explicitParams (M : DecayModel n K) (T h : ℕ) (ξ β : ℝ)
    (hT : 1 ≤ T) (hh : 1 ≤ h) (hξ : 0 < ξ) (hβ : 1 < β) : Params n K :=
  confidenceParams M T h (Hxi h ξ (LdeltaStar n K T)) β hT hh
    (legal_Hxi hh hξ (lt_of_lt_of_le (Lstar_pos
      (by have := M.two_le_n; omega) (by have := M.two_le_K; omega))
      (Lstar_le_LdeltaStar (by have := M.two_le_n; omega) (by have := M.two_le_K; omega) hT))).1
    (legal_Hxi hh hξ (lt_of_lt_of_le (Lstar_pos
      (by have := M.two_le_n; omega) (by have := M.two_le_K; omega))
      (Lstar_le_LdeltaStar (by have := M.two_le_n; omega) (by have := M.two_le_K; omega) hT))).2.1 hβ

@[simp] lemma explicitParams_L (M : DecayModel n K) (T h : ℕ) (ξ β : ℝ)
    (hT : 1 ≤ T) (hh : 1 ≤ h) (hξ : 0 < ξ) (hβ : 1 < β) :
    (explicitParams M T h ξ β hT hh hξ hβ).L = LdeltaStar n K T := by
  simp [explicitParams]

end Execution
end AnvBandit
