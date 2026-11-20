import AnvBandit.RemainingWait

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Finset Filter
namespace AnvBandit
variable {n : ℕ} {hd : 0 < n-1}

lemma lintegral_remaining_ne_top (hn : 2 ≤ n) (C : ContactMatrix n)
    (i0 i : Fin n) (j : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (max (sigmaR hd ω i0 i - j) 0)
      ∂procMeasure C (n-1)) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (lintegral_sigmaR_ne_top hn C
    (ReachData.ofIrreducible C.irreducible i0) i)
  apply lintegral_mono
  intro ω
  apply ENNReal.ofReal_le_ofReal
  exact max_le (sub_le_self _ (Nat.cast_nonneg j)) (sigmaR_nonneg hd ω i0 i)

lemma lintegral_sigmaAllE_remaining (hn : 2 ≤ n) (C : ContactMatrix n)
    (i0 i : Fin n) (j : ℕ) :
    (∫⁻ R, sigmaAllE R {i0} i - j ∂stepMeasure C) =
      ∫⁻ ω, ENNReal.ofReal (max (sigmaR hd ω i0 i - j) 0)
        ∂procMeasure C (n-1) := by
  rw [← unblock_measure hd C,
    lintegral_map (f := fun R => sigmaAllE R {i0} i - (j : ℝ≥0∞))
      ((measurable_sigmaAllE {i0} i).sub measurable_const) (measurable_unblock hd)]
  apply lintegral_congr_ae
  have hcomplete : ∀ᵐ ω ∂procMeasure C (n-1), Complete hd ω i0 := by
    rw [ae_iff]
    exact measure_Complete_compl_eq_zero hn C (ReachData.ofIrreducible C.irreducible i0)
  filter_upwards [hcomplete] with ω hω
  rw [sigmaAllE_unblock_eq_capped (Finset.mem_singleton_self i0) hω i]
  simp only [sigmaFrom_eq_sigmaStep, sigmaR, sigma,
    ENNReal.ofReal_max, ENNReal.ofReal_zero,
    ENNReal.ofReal_sub _ (Nat.cast_nonneg j), ENNReal.ofReal_natCast]
  exact (max_eq_left (show (0 : ℝ≥0∞) ≤ _ from bot_le)).symm

/-- The real ideal potential is integrable at every deterministic step. -/
theorem integrable_Vpot_inform (hn : 2 ≤ n) (C : ContactMatrix n)
    (i0 : Fin n) (j : ℕ) :
    Integrable (fun R => Vpot hd C i0 (Inform R {i0} j)) (stepMeasure C) := by
  apply (integrable_const (M1 hd C i0)).mono_nonneg
    (measurable_inform_function _ _ _).aestronglyMeasurable
  · exact Eventually.of_forall fun R => by
      unfold Vpot
      exact Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  · exact Eventually.of_forall fun R => Vpot_le_M1 hn C
      (ReachData.ofIrreducible C.irreducible i0)
      (subset_Inform R {i0} j (Finset.mem_singleton_self i0))

/-- Exact equation C.11 on the original iid contact law, with finite expectations. -/
theorem integral_Vpot_inform_eq_remainingV (hn : 2 ≤ n) (C : ContactMatrix n)
    (i0 : Fin n) (j : ℕ) :
    (∫ R, Vpot hd C i0 (Inform R {i0} j) ∂stepMeasure C) =
      remainingV hd C i0 j := by
  have hsource (R : ℕ → Fin n → Fin n) : i0 ∈ Inform R {i0} j :=
    subset_Inform R {i0} j (Finset.mem_singleton_self i0)
  simp_rw [Vpot_eq_toReal_VpotE hn C
    (ReachData.ofIrreducible C.irreducible i0) (hsource _)]
  rw [integral_toReal (measurable_inform_function _ _ _).aemeasurable
    (Eventually.of_forall fun R => lt_top_iff_ne_top.mpr
      (VpotE_ne_top hn C (ReachData.ofIrreducible C.irreducible i0) (hsource R))),
    lintegral_VpotE_inform]
  simp_rw [lintegral_sigmaAllE_remaining (hd := hd) hn C i0]
  exact ENNReal.toReal_sum fun i _ => lintegral_remaining_ne_top hn C i0 i j

end AnvBandit
