import AnvBandit.RemainingWaitReal

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Finset Filter
namespace AnvBandit
variable {n : ℕ} {hd : 0 < n-1}

lemma remainingV_eq_block_potential (hn : 2 ≤ n) (C : ContactMatrix n)
    (i0 : Fin n) (j : ℕ) :
    remainingV hd C i0 j = ∫ ω,
      Vpot hd C i0 (Inform (unblock hd ω) {i0} j) ∂procMeasure C (n-1) := by
  rw [← integral_Vpot_inform_eq_remainingV hn C i0 j, ← unblock_measure hd C]
  exact integral_map_of_stronglyMeasurable (measurable_unblock hd)
    (measurable_inform_function _ _ _).stronglyMeasurable

/-- A coarse geometric bound sufficient for summability. This is not asserted to
be the sharper tail-sum constant printed in Appendix C.2. -/
theorem remainingV_le_completion_tail (hn : 2 ≤ n) (C : ContactMatrix n)
    (i0 : Fin n) (j : ℕ) :
    remainingV hd C i0 j ≤ M1 hd C i0 *
      Real.exp 1 * Real.exp (-(epsP C * ((j : ℝ) / ((n : ℝ)-1)))) := by
  let μ := procMeasure C (n-1)
  let s : Set (ℕ → Fin (n-1) → Fin n → Fin n) :=
    {ω | (j : ℝ) < (tau hd ω i0 : ℝ)}
  have hs : MeasurableSet s := measurableSet_lt measurable_const (measurable_tau_real hd i0)
  have hM : 0 ≤ M1 hd C i0 := by
    unfold M1
    exact Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hf : Integrable (fun ω => Vpot hd C i0 (Inform (unblock hd ω) {i0} j)) μ := by
    apply (integrable_const (M1 hd C i0)).mono_nonneg
      ((measurable_inform_function (Vpot hd C i0) {i0} j).comp
        (measurable_unblock hd)).aestronglyMeasurable
    · exact Eventually.of_forall fun ω => by
        unfold Vpot
        exact Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
    · exact Eventually.of_forall fun ω => Vpot_le_M1 hn C
        (ReachData.ofIrreducible C.irreducible i0)
        (subset_Inform _ {i0} j (Finset.mem_singleton_self i0))
  have hcomplete : ∀ᵐ ω ∂μ, Complete hd ω i0 := by
    rw [ae_iff]
    exact measure_Complete_compl_eq_zero hn C (ReachData.ofIrreducible C.irreducible i0)
  have hpoint : ∀ᵐ ω ∂μ, Vpot hd C i0 (Inform (unblock hd ω) {i0} j) ≤
      s.indicator (fun _ => M1 hd C i0) ω := by
    filter_upwards [hcomplete] with ω hω
    by_cases h : ω ∈ s
    · rw [Set.indicator_of_mem h]
      exact Vpot_le_M1 hn C (ReachData.ofIrreducible C.irreducible i0)
        (subset_Inform _ {i0} j (Finset.mem_singleton_self i0))
    · rw [Set.indicator_of_notMem h]
      have ht : tau hd ω i0 ≤ j := by
        have : ¬ (j : ℝ) < (tau hd ω i0 : ℝ) := h
        exact_mod_cast le_of_not_gt this
      have hfull : Inform (unblock hd ω) {i0} j = Finset.univ := by
        apply Finset.eq_univ_of_forall
        intro i
        apply Inform_mono_le _ {i0} (tau hd ω i0) ht
        rw [Inform_tau_eq_univ hω]
        exact Finset.mem_univ i
      rw [hfull, Vpot_univ]
  rw [remainingV_eq_block_potential hn C i0 j]
  have hb := integral_mono_ae hf ((integrable_const (M1 hd C i0)).indicator hs) hpoint
  rw [integral_indicator_const _ hs] at hb
  have hp := ENNReal.toReal_mono (ENNReal.ofReal_ne_top)
    (measure_tau_gt_real_le hn C (ReachData.ofIrreducible C.irreducible i0)
      (x := (j : ℝ)) (Nat.cast_nonneg j))
  rw [ENNReal.toReal_ofReal (by positivity)] at hp
  simp only [smul_eq_mul] at hb
  have hp' : μ.real s ≤ Real.exp 1 *
      Real.exp (-(epsP C * ((j : ℝ) / ((n : ℝ)-1)))) := hp
  calc
    _ ≤ μ.real s * M1 hd C i0 := hb
    _ ≤ (Real.exp 1 * Real.exp (-(epsP C * ((j : ℝ) / ((n : ℝ)-1))))) *
        M1 hd C i0 := mul_le_mul_of_nonneg_right hp' hM
    _ = _ := by ring

end AnvBandit
