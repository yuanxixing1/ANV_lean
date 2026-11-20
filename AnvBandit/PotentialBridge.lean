import AnvBandit.IdealV

/-!
# Identification of the block and step propagation potentials

The block potential is capped by the single-source completion time, while the
step potential uses extended delays. The cap is removed only on the almost-sure
completion event. Finiteness is then transported through `unblock_measure` before
any conversion to real numbers.
-/

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Finset Filter

namespace AnvBandit

variable {n : ℕ} {hd : 0 < n - 1}

/-- Every node is reached almost surely from any set containing the source.
The statement retains the genuine finite-arrival event, before any real conversion. -/
theorem finite_arrival_ae (hn : 2 ≤ n) (C : ContactMatrix n)
    {i0 : Fin n} (R0 : ReachData C.P i0) {A : Finset (Fin n)}
    (hA : i0 ∈ A) :
    ∀ᵐ R ∂stepMeasure C, ∀ i : Fin n, ∃ t, i ∈ Inform R A t := by
  filter_upwards [stepMeasure_completeStep_ae hn C R0] with R hR
  rcases hR with ⟨t, ht⟩
  intro i
  refine ⟨t, ?_⟩
  exact Inform_mono R (Finset.singleton_subset_iff.mpr hA) t
    (by rw [ht]; exact Finset.mem_univ i)

/-- On an actually completing path the capped block delay is the genuine extended
step delay, for any informed set containing the source. -/
lemma sigmaAllE_unblock_eq_capped {ω : ℕ → Fin (n - 1) → Fin n → Fin n}
    {i0 : Fin n} {A : Finset (Fin n)} (hA : i0 ∈ A)
    (hC : Complete hd ω i0) (i : Fin n) :
    sigmaAllE (unblock hd ω) A i =
      ENNReal.ofReal ((min (sigmaFrom hd ω A i) (tau hd ω i0) : ℕ) : ℝ) := by
  have hex : ∃ t, i ∈ Inform (unblock hd ω) A t := by
    refine ⟨tau hd ω i0, ?_⟩
    exact Inform_mono (unblock hd ω) (Finset.singleton_subset_iff.mpr hA) _
      (by rw [Inform_tau_eq_univ hC]; exact Finset.mem_univ i)
  rw [sigmaAllE_of_nonempty hex, min_eq_left (sigmaFrom_le_tau hA hC)]
  simp only [sigmaAll, sigmaFrom, ENNReal.ofReal_natCast]

/-- Exact equality of the nodewise integrals, with no arbitrary default value on
the noncompletion event contributing to either side. -/
theorem lintegral_sigmaAllE_eq_capped (hn : 2 ≤ n) (C : ContactMatrix n)
    {i0 : Fin n} (R0 : ReachData C.P i0) {A : Finset (Fin n)}
    (hA : i0 ∈ A) (i : Fin n) :
    (∫⁻ R, sigmaAllE R A i ∂stepMeasure C) =
      ∫⁻ ω, ENNReal.ofReal ((min (sigmaFrom hd ω A i) (tau hd ω i0) : ℕ) : ℝ)
        ∂procMeasure C (n - 1) := by
  rw [← unblock_measure hd C,
    lintegral_map (measurable_sigmaAllE A i) (measurable_unblock hd)]
  apply lintegral_congr_ae
  have hcomplete : ∀ᵐ ω ∂procMeasure C (n - 1), Complete hd ω i0 := by
    rw [ae_iff]
    exact measure_Complete_compl_eq_zero hn C R0
  filter_upwards [hcomplete] with ω hω
  exact sigmaAllE_unblock_eq_capped hA hω i

/-- Each true expected step delay is finite, derived from the proven completion
moment bound rather than from `toReal` at infinity. -/
theorem lintegral_sigmaAllE_ne_top (hn : 2 ≤ n) (C : ContactMatrix n)
    {i0 : Fin n} (R0 : ReachData C.P i0) {A : Finset (Fin n)}
    (hA : i0 ∈ A) (i : Fin n) :
    (∫⁻ R, sigmaAllE R A i ∂stepMeasure C) ≠ ⊤ := by
  rw [lintegral_sigmaAllE_eq_capped (hd := by omega) hn C R0 hA i]
  exact lintegral_min_ne_top hn C R0 A i

theorem VpotE_ne_top (hn : 2 ≤ n) (C : ContactMatrix n)
    {i0 : Fin n} (R0 : ReachData C.P i0) {A : Finset (Fin n)}
    (hA : i0 ∈ A) : VpotE C A ≠ ⊤ := by
  unfold VpotE
  exact ENNReal.sum_ne_top.mpr fun i _ => lintegral_sigmaAllE_ne_top hn C R0 hA i

/-- The two previously separate definitions are the same finite potential. -/
theorem Vpot_eq_toReal_VpotE (hn : 2 ≤ n) (C : ContactMatrix n)
    {i0 : Fin n} (R0 : ReachData C.P i0) {A : Finset (Fin n)}
    (hA : i0 ∈ A) : Vpot hd C i0 A = (VpotE C A).toReal := by
  unfold Vpot VpotE
  rw [ENNReal.toReal_sum (fun i _ => lintegral_sigmaAllE_ne_top hn C R0 hA i)]
  exact Finset.sum_congr rfl fun i _ => congrArg ENNReal.toReal
    (lintegral_sigmaAllE_eq_capped (hd := hd) hn C R0 hA i).symm

/-- The reverse conversion explicitly uses the previously proved finiteness. -/
theorem VpotE_eq_ofReal_Vpot (hn : 2 ≤ n) (C : ContactMatrix n)
    {i0 : Fin n} (R0 : ReachData C.P i0) {A : Finset (Fin n)}
    (hA : i0 ∈ A) : VpotE C A = ENNReal.ofReal (Vpot hd C i0 A) := by
  rw [Vpot_eq_toReal_VpotE hn C R0 hA,
    ENNReal.ofReal_toReal (VpotE_ne_top hn C R0 hA)]

/-- The cap's chosen source does not change the potential on sets containing
both sources. This follows from equality to the same uncapped step potential. -/
theorem Vpot_source_independent (hn : 2 ≤ n) (C : ContactMatrix n)
    {i0 i1 : Fin n} {A : Finset (Fin n)} (h0 : i0 ∈ A) (h1 : i1 ∈ A) :
    Vpot hd C i0 A = Vpot hd C i1 A := by
  rw [Vpot_eq_toReal_VpotE hn C (ReachData.ofIrreducible C.irreducible i0) h0,
    Vpot_eq_toReal_VpotE hn C (ReachData.ofIrreducible C.irreducible i1) h1]

/-- The one-step extended expectation is finite, by the exact recursion and the
finite original potential. -/
theorem lintegral_VpotE_infStep_ne_top (hn : 2 ≤ n) (C : ContactMatrix n)
    {i0 : Fin n} (R0 : ReachData C.P i0) {A : Finset (Fin n)}
    (hA : i0 ∈ A) :
    (∫⁻ J, VpotE C (infStep J A) ∂stepDist C) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (VpotE_ne_top hn C R0 hA)
  calc
    (∫⁻ J, VpotE C (infStep J A) ∂stepDist C) ≤
        ((Finset.univ \ A).card : ℝ≥0∞) +
          ∫⁻ J, VpotE C (infStep J A) ∂stepDist C := le_add_left le_rfl
    _ = VpotE C A := (VpotE_recursion C).symm

/-- The real one-step expectation is genuinely integrable, not a totalized
Bochner integral assigned zero on nonintegrable input. -/
theorem integrable_Vpot_infStep (hn : 2 ≤ n) (C : ContactMatrix n)
    {i0 : Fin n} (R0 : ReachData C.P i0) {A : Finset (Fin n)}
    (hA : i0 ∈ A) :
    Integrable (fun J => Vpot hd C i0 (infStep J A)) (stepDist C) := by
  have hm : Measurable (fun J : Fin n → Fin n => VpotE C (infStep J A)) :=
    Measurable.of_discrete
  have heq : (fun J => (VpotE C (infStep J A)).toReal) =
      (fun J => Vpot hd C i0 (infStep J A)) := by
    funext J
    exact (Vpot_eq_toReal_VpotE hn C R0 (subset_infStep J A hA)).symm
  rw [← heq]
  exact integrable_toReal_of_lintegral_ne_top hm.aemeasurable
    (lintegral_VpotE_infStep_ne_top hn C R0 hA)

/-- Real-valued one-step recursion (C.7) for the same potential that satisfies
the bounds, anchors and antitonicity in `PotentialFn.lean`. -/
theorem Vpot_recursion (hn : 2 ≤ n) (C : ContactMatrix n)
    {i0 : Fin n} (R0 : ReachData C.P i0) {A : Finset (Fin n)}
    (hA : i0 ∈ A) :
    Vpot hd C i0 A = ((Finset.univ \ A).card : ℝ) +
      ∫ J, Vpot hd C i0 (infStep J A) ∂stepDist C := by
  have hfin := lintegral_VpotE_infStep_ne_top hn C R0 hA
  have hpoint : ∀ J, VpotE C (infStep J A) ≠ ⊤ := fun J =>
    VpotE_ne_top hn C R0 (subset_infStep J A hA)
  have hmeas : Measurable (fun J : Fin n → Fin n => VpotE C (infStep J A)) :=
    Measurable.of_discrete
  have hint : (∫⁻ J, VpotE C (infStep J A) ∂stepDist C).toReal =
      ∫ J, Vpot hd C i0 (infStep J A) ∂stepDist C := by
    rw [← integral_toReal hmeas.aemeasurable
      (Filter.Eventually.of_forall fun J => lt_top_iff_ne_top.mpr (hpoint J))]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun J =>
      (Vpot_eq_toReal_VpotE hn C R0 (subset_infStep J A hA)).symm
  rw [Vpot_eq_toReal_VpotE hn C R0 hA, VpotE_recursion C,
    ENNReal.toReal_add (by simp) hfin, ENNReal.toReal_natCast, hint]

/-- Original-model entry point: the spanning witness is constructed from the
matrix's irreducibility, rather than required as an additional graph input. -/
theorem Vpot_recursion_of_irreducible (hn : 2 ≤ n) (C : ContactMatrix n)
    {i0 : Fin n} {A : Finset (Fin n)} (hA : i0 ∈ A) :
    Vpot hd C i0 A = ((Finset.univ \ A).card : ℝ) +
      ∫ J, Vpot hd C i0 (infStep J A) ∂stepDist C :=
  Vpot_recursion hn C (ReachData.ofIrreducible C.irreducible i0) hA

end AnvBandit
