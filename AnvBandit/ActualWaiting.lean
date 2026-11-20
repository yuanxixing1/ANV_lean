import AnvBandit.ActualPropagation
import AnvBandit.ExecutionContacts
import AnvBandit.PotentialBridge

/-!
# Actual-law waiting variables and transport to the original propagation moments

Regrouping is an exact measurable inverse to `unblock`; it does not introduce a new
contact law or condition on a good event. This module is the probability integration
layer for the actual finite-horizon pathwise global bound.
-/
noncomputable section
open scoped BigOperators ENNReal
open Finset MeasureTheory ProbabilityTheory

namespace AnvBandit.ActualWaiting
open Execution ExecutionLaw ActualPropagation
variable {n K d : ℕ}

def groupContacts (d : ℕ) (R : ℕ → Fin n → Fin n) :
    ℕ → Fin d → Fin n → Fin n := fun b s => R (b*d+s.val)

theorem measurable_groupContacts (d : ℕ) :
    Measurable (groupContacts (n := n) d) := by
  unfold groupContacts
  fun_prop

theorem unblock_groupContacts (hd : 0 < d) (R : ℕ → Fin n → Fin n) :
    unblock hd (groupContacts d R) = R := by
  funext t i
  change R (t/d*d+t%d) i = R t i
  rw [show t/d*d+t%d = t by simpa [Nat.mul_comm] using Nat.div_add_mod t d]

theorem groupContacts_unblock (hd : 0 < d)
    (ω : ℕ → Fin d → Fin n → Fin n) : groupContacts d (unblock hd ω) = ω := by
  funext b s i
  have hdiv : (b*d+s.val)/d = b := by
    rw [show b*d+s.val = s.val+d*b by ring,
      Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt s.isLt, zero_add]
  have hmod : (b*d+s.val)%d = s.val := by
    rw [show b*d+s.val = s.val+d*b by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt s.isLt]
  have hfin : (⟨(b*d+s.val)%d, Nat.mod_lt _ hd⟩ : Fin d) = s := Fin.ext hmod
  simp only [groupContacts, unblock, hdiv, hfin]

theorem groupContacts_law (hd : 0 < d) (C : ContactMatrix n) :
    (stepMeasure C).map (groupContacts d) = procMeasure C d := by
  rw [← unblock_measure hd C,
    Measure.map_map (measurable_groupContacts d) (measurable_unblock hd)]
  have he : groupContacts d ∘ unblock (n := n) hd = id := by
    funext ω
    exact groupContacts_unblock hd ω
  rw [he, Measure.map_id]

def actualBlocks (M : DecayModel n K) (p : Params n K) (ω : Path n) :
    ℕ → Fin (n-1) → Fin n → Fin n :=
  groupContacts (n-1) (phaseContactStream p (preparation M p) ω)

theorem measurable_actualBlocks (M : DecayModel n K) (p : Params n K) :
    Measurable (actualBlocks M p) := by
  apply (measurable_groupContacts (n-1)).comp
  unfold phaseContactStream pathContacts
  fun_prop

theorem actualBlocks_law (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) :
    (executionMeasure M p C lam).map (actualBlocks M p) = procMeasure C (n-1) := by
  change (executionMeasure M p C lam).map
    (groupContacts (n-1) ∘ phaseContactStream p (preparation M p)) = _
  rw [← Measure.map_map (measurable_groupContacts (n-1)) (by
    unfold phaseContactStream pathContacts; fun_prop), actual_contact_stream_law]
  exact groupContacts_law (by have := p.hn; omega) C

def actualTau (M : DecayModel n K) (p : Params n K) (ω : Path n) : ℕ :=
  tau (by have := p.hn; omega) (actualBlocks M p ω) (holder p M.star)

def actualS (M : DecayModel n K) (p : Params n K) (ω : Path n) : ℕ :=
  p.phaseEnd (preparation M p + actualTau M p ω)

theorem actualS_eq_Sglob (M : DecayModel n K) (p : Params n K) (ω : Path n) :
    (actualS M p ω : ℝ) = Sglob (by have := p.hn; omega) p.H
      (preparation M p) p.β (actualBlocks M p ω) (holder p M.star) := by
  simp [actualS, actualTau, Params.phaseEnd, Sglob, tauR, Nat.cast_add]

theorem phaseStream_eq_shifted (M : DecayModel n K) (p : Params n K) (ω : Path n) :
    phaseContactStream p (preparation M p) ω = shiftedContacts M p (pathContacts p ω) := by
  funext j
  unfold phaseContactStream shiftedContacts
  congr 1
  omega

/-- Completion is derived on the original canonical measure before any good-event restriction. -/
theorem actual_complete_ae (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) :
    ∀ᵐ ω ∂executionMeasure M p C lam,
      Inform (shiftedContacts M p (pathContacts p ω)) {holder p M.star}
        (actualTau M p ω) = univ := by
  have hd : 0 < n-1 := by have := p.hn; omega
  have hc : ∀ᵐ b ∂procMeasure C (n-1), Complete hd b (holder p M.star) := by
    rw [ae_iff]
    exact measure_Complete_compl_eq_zero p.hn C
      (ReachData.ofIrreducible C.irreducible (holder p M.star))
  rw [← actualBlocks_law M p C lam] at hc
  have hh := ae_of_ae_map (measurable_actualBlocks M p).aemeasurable hc
  filter_upwards [hh] with ω hω
  have hmem : Inform (unblock hd (actualBlocks M p ω)) {holder p M.star}
      (actualTau M p ω) = univ := Nat.sInf_mem hω
  rw [actualBlocks, unblock_groupContacts, phaseStream_eq_shifted] at hmem
  exact hmem

/-- Measurability of the original block-level scheduled waiting variable. -/
theorem measurable_Sglob {n : ℕ} (hd : 0 < n-1) (H r β : ℝ) (i0 : Fin n) :
    Measurable (fun b => Sglob hd H r β b i0) := by
  unfold Sglob tauR
  exact measurable_const.mul
    ((measurable_of_countable (fun x : ℕ => (x : ℝ))).comp (Nat.measurable_ceil.comp
      ((measurable_const.add (measurable_tau_real hd i0)).pow_const β)))

theorem measurable_actualS_real (M : DecayModel n K) (p : Params n K) :
    Measurable (fun ω : Path n => (actualS M p ω : ℝ)) := by
  have h := (measurable_Sglob (by have := p.hn; omega) (p.H : ℝ)
    (preparation M p : ℝ) p.β (holder p M.star)).comp (measurable_actualBlocks M p)
  convert h using 1
  funext ω
  exact actualS_eq_Sglob M p ω

/-- Expected truncated waiting time of the actual coupled contact stream. -/
def expectedWaiting (M : DecayModel n K) (p : Params n K) (C : ContactMatrix n)
    (lam : Fin 2) : ℝ :=
  (∫⁻ ω, ENNReal.ofReal ((min p.T (actualS M p ω) : ℕ) : ℝ)
    ∂executionMeasure M p C lam).toReal

theorem expectedWaiting_eq_EminTS (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) :
    expectedWaiting M p C lam = EminTS (by have := p.hn; omega) C
      (holder p M.star) p.H (preparation M p) p.β p.T := by
  unfold expectedWaiting EminTS
  congr 1
  rw [← actualBlocks_law M p C lam]
  let f : (ℕ → Fin (n-1) → Fin n → Fin n) → ℝ≥0∞ := fun b =>
    ENNReal.ofReal (min (p.T : ℝ) (Sglob (by have := p.hn; omega)
      (p.H : ℝ) (preparation M p : ℝ) p.β b (holder p M.star)))
  have hf : Measurable f := ENNReal.measurable_ofReal.comp
    (measurable_const.min (measurable_Sglob _ _ _ _ _))
  change _ = ∫⁻ b, f b ∂(executionMeasure M p C lam).map (actualBlocks M p)
  rw [lintegral_map hf (measurable_actualBlocks M p)]
  apply lintegral_congr
  intro ω
  dsimp [f]
  rw [← actualS_eq_Sglob]
  simp [Nat.cast_min]

/-- Exact original global waiting moment, not an independent free cost input. -/
theorem expectedWaiting_le_Pbeta (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) :
    expectedWaiting M p C lam ≤ Pbeta (by have := p.hn; omega) C
      (holder p M.star) p.H (preparation M p) p.β := by
  rw [expectedWaiting_eq_EminTS]
  exact EminTS_le_Pbeta p.hn C (ReachData.ofIrreducible C.irreducible _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) p.hβ.le


theorem expectedWaiting_le_horizon (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) : expectedWaiting M p C lam ≤ p.T := by
  unfold expectedWaiting
  apply ENNReal.toReal_le_of_le_ofReal (Nat.cast_nonneg _)
  calc
    (∫⁻ ω, ENNReal.ofReal ((min p.T (actualS M p ω) : ℕ) : ℝ)
      ∂executionMeasure M p C lam) ≤
        ∫⁻ _ω : Path n, ENNReal.ofReal (p.T : ℝ) ∂executionMeasure M p C lam := by
      apply lintegral_mono
      intro ω
      exact ENNReal.ofReal_le_ofReal (Nat.cast_le.mpr (Nat.min_le_left _ _))
    _ = ENNReal.ofReal (p.T : ℝ) := by simp

theorem expectedWaiting_le_truncated_Pbeta (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) :
    expectedWaiting M p C lam ≤ min (p.T : ℝ)
      (Pbeta (by have := p.hn; omega) C (holder p M.star) p.H (preparation M p) p.β) :=
  le_min (expectedWaiting_le_horizon M p C lam) (expectedWaiting_le_Pbeta M p C lam)

end AnvBandit.ActualWaiting
