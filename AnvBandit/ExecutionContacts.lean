import AnvBandit.ExecutionKernel
import AnvBandit.HeadTail
import Mathlib.Probability.Independence.InfinitePi

/-!
# Actual phase contacts have the original product-process law

The proof works under the original unconditional measure. It never conditions on the
concentration event. The terminal and post-terminal contacts are analysis-only extensions.
-/
noncomputable section
open scoped BigOperators Classical
open Finset MeasureTheory ProbabilityTheory Preorder
namespace AnvBandit.ExecutionLaw
variable {n K : ℕ}

/-- All fresh round contacts, including analysis-only unused contacts. -/
def roundContacts (ω : Path n) (r : ℕ) : Fin n → Fin n := (ω (r+1)).2

/-- A past round contact recovered from a finite history; the default is never used below. -/
def prefixRoundContact (t : ℕ) (h : Prefix n t) (r : ℕ) : Fin n → Fin n :=
  if hr : r + 1 ≤ t then (h ⟨r+1, Finset.mem_Iic.mpr hr⟩).2 else id

/-- The full finite contact-cylinder law, derived from joint conditional freshness. -/
theorem roundContacts_cylinder (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (s : Finset ℕ)
    (B : ℕ → Set (Fin n → Fin n)) :
    (executionMeasure M p C lam) {ω | ∀ r ∈ s, roundContacts ω r ∈ B r} =
      ∏ r ∈ s, (contactDistribution C).toMeasure (B r) := by
  let μ := executionMeasure M p C lam
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert t s hlt ih =>
    have hnot : t ∉ s := by intro ht; exact (lt_irrefl t) (hlt t ht)
    let A : Set (Prefix n t) := {h | ∀ r ∈ s, prefixRoundContact t h r ∈ B r}
    have hA : (frestrictLe t) ⁻¹' A = {ω : Path n | ∀ r ∈ s, roundContacts ω r ∈ B r} := by
      ext ω
      change (∀ r ∈ s, prefixRoundContact t (frestrictLe t ω) r ∈ B r) ↔ _
      apply forall_congr'
      intro r
      apply forall_congr'
      intro hr
      simp [prefixRoundContact, show r+1 ≤ t by have := hlt r hr; omega,
        frestrictLe, roundContacts]
    have hset : (fun ω : Path n => (frestrictLe t ω, (ω (t+1)).2)) ⁻¹' (A ×ˢ B t) =
        {ω | ∀ r ∈ insert t s, roundContacts ω r ∈ B r} := by
      ext ω
      have hAω := Set.ext_iff.mp hA ω
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_setOf_eq] at hAω ⊢
      rw [hAω]
      simp [roundContacts, and_comm]
    have hj := congrArg (fun ν : Measure (Prefix n t × (Fin n → Fin n)) => ν (A ×ˢ B t))
      (history_contact_joint M p C lam t)
    rw [Measure.map_apply (by fun_prop) (Set.to_countable _ |>.measurableSet), hset,
      Measure.prod_prod, Measure.map_apply (measurable_frestrictLe t)
        (Set.to_countable _ |>.measurableSet), hA] at hj
    rw [hj, ih, Finset.prod_insert hnot]
    exact mul_comm _ _

/-- All fresh contact vectors form the original independent product process. -/
theorem roundContacts_law (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) :
    (executionMeasure M p C lam).map roundContacts =
      Measure.infinitePi (fun _ : ℕ => (contactDistribution C).toMeasure) := by
  apply Measure.eq_infinitePi
  intro s B hB
  rw [Measure.map_apply (by unfold roundContacts; fun_prop) (MeasurableSet.pi (Finset.countable_toSet s) (fun i hi => hB i))]
  exact roundContacts_cylinder M p C lam s B

/-- The PMF joint row product is the same `stepDist` already used by propagation. -/
theorem contactDistribution_toMeasure (C : ContactMatrix n) :
    (contactDistribution C).toMeasure = stepDist C := by
  apply Measure.ext_of_singleton
  intro j
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), contactDistribution_apply]
  simp only [stepDist, Measure.pi_singleton, nodeDist_singleton]

/-- The ideal process starts with the contact at phase `offset+1`, including future
analysis-only contacts after the finite algorithm stops. -/
def phaseContactStream (p : Execution.Params n K) (offset : ℕ) (ω : Path n) :
    ℕ → Fin n → Fin n := fun j => pathContacts p ω (offset+j+1)

/-- Actual phase contacts, with any fixed offset, have exactly the propagation process law.
No concentration-event conditioning and no reward independence across rounds is used. -/
theorem actual_contact_stream_law (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (offset : ℕ) :
    (executionMeasure M p C lam).map (phaseContactStream p offset) = stepMeasure C := by
  let f : ℕ → ℕ := fun j => p.phaseEnd (offset+j+1) - 1
  have hpos (j : ℕ) : 1 ≤ p.phaseEnd (offset+j+1) :=
    le_trans (by omega) (p.le_phaseEnd _)
  have hfinj : Function.Injective f := by
    intro a b hab
    have he : p.phaseEnd (offset+a+1) = p.phaseEnd (offset+b+1) := by
      dsimp [f] at hab
      have ha := hpos a
      have hb := hpos b
      omega
    have := p.phaseEnd_strictMono.injective he
    omega
  have hcomp : phaseContactStream p offset =
      (fun R : ℕ → Fin n → Fin n => fun j => R (f j)) ∘ roundContacts := by
    funext ω j
    dsimp [phaseContactStream, pathContacts, roundContacts, f]
    rw [Nat.sub_add_cancel (hpos j)]
  rw [hcomp, ← Measure.map_map (by fun_prop) (by unfold roundContacts; fun_prop),
    roundContacts_law, Measure.map_infinitePi_infinitePi_of_inj hfinj]
  simp only [contactDistribution_toMeasure, stepMeasure]

end AnvBandit.ExecutionLaw
