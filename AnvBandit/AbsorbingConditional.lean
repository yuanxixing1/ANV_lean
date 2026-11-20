import AnvBandit.Absorbing
import AnvBandit.ExecutionKernel

/-! Communication-before conditioning: the current reward is known, but the
current joint contact vector is not. No global good event is conditioned on. -/
noncomputable section
open scoped BigOperators Classical
open Finset MeasureTheory ProbabilityTheory Preorder
namespace AnvBandit.Absorbing
open Execution ExecutionLaw ExecutionBounds
variable {n K : ℕ}

abbrev Precontact (n t : ℕ) := Prefix n t × (Fin n → Bool)

def beforeContact (t : ℕ) (ω : Path n) : Precontact n t :=
  (frestrictLe t ω, (ω (t+1)).1)

lemma beforeContact_measurable (t : ℕ) : Measurable (beforeContact (n := n) t) := by
  exact (measurable_frestrictLe t).prodMk (measurable_fst.comp (measurable_pi_apply (t+1)))

/-- Generic finite-precontact transport through the *proved* actual joint contact
law. The function is arbitrary because both its domains are finite, so neither
measurability nor integrability is an unproved application assumption. -/
theorem conditional_contact_integral (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (t : ℕ)
    (f : Precontact n t × (Fin n → Fin n) → ℝ) :
    (executionMeasure M p C lam)[fun ω => f (beforeContact t ω, (ω (t+1)).2) |
        (inferInstance : MeasurableSpace (Precontact n t)).comap (beforeContact t)]
      =ᵐ[executionMeasure M p C lam]
        fun ω => ∫ R, f (beforeContact t ω, R) ∂(contactDistribution C).toMeasure := by
  let μ := executionMeasure M p C lam
  have hx := beforeContact_measurable (n := n) t
  have hy : Measurable (fun ω : Path n => (ω (t+1)).2) :=
    measurable_snd.comp (measurable_pi_apply (t+1))
  have hf : StronglyMeasurable f := (measurable_of_countable f).stronglyMeasurable
  have hi : Integrable (fun ω : Path n => f (beforeContact t ω, (ω (t+1)).2)) μ := by
    exact (integrable_map_measure hf.aestronglyMeasurable (hx.prodMk hy).aemeasurable).mp
      Integrable.of_finite
  have hc := condExp_prod_ae_eq_integral_condDistrib hx hy.aemeasurable hf hi
  have hl := contact_step_conditional_law M p C lam t
  have hl' : ∀ᵐ ω ∂μ,
      condDistrib (fun ω : Path n => (ω (t+1)).2) (beforeContact t) μ (beforeContact t ω) =
        (contactDistribution C).toMeasure := by
    have h := ae_of_ae_map hx.aemeasurable hl
    exact h
  filter_upwards [hc, hl'] with ω hc hl
  exact hc.trans (by rw [hl])

/-- The unobserved current contact is replaced by a fixed dummy. This is only a
factorization of precontact information, never a change to the actual run law. -/
def reconstruct (t : ℕ) (z : Precontact n t) : Path n := fun r =>
  if h : r ≤ t then z.1 ⟨r, mem_Iic.mpr h⟩
  else if r = t+1 then (z.2, id) else default

lemma beforeContact_reconstruct (t : ℕ) (z : Precontact n t) :
    beforeContact t (reconstruct t z) = z := by
  apply Prod.ext
  · funext r
    simp [beforeContact, reconstruct, frestrictLe, (mem_Iic.mp r.property)]
  · simp [beforeContact, reconstruct]

lemma coordinates_eq_of_beforeContact_eq (t : ℕ) {ω ω' : Path n}
    (h : beforeContact t ω = beforeContact t ω') (r : ℕ) (hr : r ≤ t) : ω r = ω' r := by
  exact congrArg (fun z : Precontact n t => z.1 ⟨r, mem_Iic.mpr hr⟩) h

lemma run_eq_of_beforeContact_eq (p : Params n K) (t : ℕ) {ω ω' : Path n}
    (h : beforeContact t ω = beforeContact t ω') (r : ℕ) (hr : r ≤ t) :
    run p (realTape (pathRewards ω)) (pathContacts p ω) r =
      run p (realTape (pathRewards ω')) (pathContacts p ω') r := by
  apply run_congr
  · intro s hs
    have he := coordinates_eq_of_beforeContact_eq t h (s+1) (by omega)
    funext i
    change rewardReal ((ω (s+1)).1 i) = rewardReal ((ω' (s+1)).1 i)
    rw [he]
  · intro ℓ hℓ _
    exact congrArg Prod.snd (coordinates_eq_of_beforeContact_eq t h (p.phaseEnd ℓ) (hℓ.trans hr))

lemma reward_eq_of_beforeContact_eq (t : ℕ) {ω ω' : Path n}
    (h : beforeContact t ω = beforeContact t ω') (r : ℕ) (hr : r ≤ t) :
    pathRewards ω r = pathRewards ω' r := by
  by_cases he : r = t
  · subst r
    exact congrArg Prod.snd h
  · exact congrArg Prod.fst (coordinates_eq_of_beforeContact_eq t h (r+1) (by omega))

/-- The prefix test through the current reward is already known before the
current contact. Actual conditional means, not independent reward streams, are
used in this equality. -/
lemma prefixGood_beforeContact (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (t v : ℕ) (hv : v ≤ t+1) {ω ω' : Path n}
    (h : beforeContact t ω = beforeContact t ω') :
    prefixGood M p lam pathRewards (pathContacts p) v ω ↔
      prefixGood M p lam pathRewards (pathContacts p) v ω' := by
  have hs : ∀ i k r, r < v →
      selected p pathRewards (pathContacts p) i k r ω =
        selected p pathRewards (pathContacts p) i k r ω' := by
    intro i k r hr
    simp only [selected, I, run_eq_of_beforeContact_eq p t h r (by omega)]
    rfl
  have hx : ∀ (i : Fin n) (k : Fin K) r, r < v → reward pathRewards i k r ω = reward pathRewards i k r ω' := by
    intro i k r hr
    change rewardReal (pathRewards ω r i) = rewardReal (pathRewards ω' r i)
    rw [reward_eq_of_beforeContact_eq t h r (by omega)]
  have hp : ∀ i k r, r < v → mean M p lam pathRewards (pathContacts p) i k r ω =
      mean M p lam pathRewards (pathContacts p) i k r ω' := by
    intro i k r hr
    unfold mean
    rw [← stateMean_run, ← stateMean_run, run_eq_of_beforeContact_eq p t h r (by omega)]
  have hn : ∀ i k r, r ≤ v →
      ObservedPrefix.count (selected p pathRewards (pathContacts p) i k) r ω =
        ObservedPrefix.count (selected p pathRewards (pathContacts p) i k) r ω' := by
    intro i k r hr
    unfold ObservedPrefix.count
    apply sum_congr rfl
    intro q hq
    rw [hs i k q (lt_of_lt_of_le (mem_range.mp hq) hr)]
  have hz : ∀ i k m,
      ObservedPrefix.centered (selected p pathRewards (pathContacts p) i k)
        (reward pathRewards i k) (mean M p lam pathRewards (pathContacts p) i k) m v ω =
      ObservedPrefix.centered (selected p pathRewards (pathContacts p) i k)
        (reward pathRewards i k) (mean M p lam pathRewards (pathContacts p) i k) m v ω' := by
    intro i k m
    unfold ObservedPrefix.centered
    apply sum_congr rfl
    intro r hr
    have hr' := mem_range.mp hr
    simp only [ObservedPrefix.capped, hs i k r hr', hn i k r hr'.le, hx i k r hr', hp i k r hr']
    split_ifs <;> rfl
  unfold prefixGood ObservedPrefix.good
  simp only [Set.mem_setOf_eq, hn _ _ _ le_rfl, hz]

lemma preBoundary_beforeContact (p : Params n K) (j : ℕ) (t : ℕ)
    (ht : p.phaseEnd (j+1) = t+1) {ω ω' : Path n}
    (h : beforeContact t ω = beforeContact t ω') :
    preBoundary p (realTape (pathRewards ω)) (pathContacts p ω) (j+1) =
      preBoundary p (realTape (pathRewards ω')) (pathContacts p ω') (j+1) := by
  unfold preBoundary
  have hx : realTape (pathRewards ω) t = realTape (pathRewards ω') t := by
    funext i
    change rewardReal (pathRewards ω t i) = rewardReal (pathRewards ω' t i)
    rw [reward_eq_of_beforeContact_eq t h t le_rfl]
  simp only [ht, Nat.add_sub_cancel, run_eq_of_beforeContact_eq p t h t le_rfl, hx]

lemma nextState_beforeContact (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (j t : ℕ) (ht : p.phaseEnd (j+1) = t+1) {ω ω' : Path n}
    (h : beforeContact t ω = beforeContact t ω') (R : Fin n → Fin n) :
    nextState M p lam pathRewards (pathContacts p) j ω R =
      nextState M p lam pathRewards (pathContacts p) j ω' R := by
  have hg := prefixGood_beforeContact M p lam t (p.phaseEnd (j+1)) (by omega) h
  simp only [nextState, live, hg, preBoundary_beforeContact p j t ht h]
  split_ifs <;> rfl

/-- The conditional expected absorbed next potential is exactly the contact
kernel integral, conditioned after the phase reward but before its contact. -/
theorem conditional_next_potential (M : DecayModel n K) (p : Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (j : ℕ) :
    let t := p.phaseEnd (j+1)-1
    (executionMeasure M p C lam)[fun ω =>
      Vpot (by have := p.hn; omega) C (holder p M.star)
        (state M p lam pathRewards (pathContacts p) (j+1) ω) |
        (inferInstance : MeasurableSpace (Precontact n t)).comap (beforeContact t)]
      =ᵐ[executionMeasure M p C lam]
        fun ω => ∫ R, Vpot (by have := p.hn; omega) C (holder p M.star)
          (nextState M p lam pathRewards (pathContacts p) j ω R)
          ∂(contactDistribution C).toMeasure := by
  dsimp only
  let t := p.phaseEnd (j+1)-1
  have hpos : 1 ≤ p.phaseEnd (j+1) := (show 1 ≤ j+1 by omega).trans (p.le_phaseEnd _)
  have ht : p.phaseEnd (j+1) = t+1 := by dsimp [t]; omega
  let hd : 0 < n-1 := by have := p.hn; omega
  let f : Precontact n t × (Fin n → Fin n) → ℝ := fun z =>
    Vpot hd C (holder p M.star)
      (nextState M p lam pathRewards (pathContacts p) j (reconstruct t z.1) z.2)
  have heq (ω : Path n) (R : Fin n → Fin n) :
      f (beforeContact t ω, R) = Vpot hd C (holder p M.star)
        (nextState M p lam pathRewards (pathContacts p) j ω R) := by
    unfold f
    rw [nextState_beforeContact M p lam j t ht (beforeContact_reconstruct t (beforeContact t ω)) R]
  have hfun : (fun ω : Path n => f (beforeContact t ω, (ω (t+1)).2)) =
      (fun ω => Vpot hd C (holder p M.star)
        (state M p lam pathRewards (pathContacts p) (j+1) ω)) := by
    funext ω
    rw [heq]
    have hec : (ω (t+1)).2 = pathContacts p ω (j+1) := by simp only [pathContacts, ht]
    rw [hec, nextState_actual]
  have hc := conditional_contact_integral M p C lam t f
  rw [hfun] at hc
  exact hc.trans (Filter.Eventually.of_forall fun ω => integral_congr_ae
    (Filter.Eventually.of_forall fun R => heq ω R))

end AnvBandit.Absorbing
