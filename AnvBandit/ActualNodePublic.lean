import AnvBandit.ActualNodeArrival
import AnvBandit.ActualNodeGrouping
import AnvBandit.ActualPublicBudget

/-! The public per-node cost candidate. The team positive-area budget occurs exactly once,
after taking the union of terminal and lost node-arm pairs. -/
noncomputable section
open scoped BigOperators
open Finset
namespace AnvBandit.ActualPropagation
open Execution ExecutionLaw ExecutionBounds ActualPublicBudget
variable {n K : ℕ} {Ω : Type*}

theorem path_node_public_candidate (M : DecayModel n K) (p : Params n K)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n) (ω : Ω)
    (hg : ω ∈ ObservedPrefix.good (selected p X J) (reward X) (mean M p 1 X J) p.T p.L)
    (σ : Fin n → ℕ) (τ : ℕ) (hστ : ∀ i, σ i ≤ τ)
    (harrived : ∀ i, i ∈ Inform (shiftedContacts M p (J ω)) {holder p M.star} (σ i))
    (hcomplete : Inform (shiftedContacts M p (J ω)) {holder p M.star} τ = univ)
    (c : Fin K → ℝ) (hc : ∀ k, 0 ≤ c k) (hstar : c M.star = 0) :
    (∑ t ∈ range p.T, ∑ i, c (I p (realTape (X ω)) (J ω) t i)) ≤
      M.supOthers c * ((∑ i, min p.T (p.phaseEnd (preparation M p+σ i)) : ℕ) : ℝ)
        + M.CNcap c p.L + M.wNmax c p.L * ((∑ i : Fin n, (τ - σ i) : ℕ) : ℝ) + M.Bpub c := by
  let R := goodRunOn M p 1 X J ω hg
  let arr := fun i => p.phaseEnd (preparation M p+σ i)
  let U := univ.filter (fun i => arr i < p.T)
  let D := fun i => ((run p (realTape (X ω)) (J ω) p.T).nodes i).D
  let Lost := fun i => (univ : Finset (Fin K)).filter (fun k =>
    k ∉ permSet n K i ∪ D i ∧ ∃ t ∈ range p.T, arr i ≤ t ∧ R.I t i = k)
  let A := fun i => (permSet n K i ∪ D i).erase M.star ∪ Lost i
  let S := fun i k => ((range p.T).filter (fun t => arr i ≤ t)).filter (fun t => R.I t i = k)
  have hterminal : ∀ i ∈ U, M.star ∈ permSet n K i ∪ D i := by
    intro i hi
    exact holds_at_terminal_of_arrival M p 1 X J ω hg i (σ i) (harrived i)
      (mem_filter.mp hi).2
  have hcover : ∀ i t, arr i < p.T → t ∈ (range p.T).filter (fun t => arr i ≤ t) →
      R.I t i = M.star ∨ R.I t i ∈ A i := by
    intro i t hai ht
    by_cases hs : R.I t i = M.star
    · exact Or.inl hs
    · right
      by_cases hm : R.I t i ∈ permSet n K i ∪ D i
      · exact mem_union_left _ (mem_erase.mpr ⟨hs, hm⟩)
      · apply mem_union_right
        exact mem_filter.mpr ⟨mem_univ _, hm, t, (mem_filter.mp ht).1,
          (mem_filter.mp ht).2, rfl⟩
  have hgroup := R.node_cost_group c hc hstar arr A hcover
  have hpub := terminal_lost_public_selected_cost M p X J ω c hc hstar U D
    (holder p M.star) (mem_sticky_holder p M.star)
    (fun i _ => ((run p (realTape (X ω)) (J ω) p.T).nodes i).disjoint)
    (fun i _ => ((run p (realTape (X ω)) (J ω) p.T).nodes i).card_le)
    hterminal
    (fun i _ => ((run p (realTape (X ω)) (J ω) p.T).nodes i).active_card_le p)
    Lost (fun i => τ-σ i)
    (by
      intro i hi k hk
      have hn := (mem_filter.mp hk).2.1
      have hne : k ≠ M.star := fun h => hn (h ▸ hterminal i hi)
      simpa [DecayModel.others] using hne)
    (by
      intro i hi
      apply disjoint_left.mpr
      intro k hk hl
      exact (mem_filter.mp hl).2.1 (mem_of_mem_erase hk))
    (by
      intro i _
      exact actual_elimination_budget M p 1 X J ω hg i (σ i) τ (hστ i) hcomplete)
    S (by
      intro i hi k hk t ht
      obtain ⟨htS, htk⟩ := mem_filter.mp ht
      obtain ⟨htT, hat⟩ := mem_filter.mp htS
      have ht' := mem_range.mp htT
      exact ⟨ht', holds_after_ideal_arrival M p 1 X J ω hg i (σ i) t
        (harrived i) hat ht', htk, ObservedPrefix.good_prefix _ _ _ ht'.le hg⟩)
  have hmax : 0 ≤ M.wNmax c p.L := by
    have hw : M.wk (statisticalWeights M c p.L) p.L = M.wkN c p.L :=
      funext (wk_statisticalWeights M c p.L)
    simpa only [DecayModel.wmax, DecayModel.wNmax, hw] using
      M.wmax_nonneg (statisticalWeights_nonneg M c hc p.L) p.L
  have helsum : (∑ i ∈ U, (τ-σ i : ℕ) : ℝ) ≤ ((∑ i : Fin n, (τ - σ i) : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ U) (fun i _ _ => Nat.cast_nonneg _)
  have helmul := mul_le_mul_of_nonneg_right helsum hmax
  change (∑ t ∈ range p.T, ∑ i, c (R.I t i)) ≤ _
  change (∑ t ∈ range p.T, ∑ i, c (R.I t i)) ≤
    M.supOthers c * ((∑ i, min p.T (arr i) : ℕ) : ℝ) +
      ∑ i ∈ U, ∑ k ∈ A i, c k * (S i k).card at hgroup
  change (∑ i ∈ U, ∑ k ∈ A i, c k * (S i k).card) ≤ _ at hpub
  dsimp only [arr] at hgroup
  nlinarith

/-- Both actual node candidates hold on the same finite good event; taking their minimum
here does not assert any interchange of expectation and minimum. -/
theorem path_node_public_min (M : DecayModel n K) (p : Params n K)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n) (ω : Ω)
    (hg : ω ∈ ObservedPrefix.good (selected p X J) (reward X) (mean M p 1 X J) p.T p.L)
    (σ : Fin n → ℕ) (τ : ℕ) (hστ : ∀ i, σ i ≤ τ)
    (harrived : ∀ i, i ∈ Inform (shiftedContacts M p (J ω)) {holder p M.star} (σ i))
    (hcomplete : Inform (shiftedContacts M p (J ω)) {holder p M.star} τ = univ)
    (c : Fin K → ℝ) (hc : ∀ k, 0 ≤ c k) (hstar : c M.star = 0) :
    (∑ t ∈ range p.T, ∑ i, c (I p (realTape (X ω)) (J ω) t i)) ≤
      M.supOthers c * ((∑ i, min p.T (p.phaseEnd (preparation M p+σ i)) : ℕ) : ℝ) +
        M.Clam c p.L ((∑ i : Fin n, (τ - σ i) : ℕ) : ℝ) 1 := by
  have hp := path_node_personal_candidate M p 1 X J ω hg σ τ hστ harrived hcomplete c hc hstar
  have hn := path_node_public_candidate M p X J ω hg σ τ hστ harrived hcomplete c hc hstar
  change _ ≤ _ + min _ _
  rw [add_min]
  exact le_min (by nlinarith [hp]) (by nlinarith [hn])

end AnvBandit.ActualPropagation
