import AnvBandit.Absorbing

/-! Disjoint completed-phase charging. Cumulative counts are never reset in
this argument: phase intervals are disjoint subsets of the same finite prefix. -/
noncomputable section
open scoped BigOperators Classical
open Finset
set_option maxHeartbeats 1000000
namespace AnvBandit.Absorbing
open Execution ExecutionLaw ExecutionBounds
variable {n K : ℕ} {Ω : Type*}

def phaseSelected (p : Params n K) (X : ℕ → Fin n → ℝ)
    (J : ℕ → Fin n → Fin n) (ℓ : ℕ) (i : Fin n) (k : Fin K) : Finset ℕ :=
  (Ico (p.phaseEnd (ℓ-1)) (p.phaseEnd ℓ)).filter (fun t => I p X J t i = k)

lemma interval_count (p : Params n K) (X : ℕ → Fin n → ℝ)
    (J : ℕ → Fin n → Fin n) (a b : ℕ) (hab : a ≤ b) (hb : b ≤ p.T)
    (i : Fin n) (k : Fin K) :
    N p X J a i k + ((Ico a b).filter (fun t => I p X J t i = k)).card = N p X J b i k := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have hbT : b < p.T := by omega
    rw [Nat.Ico_succ_right_eq_insert_Ico hab, filter_insert]
    by_cases hsel : I p X J b i = k
    · rw [if_pos hsel, card_insert_of_notMem (by simp), N_step p X J hbT, if_pos hsel]
      have h := ih (by omega)
      omega
    · rw [if_neg hsel, N_step p X J hbT, if_neg hsel, add_zero]
      exact ih (by omega)

lemma phaseSelected_card (p : Params n K) (X : ℕ → Fin n → ℝ)
    (J : ℕ → Fin n → Fin n) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (ht : p.phaseEnd ℓ ≤ p.T)
    (i : Fin n) (k : Fin K) :
    (phaseSelected p X J ℓ i k).card = ((preBoundary p X J ℓ).nodes i).C k := by
  have hc := preBoundary_count_conservation p X J ℓ hℓ ht i k
  have hi := interval_count p X J (p.phaseEnd (ℓ-1)) (p.phaseEnd ℓ)
    (p.phaseEnd_strictMono.monotone (Nat.sub_le _ _)) ht i k
  unfold phaseSelected
  omega

lemma phaseSelected_disjoint (p : Params n K) (X : ℕ → Fin n → ℝ)
    (J : ℕ → Fin n → Fin n) {a b : ℕ} (hne : a ≠ b) (i : Fin n) (k : Fin K) :
    Disjoint (phaseSelected p X J a i k) (phaseSelected p X J b i k) := by
  apply disjoint_left.mpr
  intro t ha hb
  have ha' := mem_Ico.mp (mem_filter.mp ha).1
  have hb' := mem_Ico.mp (mem_filter.mp hb).1
  rcases lt_or_gt_of_ne hne with hab | hba
  · have he := p.phaseEnd_strictMono.monotone (show a ≤ b-1 by omega)
    omega
  · have he := p.phaseEnd_strictMono.monotone (show b ≤ a-1 by omega)
    omega

/-- A finite family of completed phases in which this node holds the optimum
uses only one cumulative `m_k` budget, not one budget per phase. -/
theorem held_phase_pair_budget (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n) (ω : Ω)
    (v : ℕ) (hv : v ≤ p.T)
    (hg : prefixGood M p lam X J v ω) (F : Finset ℕ)
    (hpos : ∀ ℓ ∈ F, 1 ≤ ℓ) (hend : ∀ ℓ ∈ F, p.phaseEnd ℓ ≤ v)
    (i : Fin n) (k : Fin K) (hk : k ≠ M.star)
    (hhold : ∀ ℓ ∈ F, M.star ∈ ((preBoundary p (realTape (X ω)) (J ω) ℓ).nodes i).active) :
    ∑ ℓ ∈ F, ((preBoundary p (realTape (X ω)) (J ω) ℓ).nodes i).C k ≤ M.mkAll p.L k := by
  let R := goodRunOnPrefix M p lam X J ω v hv hg
  let S := fun ℓ => phaseSelected p (realTape (X ω)) (J ω) ℓ i k
  have hd : (F : Set ℕ).PairwiseDisjoint S := by
    intro a ha b hb hab
    exact phaseSelected_disjoint p _ _ hab i k
  have hs : F.biUnion S ⊆ (range v).filter (fun t => M.star ∈ R.active t i ∧ R.I t i = k) := by
    intro t ht
    obtain ⟨ℓ, hℓ, htl⟩ := mem_biUnion.mp ht
    have ht' := mem_filter.mp htl
    have hti := mem_Ico.mp ht'.1
    refine mem_filter.mpr ⟨mem_range.mpr (hti.2.trans_le (hend ℓ hℓ)), ?_, ht'.2⟩
    change M.star ∈ ((run p (realTape (X ω)) (J ω) t).nodes i).active
    rw [active_during_phase p _ _ ℓ (hpos ℓ hℓ) t
      (hti.2.trans_le ((hend ℓ hℓ).trans hv)) hti.1 hti.2 i,
      ← preBoundary_active p _ _ ℓ (hpos ℓ hℓ) ((hend ℓ hℓ).trans hv) i]
    exact hhold ℓ hℓ
  calc
    _ = ∑ ℓ ∈ F, (S ℓ).card := by
      apply sum_congr rfl
      intro ℓ hℓ
      exact (phaseSelected_card p _ _ ℓ (hpos ℓ hℓ) ((hend ℓ hℓ).trans hv) i k).symm
    _ = (F.biUnion S).card := (card_biUnion hd).symm
    _ ≤ _ := (card_le_card hs).trans (R.pair_budget i hk)

/-- Personal C.9 for any finite set of erroneous, prefix-good complete phases.
The single prefix event is legitimate here: it ends at the last charged phase,
not at the original horizon, and will be selected pathwise before first failure. -/
theorem erroneous_phases_personal_budget (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n) (ω : Ω)
    (v : ℕ) (hv : v ≤ p.T) (hg : prefixGood M p lam X J v ω) (F : Finset ℕ)
    (hpos : ∀ ℓ ∈ F, 1 ≤ ℓ) (hend : ∀ ℓ ∈ F, p.phaseEnd ℓ ≤ v)
    (hwrong : ∀ ℓ ∈ F, wrong M.star (preBoundary p (realTape (X ω)) (J ω) ℓ)) :
    ∑ ℓ ∈ F, (p.phaseEnd ℓ-p.phaseEnd (ℓ-1)) ≤
      2 * n * ∑ k ∈ M.others, M.mkAll p.L k := by
  let s := fun ℓ => preBoundary p (realTape (X ω)) (J ω) ℓ
  let q := fun ℓ i k => if M.star ∈ ((s ℓ).nodes i).active then ((s ℓ).nodes i).C k else 0
  have hlocal : ∀ ℓ ∈ F, p.phaseEnd ℓ-p.phaseEnd (ℓ-1) ≤
      2 * ∑ i : Fin n, ∑ k ∈ M.others, q ℓ i k := by
    intro ℓ hℓ
    let i := blamed p M.star (s ℓ)
    have hb := blamed_spec p M.star (s ℓ) (hwrong ℓ hℓ)
    have hh := erroneous_phase_half M p (realTape (X ω)) (J ω) ℓ (hpos ℓ hℓ)
      ((hend ℓ hℓ).trans hv) (hwrong ℓ hℓ)
    have hsub : ((s ℓ).nodes i).active.erase M.star ⊆ M.others := by
      intro k hk
      have hne := (mem_erase.mp hk).1
      simpa [DecayModel.others] using hne
    have hkbound : (∑ k ∈ ((s ℓ).nodes i).active.erase M.star, ((s ℓ).nodes i).C k) ≤
        ∑ k ∈ M.others, q ℓ i k := by
      have hheld : M.star ∈ ((s ℓ).nodes i).active := (mem_holders _ _ _).mp hb.1
      simp only [q, if_pos hheld]
      exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
    have hibound : (∑ k ∈ M.others, q ℓ i k) ≤ ∑ i : Fin n, ∑ k ∈ M.others, q ℓ i k :=
      single_le_sum (f := fun i : Fin n => ∑ k ∈ M.others, q ℓ i k)
        (fun _ _ => Nat.zero_le _) (mem_univ i)
    exact hh.trans (Nat.mul_le_mul_left 2 (hkbound.trans hibound))
  have hpairs : ∀ i : Fin n, ∀ k ∈ M.others, (∑ ℓ ∈ F, q ℓ i k) ≤ M.mkAll p.L k := by
    intro i k hk
    let Fi := F.filter (fun ℓ => M.star ∈ ((s ℓ).nodes i).active)
    have hbudget := held_phase_pair_budget M p lam X J ω v hv hg Fi
      (fun ℓ hℓ => hpos ℓ (mem_filter.mp hℓ).1)
      (fun ℓ hℓ => hend ℓ (mem_filter.mp hℓ).1) i k
      (by simpa [DecayModel.others] using hk)
      (fun ℓ hℓ => (mem_filter.mp hℓ).2)
    simpa only [Fi, sum_filter, q, s] using hbudget
  calc
    _ ≤ ∑ ℓ ∈ F, 2 * ∑ i : Fin n, ∑ k ∈ M.others, q ℓ i k := sum_le_sum hlocal
    _ = 2 * ∑ i : Fin n, ∑ k ∈ M.others, ∑ ℓ ∈ F, q ℓ i k := by
      rw [← mul_sum, sum_comm]
      congr 1
      apply sum_congr rfl
      intro i _
      rw [sum_comm]
    _ ≤ 2 * ∑ _i : Fin n, ∑ k ∈ M.others, M.mkAll p.L k := by
      apply Nat.mul_le_mul_left
      exact sum_le_sum (fun i _ => sum_le_sum (fun k hk => hpairs i k hk))
    _ = _ := by simp [Nat.mul_assoc]

/-- Actual charged phases up to a finite cutoff; zero is excluded. -/
def erroneousPhases (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n)
    (ω : Ω) (Ph : ℕ) : Finset ℕ :=
  (range (Ph+1)).filter (fun ℓ => 1 ≤ ℓ ∧ live M p lam X J ℓ ω ∧
    wrong M.star (preBoundary p (realTape (X ω)) (J ω) ℓ))

/-- The personal error budget on *every* trajectory. No global or caller-supplied
prefix confidence assumption remains: the latest charged phase supplies its own
prefix event by the definition of the actual absorbed error indicator. -/
theorem actual_error_budget_personal (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n)
    (ω : Ω) (Ph : ℕ) :
    (∑ ℓ ∈ erroneousPhases M p lam X J ω Ph, (p.phaseEnd ℓ-p.phaseEnd (ℓ-1))) ≤
      2*n*∑ k ∈ M.others, M.mkAll p.L k := by
  let F := erroneousPhases M p lam X J ω Ph
  by_cases hF : F.Nonempty
  · let a := F.max' hF
    have ha : a ∈ F := F.max'_mem hF
    have has := (mem_filter.mp ha).2
    have hgood := has.2.1
    apply erroneous_phases_personal_budget M p lam X J ω (p.phaseEnd a) hgood.1.le hgood.2 F
    · intro ℓ hℓ
      exact (mem_filter.mp hℓ).2.1
    · intro ℓ hℓ
      exact p.phaseEnd_strictMono.monotone (F.le_max' ℓ hℓ)
    · intro ℓ hℓ
      exact (mem_filter.mp hℓ).2.2.2
  · have he : F = ∅ := not_nonempty_iff_eq_empty.mp hF
    change (∑ ℓ ∈ F, _) ≤ _
    simp [he]

/-- All optimal-holder selected rounds in a finite charged phase family.
The union, not a list with multiplicity, shares each node-arm budget once. -/
def chargedTimes (M : DecayModel n K) (p : Params n K)
    (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n)
    (F : Finset ℕ) (i : Fin n) (k : Fin K) : Finset ℕ :=
  (F.filter (fun ℓ => M.star ∈ ((preBoundary p X J ℓ).nodes i).active)).biUnion
    (fun ℓ => phaseSelected p X J ℓ i k)

lemma chargedTimes_card (M : DecayModel n K) (p : Params n K)
    (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n)
    (F : Finset ℕ) (hpos : ∀ ℓ ∈ F, 1 ≤ ℓ) (hend : ∀ ℓ ∈ F, p.phaseEnd ℓ ≤ p.T)
    (i : Fin n) (k : Fin K) :
    (chargedTimes M p X J F i k).card = ∑ ℓ ∈ F,
      if M.star ∈ ((preBoundary p X J ℓ).nodes i).active then ((preBoundary p X J ℓ).nodes i).C k else 0 := by
  unfold chargedTimes
  rw [card_biUnion (by
    intro a ha b hb hab
    exact phaseSelected_disjoint p X J hab i k)]
  rw [sum_filter]
  apply sum_congr rfl
  intro ℓ hℓ
  rw [phaseSelected_card p X J ℓ (hpos ℓ hℓ) (hend ℓ hℓ) i k]

lemma chargedTimes_spec (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n) (ω : Ω)
    (F : Finset ℕ) (hpos : ∀ ℓ ∈ F, 1 ≤ ℓ)
    (hlive : ∀ ℓ ∈ F, live M p lam X J ℓ ω)
    (i : Fin n) (k : Fin K) (t : ℕ)
    (ht : t ∈ chargedTimes M p (realTape (X ω)) (J ω) F i k) :
    t < p.T ∧ M.star ∈ ((run p (realTape (X ω)) (J ω) t).nodes i).active ∧
      I p (realTape (X ω)) (J ω) t i = k ∧ prefixGood M p lam X J t ω := by
  obtain ⟨ℓ, hℓ, htℓ⟩ := mem_biUnion.mp ht
  have hF := (mem_filter.mp hℓ).1
  have hhold := (mem_filter.mp hℓ).2
  have hsel := (mem_filter.mp htℓ).2
  have htime := mem_Ico.mp (mem_filter.mp htℓ).1
  have hl := hlive ℓ hF
  refine ⟨htime.2.trans hl.1, ?_, hsel, prefixGood_mono M p lam X J htime.2.le hl.2⟩
  rw [active_during_phase p _ _ ℓ (hpos ℓ hF) t (htime.2.trans hl.1) htime.1 htime.2 i,
    ← preBoundary_active p _ _ ℓ (hpos ℓ hF) hl.1.le i]
  exact hhold

/-- Combinatorial charging before either personal or public statistical bounds.
Each counted node-round belongs to only one completed phase. -/
theorem erroneous_phases_charge (M : DecayModel n K) (p : Params n K)
    (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n) (F : Finset ℕ)
    (hpos : ∀ ℓ ∈ F, 1 ≤ ℓ) (hend : ∀ ℓ ∈ F, p.phaseEnd ℓ ≤ p.T)
    (hwrong : ∀ ℓ ∈ F, wrong M.star (preBoundary p X J ℓ)) :
    (∑ ℓ ∈ F, (p.phaseEnd ℓ-p.phaseEnd (ℓ-1))) ≤
      2 * ∑ i : Fin n, ∑ k ∈ M.others, (chargedTimes M p X J F i k).card := by
  let s := fun ℓ => preBoundary p X J ℓ
  let q := fun ℓ i k => if M.star ∈ ((s ℓ).nodes i).active then ((s ℓ).nodes i).C k else 0
  have hlocal : ∀ ℓ ∈ F, p.phaseEnd ℓ-p.phaseEnd (ℓ-1) ≤
      2 * ∑ i : Fin n, ∑ k ∈ M.others, q ℓ i k := by
    intro ℓ hℓ
    let i := blamed p M.star (s ℓ)
    have hb := blamed_spec p M.star (s ℓ) (hwrong ℓ hℓ)
    have hh := erroneous_phase_half M p X J ℓ (hpos ℓ hℓ) (hend ℓ hℓ) (hwrong ℓ hℓ)
    have hsub : ((s ℓ).nodes i).active.erase M.star ⊆ M.others := by
      intro k hk
      simpa [DecayModel.others] using (mem_erase.mp hk).1
    have hkbound : (∑ k ∈ ((s ℓ).nodes i).active.erase M.star, ((s ℓ).nodes i).C k) ≤
        ∑ k ∈ M.others, q ℓ i k := by
      have hheld : M.star ∈ ((s ℓ).nodes i).active := (mem_holders _ _ _).mp hb.1
      simp only [q, if_pos hheld]
      exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
    have hibound : (∑ k ∈ M.others, q ℓ i k) ≤ ∑ i : Fin n, ∑ k ∈ M.others, q ℓ i k :=
      single_le_sum (f := fun i : Fin n => ∑ k ∈ M.others, q ℓ i k)
        (fun _ _ => Nat.zero_le _) (mem_univ i)
    exact hh.trans (Nat.mul_le_mul_left 2 (hkbound.trans hibound))
  calc
    _ ≤ ∑ ℓ ∈ F, 2 * ∑ i : Fin n, ∑ k ∈ M.others, q ℓ i k := sum_le_sum hlocal
    _ = 2 * ∑ i : Fin n, ∑ k ∈ M.others, ∑ ℓ ∈ F, q ℓ i k := by
      rw [← mul_sum, sum_comm]
      congr 1
      apply sum_congr rfl
      intro i _
      rw [sum_comm]
    _ = _ := by
      congr 1
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro k hk
      exact (chargedTimes_card M p X J F hpos hend i k).symm

end AnvBandit.Absorbing
