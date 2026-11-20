import AnvBandit.ExecutionLaw
import AnvBandit.ExecutionPhases
import AnvBandit.GoodEvent

/-! Original-model finite good-path interface. Mean sandwiches and UCB/counting obligations
are derived here, not supplied as fields of the original stochastic model. -/
noncomputable section
open scoped BigOperators
open Finset
namespace AnvBandit.ExecutionBounds
variable {n K : ℕ} {Ω : Type*}
open ExecutionLaw

def selected (p : Execution.Params n K) (X : Ω → ℕ → Fin n → Bool)
    (J : Ω → ℕ → Fin n → Fin n) (i : Fin n) (k : Fin K) (t : ℕ) (ω : Ω) : Bool :=
  decide (Execution.I p (realTape (X ω)) (J ω) t i = k)

def reward (X : Ω → ℕ → Fin n → Bool) (i : Fin n) (_k : Fin K)
    (t : ℕ) (ω : Ω) : ℝ := realTape (X ω) t i

def mean (M : DecayModel n K) (p : Execution.Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n)
    (i : Fin n) (_k : Fin K) (t : ℕ) (ω : Ω) : ℝ :=
  actualMean M p lam (X ω) (J ω) t i

theorem count_eq_N (p : Execution.Params n K) (X : Ω → ℕ → Fin n → Bool)
    (J : Ω → ℕ → Fin n → Fin n) (i : Fin n) (k : Fin K) (t : ℕ)
    (ht : t ≤ p.T) (ω : Ω) :
    ObservedPrefix.count (selected p X J i k) t ω =
      Execution.N p (realTape (X ω)) (J ω) t i k := by
  rw [Execution.N_eq_sum p _ _ t ht]
  simp [ObservedPrefix.count, selected]

theorem sampleSum_reward (p : Execution.Params n K) (X : Ω → ℕ → Fin n → Bool)
    (J : Ω → ℕ → Fin n → Fin n) (i : Fin n) (k : Fin K) (m : ℕ) (ω : Ω) :
    ObservedPrefix.sampleSum (selected p X J i k) (reward X i k) m p.T ω =
      Execution.sampleSum p (realTape (X ω)) (J ω) i k m := by
  unfold ObservedPrefix.sampleSum Execution.sampleSum
  apply sum_congr rfl
  intro t ht
  rw [ObservedPrefix.capped, count_eq_N p X J i k t (le_of_lt (mem_range.mp ht))]
  simp [selected, reward]

/-- Only the genuinely observed finite concentration event remains as an intermediate
path condition. The mean sandwich follows from the original model and simultaneous counts. -/
def goodRunOn (M : DecayModel n K) (p : Execution.Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n) (ω : Ω)
    (hg : ω ∈ ObservedPrefix.good (selected p X J) (reward X) (mean M p lam X J) p.T p.L) :
    GoodRunOn M p.T :=
  Execution.goodRunOnOfBounds p M (realTape (X ω)) (J ω)
    (fun i k m => ObservedPrefix.sampleSum (selected p X J i k) (mean M p lam X J i k) m p.T ω)
    (by
      intro i k m hm hmN
      apply ObservedPrefix.observed_mean_bounds (selected p X J i k)
        (mean M p lam X J i k) (M.b k) (M.f k) hm
      · simpa [count_eq_N p X J i k p.T le_rfl] using hmN
      · intro t ht hs
        have hk : Execution.I p (realTape (X ω)) (J ω) t i = k := by
          simpa [selected] using hs
        have hlo := (actualMean_bounds M p lam (X ω) (J ω) t i).1
        have hup := actualMean_le_personal_envelope M p lam (X ω) (J ω) t i
        rw [hk] at hlo hup
        rw [count_eq_N p X J i k t ht.le]
        exact ⟨hlo, by simpa [mean, Nat.add_comm] using hup⟩)
    (by
      intro i k m hm hmN
      have h := ObservedPrefix.good_empirical_mean (selected p X J) (reward X)
        (mean M p lam X J) hg i k m hm
        (by simpa [count_eq_N p X J i k p.T le_rfl] using hmN)
      simpa [sampleSum_reward, Execution.empiricalPrefix] using h)

/-- Once a prefix has been observed, later rewards do not alter its capped sum. -/
theorem sampleSum_stable (sel : ℕ → Ω → Bool) (Z : ℕ → Ω → ℝ)
    {m v T : ℕ} {ω : Ω} (hvT : v ≤ T) (hm : m ≤ ObservedPrefix.count sel v ω) :
    ObservedPrefix.sampleSum sel Z m T ω = ObservedPrefix.sampleSum sel Z m v ω := by
  induction T, hvT using Nat.le_induction with
  | base => rfl
  | succ t hvt ih =>
    have hmt := hm.trans (ObservedPrefix.count_mono sel ω hvt)
    have hc : ObservedPrefix.capped sel m t ω = false := by
      simp [ObservedPrefix.capped, Nat.not_lt.mpr hmt]
    unfold ObservedPrefix.sampleSum at *
    rw [sum_range_succ, if_neg (by simp [hc]), add_zero]
    exact ih

theorem sampleSum_reward_prefix (p : Execution.Params n K) (X : Ω → ℕ → Fin n → Bool)
    (J : Ω → ℕ → Fin n → Fin n) (i : Fin n) (k : Fin K) (m v : ℕ)
    (hv : v ≤ p.T) (ω : Ω) (hm : m ≤ Execution.N p (realTape (X ω)) (J ω) v i k) :
    ObservedPrefix.sampleSum (selected p X J i k) (reward X i k) m v ω =
      Execution.sampleSum p (realTape (X ω)) (J ω) i k m := by
  have he := sampleSum_stable (selected p X J i k) (reward X i k) hv
    (by simpa [count_eq_N p X J i k v hv] using hm)
  rw [sampleSum_reward] at he
  exact he.symm

/-- Prefix-good interface for first-failure arguments; the confidence logarithm remains
that of the original horizon, while only observations available by v are constrained. -/
def goodRunOnPrefix (M : DecayModel n K) (p : Execution.Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n) (ω : Ω)
    (v : ℕ) (hv : v ≤ p.T)
    (hg : ω ∈ ObservedPrefix.good (selected p X J) (reward X) (mean M p lam X J) v p.L) :
    GoodRunOn M v where
  L := p.L
  hL := (Ldelta_pos p.hn p.hK p.hT p.hδ.1 p.hδ.2).le
  I := Execution.I p (realTape (X ω)) (J ω)
  bhat := Execution.empiricalPrefix p (realTape (X ω)) (J ω)
  meanSum := fun i k m => ObservedPrefix.sampleSum (selected p X J i k)
    (mean M p lam X J i k) m v ω
  mean_bounds := by
    intro i k m hm hmN
    rw [Execution.pullCount_eq_N p _ _ v hv] at hmN
    apply ObservedPrefix.observed_mean_bounds (selected p X J i k)
      (mean M p lam X J i k) (M.b k) (M.f k) hm
    · simpa [count_eq_N p X J i k v hv] using hmN
    · intro t ht hs
      have hk : Execution.I p (realTape (X ω)) (J ω) t i = k := by simpa [selected] using hs
      have hlo := (actualMean_bounds M p lam (X ω) (J ω) t i).1
      have hup := actualMean_le_personal_envelope M p lam (X ω) (J ω) t i
      rw [hk] at hlo hup
      rw [count_eq_N p X J i k t (le_trans ht.le hv)]
      exact ⟨hlo, by simpa [mean, Nat.add_comm] using hup⟩
  hc := by
    intro i k m hm hmN
    rw [Execution.pullCount_eq_N p _ _ v hv] at hmN
    have h := ObservedPrefix.good_empirical_mean (selected p X J) (reward X)
      (mean M p lam X J) hg i k m hm
      (by simpa [count_eq_N p X J i k v hv] using hmN)
    rw [sampleSum_reward_prefix p X J i k m v hv ω hmN] at h
    exact h
  active := fun t i => ((Execution.run p (realTape (X ω)) (J ω) t).nodes i).active
  sel_mem := fun t _ i => Execution.selected_mem p _ _ t i
  ucb := by
    intro t ht i hstar
    have htT := le_trans ht.le hv
    simp only [Execution.pullCount_eq_N p _ _ t htT]
    have hchoose := Execution.LocalState.choose_spec p
      ((Execution.run p (realTape (X ω)) (J ω) t).nodes i)
    rcases hchoose with hz | hall
    · exact Or.inl hz
    · right
      have hsel := hall (Execution.I p (realTape (X ω)) (J ω) t i)
        (Execution.selected_mem p _ _ t i)
      have hs := hall M.star hstar
      refine ⟨hsel.1, hs.1, ?_⟩
      rw [Execution.empiricalPrefix_at_count p _ _ t htT,
        Execution.empiricalPrefix_at_count p _ _ t htT]
      exact hs.2

/-- Exact B.2 arithmetic for a real local state. The phase-total and count hypotheses are
explicit intermediate obligations; they are not fields of the execution or original model. -/
theorem cache_eq_of_exact_budget (M : DecayModel n K) (p : Execution.Params n K)
    (i : Fin n) (s : Execution.LocalState n K i) (d : ℕ)
    (hs : M.star ∈ s.active) (hcount : ∀ k ∈ s.active, k ≠ M.star → s.C k ≤ M.mkAll p.L k)
    (htotal : ∑ k ∈ s.active, s.C k = d) (hd : M.Bschedule p.L < d) :
    s.cache = M.star := by
  have hsub : s.active.erase M.star ⊆ M.others := by
    intro k hk
    have hne := (mem_erase.mp hk).1
    simpa [DecayModel.others] using hne
  have hcard : (s.active.erase M.star).card ≤ kappa n K := by
    rw [card_erase_of_mem hs]
    exact Nat.sub_le_sub_right (s.active_card_le p) 1
  have hsum : ∑ k ∈ s.active.erase M.star, s.C k ≤ M.HKappa p.L := by
    apply le_trans _ (M.sum_mk_le_hkappa hsub hcard)
    exact sum_le_sum (fun k hk => hcount k (mem_erase.mp hk).2 (mem_erase.mp hk).1)
  have hsplit := sum_erase_add s.active s.C hs
  rw [htotal] at hsplit
  apply s.cache_eq_of_strict M.star hs
  intro k hk hne
  have hmk := M.mkAll_le_mMax (L := p.L) (k := k) (by simpa [DecayModel.others] using hne)
  have hck := hcount k hk hne
  unfold DecayModel.Bschedule at hd
  omega

/-- B.2 for the actual completed phase under the finite observed-prefix event, with
exact `HKappa + mMax` rather than the coarse capacity-times-maximum budget. -/
theorem reliable_cache (M : DecayModel n K) (p : Execution.Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n) (ω : Ω)
    (hg : ω ∈ ObservedPrefix.good (selected p X J) (reward X) (mean M p lam X J) p.T p.L)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (ht : p.phaseEnd ℓ ≤ p.T) (i : Fin n)
    (hs : M.star ∈ ((Execution.run p (realTape (X ω)) (J ω)
      (p.phaseEnd (ℓ-1))).nodes i).active)
    (hd : M.Bschedule p.L < p.phaseEnd ℓ - p.phaseEnd (ℓ-1)) :
    ((Execution.preBoundary p (realTape (X ω)) (J ω) ℓ).nodes i).cache = M.star := by
  let R := goodRunOn M p lam X J ω hg
  have hab := (p.phaseEnd_strictMono (show ℓ-1 < ℓ by omega)).le
  apply cache_eq_of_exact_budget M p i _ _
  · rwa [Execution.preBoundary_active p _ _ ℓ hℓ ht i]
  · intro k hk hne
    have hr := R.phase_residual_budget i hne (p.phaseEnd (ℓ-1)) (p.phaseEnd ℓ) hab ht (by
      intro t hat htb
      change M.star ∈ ((Execution.run p (realTape (X ω)) (J ω) t).nodes i).active
      rwa [Execution.active_during_phase p _ _ ℓ hℓ t (lt_of_lt_of_le htb ht) hat htb i])
    change pullCount (Execution.I p (realTape (X ω)) (J ω)) (p.phaseEnd ℓ) i k -
      pullCount (Execution.I p (realTape (X ω)) (J ω)) (p.phaseEnd (ℓ-1)) i k ≤
      M.mkAll p.L k - pullCount (Execution.I p (realTape (X ω)) (J ω))
        (p.phaseEnd (ℓ-1)) i k at hr
    rw [Execution.pullCount_eq_N p _ _ _ ht,
      Execution.pullCount_eq_N p _ _ _ (le_trans hab ht)] at hr
    have hc := Execution.preBoundary_count_conservation p (realTape (X ω)) (J ω) ℓ hℓ ht i k
    omega
  · exact Execution.preBoundary_total p _ _ ℓ hℓ ht i
  · exact hd
/-- Prefix version of reliable_cache, valid before a possible later concentration failure. -/
theorem reliable_cache_prefix (M : DecayModel n K) (p : Execution.Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n) (ω : Ω)
    (v : ℕ) (hv : v ≤ p.T)
    (hg : ω ∈ ObservedPrefix.good (selected p X J) (reward X) (mean M p lam X J) v p.L)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (ht : p.phaseEnd ℓ ≤ v) (i : Fin n)
    (hs : M.star ∈ ((Execution.run p (realTape (X ω)) (J ω)
      (p.phaseEnd (ℓ-1))).nodes i).active)
    (hd : M.Bschedule p.L < p.phaseEnd ℓ - p.phaseEnd (ℓ-1)) :
    ((Execution.preBoundary p (realTape (X ω)) (J ω) ℓ).nodes i).cache = M.star := by
  let R := goodRunOnPrefix M p lam X J ω v hv hg
  have htT := le_trans ht hv
  have hab := (p.phaseEnd_strictMono (show ℓ-1 < ℓ by omega)).le
  apply cache_eq_of_exact_budget M p i _ _
  · rwa [Execution.preBoundary_active p _ _ ℓ hℓ htT i]
  · intro k hk hne
    have hr := R.phase_residual_budget i hne (p.phaseEnd (ℓ-1)) (p.phaseEnd ℓ) hab ht (by
      intro t hat htb
      change M.star ∈ ((Execution.run p (realTape (X ω)) (J ω) t).nodes i).active
      rwa [Execution.active_during_phase p _ _ ℓ hℓ t (lt_of_lt_of_le htb htT) hat htb i])
    change pullCount (Execution.I p (realTape (X ω)) (J ω)) (p.phaseEnd ℓ) i k -
      pullCount (Execution.I p (realTape (X ω)) (J ω)) (p.phaseEnd (ℓ-1)) i k ≤
      M.mkAll p.L k - pullCount (Execution.I p (realTape (X ω)) (J ω))
        (p.phaseEnd (ℓ-1)) i k at hr
    rw [Execution.pullCount_eq_N p _ _ _ htT,
      Execution.pullCount_eq_N p _ _ _ (le_trans hab htT)] at hr
    have hc := Execution.preBoundary_count_conservation p (realTape (X ω)) (J ω) ℓ hℓ htT i k
    omega
  · exact Execution.preBoundary_total p _ _ ℓ hℓ htT i
  · exact hd
/-- Residual-budget form of the recommendation arithmetic, including an empty
suboptimal active set (`Finset.sup` is zero there). -/
theorem cache_eq_of_residual_budget (i : Fin n) (s : Execution.LocalState n K i)
    (k : Fin K) (z : Fin K → ℕ) (d : ℕ) (hs : k ∈ s.active)
    (hcount : ∀ j ∈ s.active, j ≠ k → s.C j ≤ z j)
    (htotal : ∑ j ∈ s.active, s.C j = d)
    (hd : (∑ j ∈ s.active.erase k, z j) + (s.active.erase k).sup z < d) :
    s.cache = k := by
  have hsum : ∑ j ∈ s.active.erase k, s.C j ≤ ∑ j ∈ s.active.erase k, z j :=
    sum_le_sum (fun j hj => hcount j (mem_erase.mp hj).2 (mem_erase.mp hj).1)
  have hsplit := sum_erase_add s.active s.C hs
  rw [htotal] at hsplit
  apply s.cache_eq_of_strict k hs
  intro j hj hne
  have hmax : z j ≤ (s.active.erase k).sup z := Finset.le_sup (mem_erase.mpr ⟨hne, hj⟩)
  have hcnt := hcount j hj hne
  omega

/-- Exact remaining exploration budget of an actually completed phase. -/
theorem phase_residual_count_prefix (M : DecayModel n K) (p : Execution.Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n) (ω : Ω)
    (v : ℕ) (hv : v ≤ p.T)
    (hg : ω ∈ ObservedPrefix.good (selected p X J) (reward X) (mean M p lam X J) v p.L)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (ht : p.phaseEnd ℓ ≤ v) (i : Fin n)
    (hs : M.star ∈ ((Execution.run p (realTape (X ω)) (J ω)
      (p.phaseEnd (ℓ-1))).nodes i).active) (k : Fin K) (hk : k ≠ M.star) :
    ((Execution.preBoundary p (realTape (X ω)) (J ω) ℓ).nodes i).C k ≤
      M.mkAll p.L k - Execution.N p (realTape (X ω)) (J ω) (p.phaseEnd (ℓ-1)) i k := by
  let R := goodRunOnPrefix M p lam X J ω v hv hg
  have htT := le_trans ht hv
  have hab := (p.phaseEnd_strictMono (show ℓ-1 < ℓ by omega)).le
  have hr := R.phase_residual_budget i hk (p.phaseEnd (ℓ-1)) (p.phaseEnd ℓ) hab ht (by
    intro t hat htb
    change M.star ∈ ((Execution.run p (realTape (X ω)) (J ω) t).nodes i).active
    rwa [Execution.active_during_phase p _ _ ℓ hℓ t (lt_of_lt_of_le htb htT) hat htb i])
  change pullCount (Execution.I p (realTape (X ω)) (J ω)) (p.phaseEnd ℓ) i k -
    pullCount (Execution.I p (realTape (X ω)) (J ω)) (p.phaseEnd (ℓ-1)) i k ≤
    M.mkAll p.L k - pullCount (Execution.I p (realTape (X ω)) (J ω))
      (p.phaseEnd (ℓ-1)) i k at hr
  rw [Execution.pullCount_eq_N p _ _ _ htT,
    Execution.pullCount_eq_N p _ _ _ (le_trans hab htT)] at hr
  have hc := Execution.preBoundary_count_conservation p (realTape (X ω)) (J ω) ℓ hℓ htT i k
  omega

/-- Full residual B.2 condition, not just the global exact-B sufficient condition. -/
theorem reliable_cache_prefix_residual (M : DecayModel n K) (p : Execution.Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n) (ω : Ω)
    (v : ℕ) (hv : v ≤ p.T)
    (hg : ω ∈ ObservedPrefix.good (selected p X J) (reward X) (mean M p lam X J) v p.L)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (ht : p.phaseEnd ℓ ≤ v) (i : Fin n)
    (hs : M.star ∈ ((Execution.run p (realTape (X ω)) (J ω)
      (p.phaseEnd (ℓ-1))).nodes i).active)
    (hd : let S := ((Execution.run p (realTape (X ω)) (J ω) (p.phaseEnd (ℓ-1))).nodes i).active
          let z := fun k => M.mkAll p.L k -
            Execution.N p (realTape (X ω)) (J ω) (p.phaseEnd (ℓ-1)) i k
          (∑ k ∈ S.erase M.star, z k) + (S.erase M.star).sup z <
            p.phaseEnd ℓ - p.phaseEnd (ℓ-1)) :
    ((Execution.preBoundary p (realTape (X ω)) (J ω) ℓ).nodes i).cache = M.star := by
  have htT := le_trans ht hv
  apply cache_eq_of_residual_budget i _ M.star
    (fun k => M.mkAll p.L k - Execution.N p (realTape (X ω)) (J ω) (p.phaseEnd (ℓ-1)) i k) _
  · rwa [Execution.preBoundary_active p _ _ ℓ hℓ htT i]
  · intro k _ hk
    exact phase_residual_count_prefix M p lam X J ω v hv hg ℓ hℓ ht i hs k hk
  · exact Execution.preBoundary_total p _ _ ℓ hℓ htT i
  · rwa [Execution.preBoundary_active p _ _ ℓ hℓ htT i]

end AnvBandit.ExecutionBounds
