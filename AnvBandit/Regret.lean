import AnvBandit.Serial

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Joint-trajectory benchmark, usage counts and regret (Section 2.2)

Model-level quantities of Section 2.2 and Appendix A.5:

* usage counts `N_{i,k}(t)`, `M_k(t)` (2.1) and effective usage `q^{(λ)}_{i,k}(t)` (2.2),
* joint-trajectory value `J^{(λ)}_T(u)` and omniscient benchmark `V^{⋆,λ}_T` (2.6),
* regret `R_team, R_avg` and base-value loss `R_b` (2.7), (2.8),
* the honest identity `J^{(0)}_T(u) = ∑_i F_{k}(N_{i,k}(T))` and the two per-agent inequalities
  behind (A.7).
-/

noncomputable section
open scoped BigOperators
open Finset

namespace AnvBandit

variable {n K : ℕ}

/-- Personal usage count `N_{i,k}(t)`: pulls of arm `k` by agent `i` over rounds `s < t`. -/
def Nfin {T : ℕ} (u : Fin n → Fin T → Fin K) (t : Fin T) (i : Fin n) (k : Fin K) : ℕ :=
  ((Finset.univ : Finset (Fin T)).filter (fun s => s < t ∧ u i s = k)).card

/-- Terminal personal usage count `N_{i,k}(T)`. -/
def Ntot {T : ℕ} (u : Fin n → Fin T → Fin K) (i : Fin n) (k : Fin K) : ℕ :=
  ((Finset.univ : Finset (Fin T)).filter (fun s => u i s = k)).card

/-- Terminal team usage count `M_k(T)`. -/
def Mtot {T : ℕ} (u : Fin n → Fin T → Fin K) (k : Fin K) : ℕ :=
  ∑ i : Fin n, Ntot u i k

/-- Effective usage `q^{(0)}_{i,k}(t) = 1 + N_{i,k}(t−1)`. -/
def qeff0 {T : ℕ} (u : Fin n → Fin T → Fin K) (t : Fin T) (i : Fin n) (k : Fin K) : ℕ :=
  1 + Nfin u t i k

/-- Effective usage `q^{(1)}_{i,k}(t) = 1 + M_k(t−1)`. -/
def qeff1 {T : ℕ} (u : Fin n → Fin T → Fin K) (t : Fin T) (k : Fin K) : ℕ :=
  1 + ∑ i : Fin n, Nfin u t i k

/-- Joint-trajectory value `J^{(0)}_T(u)` (personal fatigue). -/
def J0 {T : ℕ} (M : DecayModel n K) (u : Fin n → Fin T → Fin K) : ℝ :=
  ∑ t : Fin T, ∑ i : Fin n, M.mean (u i t) (qeff0 u t i (u i t))

/-- Joint-trajectory value `J^{(1)}_T(u)` (public fatigue). -/
def J1 {T : ℕ} (M : DecayModel n K) (u : Fin n → Fin T → Fin K) : ℝ :=
  ∑ t : Fin T, ∑ i : Fin n, M.mean (u i t) (qeff1 u t (u i t))

/-- Omniscient benchmark `V^{⋆,0}_T`. -/
def Vstar0 {T : ℕ} (M : DecayModel n K) : ℝ :=
  (Finset.univ : Finset (Fin n → Fin T → Fin K)).sup'
    ⟨fun _ _ => ⟨0, by have := M.two_le_K; omega⟩, Finset.mem_univ _⟩ (J0 M)

/-- Omniscient benchmark `V^{⋆,1}_T`. -/
def Vstar1 {T : ℕ} (M : DecayModel n K) : ℝ :=
  (Finset.univ : Finset (Fin n → Fin T → Fin K)).sup'
    ⟨fun _ _ => ⟨0, by have := M.two_le_K; omega⟩, Finset.mem_univ _⟩ (J1 M)

/-- Base-value loss `R_b = ∑_{k≠⋆} Δ_k E M_k(T)`. -/
def Rb (M : DecayModel n K) (EMk : Fin K → ℝ) : ℝ :=
  ∑ k ∈ M.others, M.gap k * EMk k

/-- Team regret `R_team = V^{⋆,λ}_T − E J^{(λ)}_T(I)`. -/
def Rteam (V : ℝ) (EJ : ℝ) : ℝ := V - EJ

/-- Average per-agent regret. -/
def Ravg (V : ℝ) (EJ : ℝ) (n : ℕ) : ℝ := Rteam V EJ / n

lemma Phi_mono {f : ℕ → ℝ} (hf : ∀ s, 0 ≤ f s) : Monotone (Phi f) := by
  intro m u hmu
  unfold Phi
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hmu)
    (fun s _ _ => hf (s + 1))


/-! ## General finite-combinatorial helpers -/

/-- `Sfib u i k` is the set of rounds at which agent `i` pulls arm `k`. -/
def Sfib {n K T : ℕ} (u : Fin n → Fin T → Fin K) (i : Fin n) (k : Fin K) : Finset (Fin T) :=
  Finset.univ.filter (fun s => u i s = k)

lemma Ntot_eq_card_Sfib {n K T : ℕ} (u : Fin n → Fin T → Fin K) (i : Fin n) (k : Fin K) :
    Ntot u i k = (Sfib u i k).card := rfl

lemma Nfin_eq_fiber {n K T : ℕ} (u : Fin n → Fin T → Fin K) (t : Fin T) (i : Fin n)
    (k : Fin K) : Nfin u t i k = ((Sfib u i k).filter (fun s => s < t)).card := by
  unfold Nfin Sfib
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

/-- The number of rounds strictly before `t` within `S`. -/
lemma fiber_card_lt {T : ℕ} (S : Finset (Fin T)) {t t' : Fin T} (ht : t ∈ S) (ht' : t' ∈ S)
    (h : t < t') : (S.filter (fun s => s < t)).card < (S.filter (fun s => s < t')).card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro s hs
    simp only [Finset.mem_filter] at hs ⊢
    exact ⟨hs.1, lt_trans hs.2 h⟩
  · intro hEq
    have hmem : t ∈ S.filter (fun s => s < t') := by
      simp only [Finset.mem_filter]; exact ⟨ht, h⟩
    rw [← hEq] at hmem
    simp only [Finset.mem_filter] at hmem
    exact absurd hmem.2 (lt_irrefl t)

lemma fiber_card_mem {T : ℕ} (S : Finset (Fin T)) {t : Fin T} (ht : t ∈ S) :
    (S.filter (fun s => s < t)).card ∈ Finset.range S.card := by
  rw [Finset.mem_range]
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
  intro hEq
  have hmem : t ∈ S.filter (fun s => s < t) := by rw [hEq]; exact ht
  simp only [Finset.mem_filter] at hmem
  exact absurd hmem.2 (lt_irrefl t)

lemma fiber_card_inj {T : ℕ} (S : Finset (Fin T)) :
    Set.InjOn (fun t => (S.filter (fun s => s < t)).card) (↑S : Set (Fin T)) := by
  intro t ht t' ht' h
  change (S.filter (fun s => s < t)).card = (S.filter (fun s => s < t')).card at h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h1 : (S.filter (fun s => s < t)).card < (S.filter (fun s => s < t')).card :=
      fiber_card_lt S ht ht' hlt
    omega
  · have h1 : (S.filter (fun s => s < t')).card < (S.filter (fun s => s < t)).card :=
      fiber_card_lt S ht' ht hlt
    omega

/-- The map `t ↦ #{s ∈ S : s < t}` is a bijection from `S` onto `range S.card`. -/
lemma fiber_card_surj {T : ℕ} (S : Finset (Fin T)) :
    Set.SurjOn (fun t => (S.filter (fun s => s < t)).card) (↑S : Set (Fin T))
      (↑(Finset.range S.card) : Set ℕ) := by
  have himg : (S.image (fun t => (S.filter (fun s => s < t)).card)) = Finset.range S.card := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      exact fiber_card_mem S ht
    · exact le_of_eq (by
        rw [Finset.card_image_of_injOn (fiber_card_inj S), Finset.card_range])
  intro b hb
  rw [Finset.mem_coe] at hb
  have hb' : b ∈ S.image (fun t => (S.filter (fun s => s < t)).card) := by rw [himg]; exact hb
  rw [Finset.mem_image] at hb'
  obtain ⟨a, ha, hab⟩ := hb'
  exact ⟨a, ha, hab⟩

/-- Reindexing a sum over a finite set by the count of strictly smaller elements. -/
lemma fiber_shift {T : ℕ} (S : Finset (Fin T)) (f : ℕ → ℝ) :
    ∑ t ∈ S, f (1 + (S.filter (fun s => s < t)).card) = Phi f S.card := by
  rw [Phi]
  refine Finset.sum_nbij (fun t => (S.filter (fun s => s < t)).card) ?_
    (fiber_card_inj S) (fiber_card_surj S) ?_
  · intro t ht; exact fiber_card_mem S ht
  · intro t ht; rw [Nat.add_comm]

/-- Decomposition of a per-agent sum by the arm that was pulled. -/
lemma sum_by_arm {n K T : ℕ} (u : Fin n → Fin T → Fin K) (i : Fin n)
    (F : Fin T → Fin K → ℝ) :
    ∑ t : Fin T, F t (u i t) = ∑ k : Fin K, ∑ t ∈ Sfib u i k, F t k := by
  have h1 : ∀ t : Fin T, F t (u i t) = ∑ k : Fin K, (if k = u i t then F t k else 0) := by
    intro t
    rw [Finset.sum_ite_eq']
    simp
  calc ∑ t : Fin T, F t (u i t)
      = ∑ t : Fin T, ∑ k : Fin K, (if k = u i t then F t k else 0) :=
        Finset.sum_congr rfl fun t _ => h1 t
    _ = ∑ k : Fin K, ∑ t : Fin T, (if k = u i t then F t k else 0) := Finset.sum_comm
    _ = ∑ k : Fin K, ∑ t ∈ Sfib u i k, F t k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Sfib, Finset.sum_filter]
        refine Finset.sum_congr rfl fun t _ => ?_
        by_cases h : u i t = k
        · simp [h]
        · simp only [h, if_false]
          rw [if_neg (fun h' => h h'.symm)]

/-- Each agent pulls exactly `T` arms in total. -/
lemma sum_Ntot_eq {n K T : ℕ} (u : Fin n → Fin T → Fin K) (i : Fin n) :
    ∑ k, Ntot u i k = T := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin T)))
    (f := fun s : Fin T => u i s) (t := (Finset.univ : Finset (Fin K)))
    (fun a _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at h
  conv_rhs => rw [h]
  exact Finset.sum_congr rfl fun k _ => by simp [Ntot]


namespace DecayModel

variable (M : DecayModel n K)

/-- `(∑_k m_k : ℝ) = T` when `∑_k m_k = T`. -/
lemma cast_sum_eq {T : ℕ} {m : Fin K → ℕ} (hT : ∑ k, m k = T) :
    (∑ k, (m k : ℝ)) = (T : ℝ) := by
  rw [← hT, Nat.cast_sum]


/-- Partial sums of `f_k(s+1) − Δ_k` are bounded by `D_k`. -/
lemma sum_range_sub_le_Dk {k : Fin K} (hk : k ≠ M.star) (m : ℕ) :
    ∑ s ∈ Finset.range m, (M.f k (s + 1) - M.gap k) ≤ M.Dk k := by
  have hsummable := M.summable_DbTerm hk
  calc ∑ s ∈ Finset.range m, (M.f k (s + 1) - M.gap k)
      ≤ ∑ s ∈ Finset.range m, M.DbTerm k s := Finset.sum_le_sum fun s _ => le_max_left _ _
    _ ≤ ∑' s, M.DbTerm k s := hsummable.sum_le_tsum _ (fun s _ => M.DbTerm_nonneg k s)
    _ = M.Dk k := rfl

/-- `∑_{s=1}^{m} [Δ_k − f_k(s)] ≤ m Δ_k`. -/
lemma sum_range_gap_sub_le {k : Fin K} (m : ℕ) :
    ∑ s ∈ Finset.range m, (M.gap k - M.f k (s + 1)) ≤ (m : ℝ) * M.gap k := by
  calc ∑ s ∈ Finset.range m, (M.gap k - M.f k (s + 1))
      ≤ ∑ _s ∈ Finset.range m, M.gap k :=
        Finset.sum_le_sum fun s _ => by have := M.f_nonneg k (s + 1); linarith
    _ = (m : ℝ) * M.gap k := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- `∑_{s=1}^{m} (f_k(s+1) − Δ_k) = Φ_k(m) − m Δ_k`. -/
lemma sum_range_eq_Phi_sub {k : Fin K} (m : ℕ) :
    ∑ s ∈ Finset.range m, (M.f k (s + 1) - M.gap k)
      = Phi (M.f k) m - (m : ℝ) * M.gap k := by
  rw [Phi, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Decomposition of the serial allocation, `others`-summed form. -/
lemma serialAlloc_eq (m : Fin K → ℕ) :
    M.serialAlloc m
      = (∑ k, (m k : ℝ)) * M.b M.star + Phi (M.f M.star) (m M.star)
        + ∑ k ∈ M.others, (Phi (M.f k) (m k) - (m k : ℝ) * M.gap k) := by
  have h1 : M.serialAlloc m
      = ∑ k, ((m k : ℝ) * (M.b M.star - M.gap k) + Phi (M.f k) (m k)) := by
    simp only [serialAlloc, Fk]
    exact Finset.sum_congr rfl fun k _ => by
      have hbk : M.b k = M.b M.star - M.gap k := by rw [gap]; ring
      rw [hbk]
  rw [h1, Finset.sum_add_distrib]
  have hb : (∑ k, (m k : ℝ) * (M.b M.star - M.gap k))
      = (∑ k, (m k : ℝ)) * M.b M.star - ∑ k, (m k : ℝ) * M.gap k := by
    rw [show (∑ k, (m k : ℝ) * (M.b M.star - M.gap k))
        = ∑ k, ((m k : ℝ) * M.b M.star - (m k : ℝ) * M.gap k) from
          Finset.sum_congr rfl fun k _ => by ring]
    rw [Finset.sum_sub_distrib, Finset.sum_mul]
  rw [hb]
  have hs : (∑ k, Phi (M.f k) (m k))
      = Phi (M.f M.star) (m M.star) + ∑ k ∈ M.others, Phi (M.f k) (m k) := by
    rw [others, ← Finset.sum_erase_add _ _ (Finset.mem_univ M.star)]; ring
  have hg : (∑ k, (m k : ℝ) * M.gap k) = ∑ k ∈ M.others, (m k : ℝ) * M.gap k := by
    rw [others, ← Finset.sum_erase_add _ _ (Finset.mem_univ M.star)]
    have : (m M.star : ℝ) * M.gap M.star = 0 := by rw [gap_star, mul_zero]
    rw [this, add_zero]
  rw [hs, hg, Finset.sum_sub_distrib]
  ring

/-- **(A.7), first inequality.** For any allocation `m` with `∑_k m_k = T`,
`∑_k F_k(m_k) ≤ F_{k⋆}(T) + D_b`. -/
lemma serialAlloc_le_Fkstar_add_Db {T : ℕ} (m : Fin K → ℕ) (hT : ∑ k, m k = T) :
    M.serialAlloc m ≤ M.Fk M.star T + M.Db := by
  rw [M.serialAlloc_eq m, cast_sum_eq hT]
  have hsplit : ∑ k ∈ M.others, (Phi (M.f k) (m k) - (m k : ℝ) * M.gap k)
      = ∑ k ∈ M.others, ∑ s ∈ Finset.range (m k), (M.f k (s + 1) - M.gap k) :=
    Finset.sum_congr rfl fun k _ => (M.sum_range_eq_Phi_sub (k := k) (m k)).symm
  rw [hsplit]
  have hle : ∑ k ∈ M.others, ∑ s ∈ Finset.range (m k), (M.f k (s + 1) - M.gap k)
      ≤ ∑ k ∈ M.others, M.Dk k :=
    Finset.sum_le_sum fun k hk => M.sum_range_sub_le_Dk (Finset.mem_erase.mp hk).1 (m k)
  have hmstar : m M.star ≤ T := by
    have := Finset.single_le_sum (f := fun k => m k) (fun k _ => Nat.zero_le _)
      (Finset.mem_univ M.star)
    rwa [hT] at this
  have hPhi : Phi (M.f M.star) (m M.star) ≤ Phi (M.f M.star) T :=
    Phi_mono (fun s => M.f_nonneg M.star s) hmstar
  have hDb : M.Db = ∑ k ∈ M.others, M.Dk k := rfl
  simp only [Fk]
  rw [hDb]
  linarith [hle, hPhi]

/-- **(A.7), second inequality.** For any allocation `m` with `∑_k m_k = T` and `T ≥ 1`,
`F_{k⋆}(T) − ∑_k F_k(m_k) ≤ ∑_{k≠⋆} (Δ_k + ψ_{k⋆}(T)) m_k`. -/
lemma Fkstar_sub_serialAlloc_le {T : ℕ} (hT1 : 1 ≤ T) (m : Fin K → ℕ)
    (hT : ∑ k, m k = T) :
    M.Fk M.star T - M.serialAlloc m
      ≤ ∑ k ∈ M.others, (M.gap k + psi (M.f M.star) T) * (m k : ℝ) := by
  rw [M.serialAlloc_eq m, cast_sum_eq hT]
  have hsplit : ∑ k ∈ M.others, (Phi (M.f k) (m k) - (m k : ℝ) * M.gap k)
      = ∑ k ∈ M.others, ∑ s ∈ Finset.range (m k), (M.f k (s + 1) - M.gap k) :=
    Finset.sum_congr rfl fun k _ => (M.sum_range_eq_Phi_sub (k := k) (m k)).symm
  rw [hsplit]
  have hneg : ∑ k ∈ M.others, ∑ s ∈ Finset.range (m k), (M.f k (s + 1) - M.gap k)
      = - ∑ k ∈ M.others, ∑ s ∈ Finset.range (m k), (M.gap k - M.f k (s + 1)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
  rw [hneg]
  have hmstar : m M.star ≤ T := by
    have := Finset.single_le_sum (f := fun k => m k) (fun k _ => Nat.zero_le _)
      (Finset.mem_univ M.star)
    rwa [hT] at this
  have hTsub : ((T - m M.star : ℕ) : ℝ) = ∑ k ∈ M.others, (m k : ℝ) := by
    have h2 : (∑ k ∈ M.others, m k) = T - m M.star := by
      have := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin K))) (f := m)
        (Finset.mem_univ M.star)
      rw [others]
      omega
    rw [← h2, Nat.cast_sum]
  have htail := M.Phi_tail_bound M.star hmstar hT1
  have hgapsum : ∑ k ∈ M.others, ∑ s ∈ Finset.range (m k), (M.gap k - M.f k (s + 1))
      ≤ ∑ k ∈ M.others, (m k : ℝ) * M.gap k :=
    Finset.sum_le_sum fun k _ => M.sum_range_gap_sub_le (m k)
  have hfinal : ∑ k ∈ M.others, (M.gap k + psi (M.f M.star) T) * (m k : ℝ)
      = (∑ k ∈ M.others, (m k : ℝ) * M.gap k)
        + psi (M.f M.star) T * ∑ k ∈ M.others, (m k : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hfinal, ← hTsub]
  have hψ : 0 ≤ psi (M.f M.star) T := psi_nonneg (fun s _ => M.f_nonneg M.star s) T
  simp only [Fk]
  nlinarith [hgapsum, htail, hψ, mul_nonneg hψ (Nat.cast_nonneg (T - m M.star))]

end DecayModel

namespace DecayModel

variable (M : DecayModel n K)

/-- `ε_0(T) = ψ_{k⋆}(T)`. -/
lemma eps_zero (T : ℕ) : M.eps T 0 = psi (M.f M.star) T := by
  simp [DecayModel.eps]

/-- `ρ^{(λ)}_k(T) = Δ_k + ε_λ(T)` for `k ≠ ⋆`. -/
lemma rho_eq {T : ℕ} {lam : Fin 2} {k : Fin K} (hk : k ≠ M.star) :
    M.rho T lam k = M.gap k + M.eps T lam := by
  simp [DecayModel.rho, hk]

end DecayModel

/-- **The honest identity for personal fatigue**: `J^{(0)}_T(u) = ∑_i F_k(N_{i,k}(T))`. -/
theorem J0_eq_serial {T : ℕ} (M : DecayModel n K) (u : Fin n → Fin T → Fin K) :
    J0 M u = ∑ i, M.serialAlloc (fun k => Ntot u i k) := by
  rw [J0, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_by_arm u i (fun t k => M.mean k (qeff0 u t i k))]
  change ∑ k, ∑ t ∈ Sfib u i k, M.mean k (qeff0 u t i k) = ∑ k, M.Fk k (Ntot u i k)
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : ∑ t ∈ Sfib u i k, M.mean k (qeff0 u t i k)
      = (Sfib u i k).card * M.b k + Phi (M.f k) (Sfib u i k).card := by
    have h2 : ∑ t ∈ Sfib u i k, M.mean k (qeff0 u t i k)
        = ∑ t ∈ Sfib u i k, (M.b k + M.f k (1 + ((Sfib u i k).filter (fun s => s < t)).card)) := by
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [qeff0, Nfin_eq_fiber, DecayModel.mean]
    rw [h2, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      fiber_shift (Sfib u i k) (M.f k)]
  exact h1.trans (rfl : (Sfib u i k).card * M.b k + Phi (M.f k) (Sfib u i k).card
    = M.Fk k (Ntot u i k))

/-- **(A.7) upper bound on the personal-fatigue benchmark.** -/
theorem Vstar0_le {T : ℕ} (M : DecayModel n K) :
    Vstar0 (T := T) M ≤ (n : ℝ) * M.Fk M.star T + M.Gamma 0 := by
  rw [Vstar0]
  refine (Finset.sup'_le_iff _ _).mpr (fun u _ => ?_)
  rw [J0_eq_serial]
  have hterm : ∀ i : Fin n, M.serialAlloc (fun k => Ntot u i k) ≤ M.Fk M.star T + M.Db :=
    fun i => M.serialAlloc_le_Fkstar_add_Db (fun k => Ntot u i k) (sum_Ntot_eq u i)
  calc ∑ i, M.serialAlloc (fun k => Ntot u i k)
      ≤ ∑ _i : Fin n, (M.Fk M.star T + M.Db) := Finset.sum_le_sum fun i _ => hterm i
    _ = (n : ℝ) * (M.Fk M.star T + M.Db) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (n : ℝ) * M.Fk M.star T + M.Gamma 0 := by
        rw [show M.Gamma 0 = (n : ℝ) * M.Db from rfl]; ring

/-- **(A.7) trajectory conversion**: for any joint action sequence `u`,
`V^{⋆,0}_T − J^{(0)}_T(u) ≤ Γ_0 + ∑_{k≠⋆} ρ^{(0)}_k(T) M_k(T)`. -/
theorem regret_conversion_lambda0 {T : ℕ} (hT : 1 ≤ T) (M : DecayModel n K)
    (u : Fin n → Fin T → Fin K) :
    Vstar0 (T := T) M - J0 M u
      ≤ M.Gamma 0 + ∑ k ∈ M.others, M.rho T 0 k * (Mtot u k : ℝ) := by
  have hV := Vstar0_le (T := T) M
  have hJ : (n : ℝ) * M.Fk M.star T
      - ∑ k ∈ M.others, (M.gap k + psi (M.f M.star) T) * (Mtot u k : ℝ) ≤ J0 M u := by
    rw [J0_eq_serial]
    have hterm : ∀ i : Fin n, M.Fk M.star T
        - ∑ k ∈ M.others, (M.gap k + psi (M.f M.star) T) * (Ntot u i k : ℝ)
        ≤ M.serialAlloc (fun k => Ntot u i k) := fun i =>
      by linarith [M.Fkstar_sub_serialAlloc_le hT (fun k => Ntot u i k) (sum_Ntot_eq u i)]
    have hsum : ∑ i : Fin n, (M.Fk M.star T
        - ∑ k ∈ M.others, (M.gap k + psi (M.f M.star) T) * (Ntot u i k : ℝ))
        = (n : ℝ) * M.Fk M.star T
          - ∑ k ∈ M.others, (M.gap k + psi (M.f M.star) T) * (Mtot u k : ℝ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show (Mtot u k : ℝ) = ∑ i, (Ntot u i k : ℝ) from by rw [Mtot, Nat.cast_sum],
        Finset.mul_sum]
    rw [← hsum]
    exact Finset.sum_le_sum fun i _ => hterm i
  have hrhs : ∑ k ∈ M.others, (M.gap k + psi (M.f M.star) T) * (Mtot u k : ℝ)
      = ∑ k ∈ M.others, M.rho T 0 k * (Mtot u k : ℝ) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [M.rho_eq (Finset.mem_erase.mp hk).1, M.eps_zero]
  rw [hrhs] at hJ
  linarith


/-! ## Public-fatigue trajectory conversion ((A.8)) -/

/-- Number of agents that pull arm `k` in round `t`. -/
def Xpub {n K T : ℕ} (u : Fin n → Fin T → Fin K) (t : Fin T) (k : Fin K) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun i => u i t = k)).card

/-- Per-round decomposition of a per-agent sum by the arm pulled. -/
lemma sum_by_arm_round {n K T : ℕ} (u : Fin n → Fin T → Fin K) (t : Fin T)
    (F : Fin K → ℝ) :
    ∑ i : Fin n, F (u i t) = ∑ k : Fin K, (Xpub u t k : ℝ) * F k := by
  have h1 : ∀ i : Fin n, F (u i t) = ∑ k : Fin K, (if k = u i t then F k else 0) := by
    intro i
    rw [Finset.sum_ite_eq']; simp
  calc ∑ i : Fin n, F (u i t)
      = ∑ i : Fin n, ∑ k : Fin K, (if k = u i t then F k else 0) :=
        Finset.sum_congr rfl fun i _ => h1 i
    _ = ∑ k : Fin K, ∑ i : Fin n, (if k = u i t then F k else 0) := Finset.sum_comm
    _ = ∑ k : Fin K, ∑ i ∈ (Finset.univ.filter (fun i => u i t = k)), F k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases h : u i t = k
        · simp [h]
        · simp only [h, if_false]
          rw [if_neg (fun h' => h h'.symm)]
    _ = ∑ k : Fin K, (Xpub u t k : ℝ) * F k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul, Xpub]

/-- The public count before round `t` equals the sum of the per-round batch sizes. -/
lemma Cpub_eq {n K T : ℕ} (u : Fin n → Fin T → Fin K) (t : Fin T) (k : Fin K) :
    ∑ i : Fin n, Nfin u t i k
      = ∑ s ∈ (Finset.univ.filter (fun s : Fin T => s < t)), Xpub u s k := by
  have h1 : ∀ i : Fin n, Nfin u t i k
      = ∑ s : Fin T, (if s < t ∧ u i s = k then 1 else 0) := by
    intro i
    rw [Nfin, Finset.card_eq_sum_ones, Finset.sum_filter]
  have h2 : ∀ s : Fin T, ∑ i : Fin n, (if s < t ∧ u i s = k then 1 else 0)
      = if s < t then Xpub u s k else 0 := by
    intro s
    by_cases hs : s < t
    · rw [if_pos hs]
      have h3 : ∑ i : Fin n, (if s < t ∧ u i s = k then 1 else 0)
          = ∑ i : Fin n, (if u i s = k then 1 else 0) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [if_congr (and_iff_right hs) rfl rfl]
      rw [h3]
      simp only [Xpub, Finset.card_eq_sum_ones, Finset.sum_filter]
    · rw [if_neg hs]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [if_neg]
      exact fun h => hs h.1
  calc ∑ i : Fin n, Nfin u t i k
      = ∑ i : Fin n, ∑ s : Fin T, (if s < t ∧ u i s = k then 1 else 0) :=
        Finset.sum_congr rfl fun i _ => h1 i
    _ = ∑ s : Fin T, ∑ i : Fin n, (if s < t ∧ u i s = k then 1 else 0) := Finset.sum_comm
    _ = ∑ s : Fin T, (if s < t then Xpub u s k else 0) := Finset.sum_congr rfl fun s _ => h2 s
    _ = ∑ s ∈ (Finset.univ.filter (fun s : Fin T => s < t)), Xpub u s k := by
        rw [Finset.sum_filter]

/-- Per-arm batch-size list. -/
def blist {n K T : ℕ} (u : Fin n → Fin T → Fin K) (k : Fin K) : List ℕ :=
  List.ofFn (fun t : Fin T => Xpub u t k)

lemma blist_sum {n K T : ℕ} (u : Fin n → Fin T → Fin K) (k : Fin K) :
    (blist u k).sum = Mtot u k := by
  rw [blist, List.sum_ofFn]
  simp only [Mtot, Ntot, Xpub, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]

lemma sum_Mtot {n K T : ℕ} (u : Fin n → Fin T → Fin K) : ∑ k, Mtot u k = n * T := by
  simp only [Mtot]
  rw [Finset.sum_comm]
  simp only [sum_Ntot_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp

lemma fiber_sum_succ {T : ℕ} (X : Fin (T + 1) → ℕ) (t : Fin T) :
    ∑ s ∈ (Finset.univ.filter (fun s : Fin (T + 1) => s < t.succ)), X s
      = X 0 + ∑ i ∈ (Finset.univ.filter (fun i : Fin T => i < t)), X i.succ := by
  rw [Finset.sum_filter, Fin.sum_univ_succ, Finset.sum_filter]
  rw [if_pos (Fin.succ_pos t)]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [if_congr Fin.succ_lt_succ_iff rfl rfl]

lemma syncVal_ofFn (v : ℕ → ℝ) :
    ∀ (T : ℕ) (X : Fin T → ℕ) (c : ℕ),
      syncVal v c (List.ofFn X)
        = ∑ t : Fin T, (X t : ℝ)
            * v (c + (∑ s ∈ (Finset.univ.filter (fun s : Fin T => s < t)), X s) + 1)
  | 0, X, c => by simp [List.ofFn_zero]
  | T + 1, X, c => by
    rw [List.ofFn_succ, syncVal_cons, Fin.sum_univ_succ]
    rw [syncVal_ofFn v T (fun i : Fin T => X i.succ) (c + X 0)]
    congr 1
    · simp
    · refine Finset.sum_congr rfl fun t _ => ?_
      rw [fiber_sum_succ]
      congr 1
      congr 1
      omega



/-- `posPart` is monotone. -/
lemma posPart_mono : Monotone posPart := fun a b hab => max_le_max hab le_rfl

lemma syncVal_mono {v v' : ℕ → ℝ} (h : ∀ s, v s ≤ v' s) :
    ∀ (l : List ℕ) (c : ℕ), syncVal v c l ≤ syncVal v' c l
  | [], c => le_refl _
  | x :: xs, c => by
    rw [syncVal_cons, syncVal_cons]
    exact add_le_add (mul_le_mul_of_nonneg_left (h (c + 1)) (Nat.cast_nonneg x))
      (syncVal_mono h xs (c + x))

lemma syncVal_add_const (a : ℕ → ℝ) (b : ℝ) :
    ∀ (l : List ℕ) (c : ℕ), syncVal (fun s => a s + b) c l = syncVal a c l + (l.sum : ℝ) * b
  | [], c => by simp
  | x :: xs, c => by
    rw [syncVal_cons, syncVal_cons, syncVal_add_const a b xs (c + x), List.sum_cons]
    push_cast
    ring

/-- `syncVal` never exceeds the serial value plus the `(n-1)·v` batching error (zeros allowed). -/
lemma syncVal_le_serial' (v : ℕ → ℝ) (hv0 : ∀ s, 0 ≤ v s) (hvanti : Antitone v)
    (n : ℕ) :
    ∀ (l : List ℕ) (c : ℕ), (∀ x ∈ l, x ≤ n) →
      syncVal v c l ≤ serialVal v c l + (n - 1 : ℕ) * v (c + 1)
  | [], c, _ => by
    simp only [syncVal_nil, serialVal_nil, zero_add]
    exact mul_nonneg (Nat.cast_nonneg _) (hv0 (c + 1))
  | x :: xs, c, hxn => by
    have hxs : ∀ y ∈ xs, y ≤ n := fun y hy => hxn y (by simp [hy])
    rcases Nat.eq_zero_or_pos x with hx | hx
    · subst hx
      rw [syncVal_cons, serialVal_cons]
      simp only [Nat.cast_zero, zero_mul, zero_add, Finset.range_zero,
        Finset.sum_empty, add_zero]

      exact syncVal_le_serial' v hv0 hvanti n xs c hxs
    · rw [syncVal_cons, serialVal_cons]
      have hb := batchErr_upper hv0 hvanti (c := c) hx
      have hih := syncVal_le_serial' v hv0 hvanti n xs (c + x) hxs
      have hxn' : x ≤ n := hxn x (by simp)
      have hcastx : ((x - 1 : ℕ) : ℝ) = (x : ℝ) - 1 := by rw [Nat.cast_sub hx]; norm_num
      have hcastn : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (le_trans hx hxn')]; norm_num
      have hnx : ((x - 1 : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
        have : x - 1 ≤ n - 1 := by omega
        exact_mod_cast this
      have h1 : v (c + x + 1) ≤ v (c + x) := hvanti (by omega)
      have h2 : v (c + x) ≤ v (c + 1) := hvanti (by omega)
      have h3 : 0 ≤ v (c + 1) - v (c + x) := by linarith
      have hx1 : (0:ℝ) ≤ (x:ℝ) - 1 := by
        have : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
        linarith
      nlinarith [hb, hih, h1, h2, h3, hv0 (c + x + 1), hv0 (c + 1), hcastx, hcastn, hnx,
        mul_nonneg hx1 h3]

/-- `syncVal` never exceeds the serial value plus the `(n-1)·v(1)` batching error. -/
lemma syncVal_le_serial_add (v : ℕ → ℝ) (hv0 : ∀ s, 0 ≤ v s) (hvanti : Antitone v)
    (n : ℕ) (l : List ℕ) (hxn : ∀ x ∈ l, x ≤ n) :
    syncVal v 0 l ≤ Phi v l.sum + (n - 1 : ℕ) * v 1 := by
  have h := syncVal_le_serial' v hv0 hvanti n l 0 hxn
  rw [show serialVal v 0 l = Phi v l.sum from by simp [serialVal, Phi], Nat.zero_add] at h
  exact h

/-- `Xpub u t k ≤ n`. -/
lemma Xpub_le {n K T : ℕ} (u : Fin n → Fin T → Fin K) (t : Fin T) (k : Fin K) :
    Xpub u t k ≤ n := by
  calc Xpub u t k ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = n := by rw [Finset.card_univ, Fintype.card_fin]

lemma blist_le {n K T : ℕ} (u : Fin n → Fin T → Fin K) (k : Fin K) :
    ∀ x ∈ blist u k, x ≤ n := by
  intro x hx
  rw [blist, List.mem_ofFn] at hx
  obtain ⟨t, rfl⟩ := hx
  exact Xpub_le u t k

namespace DecayModel

variable (M : DecayModel n K)

lemma Phi_dbterm_le {k : Fin K} (hk : k ≠ M.star) (m : ℕ) :
    Phi (fun s => posPart (M.f k s - M.gap k)) m ≤ M.Dk k := by
  have hsummable := M.summable_DbTerm hk
  rw [Phi]
  calc ∑ s ∈ Finset.range m, posPart (M.f k (s + 1) - M.gap k)
      = ∑ s ∈ Finset.range m, M.DbTerm k s := rfl
    _ ≤ ∑' s, M.DbTerm k s := hsummable.sum_le_tsum _ (fun s _ => M.DbTerm_nonneg k s)
    _ = M.Dk k := rfl

lemma gap_sum_others (g : Fin K → ℝ) :
    ∑ k, g k * M.gap k = ∑ k ∈ M.others, g k * M.gap k := by
  rw [← Finset.sum_erase_add (s := (Finset.univ : Finset (Fin K)))
    (f := fun k => g k * M.gap k) (Finset.mem_univ M.star), others]
  rw [gap_star, mul_zero, add_zero]

lemma sum_erase_star (g : Fin K → ℝ) :
    ∑ k, g k = g M.star + ∑ k ∈ M.others, g k := by
  rw [others, ← Finset.sum_erase_add (s := (Finset.univ : Finset (Fin K)))
    (f := g) (Finset.mem_univ M.star)]
  ring

/-- For a suboptimal arm, `syncVal (f k) 0 l` is bounded by `D_k`, the batching error and the
value of the bottom gap. -/
lemma syncVal_fk_le {k : Fin K} (hk : k ≠ M.star) (l : List ℕ)
    (hxn : ∀ x ∈ l, x ≤ n) :
    syncVal (M.f k) 0 l
      ≤ M.Dk k + (n - 1 : ℕ) * posPart (M.f k 1 - M.gap k) + (l.sum : ℝ) * M.gap k := by
  have hpt : ∀ s, M.f k s ≤ posPart (M.f k s - M.gap k) + M.gap k := by
    intro s
    by_cases h : M.gap k ≤ M.f k s
    · rw [posPart_eq_self_of_nonneg (by linarith)]; linarith
    · rw [posPart_eq_zero_of_nonpos (by linarith)]; linarith
  have hanti : Antitone (fun s => posPart (M.f k s - M.gap k)) :=
    fun a b hab => posPart_mono (sub_le_sub_right (M.f_anti k hab) _)
  calc syncVal (M.f k) 0 l
      ≤ syncVal (fun s => posPart (M.f k s - M.gap k) + M.gap k) 0 l := syncVal_mono hpt l 0
    _ = syncVal (fun s => posPart (M.f k s - M.gap k)) 0 l + (l.sum : ℝ) * M.gap k :=
        syncVal_add_const _ _ l 0
    _ ≤ (Phi (fun s => posPart (M.f k s - M.gap k)) l.sum
          + (n - 1 : ℕ) * (fun s => posPart (M.f k s - M.gap k)) 1)
        + (l.sum : ℝ) * M.gap k := by
        gcongr
        exact syncVal_le_serial_add _ (fun s => posPart_nonneg _) hanti n l hxn
    _ ≤ M.Dk k + (n - 1 : ℕ) * posPart (M.f k 1 - M.gap k) + (l.sum : ℝ) * M.gap k := by
        have := M.Phi_dbterm_le hk l.sum
        linarith

end DecayModel

/-- **Public-fatigue bridge**: the joint-trajectory value equals the synchronous batch value. -/
theorem J1_eq_sync {T : ℕ} (M : DecayModel n K) (u : Fin n → Fin T → Fin K) :
    J1 M u = M.syncAlloc (fun k => blist u k) := by
  rw [J1]
  have hper : ∀ t : Fin T, ∑ i : Fin n, M.mean (u i t) (qeff1 u t (u i t))
      = ∑ k : Fin K, (Xpub u t k : ℝ)
          * M.mean k (1 + ∑ s ∈ (Finset.univ.filter (fun s : Fin T => s < t)), Xpub u s k) := by
    intro t
    rw [sum_by_arm_round u t (fun k => M.mean k (qeff1 u t k))]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    rw [qeff1, Cpub_eq]
  rw [Finset.sum_congr rfl fun t _ => hper t, Finset.sum_comm]
  rw [show M.syncAlloc (fun k => blist u k)
      = ∑ k, ((blist u k).sum : ℝ) * M.b k + ∑ k, syncVal (M.f k) 0 (blist u k) from rfl]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show ∑ t : Fin T, (Xpub u t k : ℝ)
        * M.mean k (1 + ∑ s ∈ (Finset.univ.filter (fun s : Fin T => s < t)), Xpub u s k)
      = (∑ t : Fin T, (Xpub u t k : ℝ)) * M.b k
        + ∑ t : Fin T, (Xpub u t k : ℝ)
          * M.f k (1 + ∑ s ∈ (Finset.univ.filter (fun s : Fin T => s < t)), Xpub u s k)
      from by
        rw [show (∑ t : Fin T, (Xpub u t k : ℝ)
              * M.mean k (1 + ∑ s ∈ (Finset.univ.filter (fun s : Fin T => s < t)), Xpub u s k))
            = ∑ t : Fin T, ((Xpub u t k : ℝ) * M.b k
              + (Xpub u t k : ℝ)
                * M.f k (1 + ∑ s ∈ (Finset.univ.filter (fun s : Fin T => s < t)), Xpub u s k))
            from Finset.sum_congr rfl fun t _ => by rw [DecayModel.mean]; ring]
        rw [Finset.sum_add_distrib, Finset.sum_mul]]
  have hff : ∑ t : Fin T, (Xpub u t k : ℝ)
        * M.f k (1 + ∑ s ∈ (Finset.univ.filter (fun s : Fin T => s < t)), Xpub u s k)
      = ∑ t : Fin T, (Xpub u t k : ℝ)
        * M.f k (0 + (∑ s ∈ (Finset.univ.filter (fun s : Fin T => s < t)), Xpub u s k) + 1) := by
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [show (1 + ∑ s ∈ (Finset.univ.filter (fun s : Fin T => s < t)), Xpub u s k)
        = (0 + (∑ s ∈ (Finset.univ.filter (fun s : Fin T => s < t)), Xpub u s k) + 1)
        from by omega]
  rw [blist, List.sum_ofFn, Nat.cast_sum, syncVal_ofFn, hff]

/-- **(A.8) lower bound**: `J^{(1)}_T(u) ≥ ∑_k F_k(M_k(T))`. -/
theorem J1_ge_serial {T : ℕ} (M : DecayModel n K) (u : Fin n → Fin T → Fin K) :
    M.serialAlloc (fun k => Mtot u k) ≤ J1 M u := by
  rw [J1_eq_sync]
  refine le_trans ?_ (M.serialAlloc_le_syncAlloc (fun k => blist u k))
  refine le_of_eq ?_
  exact Finset.sum_congr rfl fun k _ => by simp only [blist_sum]

/-- **(A.8) upper bound on the public-fatigue benchmark.** -/
theorem Vstar1_le {T : ℕ} (M : DecayModel n K) :
    Vstar1 (T := T) M ≤ (n : ℝ) * T * M.b M.star + Phi (M.f M.star) (n * T) + M.Db
      + (n - 1 : ℕ) * M.Aplus := by
  rw [Vstar1]
  refine (Finset.sup'_le_iff _ _).mpr (fun u _ => ?_)
  rw [J1_eq_sync]
  have hbsum : (∑ k : Fin K, ((blist u k).sum : ℝ)) = (n : ℝ) * T := by
    rw [← Nat.cast_sum]
    simp only [blist_sum]
    rw [sum_Mtot]
    push_cast; ring
  rw [show M.syncAlloc (fun k => blist u k)
      = ∑ k, ((blist u k).sum : ℝ) * M.b k + ∑ k, syncVal (M.f k) 0 (blist u k) from rfl]
  have hb : ∑ k : Fin K, ((blist u k).sum : ℝ) * M.b k
      = (n : ℝ) * T * M.b M.star
        - ∑ k ∈ M.others, ((blist u k).sum : ℝ) * M.gap k := by
    have hbk : ∀ k, M.b k = M.b M.star - M.gap k := fun k => by rw [DecayModel.gap]; ring
    rw [Finset.sum_congr rfl (fun k (_ : k ∈ (Finset.univ : Finset (Fin K))) => by rw [hbk k])]
    rw [show (∑ k : Fin K, ((blist u k).sum : ℝ) * (M.b M.star - M.gap k))
        = ∑ k : Fin K, (((blist u k).sum : ℝ) * M.b M.star
            - ((blist u k).sum : ℝ) * M.gap k)
        from Finset.sum_congr rfl fun k _ => by ring]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hbsum, M.gap_sum_others]
  have hs : ∑ k : Fin K, syncVal (M.f k) 0 (blist u k)
      ≤ Phi (M.f M.star) (n * T) + (n - 1 : ℕ) * M.f M.star 1
        + ∑ k ∈ M.others, (M.Dk k + (n - 1 : ℕ) * posPart (M.f k 1 - M.gap k)
            + ((blist u k).sum : ℝ) * M.gap k) := by
    rw [M.sum_erase_star (fun k => syncVal (M.f k) 0 (blist u k))]
    refine add_le_add ?_ (Finset.sum_le_sum fun k hk => ?_)
    · refine le_trans (syncVal_le_serial_add (M.f M.star) (fun s => M.f_nonneg M.star s)
          (M.f_anti M.star) n (blist u M.star) (blist_le u M.star)) ?_
      have hle : (blist u M.star).sum ≤ n * T := by
        rw [blist_sum]
        calc Mtot u M.star ≤ ∑ k, Mtot u k :=
              Finset.single_le_sum (f := fun k => Mtot u k) (fun k _ => Nat.zero_le _)
                (Finset.mem_univ M.star)
          _ = n * T := sum_Mtot u
      have := Phi_mono (fun s => M.f_nonneg M.star s) hle
      linarith [this]
    · exact M.syncVal_fk_le (Finset.mem_erase.mp hk).1 (blist u k) (blist_le u k)
  rw [hb]
  have hsum : ∑ k ∈ M.others, (M.Dk k + (n - 1 : ℕ) * posPart (M.f k 1 - M.gap k)
        + ((blist u k).sum : ℝ) * M.gap k)
      = M.Db + (n - 1 : ℕ) * (∑ k ∈ M.others, posPart (M.f k 1 - M.gap k))
        + ∑ k ∈ M.others, ((blist u k).sum : ℝ) * M.gap k := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, M.Db_eq_sum_Dk]
  rw [hsum] at hs
  have haplus : M.Aplus = M.f M.star 1 + ∑ k ∈ M.others, posPart (M.f k 1 - M.gap k) := rfl
  rw [haplus]
  linarith [hs]


/-- `ε_1(T) = ψ_{k⋆}(nT)`. -/
lemma DecayModel.eps_one (M : DecayModel n K) (T : ℕ) :
    M.eps T 1 = psi (M.f M.star) (n * T) := by
  simp [DecayModel.eps]

/-- Lower bound on the serial allocation: `∑_k F_k(m_k) ≥ S b_⋆ + Φ_⋆(m_⋆) − ∑_{k≠⋆} Δ_k m_k`
when `∑_k m_k = S`. -/
lemma serialAlloc_ge {S : ℕ} (M : DecayModel n K) (m : Fin K → ℕ)
    (hS : ∑ k, m k = S) :
    (S : ℝ) * M.b M.star + Phi (M.f M.star) (m M.star)
      - ∑ k ∈ M.others, (m k : ℝ) * M.gap k ≤ M.serialAlloc m := by
  rw [M.serialAlloc_eq m, DecayModel.cast_sum_eq hS]
  rw [Finset.sum_sub_distrib]
  have hnn : 0 ≤ ∑ k ∈ M.others, Phi (M.f k) (m k) :=
    Finset.sum_nonneg fun k _ => Phi_nonneg (fun s _ => M.f_nonneg k s) _
  linarith

/-- **(A.8) trajectory conversion**: for any joint action sequence `u`,
`V^{⋆,1}_T − J^{(1)}_T(u) ≤ Γ_1 + ∑_{k≠⋆} ρ^{(1)}_k(T) M_k(T)`. -/
theorem regret_conversion_lambda1 {T : ℕ} (hT : 1 ≤ T) (M : DecayModel n K)
    (u : Fin n → Fin T → Fin K) :
    Vstar1 (T := T) M - J1 M u
      ≤ M.Gamma 1 + ∑ k ∈ M.others, M.rho T 1 k * (Mtot u k : ℝ) := by
  have hV := Vstar1_le (T := T) M
  have hJ : M.serialAlloc (fun k => Mtot u k) ≤ J1 M u := J1_ge_serial M u
  have hlow := serialAlloc_ge M (fun k => Mtot u k) (sum_Mtot u)
  have hsum' : ∑ k, Mtot u k = n * T := sum_Mtot u
  have hmstar : Mtot u M.star ≤ n * T := by
    rw [← hsum']
    exact Finset.single_le_sum (f := fun k => Mtot u k) (fun k _ => Nat.zero_le _)
      (Finset.mem_univ M.star)
  have hnT1 : 1 ≤ n * T := by
    have h1 : 0 < n := by have := M.two_le_n; omega
    have h2 : 0 < T := by omega
    exact Nat.succ_le_of_lt (Nat.mul_pos h1 h2)
  have htail := M.Phi_tail_bound M.star hmstar hnT1
  have hcastN : ((n * T : ℕ) : ℝ) = (n : ℝ) * T := by push_cast; ring
  have hcast : ((n * T - Mtot u M.star : ℕ) : ℝ) = ∑ k ∈ M.others, (Mtot u k : ℝ) := by
    have h2 : ∑ k ∈ M.others, Mtot u k = n * T - Mtot u M.star := by
      have hs := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin K)))
        (f := fun k => Mtot u k) (Finset.mem_univ M.star)
      rw [hsum'] at hs
      simp only [DecayModel.others] at hs ⊢
      omega
    rw [← h2, Nat.cast_sum]
  have hbound : ∑ k ∈ M.others, (M.gap k + psi (M.f M.star) (n * T)) * (Mtot u k : ℝ)
      = (∑ k ∈ M.others, (Mtot u k : ℝ) * M.gap k)
        + psi (M.f M.star) (n * T) * ∑ k ∈ M.others, (Mtot u k : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hrhs : ∑ k ∈ M.others, (M.gap k + psi (M.f M.star) (n * T)) * (Mtot u k : ℝ)
      = ∑ k ∈ M.others, M.rho T 1 k * (Mtot u k : ℝ) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [M.rho_eq (Finset.mem_erase.mp hk).1, M.eps_one]
  have hgam : M.Gamma 1 = M.Db + (n - 1 : ℕ) * M.Aplus := by
    show (M.Db + (↑n - 1) * M.Aplus) = M.Db + (↑(n - 1)) * M.Aplus
    congr 2
    rw [Nat.cast_sub (by have := M.two_le_n; omega : 1 ≤ n)]
    norm_num
  have hge : (n : ℝ) * T * M.b M.star + Phi (M.f M.star) (n * T)
      + M.Db + (n - 1 : ℕ) * M.Aplus - J1 M u
      ≤ Phi (M.f M.star) (n * T) - Phi (M.f M.star) (Mtot u M.star)
        + ∑ k ∈ M.others, (Mtot u k : ℝ) * M.gap k + (M.Db + (n - 1 : ℕ) * M.Aplus) := by
    rw [hcastN] at hlow
    linarith [hlow, hJ]
  calc Vstar1 (T := T) M - J1 M u
      ≤ (n : ℝ) * T * M.b M.star + Phi (M.f M.star) (n * T) + M.Db
          + (n - 1 : ℕ) * M.Aplus - J1 M u := by linarith [hV]
    _ ≤ Phi (M.f M.star) (n * T) - Phi (M.f M.star) (Mtot u M.star)
          + ∑ k ∈ M.others, (Mtot u k : ℝ) * M.gap k + (M.Db + (n - 1 : ℕ) * M.Aplus) := hge
    _ ≤ (n * T - Mtot u M.star : ℕ) * psi (M.f M.star) (n * T)
          + ∑ k ∈ M.others, (Mtot u k : ℝ) * M.gap k + (M.Db + (n - 1 : ℕ) * M.Aplus) := by
        linarith [htail]
    _ = (∑ k ∈ M.others, (Mtot u k : ℝ) * M.gap k
          + psi (M.f M.star) (n * T) * ∑ k ∈ M.others, (Mtot u k : ℝ))
          + (M.Db + (n - 1 : ℕ) * M.Aplus) := by
        rw [hcast]; ring
    _ = (∑ k ∈ M.others, (M.gap k + psi (M.f M.star) (n * T)) * (Mtot u k : ℝ))
          + (M.Db + (n - 1 : ℕ) * M.Aplus) := by rw [hbound]
    _ = M.Gamma 1 + ∑ k ∈ M.others, M.rho T 1 k * (Mtot u k : ℝ) := by
        rw [hgam, hrhs]; ring


end AnvBandit
