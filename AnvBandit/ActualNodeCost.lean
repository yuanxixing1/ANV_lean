import AnvBandit.ExecutionPhases

/-!
# Actual per-node elimination accounting

The deterministic removal budget is proved for the executable state transition, not supplied
as an algorithm hypothesis. A repeated arm is charged only once by the finite union below.
Communication at the terminal horizon is excluded by the executor itself.
-/
noncomputable section
open Finset
namespace AnvBandit.Execution
variable {n K : ℕ}

/-- One actual receive can discard at most one distinct previously active arm. -/
theorem LocalState.receive_removed_card {i : Fin n} (s : LocalState n K i) (o : Fin K) :
    (s.active \ (s.receive o).active).card ≤ 1 := by
  by_cases ho : o ∈ s.active
  · unfold LocalState.receive
    rw [dif_pos ho]
    simp [LocalState.active]
  · have hsub : s.active \ (s.receive o).active ⊆ s.D.erase s.topD := by
      intro k hk
      obtain ⟨hk, hn⟩ := mem_sdiff.mp hk
      have hnsticky : k ∉ sticky n i := fun h => hn (LocalState.receive_sticky s o k h)
      have hD : k ∈ s.D := (mem_union.mp hk).resolve_left hnsticky
      have hne : k ≠ s.topD := by
        intro heq
        subst k
        exact hn (by
          unfold LocalState.receive
          rw [dif_neg ho]
          change s.topD ∈ sticky n i ∪ {s.topD, o}
          exact mem_union_right _ (mem_insert_self _ _))
      exact mem_erase.mpr ⟨hne, hD⟩
    have hc := card_le_card hsub
    rw [card_erase_of_mem s.topD_mem] at hc
    have hs := s.card_le
    omega

/-- The number of newly removed arms is bounded by the actual phase increment (zero or one). -/
theorem step_removed_card (p : Params n K) (t : ℕ) (s : State n K)
    (x : Fin n → ℝ) (j : Fin n → Fin n) (i : Fin n) :
    ((s.nodes i).active \ ((step p t s x j).nodes i).active).card + s.phase
      ≤ (step p t s x j).phase := by
  by_cases ht : t < p.T
  · by_cases hc : communicates p t s
    · simp only [step, if_pos ht, if_pos hc]
      have hb := ((observe p s x).nodes i).receive_removed_card
        (((observe p s x).nodes (j i)).cache)
      change ((s.nodes i).active \ (((observe p s x).nodes i).receive
        (((observe p s x).nodes (j i)).cache)).active).card + s.phase ≤ s.phase + 1
      change ((s.nodes i).active \ (((observe p s x).nodes i).receive
        (((observe p s x).nodes (j i)).cache)).active).card ≤ 1 at hb
      omega
    · simp [step, ht, hc, observe, LocalState.observe, LocalState.active]
  · simp [step, ht]

/-- Distinct arms discarded in the half-open interval of rounds `[a,a+len)`. -/
def removedDuring (p : Params n K) (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n) (i : Fin n) (a : ℕ) : ℕ → Finset (Fin K)
  | 0 => ∅
  | len + 1 => removedDuring p X J i a len ∪
      (((run p X J (a+len)).nodes i).active \ ((run p X J (a+len+1)).nodes i).active)

/-- Removal accounting counts actual updates; no statistical or reliability premise occurs. -/
theorem removedDuring_card (p : Params n K) (X J) (i : Fin n) (a len : ℕ) :
    (removedDuring p X J i a len).card + (run p X J a).phase
      ≤ (run p X J (a+len)).phase := by
  induction len with
  | zero => simp [removedDuring]
  | succ len ih =>
    have hc := card_union_le (removedDuring p X J i a len)
      (((run p X J (a+len)).nodes i).active \ ((run p X J (a+len+1)).nodes i).active)
    have hs := step_removed_card p (a+len) (run p X J (a+len)) (X (a+len))
      (J (run p X J (a+len)).phase) i
    rw [← run_succ] at hs
    change (removedDuring p X J i a len ∪
      (((run p X J (a+len)).nodes i).active \ ((run p X J (a+len+1)).nodes i).active)).card
      + (run p X J a).phase ≤ (run p X J (a+(len+1))).phase
    have heq : a + (len + 1) = a + len + 1 := by omega
    rw [heq]
    omega

/-- Any arm previously present but absent at the endpoint was discarded at an actual update. -/
theorem mem_removedDuring (p : Params n K) (X J) (i : Fin n) (a len r : ℕ)
    (hr : r ≤ len) (k : Fin K)
    (hk : k ∈ ((run p X J (a+r)).nodes i).active)
    (hn : k ∉ ((run p X J (a+len)).nodes i).active) :
    k ∈ removedDuring p X J i a len := by
  induction len with
  | zero =>
    have he : r = 0 := by omega
    subst r
    exact (hn hk).elim
  | succ len ih =>
    by_cases hr' : r ≤ len
    · by_cases hm : k ∈ ((run p X J (a+len)).nodes i).active
      · apply mem_union_right
        exact mem_sdiff.mpr ⟨hm, by simpa [Nat.add_assoc] using hn⟩
      · exact mem_union_left _ (ih hr' hm)
    · have : r = len + 1 := by omega
      subst r
      exact (hn hk).elim

/-- Distinct selected arms missing at the endpoint are bounded by elapsed actual updates.
This remains valid under reinsertion: the union never resets an arm's budget. -/
theorem lost_selected_card (p : Params n K) (X J) (i : Fin n) (a len : ℕ) :
    ((univ : Finset (Fin K)).filter (fun k =>
      k ∉ ((run p X J (a+len)).nodes i).active ∧
      ∃ r < len, I p X J (a+r) i = k)).card
      ≤ (run p X J (a+len)).phase - (run p X J a).phase := by
  have hsub : ((univ : Finset (Fin K)).filter (fun k =>
      k ∉ ((run p X J (a+len)).nodes i).active ∧
      ∃ r < len, I p X J (a+r) i = k)) ⊆ removedDuring p X J i a len := by
    intro k hk
    obtain ⟨_, hn, r, hr, heq⟩ := mem_filter.mp hk
    apply mem_removedDuring p X J i a len r (by omega) k
    · rw [← heq]
      exact ((run p X J (a+r)).nodes i).choose_mem p
    · exact hn
  have hc := card_le_card hsub
  have hb := removedDuring_card p X J i a len
  omega

/-- A stopped run cannot have executed more communication updates than nominal boundaries.
This includes `t = T`, where the final boundary causes no communication. -/
theorem phase_le_of_time_le (p : Params n K) (X J) (r t : ℕ)
    (ht : t ≤ p.phaseEnd r) : (run p X J t).phase ≤ r + 1 := by
  induction t with
  | zero => simp [run, initial]
  | succ t ih =>
    have hi := ih (by omega)
    rw [run_succ]
    by_cases hT : t < p.T
    · by_cases hc : communicates p t (run p X J t)
      · have hphase : (run p X J t).phase ≤ r :=
          p.phaseEnd_strictMono.le_iff_le.mp (by rw [← hc.1]; exact ht)
        simp only [step, if_pos hT, if_pos hc, communicate, observe]
        omega
      · simpa [step, hT, hc, observe] using hi
    · simpa [step, hT] using hi

/-- The paper's exact `τ − σᵢ` elimination budget, prior to replacing a stable endpoint by `T`.
The endpoint may be horizon-truncated; no artificial communication is performed there. -/
theorem lost_selected_card_phase_interval (p : Params n K) (X J) (i : Fin n)
    (s r b : ℕ) (ha : p.phaseEnd s < p.T) (hab : p.phaseEnd s ≤ b)
    (hb : b ≤ p.phaseEnd r) :
    ((univ : Finset (Fin K)).filter (fun k =>
      k ∉ ((run p X J b).nodes i).active ∧
      ∃ t ∈ range b, p.phaseEnd s ≤ t ∧ I p X J t i = k)).card ≤ r - s := by
  have hbase := lost_selected_card p X J i (p.phaseEnd s) (b - p.phaseEnd s)
  have he : p.phaseEnd s + (b - p.phaseEnd s) = b := by omega
  rw [he] at hbase
  have hset : ((univ : Finset (Fin K)).filter (fun k =>
      k ∉ ((run p X J b).nodes i).active ∧
      ∃ t ∈ range b, p.phaseEnd s ≤ t ∧ I p X J t i = k)) =
      ((univ : Finset (Fin K)).filter (fun k =>
      k ∉ ((run p X J b).nodes i).active ∧
      ∃ j < b - p.phaseEnd s, I p X J (p.phaseEnd s+j) i = k)) := by
    ext k
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hn, t, ht, hat, hk⟩
      refine ⟨hn, t-p.phaseEnd s, ?_, ?_⟩
      · have := mem_range.mp ht; omega
      · have he' : p.phaseEnd s + (t-p.phaseEnd s) = t := by omega
        simpa [he'] using hk
    · rintro ⟨hn, j, hj, hk⟩
      exact ⟨hn, p.phaseEnd s+j, mem_range.mpr (by omega), by omega, hk⟩
  rw [hset]
  have hstart := phase_at_boundary p X J s ha
  have hend := phase_le_of_time_le p X J r b hb
  rw [hstart] at hbase
  omega

/-- Stable-tail adapter: once full active sets stabilize, no later selected arm can be lost.
The application obtains `hstable` from actual reliable communication, not as a model field. -/
theorem lost_selected_card_of_stable (p : Params n K) (X J) (i : Fin n)
    (s r b : ℕ) (ha : p.phaseEnd s < p.T) (hab : p.phaseEnd s ≤ b)
    (hb : b ≤ p.phaseEnd r) (hbT : b ≤ p.T)
    (hstable : ∀ t, b ≤ t → t ≤ p.T →
      ((run p X J t).nodes i).active = ((run p X J b).nodes i).active) :
    ((univ : Finset (Fin K)).filter (fun k =>
      k ∉ ((run p X J p.T).nodes i).active ∧
      ∃ t ∈ range p.T, p.phaseEnd s ≤ t ∧ I p X J t i = k)).card ≤ r - s := by
  refine (card_le_card ?_).trans (lost_selected_card_phase_interval p X J i s r b ha hab hb)
  intro k hk
  obtain ⟨_, hn, t, ht, hat, hsel⟩ := mem_filter.mp hk
  have htb : t < b := by
    by_contra hh
    have hmem : k ∈ ((run p X J t).nodes i).active := by
      rw [← hsel]
      exact ((run p X J t).nodes i).choose_mem p
    rw [hstable t (by omega) (mem_range.mp ht).le] at hmem
    rw [hstable p.T hbT le_rfl] at hn
    exact hn hmem
  refine mem_filter.mpr ⟨mem_univ _, ?_, t, mem_range.mpr htb, hat, hsel⟩
  simpa only [hstable p.T hbT le_rfl] using hn

end AnvBandit.Execution
