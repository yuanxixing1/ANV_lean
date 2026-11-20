import AnvBandit.Execution
/-! Full-K, no-communication UCB transducer. Contacts are an ignored compatibility argument;
no state transition reads them. Personal statistics persist throughout the horizon. -/
noncomputable section
open scoped BigOperators
open Finset
namespace AnvBandit.BaselineExecution
abbrev Params := Execution.Params
variable {n K : ℕ}
structure LocalState (n K : ℕ) (i : Fin n) where
  seed : Fin K
  N : Fin K → ℕ
  Y : Fin K → ℝ
structure State (n K : ℕ) where
  nodes : (i : Fin n) → LocalState n K i
namespace LocalState
variable {i : Fin n}
def active (_s : LocalState n K i) : Finset (Fin K) := univ
theorem active_nonempty (s : LocalState n K i) : s.active.Nonempty :=
  ⟨s.seed, mem_univ _⟩
def unseen (s : LocalState n K i) : Finset (Fin K) := s.active.filter (fun k => s.N k = 0)

def index (p : Params n K) (s : LocalState n K i) (k : Fin K) : ℝ :=
  s.Y k / s.N k + rdelta p.L (s.N k)

/-- A finite implementation of least-index argmax with index `+∞` at unseen arms. -/
def choose (p : Params n K) (s : LocalState n K i) : Fin K :=
  if h : s.unseen.Nonempty then s.unseen.min' h
  else topArg (s.index p) s.active s.active_nonempty

theorem choose_mem (p : Params n K) (s : LocalState n K i) :
    s.choose p ∈ s.active := by
  unfold choose
  split
  · exact mem_of_mem_filter _ (Finset.min'_mem _ _)
  · exact topArg_mem _ _ _

/-- Exact comparison needed by UCB counting: an observed selected arm dominates every active
arm, all of which must then be observed. -/
theorem choose_spec (p : Params n K) (s : LocalState n K i) :
    s.N (s.choose p) = 0 ∨
      (∀ k ∈ s.active, 1 ≤ s.N k ∧ s.index p k ≤ s.index p (s.choose p)) := by
  unfold choose
  split
  · rename_i h
    left
    have hm : s.unseen.min' h ∈ s.unseen := s.unseen.min'_mem h
    exact (mem_filter.mp hm).2
  · right
    rename_i h
    intro k hk
    constructor
    · have hn : s.N k ≠ 0 := by
        intro hz
        exact h ⟨k, mem_filter.mpr ⟨hk, hz⟩⟩
      omega
    · exact topArg_max _ _ _ hk

def observe (p : Params n K) (s : LocalState n K i) (x : ℝ) : LocalState n K i :=
  { s with N := fun k => s.N k + if s.choose p = k then 1 else 0
           Y := fun k => s.Y k + if s.choose p = k then x else 0 }
end LocalState

def initial (p : Params n K) : State n K where
  nodes := fun _ => ⟨⟨0, by have := p.hK; omega⟩, fun _ => 0, fun _ => 0⟩
def actions (p : Params n K) (s : State n K) : Fin n → Fin K :=
  fun i => (s.nodes i).choose p
def observe (p : Params n K) (s : State n K) (x : Fin n → ℝ) : State n K :=
  ⟨fun i => (s.nodes i).observe p (x i)⟩
def step (p : Params n K) (t : ℕ) (s : State n K) (x : Fin n → ℝ)
    (_j : Fin n → Fin n) : State n K :=
  if t < p.T then observe p s x else s
def run (p : Params n K) (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n) : ℕ → State n K
  | 0 => initial p
  | t+1 => step p t (run p X J t) (X t) (J t)
@[simp] theorem run_succ (p : Params n K) (X : ℕ → Fin n → ℝ)
    (J : ℕ → Fin n → Fin n) (t : ℕ) :
    run p X J (t+1) = step p t (run p X J t) (X t) (J t) := rfl

theorem run_congr (p : Params n K) (X X' : ℕ → Fin n → ℝ)
    (J J' : ℕ → Fin n → Fin n) (t : ℕ)
    (hX : ∀ s, s < t → X s = X' s) : run p X J t = run p X' J' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [run_succ, step]
    rw [ih (fun s hs => hX s (by omega)), hX t (by omega)]

theorem contacts_ignored (p : Params n K) (X : ℕ → Fin n → ℝ)
    (J J' : ℕ → Fin n → Fin n) (t : ℕ) : run p X J t = run p X J' t :=
  run_congr p X X J J' t (fun _ _ => rfl)
def I (p : Params n K) (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n)
    (t : ℕ) : Fin n → Fin K := actions p (run p X J t)

def N (p : Params n K) (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n)
    (t : ℕ) (i : Fin n) (k : Fin K) : ℕ := ((run p X J t).nodes i).N k

def Y (p : Params n K) (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n)
    (t : ℕ) (i : Fin n) (k : Fin K) : ℝ := ((run p X J t).nodes i).Y k

@[simp] theorem N_zero (p : Params n K) (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n) (i : Fin n) (k : Fin K) :
    N p X J 0 i k = 0 := rfl
@[simp] theorem Y_zero (p : Params n K) (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n) (i : Fin n) (k : Fin K) :
    Y p X J 0 i k = 0 := rfl

theorem N_step (p : Params n K) (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n) {t : ℕ} (ht : t < p.T) (i : Fin n) (k : Fin K) :
    N p X J (t+1) i k = N p X J t i k + if I p X J t i = k then 1 else 0 := by
  simp only [N, run, step, if_pos ht]
  simp [observe, LocalState.observe, I, actions]

theorem Y_step (p : Params n K) (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n) {t : ℕ} (ht : t < p.T) (i : Fin n) (k : Fin K) :
    Y p X J (t+1) i k = Y p X J t i k + if I p X J t i = k then X t i else 0 := by
  simp only [Y, run, step, if_pos ht]
  simp [observe, LocalState.observe, I, actions]

theorem run_frozen (p : Params n K) (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n) {t : ℕ} (ht : p.T ≤ t) :
    run p X J (t+1) = run p X J t := by
  simp [run, step, Nat.not_lt.mpr ht]

/-- The transducer's counts are exactly the actual action indicators, not supplied data. -/
theorem N_eq_sum (p : Params n K) (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n) (t : ℕ) (ht : t ≤ p.T) (i : Fin n) (k : Fin K) :
    N p X J t i k = ∑ s ∈ range t, if I p X J s i = k then 1 else 0 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [N_step p X J (by omega), Finset.sum_range_succ, ih (by omega)]

/-- The transducer's reward sums contain only actually received rewards of this arm. -/
theorem Y_eq_sum (p : Params n K) (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n) (t : ℕ) (ht : t ≤ p.T) (i : Fin n) (k : Fin K) :
    Y p X J t i k = ∑ s ∈ range t, if I p X J s i = k then X s i else 0 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Y_step p X J (by omega), Finset.sum_range_succ, ih (by omega)]

theorem selected_mem (p : Params n K) (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n) (t : ℕ) (i : Fin n) :
    I p X J t i ∈ ((run p X J t).nodes i).active :=
  LocalState.choose_mem _ _

/-- Counts are monotone on the finite execution domain. -/
theorem N_mono (p : Params n K) (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n) {s t : ℕ} (hst : s ≤ t) (ht : t ≤ p.T)
    (i : Fin n) (k : Fin K) : N p X J s i k ≤ N p X J t i k := by
  rw [N_eq_sum p X J s (le_trans hst ht), N_eq_sum p X J t ht]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hst) (by intros; omega)

/-- A pathwise sum of the first `m` actually observed rewards, cut off at `T`.
Unobserved rewards contribute zero rather than imposing any hypothetical-prefix property. -/
def sampleSum (p : Params n K) (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n) (i : Fin n) (k : Fin K) (m : ℕ) : ℝ :=
  ∑ s ∈ range p.T, if I p X J s i = k ∧ N p X J s i k < m then X s i else 0

def empiricalPrefix (p : Params n K) (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n) (i : Fin n) (k : Fin K) (m : ℕ) : ℝ :=
  sampleSum p X J i k m / m

/-- Every index used by the algorithm is the empirical mean of the corresponding observed
prefix, not a separate unconstrained statistic. -/
theorem sampleSum_at_count (p : Params n K) (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n) (t : ℕ) (ht : t ≤ p.T)
    (i : Fin n) (k : Fin K) : sampleSum p X J i k (N p X J t i k) = Y p X J t i k := by
  rw [Y_eq_sum p X J t ht]
  unfold sampleSum
  calc (∑ s ∈ range p.T,
      if I p X J s i = k ∧ N p X J s i k < N p X J t i k then X s i else 0)
      = ∑ s ∈ range p.T, if s < t then (if I p X J s i = k then X s i else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro s hs
        by_cases hst : s < t
        · by_cases hsel : I p X J s i = k
          · have hstep := N_step p X J (show s < p.T by omega) i k
            rw [if_pos hsel] at hstep
            have hmono := N_mono p X J (show s+1 ≤ t by omega) ht i k
            have hlt : N p X J s i k < N p X J t i k := by omega
            simp [hst, hsel, hlt]
          · simp [hst, hsel]
        · have hmono := N_mono p X J (show t ≤ s by omega)
              (show s ≤ p.T by have := mem_range.mp hs; omega) i k
          have hnot : ¬ N p X J s i k < N p X J t i k := by omega
          simp [hst, hnot]
    _ = ∑ s ∈ range t, if I p X J s i = k then X s i else 0 := by
      rw [← Finset.sum_filter]
      congr 1
      ext s
      simp only [mem_filter, mem_range]
      omega

theorem empiricalPrefix_at_count (p : Params n K) (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n) (t : ℕ) (ht : t ≤ p.T)
    (i : Fin n) (k : Fin K) :
    empiricalPrefix p X J i k (N p X J t i k) = Y p X J t i k / N p X J t i k := by
  rw [empiricalPrefix, sampleSum_at_count p X J t ht]

/-- Every actual round contributes exactly one local pull, regardless of phase updates. -/
theorem sum_N (p : Params n K) (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n) (t : ℕ) (ht : t ≤ p.T) (i : Fin n) :
    (∑ k, N p X J t i k) = t := by
  simp_rw [N_eq_sum p X J t ht]
  rw [Finset.sum_comm]
  simp

/-- The public count, computed by the environment, is never an input to `choose`. -/
def teamCount (p : Params n K) (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n) (t : ℕ) (k : Fin K) : ℕ :=
  ∑ i, N p X J t i k

theorem team_total (p : Params n K) (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n) (t : ℕ) (ht : t ≤ p.T) :
    (∑ k, teamCount p X J t k) = n * t := by
  unfold teamCount
  rw [Finset.sum_comm]
  simp [sum_N p X J t ht]

theorem N_le_time (p : Params n K) (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n) (t : ℕ) (ht : t ≤ p.T)
    (i : Fin n) (k : Fin K) : N p X J t i k ≤ t := by
  calc N p X J t i k ≤ ∑ j, N p X J t i j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le _) (mem_univ k)
    _ = t := sum_N p X J t ht i

theorem pullCount_eq_N (p : Params n K) (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n) (t : ℕ) (ht : t ≤ p.T)
    (i : Fin n) (k : Fin K) : pullCount (I p X J) t i k = N p X J t i k :=
  (N_eq_sum p X J t ht i k).symm

/-- Bridge into the finite deterministic counting layer. The two hypotheses are explicitly
finite-event obligations for the probability/environment layer, not an algorithm definition.
All selection, count and empirical-statistic fields are proved from the actual executor. -/
def goodRunOnOfBounds (p : Params n K) (M : DecayModel n K) (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n)
    (meanSum : Fin n → Fin K → ℕ → ℝ)
    (hp : ∀ i k m, 1 ≤ m → m ≤ N p X J p.T i k →
      M.b k ≤ meanSum i k m / m ∧ meanSum i k m / m ≤ M.b k + psi (M.f k) m)
    (hc : ∀ i k m, 1 ≤ m → m ≤ N p X J p.T i k →
      |empiricalPrefix p X J i k m - meanSum i k m / m|
        ≤ rdelta p.L m) : GoodRunOn M p.T where
  L := p.L
  hL := (Ldelta_pos p.hn p.hK p.hT p.hδ.1 p.hδ.2).le
  I := I p X J
  bhat := empiricalPrefix p X J
  meanSum := meanSum
  mean_bounds := by
    intro i k m hm hobs
    apply hp i k m hm
    simpa [pullCount_eq_N p X J p.T le_rfl] using hobs
  hc := by
    intro i k m hm hobs
    apply hc i k m hm
    simpa [pullCount_eq_N p X J p.T le_rfl] using hobs
  active := fun t i => ((run p X J t).nodes i).active
  sel_mem := fun t _ i => selected_mem p X J t i
  ucb := by
    intro t ht i hstar
    simp only [pullCount_eq_N p X J t (Nat.le_of_lt ht)]
    have hchoose := LocalState.choose_spec p ((run p X J t).nodes i)
    rcases hchoose with hz | hall
    · exact Or.inl hz
    · right
      have hsel := hall (I p X J t i) (selected_mem p X J t i)
      have hs := hall M.star hstar
      refine ⟨hsel.1, hs.1, ?_⟩
      rw [empiricalPrefix_at_count p X J t (Nat.le_of_lt ht),
        empiricalPrefix_at_count p X J t (Nat.le_of_lt ht)]
      exact hs.2


end AnvBandit.BaselineExecution
