import AnvBandit.AlgLine
import AnvBandit.Terminal
import AnvBandit.ScheduleLower

/-!
# Actual finite-horizon execution of Algorithm 1

This is a deterministic transducer of reward vectors and phase-indexed contact vectors.
It has no field asserting concentration, reliability, stability, or a loss bound.
Actions use only the public confidence constant and the node's own statistics.
Round `t` is paper round `t+1`; all nodes act before any reward update.
-/
noncomputable section
open scoped BigOperators
open Finset
namespace AnvBandit.Execution

/-- Public inputs only. In particular, no `DecayModel` is available to this type. -/
structure Params (n K : ℕ) where
  hn : 2 ≤ n
  hK : 2 ≤ K
  T : ℕ
  hT : 1 ≤ T
  h : ℕ
  hh : 1 ≤ h
  H : ℕ
  hH : 1 ≤ H
  hdiv : h ∣ H
  δ : ℝ
  hδ : 0 < δ ∧ δ < 1
  β : ℝ
  hβ : 1 < β

variable {n K : ℕ}

def Params.L (p : Params n K) : ℝ := Ldelta n K p.T p.δ

/-- The public execution configuration satisfies exactly the shared legal parameter domain. -/
theorem Params.legal (p : Params n K) :
    LegalParameters n K p.T p.h p.H p.δ p.β :=
  ⟨p.hn, p.hK, p.hT, p.hh, p.hH, p.hdiv, p.hδ.1, p.hδ.2, p.hβ⟩

def Params.phaseEnd (p : Params n K) (ℓ : ℕ) : ℕ :=
  p.H * ⌈(ℓ : ℝ) ^ p.β⌉₊

@[simp] theorem Params.phaseEnd_zero (p : Params n K) : p.phaseEnd 0 = 0 := by
  simp [Params.phaseEnd, Real.zero_rpow (show p.β ≠ 0 by linarith [p.hβ])]

@[simp] theorem Params.phaseEnd_one (p : Params n K) : p.phaseEnd 1 = p.H := by
  simp [Params.phaseEnd]

/-- Strictly increasing endpoints; this does not assert monotonicity of rounded phase lengths. -/
theorem Params.phaseEnd_strictMono (p : Params n K) : StrictMono p.phaseEnd := by
  have hH := p.hH
  apply strictMono_nat_of_lt_succ
  intro ℓ
  by_cases hzero : ℓ = 0
  · subst ℓ
    simp only [phaseEnd_zero, zero_add, phaseEnd_one]
    omega
  · have hℓ : (1 : ℝ) ≤ ℓ := by exact_mod_cast (show 1 ≤ ℓ by omega)
    have hr := rpow_sub_ge (a := (ℓ : ℝ)) (b := (ℓ : ℝ)+1)
      (p := p.β) (by positivity) (by positivity) p.hβ.le
    have hone : 1 ≤ (ℓ : ℝ) ^ (p.β-1) := Real.one_le_rpow hℓ (by linarith [p.hβ])
    have hmul : p.β ≤ p.β * (ℓ : ℝ) ^ (p.β-1) :=
      le_mul_of_one_le_right (by linarith [p.hβ]) hone
    have hpow : (ℓ : ℝ) ^ p.β + 1 ≤ ((ℓ : ℝ)+1) ^ p.β := by
      have hp := p.hβ
      nlinarith
    have hc := Nat.ceil_mono hpow
    rw [Nat.ceil_add_one (Real.rpow_nonneg (Nat.cast_nonneg ℓ) p.β)] at hc
    have hceil : ⌈(ℓ : ℝ)^p.β⌉₊ < ⌈((ℓ+1 : ℕ) : ℝ)^p.β⌉₊ := by
      simp only [Nat.cast_add, Nat.cast_one]
      omega
    exact Nat.mul_lt_mul_of_pos_left hceil (by omega)

/-- Paper equation (3.1), with zero-based node and arm labels. -/
def sticky (n : ℕ) (i : Fin n) : Finset (Fin K) :=
  permSet n K i

@[simp] theorem mem_sticky (i : Fin n) (k : Fin K) :
    k ∈ sticky n i ↔ k.val % n = i.val := by simp [sticky, permSet]

theorem sticky_disjoint {i j : Fin n} (hij : i ≠ j) :
    Disjoint (sticky n i : Finset (Fin K)) (sticky n j) := by
  apply Finset.disjoint_left.mpr
  intro k hi hj
  apply hij
  apply Fin.ext
  exact ((mem_sticky i k).mp hi).symm.trans ((mem_sticky j k).mp hj)

def holder (p : Params n K) (k : Fin K) : Fin n :=
  ⟨k.val % n, Nat.mod_lt _ (by have := p.hn; omega)⟩

@[simp] theorem mem_sticky_holder (p : Params n K) (k : Fin K) :
    k ∈ sticky n (holder p k) := by simp [holder]

theorem holder_unique (p : Params n K) (k : Fin K) (i : Fin n)
    (hi : k ∈ sticky n i) : i = holder p k := by
  apply Fin.ext
  exact ((mem_sticky i k).mp hi).symm

theorem complement_nonempty (p : Params n K) (i : Fin n) :
    (univ \ sticky n i : Finset (Fin K)).Nonempty := by
  have hn := p.hn
  have hK := p.hK
  by_cases hi : i.val = 0
  · refine ⟨⟨1, by omega⟩, mem_sdiff.mpr ⟨mem_univ _, ?_⟩⟩
    simp only [mem_sticky, Fin.val_mk]
    rw [Nat.mod_eq_of_lt (show 1 < n by omega)]
    omega
  · refine ⟨⟨0, by omega⟩, mem_sdiff.mpr ⟨mem_univ _, ?_⟩⟩
    simp only [mem_sticky, Fin.val_mk, Nat.zero_mod]
    omega

/-- The modulo allocation has at most the paper's ceiling share at each node. -/
theorem sticky_card_le (p : Params n K) (i : Fin n) :
    (sticky n i : Finset (Fin K)).card ≤ ⌈(K : ℝ) / n⌉₊ := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := p.hn; omega)
  have hmap : Set.MapsTo (fun k : Fin K => k.val / n)
      (↑(sticky n i : Finset (Fin K)) : Set (Fin K)) (↑(range ⌈(K : ℝ) / n⌉₊) : Set ℕ) := by
    intro k hk
    apply mem_range.mpr
    rw [Nat.lt_ceil, lt_div_iff₀ hn]
    have hd := Nat.div_mul_le_self k.val n
    have hlt : k.val / n * n < K := lt_of_le_of_lt hd k.isLt
    exact_mod_cast hlt
  have hinj : Set.InjOn (fun k : Fin K => k.val / n) (↑(sticky n i : Finset (Fin K)) : Set (Fin K)) := by
    intro a ha b hb heq
    dsimp only at heq
    have hma := (mem_sticky i a).mp ha
    have hmb := (mem_sticky i b).mp hb
    apply Fin.ext
    have hda := Nat.mod_add_div a.val n
    have hdb := Nat.mod_add_div b.val n
    rw [hma, heq] at hda
    rw [hmb] at hdb
    omega
  have hc := Finset.card_le_card_of_injOn (fun k : Fin K => k.val / n) hmap hinj
  simpa using hc

/-- Exactly the first one or two elements of a nonempty finite ordered set. -/
def firstTwo (S : Finset (Fin K)) (hS : S.Nonempty) : Finset (Fin K) :=
  let a := S.min' hS
  if h : (S.erase a).Nonempty then {a, (S.erase a).min' h} else {a}

theorem firstTwo_nonempty (S : Finset (Fin K)) (hS : S.Nonempty) :
    (firstTwo S hS).Nonempty := by
  dsimp only [firstTwo]
  split <;> simp

theorem firstTwo_card_le (S : Finset (Fin K)) (hS : S.Nonempty) :
    (firstTwo S hS).card ≤ 2 := by
  dsimp only [firstTwo]
  split
  · exact le_trans (Finset.card_insert_le _ _) (by simp)
  · simp

theorem firstTwo_subset (S : Finset (Fin K)) (hS : S.Nonempty) :
    firstTwo S hS ⊆ S := by
  intro k hk
  dsimp only [firstTwo] at hk
  split at hk
  · simp only [mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact S.min'_mem hS
    · exact mem_of_mem_erase (Finset.min'_mem _ _)
  · simp only [mem_singleton] at hk
    subst k
    exact S.min'_mem hS

theorem firstTwo_card (S : Finset (Fin K)) (hS : S.Nonempty) :
    (firstTwo S hS).card = min 2 S.card := by
  dsimp only [firstTwo]
  split
  · rename_i h
    have ha := S.min'_mem hS
    have hb := mem_erase.mp ((S.erase (S.min' hS)).min'_mem h)
    have hc : 2 ≤ S.card := by
      have := Finset.card_pos.mpr h
      rw [Finset.card_erase_of_mem ha] at this
      omega
    simp [Ne.symm hb.1, min_eq_left hc]
  · rename_i h
    have heq : S = {S.min' hS} := by
      ext k
      simp only [mem_singleton]
      constructor
      · intro hk
        by_contra hne
        exact h ⟨k, mem_erase.mpr ⟨hne, hk⟩⟩
      · rintro rfl
        exact S.min'_mem hS
    have hc : S.card = 1 := by rw [heq]; simp
    simp [hc]

def initialD (p : Params n K) (i : Fin n) : Finset (Fin K) :=
  firstTwo (univ \ sticky n i) (complement_nonempty p i)

/-- Local state carries only elementary representation invariants; all constructors below prove
these invariants. No statistical or regret assertion is a state field. -/
structure LocalState (n K : ℕ) (i : Fin n) where
  D : Finset (Fin K)
  nonempty : D.Nonempty
  card_le : D.card ≤ 2
  disjoint : Disjoint (sticky n i) D
  N : Fin K → ℕ
  Y : Fin K → ℝ
  C : Fin K → ℕ

structure State (n K : ℕ) where
  nodes : (i : Fin n) → LocalState n K i
  phase : ℕ

namespace LocalState
variable {i : Fin n}
def active (s : LocalState n K i) : Finset (Fin K) := sticky n i ∪ s.D

theorem active_nonempty (s : LocalState n K i) : s.active.Nonempty :=
  s.nonempty.mono Finset.subset_union_right

theorem active_card_le (p : Params n K) (s : LocalState n K i) :
    s.active.card ≤ smax n K := by
  apply le_min
  · exact le_trans (Finset.card_le_card (Finset.subset_univ _)) (by simp)
  · have hu := Finset.card_union_le (sticky n i : Finset (Fin K)) s.D
    have hp := sticky_card_le p i
    have hd := s.card_le
    unfold active
    omega

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

/-- The cached recommendation uses the entire active set, not just `D`. -/
def cache (s : LocalState n K i) : Fin K :=
  topArg (fun k => (s.C k : ℝ)) s.active s.active_nonempty

def topD (s : LocalState n K i) : Fin K :=
  topArg (fun k => (s.C k : ℝ)) s.D s.nonempty

@[simp] theorem cache_mem (s : LocalState n K i) : s.cache ∈ s.active :=
  topArg_mem _ _ _

@[simp] theorem topD_mem (s : LocalState n K i) : s.topD ∈ s.D :=
  topArg_mem _ _ _

/-- All nodes are updated using the action fixed before this reward vector is supplied. -/
def observe (p : Params n K) (s : LocalState n K i) (x : ℝ) : LocalState n K i :=
  { s with
    N := fun k => s.N k + if s.choose p = k then 1 else 0
    Y := fun k => s.Y k + if s.choose p = k then x else 0
    C := fun k => s.C k + if s.choose p = k then 1 else 0 }

/-- Communication changes only `D` and phase counts. The cumulative statistics are retained. -/
def receive (s : LocalState n K i) (o : Fin K) : LocalState n K i :=
  if h : o ∈ s.active then { s with C := fun _ => 0 }
  else
    { D := {s.topD, o}
      nonempty := by simp
      card_le := le_trans (Finset.card_insert_le _ _) (by simp)
      disjoint := by
        apply Finset.disjoint_left.mpr
        intro k hk hnew
        simp only [mem_insert, mem_singleton] at hnew
        rcases hnew with rfl | rfl
        · exact Finset.disjoint_left.mp s.disjoint hk s.topD_mem
        · exact h (Finset.mem_union_left _ hk)
      N := s.N
      Y := s.Y
      C := fun _ => 0 }

@[simp] theorem receive_N (s : LocalState n K i) (o : Fin K) :
    (s.receive o).N = s.N := by unfold receive; split <;> rfl
@[simp] theorem receive_Y (s : LocalState n K i) (o : Fin K) :
    (s.receive o).Y = s.Y := by unfold receive; split <;> rfl
@[simp] theorem receive_C (s : LocalState n K i) (o : Fin K) :
    (s.receive o).C = fun _ => 0 := by unfold receive; split <;> rfl

theorem received_mem (s : LocalState n K i) (o : Fin K) :
    o ∈ (s.receive o).active := by
  unfold receive
  split
  · assumption
  · simp [active]

theorem receive_sticky (s : LocalState n K i) (o k : Fin K)
    (hk : k ∈ sticky n i) : k ∈ (s.receive o).active :=
  Finset.mem_union_left _ hk

theorem cache_eq_of_strict (s : LocalState n K i) (k : Fin K) (hk : k ∈ s.active)
    (hmax : ∀ j ∈ s.active, j ≠ k → s.C j < s.C k) : s.cache = k := by
  by_contra hne
  have hlt := hmax s.cache s.cache_mem hne
  have hge := topArg_max (fun j => (s.C j : ℝ)) s.active s.active_nonempty hk
  have hltR : (s.C s.cache : ℝ) < s.C k := by exact_mod_cast hlt
  exact (not_lt_of_ge hge) hltR

@[simp] theorem receive_D_of_mem (s : LocalState n K i) (o : Fin K) (ho : o ∈ s.active) :
    (s.receive o).D = s.D := by simp [receive, ho]

/-- Restricting the least argmax to a subset containing it does not change the result. -/
theorem topArg_restrict (c : Fin K → ℝ) (S D : Finset (Fin K))
    (hS : S.Nonempty) (hD : D.Nonempty) (hsub : D ⊆ S)
    (hmem : topArg c S hS ∈ D) : topArg c S hS = topArg c D hD := by
  have hma : topArg c S hS ∈ S.filter (fun k => c k = S.sup' hS c) :=
    Finset.min'_mem _ _
  have hmb : topArg c D hD ∈ D.filter (fun k => c k = D.sup' hD c) :=
    Finset.min'_mem _ _
  have ha := (mem_filter.mp hma).2
  have hb := (mem_filter.mp hmb).2
  have hab := topArg_max c D hD hmem
  have hba := topArg_max c S hS (hsub (topArg_mem c D hD))
  have heq : c (topArg c S hS) = c (topArg c D hD) := le_antisymm hab hba
  apply le_antisymm
  · apply topArg_min c S hS (hsub (topArg_mem c D hD))
    rw [← heq, ha]
  · apply topArg_min c D hD hmem
    rw [heq, hb]

/-- The cached full-active-set recommendation is retained, including when it lies in `D`. -/
theorem cache_retained (s : LocalState n K i) (o : Fin K) :
    s.cache ∈ (s.receive o).active := by
  by_cases hs : s.cache ∈ sticky n i
  · exact receive_sticky s o s.cache hs
  · have hd : s.cache ∈ s.D := (mem_union.mp s.cache_mem).resolve_left hs
    have heq : s.cache = s.topD :=
      topArg_restrict _ _ _ _ _ Finset.subset_union_right hd
    unfold receive
    split
    · exact s.cache_mem
    · simp [active, heq]

end LocalState

def initial (p : Params n K) : State n K where
  nodes i :=
    { D := initialD p i
      nonempty := firstTwo_nonempty _ _
      card_le := firstTwo_card_le _ _
      disjoint := by
        apply Finset.disjoint_left.mpr
        intro k hk hD
        have := firstTwo_subset _ (complement_nonempty p i) hD
        exact (mem_sdiff.mp this).2 hk
      N := fun _ => 0
      Y := fun _ => 0
      C := fun _ => 0 }
  phase := 1

/-- This vector is computed from the common pre-reward state. -/
def actions (p : Params n K) (s : State n K) : Fin n → Fin K :=
  fun i => (s.nodes i).choose p

def observe (p : Params n K) (s : State n K) (x : Fin n → ℝ) : State n K :=
  { s with nodes := fun i => (s.nodes i).observe p (x i) }

/-- Every returned recommendation is read from the same precommunication state `s`. -/
def communicate (s : State n K) (j : Fin n → Fin n) : State n K :=
  { nodes := fun i => (s.nodes i).receive ((s.nodes (j i)).cache)
    phase := s.phase + 1 }

/-- Once all cached recommendations are the already-held best arm, communication preserves
all active sets. This is a conditional update lemma, not an assumed stability property. -/
theorem communicate_sets_unchanged (s : State n K) (j : Fin n → Fin n) (k : Fin K)
    (hcache : ∀ i, (s.nodes i).cache = k)
    (hhold : ∀ i, k ∈ (s.nodes i).active) (i : Fin n) :
    ((communicate s j).nodes i).active = (s.nodes i).active := by
  simp [communicate, LocalState.active, hcache, LocalState.receive_D_of_mem _ _ (hhold i)]

/-- A communication occurs only at a complete nominal phase end strictly before `T`. -/
def communicates (p : Params n K) (t : ℕ) (s : State n K) : Prop :=
  t + 1 = p.phaseEnd s.phase ∧ t + 1 < p.T

instance (p : Params n K) (t : ℕ) (s : State n K) : Decidable (communicates p t s) :=
  inferInstanceAs (Decidable (t+1 = p.phaseEnd s.phase ∧ t+1 < p.T))

/-- One round; the process freezes after the horizon. Contacts are phase-indexed. -/
def step (p : Params n K) (t : ℕ) (s : State n K)
    (x : Fin n → ℝ) (j : Fin n → Fin n) : State n K :=
  if t < p.T then
    let s' := observe p s x
    if communicates p t s then communicate s' j else s'
  else s

/-- The actual state after `t` rounds, stopped at `T`.
`J ℓ` is the contact vector at the end of paper phase `ℓ≥1`; `J 0` is unused.
For the reliable-phase coupling, ideal step zero uses `J (rH+1)` and ideal set `Y j`
is compared at time `t_(rH+j)`. No contact is used at a terminal phase end. -/
def run (p : Params n K) (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n) : ℕ → State n K
  | 0 => initial p
  | t + 1 =>
    let s := run p X J t
    step p t s (X t) (J s.phase)

@[simp] theorem run_succ (p : Params n K) (X : ℕ → Fin n → ℝ)
    (J : ℕ → Fin n → Fin n) (t : ℕ) :
    run p X J (t+1) = step p t (run p X J t) (X t) (J (run p X J t).phase) := rfl

/-- States use no future rewards or contacts at uncompleted/terminal boundaries. -/
theorem run_congr (p : Params n K) (X X' : ℕ → Fin n → ℝ)
    (J J' : ℕ → Fin n → Fin n) (t : ℕ)
    (hX : ∀ s < t, X s = X' s)
    (hJ : ∀ ℓ, p.phaseEnd ℓ ≤ t → p.phaseEnd ℓ < p.T → J ℓ = J' ℓ) :
    run p X J t = run p X' J' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have he := ih (fun s hs => hX s (by omega))
      (fun ℓ hℓ hT => hJ ℓ (by omega) hT)
    rw [run_succ, run_succ, he]
    by_cases ht : t < p.T
    · simp only [step, if_pos ht, hX t (by omega)]
      by_cases hc : communicates p t (run p X' J' t)
      · simp only [if_pos hc]
        rw [hJ _ (by rw [← hc.1]) (by rw [← hc.1]; exact hc.2)]
      · simp only [if_neg hc]
    · simp only [step, if_neg ht]

/-- Finite history may store contacts only through this finite phase index. -/
theorem Params.le_phaseEnd (p : Params n K) (ℓ : ℕ) : ℓ ≤ p.phaseEnd ℓ := by
  induction ℓ with
  | zero => omega
  | succ ℓ ih =>
    have hs := p.phaseEnd_strictMono (Nat.lt_succ_self ℓ)
    simp only [Nat.succ_eq_add_one] at *
    omega

theorem phase_bounds (p : Params n K) (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n) (t : ℕ) :
    1 ≤ (run p X J t).phase ∧ (run p X J t).phase ≤ t+1 := by
  induction t with
  | zero => simp [run, initial]
  | succ t ih =>
    by_cases ht : t < p.T
    · simp only [run, step, if_pos ht]
      split <;> simp only [communicate, observe] <;> omega
    · simp only [run, step, if_neg ht]
      omega

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
  split <;> simp [communicate, observe, LocalState.observe, I, actions]

theorem Y_step (p : Params n K) (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n) {t : ℕ} (ht : t < p.T) (i : Fin n) (k : Fin K) :
    Y p X J (t+1) i k = Y p X J t i k + if I p X J t i = k then X t i else 0 := by
  simp only [Y, run, step, if_pos ht]
  split <;> simp [communicate, observe, LocalState.observe, I, actions]

theorem run_frozen (p : Params n K) (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n) {t : ℕ} (ht : p.T ≤ t) :
    run p X J (t+1) = run p X J t := by
  simp [run, step, Nat.not_lt.mpr ht]

theorem no_terminal_communication (p : Params n K) (t : ℕ) (s : State n K)
    (ht : p.T ≤ t + 1) : ¬ communicates p t s := by
  intro h
  exact (Nat.not_lt.mpr ht) h.2

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

theorem source_holds (p : Params n K) (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n) (t : ℕ) (k : Fin K) :
    k ∈ ((run p X J t).nodes (holder p k)).active :=
  mem_union_left _ (mem_sticky_holder p k)

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

theorem phaseEnd_multiple (p : Params n K) (ℓ : ℕ) : p.h ∣ p.phaseEnd ℓ := by
  exact dvd_mul_of_dvd_left p.hdiv _

theorem communication_legal (p : Params n K) (t : ℕ) (s : State n K)
    (hc : communicates p t s) : 0 < t + 1 ∧ p.h ∣ t + 1 ∧ t + 1 < p.T := by
  exact ⟨by omega, hc.1.symm ▸ phaseEnd_multiple p s.phase, hc.2⟩

/-- Canonical action counts agree with the actual recursively maintained statistics. -/
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

/-- Once the finite prefix event and the model's mean sandwich are established, the real
algorithm inherits the pair budget without an infinite-good-event assumption. -/
theorem pair_budget_of_finite_bounds (p : Params n K) (M : DecayModel n K) (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n)
    (meanSum : Fin n → Fin K → ℕ → ℝ)
    (hp : ∀ i k m, 1 ≤ m → m ≤ N p X J p.T i k →
      M.b k ≤ meanSum i k m / m ∧ meanSum i k m / m ≤ M.b k + psi (M.f k) m)
    (hc : ∀ i k m, 1 ≤ m → m ≤ N p X J p.T i k →
      |empiricalPrefix p X J i k m - meanSum i k m / m|
        ≤ rdelta p.L m)
    (i : Fin n) {k : Fin K} (hk : k ≠ M.star) :
    ((range p.T).filter (fun t => M.star ∈ ((run p X J t).nodes i).active ∧
      I p X J t i = k)).card ≤ M.mkAll p.L k :=
  (goodRunOnOfBounds p M X J meanSum hp hc).pair_budget i hk

end AnvBandit.Execution
