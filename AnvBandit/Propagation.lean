import AnvBandit.Contact
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-!
# The contact process as a probability space: tail bound and moments (Lemma B.4)

Assumption 2.4 models the request mechanism by an irreducible row-stochastic matrix
`P ∈ [0,1]^{n×n}`.  This file builds the probability space of the propagation process, formalises
the ideal propagation from a single initially-informed node `i0`, and proves both parts of
**Lemma B.4**:

* `measure_completion_gt_le` — the propagation tail bound
  `P{τ(i₀) > m(n−1)} ≤ (1 − ε_P)^m` with `ε_P = p_min^{n−1}`;
* `integral_rpow_completion_le` — the moment bound
  `E τ(i₀)^β ≤ e Γ(β+1) ((n−1)/ε_P)^β`.

The probabilistic input is a single node per step: irreducibility of `P` yields a *spanning
information tree* rooted at `i0` (`ReachData`), and the event that, in each step of a block of
`n−1` steps, the designated node requests its parent is a cylinder of probability exactly
`∏_v P (v) (parent v) ≥ ε_P`.  Because each such block-driver uses the *fixed* tree and the set of
informed nodes always contains `i0`, a successful block forces completion within `n−1` steps from
any history.  Blocks are independent, giving `(1−ε_P)^m`.
-/

noncomputable section
open scoped BigOperators ENNReal
open Finset MeasureTheory

namespace AnvBandit

/-! ## 1. Irreducibility of the contact matrix and the spanning information structure -/

/-- Information reachability: information can flow from `a` to `b` if there is a chain
`a = u₀, …, u_m = b` with `0 < P (u_{j+1}) (u_j)` (each node requests its predecessor with positive
probability). -/
def InfoReach {n : ℕ} (P : Fin n → Fin n → ℝ) (a b : Fin n) : Prop :=
  Relation.ReflTransGen (fun x y => 0 < P y x) a b

/-- Irreducibility of the contact matrix (Assumption 2.4): the information graph is strongly
connected, i.e. information reaches every node from every other node. -/
def IsIrreducible {n : ℕ} (P : Fin n → Fin n → ℝ) : Prop :=
  ∀ a b, InfoReach P a b

/-- Strong-connectivity witness for the propagation from `i0` (Lemma B.4's spanning structure):
every node carries a `rank` (its distance in the information graph) with `rank i0 = 0`, and a
`parent` of strictly smaller rank reachable by a positive-probability request. -/
structure ReachData {n : ℕ} (P : Fin n → Fin n → ℝ) (i0 : Fin n) where
  rank : Fin n → ℕ
  rank_i0 : rank i0 = 0
  rank_eq_zero : ∀ v, rank v = 0 → v = i0
  rank_le : ∀ v, rank v ≤ n - 1
  parent : Fin n → Fin n
  edge_pos : ∀ v, v ≠ i0 → 0 < P v (parent v)
  parent_lt : ∀ v, v ≠ i0 → rank (parent v) < rank v

/-- Breadth-first reachable set: nodes reachable from `i0` in at most `k` information steps. -/
def gen {n : ℕ} (P : Fin n → Fin n → ℝ) (i0 : Fin n) : ℕ → Finset (Fin n)
  | 0 => {i0}
  | k + 1 => gen P i0 k ∪ Finset.univ.filter (fun v => ∃ u ∈ gen P i0 k, 0 < P v u)

variable {n : ℕ} {P : Fin n → Fin n → ℝ} {i0 : Fin n}

@[simp] lemma gen_zero : gen P i0 0 = {i0} := rfl

lemma gen_succ (k : ℕ) :
    gen P i0 (k + 1) =
      gen P i0 k ∪ Finset.univ.filter (fun v => ∃ u ∈ gen P i0 k, 0 < P v u) := rfl

lemma mem_gen_succ {k : ℕ} {v : Fin n} :
    v ∈ gen P i0 (k + 1) ↔ v ∈ gen P i0 k ∨ ∃ u ∈ gen P i0 k, 0 < P v u := by
  simp only [gen_succ, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]

lemma gen_mono (k : ℕ) : gen P i0 k ⊆ gen P i0 (k + 1) := Finset.subset_union_left

lemma mem_gen_self (k : ℕ) : i0 ∈ gen P i0 k := by
  induction k with
  | zero => simp
  | succ k ih => exact gen_mono k ih

/-- Membership in `gen` implies information reachability. -/
lemma gen_reach : ∀ k, ∀ v, v ∈ gen P i0 k → InfoReach P i0 v := by
  intro k
  induction k with
  | zero =>
    intro v hv
    simp only [gen_zero, Finset.mem_singleton] at hv; subst hv; exact .refl
  | succ k ih =>
    intro v hv
    rw [mem_gen_succ] at hv
    rcases hv with hv | ⟨u, hu, hpu⟩
    · exact ih v hv
    · exact (ih u hu).tail hpu

/-- Information reachability implies membership in some `gen`. -/
lemma reach_gen {v : Fin n} (h : InfoReach P i0 v) : ∃ k, v ∈ gen P i0 k := by
  induction h with
  | refl => exact ⟨0, mem_gen_self 0⟩
  | tail _ hc ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, (mem_gen_succ).mpr (Or.inr ⟨_, hk, hc⟩)⟩

/-- **Growth of the reachable set.** Under irreducibility, as long as `gen` has not covered all
nodes, the next step adds at least one new node. -/
lemma gen_growth (hP : IsIrreducible P) (k : ℕ) (hk : gen P i0 k ≠ Finset.univ) :
    ∃ v, v ∉ gen P i0 k ∧ v ∈ gen P i0 (k + 1) := by
  by_contra hcon
  have hsub : gen P i0 (k + 1) ⊆ gen P i0 k := by
    intro v hv
    by_contra hvk
    exact hcon ⟨v, hvk, hv⟩
  have heq : gen P i0 (k + 1) = gen P i0 k :=
    Finset.Subset.antisymm hsub (gen_mono k)
  have hclosed : ∀ v : Fin n, (∃ u ∈ gen P i0 k, 0 < P v u) → v ∈ gen P i0 k := by
    intro v hv
    have : v ∈ gen P i0 (k + 1) := (mem_gen_succ).mpr (Or.inr hv)
    rwa [heq] at this
  have hgen : ∀ m, gen P i0 m ⊆ gen P i0 k := by
    intro m
    induction m with
    | zero => rw [gen_zero]; exact Finset.singleton_subset_iff.mpr (mem_gen_self k)
    | succ m ih =>
      intro v hv
      rw [mem_gen_succ] at hv
      rcases hv with hv | hv
      · exact ih hv
      · obtain ⟨u, hu, hpu⟩ := hv
        exact hclosed v ⟨u, ih hu, hpu⟩
  refine hk (Finset.eq_univ_of_forall fun v => ?_)
  obtain ⟨m, hm⟩ := reach_gen (hP i0 v)
  exact hgen m hm

/-- The reachable set has grown to size `k+1` (or already covered everything). -/
lemma gen_card_ge (hP : IsIrreducible P) (k : ℕ) :
    gen P i0 k = Finset.univ ∨ k + 1 ≤ (gen P i0 k).card := by
  induction k with
  | zero => right; rw [gen_zero]; simp
  | succ k ih =>
    rcases eq_or_ne (gen P i0 k) Finset.univ with h | h
    · exact Or.inl (Finset.eq_univ_of_forall fun v =>
        gen_mono k (by rw [h]; exact Finset.mem_univ v))
    · rcases ih with huniv | hcard
      · exact absurd huniv h
      · obtain ⟨v, hvnot, hv⟩ := gen_growth hP k h
        right
        have hlt : (gen P i0 k).card < (gen P i0 (k + 1)).card :=
          Finset.card_lt_card ⟨gen_mono k, fun hsub => hvnot (hsub hv)⟩
        omega

/-- **Saturation.** Under irreducibility the BFS reachable set is everything after `n−1` steps. -/
lemma gen_saturate (hP : IsIrreducible P) : gen P i0 (n - 1) = Finset.univ := by
  rcases gen_card_ge (P := P) (i0 := i0) hP (n - 1) with h | h
  · exact h
  · have hn : 1 ≤ n := Nat.lt_of_le_of_lt (Nat.zero_le _) i0.isLt
    have hcard_le : (gen P i0 (n - 1)).card ≤ n := by
      simpa using Finset.card_le_card (Finset.subset_univ (gen P i0 (n - 1)))
    have hcard_ge : n ≤ (gen P i0 (n - 1)).card := by omega
    exact Finset.eq_univ_of_card _ (by rw [le_antisymm hcard_le hcard_ge]; simp)

/-- **Existence of the spanning structure (Lemma B.4's input).** Every initial node of an
irreducible contact matrix carries `ReachData`: its BFS distance and a positive-probability
parent of smaller distance. -/
noncomputable def ReachData.ofIrreducible {n : ℕ} {P : Fin n → Fin n → ℝ}
    (hP : IsIrreducible P) (i0 : Fin n) : ReachData P i0 := by
  classical
  have hex : ∀ v : Fin n, ∃ k, v ∈ gen P i0 k :=
    fun v => ⟨n - 1, by rw [gen_saturate hP]; exact Finset.mem_univ v⟩
  let rk : Fin n → ℕ := fun v => Nat.find (hex v)
  have rk_spec : ∀ v, v ∈ gen P i0 (rk v) := fun v => Nat.find_spec (hex v)
  have rk_min : ∀ v k, v ∈ gen P i0 k → rk v ≤ k := fun v k hk => Nat.find_le hk
  have hrank_i0 : rk i0 = 0 := by
    have := rk_min i0 0 (mem_gen_self (P := P) (i0 := i0) 0); omega
  have hrank_zero : ∀ v, rk v = 0 → v = i0 := by
    intro v hv
    have hmem : v ∈ gen P i0 0 := hv ▸ rk_spec v
    simpa using hmem
  have hparent : ∀ v, v ≠ i0 → ∃ u, 0 < P v u ∧ rk u < rk v := by
    intro v hv
    have hv0 : rk v ≠ 0 := fun h => hv (hrank_zero v h)
    have hge : 1 ≤ rk v := Nat.one_le_iff_ne_zero.mpr hv0
    have hspec : v ∈ gen P i0 (rk v - 1 + 1) := by rw [Nat.sub_add_cancel hge]; exact rk_spec v
    rcases (mem_gen_succ.mp hspec) with h | ⟨u, hu, hpu⟩
    · exact absurd (rk_min v (rk v - 1) h) (by omega)
    · exact ⟨u, hpu, by have := rk_min u (rk v - 1) hu; omega⟩
  refine
    { rank := rk
      rank_i0 := hrank_i0
      rank_eq_zero := hrank_zero
      rank_le := fun v =>
        rk_min v (n - 1) (by rw [gen_saturate hP]; exact Finset.mem_univ v)
      parent := fun v => if hv : v = i0 then i0 else Classical.choose (hparent v hv)
      edge_pos := ?_
      parent_lt := ?_ }
  · intro v hv
    simp only [dif_neg hv]
    exact (Classical.choose_spec (hparent v hv)).1
  · intro v hv
    simp only [dif_neg hv]
    exact (Classical.choose_spec (hparent v hv)).2


/-! ## 2. The probability space of the propagation process -/

section Measures

/-- The law of a single node's request, given the row `r` of the contact matrix: the node requests
`j` with probability `r j`. -/
noncomputable def nodeDist {n : ℕ} (r : Fin n → ℝ) : Measure (Fin n) :=
  ∑ j, ENNReal.ofReal (r j) • Measure.dirac j

/-- Rows of a contact matrix are probability distributions. -/
instance rowInst {n : ℕ} (C : ContactMatrix n) (i : Fin n) :
    IsProbabilityMeasure (nodeDist (C.P i)) :=
  ⟨by
    rw [nodeDist, Measure.finsetSum_apply]
    simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => C.nonneg i j), C.row_sum i, ENNReal.ofReal_one]⟩

lemma nodeDist_apply {n : ℕ} (r : Fin n → ℝ) (s : Set (Fin n)) :
    nodeDist r s = ∑ j, ENNReal.ofReal (r j) * Measure.dirac j s := by
  rw [nodeDist, Measure.finsetSum_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [Measure.smul_apply, smul_eq_mul]

lemma nodeDist_singleton {n : ℕ} (r : Fin n → ℝ) (j : Fin n) :
    nodeDist r {j} = ENNReal.ofReal (r j) := by
  rw [nodeDist_apply, Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [Set.mem_singleton_iff, hk]
  · intro hj; exact absurd (Finset.mem_univ j) hj

/-- The law of one propagation step: nodes request independently, node `i` according to `P i ·`. -/
noncomputable def stepDist {n : ℕ} (C : ContactMatrix n) : Measure (Fin n → Fin n) :=
  Measure.pi (fun i => nodeDist (C.P i))

instance stepDist.instIsProbabilityMeasure {n : ℕ} (C : ContactMatrix n) :
    IsProbabilityMeasure (stepDist C) := by
  unfold stepDist; infer_instance

lemma stepDist_eval {n : ℕ} (C : ContactMatrix n) (v p : Fin n) :
    stepDist C {R : Fin n → Fin n | R v = p} = ENNReal.ofReal (C.P v p) := by
  have hmeas : Measurable (Function.eval v : (Fin n → Fin n) → Fin n) := measurable_pi_apply v
  have h1 : ∀ j : Fin n, nodeDist (C.P j) (Set.univ : Set (Fin n)) = 1 :=
    fun j => measure_univ
  rw [show {R : Fin n → Fin n | R v = p} =
        (Function.eval v : (Fin n → Fin n) → Fin n) ⁻¹' ({p} : Set (Fin n)) from by
      ext R; simp [Set.mem_singleton_iff]]
  unfold stepDist
  rw [← Measure.map_apply hmeas (measurableSet_singleton p),
    Measure.pi_map_eval (μ := fun i => nodeDist (C.P i)) v]
  rw [show (∏ j ∈ Finset.univ.erase v, nodeDist (C.P j) (Set.univ : Set (Fin n))) = 1 from
        Finset.prod_eq_one (fun j _ => h1 j)]
  rw [one_smul]
  exact nodeDist_singleton (C.P v) p

/-- The law of one propagation block of `d` steps. -/
noncomputable def blockDist {n : ℕ} (C : ContactMatrix n) (d : ℕ) :
    Measure (Fin d → Fin n → Fin n) :=
  Measure.pi (fun _ => stepDist C)

instance blockDist.instIsProbabilityMeasure {n : ℕ} (C : ContactMatrix n) (d : ℕ) :
    IsProbabilityMeasure (blockDist C d) := by
  unfold blockDist; infer_instance

/-- The full law of the propagation process: i.i.d. blocks indexed by `ℕ`. -/
noncomputable def procMeasure {n : ℕ} (C : ContactMatrix n) (d : ℕ) :
    Measure (ℕ → Fin d → Fin n → Fin n) :=
  Measure.infinitePi (fun _ => blockDist C d)

instance procMeasure.instIsProbabilityMeasure {n : ℕ} (C : ContactMatrix n) (d : ℕ) :
    IsProbabilityMeasure (procMeasure C d) := by
  unfold procMeasure; infer_instance

/-- The per-block success probability `ε_P = p_min^{n−1}`. -/
def epsP {n : ℕ} (C : ContactMatrix n) : ℝ := C.pmin ^ (n - 1)

lemma pmin_le_one {n : ℕ} (C : ContactMatrix n) (i0 : Fin n) : C.pmin ≤ 1 := by
  have hex : ∃ j : Fin n, 0 < C.P i0 j := by
    by_contra h
    simp only [not_exists, not_lt] at h
    have : ∑ j, C.P i0 j ≤ 0 := Finset.sum_nonpos (fun j _ => h j)
    rw [C.row_sum i0] at this; norm_num at this
  obtain ⟨j, hj⟩ := hex
  calc C.pmin ≤ C.P i0 j := C.le_pmin i0 j hj
    _ ≤ ∑ k, C.P i0 k := Finset.single_le_sum (fun k _ => C.nonneg i0 k) (Finset.mem_univ j)
    _ = 1 := C.row_sum i0

lemma epsP_pos {n : ℕ} (C : ContactMatrix n) : 0 < epsP C := pow_pos C.pmin_pos _

lemma epsP_le_one {n : ℕ} (C : ContactMatrix n) (i0 : Fin n) : epsP C ≤ 1 :=
  pow_le_one₀ C.pmin_pos.le (pmin_le_one C i0)

lemma epsP_nonneg {n : ℕ} (C : ContactMatrix n) : 0 ≤ epsP C := (epsP_pos C).le

end Measures


/-! ## 3. The block process and its deterministic driver -/

section Block

/-- One propagation block, applied step by step: the informed set after `k` of the `d` steps. -/
def blockState {n d : ℕ} (w : Fin d → Fin n → Fin n) (A : Finset (Fin n)) : ℕ → Finset (Fin n)
  | 0 => A
  | k + 1 => if h : k < d then infStep (w ⟨k, h⟩) (blockState w A k) else blockState w A k

@[simp] lemma blockState_zero {n d : ℕ} (w : Fin d → Fin n → Fin n) (A : Finset (Fin n)) :
    blockState w A 0 = A := rfl

lemma blockState_succ {n d : ℕ} (w : Fin d → Fin n → Fin n) (A : Finset (Fin n)) {k : ℕ}
    (h : k < d) : blockState w A (k + 1) = infStep (w ⟨k, h⟩) (blockState w A k) := by
  simp only [blockState, dif_pos h]

lemma blockState_succ_of_not_lt {n d : ℕ} (w : Fin d → Fin n → Fin n) (A : Finset (Fin n)) {k : ℕ}
    (h : ¬ k < d) : blockState w A (k + 1) = blockState w A k := by
  simp only [blockState, dif_neg h]

/-- The informed set after `m` whole blocks of length `d`. -/
def StateProc {n d : ℕ} (ω : ℕ → Fin d → Fin n → Fin n) (A : Finset (Fin n)) : ℕ → Finset (Fin n)
  | 0 => A
  | m + 1 => blockState (ω m) (StateProc ω A m) d

@[simp] lemma StateProc_zero {n d : ℕ} (ω : ℕ → Fin d → Fin n → Fin n) (A : Finset (Fin n)) :
    StateProc ω A 0 = A := rfl

lemma subset_blockState {n d : ℕ} (w : Fin d → Fin n → Fin n) (A : Finset (Fin n)) (k : ℕ) :
    A ⊆ blockState w A k := by
  induction k with
  | zero => exact Finset.Subset.refl A
  | succ k ih =>
    by_cases h : k < d
    · rw [blockState_succ w A h]
      exact ih.trans (subset_infStep (w ⟨k, h⟩) _)
    · rw [blockState_succ_of_not_lt w A h]
      exact ih

lemma subset_StateProc {n d : ℕ} (ω : ℕ → Fin d → Fin n → Fin n) (A : Finset (Fin n)) (m : ℕ) :
    A ⊆ StateProc ω A m := by
  induction m with
  | zero => exact Finset.Subset.refl A
  | succ m ih => exact ih.trans (subset_blockState (ω m) _ d)

/-- **Deterministic driver of the propagation.** If in a block each node of rank `t+1` requests its
parent at step `t`, then the block informs the whole population, starting from any set containing
`i0`. This driver is *state-independent*: it works from any history, because the informed set always
contains `i0`. -/
lemma blockState_univ {n d : ℕ} (w : Fin d → Fin n → Fin n) (A : Finset (Fin n))
    (i0 : Fin n) (rank : Fin n → ℕ) (parent : Fin n → Fin n)
    (hA : i0 ∈ A) (hi0 : rank i0 = 0) (hrank_le : ∀ v, rank v ≤ d)
    (hzero : ∀ v, rank v = 0 → v = i0)
    (hpar : ∀ v, v ≠ i0 → rank (parent v) < rank v)
    (hedge : ∀ t : Fin d, ∀ v, rank v = t.val + 1 → w t v = parent v) :
    blockState w A d = Finset.univ := by
  have key : ∀ k, k ≤ d → Finset.univ.filter (fun v => rank v ≤ k) ⊆ blockState w A k := by
    intro k
    induction k with
    | zero =>
      intro _ v hv
      rw [blockState_zero]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      have : v = i0 := hzero v (by omega)
      rw [this]; exact hA
    | succ k ih =>
      intro hk v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      have hkd : k < d := by omega
      rw [blockState_succ w A hkd, infStep]
      rcases lt_or_eq_of_le hv with hlt | heq
      · refine Finset.mem_union_left _ (ih (by omega) ?_)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      · have hvne : v ≠ i0 := by rintro rfl; rw [hi0] at heq; omega
        have hp_rank : rank (parent v) ≤ k := by have := hpar v hvne; omega
        refine Finset.mem_union_right _ ?_
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ v, ?_⟩
        have : w ⟨k, hkd⟩ v = parent v := hedge ⟨k, hkd⟩ v (by simpa using heq)
        rw [this]
        exact ih (by omega) (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hp_rank)
  refine Finset.eq_univ_of_forall fun v => key d le_rfl ?_
  simp [hrank_le v]

/-- A `ReachData` version of the deterministic driver: a successful block informs everything. -/
lemma blockState_univ_of_reach {n : ℕ} {P : Fin n → Fin n → ℝ} {i0 : Fin n}
    (R : ReachData P i0) (w : Fin (n - 1) → Fin n → Fin n)
    (A : Finset (Fin n)) (hA : i0 ∈ A)
    (hedge : ∀ t : Fin (n - 1), ∀ v, R.rank v = t.val + 1 → w t v = R.parent v) :
    blockState w A (n - 1) = Finset.univ :=
  blockState_univ w A i0 R.rank R.parent hA R.rank_i0 (fun v => R.rank_le v)
    R.rank_eq_zero R.parent_lt hedge

end Block


/-! ## 4. The successful-block cylinder and its probability -/

section Event

/-- The per-step constraint: every node of rank `t+1` requests its parent. -/
def stepConstraint {n : ℕ} (rank : Fin n → ℕ) (parent : Fin n → Fin n) (t : ℕ) :
    Set (Fin n → Fin n) :=
  Set.univ.pi (fun v : Fin n => if rank v = t + 1 then ({parent v} : Set (Fin n)) else Set.univ)

/-- The per-block success cylinder: at step `t` of the block every node of rank `t+1` requests its
parent. -/
def blockEvent {n d : ℕ} (rank : Fin n → ℕ) (parent : Fin n → Fin n) :
    Set (Fin d → Fin n → Fin n) :=
  Set.univ.pi (fun t : Fin d => stepConstraint rank parent t.val)

lemma mem_blockEvent {n d : ℕ} {rank : Fin n → ℕ} {parent : Fin n → Fin n}
    {w : Fin d → Fin n → Fin n} :
    w ∈ blockEvent rank parent ↔
      ∀ t : Fin d, ∀ v : Fin n, rank v = t.val + 1 → w t v = parent v := by
  simp only [blockEvent, stepConstraint, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_ite_univ_right, Set.mem_singleton_iff]

lemma stepDist_stepConstraint {n : ℕ} (C : ContactMatrix n) (rank : Fin n → ℕ)
    (parent : Fin n → Fin n) (t : ℕ) :
    stepDist C (stepConstraint rank parent t) =
      ∏ v : Fin n, (if rank v = t + 1 then ENNReal.ofReal (C.P v (parent v)) else 1) := by
  rw [stepConstraint]
  unfold stepDist
  rw [Measure.pi_pi (μ := fun i => nodeDist (C.P i))]
  refine Finset.prod_congr rfl fun v _ => ?_
  by_cases h : rank v = t + 1
  · rw [if_pos h, if_pos h]; exact nodeDist_singleton (C.P v) (parent v)
  · rw [if_neg h, if_neg h]; exact measure_univ

lemma blockDist_blockEvent {n : ℕ} (C : ContactMatrix n) {i0 : Fin n} (R : ReachData C.P i0) :
    blockDist C (n - 1) (blockEvent (d := n - 1) R.rank R.parent) =
      ∏ v : Fin n, (if v = i0 then 1 else ENNReal.ofReal (C.P v (R.parent v))) := by
  classical
  rw [blockEvent]
  unfold blockDist
  rw [Measure.pi_pi (μ := fun _ : Fin (n - 1) => stepDist C)]
  simp only [stepDist_stepConstraint]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun v _ => ?_
  by_cases hv : v = i0
  · subst hv
    rw [if_pos rfl]
    refine Finset.prod_eq_one fun t _ => ?_
    rw [R.rank_i0, if_neg]; omega
  · rw [if_neg hv]
    have hv0 : R.rank v ≠ 0 := fun h => hv (R.rank_eq_zero v h)
    have hge : 1 ≤ R.rank v := Nat.one_le_iff_ne_zero.mpr hv0
    have hlt : R.rank v - 1 < n - 1 := by have := R.rank_le v; omega
    rw [Fintype.prod_eq_single (a := (⟨R.rank v - 1, hlt⟩ : Fin (n - 1)))
      (f := fun t : Fin (n - 1) =>
        if R.rank v = (t : ℕ) + 1 then ENNReal.ofReal (C.P v (R.parent v)) else 1)
      (fun t ht => if_neg fun hc => ht (Fin.ext (by simp only []; omega)))]
    rw [if_pos (by simp only []; omega)]

/-- The successful-block cylinder has probability at least `ε_P = p_min^{n−1}`. -/
lemma blockDist_blockEvent_ge {n : ℕ} (C : ContactMatrix n) {i0 : Fin n} (R : ReachData C.P i0) :
    ENNReal.ofReal (epsP C) ≤ blockDist C (n - 1) (blockEvent (d := n - 1) R.rank R.parent) := by
  classical
  rw [blockDist_blockEvent C R]
  have hcard : (Finset.univ.erase i0 : Finset (Fin n)).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i0), Finset.card_univ, Fintype.card_fin]
  calc ENNReal.ofReal (epsP C)
      = ENNReal.ofReal C.pmin ^ (n - 1) := by
        rw [epsP, ENNReal.ofReal_pow C.pmin_pos.le]
    _ = ∏ _v ∈ (Finset.univ.erase i0 : Finset (Fin n)), ENNReal.ofReal C.pmin := by
        rw [Finset.prod_const, hcard]
    _ ≤ ∏ _v ∈ (Finset.univ.erase i0 : Finset (Fin n)), ENNReal.ofReal C.pmin := le_rfl
    _ ≤ ∏ v ∈ (Finset.univ.erase i0 : Finset (Fin n)),
          ENNReal.ofReal (C.P v (R.parent v)) := by
        refine Finset.prod_le_prod' fun v hv => ?_
        rw [Finset.mem_erase] at hv
        exact ENNReal.ofReal_le_ofReal (C.le_pmin v (R.parent v) (R.edge_pos v hv.1))
    _ = ∏ v : Fin n, (if v = i0 then 1 else ENNReal.ofReal (C.P v (R.parent v))) := by
        rw [← Finset.mul_prod_erase Finset.univ
              (fun v : Fin n => if v = i0 then 1 else ENNReal.ofReal (C.P v (R.parent v)))
              (Finset.mem_univ i0), if_pos rfl, one_mul]
        refine Finset.prod_congr rfl fun v hv => ?_
        rw [Finset.mem_erase] at hv
        rw [if_neg hv.1]

end Event


/-! ## 5. Block/step correspondence, the completion time, and the tail bound -/

section Tail

/-- A block read as a step-sequence: step `s < d` is the `s`-th request function of the block. -/
def blockSeq {n d : ℕ} (hd : 0 < d) (w : Fin d → Fin n → Fin n) : ℕ → Fin n → Fin n :=
  fun s => if h : s < d then w ⟨s, h⟩ else w ⟨0, hd⟩

lemma Inform_blockSeq {n d : ℕ} (hd : 0 < d) (w : Fin d → Fin n → Fin n) (B : Finset (Fin n)) :
    ∀ k, k ≤ d → Inform (blockSeq hd w) B k = blockState w B k
  | 0, _ => by rw [Inform_zero, blockState_zero]
  | k + 1, hk => by
      have hk' : k < d := by omega
      have hfun : blockSeq hd w k = w ⟨k, hk'⟩ := by simp only [blockSeq, dif_pos hk']
      rw [Inform_succ, blockState_succ w B hk', Inform_blockSeq hd w B k (by omega), hfun]

lemma Inform_shift {n : ℕ} (R : ℕ → Fin n → Fin n) (A : Finset (Fin n)) (a : ℕ) :
    ∀ b, Inform R A (a + b) = Inform (fun s => R (a + s)) (Inform R A a) b
  | 0 => by rw [Nat.add_zero, Inform_zero]
  | b + 1 => by
      have h1 : a + (b + 1) = (a + b) + 1 := by omega
      rw [h1, Inform_succ, Inform_succ, Inform_shift R A a b]

lemma Inform_congr {n : ℕ} (R R' : ℕ → Fin n → Fin n) (A : Finset (Fin n)) {k : ℕ}
    (h : ∀ s, s < k → R s = R' s) : Inform R A k = Inform R' A k := by
  induction k with
  | zero => rw [Inform_zero, Inform_zero]
  | succ k ih => rw [Inform_succ, Inform_succ, ih (fun s hs => h s (by omega)), h k (by omega)]

/-- A block sequence read as a step sequence. -/
def unblock {n d : ℕ} (hd : 0 < d) (ω : ℕ → Fin d → Fin n → Fin n) : ℕ → Fin n → Fin n :=
  fun t => ω (t / d) ⟨t % d, Nat.mod_lt t hd⟩

lemma Inform_unblock {n d : ℕ} (hd : 0 < d) (ω : ℕ → Fin d → Fin n → Fin n) (A : Finset (Fin n)) :
    ∀ m, Inform (unblock hd ω) A (m * d) = StateProc ω A m
  | 0 => by rw [Nat.zero_mul, Inform_zero, StateProc_zero]
  | m + 1 => by
      have h1 : (m + 1) * d = m * d + d := by ring
      have hagree : ∀ s, s < d → (fun s => unblock hd ω (m * d + s)) s = blockSeq hd (ω m) s := by
        intro s hs
        simp only [blockSeq, dif_pos hs, unblock]
        have hdiv : (m * d + s) / d = m := by
          rw [show m * d + s = s + d * m by ring, Nat.add_mul_div_left _ _ hd,
            Nat.div_eq_of_lt hs, zero_add]
        have hmod : (m * d + s) % d = s := by
          rw [show m * d + s = s + d * m by ring, Nat.add_mul_mod_self_left,
            Nat.mod_eq_of_lt hs]
        have hfin : (⟨(m * d + s) % d, Nat.mod_lt (m * d + s) hd⟩ : Fin d) = ⟨s, hs⟩ :=
          Fin.ext hmod
        rw [hdiv, hfin]
      rw [h1, Inform_shift, Inform_unblock hd ω A m,
        Inform_congr (fun s => unblock hd ω (m * d + s)) (blockSeq hd (ω m)) _ hagree,
        Inform_blockSeq hd (ω m) (StateProc ω A m) d le_rfl]
      rfl

/-- The completion time of the ideal propagation, in *steps*, starting from `{i0}`: the first step
`t` at which every node is informed.  On the (null) set of trajectories for which the propagation
never completes, `sInf ∅ = 0`; this only differs from the paper's `τ = ∞` on a `procMeasure`-null
set, so all probability and expectation statements below are unaffected (and the tail bound itself
forces that set to have measure `0`). -/
def tau {n : ℕ} (hd : 0 < n - 1) (ω : ℕ → Fin (n - 1) → Fin n → Fin n) (i0 : Fin n) : ℕ :=
  sInf {t | Inform (unblock hd ω) {i0} t = Finset.univ}

lemma StateProc_mono {n d : ℕ} (ω : ℕ → Fin d → Fin n → Fin n) (A : Finset (Fin n)) (m : ℕ) :
    ∀ {l : ℕ}, m ≤ l → StateProc ω A m ⊆ StateProc ω A l := by
  intro l
  induction l with
  | zero =>
      intro h
      have hm : m = 0 := by omega
      rw [hm]
  | succ l ih =>
      intro h
      rcases Nat.lt_or_ge m (l + 1) with hlt | hge
      · exact (ih (by omega)).trans (subset_blockState (ω l) _ d)
      · have hm : m = l + 1 := by omega
        rw [hm]

/-- A block that satisfies the driver informs the whole population, whatever the current set. -/
lemma blockSuccess_completes {n : ℕ} (C : ContactMatrix n) {i0 : Fin n} (R : ReachData C.P i0)
    (ω : ℕ → Fin (n - 1) → Fin n → Fin n) :
    ∀ b, (∀ t : Fin (n - 1), ∀ v : Fin n, R.rank v = t.val + 1 → ω b t v = R.parent v) →
      StateProc ω {i0} (b + 1) = Finset.univ := by
  intro b hb
  have hA : i0 ∈ StateProc ω {i0} b := subset_StateProc ω {i0} b (Finset.mem_singleton_self i0)
  exact blockState_univ_of_reach R (ω b) (StateProc ω {i0} b) hA hb

end Tail


/-! ## 6. The propagation tail bound and moments (Lemma B.4) -/

section TailBound

lemma measurableSet_blockEvent {n d : ℕ} (rank : Fin n → ℕ) (parent : Fin n → Fin n) :
    MeasurableSet (blockEvent (n := n) (d := d) rank parent) := by
  rw [blockEvent]
  refine MeasurableSet.pi Set.countable_univ (fun t _ => ?_)
  rw [stepConstraint]
  refine MeasurableSet.pi Set.countable_univ (fun v _ => ?_)
  by_cases h : rank v = t.val + 1
  · rw [if_pos h]; exact measurableSet_singleton _
  · rw [if_neg h]; exact MeasurableSet.univ

/-- **Independence of the blocks.** The event that the first `m` blocks all fail has probability
`(blockDist Bᶜ)^m`. -/
lemma procMeasure_blockEvent_compl {n : ℕ} (C : ContactMatrix n) {i0 : Fin n}
    (R : ReachData C.P i0) (m : ℕ) :
    procMeasure C (n - 1)
        (Set.pi (Finset.range m) (fun _ : ℕ => (blockEvent (d := n - 1) R.rank R.parent)ᶜ)) =
      (blockDist C (n - 1) (blockEvent (d := n - 1) R.rank R.parent)ᶜ) ^ m := by
  rw [procMeasure,
    Measure.infinitePi_pi (μ := fun _ : ℕ => blockDist C (n - 1))
      (t := fun _ : ℕ => (blockEvent (d := n - 1) R.rank R.parent)ᶜ)
      (mt := fun _ _ => (measurableSet_blockEvent (d := n - 1) R.rank R.parent).compl),
    Finset.prod_const, Finset.card_range]

/-- One failed block has probability at most `1 − ε_P`. -/
lemma blockDist_compl_le {n : ℕ} (C : ContactMatrix n) {i0 : Fin n} (R : ReachData C.P i0) :
    blockDist C (n - 1) (blockEvent (d := n - 1) R.rank R.parent)ᶜ ≤
      ENNReal.ofReal (1 - epsP C) := by
  have hB := measurableSet_blockEvent (d := n - 1) R.rank R.parent
  calc blockDist C (n - 1) (blockEvent (d := n - 1) R.rank R.parent)ᶜ
      = 1 - blockDist C (n - 1) (blockEvent (d := n - 1) R.rank R.parent) := by
        rw [MeasureTheory.measure_compl hB (MeasureTheory.measure_ne_top _ _), measure_univ]
    _ ≤ 1 - ENNReal.ofReal (epsP C) := tsub_le_tsub_left (blockDist_blockEvent_ge C R) 1
    _ = ENNReal.ofReal (1 - epsP C) := by
        rw [ENNReal.ofReal_sub 1 (epsP_nonneg C), ENNReal.ofReal_one]

/-- **Lemma B.4, tail bound (block form).** If the state after `m` blocks of length `n−1` is not the
whole population, then all `m` blocks failed; by independence this has probability at most
`(1−ε_P)^m`. -/
lemma measure_complete_gt_le {n : ℕ} (C : ContactMatrix n) {i0 : Fin n} (R : ReachData C.P i0)
    (m : ℕ) :
    procMeasure C (n - 1) {ω | StateProc ω {i0} m ≠ Finset.univ} ≤
      ENNReal.ofReal ((1 - epsP C) ^ m) := by
  have hsub : {ω | StateProc ω {i0} m ≠ Finset.univ} ⊆
      Set.pi (Finset.range m) (fun _ : ℕ => (blockEvent (d := n - 1) R.rank R.parent)ᶜ) := by
    intro ω hω
    rw [Set.mem_setOf_eq] at hω
    rw [Set.mem_pi]
    intro b hb
    have hbm : b < m := by simpa using hb
    rw [Set.mem_compl_iff, mem_blockEvent]
    intro hbe
    have hcomp := blockSuccess_completes C R ω b hbe
    have hmono := StateProc_mono ω {i0} (b + 1) (l := m) (by omega)
    rw [hcomp] at hmono
    exact hω (Finset.Subset.antisymm (Finset.subset_univ _) hmono)
  refine (measure_mono hsub).trans ?_
  rw [procMeasure_blockEvent_compl C R m]
  calc (blockDist C (n - 1) (blockEvent (d := n - 1) R.rank R.parent)ᶜ) ^ m
      ≤ (ENNReal.ofReal (1 - epsP C)) ^ m := pow_le_pow_left' (blockDist_compl_le C R) m
    _ = ENNReal.ofReal ((1 - epsP C) ^ m) := by
        rw [ENNReal.ofReal_pow (by have := epsP_le_one C i0; linarith)]

/-- **Lemma B.4, tail bound.** `P{τ(i₀) > m(n−1)} ≤ (1−ε_P)^m` with `ε_P = p_min^{n−1}`. -/
theorem measure_tau_gt_le {n : ℕ} (hn : 2 ≤ n) (C : ContactMatrix n) {i0 : Fin n}
    (R : ReachData C.P i0) (m : ℕ) :
    procMeasure C (n - 1) {ω | m * (n - 1) < tau (by omega : 0 < n - 1) ω i0} ≤
      ENNReal.ofReal ((1 - epsP C) ^ m) := by
  have hd : 0 < n - 1 := by omega
  refine (measure_mono ?_).trans (measure_complete_gt_le C R m)
  intro ω hω
  rw [Set.mem_setOf_eq] at hω ⊢
  intro hcomp
  have hS : m * (n - 1) ∈ {t | Inform (unblock hd ω) {i0} t = Finset.univ} := by
    simp only [Set.mem_setOf_eq]
    rw [Inform_unblock hd ω {i0} m, hcomp]
  have hle := Nat.sInf_le hS
  rw [tau] at hω
  exact absurd hω (not_lt.mpr hle)

end TailBound


/-! ## 7. Measurability of the completion time and the real-parameter tail bound -/

section MomentInput

lemma Inform_mono_le {n : ℕ} (R : ℕ → Fin n → Fin n) (A : Finset (Fin n)) (t : ℕ) :
    ∀ {t' : ℕ}, t ≤ t' → Inform R A t ⊆ Inform R A t' := by
  intro t'
  induction t' with
  | zero =>
      intro h
      have ht : t = 0 := by omega
      rw [ht]
  | succ t' ih =>
      intro h
      rcases Nat.lt_or_ge t (t' + 1) with hlt | hge
      · exact (ih (by omega)).trans (subset_infStep (R t') _)
      · have ht : t = t' + 1 := by omega
        rw [ht]

lemma measurable_inform_eq {n d : ℕ} (hd : 0 < d) (A S : Finset (Fin n)) (t : ℕ) :
    MeasurableSet {ω : ℕ → Fin d → Fin n → Fin n | Inform (unblock hd ω) A t = S} := by
  induction t generalizing S with
  | zero =>
      by_cases h : A = S
      · rw [show {ω : ℕ → Fin d → Fin n → Fin n | Inform (unblock hd ω) A 0 = S} = Set.univ from by
          ext ω; simp [Inform_zero, h]]
        exact MeasurableSet.univ
      · rw [show {ω : ℕ → Fin d → Fin n → Fin n | Inform (unblock hd ω) A 0 = S} = ∅ from by
          ext ω; simp [Inform_zero, h]]
        exact MeasurableSet.empty
  | succ t ih =>
      have hset : {ω : ℕ → Fin d → Fin n → Fin n | Inform (unblock hd ω) A (t + 1) = S} =
          ⋃ S' : Finset (Fin n),
            ({ω | Inform (unblock hd ω) A t = S'} ∩
             {ω | infStep (ω (t / d) ⟨t % d, Nat.mod_lt t hd⟩) S' = S}) := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Inform_succ, unblock]
        constructor
        · intro h; exact ⟨_, rfl, h⟩
        · rintro ⟨S', hS', hin⟩; rw [hS']; exact hin
      rw [hset]
      refine MeasurableSet.iUnion fun S' => (ih S').inter ?_
      have heq : {ω : ℕ → Fin d → Fin n → Fin n |
            infStep (ω (t / d) ⟨t % d, Nat.mod_lt t hd⟩) S' = S} =
          (fun ω : ℕ → Fin d → Fin n → Fin n => ω (t / d)) ⁻¹'
            {R : Fin d → Fin n → Fin n | infStep (R ⟨t % d, Nat.mod_lt t hd⟩) S' = S} := rfl
      rw [heq]
      exact MeasurableSet.preimage (Set.Countable.measurableSet (Set.toFinite _).countable)
        (measurable_pi_apply (t / d))

lemma measurable_completion_le {n : ℕ} (hd : 0 < n - 1) (i0 : Fin n) (k : ℕ) :
    MeasurableSet {ω : ℕ → Fin (n - 1) → Fin n → Fin n |
      sInf {t | Inform (unblock hd ω) {i0} t = Finset.univ} ≤ k} := by
  have hM : ∀ j, MeasurableSet {ω : ℕ → Fin (n - 1) → Fin n → Fin n |
      Inform (unblock hd ω) {i0} j = Finset.univ} := fun j => measurable_inform_eq hd {i0} _ j
  have hset : {ω : ℕ → Fin (n - 1) → Fin n → Fin n |
        sInf {t | Inform (unblock hd ω) {i0} t = Finset.univ} ≤ k} =
      (⋃ j : Fin (k + 1), {ω | Inform (unblock hd ω) {i0} j.val = Finset.univ}) ∪
      (⋃ j : ℕ, {ω | Inform (unblock hd ω) {i0} j = Finset.univ})ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion, Set.mem_compl_iff]
    constructor
    · intro h
      rcases em (∃ j, Inform (unblock hd ω) {i0} j = Finset.univ) with ⟨j, hj⟩ | hn'
      · left
        have hmem : sInf {t | Inform (unblock hd ω) {i0} t = Finset.univ} ∈
            {t | Inform (unblock hd ω) {i0} t = Finset.univ} := Nat.sInf_mem ⟨j, hj⟩
        exact ⟨⟨_, by omega⟩, hmem⟩
      · exact Or.inr hn'
    · rintro (⟨j, hj⟩ | hn')
      · exact le_trans (Nat.sInf_le hj) (by omega)
      · have hempty : {t | Inform (unblock hd ω) {i0} t = Finset.univ} = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro j hj
          exact hn' ⟨j, hj⟩
        rw [hempty, Nat.sInf_empty]
        exact Nat.zero_le k
  rw [hset]
  exact (MeasurableSet.iUnion fun j : Fin (k + 1) => hM j.val).union
    (MeasurableSet.iUnion hM).compl

lemma measurable_tau_le {n : ℕ} (hd : 0 < n - 1) (i0 : Fin n) (k : ℕ) :
    MeasurableSet {ω : ℕ → Fin (n - 1) → Fin n → Fin n | tau hd ω i0 ≤ k} := by
  have h := measurable_completion_le hd i0 k
  convert h using 2 with ω
  simp only [tau]

lemma measurable_tau_real {n : ℕ} (hd : 0 < n - 1) (i0 : Fin n) :
    Measurable fun ω : ℕ → Fin (n - 1) → Fin n → Fin n => (tau hd ω i0 : ℝ) := by
  refine measurable_of_Iic fun x => ?_
  rcases lt_or_ge x 0 with hx | hx
  · have hz : {ω : ℕ → Fin (n - 1) → Fin n → Fin n | (tau hd ω i0 : ℝ) ≤ x} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro ω
      simp only [Set.mem_setOf_eq, not_le]
      exact lt_of_lt_of_le hx (Nat.cast_nonneg _)
    rw [show (fun ω : ℕ → Fin (n - 1) → Fin n → Fin n => (tau hd ω i0 : ℝ)) ⁻¹' Set.Iic x
        = {ω | (tau hd ω i0 : ℝ) ≤ x} from rfl, hz]
    exact MeasurableSet.empty
  · have hset : {ω : ℕ → Fin (n - 1) → Fin n → Fin n | (tau hd ω i0 : ℝ) ≤ x} =
        {ω | tau hd ω i0 ≤ ⌊x⌋₊} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      rw [Nat.le_floor_iff hx]
    rw [show (fun ω : ℕ → Fin (n - 1) → Fin n → Fin n => (tau hd ω i0 : ℝ)) ⁻¹' Set.Iic x
        = {ω | (tau hd ω i0 : ℝ) ≤ x} from rfl, hset]
    exact measurable_tau_le hd i0 ⌊x⌋₊

/-- `(1−ε)^⌊x/d⌋ ≤ e · e^{−ε·(x/d)}` for `0 < ε ≤ 1`, `d > 0`, `x ≥ 0`. -/
lemma one_sub_pow_floor_le {ε x d : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hd : 0 < d) (hx : 0 ≤ x) :
    (1 - ε) ^ ⌊x / d⌋₊ ≤ Real.exp 1 * Real.exp (-(ε * (x / d))) := by
  have hbase : 0 ≤ 1 - ε := by linarith
  have h1 : (1 - ε) ^ ⌊x / d⌋₊ ≤ Real.exp (-ε) ^ ⌊x / d⌋₊ :=
    pow_le_pow_left₀ hbase (Real.one_sub_le_exp_neg ε) _
  have h2 : Real.exp (-ε) ^ ⌊x / d⌋₊ = Real.exp (-(ε * (⌊x / d⌋₊ : ℝ))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hlt : x / d - (⌊x / d⌋₊ : ℝ) < 1 := by
    have := Nat.lt_floor_add_one (x / d); linarith
  have h3 : -(ε * (⌊x / d⌋₊ : ℝ)) ≤ -(ε * (x / d)) + 1 := by
    have hmul : ε * (x / d - (⌊x / d⌋₊ : ℝ)) < ε := by
      simpa using mul_lt_mul_of_pos_left hlt hε0
    nlinarith [hmul, hε1]
  calc (1 - ε) ^ ⌊x / d⌋₊ ≤ Real.exp (-ε) ^ ⌊x / d⌋₊ := h1
    _ = Real.exp (-(ε * (⌊x / d⌋₊ : ℝ))) := h2
    _ ≤ Real.exp (-(ε * (x / d)) + 1) := Real.exp_le_exp.mpr h3
    _ = Real.exp 1 * Real.exp (-(ε * (x / d))) := by rw [Real.exp_add, mul_comm]

/-- **Lemma B.4, tail bound for real parameters.** `P{τ(i₀) > x} ≤ e·e^{−ε_P x/(n−1)}`. -/
lemma measure_tau_gt_real_le {n : ℕ} (hn : 2 ≤ n) (C : ContactMatrix n) {i0 : Fin n}
    (R : ReachData C.P i0) {x : ℝ} (hx : 0 ≤ x) :
    procMeasure C (n - 1) {ω | x < (tau (by omega : 0 < n - 1) ω i0 : ℝ)} ≤
      ENNReal.ofReal (Real.exp 1 * Real.exp (-(epsP C * (x / ((n : ℝ) - 1))))) := by
  have hd : 0 < n - 1 := by omega
  have hnd : (0 : ℝ) < (n : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hdm : ((n : ℝ) - 1) = ((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; push_cast; ring
  have hsub : {ω | x < (tau hd ω i0 : ℝ)} ⊆
      {ω | ⌊x / ((n : ℝ) - 1)⌋₊ * (n - 1) < tau hd ω i0} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have hm_le : (⌊x / ((n : ℝ) - 1)⌋₊ : ℝ) * ((n : ℝ) - 1) ≤ x := by
      have h1 : (⌊x / ((n : ℝ) - 1)⌋₊ : ℝ) ≤ x / ((n : ℝ) - 1) :=
        Nat.floor_le (div_nonneg hx hnd.le)
      calc (⌊x / ((n : ℝ) - 1)⌋₊ : ℝ) * ((n : ℝ) - 1)
            ≤ (x / ((n : ℝ) - 1)) * ((n : ℝ) - 1) := mul_le_mul_of_nonneg_right h1 hnd.le
        _ = x := by field_simp
    have : ((⌊x / ((n : ℝ) - 1)⌋₊ * (n - 1) : ℕ) : ℝ) < (tau hd ω i0 : ℝ) := by
      rw [Nat.cast_mul, ← hdm]; linarith
    exact Nat.cast_lt.mp this
  refine (measure_mono hsub).trans ?_
  refine (measure_tau_gt_le hn C R ⌊x / ((n : ℝ) - 1)⌋₊).trans ?_
  exact ENNReal.ofReal_le_ofReal
    (one_sub_pow_floor_le (d := (n : ℝ) - 1) (epsP_pos C) (epsP_le_one C i0) hnd hx)

end MomentInput

/-! ## 8. The moment bound (Lemma B.4) -/

section MomentBound

open MeasureTheory in
/-- FTC for the Beta density: `∫_0^a β t^{β−1} dt = a^β` for `β > 1`, `a ≥ 0`. -/
lemma intervalIntegral_beta {β a : ℝ} (hβ : 1 ≤ β) (ha : 0 ≤ a) :
    ∫ t in (0 : ℝ)..a, β * t ^ (β - 1) = a ^ β := by
  rw [intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith : -1 < β - 1))]
  have hz : (0 : ℝ) ^ (β - 1 + 1) = 0 := Real.zero_rpow (by linarith : β - 1 + 1 ≠ 0)
  have hc : β - 1 + 1 = β := by ring
  rw [hz, hc, sub_zero]
  field_simp

/-- **Lemma B.4, moment bound.** `E τ(i₀)^β ≤ e Γ(β+1) ((n−1)/ε_P)^β`. -/
theorem integral_rpow_tau_le {n : ℕ} (hn : 2 ≤ n) (C : ContactMatrix n) {i0 : Fin n}
    (R : ReachData C.P i0) {β : ℝ} (hβ : 1 ≤ β) :
    ∫⁻ ω, ENNReal.ofReal ((tau (by omega : 0 < n - 1) ω i0 : ℝ) ^ β) ∂procMeasure C (n - 1) ≤
      ENNReal.ofReal (Real.exp 1 * Real.Gamma (β + 1) * (((n : ℝ) - 1) / epsP C) ^ β) := by
  have hd : 0 < n - 1 := by omega
  have hnd : (0 : ℝ) < (n : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hε : 0 < epsP C := epsP_pos C
  have hr : 0 < epsP C / ((n : ℝ) - 1) := div_pos hε hnd
  have hβ0 : 0 < β := by linarith
  -- FTC rewrite of the integrand
  have hFTC : ∀ ω : ℕ → Fin (n - 1) → Fin n → Fin n,
      ENNReal.ofReal ((tau hd ω i0 : ℝ) ^ β) =
        ENNReal.ofReal (∫ t in (0 : ℝ)..(tau hd ω i0 : ℝ), β * t ^ (β - 1)) :=
    fun ω => by rw [intervalIntegral_beta hβ (Nat.cast_nonneg _)]
  -- the layer-cake identity
  have hlay := lintegral_comp_eq_lintegral_meas_lt_mul (μ := procMeasure C (n - 1))
    (f := fun ω : ℕ → Fin (n - 1) → Fin n → Fin n => (tau hd ω i0 : ℝ))
    (g := fun t : ℝ => β * t ^ (β - 1))
    (Filter.Eventually.of_forall fun ω => Nat.cast_nonneg _)
    (measurable_tau_real hd i0).aemeasurable
    (fun t _ => ContinuousOn.intervalIntegrable
      ((continuous_const.mul (Real.continuous_rpow_const (q := β - 1)
        (by linarith : (0 : ℝ) ≤ β - 1))).continuousOn))
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg (by linarith) (Real.rpow_nonneg ht.le _))
  rw [lintegral_congr_ae (Filter.Eventually.of_forall hFTC), hlay]
  have hbound : ∫⁻ t in Set.Ioi 0, (procMeasure C (n - 1)) {a | t < (tau hd a i0 : ℝ)} *
        ENNReal.ofReal (β * t ^ (β - 1)) ≤
      ∫⁻ t in Set.Ioi 0,
        ENNReal.ofReal (Real.exp 1 * Real.exp (-(epsP C * (t / ((n : ℝ) - 1))))) *
          ENNReal.ofReal (β * t ^ (β - 1)) := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_le_mul_right' (measure_tau_gt_real_le hn C R ht.le) _
  refine hbound.trans ?_
  have hprodmul : ∀ t : ℝ,
      ENNReal.ofReal (Real.exp 1 * Real.exp (-(epsP C * (t / ((n : ℝ) - 1))))) *
        ENNReal.ofReal (β * t ^ (β - 1)) =
      ENNReal.ofReal (Real.exp 1 * Real.exp (-(epsP C * (t / ((n : ℝ) - 1)))) *
        (β * t ^ (β - 1))) := fun t => (ENNReal.ofReal_mul (by positivity)).symm
  rw [lintegral_congr_ae (Filter.Eventually.of_forall hprodmul)]
  have hr_eq : ∀ t : ℝ, epsP C * (t / ((n : ℝ) - 1)) = (epsP C / ((n : ℝ) - 1)) * t := by
    intro t; ring_nf
  have hreg : (fun t : ℝ => Real.exp 1 * Real.exp (-(epsP C * (t / ((n : ℝ) - 1)))) * (β * t ^ (β - 1)))
      = fun t => (Real.exp 1 * β) * (t ^ (β - 1) * Real.exp (-(epsP C * (t / ((n : ℝ) - 1))))) := by
    funext t; ring_nf
  have hcong : ∫ t in Set.Ioi 0, t ^ (β - 1) * Real.exp (-(epsP C * (t / ((n : ℝ) - 1)))) =
      ∫ t in Set.Ioi 0, t ^ (β - 1) * Real.exp (-((epsP C / ((n : ℝ) - 1)) * t)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    rw [hr_eq t]
  have hkey := Real.integral_rpow_mul_exp_neg_mul_Ioi hβ0 hr
  have hint1 : IntegrableOn
      (fun t : ℝ => t ^ (β - 1) * Real.exp (-((epsP C / ((n : ℝ) - 1)) * t))) (Set.Ioi 0) := by
    refine .of_integral_ne_zero (fun h => ?_)
    refine absurd (show (1 / (epsP C / ((n : ℝ) - 1))) ^ β * Real.Gamma β = 0 from ?_)
      (ne_of_gt (mul_pos (Real.rpow_pos_of_pos (one_div_pos.mpr hr) β)
        (Real.Gamma_pos_of_pos hβ0)))
    rw [← hkey]; exact h
  have hint1' : IntegrableOn
      (fun t : ℝ => t ^ (β - 1) * Real.exp (-(epsP C * (t / ((n : ℝ) - 1))))) (Set.Ioi 0) := by
    refine .of_integral_ne_zero (fun h => ?_)
    refine absurd (show (1 / (epsP C / ((n : ℝ) - 1))) ^ β * Real.Gamma β = 0 from ?_)
      (ne_of_gt (mul_pos (Real.rpow_pos_of_pos (one_div_pos.mpr hr) β)
        (Real.Gamma_pos_of_pos hβ0)))
    rw [← hkey, ← hcong]; exact h
  have hInt : IntegrableOn
      (fun t : ℝ => Real.exp 1 * Real.exp (-(epsP C * (t / ((n : ℝ) - 1)))) * (β * t ^ (β - 1)))
      (Set.Ioi 0) := by
    rw [hreg]; exact hint1'.const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hInt (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      (mul_nonneg (by linarith) (Real.rpow_nonneg ht.le _)))]
  rw [hreg, MeasureTheory.integral_const_mul, hcong, hkey,
    Real.Gamma_add_one (by linarith : β ≠ 0)]
  rw [show (1 / (epsP C / ((n : ℝ) - 1))) ^ β = (((n : ℝ) - 1) / epsP C) ^ β from by
    congr 1
    rw [one_div, inv_div]]
  ring_nf
  exact le_rfl

end MomentBound


end AnvBandit
