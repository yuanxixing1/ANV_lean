import AnvBandit.Regret

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-!
# The contact process (Assumption 2.4) and the deterministic core of Lemma B.4

Assumption 2.4 models the request mechanism by a fixed irreducible row-stochastic matrix
`P ∈ [0,1]^{n×n}`.  Writing `R t i` for the node that agent `i` requests at step `t`, the set of
"informed" nodes evolves deterministically (`infStep`): a node becomes informed when it requests a
node that was informed at the start of the step, and informed nodes stay informed.

This file defines the dynamics (`infStep`, `Inform`), the informed-time `sigmaStep`, and proves the
**deterministic skeleton** of Lemma B.4: starting from any nonempty set, if every step before
completion adds at least one informed node, then after `n−1` steps the whole population is informed.
The probabilistic tail bound `P{τ(i0) > m(n−1)} ≤ (1−ε_P)^m` (which needs the product probability
space over the request draws and the conditional probability `p_min` of an increasing step) is
recorded in `AnvBandit.Statements.lemma_B_4` with those probabilistic inputs as explicit
hypotheses.
-/

noncomputable section
open scoped BigOperators
open Finset

namespace AnvBandit

/-- A nonnegative irreducible row-stochastic matrix with a positive lower bound on its
positive entries. `ofStochasticIrreducible` below selects the attained minimum required by
the paper's exact constants; arbitrary values of this field give only relaxed bounds. -/
structure ContactMatrix (n : ℕ) where
  P : Fin n → Fin n → ℝ
  nonneg : ∀ i j, 0 ≤ P i j
  row_sum : ∀ i, ∑ j, P i j = 1
  pmin : ℝ
  pmin_pos : 0 < pmin
  le_pmin : ∀ i j, 0 < P i j → pmin ≤ P i j
  irreducible : ∀ a b : Fin n, Relation.ReflTransGen (fun x y => 0 < P y x) a b

namespace ContactMatrix

/-- Positive matrix entries, with their row and column retained. -/
def positiveEntries {n : ℕ} (P : Fin n → Fin n → ℝ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun ij => 0 < P ij.1 ij.2)

lemma positiveEntries_nonempty {n : ℕ} (hn : 0 < n) (P : Fin n → Fin n → ℝ)
    (hrow : ∀ i, ∑ j, P i j = 1) : (positiveEntries P).Nonempty := by
  classical
  let i : Fin n := ⟨0, hn⟩
  by_contra h
  have hnonpos : ∀ j, P i j ≤ 0 := by
    intro j
    by_contra hj
    have hp : 0 < P i j := lt_of_not_ge hj
    exact h ⟨(i, j), by simp [positiveEntries, hp]⟩
  have hs : ∑ j, P i j ≤ 0 := Finset.sum_nonpos (fun j _ => hnonpos j)
  rw [hrow i] at hs
  norm_num at hs

/-- Canonical construction from the original stochastic/irreducibility assumptions.
Unlike an arbitrary valid lower bound in `ContactMatrix`, this `pmin` is attained. -/
def ofStochasticIrreducible {n : ℕ} (hn : 0 < n) (P : Fin n → Fin n → ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hrow : ∀ i, ∑ j, P i j = 1)
    (hirr : ∀ a b : Fin n, Relation.ReflTransGen (fun x y => 0 < P y x) a b) :
    ContactMatrix n where
  P := P
  nonneg := hP
  row_sum := hrow
  pmin := (positiveEntries P).inf' (positiveEntries_nonempty hn P hrow)
    (fun ij => P ij.1 ij.2)
  pmin_pos := by
    apply (Finset.lt_inf'_iff _).2
    intro ij hij
    exact (Finset.mem_filter.mp hij).2
  le_pmin := by
    intro i j hij
    exact Finset.inf'_le (fun ij => P ij.1 ij.2)
      (by simp [positiveEntries, hij] : (i, j) ∈ positiveEntries P)
  irreducible := hirr

theorem ofStochasticIrreducible_pmin_attained {n : ℕ} (hn : 0 < n)
    (P : Fin n → Fin n → ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (hrow : ∀ i, ∑ j, P i j = 1)
    (hirr : ∀ a b : Fin n, Relation.ReflTransGen (fun x y => 0 < P y x) a b) :
    ∃ i j, 0 < P i j ∧ (ofStochasticIrreducible hn P hP hrow hirr).pmin = P i j := by
  obtain ⟨ij, hij, heq⟩ := Finset.exists_mem_eq_inf'
    (positiveEntries_nonempty hn P hrow) (fun ij => P ij.1 ij.2)
  exact ⟨ij.1, ij.2, (Finset.mem_filter.mp hij).2, heq⟩

end ContactMatrix

/-- One propagation step: node `i` joins the informed set `A` if it requests a node of `A`. -/
def infStep {n : ℕ} (R : Fin n → Fin n) (A : Finset (Fin n)) : Finset (Fin n) :=
  A ∪ Finset.univ.filter (fun i => R i ∈ A)

/-- The informed set after `t` propagation steps, starting from `A`. -/
def Inform {n : ℕ} (R : ℕ → Fin n → Fin n) (A : Finset (Fin n)) : ℕ → Finset (Fin n)
  | 0 => A
  | t + 1 => infStep (R t) (Inform R A t)

@[simp] lemma Inform_zero {n : ℕ} (R : ℕ → Fin n → Fin n) (A : Finset (Fin n)) :
    Inform R A 0 = A := rfl

lemma Inform_succ {n : ℕ} (R : ℕ → Fin n → Fin n) (A : Finset (Fin n)) (t : ℕ) :
    Inform R A (t + 1) = infStep (R t) (Inform R A t) := rfl

lemma subset_infStep {n : ℕ} (R : Fin n → Fin n) (A : Finset (Fin n)) :
    A ⊆ infStep R A := Finset.subset_union_left

/-- The informed set only grows. -/
lemma subset_Inform {n : ℕ} (R : ℕ → Fin n → Fin n) (A : Finset (Fin n)) :
    ∀ t, A ⊆ Inform R A t
  | 0 => Finset.Subset.refl A
  | t + 1 => (subset_Inform R A t).trans (subset_infStep (R t) _)

lemma Inform_mono {n : ℕ} (R : ℕ → Fin n → Fin n) {A B : Finset (Fin n)} (hAB : A ⊆ B) :
    ∀ t, Inform R A t ⊆ Inform R B t
  | 0 => hAB
  | t + 1 => by
    refine Finset.union_subset_union (Inform_mono R hAB t) ?_
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact Inform_mono R hAB t hi

/-- **Deterministic core of Lemma B.4.** If at each of the first `n − 1` steps the informed set
strictly grows (which happens whenever the step reaches a node of the *uninformed* complement), then
after `n − 1` steps the whole population is informed. -/
theorem Inform_eq_univ_of_increasing {n : ℕ} (R : ℕ → Fin n → Fin n) {A : Finset (Fin n)}
    (hne : A.Nonempty)
    (hincr : ∀ t, t < n - 1 → (Inform R A t).card < (Inform R A (t + 1)).card) :
    Inform R A (n - 1) = Finset.univ := by
  have hcard : ∀ t, t ≤ n - 1 → A.card + t ≤ (Inform R A t).card := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
      intro ht
      have h1 : A.card + t ≤ (Inform R A t).card := ih (by omega)
      have h2 : (Inform R A t).card < (Inform R A (t + 1)).card := hincr t (by omega)
      omega
  have hne' : 1 ≤ A.card := by have := Finset.card_pos.mpr hne; omega
  have hAcard : A.card ≤ n := by
    calc A.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  have hle : (Inform R A (n - 1)).card ≤ n := by
    calc (Inform R A (n - 1)).card ≤ (Finset.univ : Finset (Fin n)).card :=
          Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  have hge : n ≤ (Inform R A (n - 1)).card := by
    have h1 := hcard (n - 1) le_rfl
    omega
  have : (Inform R A (n - 1)).card = n := le_antisymm hle hge
  exact Finset.eq_univ_of_card _ (by rw [this, Fintype.card_fin])

/-- Propagation delay of node `i`: the first step at which it is informed, starting from `{i0}`. -/
def sigmaStep {n : ℕ} (R : ℕ → Fin n → Fin n) (i0 i : Fin n) : ℕ :=
  sInf {t | i ∈ Inform R {i0} t}

end AnvBandit
