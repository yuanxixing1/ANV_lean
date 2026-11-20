import AnvBandit.AlgCount

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-!
# The cached recommendation (3.7) and propagation dominance/stability (Lemma B.5)

* `topArg` formalises the "minimal argmax" rule `B^{(ℓ)}_i = min arg max_{k∈S^{(ℓ)}_i} C^{(ℓ)}_{i,k}`
  of equation (3.7), together with its argmax property (used by the reliable-recommendation
  Lemma B.2).
* `RunModel` records the run-level structure of Algorithm 1 (phases, active sets, cached
  recommendations, contacts) together with the *definitional* consequences of the reliable-phase
  Lemma B.3 and the update rule (3.8): a holder of `k⋆` recommends it, and receiving `k⋆` (or
  holding it) keeps it at the next phase.
* `lemma_B_5_stable` is then the genuine induction of Lemma B.5: on `E_δ`, the informed set of the
  auxiliary propagation after step `j` is contained in the set of nodes holding `k⋆` at phase
  `ℓ_0 + j`.
-/

noncomputable section
open scoped BigOperators
open Finset

namespace AnvBandit

variable {n K : ℕ}

/-- Equation (3.7): the cached recommendation is the minimal argmax of the phase counts over the
active set. -/
def topArg {K : ℕ} (c : Fin K → ℝ) (S : Finset (Fin K)) (hS : S.Nonempty) : Fin K :=
  (S.filter (fun k => c k = S.sup' hS c)).min'
    (by obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup' hS c
        exact ⟨k, Finset.mem_filter.mpr ⟨hk, hkeq.symm⟩⟩)

lemma topArg_mem (c : Fin K → ℝ) (S : Finset (Fin K)) (hS : S.Nonempty) :
    topArg c S hS ∈ S :=
  Finset.mem_of_mem_filter _ (Finset.min'_mem _ _)

lemma topArg_max (c : Fin K → ℝ) (S : Finset (Fin K)) (hS : S.Nonempty) {k : Fin K} (hk : k ∈ S) :
    c k ≤ c (topArg c S hS) := by
  have hmem : topArg c S hS ∈ S.filter (fun k => c k = S.sup' hS c) := Finset.min'_mem _ _
  rw [(Finset.mem_filter.mp hmem).2]
  exact Finset.le_sup' c hk

lemma topArg_min (c : Fin K → ℝ) (S : Finset (Fin K)) (hS : S.Nonempty) {k : Fin K}
    (hk : k ∈ S) (hmax : c k = S.sup' hS c) : topArg c S hS ≤ k :=
  Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hk, hmax⟩)

/-- Run-level structure of Algorithm 1 on `E_δ`.  The fields record the phases, active sets,
cached recommendations and contacts together with the *definitional* consequences of the reliable
phase (Lemma B.3) and of the update rule (3.8). -/
structure RunModel (M : DecayModel n K) where
  /-- The phase index `ℓ_0 = r_H + 1` from which reliable phases begin. -/
  l0 : ℕ
  /-- The permanent holder `i⋆` of `k⋆`. -/
  i0 : Fin n
  /-- Active set of node `i` during phase `ℓ`. -/
  Aph : ℕ → Fin n → Finset (Fin K)
  /-- Cached recommendation of node `i` at the end of phase `ℓ`. -/
  cache : ℕ → Fin n → Fin K
  /-- Contactee requested by node `i` at the end of phase `ℓ`. -/
  J : ℕ → Fin n → Fin n
  /-- The source node permanently holds `k⋆`. -/
  source_holds : ∀ ℓ, M.star ∈ Aph ℓ i0
  /-- Lemma B.3: in a reliable phase, a holder of `k⋆` recommends it. -/
  rec_star : ∀ ℓ i, l0 ≤ ℓ → M.star ∈ Aph ℓ i → cache ℓ i = M.star
  /-- Update rule (3.8): receiving `k⋆` keeps it at the next phase. -/
  upd_get : ∀ ℓ i, l0 ≤ ℓ → cache ℓ (J ℓ i) = M.star → M.star ∈ Aph (ℓ + 1) i
  /-- Update rule (3.8) + uniqueness of the phase maximum: holding `k⋆` keeps it. -/
  upd_keep : ∀ ℓ i, l0 ≤ ℓ → M.star ∈ Aph ℓ i → M.star ∈ Aph (ℓ + 1) i

/-- The informed set of the auxiliary propagation after `j` steps. -/
def RunModel.infSet {n K : ℕ} {M : DecayModel n K} (Rm : RunModel M) : ℕ → Finset (Fin n)
  | 0 => ({Rm.i0} : Finset (Fin n))
  | (j + 1) => RunModel.infSet Rm j ∪
      ((Finset.univ : Finset (Fin n)).filter
        (fun i => Rm.J (Rm.l0 + j) i ∈ RunModel.infSet Rm j))

/-- **Lemma B.5 (propagation dominance/stability).**  On `E_δ`, every node informed after the `j`-th
auxiliary propagation step holds `k⋆` at the start of phase `ℓ_0 + j`. -/
theorem lemma_B_5_stable (Rm : RunModel M) :
    ∀ j i, i ∈ Rm.infSet j → M.star ∈ Rm.Aph (Rm.l0 + j) i := by
  intro j
  induction j with
  | zero =>
    intro i hi
    rw [RunModel.infSet, Finset.mem_singleton] at hi
    subst hi
    exact Rm.source_holds Rm.l0
  | succ j ih =>
    intro i hi
    rw [RunModel.infSet, Finset.mem_union, Finset.mem_filter] at hi
    rcases hi with h | ⟨_, hcontact⟩
    · have h1 := ih i h
      have := Rm.upd_keep (Rm.l0 + j) i (Nat.le_add_right _ _) h1
      rwa [show Rm.l0 + (j + 1) = Rm.l0 + j + 1 by omega]
    · have h1 := ih (Rm.J (Rm.l0 + j) i) hcontact
      have h2 := Rm.rec_star (Rm.l0 + j) (Rm.J (Rm.l0 + j) i) (Nat.le_add_right _ _) h1
      have := Rm.upd_get (Rm.l0 + j) i (Nat.le_add_right _ _) h2
      rwa [show Rm.l0 + (j + 1) = Rm.l0 + j + 1 by omega]

/-- **Lemma B.5 (permanence of the stabilised set).**  Once every node holds `k⋆` at some reliable
phase `l ≥ l₀`, it holds `k⋆` at every later phase: the active sets only gain `k⋆` and never
lose it (`upd_keep`). -/
theorem RunModel.holds_forever {n K : ℕ} {M : DecayModel n K} (Rm : RunModel M) {l : ℕ}
    (hl : Rm.l0 ≤ l) (h : ∀ i, M.star ∈ Rm.Aph l i) :
    ∀ d, ∀ i, M.star ∈ Rm.Aph (l + d) i := by
  intro d
  induction d with
  | zero => simpa using h
  | succ d ih =>
    intro i
    have := Rm.upd_keep (l + d) i (by omega) (ih i)
    rwa [show l + (d + 1) = l + d + 1 by omega]

/-- Corollary of Lemma B.5: once the auxiliary propagation has finished (`τ` steps), every node
holds `k⋆`, and — by the update rule — keeps holding it. -/
theorem lemma_B_5_all (Rm : RunModel M) {τ : ℕ} (hτ : Rm.infSet τ = (Finset.univ : Finset (Fin n))) :
    ∀ i, M.star ∈ Rm.Aph (Rm.l0 + τ) i :=
  fun i => lemma_B_5_stable Rm τ i (by rw [hτ]; exact Finset.mem_univ i)

end AnvBandit
