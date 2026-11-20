import AnvBandit.Execution
import AnvBandit.Contact
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Reward semantics of the actual execution

The deterministic functions here evaluate the original model along the actual recursively
defined execution. Boolean rewards are cast into the real reward input of that execution.
The public effective count is evaluated before the simultaneous reward vector, never updated
between nodes. These statements do not yet constitute the probability-law construction.
-/
noncomputable section
open scoped BigOperators Classical
set_option maxHeartbeats 1000000
open Finset MeasureTheory ProbabilityTheory

namespace AnvBandit.ExecutionLaw

variable {n K : ℕ}

/-- Exact real encoding of a Bernoulli outcome. -/
def rewardReal (x : Bool) : ℝ := if x then 1 else 0

theorem rewardReal_mem (x : Bool) : rewardReal x ∈ Set.Icc (0 : ℝ) 1 := by
  cases x <;> norm_num [rewardReal]

def realTape (X : ℕ → Fin n → Bool) : ℕ → Fin n → ℝ :=
  fun t i => rewardReal (X t i)

/-- Effective use at the start of round `t` (paper round `t+1`). -/
def effectiveUse (p : Execution.Params n K) (lam : Fin 2)
    (X : ℕ → Fin n → Bool) (J : ℕ → Fin n → Fin n)
    (t : ℕ) (i : Fin n) (k : Fin K) : ℕ :=
  1 + if lam = 0 then Execution.N p (realTape X) J t i k
      else Execution.teamCount p (realTape X) J t k

/-- The model's conditional reward mean, evaluated at the actual action and history. -/
def actualMean (M : DecayModel n K) (p : Execution.Params n K) (lam : Fin 2)
    (X : ℕ → Fin n → Bool) (J : ℕ → Fin n → Fin n)
    (t : ℕ) (i : Fin n) : ℝ :=
  let k := Execution.I p (realTape X) J t i
  M.mean k (effectiveUse p lam X J t i k)

theorem personal_le_team (p : Execution.Params n K) (X J) (t : ℕ)
    (i : Fin n) (k : Fin K) :
    Execution.N p (realTape X) J t i k ≤ Execution.teamCount p (realTape X) J t k := by
  unfold Execution.teamCount
  exact Finset.single_le_sum (f := fun j : Fin n => Execution.N p (realTape X) J t j k)
    (fun j _ => Nat.zero_le _) (Finset.mem_univ i)

theorem personal_le_effectiveUse (p : Execution.Params n K) (lam : Fin 2)
    (X J) (t : ℕ) (i : Fin n) (k : Fin K) :
    1 + Execution.N p (realTape X) J t i k ≤ effectiveUse p lam X J t i k := by
  unfold effectiveUse
  split
  · exact le_rfl
  · exact Nat.add_le_add_left (personal_le_team p X J t i k) 1

theorem actualMean_bounds (M : DecayModel n K) (p : Execution.Params n K)
    (lam : Fin 2) (X J) (t : ℕ) (i : Fin n) :
    M.b (Execution.I p (realTape X) J t i) ≤ actualMean M p lam X J t i ∧
    actualMean M p lam X J t i ≤ 1 := by
  dsimp [actualMean, DecayModel.mean]
  constructor
  · exact le_add_of_nonneg_right (M.f_nonneg _ _)
  · have h := M.f_le_gap (Execution.I p (realTape X) J t i)
        (effectiveUse p lam X J t i (Execution.I p (realTape X) J t i))
    linarith

theorem actualMean_mem (M : DecayModel n K) (p : Execution.Params n K)
    (lam : Fin 2) (X J) (t : ℕ) (i : Fin n) :
    actualMean M p lam X J t i ∈ Set.Icc (0 : ℝ) 1 := by
  have h := actualMean_bounds M p lam X J t i
  exact ⟨le_trans (le_of_lt (M.b_pos _)) h.1, h.2⟩

/-- Public fatigue uses a single common pre-round state for equal chosen arms. -/
theorem public_same_arm_mean (M : DecayModel n K) (p : Execution.Params n K)
    (X J) (t : ℕ) (i j : Fin n)
    (h : Execution.I p (realTape X) J t i = Execution.I p (realTape X) J t j) :
    actualMean M p 1 X J t i = actualMean M p 1 X J t j := by
  simp [actualMean, effectiveUse, h]

/-- Pathwise history-dependent mean bound used at each actually selected observation. -/
theorem actualMean_le_personal_envelope (M : DecayModel n K)
    (p : Execution.Params n K) (lam : Fin 2) (X J) (t : ℕ) (i : Fin n) :
    actualMean M p lam X J t i ≤
      M.b (Execution.I p (realTape X) J t i) +
        M.f (Execution.I p (realTape X) J t i)
          (1 + Execution.N p (realTape X) J t i (Execution.I p (realTape X) J t i)) := by
  unfold actualMean DecayModel.mean
  exact add_le_add_right
    (M.f_anti _ (personal_le_effectiveUse p lam X J t i _)) _

/-- Finite independent product, retaining the full joint law rather than only marginals. -/
def finiteProduct {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Fintype (α i)]
    (q : ∀ i, PMF (α i)) : PMF (∀ i, α i) :=
  PMF.ofFintype (fun x => ∏ i, q i (x i)) (by
    classical
    rw [← Fintype.prod_sum]
    have hsum (i : ι) : ∑ x, q i x = 1 := by
      simpa only [tsum_fintype] using (q i).tsum_coe
    simp_rw [hsum]
    simp)

@[simp] theorem finiteProduct_apply {ι : Type*} [Fintype ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] (q : ∀ i, PMF (α i)) (x : ∀ i, α i) :
    finiteProduct q x = ∏ i, q i (x i) := rfl

/-- Reward means for one pre-round state of the deterministic transducer. -/
def stateMean (M : DecayModel n K) (p : Execution.Params n K) (lam : Fin 2)
    (s : Execution.State n K) (i : Fin n) : ℝ :=
  let k := Execution.actions p s i
  M.mean k (1 + if lam = 0 then (s.nodes i).N k else ∑ j, (s.nodes j).N k)

theorem stateMean_mem (M : DecayModel n K) (p : Execution.Params n K) (lam : Fin 2)
    (s : Execution.State n K) (i : Fin n) : stateMean M p lam s i ∈ Set.Icc (0 : ℝ) 1 := by
  dsimp [stateMean, DecayModel.mean]
  constructor
  · exact add_nonneg (le_of_lt (M.b_pos _)) (M.f_nonneg _ _)
  · have h := M.f_le_gap (Execution.actions p s i)
      (1 + if lam = 0 then (s.nodes i).N (Execution.actions p s i)
          else ∑ j, (s.nodes j).N (Execution.actions p s i))
    linarith

/-- Independent conditional Bernoulli rewards from a fixed pre-round state. -/
def rewardDistribution (M : DecayModel n K) (p : Execution.Params n K) (lam : Fin 2)
    (s : Execution.State n K) : PMF (Fin n → Bool) :=
  finiteProduct fun i => PMF.bernoulli
    ⟨stateMean M p lam s i, (stateMean_mem M p lam s i).1⟩
    ((stateMean_mem M p lam s i).2)

/-- Row law of the original contact matrix. -/
def contactRow (C : ContactMatrix n) (i : Fin n) : PMF (Fin n) :=
  PMF.ofFintype (fun j => ENNReal.ofReal (C.P i j)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => C.nonneg i j), C.row_sum i]
    simp)

def contactDistribution (C : ContactMatrix n) : PMF (Fin n → Fin n) :=
  finiteProduct (contactRow C)

theorem contactDistribution_apply (C : ContactMatrix n) (j : Fin n → Fin n) :
    contactDistribution C j = ∏ i, ENNReal.ofReal (C.P i (j i)) := rfl

theorem rewardDistribution_apply (M : DecayModel n K) (p : Execution.Params n K)
    (lam : Fin 2) (s : Execution.State n K) (x : Fin n → Bool) :
    rewardDistribution M p lam s x =
      ∏ i, if x i then ENNReal.ofReal (stateMean M p lam s i)
            else 1 - ENNReal.ofReal (stateMean M p lam s i) := by
  unfold rewardDistribution
  rw [finiteProduct_apply]
  apply Finset.prod_congr rfl
  intro i hi
  have he : (⟨stateMean M p lam s i, (stateMean_mem M p lam s i).1⟩ : NNReal) =
      (stateMean M p lam s i).toNNReal := by
    apply NNReal.eq
    simp [Real.toNNReal_of_nonneg (stateMean_mem M p lam s i).1]
    rfl
  cases h : x i <;> simp [PMF.bernoulli_apply, h, he, ENNReal.ofReal]

/-- A round's fresh random inputs; unused contact draws are analysis-only. -/
abbrev Outcome (n : ℕ) := (Fin n → Bool) × (Fin n → Fin n)

def outcomeDistribution (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (s : Execution.State n K) : PMF (Outcome n) :=
  (rewardDistribution M p lam s).bind fun x =>
    (contactDistribution C).map fun j => (x, j)

/-- Replay uses exactly the deterministic one-round update, including its terminal guard. -/
def replay (p : Execution.Params n K) (h : List (Outcome n)) : ℕ × Execution.State n K :=
  h.foldl (fun z o => (z.1 + 1,
    Execution.step p z.1 z.2 (fun i => rewardReal (o.1 i)) o.2)) (0, Execution.initial p)

@[simp] theorem replay_nil (p : Execution.Params n K) :
    replay p [] = (0, Execution.initial p) := rfl

theorem replay_append (p : Execution.Params n K) (h : List (Outcome n)) (o : Outcome n) :
    replay p (h ++ [o]) = ((replay p h).1 + 1,
      Execution.step p (replay p h).1 (replay p h).2 (fun i => rewardReal (o.1 i)) o.2) := by
  simp [replay, List.foldl_append]

/-- A normalized finite-history law exists for every original environment and contact matrix.
This construction does not assume concentration, good events, reliability, or regret bounds.
The subsequent conditional-law/correspondence proofs remain separate obligations. -/
def historyDistribution (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) : ℕ → PMF (List (Outcome n))
  | 0 => PMF.pure []
  | t + 1 => (historyDistribution M p C lam t).bind fun h =>
      (outcomeDistribution M p C lam (replay p h).2).map (fun o => h ++ [o])

/-- Every sampled history has the requested length; the normalized law is not an assumed
abstract object with potentially empty constraints. -/
theorem historyDistribution_support_length (M : DecayModel n K)
    (p : Execution.Params n K) (C : ContactMatrix n) (lam : Fin 2) (t : ℕ)
    (h : List (Outcome n)) (hh : h ∈ (historyDistribution M p C lam t).support) :
    h.length = t := by
  induction t generalizing h with
  | zero =>
    have heq : h = [] := by simpa [historyDistribution] using hh
    subst h
    rfl
  | succ t ih =>
    simp only [historyDistribution, PMF.mem_support_bind_iff] at hh
    obtain ⟨h₀, hh₀, hh⟩ := hh
    obtain ⟨o, ho, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hh
    simp [ih h₀ hh₀]


/-- A coordinate-weighted finite product sum; used to derive marginals from the joint law. -/
theorem product_weighted_sum {ι α R : Type*} [Fintype ι] [Fintype α]
    [CommSemiring R] (q : ι → α → R) (hq : ∀ i, ∑ a, q i a = 1)
    (i : ι) (g : α → R) :
    ∑ x : ι → α, (∏ j, q j (x j)) * g (x i) = ∑ a, q i a * g a := by
  classical
  calc
    _ = ∑ x : ι → α, ∏ j, q j (x j) * (if j = i then g (x j) else 1) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.prod_mul_distrib]
      simp
    _ = ∏ j, ∑ a, q j a * (if j = i then g a else 1) :=
      (Fintype.prod_sum (fun j a => q j a * (if j = i then g a else 1))).symm
    _ = ∏ j, if j = i then (∑ a, q j a * g a) else 1 := by
      apply Finset.prod_congr rfl
      intro j hj
      by_cases h : j = i <;> simp [h, hq]
    _ = _ := by simp

/-- Evaluation of the finite independent product has exactly the selected row law. -/
theorem finiteProduct_map_eval {ι α : Type*} [Fintype ι] [Fintype α]
    (q : ι → PMF α) (i : ι) : (finiteProduct q).map (fun x => x i) = q i := by
  classical
  ext a
  rw [PMF.map_apply, tsum_fintype]
  have hsum (j : ι) : ∑ b, q j b = 1 := by
    simpa only [tsum_fintype] using (q j).tsum_coe
  calc
    _ = ∑ x : ι → α, (∏ j, q j (x j)) * (if a = x i then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [finiteProduct_apply]
      split <;> simp_all
    _ = ∑ b, q i b * (if a = b then 1 else 0) :=
      product_weighted_sum (fun j b => q j b) hsum i (fun b => if a = b then 1 else 0)
    _ = _ := by simp

@[simp] theorem outcomeDistribution_map_fst (M : DecayModel n K)
    (p : Execution.Params n K) (C : ContactMatrix n) (lam : Fin 2)
    (s : Execution.State n K) :
    (outcomeDistribution M p C lam s).map Prod.fst = rewardDistribution M p lam s := by
  simp [outcomeDistribution, PMF.map_bind, PMF.map_comp, Function.comp_def,
    PMF.map_const, PMF.map]

@[simp] theorem outcomeDistribution_map_snd (M : DecayModel n K)
    (p : Execution.Params n K) (C : ContactMatrix n) (lam : Fin 2)
    (s : Execution.State n K) :
    (outcomeDistribution M p C lam s).map Prod.snd = contactDistribution C := by
  simp [outcomeDistribution, PMF.map_bind, PMF.map_comp, Function.comp_def,
    PMF.map]


/-- Full joint mass, including independence of fresh contacts from current rewards. -/
theorem outcomeDistribution_apply (M : DecayModel n K) (p : Execution.Params n K)
    (C : ContactMatrix n) (lam : Fin 2) (s : Execution.State n K) (o : Outcome n) :
    outcomeDistribution M p C lam s o =
      rewardDistribution M p lam s o.1 * contactDistribution C o.2 := by
  classical
  rcases o with ⟨x,j⟩
  simp [outcomeDistribution, PMF.bind_apply, PMF.map_apply, Prod.mk.injEq,
    and_comm, ite_and, tsum_ite_eq, tsum_ite_eq']

/-- The replay counter is exactly the history length, independent of the sampled outcomes. -/
theorem replay_time (p : Execution.Params n K) (h : List (Outcome n)) :
    (replay p h).1 = h.length := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h o ih => rw [replay_append]; simpa using congrArg Nat.succ ih

/-- Running a sequence of round inputs is identical to the phase-indexed execution:
only the contact vector at the actual boundary is read. -/
theorem replay_eq_run (p : Execution.Params n K) (ω : ℕ → Outcome n) (t : ℕ) :
    (replay p (List.ofFn (fun i : Fin t => ω (i.val + 1)))).2 =
      Execution.run p (fun r i => rewardReal ((ω (r + 1)).1 i))
        (fun ℓ => (ω (p.phaseEnd ℓ)).2) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [List.ofFn_succ']
    simp only [List.concat_eq_append, Fin.coe_castSucc, Fin.val_last]
    rw [replay_append, replay_time, List.length_ofFn, ih]
    simp only [Execution.run]
    unfold Execution.step
    split
    · split
      · rename_i hc
        have he := hc.1
        rw [he]
      · rfl
    · rfl

/-- The mean computed by the state kernel is exactly the original history-dependent mean. -/
theorem stateMean_run (M : DecayModel n K) (p : Execution.Params n K)
    (lam : Fin 2) (X J) (t : ℕ) (i : Fin n) :
    stateMean M p lam (Execution.run p (realTape X) J t) i =
      actualMean M p lam X J t i := rfl

end AnvBandit.ExecutionLaw
