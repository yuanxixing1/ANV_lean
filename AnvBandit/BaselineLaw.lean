import AnvBandit.BaselineExecution
import AnvBandit.ExecutionLaw
noncomputable section
open scoped BigOperators Classical
open Finset MeasureTheory ProbabilityTheory
namespace AnvBandit.BaselineLaw
variable {n K : ℕ}
open ExecutionLaw (finiteProduct finiteProduct_apply finiteProduct_map_eval)
def rewardReal (x : Bool) : ℝ := if x then 1 else 0

theorem rewardReal_mem (x : Bool) : rewardReal x ∈ Set.Icc (0 : ℝ) 1 := by
  cases x <;> norm_num [rewardReal]

def realTape (X : ℕ → Fin n → Bool) : ℕ → Fin n → ℝ :=
  fun t i => rewardReal (X t i)

/-- Effective use at the start of round `t` (paper round `t+1`). -/
def effectiveUse (p : BaselineExecution.Params n K) (lam : Fin 2)
    (X : ℕ → Fin n → Bool) (J : ℕ → Fin n → Fin n)
    (t : ℕ) (i : Fin n) (k : Fin K) : ℕ :=
  1 + if lam = 0 then BaselineExecution.N p (realTape X) J t i k
      else BaselineExecution.teamCount p (realTape X) J t k

/-- The model's conditional reward mean, evaluated at the actual action and history. -/
def actualMean (M : DecayModel n K) (p : BaselineExecution.Params n K) (lam : Fin 2)
    (X : ℕ → Fin n → Bool) (J : ℕ → Fin n → Fin n)
    (t : ℕ) (i : Fin n) : ℝ :=
  let k := BaselineExecution.I p (realTape X) J t i
  M.mean k (effectiveUse p lam X J t i k)

theorem personal_le_team (p : BaselineExecution.Params n K) (X J) (t : ℕ)
    (i : Fin n) (k : Fin K) :
    BaselineExecution.N p (realTape X) J t i k ≤ BaselineExecution.teamCount p (realTape X) J t k := by
  unfold BaselineExecution.teamCount
  exact Finset.single_le_sum (f := fun j : Fin n => BaselineExecution.N p (realTape X) J t j k)
    (fun j _ => Nat.zero_le _) (Finset.mem_univ i)

theorem personal_le_effectiveUse (p : BaselineExecution.Params n K) (lam : Fin 2)
    (X J) (t : ℕ) (i : Fin n) (k : Fin K) :
    1 + BaselineExecution.N p (realTape X) J t i k ≤ effectiveUse p lam X J t i k := by
  unfold effectiveUse
  split
  · exact le_rfl
  · exact Nat.add_le_add_left (personal_le_team p X J t i k) 1

theorem actualMean_bounds (M : DecayModel n K) (p : BaselineExecution.Params n K)
    (lam : Fin 2) (X J) (t : ℕ) (i : Fin n) :
    M.b (BaselineExecution.I p (realTape X) J t i) ≤ actualMean M p lam X J t i ∧
    actualMean M p lam X J t i ≤ 1 := by
  dsimp [actualMean, DecayModel.mean]
  constructor
  · exact le_add_of_nonneg_right (M.f_nonneg _ _)
  · have h := M.f_le_gap (BaselineExecution.I p (realTape X) J t i)
        (effectiveUse p lam X J t i (BaselineExecution.I p (realTape X) J t i))
    linarith

theorem actualMean_mem (M : DecayModel n K) (p : BaselineExecution.Params n K)
    (lam : Fin 2) (X J) (t : ℕ) (i : Fin n) :
    actualMean M p lam X J t i ∈ Set.Icc (0 : ℝ) 1 := by
  have h := actualMean_bounds M p lam X J t i
  exact ⟨le_trans (le_of_lt (M.b_pos _)) h.1, h.2⟩

/-- Public fatigue uses a single common pre-round state for equal chosen arms. -/
theorem public_same_arm_mean (M : DecayModel n K) (p : BaselineExecution.Params n K)
    (X J) (t : ℕ) (i j : Fin n)
    (h : BaselineExecution.I p (realTape X) J t i = BaselineExecution.I p (realTape X) J t j) :
    actualMean M p 1 X J t i = actualMean M p 1 X J t j := by
  simp [actualMean, effectiveUse, h]

/-- Pathwise history-dependent mean bound used at each actually selected observation. -/
theorem actualMean_le_personal_envelope (M : DecayModel n K)
    (p : BaselineExecution.Params n K) (lam : Fin 2) (X J) (t : ℕ) (i : Fin n) :
    actualMean M p lam X J t i ≤
      M.b (BaselineExecution.I p (realTape X) J t i) +
        M.f (BaselineExecution.I p (realTape X) J t i)
          (1 + BaselineExecution.N p (realTape X) J t i (BaselineExecution.I p (realTape X) J t i)) := by
  unfold actualMean DecayModel.mean
  exact add_le_add_right
    (M.f_anti _ (personal_le_effectiveUse p lam X J t i _)) _

/-- Reward means for one pre-round state of the deterministic transducer. -/
def stateMean (M : DecayModel n K) (p : BaselineExecution.Params n K) (lam : Fin 2)
    (s : BaselineExecution.State n K) (i : Fin n) : ℝ :=
  let k := BaselineExecution.actions p s i
  M.mean k (1 + if lam = 0 then (s.nodes i).N k else ∑ j, (s.nodes j).N k)

theorem stateMean_mem (M : DecayModel n K) (p : BaselineExecution.Params n K) (lam : Fin 2)
    (s : BaselineExecution.State n K) (i : Fin n) : stateMean M p lam s i ∈ Set.Icc (0 : ℝ) 1 := by
  dsimp [stateMean, DecayModel.mean]
  constructor
  · exact add_nonneg (le_of_lt (M.b_pos _)) (M.f_nonneg _ _)
  · have h := M.f_le_gap (BaselineExecution.actions p s i)
      (1 + if lam = 0 then (s.nodes i).N (BaselineExecution.actions p s i)
          else ∑ j, (s.nodes j).N (BaselineExecution.actions p s i))
    linarith

/-- Independent conditional Bernoulli rewards from a fixed pre-round state. -/
def rewardDistribution (M : DecayModel n K) (p : BaselineExecution.Params n K) (lam : Fin 2)
    (s : BaselineExecution.State n K) : PMF (Fin n → Bool) :=
  finiteProduct fun i => PMF.bernoulli
    ⟨stateMean M p lam s i, (stateMean_mem M p lam s i).1⟩
    ((stateMean_mem M p lam s i).2)

theorem rewardDistribution_apply (M : DecayModel n K) (p : BaselineExecution.Params n K)
    (lam : Fin 2) (s : BaselineExecution.State n K) (x : Fin n → Bool) :
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

/-- Auxiliary second coordinate is deterministic and never observed or used. -/
abbrev Outcome (n : ℕ) := ExecutionLaw.Outcome n
def outcomeDistribution (M : DecayModel n K) (p : BaselineExecution.Params n K)
    (lam : Fin 2) (s : BaselineExecution.State n K) : PMF (Outcome n) :=
  (rewardDistribution M p lam s).map fun x => (x, id)
/-- Replay uses exactly the deterministic one-round update, including its terminal guard. -/
def replay (p : BaselineExecution.Params n K) (h : List (Outcome n)) : ℕ × BaselineExecution.State n K :=
  h.foldl (fun z o => (z.1 + 1,
    BaselineExecution.step p z.1 z.2 (fun i => rewardReal (o.1 i)) o.2)) (0, BaselineExecution.initial p)

@[simp] theorem replay_nil (p : BaselineExecution.Params n K) :
    replay p [] = (0, BaselineExecution.initial p) := rfl

theorem replay_append (p : BaselineExecution.Params n K) (h : List (Outcome n)) (o : Outcome n) :
    replay p (h ++ [o]) = ((replay p h).1 + 1,
      BaselineExecution.step p (replay p h).1 (replay p h).2 (fun i => rewardReal (o.1 i)) o.2) := by
  simp [replay, List.foldl_append]

@[simp] theorem outcomeDistribution_map_fst (M : DecayModel n K)
    (p : BaselineExecution.Params n K) (lam : Fin 2) (s : BaselineExecution.State n K) :
    (outcomeDistribution M p lam s).map Prod.fst = rewardDistribution M p lam s := by
  simp only [outcomeDistribution, PMF.map_comp, Function.comp_def]
  exact PMF.map_id _
theorem replay_time (p : BaselineExecution.Params n K) (h : List (Outcome n)) :
    (replay p h).1 = h.length := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h o ih => rw [replay_append]; simpa using congrArg Nat.succ ih

/-- Replay equals full-K execution; compatibility contacts are never read. -/
theorem replay_eq_run (p : BaselineExecution.Params n K) (ω : ℕ → Outcome n) (t : ℕ) :
    (replay p (List.ofFn (fun i : Fin t => ω (i.val + 1)))).2 =
      BaselineExecution.run p (fun r i => rewardReal ((ω (r + 1)).1 i))
        (fun ℓ => (ω (p.phaseEnd ℓ)).2) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [List.ofFn_succ']
    simp only [List.concat_eq_append, Fin.coe_castSucc, Fin.val_last]
    rw [replay_append, replay_time, List.length_ofFn, ih]
    simp only [BaselineExecution.run]
    rfl

/-- The mean computed by the state kernel is exactly the original history-dependent mean. -/
theorem stateMean_run (M : DecayModel n K) (p : BaselineExecution.Params n K)
    (lam : Fin 2) (X J) (t : ℕ) (i : Fin n) :
    stateMean M p lam (BaselineExecution.run p (realTape X) J t) i =
      actualMean M p lam X J t i := rfl


end AnvBandit.BaselineLaw
