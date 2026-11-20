import AnvBandit.BaselineProbability

/-! Operational baseline audit: all arms available and strictly local information use.
The public-fatigue environment is shared, but the selection algorithm itself receives no
other node's data, public counts, or messages. -/
noncomputable section
open Finset
namespace AnvBandit.BaselineExecution
variable {n K : ℕ}

theorem full_arm_set (p : Params n K) (X : ℕ → Fin n → ℝ)
    (J : ℕ → Fin n → Fin n) (t : ℕ) (i : Fin n) :
    ((run p X J t).nodes i).active = univ := rfl

theorem local_state_congr (p : Params n K) (X X' : ℕ → Fin n → ℝ)
    (J J' : ℕ → Fin n → Fin n) (t : ℕ) (i : Fin n)
    (hx : ∀ s < t, X s i = X' s i) :
    (run p X J t).nodes i = (run p X' J' t).nodes i := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hi := ih (fun s hs => hx s (by omega))
    simp only [run, step]
    split
    · simp only [observe]
      rw [hi, hx t (by omega)]
    · exact hi

theorem action_local_information (p : Params n K) (X X' : ℕ → Fin n → ℝ)
    (J J' : ℕ → Fin n → Fin n) (t : ℕ) (i : Fin n)
    (hx : ∀ s < t, X s i = X' s i) : I p X J t i = I p X' J' t i := by
  unfold I actions
  rw [local_state_congr p X X' J J' t i hx]

/-- The algorithm uses no phase/contact parameter: only the shared horizon and confidence
logarithm can affect its execution. -/
theorem choose_params_congr (p q : Params n K) (hL : p.L = q.L)
    (i : Fin n) (s : LocalState n K i) : s.choose p = s.choose q := by
  unfold LocalState.choose LocalState.index
  rw [hL]

theorem run_params_congr (p q : Params n K) (hT : p.T = q.T) (hL : p.L = q.L)
    (X : ℕ → Fin n → ℝ) (J : ℕ → Fin n → Fin n) (t : ℕ) :
    run p X J t = run q X J t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [run, step, hT, ih]
    split
    · unfold observe
      congr 1
      funext i
      unfold LocalState.observe
      rw [choose_params_congr p q hL]
    · rfl

end AnvBandit.BaselineExecution
