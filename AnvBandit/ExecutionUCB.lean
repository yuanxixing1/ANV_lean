import AnvBandit.Execution
import AnvBandit.BaselineExecution

/-! Literal extended-real UCB and least-index tie-breaking, for both actual algorithms. -/
noncomputable section
open Finset
namespace AnvBandit.ExecutionUCB
variable {K : ℕ}

def extendedIndex (N : Fin K → ℕ) (u : Fin K → ℝ) (k : Fin K) : WithTop ℝ :=
  if N k = 0 then ⊤ else (u k : WithTop ℝ)

def priorityChoice (S : Finset (Fin K)) (hS : S.Nonempty)
    (N : Fin K → ℕ) (u : Fin K → ℝ) : Fin K :=
  if h : (S.filter (fun k => N k = 0)).Nonempty then
    (S.filter (fun k => N k = 0)).min' h
  else topArg u S hS

/-- Complete maximization and tie specification, not merely the comparison used in budgets. -/
theorem priorityChoice_spec (S : Finset (Fin K)) (hS : S.Nonempty)
    (N : Fin K → ℕ) (u : Fin K → ℝ) :
    let a := priorityChoice S hS N u
    a ∈ S ∧ (∀ k ∈ S, extendedIndex N u k ≤ extendedIndex N u a) ∧
      (∀ k ∈ S, extendedIndex N u k = extendedIndex N u a → a ≤ k) := by
  classical
  dsimp only
  unfold priorityChoice
  split
  · rename_i h
    have ha := mem_filter.mp ((S.filter (fun k => N k = 0)).min'_mem h)
    refine ⟨ha.1, ?_, ?_⟩
    · intro k hk
      simp [extendedIndex, ha.2]
    · intro k hk he
      have hz : N k = 0 := by
        by_contra hn
        simp [extendedIndex, hn, ha.2] at he
      exact Finset.min'_le _ _ (mem_filter.mpr ⟨hk, hz⟩)
  · rename_i h
    have hn : ∀ k ∈ S, N k ≠ 0 := by
      intro k hk hz
      exact h ⟨k, mem_filter.mpr ⟨hk, hz⟩⟩
    have ha := topArg_mem u S hS
    refine ⟨ha, ?_, ?_⟩
    · intro k hk
      simpa [extendedIndex, hn k hk, hn _ ha] using topArg_max u S hS hk
    · intro k hk he
      have he' : u k = u (topArg u S hS) := by
        simpa [extendedIndex, hn k hk, hn _ ha] using he
      apply topArg_min u S hS hk
      have hm : topArg u S hS ∈ S.filter (fun k => u k = S.sup' hS u) :=
        Finset.min'_mem _ _
      exact he'.trans (mem_filter.mp hm).2

/-- Literally `min argmax` on `WithTop ℝ`, with zero observations assigned `+∞`. -/
theorem priorityChoice_eq_min_argmax (S : Finset (Fin K)) (hS : S.Nonempty)
    (N : Fin K → ℕ) (u : Fin K → ℝ) :
    priorityChoice S hS N u =
      (S.filter (fun k => extendedIndex N u k = S.sup' hS (extendedIndex N u))).min'
        (by obtain ⟨k, hk, he⟩ := Finset.exists_mem_eq_sup' hS (extendedIndex N u)
            exact ⟨k, mem_filter.mpr ⟨hk, he.symm⟩⟩) := by
  classical
  obtain ⟨ha, hmax, hmin⟩ := priorityChoice_spec S hS N u
  have he : extendedIndex N u (priorityChoice S hS N u) =
      S.sup' hS (extendedIndex N u) := by
    apply le_antisymm
    · exact Finset.le_sup' _ ha
    · exact Finset.sup'_le _ _ hmax
  apply le_antisymm
  · apply hmin
    · exact mem_of_mem_filter _ (Finset.min'_mem _ _)
    · rw [he]
      exact (mem_filter.mp (Finset.min'_mem
        (S.filter (fun k => extendedIndex N u k = S.sup' hS (extendedIndex N u))) _)).2
  · exact Finset.min'_le _ _ (mem_filter.mpr ⟨ha, he⟩)

 theorem cooperative_choose_eq_min_argmax {n : ℕ} (p : Execution.Params n K)
    {i : Fin n} (s : Execution.LocalState n K i) :
    s.choose p =
      (s.active.filter (fun k => extendedIndex s.N (s.index p) k =
        s.active.sup' s.active_nonempty (extendedIndex s.N (s.index p)))).min'
        (by obtain ⟨k, hk, he⟩ := Finset.exists_mem_eq_sup' s.active_nonempty
              (extendedIndex s.N (s.index p))
            exact ⟨k, mem_filter.mpr ⟨hk, he.symm⟩⟩) :=
  priorityChoice_eq_min_argmax s.active s.active_nonempty s.N (s.index p)

 theorem baseline_choose_eq_min_argmax {n : ℕ} (p : Execution.Params n K)
    {i : Fin n} (s : BaselineExecution.LocalState n K i) :
    s.choose p =
      (s.active.filter (fun k => extendedIndex s.N (s.index p) k =
        s.active.sup' s.active_nonempty (extendedIndex s.N (s.index p)))).min'
        (by obtain ⟨k, hk, he⟩ := Finset.exists_mem_eq_sup' s.active_nonempty
              (extendedIndex s.N (s.index p))
            exact ⟨k, mem_filter.mpr ⟨hk, he.symm⟩⟩) :=
  priorityChoice_eq_min_argmax s.active s.active_nonempty s.N (s.index p)
end AnvBandit.ExecutionUCB
