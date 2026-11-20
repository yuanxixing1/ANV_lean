import AnvBandit.BaselineLaw
import AnvBandit.GoodEvent

/-! Original-model finite good-path interface. Mean sandwiches and UCB/counting obligations
are derived here, not supplied as fields of the original stochastic model. -/
noncomputable section
open scoped BigOperators
open Finset
namespace AnvBandit.BaselineBounds
variable {n K : ℕ} {Ω : Type*}
open BaselineLaw

def selected (p : BaselineExecution.Params n K) (X : Ω → ℕ → Fin n → Bool)
    (J : Ω → ℕ → Fin n → Fin n) (i : Fin n) (k : Fin K) (t : ℕ) (ω : Ω) : Bool :=
  decide (BaselineExecution.I p (realTape (X ω)) (J ω) t i = k)

def reward (X : Ω → ℕ → Fin n → Bool) (i : Fin n) (_k : Fin K)
    (t : ℕ) (ω : Ω) : ℝ := realTape (X ω) t i

def mean (M : DecayModel n K) (p : BaselineExecution.Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n)
    (i : Fin n) (_k : Fin K) (t : ℕ) (ω : Ω) : ℝ :=
  actualMean M p lam (X ω) (J ω) t i

theorem count_eq_N (p : BaselineExecution.Params n K) (X : Ω → ℕ → Fin n → Bool)
    (J : Ω → ℕ → Fin n → Fin n) (i : Fin n) (k : Fin K) (t : ℕ)
    (ht : t ≤ p.T) (ω : Ω) :
    ObservedPrefix.count (selected p X J i k) t ω =
      BaselineExecution.N p (realTape (X ω)) (J ω) t i k := by
  rw [BaselineExecution.N_eq_sum p _ _ t ht]
  simp [ObservedPrefix.count, selected]

theorem sampleSum_reward (p : BaselineExecution.Params n K) (X : Ω → ℕ → Fin n → Bool)
    (J : Ω → ℕ → Fin n → Fin n) (i : Fin n) (k : Fin K) (m : ℕ) (ω : Ω) :
    ObservedPrefix.sampleSum (selected p X J i k) (reward X i k) m p.T ω =
      BaselineExecution.sampleSum p (realTape (X ω)) (J ω) i k m := by
  unfold ObservedPrefix.sampleSum BaselineExecution.sampleSum
  apply sum_congr rfl
  intro t ht
  rw [ObservedPrefix.capped, count_eq_N p X J i k t (le_of_lt (mem_range.mp ht))]
  simp [selected, reward]

/-- Only the genuinely observed finite concentration event remains as an intermediate
path condition. The mean sandwich follows from the original model and simultaneous counts. -/
def goodRunOn (M : DecayModel n K) (p : BaselineExecution.Params n K) (lam : Fin 2)
    (X : Ω → ℕ → Fin n → Bool) (J : Ω → ℕ → Fin n → Fin n) (ω : Ω)
    (hg : ω ∈ ObservedPrefix.good (selected p X J) (reward X) (mean M p lam X J) p.T p.L) :
    GoodRunOn M p.T :=
  BaselineExecution.goodRunOnOfBounds p M (realTape (X ω)) (J ω)
    (fun i k m => ObservedPrefix.sampleSum (selected p X J i k) (mean M p lam X J i k) m p.T ω)
    (by
      intro i k m hm hmN
      apply ObservedPrefix.observed_mean_bounds (selected p X J i k)
        (mean M p lam X J i k) (M.b k) (M.f k) hm
      · simpa [count_eq_N p X J i k p.T le_rfl] using hmN
      · intro t ht hs
        have hk : BaselineExecution.I p (realTape (X ω)) (J ω) t i = k := by
          simpa [selected] using hs
        have hlo := (actualMean_bounds M p lam (X ω) (J ω) t i).1
        have hup := actualMean_le_personal_envelope M p lam (X ω) (J ω) t i
        rw [hk] at hlo hup
        rw [count_eq_N p X J i k t ht.le]
        exact ⟨hlo, by simpa [mean, Nat.add_comm] using hup⟩)
    (by
      intro i k m hm hmN
      have h := ObservedPrefix.good_empirical_mean (selected p X J) (reward X)
        (mean M p lam X J) hg i k m hm
        (by simpa [count_eq_N p X J i k p.T le_rfl] using hmN)
      simpa [sampleSum_reward, BaselineExecution.empiricalPrefix] using h)


end AnvBandit.BaselineBounds
