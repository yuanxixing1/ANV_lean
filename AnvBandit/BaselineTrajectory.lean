import AnvBandit.BaselineRegret
import AnvBandit.Statements

/-! Actual joint-trajectory pseudo-regret and its path-to-expectation conversion. -/
noncomputable section
open scoped BigOperators
open Finset MeasureTheory
namespace AnvBandit.BaselineTrajectory
open BaselineExecution BaselineLaw BaselineRegret
variable {n K : ℕ}

def pathActions (p : Params n K) (ω : Path n) : Fin n → Fin p.T → Fin K :=
  fun i t => I p (realTape (pathRewards ω)) (pathContacts p ω) t.val i

def oracle (M : DecayModel n K) (T : ℕ) (lam : Fin 2) : ℝ :=
  if lam = 0 then Vstar0 (T := T) M else Vstar1 (T := T) M

def jointValue (M : DecayModel n K) {T : ℕ} (lam : Fin 2)
    (u : Fin n → Fin T → Fin K) : ℝ := if lam = 0 then J0 M u else J1 M u

def pathReward (M : DecayModel n K) (p : Params n K) (lam : Fin 2) (ω : Path n) : ℝ :=
  jointValue M lam (pathActions p ω)

/-- Exactly the paper's Vstar minus actual expected trajectory value. -/
def teamRegret (M : DecayModel n K) (p : Params n K) 
    (lam : Fin 2) : ℝ := oracle M p.T lam - ∫ ω, pathReward M p lam ω ∂executionMeasure M p lam

theorem mean_range (M : DecayModel n K) (k : Fin K) (s : ℕ) :
    0 ≤ M.mean k s ∧ M.mean k s ≤ 1 := by
  unfold DecayModel.mean
  constructor
  · exact add_nonneg (M.b_pos k).le (M.f_nonneg k s)
  · have h := M.f_le_gap k s; linarith

theorem jointValue_bounds (M : DecayModel n K) {T : ℕ} (lam : Fin 2)
    (u : Fin n → Fin T → Fin K) : 0 ≤ jointValue M lam u ∧ jointValue M lam u ≤ (n : ℝ)*T := by
  unfold jointValue
  split <;> constructor
  · exact sum_nonneg (fun t _ => sum_nonneg (fun i _ => (mean_range M _ _).1))
  · calc J0 M u ≤ ∑ _t : Fin T, ∑ _i : Fin n, (1 : ℝ) := by
          apply sum_le_sum; intro t ht
          exact sum_le_sum (fun i _ => (mean_range M _ _).2)
        _ = (n : ℝ)*T := by simp; ring
  · exact sum_nonneg (fun t _ => sum_nonneg (fun i _ => (mean_range M _ _).1))
  · calc J1 M u ≤ ∑ _t : Fin T, ∑ _i : Fin n, (1 : ℝ) := by
          apply sum_le_sum; intro t ht
          exact sum_le_sum (fun i _ => (mean_range M _ _).2)
        _ = (n : ℝ)*T := by simp; ring

theorem jointValue_le_oracle (M : DecayModel n K) {T : ℕ} (lam : Fin 2)
    (u : Fin n → Fin T → Fin K) : jointValue M lam u ≤ oracle M T lam := by
  unfold jointValue oracle
  split <;> exact Finset.le_sup' _ (Finset.mem_univ u)

theorem oracle_le (M : DecayModel n K) (T : ℕ) (lam : Fin 2) : oracle M T lam ≤ (n : ℝ)*T := by
  unfold oracle
  split
  · apply Finset.sup'_le
    intro u hu
    simpa [jointValue] using (jointValue_bounds M 0 u).2
  · apply Finset.sup'_le
    intro u hu
    simpa [jointValue] using (jointValue_bounds M 1 u).2

theorem pathActions_measurable (p : Params n K) : Measurable (pathActions p) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro t
  exact (action_predictable p t.val i).mono ((executionFiltration n).le t.val) le_rfl

theorem pathReward_measurable (M : DecayModel n K) (p : Params n K) (lam : Fin 2) :
    Measurable (pathReward M p lam) :=
  (measurable_of_countable (jointValue M lam)).comp (pathActions_measurable p)

theorem pathReward_integrable (M : DecayModel n K) (p : Params n K)
     (lam : Fin 2) : Integrable (pathReward M p lam) (executionMeasure M p lam) := by
  apply Integrable.of_bound (pathReward_measurable M p lam).stronglyMeasurable.aestronglyMeasurable
    ((n : ℝ)*p.T)
  filter_upwards [] with ω
  change ‖jointValue M lam (pathActions p ω)‖ ≤ (n : ℝ)*p.T
  rw [Real.norm_eq_abs, abs_of_nonneg (jointValue_bounds M lam (pathActions p ω)).1]
  exact (jointValue_bounds M lam (pathActions p ω)).2

theorem teamRegret_integral (M : DecayModel n K) (p : Params n K) 
    (lam : Fin 2) : teamRegret M p lam =
      ∫ ω, oracle M p.T lam - pathReward M p lam ω ∂executionMeasure M p lam := by
  rw [integral_sub (integrable_const _) (pathReward_integrable M p lam)]
  simp [teamRegret]

theorem weighted_counts {T : ℕ} (u : Fin n → Fin T → Fin K) (c : Fin K → ℝ) :
    (∑ k, c k*(Mtot u k : ℝ)) = ∑ t, ∑ i, c (u i t) := by
  have hi (i : Fin n) : (∑ k, c k*(Ntot u i k : ℝ)) = ∑ t, c (u i t) := by
    simp only [Ntot, card_eq_sum_ones, sum_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero, mul_sum, mul_ite, mul_one, mul_zero]
    rw [sum_comm]
    simp
  calc
    (∑ k, c k*(Mtot u k : ℝ)) = ∑ i, ∑ k, c k*(Ntot u i k : ℝ) := by
      simp only [Mtot, Nat.cast_sum, mul_sum]
      exact sum_comm
    _ = ∑ i, ∑ t, c (u i t) := sum_congr rfl (fun i _ => hi i)
    _ = ∑ t, ∑ i, c (u i t) := sum_comm

theorem weighted_others_counts (M : DecayModel n K) {T : ℕ}
    (u : Fin n → Fin T → Fin K) (c : Fin K → ℝ) (hstar : c M.star = 0) :
    (∑ k ∈ M.others, c k*(Mtot u k : ℝ)) = ∑ t, ∑ i, c (u i t) := by
  have h := M.sum_erase_star (fun k => c k*(Mtot u k : ℝ))
  simp only [hstar, zero_mul, zero_add] at h
  rw [← h]
  exact weighted_counts u c

theorem trajectory_conversion (M : DecayModel n K) (p : Params n K) (lam : Fin 2)
    (ω : Path n) : oracle M p.T lam - pathReward M p lam ω ≤
      M.Gamma lam + pathCost p (M.rho p.T lam) ω := by
  have h : oracle M p.T lam - pathReward M p lam ω ≤ M.Gamma lam +
      ∑ k ∈ M.others, M.rho p.T lam k*(Mtot (pathActions p ω) k : ℝ) := by
    fin_cases lam
    · exact regret_conversion_lambda0 p.hT M (pathActions p ω)
    · exact regret_conversion_lambda1 p.hT M (pathActions p ω)
  rw [weighted_others_counts M _ _ (M.rho_star p.T lam)] at h
  simp only [pathActions] at h
  rw [Fin.sum_univ_eq_sum_range (fun t => ∑ i,
    M.rho p.T lam (I p (realTape (pathRewards ω)) (pathContacts p ω) t i)) p.T] at h
  exact h

theorem weight_le_sup (M : DecayModel n K) (c : Fin K → ℝ)
    (hc : ∀ k, 0 ≤ c k) (hstar : c M.star = 0) (k : Fin K) : c k ≤ M.supOthers c := by
  by_cases hk : k = M.star
  · rw [hk, hstar]
    obtain ⟨j, hj⟩ := M.others_nonempty
    exact (hc j).trans (M.le_supOthers hj)
  · exact M.le_supOthers (by simp [DecayModel.others, hk])

/-- A.5 connected to actual expected trajectory regret, with no free regret quantity. -/
theorem teamRegret_conversion (M : DecayModel n K) (p : Params n K) 
    (lam : Fin 2) : teamRegret M p lam ≤ M.Gamma lam + weightedLoss M p lam (M.rho p.T lam) := by
  let c := M.rho p.T lam
  have hci := pathCost_integrable M p lam c (M.supOthers c) (M.rho_nonneg p.T lam)
    (weight_le_sup M c (M.rho_nonneg p.T lam) (M.rho_star p.T lam))
  rw [teamRegret_integral]
  have hb := integral_mono_ae ((integrable_const _).sub (pathReward_integrable M p lam))
    ((integrable_const (M.Gamma lam)).add hci)
    (Filter.Eventually.of_forall (trajectory_conversion M p lam))
  change (∫ ω, oracle M p.T lam - pathReward M p lam ω ∂executionMeasure M p lam) ≤
    ∫ ω, M.Gamma lam + pathCost p c ω ∂executionMeasure M p lam at hb
  rw [integral_add (integrable_const (M.Gamma lam)) hci] at hb
  simpa [weightedLoss, c] using hb

theorem teamRegret_trivial (M : DecayModel n K) (p : Params n K) 
    (lam : Fin 2) : teamRegret M p lam ≤ (n : ℝ)*p.T := by
  have hJ : 0 ≤ ∫ ω, pathReward M p lam ω ∂executionMeasure M p lam :=
    integral_nonneg (fun ω => (jointValue_bounds M lam (pathActions p ω)).1)
  have hV := oracle_le M p.T lam
  unfold teamRegret
  linarith

theorem teamRegret_nonneg (M : DecayModel n K) (p : Params n K) 
    (lam : Fin 2) : 0 ≤ teamRegret M p lam := by
  rw [teamRegret_integral]
  exact integral_nonneg (fun ω => sub_nonneg.mpr (jointValue_le_oracle M lam (pathActions p ω)))

/-- C.5: actual no-communication full-K UCB regret with both original truncations. -/
theorem teamRegret_bound (M : DecayModel n K) (p : Params n K) (lam : Fin 2) :
    teamRegret M p lam ≤ Uind ((n : ℝ)*p.T) (M.Gamma lam)
      ((n : ℝ)*M.supOthers (M.rho p.T lam)*p.T) (M.Flam (M.rho p.T lam) p.L lam)
      (p.δ*((n : ℝ)*M.supOthers (M.rho p.T lam)*p.T)) := by
  apply le_min (teamRegret_trivial M p lam)
  have hconv := teamRegret_conversion M p lam
  have hbound := weightedLoss_bound M p lam (M.rho p.T lam)
    (M.supOthers (M.rho p.T lam)) (M.rho_nonneg p.T lam)
    (weight_le_sup M _ (M.rho_nonneg p.T lam) (M.rho_star p.T lam))
    (M.rho_star p.T lam)
  linarith

end AnvBandit.BaselineTrajectory

