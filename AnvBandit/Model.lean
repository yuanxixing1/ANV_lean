import AnvBandit.Prefix

/-!
# The decaying-bandit instance (Section 2) and derived constants

This file encodes the paper's model (Assumptions 2.1–2.2) as `DecayModel`, together with the
derived quantities used in Sections 3–4 and Appendix A:

* `gap` (`Δ_k = b_⋆ − b_k`),
* `Aplus` (`A_+`), `Db` (`D_b`), `Gamma` (`Γ_0, Γ_1`),
* `eps` (`ε_λ(T)`), `rho` (`ρ^{(λ)}_k(T)`).

It also proves finiteness/positivity of `D_b`, the deterministic part of Lemma A.1 (the prefix
bounds `b_k ≤ (1/m)∑ p ≤ b_k + ψ_k(m)`) and the tail bound (A.6).
-/

noncomputable section
open scoped BigOperators Topology
open Filter Finset

namespace AnvBandit

/-- Positive part `[x]_+ = max x 0`. -/
def posPart (x : ℝ) : ℝ := max x 0

lemma posPart_nonneg (x : ℝ) : 0 ≤ posPart x := le_max_right _ _
lemma posPart_eq_zero_of_nonpos {x : ℝ} (h : x ≤ 0) : posPart x = 0 := max_eq_right h
lemma posPart_eq_self_of_nonneg {x : ℝ} (h : 0 ≤ x) : posPart x = x := max_eq_left h

variable {n K : ℕ}

/-- A homogeneous decaying-bandit instance (Assumptions 2.1–2.2).

`b k` is the (unknown) positive base value `b_k`, `f k s` the additional value `f_k(s)` at the
`s`-th use, `star` the unique base-optimal arm `k⋆`. -/
structure DecayModel (n K : ℕ) where
  b : Fin K → ℝ
  f : Fin K → ℕ → ℝ
  star : Fin K
  b_pos : ∀ k, 0 < b k
  b_le_one : ∀ k, b k ≤ 1
  f_nonneg : ∀ k s, 0 ≤ f k s
  f_anti : ∀ k, Antitone (f k)
  f_tendsto : ∀ k, Tendsto (f k) atTop (𝓝 0)
  f_le_gap : ∀ k s, f k s ≤ 1 - b k
  b_le_star : ∀ k, b k ≤ b star
  star_unique : ∀ k, b k = b star → k = star
  two_le_n : 2 ≤ n
  two_le_K : 2 ≤ K

/-- Extend a curve specified on positive use counts by `f(0)=f(1)`.
No claim about the unused raw value `f 0` is required. -/
def extendPositiveCurve (f : ℕ → ℝ) (s : ℕ) : ℝ := f (max s 1)

lemma extendPositiveCurve_eq {f : ℕ → ℝ} {s : ℕ} (hs : 1 ≤ s) :
    extendPositiveCurve f s = f s := by simp [extendPositiveCurve, max_eq_left hs]

@[simp] lemma extendPositiveCurve_zero (f : ℕ → ℝ) :
    extendPositiveCurve f 0 = f 1 := by simp [extendPositiveCurve]

lemma extendPositiveCurve_nonneg {f : ℕ → ℝ}
    (hf : ∀ s, 1 ≤ s → 0 ≤ f s) (s : ℕ) : 0 ≤ extendPositiveCurve f s :=
  hf _ (le_max_right _ _)

lemma extendPositiveCurve_le {f : ℕ → ℝ} {a : ℝ}
    (hf : ∀ s, 1 ≤ s → f s ≤ a) (s : ℕ) : extendPositiveCurve f s ≤ a :=
  hf _ (le_max_right _ _)

lemma extendPositiveCurve_antitone {f : ℕ → ℝ}
    (hf : ∀ s t, 1 ≤ s → s ≤ t → f t ≤ f s) :
    Antitone (extendPositiveCurve f) := by
  intro s t hst
  exact hf _ _ (le_max_right _ _) (max_le_max_right 1 hst)

lemma extendPositiveCurve_tendsto {f : ℕ → ℝ}
    (hf : Tendsto f atTop (𝓝 0)) : Tendsto (extendPositiveCurve f) atTop (𝓝 0) := by
  apply hf.congr'
  filter_upwards [eventually_ge_atTop 1] with s hs
  exact (extendPositiveCurve_eq hs).symm

/-- Every model whose curve axioms only concern positive use counts yields the existing
natural-indexed model. The zero-index extension adds no mathematical regularity assumption. -/
def DecayModel.ofPositiveCurves
    (b : Fin K → ℝ) (f : Fin K → ℕ → ℝ) (star : Fin K)
    (b_pos : ∀ k, 0 < b k) (b_le_one : ∀ k, b k ≤ 1)
    (f_nonneg : ∀ k s, 1 ≤ s → 0 ≤ f k s)
    (f_anti : ∀ k s t, 1 ≤ s → s ≤ t → f k t ≤ f k s)
    (f_tendsto : ∀ k, Tendsto (f k) atTop (𝓝 0))
    (f_le_gap : ∀ k s, 1 ≤ s → f k s ≤ 1 - b k)
    (b_le_star : ∀ k, b k ≤ b star)
    (star_unique : ∀ k, b k = b star → k = star)
    (two_le_n : 2 ≤ n) (two_le_K : 2 ≤ K) : DecayModel n K where
  b := b
  f := fun k => extendPositiveCurve (f k)
  star := star
  b_pos := b_pos
  b_le_one := b_le_one
  f_nonneg := fun k => extendPositiveCurve_nonneg (f_nonneg k)
  f_anti := fun k => extendPositiveCurve_antitone (f_anti k)
  f_tendsto := fun k => extendPositiveCurve_tendsto (f_tendsto k)
  f_le_gap := fun k => extendPositiveCurve_le (f_le_gap k)
  b_le_star := b_le_star
  star_unique := star_unique
  two_le_n := two_le_n
  two_le_K := two_le_K

namespace DecayModel

variable (M : DecayModel n K)

/-- The suboptimal arms (all arms except the base-optimal one). -/
def others : Finset (Fin K) := univ.erase M.star

/-- `Δ_k = b_⋆ − b_k`. -/
def gap (k : Fin K) : ℝ := M.b M.star - M.b k

lemma gap_nonneg (k : Fin K) : 0 ≤ M.gap k := sub_nonneg.mpr (M.b_le_star k)

lemma gap_star : M.gap M.star = 0 := by simp [gap]

lemma gap_pos {k : Fin K} (hk : k ≠ M.star) : 0 < M.gap k := by
  have hle := M.b_le_star k
  have hne : M.b k ≠ M.b M.star := fun h => hk (M.star_unique k h)
  have hlt : M.b k < M.b M.star := lt_of_le_of_ne hle hne
  unfold gap; linarith

/-- `A_+ = f_⋆(1) + ∑_{k≠⋆} [f_k(1) − Δ_k]_+`. -/
def Aplus : ℝ := M.f M.star 1 + ∑ k ∈ M.others, posPart (M.f k 1 - M.gap k)

/-- One summand of `D_b`: `[f_k(s) − Δ_k]_+`. -/
def DbTerm (k : Fin K) (s : ℕ) : ℝ := posPart (M.f k (s + 1) - M.gap k)

/-- `D_b = ∑_{k≠⋆} ∑_{s≥1} [f_k(s) − Δ_k]_+`. -/
def Db : ℝ := ∑ k ∈ M.others, ∑' s, M.DbTerm k s

lemma DbTerm_nonneg (k s) : 0 ≤ M.DbTerm k s := posPart_nonneg _

/-- Each inner series of `D_b` is summable (uses `f_k(s) → 0` and `Δ_k > 0`). -/
lemma summable_DbTerm {k : Fin K} (hk : k ≠ M.star) : Summable (M.DbTerm k) := by
  have hg : 0 < M.gap k := M.gap_pos hk
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (M.f_tendsto k) (M.gap k) hg
  apply summable_of_ne_finset_zero (s := Finset.range N)
  intro s hs
  have hsN : N ≤ s := by simpa [Finset.mem_range, not_lt] using hs
  have hlt : M.f k (s + 1) < M.gap k := by
    have := hN (s + 1) (le_trans hsN (Nat.le_succ s))
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (M.f_nonneg k (s + 1))] at this
  simp only [DbTerm, posPart_eq_zero_of_nonpos (by linarith : M.f k (s + 1) - M.gap k ≤ 0)]

lemma Db_nonneg : 0 ≤ M.Db := by
  unfold Db
  exact Finset.sum_nonneg fun k hk => tsum_nonneg fun s => M.DbTerm_nonneg k s

/-- `Γ_0 = n D_b`, `Γ_1 = D_b + (n−1) A_+`, indexed by the fatigue mode `λ ∈ {0,1}`. -/
def Gamma : Fin 2 → ℝ
  | 0 => n * M.Db
  | 1 => M.Db + (n - 1) * M.Aplus

/-- `ε_λ(T) = ψ_{k⋆}(n^λ T)`. -/
def eps (T : ℕ) (lam : Fin 2) : ℝ := psi (M.f M.star) (n ^ lam.val * T)

/-- `ρ^{(λ)}_k(T) = Δ_k + ε_λ(T)` for `k ≠ ⋆`, and `0` for `k = ⋆`. -/
def rho (T : ℕ) (lam : Fin 2) (k : Fin K) : ℝ :=
  if k = M.star then 0 else M.gap k + M.eps T lam

lemma rho_star (T lam) : M.rho T lam M.star = 0 := by simp [rho]

lemma rho_nonneg (T lam) (k : Fin K) : 0 ≤ M.rho T lam k := by
  rw [rho]
  split
  · rfl
  · exact add_nonneg (M.gap_nonneg k) (psi_nonneg (fun s _ => M.f_nonneg M.star s) _)

/-- The conditional mean of the `s`-th personal pull of arm `k` always lies in `[b_k, b_k+f_k(s)]`
(derived in the paper from the state dynamics; the deterministic content of Lemma A.1). -/
def AdaptMeanInGap (p : Fin K → ℕ → ℝ) : Prop :=
  ∀ k s, 1 ≤ s → M.b k ≤ p k s ∧ p k s ≤ M.b k + M.f k s

/-- Lemma A.1, deterministic part: the empirical prefix average of the conditional means lies in
`[b_k, b_k + ψ_k(m)]`. -/
lemma prefix_bounds {p : Fin K → ℕ → ℝ} (hp : M.AdaptMeanInGap p) {k : Fin K} {m : ℕ}
    (hm : 1 ≤ m) :
    M.b k ≤ (∑ s ∈ Finset.range m, p k (s + 1)) / m ∧
      (∑ s ∈ Finset.range m, p k (s + 1)) / m ≤ M.b k + psi (M.f k) m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  constructor
  · rw [le_div_iff₀ hm0]
    calc M.b k * (m : ℝ) = ∑ _s ∈ Finset.range m, M.b k := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ ∑ s ∈ Finset.range m, p k (s + 1) :=
          Finset.sum_le_sum fun s _ => (hp k (s + 1) (by omega)).1
  · rw [div_le_iff₀ hm0]
    have hΦ : Phi (M.f k) m = psi (M.f k) m * m := by
      rw [psi, div_mul_cancel₀ _ hm0.ne']
    calc ∑ s ∈ Finset.range m, p k (s + 1)
        ≤ ∑ s ∈ Finset.range m, (M.b k + M.f k (s + 1)) :=
          Finset.sum_le_sum fun s _ => (hp k (s + 1) (by omega)).2
      _ = (m : ℝ) * M.b k + Phi (M.f k) m := by
          simp only [Phi, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul]
      _ = (M.b k + psi (M.f k) m) * m := by
          rw [hΦ, add_mul]; ring_nf

/-- Tail bound (A.6): `Φ_k(u) − Φ_k(m) ≤ (u − m) ψ_k(u)` for `0 ≤ m ≤ u`, `1 ≤ u`. -/
lemma Phi_tail_bound (k : Fin K) {m u : ℕ} (hmu : m ≤ u) (hu : 1 ≤ u) :
    Phi (M.f k) u - Phi (M.f k) m ≤ (u - m : ℕ) * psi (M.f k) u := by
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
  have hanti := M.f_anti k
  have hcast : ((u - m : ℕ) : ℝ) = (u : ℝ) - m := Nat.cast_sub hmu
  have hPhi_u : Phi (M.f k) u = u * psi (M.f k) u := by
    rw [psi, mul_div_cancel₀ _ hu0.ne']
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [Phi_zero, sub_zero, hcast, Nat.cast_zero, sub_zero, hPhi_u]
  · have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hpsi_mu : psi (M.f k) u ≤ psi (M.f k) m := psi_anti_le hanti hm hmu
    have hPhi_m : Phi (M.f k) m = (m : ℝ) * psi (M.f k) m := by
      rw [psi, mul_div_cancel₀ _ hm0.ne']
    have hle : (m : ℝ) * psi (M.f k) u ≤ Phi (M.f k) m := by
      rw [hPhi_m]; exact mul_le_mul_of_nonneg_left hpsi_mu (le_of_lt hm0)
    rw [hPhi_u, hcast, hPhi_m]
    nlinarith [hle]

/-- `a_k = f_k(1)`: the added value of the first use of arm `k`. -/
def ak (k : Fin K) : ℝ := M.f k 1

lemma ak_nonneg (k : Fin K) : 0 ≤ M.ak k := M.f_nonneg k 1

lemma ak_le_one_sub (k : Fin K) : M.ak k ≤ 1 - M.b k := M.f_le_gap k 1

/-- `A = ∑_k a_k`. -/
def A : ℝ := ∑ k, M.ak k

lemma A_nonneg : 0 ≤ M.A := Finset.sum_nonneg fun k _ => M.ak_nonneg k

/-- `D_k = ∑_{s≥1} [f_k(s) − Δ_k]_+`. -/
def Dk (k : Fin K) : ℝ := ∑' s, M.DbTerm k s

lemma Db_eq_sum_Dk : M.Db = ∑ k ∈ M.others, M.Dk k := rfl

/-- Marginal mean at effective usage `s`: `μ_k(s) = b_k + f_k(s)`. -/
def mean (k : Fin K) (s : ℕ) : ℝ := M.b k + M.f k s

lemma b_le_mean (k : Fin K) (s : ℕ) : M.b k ≤ M.mean k s :=
  le_add_of_nonneg_right (M.f_nonneg k s)

lemma mean_le (k : Fin K) (s : ℕ) : M.mean k s ≤ M.b k + M.f k s := le_refl _

lemma others_nonempty : M.others.Nonempty := by
  have hK := M.two_le_K
  have hcard : 1 < Fintype.card (Fin K) := by rw [Fintype.card_fin]; omega
  obtain ⟨k, hk⟩ := Fintype.exists_ne_of_one_lt_card hcard M.star
  exact ⟨k, Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩⟩

/-- `Δ_b = min_{k ≠ ⋆} Δ_k`. -/
def DeltaMin : ℝ := M.others.inf' M.others_nonempty M.gap

lemma DeltaMin_le {k : Fin K} (hk : k ∈ M.others) : M.DeltaMin ≤ M.gap k := by
  have h := Finset.inf'_le (s := M.others) (f := M.gap) hk
  rw [show (⟨k, hk⟩ : M.others.Nonempty) = M.others_nonempty from
        Subsingleton.elim _ _] at h
  exact h

lemma DeltaMin_pos : 0 < M.DeltaMin := by
  rw [DeltaMin, Finset.lt_inf'_iff]
  intro k hk
  exact M.gap_pos (Finset.mem_erase.mp hk).1

end DecayModel

end AnvBandit
