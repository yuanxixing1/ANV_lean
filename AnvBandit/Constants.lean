import AnvBandit.Serial
import AnvBandit.Schedule

/-!
# Appendix B/C constants

Constants defined in Appendices B and C, with exact learning budgets distinguished from
coarse upper bounds. These definitions alone do not instantiate an actual algorithm run.

The propagation moments `M_1, D_P, P_β(H), A_β(H,T), K_β(H)` require the contact-process
probability space and are defined in `AnvBandit/Propagation.lean`.
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section
open scoped BigOperators Topology
open Filter Finset

namespace AnvBandit

variable {n K : ℕ}

/-- Only the paper's original numerical parameter conditions; no derived estimate is a field. -/
structure LegalParameters (n K T h H : ℕ) (δ β : ℝ) : Prop where
  two_le_n : 2 ≤ n
  two_le_K : 2 ≤ K
  one_le_T : 1 ≤ T
  one_le_h : 1 ≤ h
  one_le_H : 1 ≤ H
  h_dvd_H : h ∣ H
  delta_pos : 0 < δ
  delta_lt_one : δ < 1
  beta_gt_one : 1 < β

lemma Ldelta_pos {n K T : ℕ} {δ : ℝ}
    (hn : 2 ≤ n) (hK : 2 ≤ K) (hT : 1 ≤ T) (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 < Ldelta n K T δ := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hKR : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hnk : (4 : ℝ) ≤ (n : ℝ) * K := by
    calc (4 : ℝ) = 2 * 2 := by norm_num
      _ ≤ (n : ℝ) * K := mul_le_mul hnR hKR (by norm_num) (by positivity)
  have hnkt : (4 : ℝ) ≤ (n : ℝ) * K * T := by
    calc (4 : ℝ) ≤ (n : ℝ) * K := hnk
      _ ≤ (n : ℝ) * K * T := by
        simpa using mul_le_mul_of_nonneg_left hTR (by positivity : (0 : ℝ) ≤ (n : ℝ) * K)
  apply Real.log_pos
  rw [lt_div_iff₀ hδ]
  nlinarith

lemma legal_Hxi {h : ℕ} {ξ L : ℝ} (hh : 1 ≤ h) (hξ : 0 < ξ) (hL : 0 < L) :
    1 ≤ Hxi h ξ L ∧ h ∣ Hxi h ξ L ∧
      ξ * L ≤ (Hxi h ξ L : ℝ) ∧ (Hxi h ξ L : ℝ) < ξ * L + h := by
  have hhp : 0 < h := by omega
  have hpos : 0 < (Hxi h ξ L : ℝ) := lt_of_lt_of_le (mul_pos hξ hL) (Hxi_ge h hhp ξ L)
  have hnat : 0 < Hxi h ξ L := by exact_mod_cast hpos
  exact ⟨hnat, dvd_mul_right h _, Hxi_bracket h hhp (le_of_lt (mul_pos hξ hL))⟩

/-- For nonnegative weights, budgets over sets of size at most `r` and exactly `r`
are equivalent whenever the ambient set has at least `r` elements. -/
lemma nonneg_subset_budget_iff_exact {α : Type*} [DecidableEq α]
    (S : Finset α) (r : ℕ) (hr : r ≤ S.card) (w : α → ℝ)
    (hw : ∀ a ∈ S, 0 ≤ w a) (B : ℝ) :
    (∀ F ⊆ S, F.card ≤ r → ∑ a ∈ F, w a ≤ B) ↔
      (∀ F ⊆ S, F.card = r → ∑ a ∈ F, w a ≤ B) := by
  constructor
  · intro h F hFS hcard
    exact h F hFS hcard.le
  · intro h F hFS hcard
    obtain ⟨G, hFG, hGS, hGcard⟩ := Finset.exists_subsuperset_card_eq hFS hcard hr
    exact le_trans
      (Finset.sum_le_sum_of_subset_of_nonneg hFG (fun a ha _ => hw a (hGS ha)))
      (h G hGS hGcard)

/-- `s_max = min{K, ⌈K/n⌉ + 2}` (Section 3.1). -/
def smax (n K : ℕ) : ℕ := min K (⌈(K : ℝ) / n⌉₊ + 2)

/-- `L_* = log(8nK)` (Appendix C.3). -/
def Lstar (n K : ℕ) : ℝ := Real.log (8 * n * K)

/-- `θ^N_k = 32/Δ_k² + 1/L_*` (equation (C.16)). -/
def thetaN (n K : ℕ) (Δ : ℝ) : ℝ := 32 / Δ ^ 2 + 1 / Lstar n K

/-- `κ = s_max − 1` (Lemma B.2). -/
def kappa (n K : ℕ) : ℕ := smax n K - 1

lemma kappa_le_pred (n K : ℕ) : kappa n K ≤ K - 1 := by
  exact Nat.sub_le_sub_right (min_le_left K _) 1

namespace DecayModel

variable (M : DecayModel n K)

lemma others_card : M.others.card = K - 1 := by
  simp [others]

lemma kappa_le_others_card : kappa n K ≤ M.others.card := by
  rw [M.others_card]
  exact kappa_le_pred n K

/-- Proof-free version of the threshold `m_k` (value `1` at the optimal arm). -/
def mkAll (L : ℝ) (k : Fin K) : ℕ :=
  if hk : k = M.star then 1 else M.mkThr L k hk

lemma mkAll_eq_mkThr {L : ℝ} {k : Fin K} (hk : k ≠ M.star) :
    M.mkAll L k = M.mkThr L k hk := by
  simp only [mkAll]; rw [dif_neg hk]

lemma one_le_mkAll (L : ℝ) (k : Fin K) : 1 ≤ M.mkAll L k := by
  rw [mkAll]
  split
  · exact le_refl 1
  · rename_i hk
    rw [mkThr]
    exact le_trans (M.m0_spec hk).1 (le_max_left _ _)

/-- Proof-free version of the statistical threshold `n_k` (value `1` at the optimal arm). -/
def nkAll (L : ℝ) (k : Fin K) : ℕ :=
  if _ : k = M.star then 1 else nk L (M.gap k)

/-- `max_{k ≠ ⋆}` of a real-valued functional. -/
def supOthers (f : Fin K → ℝ) : ℝ := M.others.sup' M.others_nonempty f

lemma le_supOthers {f : Fin K → ℝ} {k : Fin K} (hk : k ∈ M.others) :
    f k ≤ M.supOthers f := by
  have h := Finset.le_sup' (s := M.others) (f := f) hk
  rwa [show (⟨k, hk⟩ : M.others.Nonempty) = M.others_nonempty from
        Subsingleton.elim _ _] at h

lemma supOthers_le {f : Fin K → ℝ} {a : ℝ} (h : ∀ k ∈ M.others, f k ≤ a) :
    M.supOthers f ≤ a :=
  Finset.sup'_le M.others_nonempty f h


/-- `m_max = max_{k≠⋆} m_k`. -/
def mMax (L : ℝ) : ℕ := M.others.sup' M.others_nonempty (fun k => M.mkAll L k)

lemma mkAll_le_mMax {L : ℝ} {k : Fin K} (hk : k ∈ M.others) :
    M.mkAll L k ≤ M.mMax L := by
  have h := Finset.le_sup' (s := M.others) (f := fun k => M.mkAll L k) hk
  rwa [show (⟨k, hk⟩ : M.others.Nonempty) = M.others_nonempty from
        Subsingleton.elim _ _] at h

lemma mkAll_cast_le_mMax {L : ℝ} {k : Fin K} (hk : k ∈ M.others) :
    (M.mkAll L k : ℝ) ≤ (M.mMax L : ℝ) := by
  exact_mod_cast M.mkAll_le_mMax hk

/-- Exact paper budget: the maximum sum over exactly `κ` distinct suboptimal arms. -/
def HKappa (L : ℝ) : ℕ :=
  (M.others.powersetCard (kappa n K)).sup'
    (Finset.powersetCard_nonempty_of_le M.kappa_le_others_card)
    (fun F => ∑ k ∈ F, M.mkAll L k)

/-- A coarse upper bound, not the definition of the paper's exact budget. -/
def HKappaUpper (L : ℝ) : ℕ := kappa n K * M.mMax L

lemma hkappa_exact_le_coarse (L : ℝ) : M.HKappa L ≤ M.HKappaUpper L := by
  apply Finset.sup'_le
  intro F hF
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hF
  calc ∑ k ∈ F, M.mkAll L k ≤ ∑ _k ∈ F, M.mMax L :=
        Finset.sum_le_sum fun k hk => M.mkAll_le_mMax (hsub hk)
    _ = M.HKappaUpper L := by simp [HKappaUpper, hcard]

/-- Subsets of size at most `κ` obey the exact budget: enlarge the set, not its weights. -/
lemma sum_mk_le_hkappa {L : ℝ} {F : Finset (Fin K)}
    (hsub : F ⊆ M.others) (hcard : F.card ≤ kappa n K) :
    ∑ k ∈ F, M.mkAll L k ≤ M.HKappa L := by
  obtain ⟨G, hFG, hGsub, hGcard⟩ :=
    Finset.exists_subsuperset_card_eq hsub hcard M.kappa_le_others_card
  have hGmem : G ∈ M.others.powersetCard (kappa n K) :=
    Finset.mem_powersetCard.mpr ⟨hGsub, hGcard⟩
  calc ∑ k ∈ F, M.mkAll L k ≤ ∑ k ∈ G, M.mkAll L k :=
        Finset.sum_le_sum_of_subset hFG
    _ ≤ M.HKappa L := Finset.le_sup' (fun F => ∑ k ∈ F, M.mkAll L k) hGmem

/-- `B = H_κ + m_max` (equation (B.1)). -/
def Bschedule (L : ℝ) : ℕ := M.HKappa L + M.mMax L

lemma Bschedule_le_coarse (L : ℝ) :
    M.Bschedule L ≤ (kappa n K + 1) * M.mMax L := by
  calc M.Bschedule L ≤ kappa n K * M.mMax L + M.mMax L :=
        Nat.add_le_add_right (M.hkappa_exact_le_coarse L) _
    _ = (kappa n K + 1) * M.mMax L := by ring

/-- `θ^M_k = max{m^0_k/L_*, θ^N_k}` (equation (C.16)). -/
def thetaM (k : Fin K) : ℝ :=
  if hk : k = M.star then 1
  else max ((M.m0 k hk : ℝ) / Lstar n K) (thetaN n K (M.gap k))

/-- `B_coef = (κ+1) max_k θ^M_k` (equation (C.17), relevant order). -/
def Bcoef : ℝ := (kappa n K + 1 : ℝ) * M.supOthers (fun k => M.thetaM k)

/-- `r = ⌈((B_coef/ξ + 2)/β)^{1/(β-1)}⌉` (equation (C.17)). -/
def rcoef (ξ β : ℝ) : ℕ := ⌈((M.Bcoef / ξ + 2) / β) ^ (1 / (β - 1))⌉₊

/-- `A_{β,ξ} = 1 + 2^{β-1}[r^β + e Γ(β+1) ((n−1)/ε_P)^β]` (equation (C.18)). -/
def Abetaxi (ξ β εP : ℝ) : ℝ :=
  1 + 2 ^ (β - 1) * ((M.rcoef ξ β : ℝ) ^ β + Real.exp 1 * Real.Gamma (β + 1) *
    ((n - 1 : ℝ) / εP) ^ β)

/-- `ρ^{(λ)}_k = Δ_k + ψ_{k⋆}(n^λ)` for `k ≠ ⋆`, and `0` at `⋆` (equation (C.19)). -/
def rhoConst (lam : Fin 2) (k : Fin K) : ℝ :=
  if k = M.star then 0 else M.gap k + psi (M.f M.star) (n ^ lam.val)

/-- `ρ^{(λ)}_max = max_{k≠⋆} ρ^{(λ)}_k` (equation (C.19)). -/
def rhoMax (lam : Fin 2) : ℝ := M.supOthers (fun k => M.rhoConst lam k)

/-- `θ^{(λ)}_k` with `θ^{(0)} = θ^M_k`, `θ^{(1)} = θ^N_k` (equation (C.19)). -/
def thetaLam (lam : Fin 2) (k : Fin K) : ℝ :=
  if lam = 0 then M.thetaM k else thetaN n K (M.gap k)

/-- `w_k(c) = c_k m_k` (Appendix C.1). -/
def wk (c : Fin K → ℝ) (L : ℝ) (k : Fin K) : ℝ := c k * (M.mkAll L k : ℝ)

lemma wk_nonneg {c : Fin K → ℝ} (hc : ∀ k, 0 ≤ c k) (L : ℝ) (k : Fin K) :
    0 ≤ M.wk c L k := mul_nonneg (hc k) (Nat.cast_nonneg _)

lemma wk_star {c : Fin K → ℝ} (hstar : c M.star = 0) (L : ℝ) : M.wk c L M.star = 0 := by
  simp [wk, hstar]


/-- `w^N_k(c) = c_k n_k` (Appendix C.1). -/
def wkN (c : Fin K → ℝ) (L : ℝ) (k : Fin K) : ℝ := c k * (M.nkAll L k : ℝ)

/-- `w_max(c) = max_{k≠⋆} w_k(c)`. -/
def wmax (c : Fin K → ℝ) (L : ℝ) : ℝ := M.supOthers (M.wk c L)

/-- `w^N_max(c)`. -/
def wNmax (c : Fin K → ℝ) (L : ℝ) : ℝ := M.supOthers (M.wkN c L)

/-- `W(c) = ∑_{k≠⋆} w_k(c)`. -/
def Wsum (c : Fin K → ℝ) (L : ℝ) : ℝ := ∑ k ∈ M.others, M.wk c L k

/-- `W^N(c)`. -/
def WNsum (c : Fin K → ℝ) (L : ℝ) : ℝ := ∑ k ∈ M.others, M.wkN c L k

/-- `W_κ(c) = max_{F ⊆ K\{⋆}, |F| = κ} ∑_{k∈F} w_k(c)`. -/
def Wkappa (c : Fin K → ℝ) (L : ℝ) : ℝ :=
  if h : kappa n K ≤ M.others.card then
    (M.others.powersetCard (kappa n K)).sup' (Finset.powersetCard_nonempty_of_le h)
      (fun F => ∑ k ∈ F, M.wk c L k)
  else M.Wsum c L

/-- `W^N_κ(c)`. -/
def WNkappa (c : Fin K → ℝ) (L : ℝ) : ℝ :=
  if h : kappa n K ≤ M.others.card then
    (M.others.powersetCard (kappa n K)).sup' (Finset.powersetCard_nonempty_of_le h)
      (fun F => ∑ k ∈ F, M.wkN c L k)
  else M.WNsum c L

/-- `C(c) = min{n W_κ(c), W(c) + (n+1) w_max(c)}` (Appendix C.1). -/
def Ccap (c : Fin K → ℝ) (L : ℝ) : ℝ :=
  min (n * M.Wkappa c L) (M.Wsum c L + (n + 1) * M.wmax c L)

/-- `C^N(c)`. -/
def CNcap (c : Fin K → ℝ) (L : ℝ) : ℝ :=
  min (n * M.WNkappa c L) (M.WNsum c L + (n + 1) * M.wNmax c L)

/-- `D^{(1/2)}_k = ∑_{s≥1} [f_k(s) − Δ_k/2]_+` (equation (A.9)). -/
def Dhalf (k : Fin K) : ℝ := ∑' s, posPart (M.f k (s + 1) - M.gap k / 2)

/-- `A^{(1/2)}_k = [a_k − Δ_k/2]_+` (equation (A.9)). -/
def Ahalf (k : Fin K) : ℝ := posPart (M.f k 1 - M.gap k / 2)

/-- `Ξ_k = D^{(1/2)}_k + (n−1) A^{(1/2)}_k` (equation (A.9)). -/
def Xi (k : Fin K) : ℝ := M.Dhalf k + (n - 1 : ℕ) * M.Ahalf k

/-- `B_pub(c) = 4 ∑_{k≠⋆} (c_k/Δ_k) Ξ_k` (Appendix C.1). -/
def Bpub (c : Fin K → ℝ) : ℝ := 4 * ∑ k ∈ M.others, c k / M.gap k * M.Xi k

/-- `F_λ(c)`, weighted exploration budget while the active set contains `k⋆` (Appendix C.1). -/
def Flam (c : Fin K → ℝ) (L : ℝ) : Fin 2 → ℝ
  | 0 => n * M.Wsum c L
  | 1 => min (n * M.Wsum c L) (n * M.WNsum c L + M.Bpub c)

/-- `C_λ(c; d)`, terminal-set and elimination budget (Appendix C.1). -/
def Clam (c : Fin K → ℝ) (L : ℝ) (d : ℝ) : Fin 2 → ℝ
  | 0 => M.Ccap c L + d * M.wmax c L
  | 1 => min (M.Ccap c L + d * M.wmax c L) (M.CNcap c L + d * M.wNmax c L + M.Bpub c)

/-- `J_λ = min{nκ max_k(ρ^{(λ)}_k θ^{(λ)}_k), ∑_k ρ^{(λ)}_k θ^{(λ)}_k + (n+1) max_k(...)}`
(equation (C.20)). -/
def Jlam (lam : Fin 2) : ℝ :=
  min (n * (kappa n K : ℝ) * M.supOthers (fun k => M.rhoConst lam k * M.thetaLam lam k))
    (∑ k ∈ M.others, M.rhoConst lam k * M.thetaLam lam k
      + (n + 1) * M.supOthers (fun k => M.rhoConst lam k * M.thetaLam lam k))

/-- `D_λ`: `D_0 = 0`, `D_1 = 4 ∑_{k≠⋆} (ρ^{(1)}_k/Δ_k) Ξ_k` (equation (C.21)). -/
def Dlam (lam : Fin 2) : ℝ :=
  if lam = 0 then 0 else M.Bpub (fun k => M.rhoConst 1 k)

lemma Wsum_nonneg {c : Fin K → ℝ} (hc : ∀ k, 0 ≤ c k) (L : ℝ) : 0 ≤ M.Wsum c L :=
  Finset.sum_nonneg fun k _ => M.wk_nonneg hc L k

lemma wmax_nonneg {c : Fin K → ℝ} (hc : ∀ k, 0 ≤ c k) (L : ℝ) : 0 ≤ M.wmax c L := by
  obtain ⟨k, hk⟩ := M.others_nonempty
  exact le_trans (M.wk_nonneg hc L k) (M.le_supOthers hk)

lemma Wkappa_nonneg {c : Fin K → ℝ} (hc : ∀ k, 0 ≤ c k) (L : ℝ) : 0 ≤ M.Wkappa c L := by
  rw [Wkappa]; split
  · rename_i h
    obtain ⟨F, hF⟩ := Finset.powersetCard_nonempty_of_le h
    have hle := Finset.le_sup' (fun F => ∑ k ∈ F, M.wk c L k) hF
    have h0 : 0 ≤ ∑ k ∈ F, M.wk c L k := Finset.sum_nonneg fun k _ => M.wk_nonneg hc L k
    linarith
  · exact Finset.sum_nonneg fun k _ => M.wk_nonneg hc L k

end DecayModel

end AnvBandit
