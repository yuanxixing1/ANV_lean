import Mathlib.Probability.Moments.SubGaussian
import AnvBandit.Schedule

/-!
# The probabilistic layer: Lemma A.1's concentration event `E_δ`

The paper's `DecayModel` (`AnvBandit/Model.lean`) and the schedule (`AnvBandit/Schedule.lean`)
capture everything deterministic.  This file supplies the probabilistic input of Lemma A.1.

Each (node, arm) pair carries an independent `{0,1}`-valued (Bernoulli-type) reward stream with
prescribed conditional means `p_{i,k,s}`; this is the reward model of Assumption 2.3 together with
`b_k ≤ p_{i,k,s} ≤ b_k + f_k(s)` (the deterministic part of Lemma A.1, `AdaptMeanInGap`).

We prove the finite-union-bound concentration statement

  `μ.real {ω | ∃ i k m ≤ T, r_δ(m) ≤ |μ̂_{i,k}(m) − avg_{i,k}(m)|} ≤ δ`

with `L_δ = log(2 n K T / δ)`, matching the paper's `P(E_δ) ≥ 1 − δ` and the factor `2nKT`
inside `L_δ`.  The single-arm bound is Hoeffding's inequality for independent sub-Gaussian
variables (`ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun`), using
Hoeffding's lemma (`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`).
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

noncomputable section
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Finset

namespace AnvBandit

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Centered prefix deviation: `∑_{s<m} (X_s − p_s)`. -/
def dev (X : ℕ → Ω → ℝ) (p : ℕ → ℝ) (m : ℕ) (ω : Ω) : ℝ :=
  ∑ s ∈ Finset.range m, (X s ω - p s)

lemma dev_eq_diff (X : ℕ → Ω → ℝ) (p : ℕ → ℝ) (m : ℕ) (ω : Ω) :
    dev X p m ω = (∑ s ∈ Finset.range m, X s ω) - (∑ s ∈ Finset.range m, p s) := by
  simp only [dev, Finset.sum_sub_distrib]

/-- Hoeffding's lemma (`a ≤ X s ≤ b`, mean `p s`): `X s − p s` is sub-Gaussian with parameter
`((b−a)/2)²`, uniformly in the mean. -/
lemma subgaussian_centered {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (p : ℕ → ℝ) (a b : ℝ)
    (hmeas : ∀ s, AEMeasurable (X s) μ)
    (hbnd : ∀ s, ∀ᵐ ω ∂μ, X s ω ∈ Set.Icc a b)
    (hmean : ∀ s, μ[X s] = p s) (s : ℕ) :
    HasSubgaussianMGF (fun ω => X s ω - p s) ((‖b - a‖₊ / 2) ^ 2) μ := by
  have h := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := X s)
      (a := a) (b := b) (hmeas s) (hbnd s)
  refine h.congr ?_
  filter_upwards with ω
  rw [hmean s]

/-- Single-arm Hoeffding bound: for i.i.d.-free independent `[a,b]`-valued rewards with means `p`,
the centered prefix sum `dev` exceeds `ε` with probability at most `exp(−ε²/(2·m·((b−a)/2)²))`. -/
lemma hoeffding_dev {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (p : ℕ → ℝ) (a b : ℝ)
    (hmeas : ∀ s, AEMeasurable (X s) μ)
    (hbnd : ∀ s, ∀ᵐ ω ∂μ, X s ω ∈ Set.Icc a b)
    (hmean : ∀ s, μ[X s] = p s)
    (hindep : iIndepFun X μ)
    (m : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ dev X p m ω}
      ≤ Real.exp (- ε ^ 2 / (2 * ((m : ℝ) * (((‖b - a‖₊ / 2) ^ 2 : ℝ≥0) : ℝ)))) := by
  have hsub : ∀ s ∈ Finset.range m,
      HasSubgaussianMGF (fun ω => X s ω - p s) ((‖b - a‖₊ / 2) ^ 2) μ :=
    fun s _ => subgaussian_centered X p a b hmeas hbnd hmean s
  have hindep' : iIndepFun (fun s => fun ω => X s ω - p s) μ :=
    hindep.comp (fun i x => x - p i) (fun i => measurable_id.sub measurable_const)
  have hmain := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (μ := μ)
    (X := fun s => fun ω => X s ω - p s) hindep' hsub hε
  have hset : {ω | ε ≤ dev X p m ω}
      = {ω | ε ≤ ∑ s ∈ Finset.range m, (fun s => fun ω => X s ω - p s) s ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, dev]
  rw [hset]
  refine le_trans hmain (le_of_eq ?_)
  have hc : ((∑ s ∈ Finset.range m, ((‖b - a‖₊ / 2) ^ 2 : ℝ≥0) : ℝ≥0) : ℝ)
      = (m : ℝ) * (((‖b - a‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  rw [hc]

/-- The `[0,1]` specialization of the sub-Gaussian parameter is `1/4`. -/
lemma sgparam01 : (((‖(1:ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = 1/4 := by
  rw [sub_zero, nnnorm_one]; norm_num

/-- The `[-1,0]` specialization of the sub-Gaussian parameter is `1/4`. -/
lemma sgparam_neg : (((‖(0:ℝ) - (-1)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = 1/4 := by
  norm_num [nnnorm_one]

/-- At radius `r_δ(m)` the Hoeffding exponent collapses to `L`. -/
lemma bad_exp_arg (m : ℕ) (hm : 1 ≤ m) (L : ℝ) (hL0 : 0 ≤ L) :
    - ((m:ℝ) * rdelta L m)^2 / (2 * ((m:ℝ) * ((1:ℝ)/4))) = -L := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  rw [rdelta, mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ L / (2*m))]
  field_simp
  ring

/-- Two-sided single-arm bound at radius `r_δ(m)`: both tails together have probability at most
`2 exp(−L)` when `L/(2m)` is the squared radius. -/
lemma measure_bad_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (p : ℕ → ℝ)
    (hmeas : ∀ s, AEMeasurable (X s) μ)
    (hbnd : ∀ s, ∀ᵐ ω ∂μ, X s ω ∈ Set.Icc (0:ℝ) 1)
    (hmean : ∀ s, μ[X s] = p s)
    (hindep : iIndepFun X μ)
    (m : ℕ) (hm : 1 ≤ m) {L : ℝ} (hL0 : 0 ≤ L) :
    μ.real {ω | rdelta L m ≤ |dev X p m ω| / m} ≤ 2 * Real.exp (-L) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hrd : 0 ≤ rdelta L m := rdelta_nonneg L m
  have hε : 0 ≤ (m : ℝ) * rdelta L m := mul_nonneg (le_of_lt hmR) hrd
  set ε : ℝ := (m : ℝ) * rdelta L m with hεdef
  -- the target set equals `{|dev| ≥ ε}`
  have hset1 : {ω | rdelta L m ≤ |dev X p m ω| / m} = {ω | ε ≤ |dev X p m ω|} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [le_div_iff₀ hmR]
    constructor <;> intro h
    · rwa [mul_comm] at h
    · rwa [mul_comm]
  rw [hset1]
  -- split into two tails
  have hsub : {ω | ε ≤ |dev X p m ω|} ⊆
      {ω | ε ≤ dev X p m ω} ∪ {ω | ε ≤ -(dev X p m ω)} := by
    intro ω hω
    rw [Set.mem_setOf_eq] at hω
    rw [Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq]
    rcases le_total 0 (dev X p m ω) with h | h
    · left; rwa [abs_of_nonneg h] at hω
    · right; rwa [abs_of_nonpos h] at hω
  -- Hoeffding on `dev` (rewards in [0,1])
  have hupper : μ.real {ω | ε ≤ dev X p m ω} ≤ Real.exp (-L) := by
    have h := hoeffding_dev X p 0 1 hmeas hbnd hmean hindep m hε
    refine le_trans h (le_of_eq ?_)
    rw [sgparam01, hεdef]
    exact congrArg Real.exp (bad_exp_arg m hm L hL0)
  -- lower tail: apply the same to `-X` (rewards in [-1,0], means `-p`)
  have hlower : μ.real {ω | ε ≤ -(dev X p m ω)} ≤ Real.exp (-L) := by
    have hdev : ∀ ω, -(dev X p m ω) = dev (fun s ω' => -X s ω') (fun s => -p s) m ω := by
      intro ω
      rw [dev, dev, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro s _
      ring
    have hset : {ω | ε ≤ -(dev X p m ω)}
        = {ω | ε ≤ dev (fun s ω' => -X s ω') (fun s => -p s) m ω} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      rw [hdev ω]
    rw [hset]
    have hmeas' : ∀ s, AEMeasurable ((fun s ω' => -X s ω') s) μ :=
      fun s => (hmeas s).neg
    have hbnd' : ∀ s, ∀ᵐ ω ∂μ, (fun s ω' => -X s ω') s ω ∈ Set.Icc (-1:ℝ) 0 := by
      intro s
      filter_upwards [hbnd s] with ω hω
      exact ⟨by linarith [hω.2], by linarith [hω.1]⟩
    have hmean' : ∀ s, μ[(fun s ω' => -X s ω') s] = (fun s => -p s) s := by
      intro s
      simp only [integral_neg]
      rw [hmean s]
    have hindep' : iIndepFun (fun s ω' => -X s ω') μ :=
      hindep.comp (fun _ x => -x) (fun _ => measurable_neg)
    have h := hoeffding_dev (fun s ω' => -X s ω') (fun s => -p s) (-1) 0 hmeas' hbnd' hmean' hindep' m hε
    refine le_trans h (le_of_eq ?_)
    rw [sgparam_neg, hεdef]
    exact congrArg Real.exp (bad_exp_arg m hm L hL0)
  calc μ.real {ω | ε ≤ |dev X p m ω|}
      ≤ μ.real ({ω | ε ≤ dev X p m ω} ∪ {ω | ε ≤ -(dev X p m ω)}) :=
        measureReal_mono hsub
    _ ≤ μ.real {ω | ε ≤ dev X p m ω} + μ.real {ω | ε ≤ -(dev X p m ω)} :=
        measureReal_union_le _ _
    _ ≤ Real.exp (-L) + Real.exp (-L) := add_le_add hupper hlower
    _ = 2 * Real.exp (-L) := by ring

/-- Arithmetic of the union bound: `nKT · 2 exp(−L) ≤ δ` when `L = log(2nKT/δ)`. -/
lemma union_bound_arith (n K T : ℕ) (δ : ℝ) (L : ℝ)
    (hL : L = Real.log (((2 * n * K * T : ℕ) : ℝ) / δ)) (hδ : 0 < δ)
    (hn : 0 < n) (hK : 0 < K) (hT : 0 < T) :
    ((n * K * T : ℕ) : ℝ) * (2 * Real.exp (-L)) ≤ δ := by
  have hexp : Real.exp (-L) = δ / (((2 * n * K * T : ℕ) : ℝ)) := by
    rw [hL, Real.exp_neg, Real.exp_log (by positivity), inv_div]
  have hcast : (((2 * n * K * T : ℕ) : ℝ)) = 2 * ((n * K * T : ℕ) : ℝ) := by push_cast; ring
  have hne : ((n * K * T : ℕ) : ℝ) ≠ 0 := by
    have : 0 < n * K * T := by positivity
    exact_mod_cast this.ne'
  have heq : ((n * K * T : ℕ) : ℝ) * (2 * Real.exp (-L)) = δ := by
    rw [hexp, hcast]
    field_simp
  exact le_of_eq heq

/-- Lemma A.1, probabilistic part: on the reward model of Assumption 2.3, the concentration
event

  `E_δ = {ω | ∀ i k m ≤ T, |μ̂_{i,k}(m) − avg_{i,k}(m)| ≤ r_δ(m)}`

has failure probability at most `δ`, where `L_δ = log(2 n K T / δ)` and `r_δ(m) = √(L_δ/(2m))`.
This is the paper's `P(E_δ) ≥ 1 − δ`. -/
theorem concentration_event {n K T : ℕ} (hn : 2 ≤ n) (hK : 2 ≤ K) (hT : 1 ≤ T)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin n → Fin K → ℕ → Ω → ℝ) (p : Fin n → Fin K → ℕ → ℝ)
    (hmeas : ∀ i k s, AEMeasurable (X i k s) μ)
    (hbnd : ∀ i k s, ∀ᵐ ω ∂μ, X i k s ω ∈ Set.Icc (0:ℝ) 1)
    (hmean : ∀ i k s, μ[X i k s] = p i k s)
    (hindep : ∀ i k, iIndepFun (fun s => X i k s) μ)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    μ.real {ω | ∃ i k m, 1 ≤ m ∧ m ≤ T ∧
        rdelta (Real.log (((2 * n * K * T : ℕ) : ℝ) / δ)) m
          ≤ |dev (X i k) (p i k) m ω| / m} ≤ δ := by
  set L : ℝ := Real.log (((2 * n * K * T : ℕ) : ℝ) / δ) with hLdef
  have hbig : (1:ℝ) ≤ ((2 * n * K * T : ℕ) : ℝ) := by
    have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hK2 : (2:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK
    have hT1 : (1:ℝ) ≤ (T:ℝ) := by exact_mod_cast hT
    have h8 : (8:ℝ) ≤ (2 * n * K * T : ℕ) := by
      push_cast
      nlinarith [hn2, hK2, hT1,
        mul_nonneg (by linarith : (0:ℝ) ≤ (n:ℝ)) (by linarith : (0:ℝ) ≤ (K:ℝ)),
        mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ (n:ℝ)) (by linarith : (0:ℝ) ≤ (K:ℝ)))
          (by linarith : (0:ℝ) ≤ (T:ℝ))]
    linarith
  have hL0 : 0 ≤ L := by
    rw [hLdef]; apply Real.log_nonneg; rw [le_div_iff₀ hδ]; linarith
  set S : Finset ((Fin n × Fin K) × ℕ) :=
    (Finset.univ : Finset (Fin n × Fin K)) ×ˢ (Finset.Icc 1 T) with hSdef
  let bad : (Fin n × Fin K) × ℕ → Set Ω :=
    fun x => {ω | rdelta L x.2 ≤ |dev (X x.1.1 x.1.2) (p x.1.1 x.1.2) x.2 ω| / x.2}
  have hsub : {ω | ∃ i k m, 1 ≤ m ∧ m ≤ T ∧ rdelta L m ≤ |dev (X i k) (p i k) m ω| / m}
      ⊆ ⋃ x ∈ S, bad x := by
    intro ω hω
    rw [Set.mem_setOf_eq] at hω
    obtain ⟨i, k, m, hm1, hmT, hbad⟩ := hω
    have hmem : ((i, k), m) ∈ S := by
      rw [hSdef, Finset.mem_product]
      exact ⟨Finset.mem_univ _, Finset.mem_Icc.mpr ⟨hm1, hmT⟩⟩
    have hbad2 : ω ∈ bad ((i, k), m) := by
      simp only [bad, Set.mem_setOf_eq]; exact hbad
    exact Set.mem_biUnion hmem hbad2
  have hbound : μ.real (⋃ x ∈ S, bad x) ≤ δ := by
    refine le_trans (measureReal_biUnion_finset_le S bad) ?_
    have hstep : ∀ x ∈ S, μ.real (bad x) ≤ 2 * Real.exp (-L) := by
      intro x hx
      rw [hSdef, Finset.mem_product] at hx
      exact measure_bad_le (X x.1.1 x.1.2) (p x.1.1 x.1.2)
        (fun s => hmeas x.1.1 x.1.2 s) (fun s => hbnd x.1.1 x.1.2 s)
        (fun s => hmean x.1.1 x.1.2 s) (hindep x.1.1 x.1.2) x.2
        (Finset.mem_Icc.mp hx.2).1 hL0
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (S.card : ℝ) = ((n * K * T : ℕ) : ℝ) := by
      have hc : S.card = n * K * T := by rw [hSdef]; simp [Finset.card_product]
      rw [hc]
    rw [hcard]
    exact union_bound_arith n K T δ L hLdef hδ (by omega) (by omega) (by omega)
  exact le_trans (measureReal_mono hsub (measure_ne_top μ _)) hbound

end AnvBandit
