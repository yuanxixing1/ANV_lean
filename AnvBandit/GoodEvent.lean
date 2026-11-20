import AnvBandit.Adaptive
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Finite, actually observed adaptive prefixes

`T` is a round horizon; `m` is a requested number of observations. They are
separate parameters. Means in this file are path-dependent. No event constrains
an unobserved prefix. The count-compensated exponential process uses the actual
number of included observations, rather than the number of rounds.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

noncomputable section
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Finset

namespace AnvBandit
namespace ObservedPrefix

variable {Ω : Type*}

/-- Number of selected rounds strictly before `T`. -/
def count (selected : ℕ → Ω → Bool) (T : ℕ) (ω : Ω) : ℕ :=
  ∑ t ∈ range T, if selected t ω then 1 else 0

/-- Select the current round exactly when it belongs to the first `m` observations. -/
def capped (selected : ℕ → Ω → Bool) (m t : ℕ) (ω : Ω) : Bool :=
  selected t ω && decide (count selected t ω < m)

@[simp] lemma count_zero (selected : ℕ → Ω → Bool) (ω : Ω) :
    count selected 0 ω = 0 := by simp [count]

lemma count_succ (selected : ℕ → Ω → Bool) (t : ℕ) (ω : Ω) :
    count selected (t + 1) ω = count selected t ω + if selected t ω then 1 else 0 := by
  simp only [count, sum_range_succ]

lemma count_le_horizon (selected : ℕ → Ω → Bool) (T : ℕ) (ω : Ω) :
    count selected T ω ≤ T := by
  induction T with
  | zero => simp
  | succ t ih =>
      rw [count_succ]
      split <;> omega

lemma count_mono (selected : ℕ → Ω → Bool) (ω : Ω) :
    Monotone (fun T => count selected T ω) := by
  apply monotone_nat_of_le_succ
  intro t
  rw [count_succ]
  omega

/-- Pathwise truncation identity, valid also for sparse and adaptive selections. -/
theorem count_capped (selected : ℕ → Ω → Bool) (m T : ℕ) (ω : Ω) :
    count (capped selected m) T ω = min (count selected T ω) m := by
  induction T with
  | zero => simp
  | succ t ih =>
      rw [count_succ, count_succ, ih]
      by_cases hs : selected t ω = true
      · by_cases hn : count selected t ω < m
        · simp [capped, hs, hn]
          omega
        · simp [capped, hs, hn]
          omega
      · have hf : selected t ω = false := Bool.eq_false_iff.mpr hs
        simp [capped, hf]

lemma count_capped_eq_of_observed (selected : ℕ → Ω → Bool) {m T : ℕ} {ω : Ω}
    (h : m ≤ count selected T ω) : count (capped selected m) T ω = m := by
  rw [count_capped, min_eq_right h]

lemma count_congr_prefix {selected selected' : ℕ → Ω → Bool} {T : ℕ} {ω : Ω}
    (h : ∀ t < T, selected t ω = selected' t ω) :
    count selected T ω = count selected' T ω := by
  apply sum_congr rfl
  intro t ht
  rw [h t (mem_range.mp ht)]

/-- Centered sum over the first `m` selected observations available by `T`.
The mean may depend on the entire realized past. -/
def centered (selected : ℕ → Ω → Bool) (X p : ℕ → Ω → ℝ)
    (m T : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ range T, if capped selected m t ω then X t ω - p t ω else 0

/-- Sum of the first `m` selected values available by the horizon. -/
def sampleSum (selected : ℕ → Ω → Bool) (X : ℕ → Ω → ℝ)
    (m T : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ range T, if capped selected m t ω then X t ω else 0

/-- Reindex a capped sum by the observation number, rather than the round number. -/
lemma sampleSum_rank (selected : ℕ → Ω → Bool) (g : ℕ → ℝ)
    (m T : ℕ) (ω : Ω) :
    sampleSum selected (fun t ω => g (count selected t ω)) m T ω =
      ∑ s ∈ range (min (count selected T ω) m), g s := by
  induction T with
  | zero => simp [sampleSum, count]
  | succ t ih =>
      change (∑ s ∈ range (t + 1),
        if capped selected m s ω then g (count selected s ω) else 0) = _
      rw [sum_range_succ]
      change sampleSum selected (fun s ω => g (count selected s ω)) m t ω + _ = _
      rw [ih, count_succ]
      by_cases hs : selected t ω = true
      · by_cases hn : count selected t ω < m
        · have hle : count selected t ω ≤ m := by omega
          have hle' : count selected t ω + 1 ≤ m := by omega
          simp [capped, hs, hn, min_eq_left hle, min_eq_left hle', sum_range_succ]
        · have hle : m ≤ count selected t ω := by omega
          have hle' : m ≤ count selected t ω + 1 := by omega
          simp [capped, hs, hn, min_eq_right hle, min_eq_right hle']
      · have hf : selected t ω = false := Bool.eq_false_iff.mpr hs
        simp [capped, hf]

lemma sampleSum_rank_of_observed (selected : ℕ → Ω → Bool) (g : ℕ → ℝ)
    {m T : ℕ} {ω : Ω} (hm : m ≤ count selected T ω) :
    sampleSum selected (fun t ω => g (count selected t ω)) m T ω = ∑ s ∈ range m, g s := by
  rw [sampleSum_rank, min_eq_right hm]

/-- Deterministic A.1 mean sandwich for actual observed prefixes. The local
condition is checked only at rounds where the arm was selected. -/
lemma observed_mean_bounds (selected : ℕ → Ω → Bool) (p : ℕ → Ω → ℝ)
    (b : ℝ) (f : ℕ → ℝ) {m T : ℕ} {ω : Ω}
    (hm1 : 1 ≤ m) (hmN : m ≤ count selected T ω)
    (hp : ∀ t < T, selected t ω = true →
      b ≤ p t ω ∧ p t ω ≤ b + f (count selected t ω + 1)) :
    b ≤ sampleSum selected p m T ω / m ∧
      sampleSum selected p m T ω / m ≤ b + psi f m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
  have hlo : (m : ℝ) * b ≤ sampleSum selected p m T ω := by
    calc
      (m : ℝ) * b = sampleSum selected (fun _ _ => b) m T ω := by
        simpa [sum_const, nsmul_eq_mul] using (sampleSum_rank_of_observed selected (fun _ => b) hmN).symm
      _ ≤ sampleSum selected p m T ω := by
        apply sum_le_sum
        intro t ht
        by_cases hd : capped selected m t ω = true
        · have hsel : selected t ω = true := (Bool.and_eq_true_iff.mp hd).1
          simpa [hd] using (hp t (mem_range.mp ht) hsel).1
        · simp [hd]
  have hup : sampleSum selected p m T ω ≤ (m : ℝ) * b + Phi f m := by
    calc
      sampleSum selected p m T ω ≤
          sampleSum selected (fun t ω => b + f (count selected t ω + 1)) m T ω := by
        apply sum_le_sum
        intro t ht
        by_cases hd : capped selected m t ω = true
        · have hsel : selected t ω = true := (Bool.and_eq_true_iff.mp hd).1
          simpa [hd] using (hp t (mem_range.mp ht) hsel).2
        · simp [hd]
      _ = ∑ s ∈ range m, (b + f (s + 1)) :=
        sampleSum_rank_of_observed selected (fun s => b + f (s+1)) hmN
      _ = (m : ℝ) * b + Phi f m := by simp [sum_add_distrib, Phi, nsmul_eq_mul]
  constructor
  · apply (le_div_iff₀ hmR).mpr
    simpa [mul_comm] using hlo
  · rw [psi, div_le_iff₀ hmR]
    have he : (b + Phi f m / m) * m = b * m + Phi f m := by
      field_simp <;> ring
    rw [he]
    simpa [mul_comm] using hup

lemma centered_eq_sampleSum_sub (selected : ℕ → Ω → Bool) (X p : ℕ → Ω → ℝ)
    (m T : ℕ) (ω : Ω) :
    centered selected X p m T ω = sampleSum selected X m T ω - sampleSum selected p m T ω := by
  rw [centered, sampleSum, sampleSum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro t ht
  split <;> simp_all

lemma centered_congr_prefix {selected selected' : ℕ → Ω → Bool}
    {X X' p p' : ℕ → Ω → ℝ} {m T : ℕ} {ω : Ω}
    (hs : ∀ t < T, selected t ω = selected' t ω)
    (hX : ∀ t < T, X t ω = X' t ω) (hp : ∀ t < T, p t ω = p' t ω) :
    centered selected X p m T ω = centered selected' X' p' m T ω := by
  apply sum_congr rfl
  intro t ht
  have htT := mem_range.mp ht
  have hc : count selected t ω = count selected' t ω :=
    count_congr_prefix (fun s hs' => hs s (hs'.trans htT))
  simp only [capped, hs t htT, hc, hX t htT, hp t htT]
  rfl

lemma centered_succ_of_observed (selected : ℕ → Ω → Bool) (X p : ℕ → Ω → ℝ)
    {m t : ℕ} {ω : Ω} (hm : m ≤ count selected t ω) :
    centered selected X p m (t + 1) ω = centered selected X p m t ω := by
  unfold centered
  rw [sum_range_succ]
  have hc : capped selected m t ω = false := by simp [capped, Nat.not_lt.mpr hm]
  simp [hc]

/-- Once `m` observations have occurred, later rounds cannot alter that prefix. -/
lemma centered_stable (selected : ℕ → Ω → Bool) (X p : ℕ → Ω → ℝ)
    {m v T : ℕ} {ω : Ω} (hvT : v ≤ T) (hm : m ≤ count selected v ω) :
    centered selected X p m T ω = centered selected X p m v ω := by
  induction T, hvT using Nat.le_induction with
  | base => rfl
  | succ t hvt ih =>
      rw [centered_succ_of_observed selected X p (hm.trans (count_mono selected ω hvt)), ih]

/-- The count-compensated exponential process. -/
def exponential (selected : ℕ → Ω → Bool) (X p : ℕ → Ω → ℝ)
    (m T : ℕ) (θ : ℝ) (ω : Ω) : ℝ :=
  Real.exp (θ * centered selected X p m T ω -
    θ ^ 2 * (count (capped selected m) T ω : ℝ) / 8)

@[simp] lemma exponential_zero (selected : ℕ → Ω → Bool) (X p : ℕ → Ω → ℝ)
    (m : ℕ) (θ : ℝ) (ω : Ω) : exponential selected X p m 0 θ ω = 1 := by
  simp [exponential, centered]

lemma exponential_pos (selected : ℕ → Ω → Bool) (X p : ℕ → Ω → ℝ)
    (m T : ℕ) (θ : ℝ) (ω : Ω) : 0 < exponential selected X p m T θ ω :=
  Real.exp_pos _

lemma exponential_succ (selected : ℕ → Ω → Bool) (X p : ℕ → Ω → ℝ)
    (m t : ℕ) (θ : ℝ) (ω : Ω) :
    exponential selected X p m (t + 1) θ ω =
      exponential selected X p m t θ ω *
        (if capped selected m t ω then
          Real.exp (θ * (X t ω - p t ω) - θ ^ 2 / 8) else 1) := by
  unfold exponential centered
  rw [sum_range_succ, count_succ]
  by_cases hd : capped selected m t ω = true
  · simp only [hd, Bool.true_eq, if_true, Nat.cast_add, Nat.cast_one]
    rw [← Real.exp_add]
    congr 1
    ring
  · simp [hd]

/-- On the observed upper-tail event the exponential process crosses the
sample-count threshold, even if the observations occurred far apart. -/
lemma upper_tail_exponential (selected : ℕ → Ω → Bool) (X p : ℕ → Ω → ℝ)
    {m T : ℕ} {x : ℝ} {ω : Ω} (hx : 0 ≤ x)
    (hm : m ≤ count selected T ω)
    (hz : (m : ℝ) * x ≤ centered selected X p m T ω) :
    Real.exp (2 * (m : ℝ) * x ^ 2) ≤ exponential selected X p m T (4 * x) ω := by
  unfold exponential
  rw [count_capped_eq_of_observed selected hm]
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_left hz (show 0 ≤ 4 * x by positivity)
  nlinarith

lemma lower_tail_exponential (selected : ℕ → Ω → Bool) (X p : ℕ → Ω → ℝ)
    {m T : ℕ} {x : ℝ} {ω : Ω} (hx : 0 ≤ x)
    (hm : m ≤ count selected T ω)
    (hz : (m : ℝ) * x ≤ -centered selected X p m T ω) :
    Real.exp (2 * (m : ℝ) * x ^ 2) ≤ exponential selected X p m T (-4 * x) ω := by
  unfold exponential
  rw [count_capped_eq_of_observed selected hm]
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_left hz (show 0 ≤ 4 * x by positivity)
  nlinarith

/-- The event contains only prefixes that actually occurred by `T`. -/
def good {n K : ℕ} (selected : Fin n → Fin K → ℕ → Ω → Bool)
    (X p : Fin n → Fin K → ℕ → Ω → ℝ) (T : ℕ) (L : ℝ) : Set Ω :=
  {ω | ∀ i k m, 1 ≤ m → m ≤ count (selected i k) T ω →
    |centered (selected i k) (X i k) (p i k) m T ω| ≤ (m : ℝ) * rdelta L m}

lemma good_prefix {n K : ℕ} (selected : Fin n → Fin K → ℕ → Ω → Bool)
    (X p : Fin n → Fin K → ℕ → Ω → ℝ) {v T : ℕ} {L : ℝ} {ω : Ω}
    (hvT : v ≤ T) (hg : ω ∈ good selected X p T L) : ω ∈ good selected X p v L := by
  intro i k m hm1 hmv
  have hmT := hmv.trans (count_mono (selected i k) ω hvT)
  have h := hg i k m hm1 hmT
  rwa [centered_stable (selected i k) (X i k) (p i k) hvT hmv] at h

lemma good_empirical_mean {n K : ℕ} (selected : Fin n → Fin K → ℕ → Ω → Bool)
    (X p : Fin n → Fin K → ℕ → Ω → ℝ) {T : ℕ} {L : ℝ} {ω : Ω}
    (hg : ω ∈ good selected X p T L) (i : Fin n) (k : Fin K) (m : ℕ)
    (hm1 : 1 ≤ m) (hmN : m ≤ count (selected i k) T ω) :
    |sampleSum (selected i k) (X i k) m T ω / m -
      sampleSum (selected i k) (p i k) m T ω / m| ≤ rdelta L m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
  rw [← sub_div, ← centered_eq_sampleSum_sub, abs_div, abs_of_pos hmR]
  apply (div_le_iff₀ hmR).mpr
  simpa [mul_comm] using hg i k m hm1 hmN

/-- Elementary sparse-prefix regression: observations in rounds 1 and 4, not rounds 0 and 1. -/
example : count (fun t (_ : Unit) => decide (t = 1 ∨ t = 4)) 5 () = 2 := by
  decide

example : count (capped (fun t (_ : Unit) => decide (t = 1 ∨ t = 4)) 2) 5 () = 2 := by
  rw [count_capped]
  decide

/-- Hoeffding's scalar Bernoulli inequality, derived from the bounded-variable
lemma rather than assumed as an exponential-moment hypothesis. -/
lemma bernoulli_hoeffding (p : unitInterval) (θ : ℝ) :
    (p : ℝ) * Real.exp (θ * (1 - p)) +
      (1 - p : ℝ) * Real.exp (θ * (0 - p)) ≤ Real.exp (θ ^ 2 / 8) := by
  let ν := bernoulliMeasure (1 : ℝ) 0 p
  have hb : ∀ᵐ x ∂ν, x ∈ Set.Icc (0 : ℝ) 1 := by
    rw [show ν = bernoulliMeasure (1 : ℝ) 0 p from rfl,
      bernoulliMeasure_def, ae_add_measure_iff]
    constructor
    · exact Measure.ae_smul_measure (by simp) _
    · exact Measure.ae_smul_measure (by simp) _
  have hmean : (∫ x, x ∂ν) = (p : ℝ) := by
    rw [show ν = bernoulliMeasure (1 : ℝ) 0 p from rfl, integral_bernoulliMeasure]
    simp
  have h := hasSubgaussianMGF_of_mem_Icc (μ := ν) (X := fun x : ℝ => x)
    measurable_id.aemeasurable hb
  have hm := h.mgf_le θ
  rw [mgf, hmean, show ν = bernoulliMeasure (1 : ℝ) 0 p from rfl,
    integral_bernoulliMeasure] at hm
  simp only [smul_eq_mul] at hm
  rw [sgparam01] at hm
  convert hm using 1
  congr 1
  ring

section ConditionalMean

variable [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : MeasurableSpace Ω} (hF : F ≤ mΩ)

include hF

/-- The weighted-mean identity follows from the original conditional mean law.
This is a conditional-expectation identity, not a concentration assumption. -/
lemma integral_predictable_mul_eq {X p w : Ω → ℝ}
    (hw : StronglyMeasurable[F] w) (hX : Integrable X μ)
    (hwX : Integrable (fun ω => w ω * X ω) μ)
    (hmean : μ[X | F] =ᵐ[μ] p) :
    (∫ ω, w ω * X ω ∂μ) = ∫ ω, w ω * p ω ∂μ := by
  calc
    (∫ ω, w ω * X ω ∂μ) = ∫ ω, (μ[(fun ω => w ω * X ω) | F]) ω ∂μ :=
      (integral_condExp hF).symm
    _ = ∫ ω, w ω * (μ[X | F]) ω ∂μ :=
      integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hw hwX hX)
    _ = ∫ ω, w ω * p ω ∂μ := by
      apply integral_congr_ae
      filter_upwards [hmean] with ω hω
      rw [hω]

/-- Affine conditional expectation under a Bernoulli conditional mean law.
Random coefficients are allowed, provided they are known before the reward.
Integrability assumptions are only the standard technical domain of this auxiliary identity. -/
lemma integral_bernoulli_transform {X p a b : Ω → ℝ}
    (hb : StronglyMeasurable[F] b) (hX : Integrable X μ)
    (ha : Integrable a μ) (hbX : Integrable (fun ω => b ω * X ω) μ)
    (hbp : Integrable (fun ω => b ω * p ω) μ)
    (hmean : μ[X | F] =ᵐ[μ] p) :
    (∫ ω, a ω + b ω * X ω ∂μ) = ∫ ω, a ω + b ω * p ω ∂μ := by
  rw [integral_add ha hbX, integral_add ha hbp,
    integral_predictable_mul_eq (mΩ := mΩ) hF hb hX hbX hmean]

/-- Conditional Hoeffding in weighted-integral form. The only stochastic input is
Bernoulli support and its original conditional mean; the exponential bound is proved.
The mean is a predictable random variable, not a deterministic sequence. -/
lemma integral_weighted_bernoulli_exp_le {X p w : Ω → ℝ}
    (hXm : StronglyMeasurable[mΩ] X) (hX01 : ∀ ω, X ω = 0 ∨ X ω = 1)
    (hpm : StronglyMeasurable[F] p) (hp01 : ∀ ω, p ω ∈ Set.Icc (0 : ℝ) 1)
    (hwm : StronglyMeasurable[F] w) (hwi : Integrable w μ)
    (hw0 : ∀ ω, 0 ≤ w ω) (hmean : μ[X | F] =ᵐ[μ] p) (θ : ℝ) :
    (∫ ω, w ω * Real.exp (θ * (X ω - p ω)) ∂μ) ≤
      Real.exp (θ ^ 2 / 8) * ∫ ω, w ω ∂μ := by
  let a : Ω → ℝ := fun ω => Real.exp (-θ * p ω)
  let b : Ω → ℝ := fun ω => a ω * (Real.exp θ - 1)
  have ham : StronglyMeasurable[F] a :=
    Real.continuous_exp.comp_stronglyMeasurable (hpm.const_mul (-θ))
  have hbm : StronglyMeasurable[F] b := ham.mul_const _
  have hab : ∀ ω, ‖a ω‖ ≤ Real.exp |θ| := by
    intro ω
    simp only [a, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have h0 := (hp01 ω).1
    have h1 := (hp01 ω).2
    rcases le_total 0 θ with ht | ht
    · nlinarith [abs_nonneg θ, mul_nonneg ht h0]
    · rw [abs_of_nonpos ht]
      nlinarith [mul_nonneg (neg_nonneg.mpr ht) (sub_nonneg.mpr h1)]
  have hxb : ∀ ω, ‖X ω‖ ≤ 1 := by
    intro ω
    rcases hX01 ω with h | h <;> simp [h]
  have hpb : ∀ ω, ‖p ω‖ ≤ 1 := by
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hp01 ω).1]
    exact (hp01 ω).2
  have hXi : Integrable X μ :=
    Integrable.of_bound hXm.aestronglyMeasurable 1 (Filter.Eventually.of_forall hxb)
  have hwai : Integrable (fun ω => w ω * a ω) μ :=
    hwi.mul_bdd (ham.mono hF).aestronglyMeasurable (Filter.Eventually.of_forall hab)
  have hwbi : Integrable (fun ω => w ω * b ω) μ := by
    simpa [b, mul_assoc] using hwai.mul_const (Real.exp θ - 1)
  have hwbXi : Integrable (fun ω => (w ω * b ω) * X ω) μ :=
    hwbi.mul_bdd hXm.aestronglyMeasurable (Filter.Eventually.of_forall hxb)
  have hwbpi : Integrable (fun ω => (w ω * b ω) * p ω) μ :=
    hwbi.mul_bdd (hpm.mono hF).aestronglyMeasurable (Filter.Eventually.of_forall hpb)
  have heq : ∀ ω, w ω * Real.exp (θ * (X ω - p ω)) =
      w ω * a ω + (w ω * b ω) * X ω := by
    intro ω
    rcases hX01 ω with hx | hx
    · simp [hx, a]
    · rw [hx]
      have he : Real.exp (θ * (1 - p ω)) = Real.exp (-θ * p ω) * Real.exp θ := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [he]
      dsimp [a, b]
      ring
  have hscalar : ∀ ω, a ω + b ω * p ω ≤ Real.exp (θ ^ 2 / 8) := by
    intro ω
    have h := bernoulli_hoeffding ⟨p ω, hp01 ω⟩ θ
    have he : Real.exp (θ * (1 - p ω)) = a ω * Real.exp θ := by
      dsimp [a]
      rw [← Real.exp_add]
      congr 1
      ring
    simp only [Subtype.coe_mk] at h
    rw [he] at h
    have he0 : Real.exp (θ * (0 - p ω)) = a ω := by
      dsimp [a]
      congr 1
      ring
    rw [he0] at h
    dsimp [b]
    nlinarith
  calc
    (∫ ω, w ω * Real.exp (θ * (X ω - p ω)) ∂μ) =
        ∫ ω, w ω * a ω + (w ω * b ω) * X ω ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall heq
    _ = ∫ ω, w ω * a ω + (w ω * b ω) * p ω ∂μ :=
      integral_bernoulli_transform (mΩ := mΩ) hF (hwm.mul hbm) hXi hwai hwbXi hwbpi hmean
    _ ≤ ∫ ω, w ω * Real.exp (θ ^ 2 / 8) ∂μ := by
      apply integral_mono (hwai.add hwbpi) (hwi.mul_const _)
      intro ω
      have h := mul_le_mul_of_nonneg_left (hscalar ω) (hw0 ω)
      change w ω * a ω + (w ω * b ω) * p ω ≤ w ω * Real.exp (θ ^ 2 / 8)
      nlinarith
    _ = Real.exp (θ ^ 2 / 8) * ∫ ω, w ω ∂μ := by
      rw [integral_mul_const, mul_comm]

end ConditionalMean

section ProcessMeasurability

variable [MeasurableSpace Ω] (F : Filtration ℕ ‹MeasurableSpace Ω›)
    (selected : ℕ → Ω → Bool)
    (hs : ∀ t, MeasurableSet[F t] {ω | selected t ω = true})

include hs

lemma count_measurable (T : ℕ) : @Measurable Ω ℕ (F T) _ (count selected T) := by
  unfold count
  apply Finset.measurable_fun_sum
  intro t ht
  exact Measurable.ite (F.mono (Nat.le_of_lt (mem_range.mp ht)) _ (hs t))
    measurable_const measurable_const

lemma capped_measurable (m t : ℕ) :
    MeasurableSet[F t] {ω | capped selected m t ω = true} := by
  have hn := count_measurable F selected hs t
  have hlt : MeasurableSet[F t] {ω | count selected t ω < m} :=
    measurableSet_lt hn measurable_const
  convert (hs t).inter hlt using 1
  ext ω
  simp only [capped, Set.mem_setOf_eq, Set.mem_inter_iff, Bool.and_eq_true, decide_eq_true_eq]

lemma centered_stronglyMeasurable (X p : ℕ → Ω → ℝ)
    (hX : ∀ t, StronglyMeasurable[F (t + 1)] (X t))
    (hp : ∀ t, StronglyMeasurable[F t] (p t)) (m T : ℕ) :
    StronglyMeasurable[F T] (centered selected X p m T) := by
  unfold centered
  apply Finset.stronglyMeasurable_fun_sum
  intro t ht
  have htT : t < T := mem_range.mp ht
  exact StronglyMeasurable.ite
    (F.mono (Nat.le_of_lt htT) _ (capped_measurable F selected hs m t))
    (((hX t).mono (F.mono (Nat.succ_le_of_lt htT))).sub
      ((hp t).mono (F.mono (Nat.le_of_lt htT)))) stronglyMeasurable_const

lemma exponential_stronglyMeasurable (X p : ℕ → Ω → ℝ)
    (hX : ∀ t, StronglyMeasurable[F (t + 1)] (X t))
    (hp : ∀ t, StronglyMeasurable[F t] (p t)) (m T : ℕ) (θ : ℝ) :
    StronglyMeasurable[F T] (exponential selected X p m T θ) := by
  have hc : StronglyMeasurable[F T]
      (fun ω => (count (capped selected m) T ω : ℝ)) := by
    have hn := count_measurable F (capped selected m)
      (capped_measurable F selected hs m) T
    exact ((measurable_of_countable (fun z : ℕ => (z : ℝ))).comp hn).stronglyMeasurable
  exact Real.continuous_exp.comp_stronglyMeasurable
    (((centered_stronglyMeasurable F selected hs X p hX hp m T).const_mul θ).sub
      (by simpa only [div_eq_mul_inv, one_div, one_mul] using (hc.const_mul (θ ^ 2)).mul_const (1 / 8)))

end ProcessMeasurability

/-- Finite centered prefixes are bounded independently of how selection depends on history. -/
lemma centered_abs_le_horizon (selected : ℕ → Ω → Bool) (X p : ℕ → Ω → ℝ)
    (hX : ∀ t ω, X t ω ∈ Set.Icc (0 : ℝ) 1)
    (hp : ∀ t ω, p t ω ∈ Set.Icc (0 : ℝ) 1) (m T : ℕ) (ω : Ω) :
    |centered selected X p m T ω| ≤ (T : ℝ) := by
  unfold centered
  calc
    |∑ t ∈ range T, if capped selected m t ω then X t ω - p t ω else 0| ≤
        ∑ t ∈ range T, |if capped selected m t ω then X t ω - p t ω else 0| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ range T, (1 : ℝ) := by
      apply sum_le_sum
      intro t ht
      split
      · apply abs_le.mpr
        constructor <;> linarith [(hX t ω).1, (hX t ω).2, (hp t ω).1, (hp t ω).2]
      · norm_num
    _ = (T : ℝ) := by simp

lemma exponential_le_bound (selected : ℕ → Ω → Bool) (X p : ℕ → Ω → ℝ)
    (hX : ∀ t ω, X t ω ∈ Set.Icc (0 : ℝ) 1)
    (hp : ∀ t ω, p t ω ∈ Set.Icc (0 : ℝ) 1) (m T : ℕ) (θ : ℝ) (ω : Ω) :
    exponential selected X p m T θ ω ≤ Real.exp (|θ| * T) := by
  apply Real.exp_le_exp.mpr
  have hz := centered_abs_le_horizon selected X p hX hp m T ω
  have hz' : θ * centered selected X p m T ω ≤ |θ| * T := by
    calc
      θ * centered selected X p m T ω ≤ |θ * centered selected X p m T ω| := le_abs_self _
      _ = |θ| * |centered selected X p m T ω| := abs_mul _ _
      _ ≤ |θ| * T := mul_le_mul_of_nonneg_left hz (abs_nonneg θ)
  have hc : 0 ≤ θ ^ 2 * (count (capped selected m) T ω : ℝ) / 8 := by positivity
  linarith

section ExponentialProcess

variable [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ ‹MeasurableSpace Ω›) (selected : ℕ → Ω → Bool)
    (hs : ∀ t, MeasurableSet[F t] {ω | selected t ω = true})
    (X p : ℕ → Ω → ℝ)
    (hXm : ∀ t, StronglyMeasurable[F (t + 1)] (X t))
    (hpm : ∀ t, StronglyMeasurable[F t] (p t))
    (hX01 : ∀ t ω, X t ω = 0 ∨ X t ω = 1)
    (hp01 : ∀ t ω, p t ω ∈ Set.Icc (0 : ℝ) 1)

include hX01 in
lemma reward_mem_Icc (t : ℕ) (ω : Ω) : X t ω ∈ Set.Icc (0 : ℝ) 1 := by
  rcases hX01 t ω with h | h <;> simp [h]

include hs hXm hpm hX01 hp01

lemma exponential_integrable (m T : ℕ) (θ : ℝ) :
    Integrable (exponential selected X p m T θ) μ := by
  apply Integrable.of_bound
    ((exponential_stronglyMeasurable F selected hs X p hXm hpm m T θ).mono
      (F.le T)).aestronglyMeasurable (Real.exp (|θ| * T))
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs, abs_of_pos (exponential_pos selected X p m T θ ω)]
  exact exponential_le_bound selected X p (reward_mem_Icc X hX01) hp01 m T θ ω

/-- Finite-step count-compensated exponential estimate, derived from the original
conditional reward mean and Bernoulli support. No concentration or MGF bound is an input. -/
theorem integral_exponential_le_one
    (hmean : ∀ t, μ[X t | F t] =ᵐ[μ] p t) (m T : ℕ) (θ : ℝ) :
    (∫ ω, exponential selected X p m T θ ω ∂μ) ≤ 1 := by
  induction T with
  | zero => simp
  | succ t ih =>
      let M := exponential selected X p m t θ
      let A : Set Ω := {ω | capped selected m t ω = true}
      let U : Ω → ℝ := A.indicator M
      let V : Ω → ℝ := fun ω => M ω - U ω
      let W : Ω → ℝ := fun ω => U ω * Real.exp (-θ ^ 2 / 8)
      have hA : MeasurableSet[F t] A := capped_measurable F selected hs m t
      have hMa : StronglyMeasurable[F t] M :=
        exponential_stronglyMeasurable F selected hs X p hXm hpm m t θ
      have hMi : Integrable M μ := exponential_integrable μ F selected hs X p hXm hpm hX01 hp01 m t θ
      have hUi : Integrable U μ := hMi.indicator (F.le t _ hA)
      have hVi : Integrable V μ := hMi.sub hUi
      have hWi : Integrable W μ := hUi.mul_const _
      have hWm : StronglyMeasurable[F t] W := (hMa.indicator hA).mul_const _
      have hW0 : ∀ ω, 0 ≤ W ω := by
        intro ω
        by_cases hω : ω ∈ A
        · simpa [W, U, hω] using
            mul_nonneg (le_of_lt (exponential_pos selected X p m t θ ω))
              (le_of_lt (Real.exp_pos (-θ ^ 2 / 8)))
        · simp [W, U, hω]
      have hstep : ∀ ω, exponential selected X p m (t + 1) θ ω =
          V ω + W ω * Real.exp (θ * (X t ω - p t ω)) := by
        intro ω
        rw [exponential_succ]
        dsimp [V, W, U, A, M]
        by_cases hd : capped selected m t ω = true
        · simp only [hd, Bool.true_eq, Set.mem_setOf_eq, Set.indicator_of_mem,
            if_true, sub_self, zero_add]
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
        · simp [hd]
      have hnexti := exponential_integrable μ F selected hs X p hXm hpm hX01 hp01 m (t+1) θ
      have hWei : Integrable (fun ω => W ω * Real.exp (θ * (X t ω - p t ω))) μ := by
        refine (hnexti.sub hVi).congr ?_
        apply Filter.Eventually.of_forall
        intro ω
        change exponential selected X p m (t+1) θ ω - V ω = _
        rw [hstep]
        ring
      have hwbound := integral_weighted_bernoulli_exp_le (F.le t)
        ((hXm t).mono (F.le (t+1))) (hX01 t) (hpm t) (hp01 t)
        hWm hWi hW0 (hmean t) θ
      have hcancel : Real.exp (θ ^ 2 / 8) * (∫ ω, W ω ∂μ) = ∫ ω, U ω ∂μ := by
        dsimp [W]
        rw [integral_mul_const]
        have hc : Real.exp (θ ^ 2 / 8) * Real.exp (-θ ^ 2 / 8) = 1 := by
          rw [← Real.exp_add]
          convert Real.exp_zero using 1 <;> ring
        calc
          Real.exp (θ ^ 2 / 8) * ((∫ ω, U ω ∂μ) * Real.exp (-θ ^ 2 / 8)) =
              (∫ ω, U ω ∂μ) * (Real.exp (θ ^ 2 / 8) * Real.exp (-θ ^ 2 / 8)) := by ring
          _ = ∫ ω, U ω ∂μ := by rw [hc, mul_one]
      calc
        (∫ ω, exponential selected X p m (t + 1) θ ω ∂μ) =
            (∫ ω, V ω ∂μ) + ∫ ω, W ω * Real.exp (θ * (X t ω - p t ω)) ∂μ := by
          rw [show exponential selected X p m (t + 1) θ =
            (fun ω => V ω + W ω * Real.exp (θ * (X t ω - p t ω))) from funext hstep,
            integral_add hVi hWei]
        _ ≤ (∫ ω, V ω ∂μ) + Real.exp (θ ^ 2 / 8) * ∫ ω, W ω ∂μ :=
          by linarith
        _ = ∫ ω, M ω ∂μ := by
          rw [hcancel]
          dsimp [V]
          rw [integral_sub hMi hUi]
          ring
        _ ≤ 1 := ih

omit hs hXm hpm hX01 hp01 in
/-- Exponential Markov inequality with its integrability requirements explicit. -/
lemma measure_le_exp_neg_of_integral_le_one {f : Ω → ℝ} {s : Set Ω} {a : ℝ}
    (hfi : Integrable f μ) (hf0 : ∀ ω, 0 ≤ f ω)
    (hEf : (∫ ω, f ω ∂μ) ≤ 1) (hsf : ∀ ω ∈ s, Real.exp a ≤ f ω) :
    μ.real s ≤ Real.exp (-a) := by
  have hsub : s ⊆ {ω | Real.exp a ≤ f ω} := hsf
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall hf0) hfi (Real.exp a)
  have hle : Real.exp a * μ.real s ≤ 1 :=
    (mul_le_mul_of_nonneg_left (measureReal_mono hsub) (Real.exp_nonneg a)).trans
      (hm.trans hEf)
  have hdiv : μ.real s ≤ 1 / Real.exp a := by
    apply (le_div_iff₀ (Real.exp_pos a)).mpr
    simpa [mul_comm] using hle
  simpa [Real.exp_neg, one_div] using hdiv

/-- A.1 upper-tail bound with distinct round horizon and observation count. -/
theorem measure_observed_upper_tail
    (hmean : ∀ t, μ[X t | F t] =ᵐ[μ] p t) (m T : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    μ.real {ω | m ≤ count selected T ω ∧
      (m : ℝ) * x ≤ centered selected X p m T ω} ≤ Real.exp (-(2 * (m : ℝ) * x ^ 2)) := by
  apply measure_le_exp_neg_of_integral_le_one μ
    (exponential_integrable μ F selected hs X p hXm hpm hX01 hp01 m T (4*x))
    (fun ω => (exponential_pos selected X p m T (4*x) ω).le)
    (integral_exponential_le_one μ F selected hs X p hXm hpm hX01 hp01 hmean m T (4*x))
  intro ω hω
  exact upper_tail_exponential selected X p hx hω.1 hω.2

/-- A.1 lower-tail bound with distinct round horizon and observation count. -/
theorem measure_observed_lower_tail
    (hmean : ∀ t, μ[X t | F t] =ᵐ[μ] p t) (m T : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    μ.real {ω | m ≤ count selected T ω ∧
      (m : ℝ) * x ≤ -centered selected X p m T ω} ≤ Real.exp (-(2 * (m : ℝ) * x ^ 2)) := by
  apply measure_le_exp_neg_of_integral_le_one μ
    (exponential_integrable μ F selected hs X p hXm hpm hX01 hp01 m T (-4*x))
    (fun ω => (exponential_pos selected X p m T (-4*x) ω).le)
    (integral_exponential_le_one μ F selected hs X p hXm hpm hX01 hp01 hmean m T (-4*x))
  intro ω hω
  exact lower_tail_exponential selected X p hx hω.1 hω.2

/-- The sparse, adaptive, actually observed-prefix concentration inequality.
No independence of selected rewards, deterministic means, or MGF assumptions occur. -/
theorem measure_observed_abs_tail
    (hmean : ∀ t, μ[X t | F t] =ᵐ[μ] p t) (m T : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    μ.real {ω | m ≤ count selected T ω ∧
      (m : ℝ) * x ≤ |centered selected X p m T ω|} ≤
        2 * Real.exp (-(2 * (m : ℝ) * x ^ 2)) := by
  have hsub : {ω | m ≤ count selected T ω ∧
      (m : ℝ) * x ≤ |centered selected X p m T ω|} ⊆
      {ω | m ≤ count selected T ω ∧ (m : ℝ) * x ≤ centered selected X p m T ω} ∪
      {ω | m ≤ count selected T ω ∧ (m : ℝ) * x ≤ -centered selected X p m T ω} := by
    intro ω hω
    rcases le_total 0 (centered selected X p m T ω) with hz | hz
    · exact Or.inl ⟨hω.1, by simpa [abs_of_nonneg hz] using hω.2⟩
    · exact Or.inr ⟨hω.1, by simpa [abs_of_nonpos hz] using hω.2⟩
  calc
    _ ≤ μ.real ({ω | m ≤ count selected T ω ∧ (m : ℝ) * x ≤ centered selected X p m T ω} ∪
        {ω | m ≤ count selected T ω ∧ (m : ℝ) * x ≤ -centered selected X p m T ω}) :=
      measureReal_mono hsub
    _ ≤ μ.real {ω | m ≤ count selected T ω ∧ (m : ℝ) * x ≤ centered selected X p m T ω} +
        μ.real {ω | m ≤ count selected T ω ∧ (m : ℝ) * x ≤ -centered selected X p m T ω} :=
      measureReal_union_le _ _
    _ ≤ Real.exp (-(2 * (m : ℝ) * x ^ 2)) + Real.exp (-(2 * (m : ℝ) * x ^ 2)) :=
      add_le_add
        (measure_observed_upper_tail μ F selected hs X p hXm hpm hX01 hp01 hmean m T hx)
        (measure_observed_lower_tail μ F selected hs X p hXm hpm hX01 hp01 hmean m T hx)
    _ = _ := by ring

end ExponentialProcess

section UniformEvent

variable [MeasurableSpace Ω] {n K T : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ ‹MeasurableSpace Ω›)
    (selected : Fin n → Fin K → ℕ → Ω → Bool)
    (X p : Fin n → Fin K → ℕ → Ω → ℝ)

lemma good_measurable
    (hs : ∀ i k t, MeasurableSet[F t] {ω | selected i k t ω = true})
    (hXm : ∀ i k t, StronglyMeasurable[F (t + 1)] (X i k t))
    (hpm : ∀ i k t, StronglyMeasurable[F t] (p i k t)) (L : ℝ) :
    MeasurableSet[F T] (good selected X p T L) := by
  unfold good
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro k
  apply MeasurableSet.iInter
  intro m
  apply MeasurableSet.iInter
  intro hm
  apply (measurableSet_le measurable_const (count_measurable F (selected i k) (hs i k) T)).imp
  exact (continuous_abs.comp_stronglyMeasurable (centered_stronglyMeasurable F (selected i k) (hs i k) (X i k) (p i k)
      (hXm i k) (hpm i k) m T)).measurableSet_le stronglyMeasurable_const

/-- The finite uniform event only checks observed prefixes. Its probability bound
is obtained from the original conditional Bernoulli mean, not entered as a field. -/
theorem measure_good_compl_le (hn : 2 ≤ n) (hK : 2 ≤ K) (hT : 1 ≤ T)
    (hs : ∀ i k t, MeasurableSet[F t] {ω | selected i k t ω = true})
    (hXm : ∀ i k t, StronglyMeasurable[F (t + 1)] (X i k t))
    (hpm : ∀ i k t, StronglyMeasurable[F t] (p i k t))
    (hX01 : ∀ i k t ω, X i k t ω = 0 ∨ X i k t ω = 1)
    (hp01 : ∀ i k t ω, p i k t ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ i k t, μ[X i k t | F t] =ᵐ[μ] p i k t)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    μ.real (good selected X p T (Real.log (((2 * n * K * T : ℕ) : ℝ) / δ)))ᶜ ≤ δ := by
  classical
  let L := Real.log (((2 * n * K * T : ℕ) : ℝ) / δ)
  have hbig : (1 : ℝ) ≤ ((2 * n * K * T : ℕ) : ℝ) := by
    have hn0 : 0 < n := by omega
    have hK0 : 0 < K := by omega
    have hT0 : 0 < T := by omega
    have hnat : 1 ≤ 2 * n * K * T := by
      have hpos : 0 < 2 * n * K * T := by positivity
      omega
    exact_mod_cast hnat
  have hL0 : 0 ≤ L := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hδ).mpr
    linarith
  let S : Finset ((Fin n × Fin K) × ℕ) := univ ×ˢ Icc 1 T
  let bad : (Fin n × Fin K) × ℕ → Set Ω := fun z =>
    {ω | z.2 ≤ count (selected z.1.1 z.1.2) T ω ∧
      (z.2 : ℝ) * rdelta L z.2 ≤
        |centered (selected z.1.1 z.1.2) (X z.1.1 z.1.2) (p z.1.1 z.1.2) z.2 T ω|}
  have hsubset : (good selected X p T L)ᶜ ⊆ ⋃ z ∈ S, bad z := by
    intro ω hω
    change ¬ (∀ i k m, 1 ≤ m → m ≤ count (selected i k) T ω →
      |centered (selected i k) (X i k) (p i k) m T ω| ≤ (m : ℝ) * rdelta L m) at hω
    push_neg at hω
    obtain ⟨i, k, m, hm1, hmN, hbad⟩ := hω
    have hmT : m ≤ T := hmN.trans (count_le_horizon (selected i k) T ω)
    exact Set.mem_biUnion (show ((i,k),m) ∈ S by simp [S, hm1, hmT]) ⟨hmN, hbad.le⟩
  have hbound : ∀ z ∈ S, μ.real (bad z) ≤ 2 * Real.exp (-L) := by
    intro z hz
    have hm : 1 ≤ z.2 := (mem_Icc.mp (mem_product.mp hz).2).1
    have hmR : (0 : ℝ) < (z.2 : ℝ) := by exact_mod_cast hm
    have he : -(2 * (z.2 : ℝ) * (rdelta L z.2) ^ 2) = -L := by
      rw [rdelta, Real.sq_sqrt (by positivity : 0 ≤ L / (2 * (z.2 : ℝ)))]
      field_simp
      <;> ring
    have htail := measure_observed_abs_tail μ F (selected z.1.1 z.1.2)
      (hs z.1.1 z.1.2) (X z.1.1 z.1.2) (p z.1.1 z.1.2)
      (hXm z.1.1 z.1.2) (hpm z.1.1 z.1.2) (hX01 z.1.1 z.1.2)
      (hp01 z.1.1 z.1.2) (hmean z.1.1 z.1.2) z.2 T (rdelta_nonneg L z.2)
    simpa only [he] using htail
  calc
    μ.real (good selected X p T L)ᶜ ≤ μ.real (⋃ z ∈ S, bad z) := measureReal_mono hsubset (measure_ne_top _ _)
    _ ≤ ∑ z ∈ S, μ.real (bad z) := measureReal_biUnion_finset_le S bad
    _ ≤ ∑ _z ∈ S, 2 * Real.exp (-L) := sum_le_sum hbound
    _ = ((n * K * T : ℕ) : ℝ) * (2 * Real.exp (-L)) := by
      rw [sum_const, nsmul_eq_mul]
      congr 1
      simp [S, card_product]
    _ ≤ δ := union_bound_arith n K T δ L rfl hδ (by omega) (by omega) (by omega)

/-- Finite-horizon version: no measurability, reward draws, or conditional-law
assumptions are required for rounds `t ≥ T`. Zero extension is only a proof device. -/
theorem measure_good_compl_le_finite (hn : 2 ≤ n) (hK : 2 ≤ K) (hT : 1 ≤ T)
    (hs : ∀ i k t, t < T → MeasurableSet[F t] {ω | selected i k t ω = true})
    (hXm : ∀ i k t, t < T → StronglyMeasurable[F (t + 1)] (X i k t))
    (hpm : ∀ i k t, t < T → StronglyMeasurable[F t] (p i k t))
    (hX01 : ∀ i k t, t < T → ∀ ω, X i k t ω = 0 ∨ X i k t ω = 1)
    (hp01 : ∀ i k t, t < T → ∀ ω, p i k t ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ i k t, t < T → μ[X i k t | F t] =ᵐ[μ] p i k t)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    μ.real (good selected X p T (Real.log (((2 * n * K * T : ℕ) : ℝ) / δ)))ᶜ ≤ δ := by
  classical
  let s' := fun i k t ω => if t < T then selected i k t ω else false
  let X' := fun i k t ω => if t < T then X i k t ω else 0
  let p' := fun i k t ω => if t < T then p i k t ω else 0
  have hs' : ∀ i k t, MeasurableSet[F t] {ω | s' i k t ω = true} := by
    intro i k t
    by_cases ht : t < T
    · simpa [s', ht] using hs i k t ht
    · simp [s', ht]
  have hX' : ∀ i k t, StronglyMeasurable[F (t+1)] (X' i k t) := by
    intro i k t
    by_cases ht : t < T
    · simpa [X', ht] using hXm i k t ht
    · simpa [X', ht] using (stronglyMeasurable_const : StronglyMeasurable[F (t+1)] (fun _ : Ω => (0 : ℝ)))
  have hp' : ∀ i k t, StronglyMeasurable[F t] (p' i k t) := by
    intro i k t
    by_cases ht : t < T
    · simpa [p', ht] using hpm i k t ht
    · simpa [p', ht] using (stronglyMeasurable_const : StronglyMeasurable[F t] (fun _ : Ω => (0 : ℝ)))
  have hX01' : ∀ i k t ω, X' i k t ω = 0 ∨ X' i k t ω = 1 := by
    intro i k t ω
    by_cases ht : t < T
    · simpa [X', ht] using hX01 i k t ht ω
    · simp [X', ht]
  have hp01' : ∀ i k t ω, p' i k t ω ∈ Set.Icc (0 : ℝ) 1 := by
    intro i k t ω
    by_cases ht : t < T
    · simpa [p', ht] using hp01 i k t ht ω
    · simp [p', ht]
  have hmean' : ∀ i k t, μ[X' i k t | F t] =ᵐ[μ] p' i k t := by
    intro i k t
    by_cases ht : t < T
    · simpa [X', p', ht] using hmean i k t ht
    · simp [X', p', ht]
  have heq : ∀ L, good s' X' p' T L = good selected X p T L := by
    intro L
    ext ω
    have hc : ∀ i k, count (s' i k) T ω = count (selected i k) T ω := by
      intro i k
      exact count_congr_prefix (fun t ht => by simp [s', ht])
    have hz : ∀ i k m, centered (s' i k) (X' i k) (p' i k) m T ω =
        centered (selected i k) (X i k) (p i k) m T ω := by
      intro i k m
      exact centered_congr_prefix (fun t ht => by simp [s', ht])
        (fun t ht => by simp [X', ht]) (fun t ht => by simp [p', ht])
    simp only [good, Set.mem_setOf_eq, hc, hz]
  have hb := measure_good_compl_le μ F s' X' p' hn hK hT hs' hX' hp' hX01' hp01' hmean' δ hδ hδ1
  rwa [heq] at hb

end UniformEvent

end ObservedPrefix
end AnvBandit
