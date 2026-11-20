import AnvBandit.Prob

/-!
# Round-indexed conditional sub-Gaussian helpers

These are conditional Azuma bounds for the first `m` **rounds**, not the first `m`
observations of an adaptively selected arm. Their sub-Gaussian hypotheses are explicit
auxiliary assumptions, not a formalization of the paper's original reward law.

The parameter `1/4` corresponds to the Hoeffding exponent coefficient `1/8` in
Mathlib's convention `exp(c * θ² / 2)`. The counted-observation argument belongs
in `GoodEvent.lean`; in particular, intersecting a round-indexed event with a
sampling event does not establish the sparse adaptive-prefix theorem.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

noncomputable section
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Finset

namespace AnvBandit

variable {Ω : Type*} [MeasurableSpace Ω]

section Neg
variable {m mΩ : MeasurableSpace Ω} {hm : m ≤ mΩ} [StandardBorelSpace Ω]
variable {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0}

/-- Conditional sub-Gaussianity is stable under negation. -/
lemma hasCondSubgaussianMGF_neg [IsFiniteMeasure μ]
    (h : HasCondSubgaussianMGF m hm X c μ) : HasCondSubgaussianMGF m hm (-X) c μ :=
  Kernel.HasSubgaussianMGF.neg h

end Neg

/-- **Round-indexed conditional Chernoff bound**, an auxiliary Azuma statement.  For a reward stream `X` and a selection process `D`, both strongly adapted to the
filtration `ℱ`, with `D_t` (`t`-th selection indicator) measurable at time `t − 1` and the centred
reward `D_t (X_t − μ_t)` conditionally sub-Gaussian with the conditional-Hoeffding parameter `1/4`,

  `P{ε ≤ ∑_{t<m} D_t (X_t − μ_t)} ≤ exp(−ε² / (2 · m · (1/4)))`. -/
theorem measure_adaptive_sum_ge_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace Ω] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (D X : ℕ → Ω → ℝ) (muc : ℕ → ℝ)
    (hDm : ∀ t, StronglyMeasurable[ℱ (t - 1)] (D t))
    (hXm : ∀ t, StronglyMeasurable[ℱ t] (X t))
    (h0 : HasSubgaussianMGF (fun ω => D 0 ω * (X 0 ω - muc 0)) (1/4 : ℝ≥0) μ)
    (hsub : ∀ t, HasCondSubgaussianMGF (ℱ (t - 1)) (ℱ.le (t - 1))
      (fun ω => D t ω * (X t ω - muc t)) (1/4 : ℝ≥0) μ)
    (m : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ t ∈ Finset.range m, D t ω * (X t ω - muc t)}
      ≤ Real.exp (- ε ^ 2 / (2 * ((m : ℝ) * (1/4)))) := by
  have hY : StronglyAdapted ℱ (fun t ω => D t ω * (X t ω - muc t)) := fun t =>
    ((hDm t).mono (ℱ.mono (Nat.sub_le t 1))).mul
      ((hXm t).sub stronglyMeasurable_const)
  have hsub' : ∀ i < m - 1, HasCondSubgaussianMGF (ℱ i) (ℱ.le i)
      (fun ω => D (i + 1) ω * (X (i + 1) ω - muc (i + 1))) ((fun _ => (1/4 : ℝ≥0)) (i + 1)) μ :=
    fun i _ => by simpa using hsub (i + 1)
  have hmain := ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF (μ := μ)
    (Y := fun t ω => D t ω * (X t ω - muc t)) (cY := fun _ => (1/4 : ℝ≥0)) hY h0 m hsub' hε
  refine le_trans hmain (le_of_eq ?_)
  congr 1
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- **Round-indexed two-sided conditional Chernoff bound**: for `x ≥ 0`, the adaptive
centred sum satisfies `P{m x ≤ |∑_{t<m} D_t (X_t − μ_t)|} ≤ 2 e^{−2 m x²}`. -/
theorem measure_adaptive_abs_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace Ω] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (D X : ℕ → Ω → ℝ) (muc : ℕ → ℝ)
    (hDm : ∀ t, StronglyMeasurable[ℱ (t - 1)] (D t))
    (hXm : ∀ t, StronglyMeasurable[ℱ t] (X t))
    (h0 : HasSubgaussianMGF (fun ω => D 0 ω * (X 0 ω - muc 0)) (1/4 : ℝ≥0) μ)
    (h0n : HasSubgaussianMGF (fun ω => -(D 0 ω * (X 0 ω - muc 0))) (1/4 : ℝ≥0) μ)
    (hsub : ∀ t, HasCondSubgaussianMGF (ℱ (t - 1)) (ℱ.le (t - 1))
      (fun ω => D t ω * (X t ω - muc t)) (1/4 : ℝ≥0) μ)
    (hsubn : ∀ t, HasCondSubgaussianMGF (ℱ (t - 1)) (ℱ.le (t - 1))
      (fun ω => -(D t ω * (X t ω - muc t))) (1/4 : ℝ≥0) μ)
    (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    μ.real {ω | (m : ℝ) * x ≤ |∑ t ∈ Finset.range m, D t ω * (X t ω - muc t)|}
      ≤ 2 * Real.exp (-(2 * ((m : ℝ) * x ^ 2))) := by
  set S : Ω → ℝ := fun ω => ∑ t ∈ Finset.range m, D t ω * (X t ω - muc t) with hS
  have hε : (0:ℝ) ≤ (m : ℝ) * x := mul_nonneg (Nat.cast_nonneg _) hx
  have hexp : - ((m : ℝ) * x) ^ 2 / (2 * ((m : ℝ) * (1/4))) = -(2 * ((m : ℝ) * x ^ 2)) := by
    rcases eq_or_ne (m : ℝ) 0 with hm0 | hm0
    · simp [hm0]
    · field_simp
      ring
  have hup : μ.real {ω | (m : ℝ) * x ≤ S ω} ≤ Real.exp (-(2 * ((m : ℝ) * x ^ 2))) :=
    le_trans (measure_adaptive_sum_ge_le μ ℱ D X muc hDm hXm h0 hsub m hε) (le_of_eq (by rw [hexp]))
  have hlow : μ.real {ω | (m : ℝ) * x ≤ -S ω} ≤ Real.exp (-(2 * ((m : ℝ) * x ^ 2))) := by
    have h := measure_adaptive_sum_ge_le μ ℱ (fun t ω => -D t ω) X muc
      (fun t => (hDm t).neg) hXm (by simpa using h0n) (fun t => by simpa using hsubn t) m hε
    have hSneg : ∀ ω, (∑ t ∈ Finset.range m, -D t ω * (X t ω - muc t)) = -S ω := by
      intro ω
      rw [hS, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun t _ => by ring)
    have hset : {ω | (m : ℝ) * x ≤ ∑ t ∈ Finset.range m, -D t ω * (X t ω - muc t)}
        = {ω | (m : ℝ) * x ≤ -S ω} := by
      ext ω0; simp only [Set.mem_setOf_eq]; rw [hSneg ω0]
    rw [hset] at h
    exact le_trans h (le_of_eq (by rw [hexp]))
  have hsub2 : {ω | (m : ℝ) * x ≤ |S ω|} ⊆ {ω | (m : ℝ) * x ≤ S ω} ∪ {ω | (m : ℝ) * x ≤ -S ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rcases le_total 0 (S ω) with h | h
    · exact Or.inl (by simp only [Set.mem_setOf_eq]; rw [abs_of_nonneg h] at hω; exact hω)
    · exact Or.inr (by simp only [Set.mem_setOf_eq]; rw [abs_of_nonpos h] at hω; exact hω)
  calc μ.real {ω | (m : ℝ) * x ≤ |S ω|}
      ≤ μ.real ({ω | (m : ℝ) * x ≤ S ω} ∪ {ω | (m : ℝ) * x ≤ -S ω}) :=
        measureReal_mono hsub2 (measure_ne_top μ _)
    _ ≤ μ.real {ω | (m : ℝ) * x ≤ S ω} + μ.real {ω | (m : ℝ) * x ≤ -S ω} :=
        measureReal_union_le _ _
    _ ≤ Real.exp (-(2 * ((m : ℝ) * x ^ 2))) + Real.exp (-(2 * ((m : ℝ) * x ^ 2))) :=
        add_le_add hup hlow
    _ ≤ 2 * Real.exp (-(2 * ((m : ℝ) * x ^ 2))) := by
        have hnn : (0:ℝ) ≤ (m : ℝ) * x ^ 2 := mul_nonneg (Nat.cast_nonneg m) (sq_nonneg x)
        have h4 : Real.exp (-(2 * ((m : ℝ) * x ^ 2))) ≤ Real.exp (-(2 * ((m : ℝ) * x ^ 2))) :=
          Real.exp_le_exp.mpr (by linarith)
        linarith [h4, Real.exp_pos (-(2 * ((m : ℝ) * x ^ 2)))]

/-- A restricted round-indexed event bound (not the sparse sampled-prefix theorem): on the
joint event `{∑_{t<m} D_t = m, m x ≤ |Z_T|}`, the adaptive bound still holds. -/
theorem measure_adaptive_abs_le_sampled (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace Ω] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (D X : ℕ → Ω → ℝ) (muc : ℕ → ℝ)
    (hDm : ∀ t, StronglyMeasurable[ℱ (t - 1)] (D t))
    (hXm : ∀ t, StronglyMeasurable[ℱ t] (X t))
    (h0 : HasSubgaussianMGF (fun ω => D 0 ω * (X 0 ω - muc 0)) (1/4 : ℝ≥0) μ)
    (h0n : HasSubgaussianMGF (fun ω => -(D 0 ω * (X 0 ω - muc 0))) (1/4 : ℝ≥0) μ)
    (hsub : ∀ t, HasCondSubgaussianMGF (ℱ (t - 1)) (ℱ.le (t - 1))
      (fun ω => D t ω * (X t ω - muc t)) (1/4 : ℝ≥0) μ)
    (hsubn : ∀ t, HasCondSubgaussianMGF (ℱ (t - 1)) (ℱ.le (t - 1))
      (fun ω => -(D t ω * (X t ω - muc t))) (1/4 : ℝ≥0) μ)
    (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    μ.real {ω | (∑ t ∈ Finset.range m, D t ω) = (m : ℝ) ∧
        (m : ℝ) * x ≤ |∑ t ∈ Finset.range m, D t ω * (X t ω - muc t)|}
      ≤ 2 * Real.exp (-(2 * ((m : ℝ) * x ^ 2))) := by
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _))
    (measure_adaptive_abs_le μ ℱ D X muc hDm hXm h0 h0n hsub hsubn m hx)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  exact hω.2

end AnvBandit
