import AnvBandit.Propagation

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace AnvBandit

/-- Head/tail factorization of an infinite product over `ℕ`. -/
theorem infinitePiNat_map_headTail {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] :
    (Measure.infinitePi (fun _ : ℕ => μ)).map
        (fun ω : ℕ → α => (ω 0, fun k => ω (k + 1)))
      = μ.prod (Measure.infinitePi (fun _ : ℕ => μ)) := by
  have hshift : (Measure.infinitePi (fun _ : ℕ => μ)).map
      (fun ω : ℕ → α => fun k => ω (k + 1))
      = Measure.infinitePi (fun _ : ℕ => μ) :=
    Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => μ)
      (f := Nat.succ) Nat.succ_injective
  have hmeas0 : AEMeasurable (fun ω : ℕ → α => ω 0)
      (Measure.infinitePi (fun _ : ℕ => μ)) := (measurable_pi_apply 0).aemeasurable
  have hmeasT : AEMeasurable (fun ω : ℕ → α => fun k => ω (k + 1))
      (Measure.infinitePi (fun _ : ℕ => μ)) :=
    (measurable_pi_iff.mpr (fun k => measurable_pi_apply (k + 1))).aemeasurable
  have hindep : IndepFun (fun ω : ℕ → α => ω 0) (fun ω : ℕ → α => fun k => ω (k + 1))
      (Measure.infinitePi (fun _ : ℕ => μ)) := by
    rw [IndepFun_iff_Indep]
    have hii : iIndepFun (fun i (ω : ℕ → α) => ω i) (Measure.infinitePi (fun _ : ℕ => μ)) :=
      iIndepFun_infinitePi (P := fun _ : ℕ => μ) (X := fun _ (a : α) => a) (fun _ => measurable_id)
    have hi : iIndep (fun i => (inferInstance : MeasurableSpace α).comap (fun ω : ℕ → α => ω i))
        (Measure.infinitePi (fun _ : ℕ => μ)) :=
      hii.iIndep (m := fun _ => (inferInstance : MeasurableSpace α))
    have hd := indep_iSup_of_disjoint
      (m := fun i => (inferInstance : MeasurableSpace α).comap (fun ω : ℕ → α => ω i))
      (fun i => measurable_iff_comap_le.mp (measurable_pi_apply i)) hi
      (S := {0}) (T := Set.Ici 1)
      (by rw [Set.disjoint_left]; intro a ha; simp only [Set.mem_singleton_iff] at ha; subst ha; simp)
    have hS : (⨆ i ∈ ({0} : Set ℕ),
        (inferInstance : MeasurableSpace α).comap (fun ω : ℕ → α => ω i))
        = (inferInstance : MeasurableSpace α).comap (fun ω : ℕ → α => ω 0) := iSup_singleton
    have hT : (⨆ i ∈ Set.Ici (1 : ℕ),
        (inferInstance : MeasurableSpace α).comap (fun ω : ℕ → α => ω i))
        = (inferInstance : MeasurableSpace (ℕ → α)).comap (fun ω : ℕ → α => fun k => ω (k + 1)) := by
      rw [MeasurableSpace.comap_process_pi (fun (a : ℕ) (ω : ℕ → α) => ω (a + 1))]
      apply le_antisymm
      · refine iSup₂_le fun i hi => ?_
        simpa [Nat.sub_add_cancel hi] using
          le_iSup (f := fun k : ℕ => (inferInstance : MeasurableSpace α).comap
            (fun ω : ℕ → α => ω (k + 1))) (i - 1)
      · refine iSup_le fun k => ?_
        exact le_iSup₂ (f := fun i (_ : i ∈ Set.Ici (1:ℕ)) =>
          (inferInstance : MeasurableSpace α).comap (fun ω : ℕ → α => ω i)) (k + 1)
          (by show (1:ℕ) ≤ k + 1; omega)
    rw [hS, hT] at hd
    exact hd
  rw [hindep.map_prod_eq_prod_map_map hmeas0 hmeasT,
    Measure.infinitePi_map_eval (μ := fun _ : ℕ => μ) 0, hshift]

/-- The step process: i.i.d. contacts, one per propagation step. -/
noncomputable def stepMeasure {n : ℕ} (C : ContactMatrix n) : Measure (ℕ → Fin n → Fin n) :=
  Measure.infinitePi (fun _ : ℕ => stepDist C)

instance stepMeasure.instIsProbabilityMeasure {n : ℕ} (C : ContactMatrix n) :
    IsProbabilityMeasure (stepMeasure C) := by unfold stepMeasure; infer_instance

/-- Head/tail factorization for the step process. -/
theorem stepMeasure_headTail {n : ℕ} (C : ContactMatrix n) :
    (stepMeasure C).map (fun R : ℕ → Fin n → Fin n => (R 0, fun k => R (k + 1)))
      = (stepDist C).prod (stepMeasure C) :=
  infinitePiNat_map_headTail (stepDist C)

lemma measurable_unblock {n d : ℕ} (hd : 0 < d) :
    Measurable (unblock (n := n) hd) := by
  rw [measurable_pi_iff]
  intro t
  exact (measurable_pi_apply (⟨t % d, Nat.mod_lt t hd⟩ : Fin d)).comp
    (measurable_pi_apply (t / d))

/-- Preimage of a step-cylinder under `unblock`, as a block-cylinder. -/
lemma unblock_preimage {n d : ℕ} (hd : 0 < d) (s : Finset ℕ)
    (t : ℕ → Set (Fin n → Fin n)) :
    unblock (n := n) hd ⁻¹' Set.pi s t
      = Set.pi (s.image (fun i => i / d))
          (fun a => Set.pi ((s.filter (fun i => i / d = a)).image
            (fun i => (⟨i % d, Nat.mod_lt i hd⟩ : Fin d)))
            (fun b => t (a * d + b.val))) := by
  ext ω; constructor
  · intro hω a ha
    obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp ha
    rw [Set.mem_pi]
    intro b hb
    obtain ⟨i'', hi'', rfl⟩ := Finset.mem_image.mp hb
    rw [Finset.mem_filter] at hi''
    have hkey : (i' / d) * d + (⟨i'' % d, Nat.mod_lt i'' hd⟩ : Fin d).val = i'' := by
      rw [Fin.val_mk, ← hi''.2, Nat.mul_comm]; exact Nat.div_add_mod i'' d
    rw [hkey]
    have hunb : unblock (n := n) hd ω i'' = ω (i' / d) ⟨i'' % d, Nat.mod_lt i'' hd⟩ := by
      simp only [unblock, hi''.2]
    rw [← hunb]; exact hω i'' hi''.1
  · intro hω i hi
    have ha : i / d ∈ s.image (fun i => i / d) := Finset.mem_image.mpr ⟨i, hi, rfl⟩
    have hb : (⟨i % d, Nat.mod_lt i hd⟩ : Fin d)
        ∈ (s.filter (fun i' => i' / d = i / d)).image
            (fun i' => (⟨i' % d, Nat.mod_lt i' hd⟩ : Fin d)) :=
      Finset.mem_image.mpr ⟨i, by rw [Finset.mem_filter]; exact ⟨hi, rfl⟩, rfl⟩
    have hthis := (Set.mem_pi.mp (hω (i / d) ha)) (⟨i % d, Nat.mod_lt i hd⟩ : Fin d)
      (show (⟨i % d, Nat.mod_lt i hd⟩ : Fin d)
          ∈ (↑((s.filter (fun i' => i' / d = i / d)).image
              (fun i' => (⟨i' % d, Nat.mod_lt i' hd⟩ : Fin d))) : Set (Fin d)) from hb)
    have hkey : (i / d) * d + (⟨i % d, Nat.mod_lt i hd⟩ : Fin d).val = i := by
      rw [Fin.val_mk, Nat.mul_comm]; exact Nat.div_add_mod i d
    rw [hkey] at hthis
    change ω (i / d) ⟨i % d, Nat.mod_lt i hd⟩ ∈ t i
    exact hthis

/-- Evaluate the block measure on a block-cylinder. -/
lemma pi_stepDist_pi {n d : ℕ} (C : ContactMatrix n) (Ba : Finset (Fin d))
    (g : Fin d → Set (Fin n → Fin n)) :
    (Measure.pi (fun _ : Fin d => stepDist C)) (Set.pi Ba g)
      = ∏ b ∈ Ba, stepDist C (g b) := by
  have hEq : Set.pi Ba g = Set.pi (Set.univ : Set (Fin d))
      (fun b => if b ∈ (Ba : Set (Fin d)) then g b else Set.univ) := by
    ext w; rw [Set.mem_pi, Set.mem_pi]
    constructor
    · intro h b hb
      by_cases hc : b ∈ (Ba : Set (Fin d))
      · rw [if_pos hc]; exact h b hc
      · rw [if_neg hc]; exact Set.mem_univ _
    · intro h b hb
      have := h b (Set.mem_univ b)
      rwa [if_pos (show b ∈ (Ba : Set (Fin d)) from hb)] at this
  rw [hEq, Measure.pi_pi (μ := fun _ : Fin d => stepDist C)]
  have hcollapse : (∏ x : Fin d,
      stepDist C (if x ∈ (Ba : Set (Fin d)) then g x else Set.univ))
      = ∏ x ∈ Ba, stepDist C (g x) := by
    rw [show (∏ x : Fin d,
          stepDist C (if x ∈ (Ba : Set (Fin d)) then g x else Set.univ))
        = ∏ x ∈ Ba, stepDist C (if x ∈ (Ba : Set (Fin d)) then g x else Set.univ) from
      (Finset.prod_subset (s₁ := Ba) (s₂ := Finset.univ)
        (f := fun x => stepDist C (if x ∈ (Ba : Set (Fin d)) then g x else Set.univ))
        (Finset.subset_univ Ba) (by
          intro x _ hx
          rw [if_neg (show x ∉ (Ba : Set (Fin d)) from hx), measure_univ])).symm]
    exact Finset.prod_congr rfl (fun b hb => by
      rw [if_pos (show b ∈ (Ba : Set (Fin d)) from hb)])
  rw [hcollapse]

/-- A double product over block fibres collapses to the product over the index set. -/
lemma prod_mod_fiber {d : ℕ} (hd : 0 < d) (s : Finset ℕ) (f : ℕ → ℝ≥0∞) :
    ∏ a ∈ s.image (fun i => i / d),
        ∏ b ∈ (s.filter (fun i => i / d = a)).image
          (fun i => (⟨i % d, Nat.mod_lt i hd⟩ : Fin d)), f (a * d + b.val)
      = ∏ i ∈ s, f i := by
  rw [eq_comm]
  trans ∏ x ∈ (s.image (fun i => i / d)).sigma
      (fun a => (s.filter (fun i => i / d = a)).image
        (fun i => (⟨i % d, Nat.mod_lt i hd⟩ : Fin d))),
      f (x.1 * d + x.2.val)
  · refine Finset.prod_bij
      (fun i _ => (⟨i / d, (⟨i % d, Nat.mod_lt i hd⟩ : Fin d)⟩ : Σ _ : ℕ, Fin d)) ?_ ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_sigma]
      exact ⟨Finset.mem_image.mpr ⟨i, hi, rfl⟩,
        Finset.mem_image.mpr ⟨i, by rw [Finset.mem_filter]; exact ⟨hi, rfl⟩, rfl⟩⟩
    · intro i1 h1 i2 h2 heq
      have h1' : i1 / d = i2 / d := congrArg (fun x : (Σ _ : ℕ, Fin d) => x.1) heq
      have h2' : i1 % d = i2 % d :=
        congrArg (fun x : (Σ _ : ℕ, Fin d) => (x.2 : Fin d).val) heq
      calc i1 = i1 / d * d + i1 % d := (by rw [Nat.mul_comm]; exact (Nat.div_add_mod i1 d).symm)
        _ = i2 / d * d + i2 % d := by rw [h1', h2']
        _ = i2 := by rw [Nat.mul_comm]; exact Nat.div_add_mod i2 d
    · intro x hx
      obtain ⟨a, b⟩ := x
      rw [Finset.mem_sigma] at hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx.2
      rw [Finset.mem_filter] at hi
      refine ⟨i, hi.1, ?_⟩
      rw [Sigma.mk.injEq]
      exact ⟨hi.2, heq_of_eq rfl⟩
    · intro i hi
      change f i = f ((⟨i / d, (⟨i % d, Nat.mod_lt i hd⟩ : Fin d)⟩ : Σ _ : ℕ, Fin d).1 * d
        + (⟨i / d, (⟨i % d, Nat.mod_lt i hd⟩ : Fin d)⟩ : Σ _ : ℕ, Fin d).2.val)
      congr 1
      rw [Nat.mul_comm]; exact (Nat.div_add_mod i d).symm
  · exact Finset.prod_sigma _ _ (fun x : (Σ _ : ℕ, Fin d) => f (x.1 * d + x.2.val))

/-- The step measure is the pushforward of the block measure under `unblock`. -/
lemma unblock_measure {n d : ℕ} (hd : 0 < d) (C : ContactMatrix n) :
    (procMeasure C d).map (unblock (n := n) hd) = stepMeasure C := by
  refine Measure.eq_infinitePi (ν := (procMeasure C d).map (unblock (n := n) hd))
    (μ := fun _ : ℕ => stepDist C) (fun s t ht => ?_)
  rw [Measure.map_apply (measurable_unblock hd)
      (MeasurableSet.pi s.countable_toSet (fun i _ => ht i)), unblock_preimage hd s t]
  have hproc : procMeasure C d
      = Measure.infinitePi (fun _ : ℕ => Measure.pi (fun _ : Fin d => stepDist C)) := rfl
  rw [hproc, Measure.infinitePi_pi (μ := fun _ : ℕ => Measure.pi (fun _ : Fin d => stepDist C))
      (t := fun a => Set.pi ((s.filter (fun i => i / d = a)).image
        (fun i => (⟨i % d, Nat.mod_lt i hd⟩ : Fin d))) (fun b => t (a * d + b.val)))
      (mt := fun a _ => MeasurableSet.pi (Finset.countable_toSet _)
        (fun b _ => ht (a * d + b.val)))]
  refine (Finset.prod_congr rfl
    (fun a _ => pi_stepDist_pi C _ (fun b => t (a * d + b.val)))).trans ?_
  exact prod_mod_fiber hd s (fun i => stepDist C (t i))

end AnvBandit
