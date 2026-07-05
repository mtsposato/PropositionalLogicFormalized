import PropositionalLogicFormalized.Proof
import PropositionalLogicFormalized.Semantics
import PropositionalLogicFormalized.Lindenbaum

set_option linter.style.header false

theorem soundness : proof Γ f → entailment Γ f := by
  intro h
  induction h with
  | @hyp Γ' f' h' =>
    simp only [entailment]
    intro v h''
    simp only [setSatisfaction] at h''
    specialize h'' f'
    apply h''
    · exact h'
  | @conj_intro Γ₁ f₁ Γ₂ f₂ h1 h2 hi1 hi2 =>
    simp only [entailment] at *
    intro v h
    simp only [satisfaction]
    simp_all
    specialize hi1 v
    specialize hi2 v
    simp only [setSatisfaction] at *
    simp_all
  | @conj_elim_l Γ' f₁ f₂ h' hi' =>
    simp only [entailment] at *
    intro v h
    specialize hi' v
    simp only [satisfaction] at hi'
    simp only [Bool.and_eq_true] at hi'
    obtain ⟨hl, hr⟩ :=  hi' h
    exact hl
  | @conj_elim_r Γ' f₁ f₂ h' hi' =>
    simp only [entailment] at *
    intro v h
    specialize hi' v
    simp only [satisfaction] at hi'
    simp only [Bool.and_eq_true] at hi'
    obtain ⟨hl, hr⟩ :=  hi' h
    exact hr
  | @disj_intro_r Γ' f₁ f₂ h' hi' =>
    simp only [entailment] at *
    intro v h
    specialize hi' v
    simp only [satisfaction]
    simp only [Bool.or_eq_true]
    left
    apply hi'
    · exact h
  | @disj_intro_l Γ' f₁ f₂ h' hi' =>
    simp only [entailment] at *
    intro v h
    specialize hi' v
    simp only [satisfaction]
    simp only [Bool.or_eq_true]
    right
    apply hi'
    · exact h
  | @disj_elim Γ' f₁ Δ₁ g f₂ Δ₂ h1 h2 h3 hi1 hi2 hi3 =>
    simp only [entailment] at *
    intro v h'
    specialize hi1 v
    specialize hi2 v
    specialize hi3 v
    obtain ⟨h4, h3' ⟩ := setsat_distr h'
    obtain ⟨h1', h2'⟩ := setsat_distr h4
    obtain hi1' := hi1 h1'
    simp only [satisfaction] at hi1'
    simp only [Bool.or_eq_true] at hi1'
    obtain hl | hr := hi1'
    · have h'': setSatisfaction v ({f₁} ∪ Δ₁) := by
        simp only [setSatisfaction] at *
        simp_all
      apply hi2
      · exact h''
    · have h'': setSatisfaction v ({f₂} ∪ Δ₂) := by
        simp only [setSatisfaction] at *
        simp_all
      apply hi3
      · exact h''
  | @imp_intro f' Γ' f₂ h' hi' =>
    simp only [entailment] at *
    intro v h1
    simp only [setSatisfaction] at *
    specialize hi' v
    simp only [satisfaction]
    by_cases h2: satisfaction v f' = true
    · simp_all
    · simp_all
  | @imp_elim Γ₁ Γ₂ f₁ f₂ h1 h2 hi1 hi2 =>
    simp only [entailment] at *
    intro v h'
    specialize hi1 v
    specialize hi2 v
    obtain ⟨ hl, hr ⟩ := setsat_distr h'
    obtain hi1' := hi1 hl
    simp only [satisfaction] at hi1'
    simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hi1'
    obtain hl'| hr' := hi1'
    · simp_all
    · exact hr'
  | @neg_intro f' Γ' h' hi' =>
    simp only [entailment] at *
    intro v h''
    specialize hi' v
    simp only [satisfaction]
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true]
    by_cases hf: satisfaction v f' = true
    · have h2: setSatisfaction v ({f'} ∪ Γ') := by
        simp only [setSatisfaction] at *
        simp_all
      exfalso
      obtain h3 := hi' h2
      simp only [satisfaction] at h3
      simp at h3
    · simp only [Bool.not_eq_true] at hf
      exact hf
  | @neg_elim Γ₁ Γ₂ f' h1 h2 hi1 hi2 =>
    simp only [entailment] at *
    intro v h''
    specialize hi1 v
    specialize hi2 v
    obtain ⟨ hl, hr ⟩ := setsat_distr h''
    simp only [satisfaction] at *
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hi1
    obtain hi1' := hi1 hl
    obtain hi2' := hi2 hr
    simp_all
  | @contr_rule Γ' f' h' hi' =>
    simp only [entailment] at *
    intro v h''
    specialize hi' v
    by_cases h2: satisfaction v f'.Neg = true
    · have h4: setSatisfaction v ({f'.Neg} ∪ Γ') := by
        simp only [setSatisfaction] at *
        simp_all
      exfalso
      obtain h4' := hi' h4
      simp only [satisfaction] at h4'
      simp_all
    · simp only [satisfaction] at h2
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_false] at h2
      exact h2
  | @int_rule Γ' h' f' hi' =>
    simp only [entailment] at *
    intro v h''
    specialize hi' v
    exfalso
    obtain hi'' := hi' h''
    simp only [satisfaction] at hi''
    simp_all

theorem weak_soundness : nd_theorem f → tautology f := by
  simp only [nd_theorem, tautology]
  intro h v
  obtain h' := soundness h
  simp only [entailment] at h'
  specialize h' v
  apply h'
  simp only [setSatisfaction]
  simp_all

theorem sat_if_consistent :
  setSatisfaction v Γ → ¬ inconsistent Γ := by
  contrapose
  intro h
  simp only [inconsistent] at h
  obtain h' := soundness h
  simp only [entailment] at h'
  intro h1
  obtain h'':= h' v h1
  simp only [satisfaction] at h''
  contradiction

theorem completeness1 : ¬ inconsistent Γ → ∃ v, setSatisfaction v Γ  := by
  intro h
  obtain ⟨Γ', hs, hcc ⟩ := lindenbaum_lemma h
  obtain h' := truth_lemma hcc
  have h1: setSatisfaction (v_max Γ') Γ' := by
    simp only [setSatisfaction]
    simp_all
  have h2: setSatisfaction (v_max Γ') Γ := by
    simp only [setSatisfaction]
    simp_all only
    simp only [Subset, LE.le, Set.Subset] at hs
    apply hs
  use v_max Γ'

theorem completeness2 : entailment Γ f → proof Γ f := by
  contrapose
  intro h h'
  have hcon : ¬ inconsistent ({f.Neg} ∪ Γ) :=
    fun hinc => h (proof.contr_rule hinc)
  obtain h1 := @entailment_iff_neg_unsat Γ f
  rw [h1] at h'
  apply h'
  simp only [semanticaly_consistent]
  rw [← h1] at h'
  obtain ⟨Γ', hs, hcc⟩ := lindenbaum_lemma hcon
  obtain ht := truth_lemma hcc
  use v_max Γ'
  have h3: setSatisfaction (v_max Γ') Γ' := by
    simp only [setSatisfaction]
    simp_all
  have h2: setSatisfaction (v_max Γ') ({f.Neg} ∪ Γ) := by
    simp only [setSatisfaction]
    simp_all only
    simp only [Subset, LE.le, Set.Subset] at hs
    apply hs
  exact h2

theorem semantic_compacteness1 :
  entailment Γ f ↔ ∃ Γ', finite_subset Γ' Γ ∧ entailment Γ' f := by
  constructor
  · intro h
    obtain h':= completeness2 h
    obtain ⟨ Γ₀, hs, hp⟩ := compactness h'
    use Γ₀
    simp_all only [true_and]
    apply soundness hp
  · intro h
    obtain ⟨ Γ', hs, hi ⟩ := h
    exact entailment_monotonocity hs hi

theorem semantic_compacteness2 :
  setSatisfaction v Γ ↔ ∀ Γ', finite_subset Γ' Γ → setSatisfaction v Γ' := by
  constructor
  · intro h Γ₀ hs
    simp only [finite_subset, Subset, LE.le, Set.Subset, setSatisfaction] at *
    simp_all
  · intro h f hf
    have h1 : entailment Γ f := by
      intro v' hv'
      simp only [setSatisfaction] at hv'
      exact hv' f hf
    obtain ⟨Γ₀, hs, h2⟩ := @semantic_compacteness1.mp h1
    apply h2
    · apply h
      apply hs
