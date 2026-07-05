import PropositionalLogicFormalized.FormulaSet
import PropositionalLogicFormalized.Proof
import PropositionalLogicFormalized.Prop

def complete_set (Γ : FormulaSet) :=
    ∀ f, f ∈ Γ ∨ f.Neg ∈ Γ

theorem if_provable_formula_in_compset (h : complete_set Γ ∧ ¬ inconsistent Γ) :
  proof Γ f → f ∈ Γ := by
  obtain ⟨ hl, hr ⟩ := h
  simp only [complete_set] at hl
  simp only [inconsistent] at hr
  intro h'
  specialize hl f
  obtain hl' | hr' := hl
  · exact hl'
  · obtain h1 := proof.hyp hr'
    obtain hf := proof.neg_elim h1 h'
    simp at hf
    contradiction

theorem conj_comp_cons_set (h : complete_set Γ ∧ ¬ inconsistent Γ) :
  f₁.Conj f₂ ∈ Γ ↔ f₁ ∈ Γ ∧ f₂ ∈ Γ := by
  constructor
  · intro h'
    constructor
    · apply if_provable_formula_in_compset
      · exact h
      · apply proof.conj_elim_l
        · apply proof.hyp h'
    · apply if_provable_formula_in_compset
      · exact h
      · apply proof.conj_elim_r
        · apply proof.hyp h'
  · intro h'
    obtain ⟨hr', hl'⟩ := h'
    · apply if_provable_formula_in_compset
      · exact h
      · obtain h1 := proof.hyp hr'
        obtain h2 := proof.hyp hl'
        obtain h3 := proof.conj_intro h1 h2
        simp only [Set.union_self] at h3
        exact h3


theorem disj_comp_cons_set (h : complete_set Γ ∧ ¬ inconsistent Γ) :
  f₁.Disj f₂ ∈ Γ ↔ f₁ ∈ Γ ∨ f₂ ∈ Γ := by
  constructor
  · intro h'
    obtain ⟨ hl, hr ⟩ := h
    simp only [complete_set, inconsistent] at *
    obtain hl1| hr1 := hl f₁
    · left
      exact hl1
    · obtain hl2| hr2 := hl f₂
      · right
        exact hl2
      · exfalso
        obtain hf1 := proof.hyp hr1
        obtain hf2 := proof.hyp hr2
        have h3: f₁ ∈ ({f₁} ∪ Γ) := by
         simp_all
        have h4: f₂ ∈ ({f₂} ∪ Γ) := by
         simp_all
        obtain hf1':= proof.hyp h3
        obtain hf2':= proof.hyp h4
        obtain hf1'':= proof.neg_elim hf1 hf1'
        simp only [Set.singleton_union, Set.union_insert,
          Set.union_self] at hf1''
        obtain hf2'':= proof.neg_elim hf2 hf2'
        simp only [Set.singleton_union, Set.union_insert,
          Set.union_self] at hf2''
        obtain hf0 := proof.hyp h'
        have h3: proof Γ Formula.False := by
          obtain h3' := proof.disj_elim hf0 hf1'' hf2''
          simp only [Set.union_self] at h3'
          exact h3'
        contradiction
  · intro h'
    obtain hl'| hr' := h'
    · apply if_provable_formula_in_compset
      · exact h
      · apply proof.disj_intro_r
        · apply proof.hyp
          · exact hl'
    · apply if_provable_formula_in_compset
      · exact h
      · apply proof.disj_intro_l
        · apply proof.hyp
          · exact hr'

theorem imp_comp_cons_set (h : complete_set Γ ∧ ¬ inconsistent Γ) :
  f₁.Imp f₂ ∈ Γ ↔ f₁ ∉ Γ ∨ f₂ ∈ Γ := by
  constructor
  · intro h'
    obtain himp':= proof.hyp h'
    obtain ⟨ hl, hr ⟩ := h
    simp only [complete_set, inconsistent] at *
    obtain hl1| hr1 := hl f₁
    · right
      apply if_provable_formula_in_compset
      · simp only [complete_set, inconsistent]
        simp_all
      · obtain hf1 := proof.hyp hl1
        obtain hf2 := proof.imp_elim himp' hf1
        simp only [Set.union_self] at hf2
        exact hf2
    · by_cases hf : f₁ ∈ Γ
      · obtain hfp := proof.hyp hf
        obtain hnfp := proof.hyp hr1
        obtain hn := proof.neg_elim hnfp hfp
        simp at hn
        contradiction
      · left
        exact hf
  · intro h'
    obtain hl' | hr' := h'
    · obtain ⟨ hl, hr ⟩ := h
      simp only [complete_set] at hl
      obtain hlf2 | hrf2 := hl f₂
      · have h1: f₂ ∈ {f₁} ∪ Γ := by
          simp_all
        apply if_provable_formula_in_compset
        · simp only [complete_set]
          simp_all
        · apply proof.imp_intro
          · apply proof.hyp h1
      · obtain hf1 := hl f₁
        obtain hf1':= or_exclusion hl' hf1
        apply if_provable_formula_in_compset
        · simp only [complete_set]
          simp_all
        · obtain hf1n := proof.hyp hf1'
          have h': f₁ ∈ ({f₁}: FormulaSet) := by
            exact Set.mem_singleton f₁
          obtain hf1n' :=  proof.hyp h'
          obtain hf2 := proof.int_rule (proof.neg_elim hf1n hf1n') f₂
          have h'': Γ ∪ {f₁} = {f₁} ∪ Γ := by
            simp_all
          rw [h''] at hf2
          apply proof.imp_intro hf2
    · have h1: f₂ ∈ {f₁} ∪ Γ := by simp_all
      obtain hf1 := proof.hyp h1
      obtain hf2 := proof.imp_intro hf1
      apply if_provable_formula_in_compset
      · exact h
      · exact hf2
