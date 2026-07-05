import PropositionalLogicFormalized.Formula
import PropositionalLogicFormalized.Boolean
import PropositionalLogicFormalized.FormulaSet

def valuation (v: Nat → Boolean)
  | Formula.False => Boolean.False
  | Formula.Var n => v (n)
  | Formula.Neg f =>
    if valuation v f = Boolean.False then
      Boolean.True
    else Boolean.False
  | Formula.Conj f₁ f₂ =>
    if (valuation v f₁ = Boolean.True && valuation v f₂ = Boolean.True) then
      Boolean.True
    else Boolean.False
  | Formula.Disj f₁ f₂ =>
    if (valuation v f₁ = Boolean.True || valuation v f₂ = Boolean.True) then
      Boolean.True
    else Boolean.False
  | Formula.Imp f₁ f₂ =>
    if (valuation v f₁ = Boolean.False || valuation v f₂ = Boolean.True) then
      Boolean.True
    else Boolean.False

def propVarsOfFormula
  | Formula.False => []
  | Formula.Var n => [n]
  | Formula.Neg f => propVarsOfFormula f
  | Formula.Conj f₁ f₂ | Formula.Disj f₁ f₂ | Formula.Imp f₁ f₂ =>
    propVarsOfFormula f₁ ++ propVarsOfFormula f₂

theorem local_determination (h : ∀ n ∈ propVarsOfFormula f, v₁ n = v₂ n) :
  valuation v₁ f = valuation v₂ f := by
  induction f with
  | False =>
    simp only [valuation]
  | Var n' =>
    simp only [valuation]
    simp only [propVarsOfFormula] at h
    simp_all
  | Neg f hi =>
    simp only [propVarsOfFormula] at h
    simp only [valuation]
    split
    case Neg.isTrue h' =>
      split
      · rfl
      case isFalse h'' =>
        obtain h3 := hi h
        rw [h'] at h3
        obtain h4: valuation v₂ f = Boolean.True := by
          simp_all
        rw [h4] at h3
        rw [h3]
    case Neg.isFalse h' =>
      split
      case isTrue h'' =>
        obtain h3 := hi h
        obtain h4: valuation v₂ f = Boolean.True := by
          simp_all
        rw [← h'', ← h4]
      case isFalse =>
        rfl
  | Conj f₁ f₂ hi₁ hi₂ =>
    simp only [valuation]
    split
    case Conj.isTrue h' =>
      simp_all
      simp only [propVarsOfFormula] at *
      simp_all
    case Conj.isFalse h' =>
      simp_all
      simp only [propVarsOfFormula] at *
      simp_all
  | Disj f₁ f₂ hi₁ hi₂ =>
    simp only [valuation]
    split
    case Disj.isTrue h' =>
      simp_all only [Bool.or_eq_true, decide_eq_true_eq, left_eq_ite_iff, not_or, reduceCtorEq,
        imp_false, not_and, Decidable.not_not]
      simp only [propVarsOfFormula] at *
      simp_all only [List.mem_append, true_or, implies_true, forall_const, or_true]
      intro h1
      simp_all
    case Disj.isFalse h' =>
      simp_all
      simp only [propVarsOfFormula] at *
      simp_all
  | Imp f₁ f₂ hi₁ hi₂ =>
    simp only [valuation]
    split
    case Imp.isTrue h' =>
      simp_all only [Bool.or_eq_true, decide_eq_true_eq, left_eq_ite_iff, not_or, reduceCtorEq,
        imp_false, not_and, Decidable.not_not]
      simp only [propVarsOfFormula] at *
      simp_all only [List.mem_append, true_or, implies_true, forall_const, or_true]
      intro h1
      simp_all
    case Imp.isFalse h' =>
      simp_all
      simp only [propVarsOfFormula] at *
      simp_all

def satisfaction (v: Nat → Boolean)
  | Formula.False => false
  | Formula.Var n => v n = Boolean.True
  | Formula.Neg f => !(satisfaction v f)
  | Formula.Conj f₁ f₂ =>
    satisfaction v f₁ && satisfaction v f₂
  | Formula.Disj f₁ f₂ =>
    satisfaction v f₁ || satisfaction v f₂
  | Formula.Imp f₁ f₂ =>
    !(satisfaction v f₁) || satisfaction v f₂

theorem valuation_satisfaction : valuation v f = Boolean.True ↔ satisfaction v f := by
  induction f generalizing v with
  | False =>
    simp only [valuation, satisfaction]
    trivial
  | Var n =>
    simp only [valuation, satisfaction]
    constructor
    · intro h
      rw [h]
      rfl
    · intro h
      simp_all
  | Neg f hi =>
    simp only [valuation, satisfaction] at *
    split
    case Neg.isTrue h' =>
      simp_all only [Bool.not_eq_eq_eq_not, Bool.not_true, true_iff]
      have h3: ¬ valuation v f = Boolean.True := by
        simp_all
      obtain h4 := iff_negative h3 hi
      simp only [Bool.not_eq_true] at h4
      exact h4
    case Neg.isFalse h' =>
      simp_all
      have h'' :  valuation v f = Boolean.True := by
        rw [boolean_oppositive] at h'
        exact h'
      obtain h2 := @hi v
      simp_all
  | Conj f₁ f₂ hi₁ hi₂ =>
    simp only [valuation, satisfaction] at *
    split
    case Conj.isTrue h' =>
      simp_all
    case Conj.isFalse h' =>
      simp_all
  | Disj f₁ f₂ hi₁ hi₂ =>
    simp only [valuation, satisfaction] at *
    split
    case Disj.isTrue h' =>
      simp_all
    case Disj.isFalse h' =>
      simp_all
  | Imp f₁ f₂ hi₁ hi₂ =>
    simp only [valuation, satisfaction] at *
    split
    case Imp.isTrue h' =>
      simp_all only [Bool.decide_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
        Bool.not_true, true_iff]
      obtain hl' | hr' := h'
      · left
        rw [boolean_oppositive2] at hl'
        obtain h4 := iff_negative hl' hi₁
        simp only [Bool.not_eq_true] at h4
        exact h4
      · right
        exact hr'
    case Imp.isFalse h' =>
      simp_all
      obtain ⟨ hl', hr'⟩ := h'
      have h'' : valuation v f₁ = Boolean.True := by
        rw [boolean_oppositive] at hl'
        exact hl'
      simp_all


def tautology (f : Formula) := ∀ v, satisfaction v f

def setSatisfaction (v) (Γ : FormulaSet) := ∀ f ∈ Γ, satisfaction v f

def semanticaly_consistent (Γ : FormulaSet) := ∃ v, setSatisfaction v Γ

def entailment (Γ : FormulaSet) (f : Formula) :=
  ∀ v, setSatisfaction v Γ → satisfaction v f


theorem tautology_iff_empty_entailment : tautology f ↔ entailment ∅ f := by
  constructor
  · intro h
    unfold tautology at h
    unfold entailment
    intro v h'
    exact h v
  · unfold entailment
    intro h
    unfold tautology
    simp only [setSatisfaction] at h
    intro v
    specialize h v
    have h' :  ∀ f, f ∈ (∅: FormulaSet) → satisfaction v f = true := by
      intro f h''
      exfalso
      apply h''
    exact h h'

theorem modus_ponens_entailment (h : entailment Γ f) (h' : entailment Γ (f.Imp f')) :
  entailment Γ f' := by
  simp only [entailment] at *
  simp only [satisfaction] at h'
  intro v h1
  obtain h2 := h v h1
  obtain h3 := h' v h1
  simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h3
  obtain h3l | h3r := h3
  · rw [h3l] at h2
    exfalso
    have h4: False := by
      simp_all
    apply h4
  · exact h3r


theorem infinite_sat_finite_sat :
  setSatisfaction v Γ → ∀ Γ', finite_subset Γ' Γ → setSatisfaction v Γ' := by
  intro h Γ' h' f h''
  simp only [setSatisfaction] at h
  simp only [finite_subset] at h'
  obtain h2 := Set.mem_of_subset_of_mem h' h''
  apply h
  exact h2

theorem entailment_monotonocity :
  Γ ⊆ Δ → entailment Γ f → entailment Δ f := by
  intro h h' v h1
  simp only [entailment] at h'
  specialize h' v
  have h3 : setSatisfaction v Γ := by
    intro f' h''
    simp only [setSatisfaction] at h1
    specialize h1 f'
    obtain h2 := @Set.mem_of_subset_of_mem Formula Γ Δ f' h
    apply h1 (h2 h'')
  apply h' h3

theorem setsat_iff_union :
  setSatisfaction v (Γ ∪ Δ) → setSatisfaction v Γ ∧ setSatisfaction v Δ := by
  intro h
  simp only [setSatisfaction] at *
  simp_all only [Set.mem_union, true_or, implies_true,
      or_true, and_self]

theorem setsat_sing_iff_sat :
  setSatisfaction v {f} → satisfaction v f := by
  intro h
  unfold setSatisfaction at h
  specialize h f
  have h2: f ∈ ({f}: FormulaSet) := by
    exact Set.mem_of_subset_of_mem (fun ⦃a⦄ a_1 ↦ a_1) rfl
  apply h h2

theorem entailment_transitivity :
  entailment Γ f → entailment (Δ ∪ {f}) f' → entailment (Γ ∪ Δ) f' := by
  intro h h' v h1
  simp_all only [entailment]
  specialize h v
  specialize h' v
  obtain h1' := setsat_iff_union h1
  obtain ⟨ h1l', h1r' ⟩ := h1'
  obtain h4:= h h1l'
  have h5: setSatisfaction v (Δ ∪ {f}) := by
    intro f'' h6
    simp_all only [imp_self, Set.mem_union]
    obtain h6l | h6r := h6
    · simp only [setSatisfaction] at h1r'
      specialize h1r' f''
      apply h1r' h6l
    · obtain h7:= singleton_iff_mem h6r
      rw [h7]
      exact h4
  apply h' h5

theorem entailment_iff_neg_unsat :
  entailment Γ f ↔ ¬ semanticaly_consistent ({f.Neg} ∪ Γ) := by
  constructor
  · intro h h'
    --simp only [entailment] at h
    simp only [semanticaly_consistent] at h'
    obtain ⟨ v, h1 ⟩ := h'
    obtain ⟨hl', hr'⟩  := setsat_iff_union h1
    obtain h2 := h v hr'
    obtain h3 := setsat_sing_iff_sat hl'
    simp only [satisfaction] at h3
    simp at h3
    simp_all
  · intro h v h1
    simp only [semanticaly_consistent] at h
    simp only [not_exists] at h
    specialize h v
    have h1': ¬ satisfaction v f.Neg := by
      simp only [setSatisfaction] at *
      simp_all only [Set.mem_union, not_forall, Bool.not_eq_true]
      obtain ⟨f', ⟨hl,hr ⟩⟩ := h
      simp only [satisfaction]
      obtain hll | hlr := hl
      · obtain h3 := singleton_iff_mem hll
        rw [h3] at hr
        simp only [satisfaction] at hr
        simp only [Bool.not_eq_eq_eq_not, Bool.not_false] at *
        exact hr
      · simp_all
    simp_all only [Bool.not_eq_true]
    simp only [satisfaction] at h1'
    simp_all

theorem setsat_if_set_sat (h : setSatisfaction v Γ) (h' : satisfaction v f) :
  setSatisfaction v (Γ ∪ {f}) := by
  simp_all only [setSatisfaction]
  intro f' h'
  specialize h f'
  simp only [Set.mem_union] at h'
  obtain hl' | hr' := h'
  · apply h hl'
  · obtain h1 := singleton_iff_mem hr'
    rw [h1]
    apply h'

theorem semantic_deduction {Γ : FormulaSet} {f₁ f₂ : Formula} :
  entailment Γ (f₁.Imp f₂) ↔ entailment (Γ ∪ {f₁}) f₂ := by
  constructor
  · intro h v h1
    simp only [entailment] at h
    specialize h v
    obtain ⟨ hl, hr ⟩ := setsat_iff_union h1
    obtain hr' := setsat_sing_iff_sat hr
    obtain h' := h hl
    simp only [satisfaction] at h'
    simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h'
    obtain hl'' | hr'' := h'
    · simp_all only [forall_const, Bool.false_eq_true]
    · exact hr''
  · intro h v h1
    specialize h v
    simp only [satisfaction]
    simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
    by_cases h': satisfaction v f₁ = true
    · have h2: setSatisfaction v (Γ ∪ {f₁}) := by
        apply setsat_if_set_sat h1 h'
      right
      simp_all
    · simp at h'
      left
      simp_all

theorem setsat_distr (h : setSatisfaction v (Γ₁ ∪ Γ₂)) :
  setSatisfaction v Γ₁ ∧ setSatisfaction v Γ₂ := by
  constructor
  · simp only [setSatisfaction] at *
    intro f h1
    simp_all
  · simp only [setSatisfaction] at *
    intro f h1
    simp_all
