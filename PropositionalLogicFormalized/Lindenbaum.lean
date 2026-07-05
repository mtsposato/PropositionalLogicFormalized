/-
This file is inspired from:
https://github.com/FormalizedFormalLogic/Foundation/blob/387f915db60c443e9b948b1da4ce84629db47118/Foundation/Modal/Tableau.lean

-/
import PropositionalLogicFormalized.Complete
import PropositionalLogicFormalized.Semantics

noncomputable instance : Decidable (¬ inconsistent (Γ ∪ {f})) :=
  Classical.propDecidable _

noncomputable def lindenbaum_next (f : Formula) (Γ : FormulaSet) : FormulaSet :=
  if ¬inconsistent (Γ ∪ {f}) then Γ ∪ {f} else Γ ∪ {f.Neg}


noncomputable def lindenbaum_next_indexed [Encodable Formula] (Γ : FormulaSet) : ℕ → FormulaSet
  | 0 => Γ
  | i + 1 =>
    match (Encodable.decode i) with
    | some f => lindenbaum_next f (lindenbaum_next_indexed Γ i)
    | none => lindenbaum_next_indexed Γ i

variable {Γ : FormulaSet}
local notation:max Γ"[" i "]" => lindenbaum_next_indexed Γ i

@[simp]
theorem lindenbaum_next_indexed_zero [Encodable Formula] :
  (lindenbaum_next_indexed Γ 0) = Γ := by
  simp [lindenbaum_next_indexed]

theorem next_parametericConsistent (h : ¬ inconsistent Γ) :
  ¬ inconsistent (lindenbaum_next f Γ) := by
  dsimp [lindenbaum_next]
  split
  case isTrue h' => exact h'
  case isFalse h' =>
    simp only [not_not] at h'
    obtain hl3 | hr3 := @inconsistent_or_neg_inconsisten Γ f h
    · contradiction
    · exact hr3

def lindenbaum_maximal [Encodable Formula] (Γ : FormulaSet) : FormulaSet := (⋃ i, Γ[i])
local notation:max Γ"∞" => lindenbaum_maximal  Γ

theorem lindenbaum_next_indexed_parametricConsistent_succ {i : ℕ} :
  ¬ inconsistent Γ[i] → ¬ inconsistent Γ[i + 1] := by
  dsimp [lindenbaum_next_indexed];
  split;
  · intro h;
    apply next_parametericConsistent h
  · tauto;

theorem lindenbaum_next_indexed_parametricConsistent (h : ¬ inconsistent Γ) (i : ℕ) :
  ¬ inconsistent Γ[i] := by
  induction i with
  | zero => simp_all;
  | succ i hi =>
    apply lindenbaum_next_indexed_parametricConsistent_succ hi

theorem lindenbaum_next_indexed_subset₁_of_lt (h : m ≤ n) : Γ[m] ⊆ Γ[n] := by
  induction h with
  | refl => simp;
  | step h ih =>
    simp [lindenbaum_next_indexed, lindenbaum_next];
    split;
    · split <;> tauto;
    · tauto;

theorem exists_list_lindenbaum_index₁ {Γ₀ : List Formula}
    (hΓ₀ : ↑Γ₀.toFinset ⊆ ⋃ i, Γ[i]) : ∃ m, ∀ φ ∈ Γ₀, φ ∈ Γ[m] := by
  induction Γ₀ with
  | nil => simp
  | cons φ Γ₀ ih =>
    simp_all only [List.coe_toFinset, List.toFinset_cons,
      Finset.coe_insert, List.mem_cons, forall_eq_or_imp]
    replace hΓ₀ := Set.insert_subset_iff.mp hΓ₀
    obtain ⟨_, ⟨i, _⟩, _⟩ := hΓ₀.1
    obtain ⟨m, hm⟩ := ih hΓ₀.2
    use (i + m)
    constructor
    · exact lindenbaum_next_indexed_subset₁_of_lt (m := i) (by omega) (by simp_all)
    · intro ψ hq
      exact lindenbaum_next_indexed_subset₁_of_lt (by simp) <| hm ψ hq

theorem exists_finset_lindenbaum_index₁ {Γ₀ : FiniteFormulaSet}
    (hΓ₀ : ↑Γ₀ ⊆ ⋃ i, Γ[i]) : ∃ m, ∀ φ ∈ Γ₀, φ ∈ Γ[m] := by
  obtain ⟨m, hm⟩ := exists_list_lindenbaum_index₁ (Γ₀ := Γ₀.toList) (by simpa)
  use m
  intro φ hφ
  apply hm
  simpa

theorem mem_lindenbaum_next_indexed (f : Formula) :
  f ∈ Γ[(Encodable.encode f) + 1] ∨ f.Neg ∈ Γ[(Encodable.encode f) + 1] := by
  simp only [lindenbaum_next_indexed, Encodable.encodek, lindenbaum_next]
  split
  · left
    simp
  · right
    simp

theorem lindenbaum_lemma (h : ¬ inconsistent Γ) :
  ∃ Γ',  Γ ⊆ Γ' ∧  complete_set Γ' ∧ ¬ inconsistent Γ' := by
  use Γ∞
  refine ⟨?subset, ?complete, ?consistent⟩
  · apply Set.subset_iUnion_of_subset 0
    simp [lindenbaum_next_indexed_zero]
  · simp only [complete_set]
    simp only [lindenbaum_maximal, Set.mem_iUnion];
    intro f
    rcases @mem_lindenbaum_next_indexed Γ f with (h' | h');
    · left; use (Encodable.encode f + 1);
    · right; use (Encodable.encode f + 1);
  · apply compacteness_2
    intro Γ₀ hΓ₀
    obtain ⟨m, hm⟩ := exists_finset_lindenbaum_index₁ hΓ₀
    intro hcon
    apply lindenbaum_next_indexed_parametricConsistent h m
    exact derivation_monotonicity hm hcon


noncomputable instance :  Decidable (Formula.Var n ∈ Γ):=
  Classical.propDecidable _

noncomputable def v_max (Γ : FormulaSet) (n : ℕ) : Boolean :=
  if Formula.Var n ∈ Γ then Boolean.True else Boolean.False


theorem comp_cons_iff (h : complete_set Γ ∧ ¬ inconsistent Γ) :
  f ∈ Γ ↔ f.Neg ∉ Γ := by
  constructor
  · intro h'
    obtain ⟨ hl, hr ⟩ := h
    simp only [complete_set, inconsistent] at *
    by_contra hc
    obtain h1 := proof.hyp h'
    obtain h2 := proof.hyp hc
    obtain h3 := proof.neg_elim h2 h1
    simp at h3
    contradiction
  · intro h'
    obtain ⟨ hl, hr ⟩ := h
    simp only [complete_set, inconsistent] at *
    specialize hl f
    have h1' := f ∈ Γ ∨ f.Neg ∈ Γ
    apply or_exclusion
    · apply h'
    · simp_all

theorem truth_lemma (h : complete_set Γ ∧ ¬ inconsistent Γ) (f : Formula) :
  satisfaction (v_max Γ) f ↔ f ∈ Γ := by
  induction f generalizing h with
  | False =>
    simp only [satisfaction]
    constructor
    · intro h'
      simp_all
    · intro h'
      obtain h1 := proof.hyp h'
      simp only [inconsistent] at h
      obtain ⟨ hl, hr ⟩ := h
      contradiction
  | Var n =>
    constructor
    · intro h'
      by_cases h1 : Formula.Var n ∈ Γ
      · exact h1
      · simp only [satisfaction, v_max] at h'
        simp_all
    · intro h'
      simp only [satisfaction, v_max]
      simp_all
  | Neg f hi =>
    obtain h'' := hi h
    simp only [satisfaction]
    simp_all only [not_false_eq_true, and_self, imp_self, Bool.not_eq_eq_eq_not, Bool.not_true]
    obtain ⟨ hl, hr ⟩ := h
    simp only [complete_set] at hl
    constructor
    · intro h2
      simp_all only [Bool.false_eq_true, false_iff]
      specialize hl f
      apply or_exclusion h'' hl
    · intro h2
      have h3: f ∉ Γ := by
        have h3': complete_set Γ ∧ ¬ inconsistent Γ := by
          simp_all
          simp [complete_set]
          simp_all
        obtain h4 := @comp_cons_iff Γ f h3'
        simp_all
      simp_all
  | Conj f₁ f₂ hi₁ hi₂ =>
    obtain h':= @conj_comp_cons_set Γ f₁ f₂ h
    simp [satisfaction]
    simp_all
  | Disj f₁ f₂ hi₁ hi₂ =>
    obtain h':= @disj_comp_cons_set Γ f₁ f₂ h
    simp [satisfaction]
    simp_all
  | Imp f₁ f₂ hi₁ hi₂ =>
    obtain h':= @imp_comp_cons_set Γ f₁ f₂ h
    simp only[satisfaction]
    simp_all only [not_false_eq_true, and_self, forall_const, Bool.or_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true]
    refine or_congr ?_ ?_
    · constructor
      · intro h''
        simp_all
      · intro h''
        simp_all
    · exact Eq.to_iff rfl
