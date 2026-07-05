import PropositionalLogicFormalized.Prop

inductive Boolean where
  | True : Boolean
  | False : Boolean
deriving DecidableEq, Repr

def Boolean.Neg
  | True => False
  | False => True

axiom neg_to_bool {a b: Boolean}: ¬ (a = b) ↔ (a = b.Neg)

theorem  boolean_excluded_middle {a b : Boolean} : a = b ∨ a = b.Neg := by
  simp only [Boolean.Neg]
  split
  case h_1 h =>
    by_cases h': a = Boolean.True
    · exact Or.symm (Or.inr h')
    · rw [neg_to_bool, Boolean.Neg] at h'
      exact Or.inr h'
  case h_2 h =>
    by_cases h': a = Boolean.False
    · exact Or.symm (Or.inr h')
    · rw [neg_to_bool, Boolean.Neg] at h'
      exact Or.inr h'

theorem boolean_double_negation {a : Boolean} : a = a.Neg.Neg := by
  simp only [Boolean.Neg]
  split
  case h_1 a' h =>
    split at h
    · trivial
    · trivial
  case h_2 a' h =>
    split at h
    · trivial
    · trivial

theorem boolean_oppositive {a b : Boolean} : ¬(a = b) ↔ a = b.Neg := by
  constructor
  · intro h
    apply or_exclusion (h) (@boolean_excluded_middle a b)
  · intro h1 h2
    simp only [Boolean.Neg] at h1
    split at h1
    · simp_all
    · simp_all

theorem boolean_oppositive2 {a b : Boolean} : a = b ↔ ¬(a = b.Neg) := by
  constructor
  · intro h h'
    simp_all
    simp only [Boolean.Neg] at h
    split at h
    · simp_all
    · simp_all
  · intro h1
    rw [boolean_oppositive, ← boolean_double_negation] at h1
    exact h1
