import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.SDiff

import PropositionalLogicFormalized.Formula

abbrev FormulaSet := Set Formula

theorem union_commu {Γ Γ' : FormulaSet} : Γ ∪ Γ' = Γ' ∪ Γ := by
  ext f
  simp only [Union.union, Set.union, Membership.mem,Set.Mem] at *
  constructor
  · intro h
    obtain hl | hr := h
    · right
      exact hl
    · left
      exact hr
  · intro h
    obtain hl | hr := h
    · right
      exact hl
    · left
      exact hr

theorem mem_set_mem_union {Γ Γ' : FormulaSet} :
  ∀ (f: Formula), f ∈ Γ → f ∈ Γ ∪ Γ' := by
  intro f h
  simp_all only [Set.mem_union, true_or]

theorem singleton_iff_mem {f f' : Formula} : f' ∈ ({f} : FormulaSet) → f' = f := by
  intro h
  simp only [Membership.mem, Set.Mem] at h
  exact ((fun a ↦ h) ∘ fun a ↦ f) f

theorem union_subset_subset {S₁' S₁ S₂' S₂ : FormulaSet}
  (h1 : S₁' ⊆ S₁) (h2 : S₂' ⊆ S₂) : S₁' ∪ S₂' ⊆ (S₁ ∪ S₂) := by
  exact Set.union_subset_union h1 h2

abbrev FiniteFormulaSet := Finset Formula

def finite_subset (Γ₀ : FiniteFormulaSet) (Γ : FormulaSet) :=
  ↑Γ₀ ⊆ Γ

instance : Singleton Formula FiniteFormulaSet :=
  ⟨fun a => ⟨{a}, Multiset.nodup_singleton a⟩⟩

instance : Union (Finset Formula) :=
  ⟨fun s t => ⟨_, t.2.ndunion s.1⟩⟩

theorem coe_distrib {Γ Γ' : FiniteFormulaSet} :
  (↑Γ: FormulaSet) ∪ (↑Γ': FormulaSet) = (↑(Γ ∪ Γ'): FormulaSet) := by
  ext x
  constructor
  · intro h
    simp_all only [Set.mem_union, SetLike.mem_coe]
    obtain hl | hr := h
    · simp only [Union.union]
      refine Finset.mem_mk.mpr ?_
      simp_all
    · simp only [Union.union]
      refine Finset.mem_mk.mpr ?_
      simp_all
  · intro h
    simp_all only [SetLike.mem_coe, Set.mem_union]
    simp only [Union.union] at h
    simp only [Finset.mem_mk, Multiset.mem_ndunion, Finset.mem_val] at h
    exact h
