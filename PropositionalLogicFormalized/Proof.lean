import PropositionalLogicFormalized.FormulaSet

inductive proof : FormulaSet → Formula → Prop where
  | hyp : f ∈ Γ → proof Γ f
  | conj_intro: proof Γ₁ f₁ → proof Γ₂ f₂ → proof (Γ₁ ∪ Γ₂) (f₁.Conj f₂)
  | conj_elim_l:  proof Γ (f₁.Conj f₂) → proof Γ f₁
  | conj_elim_r{f₁ f₂: Formula}:   proof Γ (f₁.Conj f₂) → proof Γ f₂
  | disj_intro_r: proof Γ f₁ → proof Γ (f₁.Disj f₂)
  | disj_intro_l {f₁ f₂: Formula}: proof Γ f₁ → proof Γ (f₂.Disj f₁)
  | disj_elim:
    proof Γ (f₁.Disj f₂) → proof ({f₁} ∪ Δ₁) g → proof ({f₂} ∪ Δ₂) g → proof (Γ ∪ Δ₁ ∪ Δ₂) g
  | imp_intro: proof ({f₁} ∪ Γ) f₂ → proof Γ (f₁.Imp f₂)
  | imp_elim: proof Γ₁ (f₁.Imp f₂) → proof Γ₂ f₁ → proof (Γ₁ ∪ Γ₂) f₂
  | neg_intro: proof ({f} ∪ Γ) Formula.False → proof Γ f.Neg
  | neg_elim: proof Γ₁ (f.Neg) → proof Γ₂ f → proof (Γ₁ ∪ Γ₂) Formula.False
  | contr_rule: proof ({f.Neg} ∪ Γ) Formula.False → proof Γ f
  | int_rule: proof Γ Formula.False → ∀f, proof Γ f



def nd_theorem (f : Formula) := proof ∅ f

def derivable (Γ : FormulaSet) (f : Formula) := proof Γ f

def inconsistent (Γ : FormulaSet) := proof Γ Formula.False

theorem hypothesys_is_derivation : f ∈ Γ → proof Γ f := by
  intro h
  exact proof.hyp h

theorem or_distrib (h : (p ∨ q) → r) : ((p → r) ∨ (q → r)) := by
  grind

theorem union_sub_eq_set {Γ Δ : FormulaSet} (h : Γ ⊆ Δ) : Δ ∪ Γ = Δ := by
  simp_all

theorem union_remove_par {Δ Δ₁ Δ₂ : FormulaSet} :  Δ ∪ (Δ₁ ∪ Δ₂) =  Δ ∪ Δ₁ ∪ Δ₂ := by
  exact Eq.symm (Set.union_assoc Δ Δ₁ Δ₂)


theorem derivation_monotonicity (h : Γ ⊆ Δ) :
  proof Γ f → proof Δ f := by
  intro h1
  induction h1 generalizing Δ with
  | @hyp G f' h' =>
      exact proof.hyp (h h')
  | @conj_intro Γ₁ f₁ Γ₂ f₂ h1 h2 h3 h4 =>
    simp only [Set.union_subset_iff] at h
    obtain ⟨ hl, hr ⟩ := h
    obtain h5 := proof.conj_intro (h3 hl) (h4 hr)
    simp only [Set.union_self] at h5
    apply h5
  | @conj_elim_l Γ' f₁ f₂ h' hi' =>
    apply proof.conj_elim_l (hi' h)
  | @conj_elim_r Γ' f₁ f₂ h' hi' =>
    apply proof.conj_elim_r (hi' h)
  | @disj_intro_r Γ' f₁ f₂ h' hi' =>
    apply proof.disj_intro_r (hi' h)
  | @disj_intro_l Γ' f₁ f₂ h' hi' =>
    apply proof.disj_intro_l (hi' h)
  | @disj_elim Γ' f₁ Δ₁ g f₂ Δ₂ h1 h2 h3 hi1 hi2 hi3 =>
    have h': (Γ' ⊆ Δ ∧ Δ₁ ⊆ Δ) ∧ Δ₂ ⊆ Δ := by
      simp only [Set.union_subset_iff] at h
      exact h
    obtain ⟨ ⟨ h1', h2'⟩ , h3'⟩ := h'
    obtain h7:= proof.disj_elim (hi1 h1') h2 h3
    have h8: Δ₁ ∪ Δ₂ ⊆ Δ := by
      simp_all
    obtain h9 := (union_sub_eq_set h8)
    rw [union_remove_par] at h9
    simp_all
  | @imp_intro f' Γ' f'' h' hi' =>
    apply proof.imp_intro
    apply hi'
    apply Set.union_subset_union_right {f'} h
  | @imp_elim Γ₁ Γ₂ f₁ f₂ h1 h2 hi1 hi2 =>
    simp only [Set.union_subset_iff] at h
    obtain ⟨ hl, hr ⟩ := h
    simp_all only [subset_refl]
    specialize @hi1 Δ hl
    specialize @hi2 Δ hr
    obtain h5 :=  proof.imp_elim hi1 hi2
    simp only [Set.union_self] at h5
    exact h5
  | @neg_intro f' Γ' h' hi' =>
    apply proof.neg_intro
    apply hi'
    apply Set.union_subset_union_right {f'} h
  | @neg_elim Γ₁ Γ₂ f' h1 h2 hi1 hi2 =>
    simp only [Set.union_subset_iff] at h
    obtain ⟨ hl, hr ⟩ := h
    simp_all only [subset_refl]
    specialize hi1 hl
    specialize hi2 hr
    obtain h5 :=  proof.neg_elim hi1 hi2
    simp only [Set.union_self] at h5
    exact h5
  | @contr_rule Γ' f' h' hi' =>
    apply proof.contr_rule
    apply hi'
    apply Set.union_subset_union_right
    exact h
  | @int_rule Γ' f' h' hi' =>
    apply proof.int_rule
    apply hi'
    exact h

theorem derivation_transitivity :
  proof Γ f → proof (Δ ∪ {f}) f' → proof (Γ ∪ Δ ) f' := by
  intro h h'
  rw [union_commu] at *
  obtain h4:= proof.imp_intro h'
  obtain h5:= proof.imp_elim h4 h
  exact h5

theorem every_iff_inconsistent :
  inconsistent Γ ↔ ∀ f, proof Γ f := by
  constructor
  · intro h
    simp only [inconsistent] at h
    apply proof.int_rule
    exact h
  · intro h
    simp only [inconsistent]
    specialize h Formula.False
    exact h

theorem every_iff_formula_and_neg : (∀ f, proof Γ f) ↔ (∃ f, proof Γ f ∧ proof Γ (f.Neg)) := by
  constructor
  · intro h
    simp_all only [and_self, exists_const]
  · intro h
    obtain ⟨f, hf, hnf⟩ := h
    apply proof.int_rule
    obtain h'' := proof.neg_elim hnf hf
    simp only [Set.union_self] at h''
    exact h''


theorem compactness :
  proof Γ f → ∃ Γ₀, finite_subset Γ₀ Γ ∧ proof ↑Γ₀ f := by
  intro h
  induction h with
  | @hyp Γ' f' h' =>
    use  {f'}
    simp only [finite_subset, Finset.coe_singleton, Set.singleton_subset_iff]
    constructor
    · exact h'
    · obtain h'' := Set.mem_singleton f'
      apply proof.hyp h''
  | @conj_intro Γ₁ f₁ Γ₂ f₂ h1 h2 hi1 hi2 =>
    simp_all only [finite_subset]
    obtain ⟨Γ₁', hl1, hr1⟩ := hi1
    obtain ⟨Γ₂', hl2, hr2⟩ := hi2
    use Γ₁' ∪ Γ₂'
    have h3: (↑(Γ₁' ∪ Γ₂'): FormulaSet) = (↑Γ₁': FormulaSet) ∪ (↑Γ₂': FormulaSet) := by
        rw [coe_distrib]
    constructor
    · rw [h3]
      simp_all only [Finset.coe_union, Set.union_subset_iff]
      constructor
      · exact Set.subset_union_of_subset_left hl1 Γ₂
      · exact Set.subset_union_of_subset_right hl2 Γ₁
    · rw [h3]
      apply proof.conj_intro hr1 hr2
  | @conj_elim_l Γ' f₁ f₂ h' hi' =>
     obtain ⟨Γ₀, hl', hr'⟩ := hi'
     use Γ₀
     simp_all only [true_and]
     exact proof.conj_elim_l hr'
  | @conj_elim_r Γ' f₁ f₂ h' hi' =>
     obtain ⟨Γ₀, hl', hr'⟩ := hi'
     use Γ₀
     simp_all only [true_and]
     exact proof.conj_elim_r hr'
  | @disj_intro_r Γ' f₁ f₂ h' hi' =>
    obtain ⟨Γ₀, hl', hr'⟩ := hi'
    use Γ₀
    simp_all only [true_and]
    apply proof.disj_intro_r hr'
  | @disj_intro_l Γ' f₁ f₂ h' hi' =>
    obtain ⟨Γ₀, hl', hr'⟩ := hi'
    use Γ₀
    simp_all only [true_and]
    apply proof.disj_intro_l hr'
  | @disj_elim Γ' f₁ Δ₁ g f₂ Δ₂ h1 h2 h3 hi1 hi2 hi3 =>
    obtain ⟨Γ₀, hi1l, hi1r⟩ := hi1
    obtain ⟨Δ₁', hi2l, hi2r⟩ := hi2
    obtain ⟨Δ₂', hi3l, hi3r⟩ := hi3
    let D₁ := Δ₁' \ {f₁}
    let D₂ := Δ₂' \ {f₂}
    have hD₁_sub : (↑D₁ : Set Formula) ⊆ Δ₁ := by
      intro x hx
      simp only [Finset.mem_coe] at hx
      rw [Finset.mem_sdiff] at hx
      obtain ⟨hx1, hx2⟩ := hx
      have h' := hi2l hx1
      rcases h' with hl | hr
      · exfalso
        simp_all
      · exact hr
    have hD₂_sub : (↑D₂ : Set Formula) ⊆ Δ₂ := by
      intro x hx
      simp only [Finset.mem_coe] at hx
      rw [Finset.mem_sdiff] at hx
      obtain ⟨hx1, hx2⟩ := hx
      have h' := hi3l hx1
      rcases h' with hl | hr
      · exfalso
        simp_all
      · exact hr
    have hw1 : (↑Δ₁' : Set Formula) ⊆ {f₁} ∪ ↑D₁ := by
      intro x hx
      have h' := hi2l hx
      rcases h' with hf | hΔ
      · exact mem_set_mem_union x hf
      · by_cases heq : x = f₁
        · exact mem_set_mem_union x heq
        · right
          rw [Finset.mem_coe, Finset.mem_sdiff]
          simp_all
    have hw2 : (↑Δ₂' : Set Formula) ⊆ {f₂} ∪ ↑D₂ := by
      intro x hx
      have h' := hi3l hx
      rcases h' with hf | hΔ
      · exact mem_set_mem_union x hf
      · by_cases heq : x = f₂
        · exact mem_set_mem_union x heq
        · right
          rw [Finset.mem_coe, Finset.mem_sdiff]
          simp_all
    have w2 : proof ({f₁} ∪ ↑D₁) g := derivation_monotonicity hw1 hi2r
    have w3 : proof ({f₂} ∪ ↑D₂) g := derivation_monotonicity hw2 hi3r
    use Γ₀ ∪ D₁ ∪ D₂
    constructor
    · simp only [finite_subset] at *
      rw [← coe_distrib, ← coe_distrib]
      intro x hx
      simp only [Set.mem_union] at hx
      rcases hx with (hx | hx) | hx
      · left
        left
        apply hi1l hx
      · left
        right
        exact Set.mem_of_subset_of_mem hD₁_sub hx
      · exact Set.mem_union_right (Γ' ∪ Δ₁) (hD₂_sub hx)
    · rw [← coe_distrib, ← coe_distrib]
      apply proof.disj_elim
      · apply hi1r
      · apply w2
      · apply w3
  | @imp_intro f₁ Γ' f₂ h' hi' =>
    obtain ⟨Γ₀, hil', hir'⟩ := hi'
    let D₁ := Γ₀ \ {f₁}
    have hD₁_sub : (↑D₁ : Set Formula) ⊆ Γ₀ := by
      intro x hx
      simp only [Finset.mem_coe] at hx
      rw [Finset.mem_sdiff] at hx
      obtain ⟨hx1, hx2⟩ := hx
      have h' := hil' hx1
      rcases h' with hl | hr
      · exfalso
        simp_all
      · exact Finset.mem_coe.mpr hx1
    have hw1 : (↑Γ₀ : Set Formula) ⊆ {f₁} ∪ ↑D₁ := by
      intro x hx
      have h' := hil' hx
      rcases h' with hf | hΔ
      · exact mem_set_mem_union x hf
      · by_cases heq : x = f₁
        · exact mem_set_mem_union x heq
        · right
          rw [Finset.mem_coe, Finset.mem_sdiff]
          simp_all
    obtain hw := derivation_monotonicity hw1 hir'
    use D₁
    constructor
    · intro x hx
      have hx' : x ∈ (↑Γ₀ : Set Formula) := hD₁_sub hx
      have hx'' := hil' hx'
      rcases hx'' with hl | hr
      · exfalso
        rw [Finset.mem_coe, Finset.mem_sdiff] at hx
        simp_all
      · exact hr
    · apply proof.imp_intro
      apply hw
  | @imp_elim Γ₁ Γ₂ f₁ f₂ h1 h2 hi1 hi2 =>
    obtain ⟨Γ₁', hi1l', hi1r'⟩ := hi1
    obtain ⟨Γ₂', hi2l', hi2r'⟩ := hi2
    use Γ₁' ∪ Γ₂'
    simp only [finite_subset] at *
    constructor
    · rw [←coe_distrib]
      apply union_subset_subset hi1l' hi2l'
    · rw [← coe_distrib]
      apply proof.imp_elim
      · apply hi1r'
      · apply hi2r'
  | @neg_intro f₁ Γ' h' hi' =>
    obtain ⟨Γ₀, hil', hir'⟩ := hi'
    let D₁ := Γ₀ \ {f₁}
    have hD₁_sub : (↑D₁ : Set Formula) ⊆ Γ₀ := by
      intro x hx
      simp only [Finset.mem_coe] at hx
      rw [Finset.mem_sdiff] at hx
      obtain ⟨hx1, hx2⟩ := hx
      have h' := hil' hx1
      rcases h' with hl | hr
      · exfalso
        simp_all
      · exact Finset.mem_coe.mpr hx1
    have hw1 : (↑Γ₀ : Set Formula) ⊆ {f₁} ∪ ↑D₁ := by
      intro x hx
      have h' := hil' hx
      rcases h' with hf | hΔ
      · exact mem_set_mem_union x hf
      · by_cases heq : x = f₁
        · exact mem_set_mem_union x heq
        · right
          rw [Finset.mem_coe, Finset.mem_sdiff]
          simp_all
    obtain hw := derivation_monotonicity hw1 hir'
    use D₁
    constructor
    · intro x hx
      have hx' : x ∈ (↑Γ₀ : Set Formula) := hD₁_sub hx
      have hx'' := hil' hx'
      rcases hx'' with hl | hr
      · exfalso
        rw [Finset.mem_coe, Finset.mem_sdiff] at hx
        simp_all
      · exact hr
    · apply proof.neg_intro
      apply hw
  | @neg_elim Γ₁ Γ₂ f' h1 h2 hi1 hi2 =>
    obtain ⟨Γ₁', hi1l, hi1r⟩ := hi1
    obtain ⟨Γ₂', hi2l, hi2r⟩ := hi2
    use Γ₁' ∪ Γ₂'
    simp_all only [Finset.coe_union]
    constructor
    · simp only [finite_subset]
      rw [← coe_distrib]
      exact union_subset_subset hi1l hi2l
    · apply proof.neg_elim
      · apply hi1r
      · apply hi2r
  | @contr_rule Γ' f' h' hi' =>
    obtain ⟨Γ₀, hil', hir'⟩ := hi'
    let D₁ := Γ₀ \ {f'.Neg}
    have hD₁_sub : (↑D₁ : Set Formula) ⊆ Γ₀ := by
      intro x hx
      simp only [Finset.mem_coe] at hx
      rw [Finset.mem_sdiff] at hx
      obtain ⟨hx1, hx2⟩ := hx
      have h' := hil' hx1
      rcases h' with hl | hr
      · exfalso
        simp_all
      · exact Finset.mem_coe.mpr hx1
    have hw1 : (↑Γ₀ : Set Formula) ⊆ {f'.Neg} ∪ ↑D₁ := by
      intro x hx
      have h' := hil' hx
      rcases h' with hf | hΔ
      · exact mem_set_mem_union x hf
      · by_cases heq : x = f'.Neg
        · exact mem_set_mem_union x heq
        · right
          rw [Finset.mem_coe, Finset.mem_sdiff]
          simp_all
    obtain hw := derivation_monotonicity hw1 hir'
    use D₁
    constructor
    · intro x hx
      have hx' : x ∈ (↑Γ₀ : Set Formula) := hD₁_sub hx
      have hx'' := hil' hx'
      rcases hx'' with hl | hr
      · exfalso
        rw [Finset.mem_coe, Finset.mem_sdiff] at hx
        simp_all
      · exact hr
    · apply proof.contr_rule
      apply hw
  | @int_rule Γ' h' f' hi' =>
    obtain ⟨Γ₀, hil', hir'⟩ := hi'
    use Γ₀
    simp_all only [true_and]
    apply proof.int_rule hir'

theorem compacteness_2 :
  (∀ Γ₀, finite_subset Γ₀ Γ → ¬ inconsistent Γ₀ ) → ¬ inconsistent Γ := by
  contrapose
  intro h
  simp only [not_forall, not_not]
  simp only [inconsistent] at *
  obtain ⟨ Γ₀, hl, hr ⟩ := compactness h
  use Γ₀

theorem inconsistent_or_neg_inconsisten (h : ¬ inconsistent Γ) :
  ¬ inconsistent (Γ ∪ {f}) ∨ ¬ inconsistent (Γ ∪ {f.Neg}) := by
  dsimp [inconsistent] at *
  by_contra hC
  push Not at hC
  obtain ⟨h1, h2⟩ := hC
  rw [Set.union_comm] at *
  obtain h1' := proof.neg_intro h1
  obtain h2' := proof.contr_rule h2
  obtain h3 := proof.neg_elim h1' h2'
  simp at h3
  contradiction

theorem inconsistent_supset_if_inconsistent
  (h : proof Γ f) (h' : inconsistent ({f} ∪ Γ)) : inconsistent Γ := by
  simp only [inconsistent] at *
  obtain h1 := proof.neg_intro h'
  obtain h2 := proof.neg_elim h1 h
  simp only [Set.union_self] at h2
  exact h2

theorem neg_deriv_iff_set_for_inconsistent :
   proof Γ f.Neg ↔ inconsistent ({f} ∪ Γ ) := by
  simp only [inconsistent]
  constructor
  · intro h
    have h': f ∈ ({f}: FormulaSet) := by
      exact Set.mem_singleton f
    obtain h'':= @proof.hyp {f} f h'
    obtain h''':= proof.neg_elim h h''
    exact derivation_transitivity h'' h'''
  · intro h
    apply proof.neg_intro h

theorem or_plus_neg_disj_inconsistent {f₁ f₂ : Formula} :
  inconsistent ({f₁.Disj f₂} ∪ {f₁.Neg} ∪ {f₂.Neg}) := by
  simp only [inconsistent]
  apply proof.disj_elim
  · apply @proof.hyp {f₁.Disj f₂} (f₁.Disj f₂)
    exact Set.mem_singleton (f₁.Disj f₂)
  · have h': ({f₁}: FormulaSet) ∪ {f₁.Neg} = {f₁.Neg} ∪ {f₁} := by
      exact union_commu
    rw [h']
    apply proof.neg_elim
    · apply @proof.hyp {f₁.Neg} f₁.Neg
      · exact Set.mem_singleton f₁.Neg
    · apply @proof.hyp {f₁} f₁
      · exact Set.mem_singleton f₁
  · have h': ({f₂}: FormulaSet) ∪ {f₂.Neg} = {f₂.Neg} ∪ {f₂} := by
      exact union_commu
    rw [h']
    apply proof.neg_elim
    · apply @proof.hyp {f₂.Neg} f₂.Neg
      · exact Set.mem_singleton f₂.Neg
    · apply @proof.hyp {f₂} f₂
      · exact Set.mem_singleton f₂
