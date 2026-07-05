import PropositionalLogicFormalized.Formula

theorem to_list_eq (n : Nat) :
  ("p" ++ (String.ofList (Nat.toDigits 10 n))).toList = 'p' :: (Nat.toDigits 10 n):= by
  simp_all only [String.toList_append, String.reduceToList, String.toList_ofList, List.cons_append,
    ↓Char.isValue, List.nil_append]

theorem no_digit_char_is_lp (n : Nat) : Nat.digitChar n ≠ '(' := by
  simp_all only [↓Char.isValue, ne_eq, Char.Nat.reduceDigitCharEq, not_false_eq_true]

theorem no_digit_char_is_rp (n : Nat) : Nat.digitChar n ≠ ')' := by
  simp_all only [↓Char.isValue, ne_eq, Char.Nat.reduceDigitCharEq, not_false_eq_true]

theorem toDigitsCore_ne_lp (base fuel n : Nat) (r : List Char)
    (hr : '(' ∉ r) : '(' ∉ Nat.toDigitsCore base fuel n r := by
  induction fuel generalizing n r with
  | zero =>
    simp only [Nat.toDigitsCore]
    exact hr
  | succ f ih =>
    simp only [Nat.toDigitsCore]
    split
    · simp_all
    · simp_all

theorem toDigitsCore_ne_rp (base fuel n : Nat) (r : List Char)
    (hr : ')' ∉ r) : ')' ∉ Nat.toDigitsCore base fuel n r := by
  induction fuel generalizing n r with
  | zero =>
    simp only [Nat.toDigitsCore]
    exact hr
  | succ f ih =>
    simp only [Nat.toDigitsCore]
    split
    · simp_all
    · simp_all

theorem toDigits_ne_lp (base n : Nat) : '(' ∉ Nat.toDigits base n := by
  simp only [Nat.toDigits]
  apply toDigitsCore_ne_lp base (n+1) n []
  decide

theorem toDigits_ne_rp (base n : Nat) : ')' ∉ Nat.toDigits base n := by
  simp only [Nat.toDigits]
  apply toDigitsCore_ne_rp base (n+1) n []
  decide

theorem lpCount_pos_mem (l : List Char) (h : Formula.LP.count l ≠ 0) :
    '(' ∈ l := by
  induction l with
  | nil =>
    simp [Formula.LP.count] at h
  | cons hd tl ih =>
    simp only [Formula.LP.count] at h
    split at h
    · simp_all
    · simp_all

theorem rpCount_pos_mem (l : List Char) (h : Formula.RP.count l ≠ 0) :
    ')' ∈ l := by
  induction l with
  | nil =>
    simp [Formula.RP.count] at h
  | cons hd tl ih =>
    simp only [Formula.RP.count] at h
    split at h
    · simp_all
    · simp_all

theorem lp_count_zero (l : List Char) (h : '(' ∉ l) : Formula.LP.count l = 0 := by
  induction l with
  | nil =>
    decide
  | cons h' t' hi =>
    simp_all only [↓Char.isValue, List.mem_cons, not_or, not_false_eq_true, forall_const]
    rw [Formula.LP.count_monotonicity]
    obtain ⟨ hl, hr ⟩ := h
    simp_all only [↓Char.isValue, Nat.add_zero]
    simp only [Formula.LP.count]
    split
    · simp_all only [↓Char.isValue, not_true_eq_false]
    · simp_all only [↓Char.isValue]

theorem rp_count_zero (l : List Char) (h : ')' ∉ l) : Formula.RP.count l = 0 := by
  induction l with
  | nil =>
    decide
  | cons h' t' hi =>
    simp_all only [↓Char.isValue, List.mem_cons, not_or, not_false_eq_true, forall_const]
    rw [Formula.RP.count_monotonicity]
    obtain ⟨ hl, hr ⟩ := h
    simp_all only [↓Char.isValue, Nat.add_zero]
    simp only [Formula.RP.count]
    split
    · simp_all only [↓Char.isValue, not_true_eq_false]
    · simp_all only [↓Char.isValue]

theorem Formula.LP.count_digits_zero : Formula.LP.count (Nat.toDigits 10 a) = 0 := by
  obtain h':= toDigits_ne_lp 10 a
  apply lp_count_zero (Nat.toDigits 10 a) h'

theorem Formula.RP.count_digits_zero (a : Nat) : Formula.RP.count (Nat.toDigits 10 a) = 0 := by
  obtain h':= toDigits_ne_rp 10 a
  apply rp_count_zero (Nat.toDigits 10 a) h'

theorem formula_balanced {f : Formula} : f.LP = f.RP := by
  have h1l:  Formula.LP.count ['('] = 1 := by
    decide
  have h1r:  Formula.RP.count ['('] = 0 := by
    decide
  have h2l:  Formula.LP.count ['∧'] = 0 := by
    decide
  have h2r:  Formula.RP.count ['∧'] = 0 := by
    decide
  have h3l:  Formula.LP.count [')'] = 0 := by
    decide
  have h3r:  Formula.RP.count [')'] = 1 := by
    decide
  have h4l:  Formula.LP.count ['∨'] = 0 := by
    decide
  have h4r:  Formula.RP.count ['∨'] = 0 := by
    decide
  have h5l:  Formula.LP.count ['→'] = 0 := by
    decide
  have h5r:  Formula.RP.count ['→'] = 0 := by
    decide
  have h6l:  Formula.LP.count ['p'] = 0 := by
    decide
  have h6r:  Formula.RP.count ['p'] = 0 := by
    decide
  induction f with
  | False =>
    decide
  | Var a =>
    simp only [Formula.LP, Formula.RP, Formula.toStr]
    rw [to_list_eq, Formula.RP.count_monotonicity, Formula.LP.count_monotonicity]
    simp_all only [↓Char.isValue, Nat.zero_add]
    rw [Formula.RP.count_digits_zero, Formula.LP.count_digits_zero]
  | Neg f hi =>
    simp only [Formula.LP, Formula.RP, Formula.toStr]
    have hh :∀ {f: Formula},  ("¬" ++ f.toStr).toList = ('¬' :: f.toStr.toList) := by
      simp_all only [↓Char.isValue, String.toList_append, String.reduceToList, List.cons_append,
        List.nil_append, implies_true]
    rw [hh, Formula.LP.count_monotonicity, Formula.RP.count_monotonicity]
    simp only [Formula.LP, Formula.RP] at hi
    rw [hi]
    rfl
  | Conj f₁ f₂ hi₁ hi₂  =>
    simp_all only [Formula.LP, Formula.RP, Formula.toStr]
    have hh :
      ("(" ++ f₁.toStr ++ "∧" ++ f₂.toStr ++ ")").toList =
        ('(' :: (f₁.toStr.toList ++ '∧' :: (f₂.toStr.toList ++ [')']))):= by
      simp_all only [↓Char.isValue, String.toList_append, String.reduceToList, List.cons_append,
        List.nil_append, List.append_assoc]
    rw [hh, Formula.LP.count_monotonicity, Formula.RP.count_monotonicity]
    rw [h1l, h1r]
    simp only [Formula.LP.count_append_monotonicity, Formula.RP.count_append_monotonicity]
    rw [hi₁]
    rw [Formula.LP.count_monotonicity, Formula.RP.count_monotonicity]
    simp only [Formula.LP.count_append_monotonicity, Formula.RP.count_append_monotonicity]
    rw[hi₂]
    simp_all
    omega
  | Disj  f₁ f₂ hi₁ hi₂  =>
    simp_all only [Formula.LP, Formula.RP, Formula.toStr]
    have hh :
      ("(" ++ f₁.toStr ++ "∨" ++ f₂.toStr ++ ")").toList =
        ('(' :: (f₁.toStr.toList ++ '∨' :: (f₂.toStr.toList ++ [')']))):= by
      simp_all only [↓Char.isValue, String.toList_append, String.reduceToList, List.cons_append,
        List.nil_append, List.append_assoc]
    rw [hh, Formula.LP.count_monotonicity, Formula.RP.count_monotonicity]
    rw [h1l, h1r]
    simp only [Formula.LP.count_append_monotonicity, Formula.RP.count_append_monotonicity]
    rw [hi₁]
    rw [Formula.LP.count_monotonicity, Formula.RP.count_monotonicity]
    simp only [Formula.LP.count_append_monotonicity, Formula.RP.count_append_monotonicity]
    rw[hi₂]
    simp_all
    omega
  | Imp  f₁ f₂ hi₁ hi₂ =>
    simp_all only [Formula.LP, Formula.RP, Formula.toStr]
    have hh :
      ("(" ++ f₁.toStr ++ "→" ++ f₂.toStr ++ ")").toList =
        ('(' :: (f₁.toStr.toList ++ '→' :: (f₂.toStr.toList ++ [')']))):= by
      simp_all only [↓Char.isValue, String.toList_append, String.reduceToList, List.cons_append,
        List.nil_append, List.append_assoc]
    rw [hh, Formula.LP.count_monotonicity, Formula.RP.count_monotonicity]
    rw [h1l, h1r]
    simp only [Formula.LP.count_append_monotonicity, Formula.RP.count_append_monotonicity]
    rw [hi₁]
    rw [Formula.LP.count_monotonicity, Formula.RP.count_monotonicity]
    simp only [Formula.LP.count_append_monotonicity, Formula.RP.count_append_monotonicity]
    rw[hi₂]
    simp_all
    omega

def Formula.properInitialSegements (f : Formula) :=
  let rec generate l (acc : List (List Char)) :=
    match l with
    | [] => acc
    | [_] => acc
    | h::t => let newsub := (acc[0]! ++ [h])
    generate t (newsub::acc)
  match f with
  | False => [[]]
  | Var _ => [[]]
  | Neg f => (properInitialSegements f).map ('¬'::·)
  | Conj f₁ f₂ =>
    let left   := (properInitialSegements f₁).map ('('::·)
    let f₁Full := '(' :: f₁.toStr.toList
    let middle := f₁Full ++ ['∧']
    let right  := (properInitialSegements f₂).map (middle ++ ·)
    left ++ [f₁Full] ++ right ++ [middle ++ f₂.toStr.toList]
  | Disj f₁ f₂ =>
    let left   := (properInitialSegements f₁).map ('('::·)
    let f₁Full := '(' :: f₁.toStr.toList
    let middle := f₁Full ++ ['∨']
    let right  := (properInitialSegements f₂).map (middle ++ ·)
    left ++ [f₁Full] ++ right ++ [middle ++ f₂.toStr.toList]
  | Imp f₁ f₂ =>
    let left   := (properInitialSegements f₁).map ('('::·)
    let f₁Full := '(' :: f₁.toStr.toList
    let middle := f₁Full ++ ['→']
    let right  := (properInitialSegements f₂).map (middle ++·)
    left ++ [f₁Full] ++ right ++ [middle ++ f₂.toStr.toList]


theorem Formula.nosubformula_balanced {f : Formula} {sb : List Char} :
  sb ∈ (properInitialSegements f) → Formula.LP.count sb ≥ Formula.RP.count sb := by
  induction f generalizing sb with
  | False =>
    intro h1
    have h' : properInitialSegements Formula.False = [[]] := by decide
    have h'' : sb = [] := by simp_all
    rw [h'']; decide
  | Var n =>
    have h' : properInitialSegements (Formula.Var n) = [[]] := by
      unfold properInitialSegements
      rfl
    intro h
    simp_all only [List.mem_cons, List.not_mem_nil, or_false, ge_iff_le]
    decide
  | Neg f hi =>
    intro h1
    simp only [properInitialSegements] at h1
    simp_all only [ge_iff_le, ↓Char.isValue, List.mem_map]
    obtain ⟨ w, ⟨ h2', h3 ⟩ ⟩ := h1
    rw [← h3]
    rw [LP.count_monotonicity, RP.count_monotonicity]
    have hw: LP.count w ≥ RP.count w := by
      apply hi h2'
    have hLP : LP.count ['¬'] = 0 := by decide
    have hRP : RP.count ['¬'] = 0 := by decide
    rw [hLP, hRP]
    simp only [Nat.zero_add, ge_iff_le]
    exact hw
  | Conj f₁ f₂ hi₁ hi₂  =>
    intro h1
    simp only [properInitialSegements] at h1
    simp_all only [ge_iff_le, ↓Char.isValue, List.cons_append, List.append_assoc, List.nil_append,
      List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
    obtain h1l | h1r := h1
    · obtain ⟨ w, ⟨ h2l , h2r ⟩ ⟩ := h1l
      rw [← h2r, LP.count_monotonicity, RP.count_monotonicity]
      have hLP : LP.count ['('] = 1 := by decide
      have hRP : RP.count ['('] = 0 := by decide
      rw [hLP, hRP]
      have hw := hi₁ h2l
      omega
    · obtain  h2l |  h2r := h1r
      · rw [h2l, LP.count_monotonicity, RP.count_monotonicity]
        have hLP : LP.count ['('] = 1 := by decide
        have hRP : RP.count ['('] = 0 := by decide
        rw [hLP,hRP]
        have hf₁ := @formula_balanced f₁
        unfold LP RP at hf₁
        omega
      · obtain h3l | h3r := h2r
        · obtain ⟨ w, ⟨ h4l , h4r ⟩ ⟩ := h3l
          rw [←h4r, LP.count_monotonicity, RP.count_monotonicity,
            LP.count_append_monotonicity, RP.count_append_monotonicity]
          have hLP : LP.count ['('] = 1 := by decide
          have hRP : RP.count ['('] = 0 := by decide
          rw [hLP, hRP]
          simp only [↓Char.isValue, Nat.zero_add, ge_iff_le]
          rw [LP.count_monotonicity, RP.count_monotonicity]
          have hLP' : LP.count ['∧'] = 0 := by decide
          have hRP' : RP.count ['∧'] = 0 := by decide
          rw [hLP', hRP']
          simp only [Nat.zero_add, ge_iff_le]
          have hf₁ := @formula_balanced f₁
          unfold LP RP at hf₁
          rw [hf₁]
          have hw := hi₂ h4l
          omega
        · rw [h3r, LP.count_monotonicity, RP.count_monotonicity, LP.count_append_monotonicity,
            RP.count_append_monotonicity]
          have hLP : LP.count ['('] = 1 := by decide
          have hRP : RP.count ['('] = 0 := by decide
          rw [hLP, hRP]
          simp only [↓Char.isValue, Nat.zero_add, ge_iff_le]
          rw [LP.count_monotonicity, RP.count_monotonicity]
          have hLP' : LP.count ['∧'] = 0 := by decide
          have hRP' : RP.count ['∧'] = 0 := by decide
          rw [hLP', hRP']
          simp only [Nat.zero_add, ge_iff_le]
          have hf₁ := @formula_balanced f₁
          --have hf₁ := @formula_balanced f₁
          unfold LP RP at hf₁
          rw [hf₁]
          have hf₂ := @formula_balanced f₂
          --have hf₁ := @formula_balanced f₁
          unfold LP RP at hf₂
          rw [hf₂]
          omega
  | Disj f₁ f₂ hi₁ hi₂ =>
    intro h1
    simp only [properInitialSegements] at h1
    simp_all only [ge_iff_le, ↓Char.isValue, List.cons_append, List.append_assoc, List.nil_append,
      List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
    obtain h1l | h1r := h1
    · obtain ⟨ w, ⟨ h2l , h2r ⟩ ⟩ := h1l
      rw [← h2r, LP.count_monotonicity, RP.count_monotonicity]
      have hLP : LP.count ['('] = 1 := by decide
      have hRP : RP.count ['('] = 0 := by decide
      rw [hLP, hRP]
      have hw := hi₁ h2l
      omega
    · obtain  h2l |  h2r := h1r
      · rw [h2l, LP.count_monotonicity, RP.count_monotonicity]
        have hLP : LP.count ['('] = 1 := by decide
        have hRP : RP.count ['('] = 0 := by decide
        rw [hLP,hRP]
        have hf₁ := @formula_balanced f₁
        unfold LP RP at hf₁
        omega
      · obtain h3l | h3r := h2r
        · obtain ⟨ w, ⟨ h4l , h4r ⟩ ⟩ := h3l
          rw [←h4r, LP.count_monotonicity,
            RP.count_monotonicity, LP.count_append_monotonicity, RP.count_append_monotonicity]
          have hLP : LP.count ['('] = 1 := by decide
          have hRP : RP.count ['('] = 0 := by decide
          rw [hLP, hRP]
          simp only [↓Char.isValue, Nat.zero_add, ge_iff_le]
          rw [LP.count_monotonicity, RP.count_monotonicity]
          have hLP' : LP.count ['∨'] = 0 := by decide
          have hRP' : RP.count ['∨'] = 0 := by decide
          rw [hLP', hRP']
          simp only [Nat.zero_add, ge_iff_le]
          have hf₁ := @formula_balanced f₁
          unfold LP RP at hf₁
          rw [hf₁]
          have hw := hi₂ h4l
          omega
        · rw [h3r, LP.count_monotonicity, RP.count_monotonicity,
            LP.count_append_monotonicity, RP.count_append_monotonicity]
          have hLP : LP.count ['('] = 1 := by decide
          have hRP : RP.count ['('] = 0 := by decide
          rw [hLP, hRP]
          simp only [↓Char.isValue, Nat.zero_add, ge_iff_le]
          rw [LP.count_monotonicity, RP.count_monotonicity]
          have hLP' : LP.count ['∨'] = 0 := by decide
          have hRP' : RP.count ['∨'] = 0 := by decide
          rw [hLP', hRP']
          simp only [Nat.zero_add, ge_iff_le]
          have hf₁ := @formula_balanced f₁
          unfold LP RP at hf₁
          rw [hf₁]
          have hf₂ := @formula_balanced f₂
          unfold LP RP at hf₂
          rw [hf₂]
          omega
  | Imp f₁ f₂ hi₁ hi₂ =>
    intro h1
    simp only [properInitialSegements] at h1
    simp_all only [ge_iff_le, ↓Char.isValue, List.cons_append, List.append_assoc, List.nil_append,
      List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
    obtain h1l | h1r := h1
    · obtain ⟨ w, ⟨ h2l , h2r ⟩ ⟩ := h1l
      rw [← h2r, LP.count_monotonicity, RP.count_monotonicity]
      have hLP : LP.count ['('] = 1 := by decide
      have hRP : RP.count ['('] = 0 := by decide
      rw [hLP, hRP]
      have hw := hi₁ h2l
      omega
    · obtain  h2l |  h2r := h1r
      · rw [h2l, LP.count_monotonicity, RP.count_monotonicity]
        have hLP : LP.count ['('] = 1 := by decide
        have hRP : RP.count ['('] = 0 := by decide
        rw [hLP,hRP]
        have hf₁ := @formula_balanced f₁
        unfold LP RP at hf₁
        omega
      · obtain h3l | h3r := h2r
        · obtain ⟨ w, ⟨ h4l , h4r ⟩ ⟩ := h3l
          rw [←h4r, LP.count_monotonicity,
            RP.count_monotonicity, LP.count_append_monotonicity, RP.count_append_monotonicity]
          have hLP : LP.count ['('] = 1 := by decide
          have hRP : RP.count ['('] = 0 := by decide
          rw [hLP, hRP]
          simp only [↓Char.isValue, Nat.zero_add, ge_iff_le]
          rw [LP.count_monotonicity, RP.count_monotonicity]
          have hLP' : LP.count ['→'] = 0 := by decide
          have hRP' : RP.count ['→'] = 0 := by decide
          rw [hLP', hRP']
          simp only [Nat.zero_add, ge_iff_le]
          have hf₁ := @formula_balanced f₁
          unfold LP RP at hf₁
          rw [hf₁]
          have hw := hi₂ h4l
          omega
        · rw [h3r, LP.count_monotonicity,
            RP.count_monotonicity, LP.count_append_monotonicity, RP.count_append_monotonicity]
          have hLP : LP.count ['('] = 1 := by decide
          have hRP : RP.count ['('] = 0 := by decide
          rw [hLP, hRP]
          simp only [↓Char.isValue, Nat.zero_add, ge_iff_le]
          rw [LP.count_monotonicity, RP.count_monotonicity]
          have hLP' : LP.count ['→'] = 0 := by decide
          have hRP' : RP.count ['→'] = 0 := by decide
          rw [hLP', hRP']
          simp only [Nat.zero_add, ge_iff_le]
          have hf₁ := @formula_balanced f₁
          unfold LP RP at hf₁
          rw [hf₁]
          have hf₂ := @formula_balanced f₂
          unfold LP RP at hf₂
          rw [hf₂]
          omega


theorem Formula.nosubformula_balanced_2 {f} {sb} :
  sb ∈ properInitialSegements f → (LP.count sb > 0 → LP.count sb > RP.count sb) := by
  induction f generalizing sb with
  | False =>
    intro h1 h2
    have h' : properInitialSegements Formula.False = [[]] := by decide
    have h'' : sb = [] := by
      simp_all
    have h''': LP.count [] = 0 := by
      trivial
    rw [h''] at h2
    have hrp: RP.count [] = 0 := by
      trivial
    rw [h'''] at h2
    rw [h'',h''', hrp]
    exact h2
  | Var n =>
    intro h1 h2
    have h' : properInitialSegements (Formula.Var n) = [[]] := by
      unfold properInitialSegements
      decide
    have h'' : sb = [] := by
      simp_all
    have hrp: RP.count [] = 0 := by
      trivial
    have hlp: LP.count [] = 0 := by
      trivial
    rw[h'', hlp]at h2
    rw[h'',hrp, hlp]
    exact h2
  | Neg f hi =>
    intro h1 h2
    simp only [properInitialSegements] at h1
    simp_all only [gt_iff_lt, ↓Char.isValue, List.mem_map]
    obtain ⟨ w, ⟨ h1l, h1r⟩  ⟩ := h1
    rw [← h1r, LP.count_monotonicity, RP.count_monotonicity]
    rw [← h1r, LP.count_monotonicity] at h2
    have h': LP.count ['¬'] = 0 := by
      trivial
    have h'': RP.count ['¬'] = 0 := by
      trivial
    rw [h', h'']
    rw [h'] at h2
    simp only [Nat.zero_add] at h2
    simp_all only [↓Char.isValue, Nat.zero_add]
  | Conj f₁ f₂ hi₁ hi₂ =>
    intro h1 h2
    simp only [properInitialSegements] at h1
    simp_all only [gt_iff_lt, ↓Char.isValue, List.cons_append, List.append_assoc, List.nil_append,
      List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
    obtain h1l | h1r := h1
    · obtain ⟨ w, ⟨ h2l, h2r ⟩ ⟩ := h1l
      rw [← h2r, LP.count_monotonicity, RP.count_monotonicity]
      have h': LP.count ['('] = 1 := by
        trivial
      have h'': RP.count ['('] = 0 := by
        trivial
      rw [h', h'']
      rw [← h2r, LP.count_monotonicity, h'] at h2
      have hw: LP.count w ≥ RP.count w := @nosubformula_balanced f₁ w h2l
      omega
    · obtain h2l | h2l := h1r
      · rw [h2l, LP.count_monotonicity, RP.count_monotonicity]
        have h': LP.count ['('] = 1 := by
          trivial
        have h'': RP.count ['('] = 0 := by
          trivial
        rw [h', h'']
        have hf₁: LP.count f₁.toStr.toList = RP.count f₁.toStr.toList := by
          have hf₁' : LP f₁ = RP f₁ := @formula_balanced f₁
          unfold LP RP at hf₁'
          exact hf₁'
        rw [hf₁]
        simp
      · obtain ⟨ w, ⟨ h4l, h4r ⟩ ⟩ | h3r := h2l
        · rw [← h4r, LP.count_monotonicity, RP.count_monotonicity]
          have h': LP.count ['('] = 1 := by
            trivial
          have h'': RP.count ['('] = 0 := by
            trivial
          rw [h', h'', LP.count_append_monotonicity,
            RP.count_append_monotonicity, LP.count_monotonicity, RP.count_monotonicity]
          have h1': LP.count ['∧'] = 0 := by
            trivial
          have h1'': RP.count ['∧'] = 0 := by
            trivial
          rw [h1', h1'']
          have hf₁: LP.count f₁.toStr.toList = RP.count f₁.toStr.toList := by
            have hf₁' : LP f₁ = RP f₁ := @formula_balanced f₁
            unfold LP RP at hf₁'
            exact hf₁'
          rw [hf₁]
          have hw := @nosubformula_balanced f₂ w h4l
          omega
        · rw [h3r, LP.count_monotonicity, RP.count_monotonicity,
            LP.count_append_monotonicity, RP.count_append_monotonicity]
          have h': LP.count ['('] = 1 := by
            trivial
          have h'': RP.count ['('] = 0 := by
            trivial
          rw [h', h'', LP.count_monotonicity, RP.count_monotonicity]
          have h1': LP.count ['∧'] = 0 := by
            trivial
          have h1'': RP.count ['∧'] = 0 := by
            trivial
          rw [h1', h1'']
          have hf₁: LP.count f₁.toStr.toList = RP.count f₁.toStr.toList := by
            have hf₁' : LP f₁ = RP f₁ := @formula_balanced f₁
            unfold LP RP at hf₁'
            exact hf₁'
          have hf₂: LP.count f₂.toStr.toList = RP.count f₂.toStr.toList := by
            have hf₂' : LP f₂ = RP f₂ := @formula_balanced f₂
            unfold LP RP at hf₂'
            exact hf₂'
          rw [hf₂, hf₁]
          simp_all only [↓Char.isValue, Nat.zero_add, Nat.lt_add_left_iff_pos, Nat.lt_add_one]
  | Disj f₁ f₂ hi₁ hi₂ =>
    intro h1 h2
    simp only [properInitialSegements] at h1
    simp_all only [gt_iff_lt, ↓Char.isValue, List.cons_append, List.append_assoc, List.nil_append,
      List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
    obtain h1l | h1r := h1
    · obtain ⟨ w, ⟨ h2l, h2r ⟩ ⟩ := h1l
      rw [← h2r, LP.count_monotonicity, RP.count_monotonicity]
      have h': LP.count ['('] = 1 := by
        trivial
      have h'': RP.count ['('] = 0 := by
        trivial
      rw [h', h'']
      rw [← h2r, LP.count_monotonicity, h'] at h2
      have hw: LP.count w ≥ RP.count w := @nosubformula_balanced f₁ w h2l
      omega
    · obtain h2l | h2l := h1r
      · rw [h2l, LP.count_monotonicity, RP.count_monotonicity]
        have h': LP.count ['('] = 1 := by
          trivial
        have h'': RP.count ['('] = 0 := by
          trivial
        rw [h', h'']
        have hf₁: LP.count f₁.toStr.toList = RP.count f₁.toStr.toList := by
          have hf₁' : LP f₁ = RP f₁ := @formula_balanced f₁
          unfold LP RP at hf₁'
          exact hf₁'
        rw [hf₁]
        simp
      · obtain ⟨ w, ⟨ h4l, h4r ⟩ ⟩ | h3r := h2l
        · rw [← h4r, LP.count_monotonicity, RP.count_monotonicity]
          have h': LP.count ['('] = 1 := by
            trivial
          have h'': RP.count ['('] = 0 := by
            trivial
          rw [h', h'', LP.count_append_monotonicity,
            RP.count_append_monotonicity, LP.count_monotonicity, RP.count_monotonicity]
          have h1': LP.count ['∨'] = 0 := by
            trivial
          have h1'': RP.count ['∨'] = 0 := by
            trivial
          rw [h1', h1'']
          have hf₁: LP.count f₁.toStr.toList = RP.count f₁.toStr.toList := by
            have hf₁' : LP f₁ = RP f₁ := @formula_balanced f₁
            unfold LP RP at hf₁'
            exact hf₁'
          rw [hf₁]
          have hw := @nosubformula_balanced f₂ w h4l
          omega
        · rw [h3r, LP.count_monotonicity, RP.count_monotonicity,
            LP.count_append_monotonicity, RP.count_append_monotonicity]
          have h': LP.count ['('] = 1 := by
            trivial
          have h'': RP.count ['('] = 0 := by
            trivial
          rw [h', h'', LP.count_monotonicity, RP.count_monotonicity]
          have h1': LP.count ['∨'] = 0 := by
            trivial
          have h1'': RP.count ['∨'] = 0 := by
            trivial
          rw [h1', h1'']
          have hf₁: LP.count f₁.toStr.toList = RP.count f₁.toStr.toList := by
            have hf₁' : LP f₁ = RP f₁ := @formula_balanced f₁
            unfold LP RP at hf₁'
            exact hf₁'
          have hf₂: LP.count f₂.toStr.toList = RP.count f₂.toStr.toList := by
            have hf₂' : LP f₂ = RP f₂ := @formula_balanced f₂
            unfold LP RP at hf₂'
            exact hf₂'
          rw [hf₂, hf₁]
          simp_all only [↓Char.isValue, Nat.zero_add, Nat.lt_add_left_iff_pos, Nat.lt_add_one]
  | Imp f₁ f₂ hi₁ hi₂ =>
    intro h1 h2
    simp only [properInitialSegements] at h1
    simp_all only [gt_iff_lt, ↓Char.isValue, List.cons_append, List.append_assoc, List.nil_append,
      List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
    obtain h1l | h1r := h1
    · obtain ⟨ w, ⟨ h2l, h2r ⟩ ⟩ := h1l
      rw [← h2r, LP.count_monotonicity, RP.count_monotonicity]
      have h': LP.count ['('] = 1 := by
        trivial
      have h'': RP.count ['('] = 0 := by
        trivial
      rw [h', h'']
      rw [← h2r, LP.count_monotonicity, h'] at h2
      have hw: LP.count w ≥ RP.count w := @nosubformula_balanced f₁ w h2l
      omega
    · obtain h2l | h2l := h1r
      · rw [h2l, LP.count_monotonicity, RP.count_monotonicity]
        have h': LP.count ['('] = 1 := by
          trivial
        have h'': RP.count ['('] = 0 := by
          trivial
        rw [h', h'']
        have hf₁: LP.count f₁.toStr.toList = RP.count f₁.toStr.toList := by
          have hf₁' : LP f₁ = RP f₁ := @formula_balanced f₁
          unfold LP RP at hf₁'
          exact hf₁'
        rw [hf₁]
        simp only [Nat.zero_add, Nat.lt_add_left_iff_pos, Nat.lt_add_one]
      · obtain ⟨ w, ⟨ h4l, h4r ⟩ ⟩ | h3r := h2l
        · rw [← h4r, LP.count_monotonicity, RP.count_monotonicity]
          have h': LP.count ['('] = 1 := by
            trivial
          have h'': RP.count ['('] = 0 := by
            trivial
          rw [h', h'', LP.count_append_monotonicity,
            RP.count_append_monotonicity, LP.count_monotonicity, RP.count_monotonicity]
          have h1': LP.count ['→'] = 0 := by
            trivial
          have h1'': RP.count ['→'] = 0 := by
            trivial
          rw [h1', h1'']
          have hf₁: LP.count f₁.toStr.toList = RP.count f₁.toStr.toList := by
            have hf₁' : LP f₁ = RP f₁ := @formula_balanced f₁
            unfold LP RP at hf₁'
            exact hf₁'
          rw [hf₁]
          have hw := @nosubformula_balanced f₂ w h4l
          omega
        · rw [h3r, LP.count_monotonicity, RP.count_monotonicity,
            LP.count_append_monotonicity, RP.count_append_monotonicity]
          have h': LP.count ['('] = 1 := by
            trivial
          have h'': RP.count ['('] = 0 := by
            trivial
          rw [h', h'', LP.count_monotonicity, RP.count_monotonicity]
          have h1': LP.count ['→'] = 0 := by
            trivial
          have h1'': RP.count ['→'] = 0 := by
            trivial
          rw [h1', h1'']
          have hf₁: LP.count f₁.toStr.toList = RP.count f₁.toStr.toList := by
            have hf₁' : LP f₁ = RP f₁ := @formula_balanced f₁
            unfold LP RP at hf₁'
            exact hf₁'
          have hf₂: LP.count f₂.toStr.toList = RP.count f₂.toStr.toList := by
            have hf₂' : LP f₂ = RP f₂ := @formula_balanced f₂
            unfold LP RP at hf₂'
            exact hf₂'
          rw [hf₂, hf₁]
          simp_all only [↓Char.isValue, Nat.zero_add, Nat.lt_add_left_iff_pos, Nat.lt_add_one]

theorem Formula.noproperintialsegmet_is_formula {f} {sb} :
  sb ∈ properInitialSegements f → sb ≠ f.toStr.toList := by
  induction f generalizing sb with
  | False =>
    intro h
    have h' : properInitialSegements Formula.False = [[]] := by decide
    have h'' : sb = [] := by
      simp_all
    have h''' : ['⊥'] = False.toStr.toList := by
      trivial
    rw [h'', ← h''']
    trivial
  | Var n =>
    intro hk
    have h' : properInitialSegements (Formula.Var n) = [[]] := by
      unfold properInitialSegements
      decide
    have h'' : sb = [] := by
      simp_all
    simp_all only [List.mem_cons, List.not_mem_nil, or_false, ne_eq, List.nil_eq,
      String.toList_eq_nil_iff]
    unfold toStr
    simp_all only [String.append_eq_empty_iff, String.reduceEq, String.ofList_eq_empty_iff,
      Nat.toDigits_ne_nil, and_self, not_false_eq_true]
  | Neg f hi =>
    intro h1
    simp only [properInitialSegements] at h1
    simp_all only [ne_eq, ↓Char.isValue, List.mem_map]
    obtain ⟨ w, ⟨ h1l, h1r ⟩ ⟩ := h1
    simp only [toStr]
    rw [← h1r]
    have hw := hi h1l
    simp only [↓Char.isValue, String.toList_append, String.reduceToList, List.cons_append,
      List.nil_append, List.cons.injEq, true_and, ne_eq]
    apply hw
  | Conj f₁ f₂ hi₁ hi₂ =>
    intro h1 h2
    have hbal2 := Formula.nosubformula_balanced_2 h1
    rw [h2] at hbal2
    have hfull : Formula.LP.count (f₁.Conj f₂).toStr.toList =
             Formula.RP.count (f₁.Conj f₂).toStr.toList := formula_balanced
    have hlp_pos : Formula.LP.count (f₁.Conj f₂).toStr.toList > 0 := by
      simp only [Formula.toStr]
      simp_all only [ne_eq, gt_iff_lt, lt_self_iff_false, imp_false, not_lt, Nat.le_zero_eq,
        String.toList_append, String.reduceToList, List.cons_append, ↓Char.isValue, List.nil_append,
        List.append_assoc]
      rw [LP.count_monotonicity]
      have h': LP.count ['('] = 1 := by decide
      rw[h']
      simp_all
      omega
    omega
  | Disj f₁ f₂ hi₁ hi₂ =>
    intro h1 h2
    have hbal2 := Formula.nosubformula_balanced_2 h1
    rw [h2] at hbal2
    have hfull : Formula.LP.count (f₁.Disj f₂).toStr.toList =
             Formula.RP.count (f₁.Disj f₂).toStr.toList := formula_balanced
    have hlp_pos : Formula.LP.count (f₁.Disj f₂).toStr.toList > 0 := by
      simp only [Formula.toStr]
      simp_all only [ne_eq, gt_iff_lt, lt_self_iff_false, imp_false, not_lt, Nat.le_zero_eq,
        String.toList_append, String.reduceToList, List.cons_append, ↓Char.isValue, List.nil_append,
        List.append_assoc]
      rw [LP.count_monotonicity]
      have h': LP.count ['('] = 1 := by decide
      rw [h']
      simp_all
      omega
    omega
  | Imp f₁ f₂ hi₁ hi₂  =>
    intro h1 h2
    have hbal2 := Formula.nosubformula_balanced_2 h1
    rw [h2] at hbal2
    have hfull : Formula.LP.count (f₁.Imp f₂).toStr.toList =
             Formula.RP.count (f₁.Imp f₂).toStr.toList := formula_balanced
    have hlp_pos : Formula.LP.count (f₁.Imp f₂).toStr.toList > 0 := by
      simp only [Formula.toStr]
      simp_all only [ne_eq, gt_iff_lt, lt_self_iff_false, imp_false, not_lt, Nat.le_zero_eq,
        String.toList_append, String.reduceToList, List.cons_append, ↓Char.isValue, List.nil_append,
        List.append_assoc]
      rw [LP.count_monotonicity]
      have h': LP.count ['('] = 1 := by decide
      rw[h']
      simp_all
      omega
    omega
