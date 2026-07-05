
theorem iff_negative (h : ¬ a) (h' : a ↔ b) : ¬ b := by
  simp_all

theorem or_exclusion (h : ¬ p) (h' : p ∨ q) : q := by
  simp_all
