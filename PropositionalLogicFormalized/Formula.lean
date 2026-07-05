import PropositionalLogicFormalized.Utils.List
import Mathlib.Logic.Encodable.Basic

set_option linter.style.header false

inductive Formula where
| False
| Var : Nat -> Formula
| Neg (f₁: Formula)
| Conj (f₁: Formula) (f₂: Formula)
| Disj (f₁: Formula) (f₂: Formula)
| Imp (f₁: Formula) (f₂: Formula)
deriving DecidableEq, Hashable, Nonempty

def Formula.toStr : (Formula) -> String
  | False => "⊥"
  | Var a => "p" ++ (String.ofList (Nat.toDigits 10 a))
  | Neg f => "¬" ++ f.toStr
  | Conj f₁ f₂ => "("++ f₁.toStr ++"∧"++ f₂.toStr ++")"
  | Disj f₁ f₂ => "("++ f₁.toStr ++"∨"++ f₂.toStr ++")"
  | Imp f₁ f₂ => "("++ f₁.toStr ++"→"++ f₂.toStr ++")"

def Formula.toNat : Formula → ℕ
  | False      => Nat.pair 0 0 + 1
  | Var n      => Nat.pair 1 n + 1
  | Neg f₁     => Nat.pair 2 f₁.toNat + 1
  | Conj f₁ f₂ => Nat.pair 3 (Nat.pair f₁.toNat f₂.toNat) + 1
  | Disj f₁ f₂ => Nat.pair 4 (Nat.pair f₁.toNat f₂.toNat) + 1
  | Imp f₁ f₂  => Nat.pair 5 (Nat.pair f₁.toNat f₂.toNat) + 1

def Formula.ofNat : ℕ → Option Formula
  | 0 => none
  | e + 1 =>
    let idx := e.unpair.1
    let c := e.unpair.2
    match idx with
    | 0 => some Formula.False
    | 1 => some (Formula.Var c)
    | 2 =>
      have : c < e + 1 := Nat.lt_succ_iff.mpr (Nat.unpair_right_le _)
      (ofNat c).map Formula.Neg
    | 3 =>
      have : c.unpair.1 < e + 1 :=
        Nat.lt_succ_iff.mpr <| le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)
      have : c.unpair.2 < e + 1 :=
        Nat.lt_succ_iff.mpr <| le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)
      do
        let f₁ <- ofNat c.unpair.1
        let f₂ <- ofNat c.unpair.2
        return Formula.Conj f₁ f₂
    | 4 =>
      have : c.unpair.1 < e + 1 :=
        Nat.lt_succ_iff.mpr <| le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)
      have : c.unpair.2 < e + 1 :=
        Nat.lt_succ_iff.mpr <| le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)
      do
        let f₁ <- ofNat c.unpair.1
        let f₂ <- ofNat c.unpair.2
        return Formula.Disj f₁ f₂
    | 5 =>
      have : c.unpair.1 < e + 1 :=
        Nat.lt_succ_iff.mpr <| le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)
      have : c.unpair.2 < e + 1 :=
        Nat.lt_succ_iff.mpr <| le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)
      do
        let f₁ <- ofNat c.unpair.1
        let f₂ <- ofNat c.unpair.2
        return Formula.Imp f₁ f₂
    | _ => none

instance : Repr (Formula) := ⟨fun t _ => Formula.toStr t⟩

theorem Formula.ofNat_toNat : ∀ (φ : Formula), Formula.ofNat (Formula.toNat φ) = some φ
  | False  => by simp [toNat, ofNat]
  | Var n => by
    simp only [toNat, ofNat, Nat.unpair_pair]
  | Neg f => by simp [toNat, ofNat, ofNat_toNat f]
  | Conj f₁ f₂ | Disj f₁ f₂ | Imp f₁ f₂ =>
    by simp [toNat, ofNat, ofNat_toNat f₁, ofNat_toNat f₂]

instance : Encodable Formula where
  encode := Formula.toNat
  decode := Formula.ofNat
  encodek := Formula.ofNat_toNat

def Formula.syntatic_identity (f₁ : Formula) (f₂ : Formula) :=
  f₁.toStr = f₂.toStr

@[grind]
def Formula.complexity : Formula -> Nat
| False | Var _  => 0
| Neg f => 1 + f.complexity
| Conj f₁ f₂ | Disj f₁ f₂ | Imp f₁ f₂ => 1 + max f₁.complexity  f₂.complexity


def Formula.LP (f : Formula) :=
  let rec count l :=
    match l with
    | [] => 0
    | h::t => if h = '(' then 1 + count t else count t
  count f.toStr.toList

def Formula.RP (f : Formula) :=
  let rec count l :=
    match l with
    | [] => 0
    | h::t => if h = ')' then 1 + count t else count t
  count f.toStr.toList


theorem Formula.LP.count_monotonicity : count (h::t) = count ([h]) + count t := by
  induction t with
  | nil =>
    simp_all only [Nat.left_eq_add]
    decide
  | cons h' t' hi =>
    simp only [count]
    split
    · simp_all
    · simp_all

theorem Formula.RP.count_monotonicity : count (h::t) = count ([h]) + count t := by
  induction t with
  | nil =>
    simp_all only [Nat.left_eq_add]
    decide
  | cons h' t' hi =>
    simp only [count]
    split
    · simp_all only [↓Char.isValue, Nat.add_zero]
    · simp_all only [↓Char.isValue, Nat.zero_add]

theorem Formula.LP.count_append_monotonicity : count (h ++ t) = count (h) + count t := by
  induction h with
  | nil =>
    simp_all only [List.nil_append, Nat.right_eq_add]
    decide
  | cons h' t' hi =>
    rw [LP.count_monotonicity]
    have h'': count (h' :: t' ++ t) = count ([h']) + count (t' ++ t) := by
      apply LP.count_monotonicity
    rw [h'']
    rw [hi]
    omega

theorem Formula.RP.count_append_monotonicity : count (h ++ t) = count (h) + count t := by
  induction h with
  | nil =>
    simp_all only [List.nil_append, Nat.right_eq_add]
    decide
  | cons h' t' hi =>
    rw [RP.count_monotonicity]
    have h'': count (h' :: t' ++ t) = count ([h']) + count (t' ++ t) := by
      apply RP.count_monotonicity
    rw [h'']
    rw [hi]
    omega

def Formula.uniformSub
  | False, _, _ => False
  | Var n, n', n'' => if n = n' then Var n'' else Var n
  | Neg f, n, n' => uniformSub f n n'
  | Conj f₁ f₂, n, n' => Conj (uniformSub f₁ n n') (uniformSub f₂ n n')
  | Disj f₁ f₂, n, n' => Disj (uniformSub f₁ n n') (uniformSub f₂ n n')
  | Imp f₁ f₂, n, n' => Imp (uniformSub f₁ n n') (uniformSub f₂ n n')


axiom dne_elim {f : Formula} : f = f.Neg.Neg
