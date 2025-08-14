import Mathlib.Tactic

set_option linter.unusedVariables false

theorem eg1 : True := by
  trivial

theorem eg2 (P : Prop) (h : False) : P := by
  exact False.elim h

section

variable (P Q : Prop)

example (h : 2 < 3) (i : 3 < 5) : 3 < 5 → 2 < 3  := by
  intro
  exact h

example (h : 3 < 5) (i : 3 < 5 → 2 < 3) : 2 < 3  := by
  exact i h

example (P Q R : Prop) (p : P) (h : Q → R) (j : P → Q) : R := h <| j p

example (h : P → False) : ¬ P := by
  exact h

example   (p : P)   (h : ¬ P) : False := h p
example : (p : P) → (h : ¬ P) → False := fun p => fun h => h p

def f1 (x : Nat) (y : Nat) : Nat := x + y
def f2 : (n : Nat) → (Nat → Nat) := fun x y => x + y

example : ∀ (n : Nat), n >= 0 := by
  exact Nat.zero_le

example (p : ∀ (n : Nat), n > 100) : 5 > 100 := by
  apply p

example (m n : Nat) (p : n > m) : ∃ x, x > m := by
  -- exact ⟨n, p⟩
  use n

example (P : Prop) (h : ∃ (x : Nat), P) : P := by
  rcases h with ⟨w, p⟩
  exact p

#check by_contradiction  -- classical logic

end
