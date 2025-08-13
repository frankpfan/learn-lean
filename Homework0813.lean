import Mathlib.Tactic

-- `Exercise 1:` Please define a function `f1` with mathematical formula given by
-- `f1 : ℕ × ℕ × ℕ → ℕ, (a, b, c, d) ↦ (a + c) * (d + b)`
-- You are required to use `fun`.
def f1 := fun (a b c d : Nat) => (a + c) * (b + d)

-- `Exercise 2:` Please define a function `f2` with mathematical formula given by
-- `f2 : ℕ × ℕ × ℕ → ℕ, (a, b, c, d) ↦ (a + c) * (d + b)`
-- You are required to use the tactic `intro`.
def f2 : Nat × Nat × Nat × Nat → Nat := by
  intro ⟨a, b, c, d⟩
  exact (a + c) * (b + d)

-- `Exercise 3:` Please define a function `f3 : ℕ → (ℕ × ℕ × ℕ → ℕ)`, satisfying that
-- `∀ a, b, c, d : ℕ, f3(c)(a,b,d)=f2(a,b,c,d)`,
-- where `f2` is the function in `Exercise 2`.
def f3 : Nat → (Nat × Nat × Nat → Nat) := by
  intro c ⟨a, b, d⟩
  exact f2 ⟨a, b, c, d⟩

-- `Exercise 4:` Please define 2 dependent functions, i.e. provide the term(s) of the corresponding dependent function type(s). No `sorry` or external variable is allowed.
def f4 (n : Nat) := n
def f5 (m n : Nat) := m + n

-- `Exercise 5:` Please give 2 dependent functions types which is impossible to construct a term.
-- You should explain the reason.
def t1 := (n : Nat) → False
def t2 := (A : Type) → A

-- `Exercise 6:` Consider the following functions:
def g1 : Nat → Nat → Nat → Nat → Nat := λ a b c d ↦ (a + b) * (c + d)
def g2 : Nat → Nat → Nat → Nat → Nat := by
  intro w x y z
  exact y * w + x * y + z * w + x * z
-- Please prove that these two functions are equal:
example : g1 = g2 := by
  funext
  unfold g1 g2
  rw [mul_add, add_mul, add_mul, ← add_assoc]
  nth_rw 1 [mul_comm]  -- 1 3
  nth_rw 3 [mul_comm]  -- 3 0
-- `Tips:` You can try `unfold g1 g2` at certain point in your proof.

-- `Exercise 7:` Consider the following functions:
def g1' : Nat → Nat → Nat → Nat → Nat := fun a b c d => (a - b) * (c - d)  -- a * c - a * d - b * c + b * d
def g2' : Nat → Nat → Nat → Nat → Nat := by
  intro w x y z
  exact w * y - y * x - w * z + z * x
  -- a * c - c * b - a * d + d * b
-- Please `TRY` to prove that these two functions are equal.
--- They aren't equal, so prove its negation.
example : ¬ g1' = g2' := by
  intro h
  have (a b c d : Nat) : g1' a b c d = g2' a b c d := by rw [h]
  have := this 1 2 3 4
  unfold g1' g2' at this
  have f1 : (1 - 2) * (3 - 4) = 0 := by rfl
  have f2 : 1 * 3 - 3 * 2 - 1 * 4 + 4 * 2 = 8 := by rfl
  rw [f1, f2] at this
  linarith

-- If you are unable to do so, please analysis the reason of your failure.
/-
 - Reason: In `Nat`, if n is greater than m (intuitively),
 -   then by definition (m - n) can only be 0.
 -/
