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
  cases h -- rcases h with ⟨w, p⟩
  assumption -- exact p

end

example (x : Nat) (h : x ≥ 4 ∧ x < 6 ∧ x ≠ 5) : x = 4 := by
  rcases h with ⟨h1, h2, h3⟩
  apply Nat.le_antisymm
  show x ≥ 4
  exact h1
  apply Nat.le_of_lt_succ
  simp
  apply Nat.lt_of_le_of_ne
  apply Nat.le_of_lt_succ
  simp
  exact h2
  exact h3

------------------------------------------------
-- `Conjunction (and) and disjunction (or)`

------------
-- You have already known the effect of conjugation (∧) and disjunction (∨) im mathmatics. Given two propositions `P` and `Q`,
-- the conjugation of `P` and `Q`, which is denoted as `P ∧ Q`, is true if and only if both `P` and `Q` are true. And the disjunction;
-- the disjunction of `P` and `Q`, which is denoted as `P ∨ Q`, is true if and only if `P` is true or `Q` is true.
-- It makes no difference to express this in Lean:
variable (P Q : Prop)
#check P ∧ Q
#check P ∨ Q

-- The main theme of this afternoon is to teach you how to deal with conjugation and disjunction in Lean. More specifically, you will see how to prove the propositions in the following forms:

------------
-- `1. conjugation in the condition`
example (x : Nat) (h : x ≥ 5 ∧ x < 6) : x = 5 := by
  cases h
  apply Nat.le_antisymm
  apply Nat.le_of_lt_succ
  simp
  assumption
  show x ≥ 5
  assumption
  

-- Now we have only one condition `h` about `x`, but we want to extract two conditions `h1 : x ≥ 5` and `h2 : x < 6` from it. This can be done by using `h.left` and `h.right`.
example (x : Nat) (h : x ≥ 5 ∧ x < 6) : x = 5 := by
  #check h.left
  #check h.right
  exact Nat.eq_of_le_of_lt_succ h.left h.right
-- You can also write `h.1` and `h.2` which is slightly shorter:
example (x : Nat) (h : x ≥ 5 ∧ x < 6) : x = 5 := Nat.eq_of_le_of_lt_succ h.1 h.2
-- `Question:` what's the difference (except for the usage of .left .right .1 .2) between the above two proofs?

-- When there are multiple conjunctions in a condition, you can use it as follows:
variable (R : Prop)
variable (s : P ∧ Q ∧ R) -- Be careful! `P ∧ Q ∧ R` means `P ∧ (Q ∧ R)`, not `(P ∧ Q) ∧ R`. You shold try to prove that they are equivalent.
#check s.1
#check s.2
#check s.2.1
#check s.2.2


-- There is another way to extract two conditions from a conjunction, which is more of "functional programming flavor". Think of a conjuction `P ∧ Q` as a "package". Extracting `P` and `Q` from this package is like "deconstructing" the package. In Lean, this can be achieved by the `rcases` tactic:
example (x : Nat) (h : x ≥ 5 ∧ x < 6) : x = 5 := by
  rcases h with ⟨h1,h2⟩
  -- The `rcases` tactic deconstruct the condition `h` into `h1` and `h2`
  -- `Note:` the left angle and right angle is not usual symbol "<" ">" for less than or greater than. You should type `⟨` by using `\<` and `\>`.
  -- `Note:` Please look at the InfoView. After `rcases`, the condition `h` no longer exists.
  exact Nat.eq_of_le_of_lt_succ h1 h2

-- When there is multiple conjunctions in a condition, you can use `rcases` repeatly:
example (x : Nat) (h : x ≥ 4 ∧ x < 6 ∧ x ≠ 5) : x = 4 := by
  rcases h with ⟨h1,h2⟩
  rcases h2 with ⟨h3,h4⟩
  apply Nat.le_antisymm
  show x ≥ 4
  exact h1
  apply Nat.le_of_lt_succ
  simp
  apply Nat.lt_of_le_of_ne
  apply Nat.le_of_lt_succ
  simp
  exact h3
  exact h4

-- You can also "nest" an `rcases` into another `rcases`:
example (x : Nat) (h : x ≥ 4 ∧ x < 6 ∧ x ≠ 5) : x = 4 := by
  rcases h with ⟨h1,⟨h2,h3⟩⟩
  apply Nat.le_antisymm
  show x ≥ 4
  exact h1
  apply Nat.le_of_lt_succ
  simp
  apply Nat.lt_of_le_of_ne
  apply Nat.le_of_lt_succ
  simp
  exact h2
  exact h3

-- For multiple conjugation, there is a syntactic suger for `rcases`:
example (x : Nat) (h : x ≥ 4 ∧ x < 6 ∧ x ≠ 5) : x = 4 := by
  rcases h with ⟨h1, h2, h3⟩
  apply Nat.le_antisymm
  show x ≥ 4
  exact h1
  apply Nat.le_of_lt_succ
  simp
  apply Nat.lt_of_le_of_ne
  apply Nat.le_of_lt_succ
  simp
  exact h2
  exact h3

------------
-- `2. conjugation in the goal`
example (x : Nat) (h : x = 5) : x ≥ 5 ∧ x < 6 := by
  constructor
  simp
  repeat rw [h]
  trivial
  

-- As we have learned, extacting conditions from a conjunction is to "deconstruct" a package. So proving a conjunction is to "construct" a package. In Lean, this can be done by the tactic `constructor`:
example (x : Nat) (h : x = 5) : x ≥ 5 ∧ x < 6 := by
  constructor
  · -- Do you still remember this `·`?
    rw [h]
  · rw [h]
    trivial
-- As you can see, `constructor` splits the goal, which is a conjunction `P ∧ Q`, into two goals `P` and `Q`. Now you need to prove them seperately.

-- If you there are multiple conjuctions in the goal, then you need to use `constructor` more than once:
example (x : Nat) (h : x = 5) : x ≥ 5 ∧ x < 6 ∧ x > 4 := by
  constructor
  · -- Do you still remember this `·`?
    rw [h]
  · -- Here the goal is `x < 6 ∧ x > 4`, so one more `constructor` is needed.
    constructor
    · rw [h]; trivial
    · rw [h]; trivial

-- You can also do this. Don't worry if you don't understand. It is not necessary.
example (x : Nat) (h : x = 5) : x ≥ 5 ∧ x < 6 := by
  rw [h]
  exact ⟨Nat.le_refl 5, Nat.lt_succ_self 5⟩ -- Construct a "package" for conjugation. Just like the "inverse" of rcases

------------
-- `3. disjunction in the condition`
example (x : Nat) (h : x = 5 ∨ x = 7) : ∃ y : Nat, x = y * 2 + 1 := by
  cases h with
  | inl h1 => use 2
  | inr h2 => use 3

-- In math, if we want to prove `P ∨ Q implies R`, we do something like this:
-- `We split the proof into 2 cases. If P, then R; if Q, then R.`
-- Formally, this is `(P ∨ Q → R) ↔ (P → R) ∧ (Q → R)`.
-- In Lean, we can do this by the `rcases` tactic:
example (x : Nat) (h : x = 5 ∨ x = 7) : ∃ y : Nat, x = y * 2 + 1 := by
  rcases h with h1 | h2 -- Where `h` is a disjunction. Compared to our usage of `rcases` for conjunction, here we replace `⟨h1,h2⟩` by `h1 | h2`
  · -- Now `h1` is the first possible condition in h, i.e. `x = 5`.
    use 2 -- Still remember `use`? It can be used to prove an existance statement.
   -- Normally, you still need to prove that `x = 2 * 2 + 1`. Here is some black magic of Lean.
  · use 3 -- Please complete this proof by yourself.


-- `4. disjunction in the goal`
example (x : Int) (h : x * x + 35 = 12 * x) : x = 5 ∨ x = 7 := by
  have : (x - 6) * (x - 6) - 1 = 0 := by ring

-- This is a easy one.
-- `Slogan:` If you want to prove `P ∨ Q`, you can just choose one of `P` and `Q` to prove.
-- We simply call `P` in `P ∨ Q` the left one, and `Q` in `P ∨ Q` the right one.
-- The effect of the following code is self-explaining:
example (x : Nat) (h : x = 5) : x ≤ 5 ∨ x ≥ 114513 := by
  left
  exact Nat.le_of_eq h

example (x : Nat) (h : x = 1919811) : x ≤ 5 ∨ x ≥ 114513 := by
  right
  rw [h]
  simp

-- Remark: `left` has the same effect as `apply Or.inl`; `right` has the same effect as `apply Or.inr`. So you can also write
example (x : Nat) (h : x = 5) : x ≤ 5 ∨ x ≥ 114513 := by
  apply Or.inl
  exact Nat.le_of_eq h

-- `Question:` can you find a shorter proof?

example : ∀ n : ℕ, n ≥ 0 := Nat.zero_le

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  repeat assumption

example (p q : Prop) (hpq : p → q) (hqp : q → p) : p ↔ q := by
  constructor
  repeat assumption

example (n : ℕ) : n ≥ 0 ∨ False := by
  left
  simp

example (n : ℕ) : n < 0 ∨ 1 = 1 := by
  right
  rfl

example (p q r : Prop) (hpq : p ∧ q) (hr : r) : p ∧ r := by
  constructor
  cases hpq
  repeat assumption

example (p q : Prop) (h : p ↔ q) (hp : p) : q := sorry

example (p q r : Prop) (hpq : p ∨ q) (h : q → r) : p ∨ r := sorry

example {α : Type} (q : Prop) (p : α → Prop) (h₁ : ∃ a, p a) (h₂ : ∀ a, p a → q) : q := by
  rcases h₁ with ⟨a, pa⟩
  exact h₂ a pa

example (p q r s : Prop) (h₁ : p ∧ q ∧ r) (h₂ : r → s) : s := sorry

example (p q r : Prop) (h : q → r) : p ∨ q → p ∨ r := by
  intro g
  cases g
  left
  assumption
  right
  apply h
  assumption
