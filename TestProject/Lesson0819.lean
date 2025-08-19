import Mathlib

/-
# Find the Theorems in Lean

-/

/-
## 1. Tools and websites

1. zulip chat: https://leanprover.zulipchat.com/
2. mathlib docs: https://leanprover-community.github.io/mathlib4_docs/
  * Official websites
  * Search by *name* of the theorem
3. LeanSearch: https://leansearch.net/
  * Semantic search by natural language or formal statement
4. Loogle: https://loogle.lean-lang.org/
  * Search by *type* of the theorem

-/

/-
## 2. The naming convention in Lean

### Format

Lean uses a combination of **snake_case**, **lowerCamelCase**,
and **UpperCamelCase** for all its naming.

In **snake_case**, words are separated by underscores (_) and are typically all lowercase.
In **lowerCamelCase**, the first word is lowercase and subsequent words start with
an uppercase letter, with no separators. In **UpperCamelCase**,
every word starts with an uppercase letter, also with no separators.

The following rules dictate the use of these naming conventions.

#### Rules

1.  **For terms with type `p` where `p : Prop` (i.e. proofs, theorem names):** Use **snake_case**.
2.  **For `Prop` and `Type`:** Use **UpperCamelCase**. This is the case
    when a new type or a proposition is defined, such as `Nat`, `Int`, `True` or `Nonempty`.
    This includes inductive types, structures and classes.
3.  **For function types:** A function's naming convention matches its return value.
    For example, a function of type `A → B → C` is named like a term of type `C`.
4.  **For other type terms:** Almost all other type terms use **lowerCamelCase**.
5.  **Referencing `UpperCamelCase` in `snake_case`:** When an `UpperCamelCase` name
    is part of a `snake_case` name, use `lowerCamelCase` to reference it.
6.  **Abbreviations:** Abbreviations like `LE` are treated as a single unit,
    and their casing is determined by the case of the first character.
7.  **Exceptions:** Some rare exceptions exist to maintain local naming symmetry.
    For example, `Ne` is used instead of `NE` to follow the example of `Eq`.
    Other exceptions include intervals (e.g., `Set.Icc`, `Set.Iic`),
    where `I` is capitalized even though the convention would dictate `lowerCamelCase`.

Here are some examples:
-/

/- Lean code examples -/

namespace Examples

-- A term representing a proof (rule 1)
theorem sub_one_mul {α : Type*} [NonAssocRing α] (a b : α) :
  (a - 1) * b = a * b - b := by
  rw [sub_mul, one_mul]

-- The type of natural numbers (rule 2)
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat

-- A proposition stating that `a` is the maximal element (rule 2)
def IsTop {α} (a : α) [LE α] : Prop :=
  ∀ b, b ≤ a

-- The universal set on a type `α` is the set containing all elements of `α`. (rule 3)
def Set.univ {α} : Set α := {_a | True}

-- A theorem related to `IsTop` (rule 1, rule 5)
theorem not_isTop_iff_ne_top {α : Type*} [PartialOrder α] [OrderTop α] {a : α} :
      ¬IsTop a ↔ a ≠ ⊤ := by
    constructor
    intro nt ant
    apply nt
    intro b
    rw [ant]
    apply le_top
    intro ant t
    apply ant
    apply top_le_iff.mp
    exact t ⊤

-- follows rule 2; `Ne` is an exception to rule 6
class NeZero {R : Type*} [Zero R] (n : R) : Prop where
  out : n ≠ 0

-- follows rules 1 and 5
theorem neZero_iff {R : Type*} [Zero R] {n : R} : NeZero n ↔ n ≠ 0 := by
  constructor
  intro h
  exact NeZero.out
  intro nz
  exact { out := nz }

end Examples

/-
#### Namespaces

This concept appears in many programming languages.
The purpose of namespaces is to solve the problem of giving the same name to many different things.
For example, we might want to have a theorem `min_le_right` for both integers and natural numbers.
The meaning of these two theorems is different, so we want to be able to specify that they belong
to different structures. This is where the concept of a namespace comes in.

A theorem name may have the form `Namespace.theorem_name` or `Namespace1.Namespace2.theorem_name`.
You use the `namespace` keyword to open a namespace. All theorems defined within this namespace
will be prefixed with the namespace's name. When you want to use such a theorem, you need to write
it in the format `namespace_name.theorem_name`. Alternatively, you can use the `open` keyword at
the beginning of your file to open certain namespaces, allowing you to use their theorems without
the prefix.

-/

namespace Examples

theorem Set.Subset.refl {α : Type*} (a : Set α) :
    a ⊆ a := by
  intro x
  exact id

theorem Iff.refl (a : Prop) : a ↔ a := by
  constructor <;> exact id

end Examples

#check Examples.Set.Subset.refl

#check Set.Subset.refl

-- #check Subset.refl -- fails

namespace Set

#check Subset.refl

namespace Subset

#check refl

end Subset
end Set

open Set
#check Subset.refl

/-
### How to name a theorem?

Theorem names use **snake_case** and generally follow the pattern "conclusion + of + condition1 + of + condition2...". The word "of" is used to link multiple conditions, as seen in some examples above. However, well-known theorems, like **wilsons_lemma**, usually keep their more familiar names.
-/

namespace Examples

theorem ZMod.wilsons_lemma (p : ℕ) [Fact (Nat.Prime p)] : ((p - 1).factorial : ZMod p) = -1 := by
  sorry

end Examples

/-
Here are some common naming abbreviations:

-----

## Logical Symbols

| Symbol | Code   | Name         |
| :----- | :----- | :----------- |
| ∨      | `\or`  | or           |
| ∧      | `\and` | and          |
| →      | `\r`   | of / imp     |
| ↔      | `\iff` | iff          |
| ¬      | `\n`   | not          |
| ∃      | `\ex`  | exists       |
| ∀      | `\fo`  | all / forall |
| =      |        | eq           |
| ≠      | `\ne`  | ne           |
| ∘      | `\o`   | comp         |

---

## Set Theory Symbols

| Symbol      | Code       | Name         | Notes                                      |
| :---------- | :--------- | :----------- | :----------------------------------------- |
| ∈           | `\in`      | mem          |                                            |
| ∪           | `\cup`     | union        |                                            |
| ∩           | `\cap`     | inter        |                                            |
| ⋃           | `\bigcup`  | iUnion / biUnion | `i` for "indexed," `bi` for "bounded indexed" |
| ⋂           | `\bigcap`  | iInter / biInter | `i` for "indexed," `bi` for "bounded indexed" |
| ⋃₀          | `\bigcup\0`| sUnion       | `s` for "set"                              |
| ⋂₀          | `\bigcap\0`| sInter       | `s` for "set"                              |
| \           | `\\`       | sdiff        |                                            |
| {x | p x}   |            | setOf        |                                            |
| {x}         |            | singleton    |                                            |
| {x, y}      |            | pair         |                                            |

---

## Algebraic Symbols

| Symbol      | Code       | Name          | Notes                                      |
| :---------- | :--------- | :------------ | :----------------------------------------- |
| 0           |            | zero          |                                            |
| +           |            | add           |                                            |
| -           |            | neg / sub     | `neg` for unary function, `sub` for binary function |
| 1           |            | one           |                                            |
| *           |            | mul           |                                            |
| ^           |            | pow           |                                            |
| /           |            | div           |                                            |
| •           | `\smul`    | smul          |                                            |
| ⁻¹          | `\-1`      | inv           |                                            |
| ¹/·         | `\frac1`   | invOf         |                                            |
| ∣           | `\|`       | dvd           |                                            |
| ∑           | `\sum`     | sum           |                                            |
| ∏           | `\prod`    | prod          |                                            |

---

## Lattice Symbols

| Symbol      | Code       | Name          | Notes                                      |
| :---------- | :--------- | :------------ | :----------------------------------------- |
| <           |            | lt            |                                            |
| ≤           | `\le`      | le            |                                            |
| ⊔           | `\sup`     | sup           | Binary operator                            |
| ⊓           | `\inf`     | inf           | Binary operator                            |
| ⨆           | `\Sup`     | iSup          |                                            |
| ⨅           | `\Inf`     | iInf          |                                            |
| ⊥           | `\bot`     | bot           |                                            |
| ⊤           | `\top`     | top           |                                            |

-----

Here are some exercises on Lean's naming conventions:
-/
/-
# Please give a proper name for each of the following examples:
-/
variable {α : Type}
example {a : ℤ} : a + 0 = a := by sorry  -- add_zero

example {a b c : ℤ} : (a + b) * c = a * c + b * c := by sorry  -- add_mul

example {a b : ℝ} : a / b = a * b⁻¹ := by sorry  -- div_eq_mul_inv

example {a b c : ℝ} : a ∣ b - c → (a ∣ b ↔ a ∣ c) := by sorry  -- dvd_iff_dvd_of_dvd_diff

example (s t : Set α) (x : α) : x ∈ s → x ∈ s ∪ t := by sorry  -- mem_union_right  -- mem_union_of_mem_left

example (s t : Set α) (x : α) : x ∈ s ∪ t → x ∈ s ∨ x ∈ t := by sorry  -- disjunction_of_inter

example {a : α} {p : α → Prop} : a ∈ {x | p x} ↔ p a := by sorry  -- mem_setOf_iff

example {x a : α} {s : Set α} : x ∈ insert a s → x = a ∨ x ∈ s := by sorry

example {x : α} {a b : Set α} : x ∈ a ∩ b → x ∈ a := by sorry  -- mem_left_of_mem_inter

example {a b : ℝ} : a ≤ b ↔ a < b ∨ a = b := by sorry  -- le_iff_lt_or_eq

example {a b : ℤ} : a ≤ b - 1 ↔ a < b := by sorry  -- le_sub_one_iff_lt

example {a b c : ℝ} (bc : a + b ≤ a + c) : b ≤ c := by sorry  -- le_add_left_cancel

/-
# Based on the following names, guess and state the theorems:
1. mul_add
2. add_sub_right_comm
3. le_of_lt_of_le
4. add_le_add
5. mem_union_of_mem_right
-/
namespace Naming

variable (a b c d : Nat)

theorem mul_add : a * (b + c) = a * b + a + c := sorry

theorem add_sub_right_comm : a + b - c = a - b + c := sorry

theorem le_of_lt_of_le : a < b → b ≤ c → a ≤ c := sorry

theorem add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d := sorry

theorem mem_union_of_mem_right {α : Type} {s t : Set α} {x : α} : x ∈ t → x ∈ s ∪ t := sorry

end Naming

/-
# Powerful Automated Tactics in Lean
-/

/-
The following content provides an introduction to some automated tactics, focusing on
their functionality and illustrating them with examples. Readers can explore them on
their own or use the `#help tactic` command to learn more about them.

-----

1.  One tactic that can automatically complete proofs is `simp`. In the Mathlib library,
a portion of theorems are marked with the `@[simp]` attribute, for example:
-/

namespace Examples
@[simp] theorem Nat.dvd_one {n : ℕ} : n ∣ 1 ↔ n = 1 := sorry
@[simp] theorem mul_eq_zero {a b : ℕ} : a * b = 0 ↔ a = 0 ∨ b = 0 := sorry
@[simp] theorem List.mem_singleton {a b : α} : a ∈ [b] ↔ a = b := sorry
@[simp] theorem Set.setOf_false : {a : α | False} = ∅ := sorry
end Examples

/-
The conclusions of these theorems are often equalities or of the `iff` form.

When you use `simp` in a proof, Lean automatically searches for all such theorems and
tries to match the left-hand side of each theorem with your goal. If a match is found,
Lean replaces the goal with the right-hand side of the equality. Note that after using
`simp`, Lean will blindly try to match all theorems until it can no longer continue.
As a result, the final form you get might not be what you originally wanted.
A good approach is to use `simp only`, which is similar in format to `rw`.
You can specify the theorems you want to use, and Lean will only use that specific set
of theorems for simplification. Here are some examples:
-/

example {n : ℕ} (h : Nat.Prime n → 2 < n → Odd n) : n ∈ {n | Nat.Prime n} ∩ {n | n > 2} → n ∈ {n | ¬Even n} := by
  -- simp
  simp only [gt_iff_lt, mem_inter_iff, mem_setOf_eq, Nat.not_even_iff_odd, and_imp]
  exact h

example {α : Type} {s t : Set α} {x : α} : x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t := by
  simp only [Set.mem_union]


/-
2.  `linarith` & `nlinarith`. `linarith` is a powerful automation tactic used to handle
goals involving linear order structures, such as equalities and inequalities. Its
working principle is to use proof by contradiction: it first negates the conclusion and
then searches for a contradiction among all the hypotheses. `linarith` is a terminal
tactic, so if it successfully finds a contradiction, it ends the proof; otherwise, it
throws an error. Additionally, sometimes our hypotheses are not sufficient for `linarith`
to find a contradiction, so we can provide a list of arguments after it, as in
`linarith [thm₁, thm₂, ...]`, to give `linarith` more assumptions to work with.

`nlinarith` is an upgraded version of `linarith` that can handle some nonlinear cases,
such as expressions with squares.

-/

example {a b c d : ℝ} (h1 : a < b) (h2 : b ≤ c) (h3 : c = d) : a + a < d + b := by
  linarith

example {a b c d : ℝ} (h1 : a < b) (h2 : b ≤ c) (h3 : c = d) : a + a < d + b := by
  linarith -- linarith can solve this obvious inequality

example {n : ℕ} (h : n = 5) : ¬n = 1 := by
  linarith

example (x y z : ℚ) (h1 : 2 * x < 3 * y) (h2 : - 4 * x + 2 * z < 0)
    (h3 : 12 * y - 4 * z < 0) : False := by
  linarith

example {a b : ℚ} (H : a ≤ 1 ∧ a + b ≤ 3) : 2 * a + b ≤ 4 := by
  linarith

example {x y : ℝ} (h1 : x = 5) (h2 : 1 ≤ y) : x * y + x ≥ 10 := by
  rw [h1]
  -- If this line is removed, `linarith` will fail, as it can only handle
  -- linear arithmetic, and multiplication is not linear.
  -- (Note the distinction between scalar multiplication and multiplication).
  linarith

example {α : Type*} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] (x : α) (h: x < x) : False := by
  linarith

example {x : ℝ} (h : x ≤ -3) : x ^ 2 ≥ 9 := by
  nlinarith

/-
The example about multiplication shows that `linarith` cannot directly handle nonlinear
situations, while the last example demonstrates `nlinarith`'s ability to handle nonlinear
expressions.

-----

3.  `norm_num`. `norm_num` is used to compute numerical expressions. It's worth noting
that if a variable `x` is present but we have the hypothesis `h : x = 1`, we can first
use `rw [h]` to eliminate the variable from the expression before computation.
-/

example : (1 : ℝ) + 1 = 2 := by
  norm_num

example : (1 : ℚ) + 1 ≤ 3 := by
  norm_num

example : (1 : ℤ) + 1 < 4 := by
  norm_num

example : (1 : ℂ) + 1 ≠ 5 := by
  norm_num

example : (1 : ℕ) + 1 ≠ 6 := by
  norm_num

example : ¬ (5 : ℤ) ∣ 12 := by
  norm_num

example : (3.141 : ℝ) + 2.718 = 5.859 := by
  norm_num

example : 3.141 + 2.718 = 5.859 := by
  norm_num    -- `norm_num` cannot handle floating-point numbers.
  sorry

example : |(3 : ℝ) - 7| = 4 := by
  norm_num    -- `norm_num` can also handle absolute values.

example {x : Nat} : x + 0 = x := by
  norm_num    -- `norm_num` sometimes calls `simp`, for example, this goal is not a pure numerical expression, but `norm_num` can still handle it.

/-
It is worth noting that `norm_num` cannot handle floating-point numbers. Also, it sometimes calls `simp` for simplification, as shown in the last example above, where the goal is not a purely numerical expression but `norm_num` still succeeds.

-----

4.  `positivity`. `positivity` is used to handle goals of the form `0 ≤ x`, `0 < x`, and `x ≠ 0`. It's also a terminal tactic, so it either solves the goal or reports an error. Its working principle is somewhat complex, but to put it simply, `positivity` analyzes complex expressions by combining them with the lower bounds of variables, breaking them down into simpler numerical expressions of the three forms mentioned above, and then proving each one using `norm_num`.
-/

example {a : ℤ} (ha : 3 < a) : 0 ≤ a ^ 3 + a := by
  positivity

example {a : ℤ} (ha : 1 < a) : 0 < |(3 : ℤ) + a| := by
  positivity

example : 0 < 5 - (-3) := by
  positivity

example (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (h : a * a * b * c - a * b * d = 0) : a * c = d := by
  -- positivity -- `positivity` fails!
  grind only

example : ¬ (5 : ℤ) ∣ 12 := by
  -- positivity -- `positivity` fails!
  sorry

example (x : ℝ) (hx : 0 < x) : 0 < 5 - (-x) := by
  -- norm_num
  -- positivity -- `positivity` alone fails!
  sorry

/-
As we can see, `positivity` successfully solves the first two examples. The next three examples cannot be solved by `positivity` because their proof goals are not of the three specific forms. The last example is interesting: `positivity` cannot directly analyze this expression, but after we run `norm_num`, the expression becomes `0 < 5 + x`, which can then be solved by `positivity`.

-----

5.  `ring`/`ring_nf`/`noncomm_ring` & `group`/`abel`. As their names suggest, these automation tactics are used to handle commutative rings, non-commutative rings, groups, and commutative groups, respectively. We'll use `ring` as an example to introduce a few use cases; the other tactics have similar usage.
-/

example {x y : ℤ} : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring

example (x y : ℝ) (f : ℝ → ℝ) : f (x + y) + f (y + x) = 2 * f (x + y) := by
  ring_nf

example (x y : ℤ) (h : (x - y) ^ 2 = 0) : x ^ 2 + y ^ 2 = 2 * x * y := by
  rw [← add_zero (2 * x * y), ← h]
  ring

example (x y : ℕ) : x * 2 + id y = y + 2 * id x := by
  rw [id, id]
  ring

example {R : Type} [Ring R] (a b : R) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + a * b + b * a := by
  noncomm_ring

example {G : Type} [AddCommGroup G] (a b : G) : 2 • (a - b) + a + b = 3 • a - b := by
  abel

/-
From the examples, we can see that when using `ring`-related tactics, you often need to simplify the goal to a certain extent before these automation tactics can complete the proof.

-----

6.  `field_simp`. `field_simp` is an automation tactic used to simplify division expressions, often in contexts involving division and inverses. We can understand its functionality through a few examples.
-/

example (x : ℝ) (h : x > 0) : 1 / x + 1 = (x + 1) / x := by
  field_simp
  ring

example (x: ℝ) (h1: x > 0) : (1 - x) / √x = 1/√x - √x  := by
  field_simp

example {a b : ℝ} (h : b ≠ 1) : a = (a * b - a) / (b - 1) := by
  field_simp [sub_ne_zero_of_ne h]
  ring

/-
Note that in one of the examples above, `field_simp` and `ring` are used in combination. This makes sense: `ring` handles goals related to commutative rings (only addition, subtraction, and multiplication), while `field_simp` can handle division. Together, they can solve some simple arithmetic problems. In the last example, we can provide arguments to `field_simp` using a list, extending its search scope and improving its simplification ability.

-----

7.  `omega`. Finally, let's introduce the very powerful automation tactic: `omega`. It is used to handle all propositions related to natural numbers, and its underlying mechanism is quite complex. Currently, it can handle addition, subtraction, and multiplication of natural numbers (where division is floor division), but it is almost "clueless" about the modulo operation. At some point in the future, its functionality will be improved, making it a powerful tool for proving natural number-related propositions\!
-/

example {x} : x ≥ 1 → x + 1 ≤ 2 * x := by omega

example {x} : x ≥ 2 → x / 2 ≤ x - 1 := by omega

example : 5 % 2 = 1 := by omega

example (x : ℕ) (h : Odd x) : x % 2 ≠ 0 := by
  rw [Odd] at h
  omega

example (x : Nat) : x * (x + 1) % 2 = 0 := by
  have h : Even (x * (x + 1)) := by
    exact Nat.even_mul_succ_self x
  rw [Even] at h
  omega

/-
As you can see, in the last three examples, `omega` can solve the goal for relatively simple modulo operations. It can also solve the goal after being provided with some theorems. However, we would ideally want `omega` to be able to find these theorems itself.
-/

section exercise
example (a b c d x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
    a + b / x + c / x ^ 2 + d / x ^ 3 = a + x⁻¹ * (y * b / y + (d / x + c) / x) := by
  field_simp
  ring

example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  cases h with
  | inl one => repeat rw [one]; ring
  | inr two => repeat rw [two]; ring

example {n m : ℕ} : (n + m) ^ 3 = n ^ 3 + m ^ 3 + 3 * m ^ 2 * n + 3 * m * n ^ 2 := by
  linarith

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  set x := (b - a + c) / 2 with hx_def
  set y := (a - b + c) / 2 with hy_def
  set z := (a + b - c) / 2 with hz_def
  use x, y, z
  rw [hx_def, hy_def, hz_def]
  sorry

example (x : ℕ) (h : (x : ℚ) = 1) : x = 1 := by
  simp_all only [Rat.natCast_eq_one]

example {b : ℤ} : 0 ≤ max (-3) (b ^ 2) := by
  apply le_max_iff.mpr
  right
  sorry

example (x : ℕ) : x ≥ 2 → x / 2 ≥ 1 := by
  omega

end exercise
