/-
 - 08/18 Sets ─ Notes
 -
 - Set : Type → Type
 - `Set A` is the type of sets whose elements are of type A.
 - A set `s` of type `Set A` is actually a function s : A → Prop.
 - x ∈ s is 
 -/

import Mathlib.Tactic

set_option linter.unusedVariables false

/-
# 1 Set in Lean
-/

/-
## 1.1 Definition of Set in Lean
-/

/-
In Lean, or in Type Theory, a type is not the same as a set in Set Theory. We can see this by the following example:
In Set Theory, the expression `0 ∈ ℕ` is a proposition. We can also have the expression `(1, 3) ∈ ℕ`, although this is a false proposition.
However, in Type Theory, we cannot have the expression `(1, 3) : ℕ`. Recall that the expression `x : t` means the type of `x` is `t`, and `(1, 3)` can never be a term of `ℕ`, so `(1, 3) : ℕ` just makes no sense.

In Lean, a set `s` **w.r.t. some type `α`** is actually a function of type `α → Prop`. This means, the elements of the set `s` are just those terms `x` such that the proposition `s x` holds. `Set α` is the type containing all sets w.r.t. `α`, i.e., a term `s : Set α` just means a set on type `α`.
-/
section definition_of_set
variable (α : Type)
#check Set α      -- Set α : Type
#print Set        -- def Set.{u} : Type u → Type u := fun α => α → Prop

example : (Set α) = (α → Prop) := by rfl

variable (s : Set α)

#check s          -- s : Set α

/- **Question**: How to define a set containing all terms of a type? -/
def UniverseSet : Set α := fun _ => True
-- Just returning `True` means for all a : α, a ∈ UniverseSet is True.
-- NB True is of type Prop, not Boolean.

/-
In this example, `lt_three` represents the set of natural numbers which are less than `3`.
-/
def lt_three : Set ℕ :=
  fun n => n < 3
end definition_of_set

/-
## 1.2 Properties of Set
-/
section properties_of_set
/-
### 1.2.1 Membership
-/
/-
 - Recall that the elements of a set `s : Set α` are just those `x : α`,
 - such that the proposition `s x : Prop` holds.
 - So naturally, the membership `x ∈ s : Prop` between a term `x : α` and a set `s : Set α`
 - should be defined as `s x : Prop`.
 -/
variable (α : Type) (a : α) (s : Set α)

#check a ∈ s      -- a ∈ s : Prop

example : (a ∈ s) = (s a) := by rfl

/-
 - Similarly, `a ∉ s` is just the proposition `¬(a ∈ s)` (paratheses can be omitted).
 -/

#check a ∉ s      -- a ∉ s : Prop

example : (a ∉ s) = ¬a ∈ s := by rfl

/-
### 1.2.2 Subset
-/
/-
 - In maths, for two sets `s` and `t`, when we say `s` is a subset of `t`, i.e., `s ⊆ t`,
 - we mean for any element `x ∈ s`, `x ∈ t` also holds.
 - 
 - So is this in Lean. Given two sets `s t : Set α`,
 - the proposition `s ⊆ t : Prop` is defined as `∀ x : α, x ∈ s → x ∈ t : Prop`.
 - As a result, We can use `(h : s ⊆ t)` in the same way as we do
 - w.r.t. the logical calculator like `∀`, `→`, etc.
 -/

variable (t : Set α)

#check s ⊆ t      -- s ⊆ t : Prop

example : (s ⊆ t) = (∀ ⦃x : α⦄, x ∈ s → x ∈ t) := by rfl
/-
 - Strict-implicit binder, like `⦃x y : A⦄` or `⦃x y⦄`. In contrast to `{ ... }` implicit binders,
 - strict-implicit binders do not automatically insert a `_` placeholder until at least
 - one subsequent explicit parameter is specified.
 - Do not use strict-implicit binders unless there is a subsequent explicit parameter.
 - Assuming this rule is followed, for fully applied expressions
 - implicit and strict-implicit binders have the same behavior.
 - 
 - Example: If `h : ∀ ⦃x : A⦄, x ∈ s → p x` and `hs : y ∈ s`,
 - then `h` by itself elaborates to itself without inserting `_` for the `x : A` parameter,
 - and `h hs` has type `p y`. In contrast, if `h' : ∀ {x : A}, x ∈ s → p x`,
 - then `h` by itself elaborates to have type `?m ∈ s → p ?m` with `?m` a fresh metavariable.
 -/

example (h₁ : s ⊆ t) (x : α) (h₂ : x ∈ s) : x ∈ t := by
  exact h₁ h₂

/-
### 1.2.3 Intersection
-/
/-
 - In the same way, given two sets `s t : Set α`,
 - the intersection of them `s ∩ t : Set α` is defined as `fun x => x ∈ s ∧ x ∈ t`.
 -/

#check s ∩ t      -- s ∩ t : Set α

example : (s ∩ t) = (fun x => x ∈ s ∧ x ∈ t) := by rfl
-- example : (s ∩ t) = (fun x => x ∈ t ∧ x ∈ s) :=
--   by rfl
  /-
  tactic 'rfl' failed, the left-hand side
    s ∩ t
  is not definitionally equal to the right-hand side
    fun x => x ∈ t ∧ x ∈ s
  -/

example : (a ∈ s ∩ t) = (a ∈ s ∧ a ∈ t) := by rfl

/-
 - We can use `h : a ∈ s ∩ t` in the same way as we use a proof of a logical conjunction.
 -/
example (h : a ∈ s ∩ t) : a ∈ s := by
  rcases h with ⟨mem_s, mem_t⟩  -- a ∈ s ∪ t == s a ∧ t a
  exact mem_s

example (h : a ∈ s ∩ t) : a ∈ s := by
  exact h.left

example (h₁ : a ∈ s) (h₂ : a ∈ t) : a ∈ s ∩ t := by
  -- `tauto` will do.
  constructor
  · exact h₁
  · exact h₂

/-
### 1.2.4 Union
 -/
/-
 - Given two sets `s t : Set α`, the union of them `s ∪ t : Set α` is defined as `fun x => x ∈ s ∨ x ∈ t`.
 -/
#check s ∪ t      -- s ∪ t : Set α

example : (s ∪ t) = (fun x => x ∈ s ∨ x ∈ t) := by rfl

example : (a ∈ s ∪ t) = (a ∈ s ∨ a ∈ t) := by rfl

/-
 - We can use `h : a ∈ s ∪ t` in the same way as we use a proof of a logical disjunction.
 -/
example (r : Set α) (h : a ∈ s ∪ t) (h₁ : s ⊆ r) (h₂ : t ⊆ r) : a ∈ r := by
  rcases h with mem_s | mem_t
  · exact h₁ mem_s
  · exact h₂ mem_t

example (h : a ∈ s) : a ∈ s ∨ a ∈ t := by
  left
  exact h

/-
### 1.2.5 Difference
-/
/-
 - Given two sets `s t : Set α`, the union of them `s \ t : Set α` is
 - defined as `fun x => x ∈ s ∧ x ∉ t`.
 -/

#check s \ t      -- s \ t : Set α

example : (s \ t) = (fun x => x ∈ s ∧ x ∉ t) := by rfl

example : (a ∈ s \ t) = (a ∈ s ∧ a ∉ t) := by rfl

/-
 - We can use `h : a ∈ s \ t` in the same way as we use a proof of a logical conjunction.
 -/
example (h : a ∈ s \ t) : a ∉ t := by
  exact h.right

example (h₁ : a ∈ s) (h₂ : a ∉ t) : a ∈ s \ t := by
  exact ⟨h₁, h₂⟩

/-
### 1.2.6 Complement
-/
/-
 - Given a set `s : Set α`, the complement of it `sᶜ : Set α` is defined as `fun x => x ∉ s`.
 -/

#check sᶜ         -- sᶜ : Set α

example : sᶜ = (fun x => x ∉ s) := by rfl

example : (a ∈ sᶜ) = (a ∉ s) := by rfl

/-
 - We can use `h : a ∈ sᶜ` in the same way as we use a proof of a logical negation.
 -/
example (h₁ : a ∈ s) (h₂ : a ∈ sᶜ) : 1 = 2 := by
  exfalso
  exact h₂ h₁
example (h : a ∉ t) (h₂ : s ⊆ t) : a ∈ sᶜ := by
  intro mem_s
  apply h
  exact h₂ mem_s
end properties_of_set


/-
## 1.3 Universe Set and Empty Set
-/
section univ_and_empty
axiom α : Type
/-
 - The universe set contains all the terms of a type. So by the definition of Set in Lean,
 - for the universe set `U : Set α`, `U x` should hold for every `x`,
 - which leads to `U` being `fun x => True`.
 -/

def SET'' : Set α := fun x => True  -- unused variable `x`
def SET : Set α := fun _ => True

example : ∀ x : α, x ∈ SET := by
  intro x
  exact trivial

/-
 - In Lean, we use the `Set.univ` to represent the universe set of some type `α`.
 - Note that, `α` is an implicit parameter here.
 -/
#check Set.univ     -- Set.univ.{u} {α : Type u} : Set α
example : ∀ x : α, x ∈ Set.univ := by
  intro x
  exact trivial

/-
 - The empty set contains no terms of a type. So by the definition of Set in Lean,
 - for the empty set `E : Set α`, `E x` should **NOT** hold for every `x`,
 - which leads to `E` being `fun x => False`.
 -/
def EMPTY' : Set α := fun x => False
def EMPTY : Set α := fun _ => False

example : ∀ x : α, x ∉ EMPTY := by
  intro x mem_empty
  exact mem_empty

/-
 - In Lean, we use the `∅` symbol to represent the empty set of some type `α`. Note that, `α` is an implicit parameter here.
 -/
#check ∅              -- ∅ : ?m.3167
#check (∅ : Set α)    -- ∅ : Set α
example : ∀ x : α, x ∉ (∅ : Set α) := by
  intro x mem_empty
  exact mem_empty
end univ_and_empty


/-
## 1.4 Set Builder Symbol
-/
section set_builder
/-
 - Just as what we do in maths, we can also use the set builder `{}` to construct a set in Lean.
 -
 - The basic format of this is `{x : t | p x}`,
 - where `t` is a type and `p : t → Prop` is a property on type `t`.
 - Such a set contains all the terms `x` s.t. the proposition `p x` holds.
 -/
variable (α : Type) (p : α → Prop)

#check {x : α | p x}          -- {x | p x} : Set α

#check {x | ∃ n, 2 * n = x}   -- {x | ∃ n, 2 * n = x} : Set ℕ
#check {2 * n | n}            -- {x | ∃ n, 2 * n = x} : Set ℕ
example : ({1, 2, 3} : Set Nat) = insert 1 {2, 3} := by
  rfl
end set_builder


/-
## 1.5 Function and Set
-/
section function
variable (α β : Type) (s : Set α) (f : α → β)

/-
 - In Lean, we use `f '' s` to represent the image of `s : Set α` under the function `f`.
 - In particular, `f '' s` is a set of `β`, i.e., we have the expression `f '' s : Set β`.
 -/
#check f '' s     -- f '' s : Set β

example (b : β) : v := by rfl

variable (t : Set β)

/-
 - In Lean, we use `f ⁻¹' t` to represent the preimage of `t : Set β` under the function `f`.
 - In particular, `f ⁻¹' t` is a set of `α`, i.e., we have the expression `f ⁻¹' t : Set α`.
 -/
#check f ⁻¹' t    -- f ⁻¹' t : Set α

example (a : α) : (a ∈ f ⁻¹' t) = (f a ∈ t) := by rfl
end function


/-
## 1.6 Syntax Sugar
-/
section sugar
/-
 - This is a syntax sugar, used for simplifying the expressions when coding.
 -/
example (p : ℕ → Prop) : (∀ x > 0, p x) = (∀ x, x > 0 → p x) := by rfl
example (p : ℕ → Prop) : (∃ x > 0, p x) = (∃ x, x > 0 ∧ p x) := by rfl
end sugar

/-
# 2 Subtype
-/
section subtype
/-
## 2.1 Introduction and Definition
-/
variable (α : Type) (s : Set α)

/-
 - In Type Theory, for a term `x : t`,
 - `x` is usually not a type again (not hold when `t` is `Prop`).
 - So is this when `t` is `Set α`.
 -
 - However, for a set `s : Set α`, when we write `a : s`, Lean doesn't complain!!
 - In other words, such an expression really makes sense in Lean.
 -/
variable (a : s)    -- NO ERRORS!!

/-
 - When we use the `#check` command to check the type of `a`,
 - we find that the actual type of `a` is `↑s` instead of `s` itself.
 -
 - This actually is a type coercion. `↑s` is a type, while `s` is not.
 - When we write `a : s` down, Lean knows that we need a type in the position of `s`,
 - but `s` is not a type. So Lean automatically tries to coerce `s` into a type, and there `↑s` is.
 -/
#check s
#check a            -- a : ↑s
-- Here `↑` coerces s : α → Prop to a subtype of α ?

/-
 - So what is the exact definition of `↑s`?
 -
 - This is a Subtype!
 -
 - Given a type `α`, we can take some terms of `α` by a property `p : α → Prop`
 - to form a new type. Such a new type is called a subtype of `α`.
 -
 - For example, if we set a property `p : ℕ → Prop` to be `fun n => n ≤ 9`,
 - then the related subtype of `ℕ` contains the natural numbers no more than `9`.
 -
 - We can use `{x : α // p x}` to represent such a subtype.
 - A term `a : {x : α // p x}` can be viewed as a pair, with two fields `.val` and `.property`.
 -
 - `a.val` is of type `α`, representing the corresponding term of type `α`.
 - `a.property` is of type `p a.val`, representing the proof that `a.val` satisfies the property `p`.
 -
 - We can also use `a.1` and `a.2` to visit them.
 -/
variable (p : α → Prop) (a : {x : α // p x})

#check a.val        -- ↑a : α
#check a.property   -- a.property : p ↑a
#check a.1          -- ↑a : α
#check a.2          -- a.property : p ↑a

#check Subtype.val          -- Subtype.val.{u} {α : Sort u} {p : α → Prop} (self : Subtype p) : α
#check Subtype.property     -- Subtype.property.{u} {α : Sort u} {p : α → Prop} (self : Subtype p) : p ↑self


/-
## 2.2 Example: Nested Subtype
-/
/-
 - This is a nested subtype example, which is commonly used in maths formalization.
 - Basically speaking, it is just a subtype of a subtype. There's nothing special here.
 - Only need to keep it clear that whose `.val` and `.property` we are using.
 -/
#check ℝ                    -- ℝ : Type
#check {x : ℝ // x ≥ 0}     -- { x // x ≥ 0 } : Type

variable (y : {x : ℝ // x ≥ 0})

#check y.val                -- ↑y : ℝ
#check y.property           -- y.property : ↑y ≥ 0

#check {x : {x : ℝ // x ≥ 0} // x.val > 0}  -- { x // ↑x > 0 } : Type
variable (z : {x : {x : ℝ // x ≥ 0} // x.val > 0})

#check z.val                -- ↑z : { x // x ≥ 0 }
#check z.property           -- z.property : ↑↑z > 0

#check z.val.val            -- ↑↑z : ℝ
#check z.val.property       -- (↑z).property : ↑↑z ≥ 0


variable (t : Set s) (x : t)

#check x.val            -- ↑x : ↑s
#check x.property       -- x.property : ↑x ∈ t
#check x.val.val        -- ↑↑x : α
#check x.val.property   -- (↑x).property : ↑↑x ∈ s
end subtype

/-
# 3 Type Coercion
-/
section coercion
/-
 - As it is showed in the subtype section.
 - When the type of the parameters offered and the type wanted do not match,
 - Lean attempts to do a coercion, trying to find a correponding term with the type wanted.
 -
 - If it succeeds, it marks a arrow in front of the corresponding term found,
 - like the `↑s` above and the `↑1 : ℝ` below. If it fails, Lean just throws an error,
 - reporting such a mismatching.
 -/
def f : ℝ → ℝ := fun x => x + 1

#check f (1 : ℕ)    -- f ↑1 : ℝ

/-
 - application type mismatch
 -  f (1, 2)
 - argument
 -   (1, 2)
 - has type
 -   ℕ × ℕ : Type
 - but is expected to have type
 -   ℝ : Type
 -/
-- #check f ((1, 2) : ℕ × ℕ)

/-
 - Here are several arrows representing coercion. They have different meanings.
 - (1) `↑`. `↑x` represents a coercion, which converts `x` of type `α` to type `β`,
 - using typeclasses to resolve a suitable conversion function.
 - You can often leave the `↑` off entirely,
 - since coercion is triggered implicitly whenever there is a type error,
 - but in ambiguous cases it can be useful to use `↑` to disambiguate between e.g. `↑x + ↑y` and `↑(x + y)`.
 - (2) `↥`. `↥ t` coerces `t` to a type.
 - (3) `⇑`. `⇑ t` coerces `t` to a function.
 -/

#check 1
#check (1 : ℚ)
#check (1 : ℝ)
end coercion

/-
# 4 Tactic and Practice
-/
section tactics
/-
## 4.1 `ext`
-/
variable (α : Type) (s t : Set α)
/-
 - `ext` is short for "extensionality".
 - When we want to prove two sets `s t : Set α` are equal,
 - we can use `ext x` to change the goal from `s = t` to `x ∈ s ↔ x ∈ t`,
 - where `x` is the name of the term introduced and can be customized as we want.
 -/

example (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := by
  /-
  α : Type
  s t : Set α
  h : ∀ (x : α), x ∈ s ↔ x ∈ t
  ⊢ s = t
  -/
  ext x
  /-
  α : Type
  s t : Set α
  h : ∀ (x : α), x ∈ s ↔ x ∈ t
  x : α
  ⊢ x ∈ s ↔ x ∈ t
  -/
  exact h x

#check Set.ext    -- Set.ext.{u} {α : Type u} {a b : Set α} (h : ∀ (x : α), x ∈ a ↔ x ∈ b) : a = b

example (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := by
  apply Set.ext
  intro x
  exact h x

section examples
variable (α : Type) (s t u : Set α)
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x mem_inter
  rcases mem_inter with ⟨mem_s, mem_u⟩
  constructor
  · exact h mem_s
  · exact mem_u

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rintro x ⟨mem_s, mem_u⟩
  exact ⟨h mem_s, mem_u⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun _ ⟨mem_s, mem_u⟩ => ⟨h mem_s, mem_u⟩
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun _ ⟨mem_s, mem_u⟩ => ⟨h mem_s, mem_u⟩
end examples



section exercise₁
variable (α : Type) (s t u : Set α)
example : s ∩ (s ∪ t) = s := by
  funext x
  apply eq_iff_iff.mpr  -- or use `simp`
  constructor
  intro h
  exact h.1
  intro h
  constructor
  exact h
  left
  exact h

example : s ∪ s ∩ t = s := by
  simp

example : s \ t ∪ t = s ∪ t := by
  simp

example (h : s ⊆ t) : s \ u ⊆ t \ u := by
  intro x g
  constructor
  apply h
  exact g.left
  exact g.right

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  funext x
  apply eq_iff_iff.mpr
  constructor
  intro h
  constructor
  cases h with
  | inl g => left; exact g.1
  | inr g => right; exact g.1
  intro g
  cases g
  cases h with
  | inl f => apply f.right; assumption
  | inr f => apply f.right; assumption
  intro ⟨left, right⟩
  cases left with
  | inl f =>
      left
      constructor
      assumption
      tauto
  | inr f =>
      right
      constructor
      assumption
      tauto

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  intro x h
  cases h with
  | inl g =>
      constructor
      exact g.1
      left
      exact g.2
  | inr g =>
      constructor
      exact g.1
      right
      exact g.2

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  intro x h
  rcases h with ⟨xs, xntu⟩
  constructor
  constructor
  assumption
  intro xt
  apply xntu
  left
  assumption
  intro xu
  apply xntu
  right
  assumption

-- (b ∈ f '' s) := (∃ a ∈ s, f a = b)
-- (a ∈ f ⁻¹' t) := (f a ∈ t)
variable (β : Type) (f : α → β) (v : Set β)
example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  intro imfsv
  intro x xs
  apply imfsv
  exact ⟨x, xs, rfl⟩
  intro spreimfv
  intro x ximfsv
  rcases ximfsv with ⟨y, ys, fyx⟩
  let := spreimfv ys
  simp at this
  rw [← fyx]
  assumption

end exercise₁
