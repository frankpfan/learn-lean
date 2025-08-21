import Mathlib

/-
# Structures

Modern mathematics makes essential use of algebraic structures, which capture patterns that can be instantiated in multiple settings. The subject provides various ways of defining such structures and constructing particular instances.

E.g. Groups and rings are structures.

### Defining Structures

A **structure** is a convention for organizing data, possibly including constraints that the data must satisfy. An **instance** of a structure is a specific set of data that meets these constraints. For example, we can define a point (in three-dimensional space) as a triple of real numbers:
-/

@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

/-
The `@[ext]` annotation tells Lean to automatically generate theorems that can be used to prove that two instances of the structure are equal if their corresponding components are equal—a property known as extensionality.
-/

#check Point.ext

example (a b : Point) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  ext
  · assumption
  · assumption
  · assumption

/-
### Construct terms in the structure
We can then define specific instances of the `Point` structure. Lean offers several ways to do this:
-/

def myPoint1 : Point where
  x := 2
  y := -1
  z := 4

def myPoint2 : Point :=
  ⟨2, -1, 4⟩

def myPoint3 :=
  Point.mk 2 (-1) 4

/-
In `myPoint3`, the function `Point.mk` is called the constructor of the `Point` structure because it is used to construct elements. You can specify a different name if desired, such as `build`:
-/

structure Point' where build ::
  x : ℝ
  y : ℝ
  z : ℝ

#check Point'.build 2 (-1) 4

/-
The next two examples show how to define functions on structures.
-/

namespace Point

def add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

def add' (a b : Point) : Point where
  x := a.x + b.x
  y := a.y + b.y
  z := a.z + b.z

#check add myPoint1 myPoint2
#check myPoint1.add myPoint2

end Point

/-
Typically, definitions and theorems related to structures like `Point` are placed in a namespace with the same name. In the following example, because we opened the `Point` namespace, the full name of `add` is `Point.add`. When the namespace is not open, we must use the full name. However, note that using anonymous projection notation is often convenient, allowing us to write `a.add b` instead of `Point.add a b`. Lean interprets the former as the latter because `a` has type `Point`.
-/

#check Point.add myPoint1 myPoint2
#check myPoint1.add myPoint2

/-
To prove properties of the addition function, we can use `rw` to unfold definitions and `ext` to reduce the equality of two structure elements to the equality of their components. Below, we use the `protected` keyword so that the theorem's name remains `Point.add_comm` even when the namespace is open. This is helpful when we want to avoid ambiguity with generic theorems like `add_comm`.
-/

namespace Point

protected theorem add_comm (a b : Point) : add a b = add b a := by
  rw [add, add]
  ext <;> dsimp
  · apply add_comm
  · apply add_comm
  · apply add_comm

example (a b : Point) : add a b = add b a := by simp [add, add_comm]

end Point

/-
Since Lean can internally unfold definitions, the following definitional equality holds:
-/

theorem add_x (a b : Point) : (a.add b).x = a.x + b.x :=
  rfl

/-
Structures are not only useful for specifying data types but also for imposing constraints on the data. In Lean, such constraints are represented as fields of type `Prop`. For example, the standard 2-simplex is defined as the set of points satisfying `x ≥ 0`, `y ≥ 0`, `z ≥ 0`, and `x + y + z = 1`. This set is an equilateral triangle (including its interior) in three-dimensional space with vertices at `(1, 0, 0)`, `(0, 1, 0)`, and `(0, 0, 1)`. We can represent this in Lean as follows:
-/

structure StandardTwoSimplex where
  x : ℝ
  y : ℝ
  z : ℝ
  x_nonneg : 0 ≤ x
  y_nonneg : 0 ≤ y
  z_nonneg : 0 ≤ z
  sum_eq : x + y + z = 1

/- Note that the last four fields refer to `x`, `y`, and `z`, the first three fields. We can define a function that swaps `x` and `y` on the 2-simplex:
-/

def swapXY (a : StandardTwoSimplex) : StandardTwoSimplex
    where
  x := a.y
  y := a.x
  z := a.z
  x_nonneg := a.y_nonneg
  y_nonneg := a.x_nonneg
  z_nonneg := a.z_nonneg
  sum_eq := by rw [add_comm a.y a.x, a.sum_eq]

/-
More interestingly, we can compute the midpoint of two points on the simplex. We add a `noncomputable section` at the beginning of the file to use division on real numbers.
-/

noncomputable section

namespace StandardTwoSimplex

def midpoint (a b : StandardTwoSimplex) : StandardTwoSimplex
    where
  x := (a.x + b.x) / 2
  y := (a.y + b.y) / 2
  z := (a.z + b.z) / 2
  x_nonneg := div_nonneg (add_nonneg a.x_nonneg b.x_nonneg) (by norm_num)
  y_nonneg := div_nonneg (add_nonneg a.y_nonneg b.y_nonneg) (by norm_num)
  z_nonneg := div_nonneg (add_nonneg a.z_nonneg b.z_nonneg) (by norm_num)
  sum_eq := by field_simp; linarith [a.sum_eq, b.sum_eq]

end StandardTwoSimplex

/-
Structures can depend on parameters. For example, we can generalize the standard 2-simplex to the standard `n`-simplex for any `n`. At this stage, you don’t need to know anything about the `Fin n` type except that it has `n` elements and that Lean knows how to sum over it.
-/

structure StandardSimplex (n : ℕ) where
  V : Fin n → ℝ
  NonNeg : ∀ i : Fin n, 0 ≤ V i
  sum_eq_one : (∑ i, V i) = 1

namespace StandardSimplex

def midpoint (n : ℕ) (a b : StandardSimplex n) : StandardSimplex n
    where
  V i := (a.V i + b.V i) / 2
  NonNeg := by
    intro i
    apply div_nonneg
    · linarith [a.NonNeg i, b.NonNeg i]
    norm_num
  sum_eq_one := by
    simp [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
      a.sum_eq_one, b.sum_eq_one]
    field_simp

end StandardSimplex

/-
We have seen that structures can bundle data with properties. Interestingly, they can also bundle properties without data. For example, the following `IsLinear` structure bundles the two components of linearity.
-/

structure IsLinear (f : ℝ → ℝ) where
  is_additive : ∀ x y, f (x + y) = f x + f y
  preserves_mul : ∀ x c, f (c * x) = c * f x

section
variable (f : ℝ → ℝ) (linf : IsLinear f)

#check linf.is_additive
#check linf.preserves_mul

end

/-
It’s worth noting that structures are not the only way to bundle data. The `Point` data structure could be defined using the generic `product` type, and `IsLinear` could be defined with a simple `and`.
-/

def Point'' :=
  ℝ × ℝ × ℝ

def IsLinear' (f : ℝ → ℝ) :=
  (∀ x y, f (x + y) = f x + f y) ∧ ∀ x c, f (c * x) = c * f x

/-
Generic structures can even be used for structures with dependencies between components. For example, the subtype construction bundles data with a property. `PReal` can be viewed as the type of positive real numbers. Any `x : PReal` has two components: the value and the proof of positivity. You can access these as `x.val` (of type `ℝ`) and `x.property` (which states `0 < x.val`).
-/

def PReal :=
  { y : ℝ // 0 < y }
#check Coe PReal ℝ

section
variable (x : PReal)

#check x.val
#check x.property
#check x.1
#check x.2

end

/-
We can also use subtypes to define the standard 2-simplex:
-/

def StandardTwoSimplex' :=
  { p : ℝ × ℝ × ℝ // 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.1 + p.2.1 + p.2.2 = 1 }

/-
But even though we could use products or subtypes instead of structures, structures offer many advantages. Defining a structure abstracts the underlying representation and provides custom names for accessing components. This makes proofs more stable: proofs that rely only on the structure’s interface often remain valid when we change the definition, as long as we redefine the old accessors accordingly. Moreover, as we will see, Lean provides support for weaving structures into a rich, interconnected hierarchy and managing interactions between them.
-/

namespace exercise1

/-
First we define the structure of points on 2 dimensional Euclidean space.
-/
structure Point where
  x : ℝ
  y : ℝ

/-
Define the structure of nondegenerate triangles, with four fields:
three vertices named `A`, `B` and `C`, and a field `nondegenerate` that states that the triangle is non-degenerate.
-/
structure Triangle where
  A : Point
  B : Point
  C : Point
/-
Construct a triangle with vertices at `(0, 0)`, `(1, 0)`, and `(0, 1)`.
-/
def myTriangle : Triangle where
  A := ⟨0, 0⟩
  B := ⟨1, 0⟩
  C := ⟨0, 1⟩

namespace Triangle
/-
Define the center and area of the triangle.

(Hint: area = (1/2) * |xA(yB - yC) + xB(yC - yA) + xC(yA - yB)|.)
-/
def center (t : Triangle) : Point :=
  ⟨(t.A.x + t.B.x + t.C.x) / 3, (t.A.y + t.B.y + t.C.y) / 3⟩

def area (t : Triangle) : ℝ := by
  rcases t with ⟨A, B, C⟩
  have a : ℝ := abs (A.x * (B.y - C.y) + B.x * (C.y - A.y) + C.x * (A.y - B.y)) / 2
  exact a

/-
Define the translation of a triangle by a vector (x,y).
-/
def translate (t : Triangle) (x y : ℝ) : Triangle := by
  rcases t with ⟨A, B, C⟩
  apply Triangle.mk
  · exact ⟨A.x + x, A.y + y⟩
  · exact ⟨B.x + x, B.y + y⟩
  · exact ⟨C.x + x, C.y + y⟩

/-
Show that the translation of t have the area with t.
-/
theorem area_translate (t : Triangle) (x y : ℝ)
    : area (translate t x y) = area t := by
  simp [area, translate]
  ring_nf

end Triangle

/-
Bonus: define the circumcenter (the point that have same distance to the vertices) of a triangle.
-/

/- coef_x * (y - base.y) = coef_y * (x - base.x) -/
structure Line where  -- TODO: non_singular
  base : Point
  coef_x : ℝ
  coef_y : ℝ

structure StandardizedLine where  -- TODO: non_singular
  A : ℝ
  B : ℝ
  C : ℝ

namespace Line

def standardize (m : Line) : StandardizedLine where
  A := m.coef_y
  B := - m.coef_x
  C := m.coef_x * m.base.y - m.coef_y * m.base.x

end Line

namespace StandardizedLine

def intersection (m n : StandardizedLine) : Point := by  -- TODO: not parallel
  have Δ := m.A * n.B - n.A * m.B
  have Δx := m.B * n.C - n.B * m.C
  have Δy := m.C * n.A - n.C * m.A
  exact Point.mk (Δx / Δ) (Δy / Δ)

end StandardizedLine

namespace Point

def perpendicularBisector (A B : Point) : Line where
  base := ⟨(A.x + B.x) / 2, (A.y + B.y) / 2⟩
  coef_x := A.y - B.y
  coef_y := B.x - A.x

def distance (P Q : Point) : ℝ :=
  Real.sqrt ((P.x - Q.x) ^ 2 + (P.y - Q.y) ^ 2)

end Point

/-
 - Made it! But `Real` is noncomputable so I can't easily verify its correctness.
 - (By replacing ℝ with ℚ, I have found it is correct.)
 -/
def Triangle.circumcenter (t : Triangle) : Point := by
  rcases t with ⟨A, B, C⟩
  apply StandardizedLine.intersection
  · apply Line.standardize
    exact Point.perpendicularBisector A B
  · apply Line.standardize
    exact Point.perpendicularBisector B C

end exercise1

/- This namespace is to distinguish our definitions and the definitions in Mathlib. -/
namespace Hidden
set_option linter.unusedVariables false

/-
When defining mathematical structures like additions in Lean, we definitely can define something like `Nat.add : ℕ → ℕ → ℕ` and `Vector.add : Vector → Vector → Vector`. But if we define them like this, for example, when we want to talk about the commutativity of additions, we need to give proof of `Nat.add_comm` and `Vector.add_comm` seperately. So does other properties.

This is annoying. So it is necessary to develop a general form of these structures. That means, we want somehow a carrier, acceptting a type `α`, and carrying an addition on this type `α`. This can be done by the `structure` keyword.
-/
structure Add₁ (α : Type) where
  add : α → α → α

/-
Now we can define an addition on `ℕ` in the way below.
-/
def Nat.canonical_addition₁ : Add₁ Nat where
  add := fun n m => n + m

/-
We can also define some general properties about the addition strucutre.
-/
def double₁ {α : Type} (s : Add₁ α) : α → α :=
  fun a => s.add a a

/-
But there is also a disadvantage of such definition. We **CANNOT** only use a uniform symbol like `+` to represent the general addition.

Let's check the type of function `Add.add`.
-/
#check Add₁.add  -- Hidden.Add₁.add {α : Type} (self : Add α) : α → α → α

/-
We can see that `Add₁.add` always requires a parameter of type `Add₁ α` to know what addition we want to use. So if we want to use the `+` symbol to represent the function `Add₁.add`, we have to give an `s : Add₁ α` somewhere, which is cumbersome.

To solve this, we can use the `class` keyword instead of `structure`. Basically speaking, we can use the `class` keyword in the same way as we use the `structure` keyword. This is called type classes in Lean.
-/
class Add (α : Type) where
  add : α → α → α

/-
Now if we check the type of `Add.add`, we can see that the parameter `self : Add α` now is wrapped with brackets instead of parentheses. Such parameters wrapped with brackets are called **instance implicit parameters**. This is a kind of implicit parameters, so Lean does not need us to offer the parameters and can infer is value automatically.

The main idea behind type classes is to make arguments such as `Add α` implicit, and to use a database of user-defined instances to synthesize the desired instances automatically through a process known as typeclass resolution, i.e., all instance implicit parameters should be synthesized using typeclass resolution.

Note that, instance implicit parameters are different from the common implicit parameters. Lean can only infer the values of the common implicit parameters by other explicit parameters. So it is of no use defining the `s : Add₁ α` to be an implicit parameter, because Lean never knows what it is only from other parameters.

However, all definitions of the instance-implicit-form are stored in a database. So every time such an instance implicit parameter is needed, Lean attempts to synthesize a proper one from that database. As a result, as long as we have already had one proper definition, Lean can infer the value automatically.
-/
#check Add.add  -- Hidden.Add.add {α : Type} [self : Add α] : α → α → α

/-
Now we can give the general addition function a symbol.
-/
infixl:70 " ⊹ " => Add.add

/-
This time, we do not need to offer the `s : Add α` parameter manually, because it is instance implicit and Lean infers what it is automatically.
-/
example {α : Type} [s : Add α] (a b : α) : α :=
  a ⊹ b

/-
We can use the `instance` keyword instead of `def` or some other ones to give an instance-implicit-form definition.
-/
instance Nat.canonical_addition : Add ℕ where
  add := (·+·)

/-
We can now reimplement the `double` function using an instance implicit parameter.
-/
def double {α : Type} [Add α] : α → α :=
  fun a => a ⊹ a

#check double 1

/-
We can put the cursor on some expressions in the infoview to see what instance implicit parameter Lean synthesizes for the term.

Like implicit parameters, the `@` symbol also coerces the instance implicit parameters into explicit parameters.
-/
#check (@double ℕ Nat.canonical_addition 1 : ℕ)

/-
If there are several instance-implicit-form definitions of the same type, Lean always takes the same one any time there's instance implicit parameters to be synthesized. Declared priorities and order of declaration are used as tiebreakers.
-/
instance Nat.another_addition : Add ℕ where
  add := fun m n => 0

#check 1 ⊹ 2
#check (@Add.add ℕ Nat.another_addition 1 2 : ℕ)

#check double 1
#check (@double ℕ Nat.another_addition 1 : ℕ)
/-
So if there are several instance-implicit-form definitions to use, we'd better not define the related type as a type class. If we have to, we need to offer the wanted instance implicit parameters manually. But then it is somewhat against the original purpose of using type classes.

------------------

In general, instances may depend on other instances in complicated ways. For example, we can declare an instance stating that if `α` has addition, then `α → α` also has one.
-/
instance {α : Type} [Add α] : Add (α → α) where
  add := fun f g =>
    fun a => f a ⊹ g a

/-
We can use the `#synth` command to let Lean synthesize the wanted instance.

We do not name the instance defined above, and Lean gives it a default name. Such definition is also added to the instance database.

Every time an `Add (ℕ → ℕ)` instance is needed, Lean searches in the database if there is some proper instances to help synthesize the wanted instance, and there `instAddForall` is. Then Lean attempts to synthesize an instance of `Add ℕ`, and there `Nat.another_addition` is. So from this path, Lean successfully synthesizes the wanted `Add (ℕ → ℕ)` instance.
-/
#synth Add (ℕ → ℕ)

/-
Another example is the `Coe` type class, which is used for type coercion in Lean.

Basically speaking, whenever a type coercion is needed, say the type of the term offered is `α`, the wanted type is `β`, Lean attempts to synthesize an instance of `Coe α β`.
-/
#print Coe

/-
There are also some other kinds of `Coe` type class, like `CoeHead`, `CoeTail`, etc. We won't explore all the things here, just taking one as an example.
-/
variable (f : ℕ → ℕ)
-- #check f ((1, 2) : ℕ × ℕ)

instance : Coe (ℕ × ℕ) ℕ where
  coe := fun (a, _) => a

#check f (1, 2)

example : f (1, 2) = f 1 := by
  rfl

end Hidden

/-
## Hierarchies

Structures can be organized into hierarchies, where more complex structures extend simpler ones. For example, a `Group` is a `Monoid` adding an inverse operation and the corresponding axioms. Hierarchies are useful because they allow us to reuse definitions and theorems. For instance, it would be convienient if any theorem about monoids automatically applies to groups.

At the very bottom of all hierarchies in Lean, we find data-carrying classes. The following class records that the given type `α` is endowed with a distinguished element called `one`. At this stage, it has no property at all.
-/

class One₁ (α : Type) where
  /-- The element one -/
  one : α

/-
The `class` command above defines a structure `One₁` with parameter `α : Type` and a single field `one`. It also marks this structure as a class so that arguments of type `One₁ α` for some type `α` will be inferrable using the instance resolution procedure.
-/

example (α : Type) [One₁ α] : α := One₁.one

/-
Our next task is to assign a notation to `One₁.one`. Since we don’t want collisions with the builtin notation for `1`, we will use `𝟙`. This is achieved by the following command where the first line tells Lean to use the documentation of `One₁.one` as documentation for the symbol `𝟙`.
-/

notation "𝟙" => One₁.one

example {α : Type} [One₁ α] : α := 𝟙

example {α : Type} [One₁ α] : (𝟙 : α) = 𝟙 := rfl

/-
We now want a data-carrying class recording a binary operation. We don’t want to choose between addition and multiplication for now so we’ll use diamond.
-/

class Dia₁ (α : Type) where
  dia : α → α → α

infixl:70 " ⋄ "   => Dia₁.dia

/-
As in the `One₁` example, the operation has no property at all at this stage. Let us now define the class of semigroup structures where the operation is denoted by `⋄`. For now, we define it by hand as a structure with two fields, a `Dia₁` instance and some `Prop`-valued field `dia_assoc` asserting associativity of `⋄`.

We would like to tell Lean that `Dia₁ α` should be treated as if its fields were fields of `Semigroup₁` itself. This also conveniently adds the `toDia₁` instance automatically. The `class` command supports this using the `extends` syntax as in:
-/

class Semigroup₁ (α : Type) extends Dia₁ α where
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

/-
We can only have the expression `a ⋄ b` if there is an instance of `Dia₁ α` for the type `α`.
-/
example {α : Type} [Dia₁ α] (a b : α) : α := a ⋄ b

/-
With `Semigroup₁ α`, Lean can also synthesize `Dia₁ α` for the type `α`, as a result, we can use the `⋄` operator too. This synthesis process is achieved by `Semigroup₁.toDia₁`.
-/
example {α : Type} [Semigroup₁ α] (a b : α) : α := a ⋄ b

#check Semigroup₁.toDia₁

class Semigroup₂ (α : Type) extends toDia₁ : Dia₁ α where
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

-- #check Semigroup₂.toDia₁
#check Semigroup₂.toDia₁

/-
Note this syntax is also available in the `structure` command.

The field name `toDia₁` is optional in the `extends` syntax. By default it takes the name of the class being extended and prefixes it with “to”.

------

Let us now try to combine a diamond operation and a distinguished one element with axioms saying this element is neutral on both sides.
-/

class DiaOneClass₁ (α : Type) extends One₁ α, Dia₁ α where
  /-- One is a left neutral element for diamond. -/
  one_dia : ∀ a : α, 𝟙 ⋄ a = a
  /-- One is a right neutral element for diamond -/
  dia_one : ∀ a : α, a ⋄ 𝟙 = a

/-
In the next example, we tell Lean that `α` has a `DiaOneClass₁` structure and state a property that uses both a `Dia₁` instance and a `One₁` instance.

In order to see how Lean finds those instances we set a tracing option whose result can be seen in the Infoview. This result is rather terse by default but it can be expanded by clicking on lines ending with black arrows. It includes failed attempts where Lean tried to find instances before having enough type information to succeed. The successful attempts do involve the instances generated by the `extends` syntax.
-/

set_option trace.Meta.synthInstance true in
example {α : Type} [DiaOneClass₁ α] (a b : α) : Prop := a ⋄ b = 𝟙            -- NOTE on this!

/-
Note that we don’t need to include extra fields where combining existing classes. Hence we can define monoids as:
-/

class Monoid₁ (α : Type) extends Semigroup₁ α, DiaOneClass₁ α

/-
While the above definition seems straightforward, it hides an important subtlety. Both `Semigroup₁ α` and `DiaOneClass₁ α` extend `Dia₁ α`, so one could fear that having a `Monoid₁ α` instance gives two unrelated diamond operations on `α`, one coming from a field `Monoid₁.toSemigroup₁` and one coming from a field `Monoid₁.toDiaOneClass₁`.

Indeed if we try to build a monoid class by hand using:
-/

class Monoid₂ (α : Type) where
  toSemigroup₁ : Semigroup₁ α
  toDiaOneClass₁ : DiaOneClass₁ α

/-
then we get two completely unrelated diamond operations `Monoid₂.toSemigroup₁.toDia₁.dia` and `Monoid₂.toDiaOneClass₁.toDia₁.dia`.

The version generated using the `extends` syntax does not have this problem.
-/

example {α : Type} [Monoid₁ α] :
  (Monoid₁.toSemigroup₁.toDia₁.dia : α → α → α) = Monoid₁.toDiaOneClass₁.toDia₁.dia := rfl

/- Monoid₂.mk {α : Type} (toSemigroup₁ : Semigroup₁ α) (toDiaOneClass₁ : DiaOneClass₁ α) : Monoid₂ α -/
#check Monoid₂.mk

/- Monoid₁.mk {α : Type} [toSemigroup₁ : Semigroup₁ α] [toOne₁ : One₁ α] (one_dia : ∀ (a : α), 𝟙 ⋄ a = a) (dia_one : ∀ (a : α), a ⋄ 𝟙 = a) : Monoid₁ α -/
#check Monoid₁.mk

/-
So we see that `Monoid₁` takes `Semigroup₁ α` argument as expected but then it won’t take a would-be overlapping `DiaOneClass₁ α` argument but instead tears it apart and includes only the non-overlapping parts.

And it also auto-generated an instance `Monoid₁.toDiaOneClass₁` which is not a field but has the expected signature which, from the end-user point of view, restores the symmetry between the two extended classes `Semigroup₁` and `DiaOneClass₁`.
-/

#check Monoid₁.toSemigroup₁
#check Monoid₁.toDiaOneClass₁

/-
We are now very close to defining groups. We could add to the monoid structure a field asserting the existence of an inverse for every element. But then we would need to work to access these inverses. In practice it is more convenient to add it as data. To optimize reusability, we define a new data-carrying class, and then give it some notation.
-/

class Inv₁ (α : Type) where
  /-- The inversion function -/
  inv : α → α

postfix:max "⁻¹" => Inv₁.inv

class Group₁ (G : Type) extends Monoid₁ G, Inv₁ G where
  inv_dia : ∀ a : G, a⁻¹ ⋄ a = 𝟙

/-
The above definition may seem too weak, we only ask that `a⁻¹` is a left-inverse of `a`. But the other side is automatic. In order to prove that, we need a preliminary lemma.
-/

open DiaOneClass₁ Semigroup₁ Group₁

lemma left_inv_eq_right_inv₁ {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← one_dia c, ← hba, dia_assoc, hac, dia_one b]

lemma inv_eq_of_dia {G : Type} [Group₁ G] {a b : G} (h : a ⋄ b = 𝟙) : a⁻¹ = b := by
  exact left_inv_eq_right_inv₁ (inv_dia a) h

lemma dia_inv {G : Type} [Group₁ G] (a : G) : a ⋄ a⁻¹ = 𝟙 := by
  have : a⁻¹⁻¹ ⋄ a⁻¹ = 𝟙 := by apply inv_dia
  rw [← dia_one a⁻¹⁻¹, ← inv_dia a, ← dia_assoc] at this
  repeat rw [inv_dia] at this
  rw [one_dia] at this
  assumption

/-
The hierarchies also work for the case of structures.

For example, we can define `Point3D`, `Point2DUpperHalfPlane`, `Point3DUpperHalfSpace` on the basis of `Point2D`.
-/

structure Point2D where
  x : ℝ
  y : ℝ

structure Point3D extends Point2D where
  z : ℝ

structure Point2DUpperHalfPlane extends Point2D where
  inUpperHalfPlane : 0 ≤ y

structure Point3DUpperHalfSpace extends Point3D, Point2DUpperHalfPlane where

#check Point3DUpperHalfSpace.mk
#check Point3DUpperHalfSpace.toPoint3D
#check Point3DUpperHalfSpace.toPoint2DUpperHalfPlane


/-
Exercise: Based on the natrual langauge description, define the hierarchies of order structures.
-/

namespace exercise2

/--
The class for binary relation called `le` (less than or equal to), using notation `≼`.
-/
class LE (α : Type*) where
  le : α → α → Prop

/- Type `≼` using `\preceq`. -/
infixl:70 " ≼ " => exercise.LE.le

/--
A preorder is a reflexive and transitive relation `≼`.
Make this structure extends LE.
-/
class PreOrder (α : Type*) extends LE α where
  refl : ∀ a : α, a ≼ a
  trans : ∀ a b c : α, a ≼ b → b ≼ c → a ≼ c

/--
A partial order is an antisymmetric preorder.
-/
class PartialOrder (α : Type*) extends PreOrder α where
  antisymm : ∀ a b : α, a ≼ b → b ≼ a → a = b

/--
A linear order is a total partial order. (i.e. for any two elements, either `a ≼ b` or `b ≼ a` holds.)
-/
class LinearOrder (α : Type*) extends PartialOrder α where
  totality : ∀ a b : α, a ≼ b ∨ b ≼ a

/-
Show that for any three elements `a`, `b` and `c` in a linear order, if the negation of `a ≼ b` and `b ≼ c` hold, then `c ≼ a` holds. The starting part is given below.
-/
theorem le_of_not_le_of_not_le {α : Type*} [LinearOrder α] {a b c : α}
  : ¬ a ≼ b → ¬ b ≼ c → c ≼ a := by
  intro h1 h2
  cases LinearOrder.totality a b with
  | inl ab => cases LinearOrder.totality b c with
      | inl bc => contradiction
      | inr cb => contradiction
  | inr ab => cases LinearOrder.totality b c with
      | inl bc => contradiction
      | inr cb =>
          apply PreOrder.trans c b a <;> assumption

/--
Show that the usual order "≤" on ℤ is a valid instance of the LinearOrder structure you defined above. The starting part is given below.
-/
instance Int.linearOrder : LinearOrder ℤ where
  le := Int.le
  refl := Int.le_refl
  trans := @Int.le_trans
  antisymm := @Int.le_antisymm
  totality := Int.le_total

end exercise2
