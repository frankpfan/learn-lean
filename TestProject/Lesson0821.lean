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

namespace exercise

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

/- Made it! But `Real` is noncomputable so I can't easily verify its correctness. -/
def Triangle.circumcenter (t : Triangle) : Point := by
  rcases t with ⟨A, B, C⟩
  apply StandardizedLine.intersection
  · apply Line.standardize
    exact Point.perpendicularBisector A B
  · apply Line.standardize
    exact Point.perpendicularBisector B C

theorem Triangle.circumcenter_distance (t : Triangle)
  : Point.distance t.A t.circumcenter = Point.distance t.B t.circumcenter := by
  sorry

end exercise
