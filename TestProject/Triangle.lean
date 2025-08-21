import Mathlib

noncomputable section
/-
First we define the structure of points on 2 dimensional Euclidean space.
-/
@[ext]
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
structure Line where
  base : Point
  coef_x : ℝ
  coef_y : ℝ
  non_singular : coef_x ≠ 0 ∨ coef_y ≠ 0

structure StandardizedLine where
  A : ℝ
  B : ℝ
  C : ℝ
  non_singular : A ≠ 0 ∨ B ≠ 0

namespace Line

def standardize (m : Line) : StandardizedLine where
  A := m.coef_y
  B := - m.coef_x
  C := m.coef_x * m.base.y - m.coef_y * m.base.x
  non_singular := by
    have h := m.non_singular
    grind

instance instLineStandard : Coe Line StandardizedLine where
  coe := standardize

end Line

namespace StandardizedLine

def intersection (m n : StandardizedLine) (hnp : m.A * n.B ≠ m.B * n.A) : Point := by
  let Δ := m.A * n.B - n.A * m.B
  have : Δ ≠ 0 := by grind
  let Δx := m.B * n.C - n.B * m.C
  let Δy := m.C * n.A - n.C * m.A
  exact Point.mk (Δx / Δ) (Δy / Δ)

end StandardizedLine

namespace Point

def perpendicularBisector (A B : Point) (h : A ≠ B) : Line where
  base := ⟨(A.x + B.x) / 2, (A.y + B.y) / 2⟩
  coef_x := A.y - B.y
  coef_y := B.x - A.x
  non_singular := by
    have : ¬ (A.x = B.x ∧ A.y = B.y) := by
      intro g
      rcases g with ⟨left, right⟩
      apply h
      exact Point.ext left right
    grind

def distance (P Q : Point) : ℝ :=
  Real.sqrt ((P.x - Q.x) ^ 2 + (P.y - Q.y) ^ 2)

end Point

/-
 - Made it! But `Real` is noncomputable so I can't easily verify its correctness.
 - (But by replacing ℝ with ℚ, I have found it is correct.)
 - But it's just hard to prove the existence of the intersection point. So `sorry`.
 -/
def Triangle.circumcenter (t : Triangle) (h1 : t.A ≠ t.B) (h2 : t.B ≠ t.C) (h3 : t.C ≠ t.A)
  : Point := by
  rcases t with ⟨A, B, C⟩
  simp at h1 h2 h3 
  let m : StandardizedLine := by
    exact ↑(Point.perpendicularBisector A B h1)  -- Coerce the line using `standardize`.
  let n : StandardizedLine := by
    exact ↑(Point.perpendicularBisector B C h2)  -- Same.
  apply StandardizedLine.intersection m n
  sorry

theorem Triangle.circumcenter_distance (t : Triangle)
  : Point.distance t.A t.circumcenter = Point.distance t.B t.circumcenter := by
  sorry

end
