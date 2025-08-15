import Mathlib.Tactic
-- import Mathlib.Data.Real.Irrational

-- #check by_contra
-- #help tactic push_neg

example (h : ¬ 1 = 2) : 1 ≠ 2 := by
  push_neg at h
  assumption

example (h : ¬ 1 = 2) : 1 ≠ 2 := by
  by_contra
  contradiction

section
variable (P Q : Prop)

example : (P ∧ Q) → (∀ _ : Nat, P) ∨ (∃ _ : Nat, Q) := by
  intro ⟨p, q⟩
  left
  intro a
  assumption

end

example : ∃ n : Nat, n + 2 > 5 := by
  use 4
  simp

example (P Q R S : Prop) (h₁ : P ∧ Q ∧ R) (h₂ : R → S) : S := by
  apply h₂
  exact h₁.2.2

example (P Q R S T : Prop) (h : ((P ∧ T) ∨ (Q ∧ ¬ R)) ∧ (R ∨ (S ∧ T))) : T := by
  -- Just `tauto` is OK. But--
  rcases h with ⟨left, right⟩
  rcases right
  · cases left with
    | inl qt =>
        apply And.right
        assumption
    | inr qnr =>
        cases qnr
        contradiction
  · apply And.right
    assumption

section choose_em
open Classical

example (P Q R : Prop) (h : Q → R) : P ∨ Q → P ∨ R := by
  intro u
  cases u
  · left; assumption
  · right; apply h; assumption

namespace proof

theorem classical_em (p : Prop) : p ∨ ¬p := by
  let U (x : Prop) : Prop := x = True ∨ p
  let V (x : Prop) : Prop := x = False ∨ p
  have exU : ∃ x, U x := by
    use True
    unfold U
    left
    rfl
  have exV : ∃ x, V x := by
    use False
    unfold V
    left
    rfl
  let u : Prop := Classical.choose exU
  let v : Prop := Classical.choose exV
  have u_def : U u := Classical.choose_spec exU
  have v_def : V v := Classical.choose_spec exV
  have not_uv_or_p : u ≠ v ∨ p := by
    unfold U at u_def
    unfold V at v_def
    cases' u_def with hu hp
    · cases' v_def with hv hp'
      · left
        rw [hu]
        rw [hv]
        exact true_ne_false
      · right
        exact hp'
    · right
      exact hp
  have p_implies_uv : p → u = v := by
    intro hp
    have U_eq_V : U = V := by
      unfold U V
      ext x
      constructor
      · intro h
        right
        exact hp
      · intro h
        right
        exact hp
    have : ∀ exU exV, @Classical.choose _ U exU = @Classical.choose _ V exV := by
      rw [U_eq_V]
      intro exu exv
      rfl
    unfold u v
    exact this exU exV
  cases' not_uv_or_p with hne hp
  · right
    by_contra hp
    have he : u = v := by exact p_implies_uv hp
    contradiction
  · left
    exact hp

end proof 


section exercise
variable (p q r : Prop)

example (hnp : ¬p) (hq : q) (hqp : q → p) : r := by
  by_contra
  apply hnp
  apply hqp
  exact hq

/-- Don't forget `push_neg`!! -/
example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro hnpq
  push_neg at hnpq
  by_cases p
  right
  apply hnpq
  assumption
  left
  assumption
 
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  constructor
  intro pqr pq
  cases pq
  apply pqr
  repeat assumption
  intro pqr p q
  apply pqr
  constructor
  repeat assumption
 
/-- **Boss level** -/
example {s} : (p → r ∨ s) → ((p → r) ∨ (p → s)) := by
  intro p_imp_r_or_s
  by_cases hp : p
  · cases p_imp_r_or_s hp
    · left
      intro p
      assumption
    · right
      intro p
      assumption
  · left
    intro p
    contradiction

end exercise

section exercise2

variable (α : Type) (p q : α → Prop) (r : Prop)
example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z := by
  use y

/-- A little bit hard. -/
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  constructor
  intro a
  rcases a with ⟨w, h⟩
  cases h with
  | inl pw => sorry
  | inr qw => sorry
  sorry
  
/-- Very hard. -/
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
  constructor
  intro expr
  rcases expr with ⟨x, px⟩
  intro h
  apply px
  apply h
  intro h
  sorry

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro h
  sorry

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)
/--
Consider the "barber paradox," that is, the claim that in a certain town there is a (male) barber that shaves all and only the men who do not shave themselves. Prove that this is a contradiction: -/
example (h : ∀ x : men, shaves barber x ↔ ¬shaves x x) : False := by
  sorry

end exercise2
