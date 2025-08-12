/- 
 - My Natual Number Type - NN
 - by FAN Pu 2025/08/12
 -
 - namesapce NN
 - type NN:
 -   zz : NN       -- zero
 -   ss : NN → NN  -- succ
 -
 -/

import Mathlib.Tactic

inductive NN where
  | zz : NN
  | ss (n : NN) : NN

namespace NN

def add (n m : NN) :=
  match n with
    | zz => m
    | ss p => ss (add p m)

instance NN_add : Add NN where
  add := add

theorem zero_add {n} : zz + n = n := by
  rfl

theorem succ_add {m n} : (ss m) + n = ss (m + n) := by
  rfl

theorem add_succ {m n : NN} : m + (ss n) = ss (m + n) := by
  cases m
  · rfl
  · repeat rw [succ_add]
    rw [add_succ]

theorem add_assoc (m n p : NN) : m + n + p = m + (n + p) := by
  cases m
  · repeat rw [zero_add]
  · repeat rw [succ_add]
    rw [add_assoc]

theorem add_zero  {n : NN} : n + zz = n := by
  cases n
  · rfl
  · rw [succ_add, add_zero]

theorem add_comm (m n : NN) : m + n = n + m := by
  cases m
  · rw [zero_add, add_zero]
  · rw [succ_add, add_succ, add_comm]

def mul (m n : NN) : NN :=
  match m with
  | zz => zz
  | ss m' => n + (mul m' n)

instance NN_mul : Mul NN where
  mul := mul

theorem zero_mul {n} : zz * n = zz := by
  rfl

theorem succ_mul {m n} : ss m * n = n + (m * n) := by
  rfl

theorem mul_zero {n} : n * zz = zz := by
  cases n
  · rfl
  · rw [succ_mul, zero_add, mul_zero]

theorem mul_succ {m n} : m * ss n = m + m * n := by
  cases m
  · repeat rw [zero_mul]
    rw [zero_add]
  · repeat rw [succ_mul]
    rw [mul_succ]
    repeat rw [succ_add]
    repeat rw [← add_assoc]
    rw [add_comm n]

/- TODO
theorem add_cancel_right (m n p : NN) : m + p = n + p → m = n := by
  intro h
  cases p
  · repeat rw [add_zero] at h
    assumption
  · repeat rw [add_succ] at h
    have u := add_cancel_right m n
    apply u
    rw [add_comm m, add_comm n] at h
    repeat rw [← succ_add] at h
    rw [← add_comm m, ← add_comm n] at h
    exact h

theorem add_mul (m n p : NN) : (m + n) * p = m * p + n * p := by
  cases p
  · repeat rw [mul_zero]
    rfl
  · repeat rw [mul_succ]
    rw [← add_assoc]
    rw [add_comm]
    nth_rw 5 [add_comm]
    nth_rw 2 [← add_assoc]
    rw [add_comm n m, add_assoc]
    nth_rw 4 [add_comm]
    sorry

theorem mul_assoc (m n p : NN) : m * n * p = m * (n * p) := by
  cases m
  · rfl
  · repeat rw [succ_mul]
    rw [add_mul, mul_assoc]
-/

end NN

section practice

example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_assoc, mul_comm, mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  repeat rw [← mul_assoc]
  rw [mul_comm a b]

example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm, mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc, mul_comm a b, mul_assoc]

example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a b c]
  rw [mul_assoc a e f]
  rw [h]

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [mul_comm, hyp'] at hyp
  -- You can use `rw [sub_self] at hyp` instead of following lines.
  have : a * b - a * b + a * b = a * b := by
    rw [sub_add_cancel (a * b)]
  rw [← hyp] at this
  nth_rw 2 [← zero_add (a * b)] at this
  exact add_right_cancel this

section

variable (a b c d : ℝ)

example  : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  rw [add_mul]
  repeat rw [mul_add]
  rw [← add_assoc]

end

end practice
