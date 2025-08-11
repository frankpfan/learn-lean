def hello := "world"

variable (m n : Nat)

def f (x : Nat) : Nat := x + 1

example : f (f n) =  n + 2 := by
  rfl

theorem ex1 : m + n = n + m := by
  ring
