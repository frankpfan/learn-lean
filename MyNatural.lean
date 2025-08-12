-- command #eval --

#eval 4 / 3

-- define --

def x : Nat := 3

#check x

-- logic --

variable (A I O U P Q : Prop)

example (h1 : A ∧ I) (h2 : O ∧ U) : A ∧ U := by
  have a := h1.left
  have u := h2.right
  exact ⟨a, u⟩

-- my natual number type --

inductive ℕ where
  | 𝕫 : ℕ
  | 𝕤 (n : ℕ) : ℕ

section on_ℕ

open ℕ

def add (n m : ℕ) :=
  match n with
    | 𝕫 => m
    | 𝕤 p => 𝕤 (add p m)

instance ℕ_add : Add ℕ  where
  add := add

theorem zero_add {n} : 𝕫 + n = n := by
  rfl

theorem succ_add {m n} : (𝕤 m) + n = 𝕤 (m + n) := by
  rfl

theorem add_succ {m n : ℕ} : m + (𝕤 n) = 𝕤 (m + n) := by
  cases m
  · rfl
  · repeat rw [succ_add]
    rw [add_succ]

theorem add_assoc {m n p : ℕ} : (m + n) + p = m + (n + p) := by
  cases m
  · repeat rw [zero_add]
  · repeat rw [succ_add]
    rw [add_assoc]

theorem add_zero {n : ℕ} : n + 𝕫 = n := by
  cases n
  · rfl
  · rw [succ_add, add_zero]

theorem add_comm {m n : ℕ} : m + n = n + m := by
  cases m
  · rw [zero_add, add_zero]
  · rw [succ_add, add_succ, add_comm]

end on_ℕ
