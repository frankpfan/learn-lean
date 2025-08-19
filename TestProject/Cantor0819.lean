/-
 - Cantor─Bernstain Theorem - Notes
 -
 - f : A → B,
 - g : B → A,
 - Inj f, Inj g.
 - ⊢ ∃ h : A → B, Bij h
 - 
 - (In Lean, it is
 -     {α β : Type}
 -     {f : α → β} (hf : Function.Injective f)
 -     {g : β → α} (hg : Function.Injective g)
 -     ⊢ ∃ h : α → β, Function.Bijective h
 - )
 -
 - Let
 -   C₀   := A \ g B                                        (#)
 -   Cₙ₊₁ := (g ∘ f) Cₙ
 - Let
 -   h a := | f a   ;  If ∃ n ∈ ℕ, a ∈ Cₙ,                  ($)
 -          | g⁻¹ a ;  Otherwise.
 -
 - (Inj h) For a₁,a₂ ∈ A, if h a₁ = h a₂, then ...(to be continued)
 - (Sur h) For b ∈ B, cases on g b ∈ Cₘ:
 -      If g b ∈ Cₘ, cases on m:
 -          m = 0, g b ∈ C₀ = A \ g B, i.e. g b ∉ g B, False.
 -          m > 0, g b ∈ (g ∘ f)(Cₘ₋₁),
 -              then ∃ a ∈ Cₘ₋₁ s.t. g b = g (f a).
 -              By Inj g, f a = b.
 -              And h a = f a, so h a = b.
 -      If g b ∉ C, then h (g b) = g⁻¹ (g b) = b.
 -          So take a = g b.
 -/

import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Defs
import Mathlib.Tactic.ApplyFun
import Mathlib.Data.Set.Insert

/- See equation (#) -/
def C {α β : Type} (f : α → β) (g : β → α) (k : ℕ) : Set α :=
  match k with
  | 0 => {x | x ∉ Set.range g}
  | k + 1 => g '' (f '' (C f g k))

lemma inv_g {α β : Type} {f : α → β} {g : β → α}
            {a : α} (ha : ¬ ∃ n : ℕ, a ∈ C f g n) :
    ∃ y, g y = a := by
  push_neg at ha
  have ha := ha 0
  simp [C] at ha
  exact ha

/- See equation ($) -/
noncomputable def h {α β : Type} (f : α → β) (g : β → α) : α → β := by
  intro a
  by_cases hn : ∃ n : ℕ, a ∈ C f g n
  · exact f a
  · exact (inv_g hn).choose

lemma hinj {α β : Type} {f : α → β} (hf : Function.Injective f) {g : β → α} :
    Function.Injective (h f g) := by
  intro x y hxy
  by_cases h₁ : ∃ n : ℕ, x ∈ C f g n
  · by_cases h₂ : ∃ n : ℕ, y ∈ C f g n
    · simp [h, dif_pos h₁, dif_pos h₂] at hxy  -- `dif` for dependent if-then-else
      exact hf hxy
    · simp [h, dif_pos h₁, dif_neg h₂] at hxy
      rcases h₁ with ⟨n, hx⟩
      have : ∃ m, y ∈ C f g m := by
        use n + 1
        simp [C]
        exact ⟨x, ⟨hx, hxy ▸ (inv_g h₂).choose_spec⟩⟩
      exact False.elim <| h₂ this
  · by_cases h₂ : ∃ n : ℕ, y ∈ C f g n
    · simp [h, dif_pos h₂, dif_neg h₁] at hxy
      rcases h₂ with ⟨n, hx⟩
      have : ∃ m, x ∈ C f g m := by
        use n + 1
        simp [C]  -- simp only [C, Set.mem_image, exists_exists_and_eq_and]
        exact ⟨y, ⟨hx, hxy ▸ (inv_g h₁).choose_spec⟩⟩
      exact False.elim <| h₁ this
    · simp [h, dif_neg h₂,dif_neg h₁] at hxy
      rw [← (inv_g h₁).choose_spec, ← (inv_g h₂).choose_spec, hxy]

lemma hsurj {α β : Type} {f : α → β} {g : β → α} (hg : Function.Injective g) :
    Function.Surjective (h f g) := by
  intro b
  by_cases hb : ∃ n, g b ∈ C f g n
  · rcases hb with ⟨n, hn⟩
    by_cases hn' : n = 0
    · simp [hn', C] at hn
      exact False.elim <| (hn b) rfl
    · rw [← Nat.succ_pred_eq_of_ne_zero hn'] at hn
      simp [C] at hn
      rcases hn with ⟨a, ha⟩
      use a
      unfold h
      rw [dif_pos ⟨n - 1, ha.1⟩]
      exact hg ha.2
  · use g b
    apply_fun g
    simp [h, dif_neg hb, (inv_g hb).choose_spec]

theorem CantorBernstein {α β : Type} {f : α → β} (hf : Function.Injective f) {g : β → α} (hg : Function.Injective g) :
    ∃ h : α → β, Function.Bijective h := by
  use (h f g)
  exact ⟨hinj hf, hsurj hg⟩

/- Cantor's Theorem -/

-- def power (α : Type) : Type := Set α

theorem Cantor {α : Type}
    : ∀ g : α → Set α, ¬ Function.Surjective g := by
  -- by_contra hc
  intro g surjg
  let S := { a : α |  a ∉ g a }
  have exb : ∃ b : α, g b = S := by
    exact surjg S
  rcases exb with ⟨b, gbS⟩
  by_cases h : b ∈ S
  · have := h.out
    rw [← gbS] at h
    exact this h
  · have : b ∈ S := by
      apply Set.mem_setOf.mpr
      rw [← gbS] at h
      exact h
    apply h
    exact this

def cle (α β : Type) : Prop := ∃ f : α → β, Function.Injective f
def ceq (α β : Type) : Prop := ∃ f : α → β, Function.Bijective f
def clt (α β : Type) : Prop := cle α β ∧ ¬ ceq α β

theorem Cantor' (α : Type) : clt α (Set α) := by
  simp [clt]
  let f (w : α) : Set α := { w }
  constructor
  have : Function.Injective f := by
    simp [f]
    apply Set.singleton_injective
  use f
  by_contra h
  have (g : α → Set α) (hg : Function.Bijective g) : False := by
    exact Cantor g hg.2
  apply this
  rcases h with ⟨f', bijf⟩
  sorry
