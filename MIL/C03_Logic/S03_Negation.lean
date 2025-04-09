import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S03

section
variable (a b : ℝ)

example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  intro fnlb
  rcases fnlb with ⟨a, fnlbb⟩
  rcases h a with ⟨x, hx⟩
  have : f x >= a := by
    apply fnlbb
  linarith

#print FnUb
#print FnHasUb

example : ¬FnHasUb fun x ↦ x := by
  intros h1
  rcases h1 with ⟨B, h2⟩
  have : (fun x ↦ x) B+1 <= B := by
    apply h2
  dsimp at this
  linarith


#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

#print Monotone
example (h : Monotone f) (h' : f a < f b) : a < b := by
  apply lt_of_not_ge
  intro h1
  have : f a >= f b := by
    apply h
    apply h1
  linarith

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro h1
  have : f a <= f b := by
    apply h1
    apply h
  linarith

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by
    intro x y
    have fxzero : f x = 0 := by rfl
    rw [fxzero]
    intro
    linarith
  have h' : f 1 ≤ f 0 := le_refl _
  have : (1:ℝ) <= (0:ℝ) := by
    apply h monof h'
  linarith

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro h'
  have : x < x/2 := by
    apply h
    linarith
  linarith

end


section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro a
  intro h1
  apply h
  use a

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  intro h1
  rcases h1 with ⟨a, h2⟩
  apply h a
  apply h2

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h0
  apply h
  intro a
  by_contra h1
  apply h0
  use a

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro h1
  rcases h with ⟨a, h3⟩
  have : P a := by
    apply h1
  apply h3 this


example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ¬¬Q) : Q := by
  by_contra h1
  apply h
  apply h1

example (h : Q) : ¬¬Q := by
  intro h1
  apply h1 h

end


section
variable (f : ℝ → ℝ)

#print FnHasUb
#print FnUb

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro a
  by_contra h0
  have h1 : ∀ (x : ℝ), f x <= a := by
    intro b
    by_contra h5
    apply h0
    use b
    linarith
  have h2 : FnHasUb f := by
    use a
    have h3 : FnUb f a := by
      apply h1
    apply h3
  apply h h2

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  dsimp [Monotone] at h
  push_neg at h
  apply h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

end

section
variable (a : ℕ)

example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction

end
