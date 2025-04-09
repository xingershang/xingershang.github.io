import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg]
    apply h
  · rw [abs_of_neg]
    linarith
    apply h

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg]
    linarith
    apply h
  · rw [abs_of_neg]
    apply h

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x+y) with h|h
  · rw [abs_of_nonneg]
    have h1 : x ≤ |x| := le_abs_self x
    have h2 : y ≤ |y| := le_abs_self y
    linarith
    apply h
  · rw [abs_of_neg]
    have h1 : -x ≤ |x| := neg_le_abs_self x
    have h2 : -y ≤ |y| := neg_le_abs_self y
    linarith
    apply h

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  · intro h1
    rcases le_or_gt 0 y with h | h
    · rw [abs_of_nonneg] at h1
      left
      apply h1
      apply h
    · rw [abs_of_neg] at h1
      right
      apply h1
      apply h
  · intro h1
    rcases le_or_gt 0 y with h | h
    · rcases h1 with h2 | h3
      · rw [abs_of_nonneg]
        apply h2
        apply h
      · rw [abs_of_nonneg]
        linarith
        apply h
    · rcases h1 with h2 | h3
      · rw [abs_of_neg]
        linarith
        apply h
      · rw [abs_of_neg]
        linarith
        apply h

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  · intro h1
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg] at h1
      constructor
      · linarith
      · apply h1
      apply h
    · rw [abs_of_neg] at h1
      constructor
      · linarith
      · linarith
      apply h
  · intro h1
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg]
      have ⟨h2, h3⟩ := h1
      apply h3
      apply h
    · rw [abs_of_neg]
      have ⟨h2, h3⟩ := h1
      linarith
      apply h

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  have lem : ∀ (x y : ℝ), x^2+y^2 >= 0 := by
    intro x y
    have : x^2 >= 0 := by apply pow_two_nonneg
    have : y^2 >= 0 := by apply pow_two_nonneg
    linarith
  rcases h with ⟨x, y, ⟨h1, rfl⟩ | ⟨ h2, rfl⟩⟩
  · apply lem
  · have : x^2+y^2 >= 0 := by apply lem
    linarith

#print eq_zero_or_eq_zero_of_mul_eq_zero
example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  rw [pow_two] at h
  have h1 : (x - 1) * (x + 1) = 0 := by
    linarith
  have h2 : x - 1 = 0 ∨ x + 1 = 0 := by
    apply eq_zero_or_eq_zero_of_mul_eq_zero
    apply h1
  rcases h2 with h3 | h4
  · left
    linarith
  · right
    linarith

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h1 : (x - y) * (x + y) = 0 := by
    linarith
  have h2 : x - y = 0 ∨ x + y = 0 := by
    apply eq_zero_or_eq_zero_of_mul_eq_zero
    apply h1
  rcases h2 with h3 | h4
  · left
    linarith
  · right
    linarith

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  rw [pow_two] at h
  have h1 : (x - 1) * (x + 1) = 0 := by
    rw [mul_add]
    rw [sub_mul]
    rw [sub_mul]
    ring
    rw [pow_two]
    rw [h]
    ring
  have h2 : x - 1 = 0 ∨ x + 1 = 0 := by
    apply eq_zero_or_eq_zero_of_mul_eq_zero
    apply h1
  rcases h2 with h3 | h4
  · left
    have h4 : x - 1 + 1 = 1 := by
      rw [h3]
      ring
    rw [← h4]
    ring
  · right
    have h5 : x + 1 - 1 = -1 := by
      rw [h4]
      ring
    rw [← h5]
    ring

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  rw [pow_two] at h
  have h1 : (x - y) * (x + y) = 0 := by
    rw [mul_add]
    rw [sub_mul]
    rw [sub_mul]
    ring
    rw [pow_two]
    rw [h]
    ring
  have h2 : x - y = 0 ∨ x + y = 0 := by
    apply eq_zero_or_eq_zero_of_mul_eq_zero
    apply h1
  rcases h2 with h3 | h4
  · left
    have h4 : x - y + y = y := by
      rw [h3]
      ring
    rw [← h4]
    ring
  · right
    have h5 : x + y - y = -y := by
      rw [h4]
      ring
    rw [← h5]
    ring

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  · intro h
    by_cases hp : P
    · right
      apply h hp
    · left
      apply hp
  · intro h
    rcases h with h1 | h2
    · intro hp
      exfalso
      apply h1 hp
    · intro hp
      apply h2
