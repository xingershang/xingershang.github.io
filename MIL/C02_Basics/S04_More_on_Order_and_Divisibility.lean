import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

#check le_max_left
#check max_le

example : max a b = max b a := by
  apply ge_antisymm
  · have h₁: b ≤ max a b := by
      apply le_max_right
    have h₂: a ≤ max a b := by
      apply le_max_left
    apply max_le h₁ h₂
  · have h₁: b ≤ max b a := by
      apply le_max_left
    have h₂: a ≤ max b a := by
      apply le_max_right
    apply max_le h₂ h₁

example : min (min a b) c = min a (min b c) := by
  have qxz1 : ∀ x y z: ℝ , (x ≤ z) -> (min x y ≤ z) := by
    intro x y z
    intros h₁
    have h₂ : min x y ≤ x := by apply min_le_left
    apply le_trans h₂ h₁
  have qxz2 : ∀ x y z: ℝ , (y ≤ z) -> (min x y ≤ z) := by
    intro x y z
    intros h₁
    have h₂ : min x y ≤ y := by apply min_le_right
    apply le_trans h₂ h₁
  apply le_antisymm
  · have h₁ : min (min a b) c ≤ a := by
      have h₃ : min a b ≤ a := by
        apply min_le_left
      apply qxz1
      apply h₃
    have h₂ : min (min a b) c ≤ min b c := by
      apply le_min
      · apply qxz1
        apply qxz2
        rfl
      · apply qxz2
        rfl
    apply le_min h₁ h₂
  · have h₁ : min a (min b c) ≤ min a b := by
      apply le_min
      · apply min_le_left
      · apply qxz2
        apply qxz1
        rfl
    have h₂ : min a (min b c) ≤ c := by
      apply qxz2
      apply qxz2
      rfl
    apply le_min h₁ h₂

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  · have h₁ : min a b ≤ a := by
      apply min_le_left
    apply add_le_add_right h₁
  · have h₁ : min a b ≤ b := by
      apply min_le_right
    linarith

#check add_neg_cancel_right
example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · apply aux
  · have h₁ : min (a+c) (b+c) + -c ≤ min (a+c+-c) (b+c+-c) := by
      apply aux
    have h₂ : min (a+c) (b+c) ≤ min (a+c+-c) (b+c+-c) + c := by
      linarith
    rw [add_neg_cancel_right] at h₂
    rw [add_neg_cancel_right] at h₂
    exact h₂

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  have h₁ : |a - b + b| ≤ |a - b| + |b| := by
    apply abs_add (a- b) b
  rw [sub_add_cancel a b] at h₁
  linarith

end

section
variable (w x y z : ℕ)

#check dvd_trans
#check dvd_mul_left
#check dvd_mul_of_dvd_left

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  apply dvd_add
  · have h₂ : x ∣ (x * z) := by
      apply dvd_mul_right
    apply dvd_mul_of_dvd_right
    exact h₂
  · apply dvd_mul_left
  · have h₃ : w ∣ w ^ 2 := by
      apply dvd_mul_left
    apply dvd_trans h h₃
end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

#check Nat.dvd_gcd
#check Nat.gcd_dvd_left

example : Nat.gcd m n = Nat.gcd n m := by
  apply dvd_antisymm
  · apply Nat.dvd_gcd
    · apply Nat.gcd_dvd_right
    · apply Nat.gcd_dvd_left
  · apply Nat.dvd_gcd
    · apply Nat.gcd_dvd_right
    · apply Nat.gcd_dvd_left

end
