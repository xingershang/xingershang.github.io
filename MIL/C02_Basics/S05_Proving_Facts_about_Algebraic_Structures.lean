import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  · apply le_inf
    · apply inf_le_right
    · apply inf_le_left
  · apply le_inf
    · apply inf_le_right
    · apply inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  have qxz1 : ∀ x y z: α , (x ≤ z) -> (x ⊓ y ≤ z) := by
    intro x y z
    intros h₁
    have h₂ : x ⊓ y ≤ x := by apply inf_le_left
    apply le_trans h₂ h₁
  have qxz2 : ∀ x y z: α , (y ≤ z) -> (x ⊓ y ≤ z) := by
    intro x y z
    intros h₁
    have h₂ : x ⊓ y ≤ y := by apply inf_le_right
    apply le_trans h₂ h₁
  apply le_antisymm
  · apply le_inf
    · have h₁ : x ⊓ y ≤ x := by
        apply inf_le_left
      apply qxz1
      exact h₁
    · apply le_inf
      · apply qxz1
        apply inf_le_right
      · apply inf_le_right
  · apply le_inf
    · apply le_inf
      · apply inf_le_left
      · apply qxz2
        apply inf_le_left
    · have h₁ : y ⊓ z ≤ z := by
        apply inf_le_right
      apply qxz2
      exact h₁

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  · apply sup_le
    · apply le_sup_right
    · apply le_sup_left
  · apply sup_le
    · apply le_sup_right
    · apply le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  have qxz1 : ∀ x y z: α , (x ≤ z) -> (x ≤ y ⊔ z) := by
    intro x y z
    intros h₁
    have h₂ : z ≤ y ⊔ z := by apply le_sup_right
    apply le_trans h₁ h₂
  have qxz2 : ∀ x y z: α , (x ≤ z) -> (x ≤ z ⊔ y) := by
    intro x y z
    intros h₁
    have h₂ : z ≤ z ⊔ y := by apply le_sup_left
    apply le_trans h₁ h₂
  apply le_antisymm
  · apply sup_le
    apply sup_le
    · apply le_sup_left
    · apply qxz1
      apply le_sup_left
    · apply qxz1
      apply le_sup_right
  · apply sup_le
    · apply qxz2
      apply le_sup_left
    · apply sup_le
      · apply qxz2
        apply le_sup_right
      · apply le_sup_right

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · apply inf_le_left
  · apply le_inf
    · rfl
    . apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · apply sup_le
    · rfl
    · apply inf_le_left
  · apply le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h]
  rw [inf_comm (a ⊔ b) a]
  rw [absorb1]
  rw [inf_comm (a ⊔ b) c]
  rw [h]
  rw [← sup_assoc]
  rw [inf_comm c a]
  rw [absorb2]
  rw [inf_comm c b]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw [h]
  rw [sup_comm (a ⊓ b) a]
  rw [absorb2]
  rw [sup_comm (a ⊓ b) c]
  rw [h]
  rw [← inf_assoc]
  rw [sup_comm c a]
  rw [absorb1]
  rw [sup_comm]

end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  have h₀ : -a ≤ -a := by rfl
  have h₁ : a + -a ≤ b + -a := by
    apply add_le_add h h₀
  rw [add_neg_cancel] at h₁
  rw [← sub_eq_add_neg] at h₁
  exact h₁

example (h: 0 ≤ b - a) : a ≤ b := by
  have h₀ : a ≤ a := by rfl
  have h₁ : 0 + a ≤ b - a + a := by
    apply add_le_add h h₀
  rw [sub_add_cancel] at h₁
  rw [zero_add] at h₁
  exact h₁

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h₃ : 0 ≤ b - a := by
    have h₀ : -a ≤ -a := by rfl
    have h₁ : a + -a ≤ b + -a := by
      apply add_le_add h h₀
    rw [add_neg_cancel] at h₁
    rw [← sub_eq_add_neg] at h₁
    exact h₁
  have h₄ : 0 ≤ (b-a)*c := by
    apply mul_nonneg h₃ h'
  rw [sub_mul] at h₄
  have h₅ : a*c+0≤ a*c+(b*c-a*c) := by
    apply add_le_add_left h₄ (a*c)
  rw [add_zero] at h₅
  rw [add_comm, sub_add, sub_self, sub_zero] at h₅
  exact h₅

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

#check dist
#check nonneg_of_mul_nonneg_left

example (x y : X) : 0 ≤ dist x y := by
  have h : dist x x ≤ dist x y + dist y x := by
    apply dist_triangle
  rw [dist_comm y x] at h
  rw [dist_self] at h
  have h' : dist x y + dist x y = (dist x y) * 2 := by
    linarith
  rw [h'] at h
  apply nonneg_of_mul_nonneg_left h
  norm_num
end
