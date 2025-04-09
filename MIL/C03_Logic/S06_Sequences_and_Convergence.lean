import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

#print mul_lt_mul_right
example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h


theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  simp [ConvergesTo]
  intro ε εpos
  use 0
  intro n nge
  apply εpos

#print le_of_max_le_left
#print abs_add

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  dsimp [ConvergesTo]
  dsimp [ConvergesTo] at cs
  dsimp [ConvergesTo] at ct
  intro ε εpos
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n₀ nbound
  have nb1: n₀ ≥ Ns := by
    apply le_of_max_le_left nbound
  have nb2: n₀ ≥ Nt := by
    apply le_of_max_le_right nbound
  specialize hs n₀ nb1
  specialize ht n₀ nb2
  have hadd: |s n₀ + t n₀ - (a + b)| = |(s n₀ - a) + (t n₀ - b)| := by
    congr
    linarith
  rw [hadd]
  have hadd2: |(s n₀ - a) + (t n₀ - b)| ≤ |s n₀ - a| + |t n₀ - b|  := by
    apply abs_add
  have ineq : |s n₀ - a| + |t n₀ - b| < ε := by
    linarith
  apply lt_of_le_of_lt hadd2 ineq


theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  dsimp [ConvergesTo]
  dsimp [ConvergesTo] at cs
  intro ε epos
  have epos2 : ε / |c| > 0 := by
    apply div_pos epos acpos
  rcases cs (ε/|c|) epos2 with ⟨N₁, csn1⟩
  use N₁
  intro n₂ n2pos
  specialize csn1 n₂ n2pos
  have abs_mul_pos : |(s n₂ - a) * c| = |s n₂ - a| * |c| := by
    apply abs_mul
  have abs_simp : |(s n₂ - a) * c| = |s n₂ * c - a * c| := by
    congr
    linarith
  have csn1prime : |s n₂ - a| * |c| < (ε / |c|) * |c| := by
    apply mul_lt_mul_of_pos_right csn1 acpos
  rw [mul_comm, mul_comm c a]
  rw [← abs_simp]
  rw [abs_mul_pos]
  have nzc: |c| ≠ 0 := by linarith
  have : ε / |c| * |c| = ε := by
    apply div_mul_cancel₀ ε nzc
  rw [← this]
  assumption



theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n npos
  specialize h n npos
  have q1 : |s n| - |a| < 1 := by
    apply lt_of_le_of_lt _ h
    · have q2 : |s n - a + a| <= |s n - a| + |a| := by
        apply abs_add
      have q3 : |s n - a + a| = |s n| := by
        congr
        linarith

      linarith
  linarith



theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n npos
  have maxpos0 : n ≥ N₀ := by
    apply le_of_max_le_left npos
  have maxpos1 : n ≥ N₁ := by
    apply le_of_max_le_right npos
  specialize h₁ n maxpos1
  specialize h₀ n maxpos0
  rw [sub_zero]
  rw [sub_zero] at h₁
  have h₂ : |s n| ≤ B := by
    linarith
  have : |t n| * |s n| < ε / B * B := by
    by_cases htmp : s n = 0
    · rw [htmp]
      rw [abs_zero]
      rw [mul_zero]
      rw [div_mul_cancel₀]
      assumption
      linarith
    apply mul_lt_mul h₁ h₂
    apply abs_pos.mpr htmp
    linarith
  have abs1: |s n * t n| = |s n| * |t n| := by
    apply abs_mul
  rw [abs1]
  rw [mul_comm]
  have : ε = ε / B * B := by
    rw [div_mul_cancel₀]
    linarith
  rw [this]
  assumption


theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by
    apply abs_sub_pos.mpr abne
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by
    have nna :  N ≥ Na := by
      dsimp [N]
      apply le_max_left
    specialize hNa N nna
    exact hNa
  have absb : |s N - b| < ε := by
    have nnb :  N ≥ Nb := by
      dsimp [N]
      apply le_max_right
    specialize hNb N nnb
    exact hNb
  have : |a - b| < |a - b| := by
    have ineqadd : |s N - a| + |s N - b| < ε + ε := by
      linarith
    have abadd : |a - b| = |(s N - b) - (s N - a)| := by
      have : (s N - b) - (s N - a) = a - b := by linarith
      rw [this]
    have : ε + ε = |a - b| := by
      dsimp [ε]
      linarith
    rw [this] at ineqadd
    apply lt_of_le_of_lt _ ineqadd
    rw [abadd]
    rw [add_comm]
    apply abs_sub
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
