import Mathlib

open Topology Filter Polynomial Set

-- {((3 ^ ((1 : ℝ) / 5) + 1) / 2, (3 ^ ((1 : ℝ) / 5) - 1) / 2)}
/--
Find all pairs of real numbers $(x,y)$ satisfying the system of equations
\begin{align*}
\frac{1}{x}+\frac{1}{2y}&=(x^2+3y^2)(3x^2+y^2) \\
\frac{1}{x}-\frac{1}{2y}&=2(y^4-x^4).
\end{align*}
-/
theorem putnam_2001_b2
    (x y : ℝ)
    (hx : x ≠ 0)
    (hy : y ≠ 0)
    (eq1 eq2 : Prop)
    (heq1 : eq1 ↔ (1 / x + 1 / (2 * y) = (x ^ 2 + 3 * y ^ 2) * (3 * x ^ 2 + y ^ 2)))
    (heq2 : eq2 ↔ (1 / x - 1 / (2 * y) = 2 * (y ^ 4 - x ^ 4))) :
    eq1 ∧ eq2 ↔ (x, y) ∈ (({((3 ^ ((1 : ℝ) / 5) + 1) / 2, (3 ^ ((1 : ℝ) / 5) - 1) / 2)}) : Set (ℝ × ℝ) ) := by
  let a : ℝ := 3 ^ ((1 : ℝ) / 5)
  have ha5 : a ^ (5 : ℕ) = 3 := by
    dsimp [a]
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have ha6 : a ^ (6 : ℕ) = 3 * a := by
    calc
      a ^ (6 : ℕ) = a ^ (5 : ℕ) * a := by ring
      _ = 3 * a := by rw [ha5]
  constructor
  · intro h
    have h1 : 1 / x + 1 / (2 * y) = (x ^ 2 + 3 * y ^ 2) * (3 * x ^ 2 + y ^ 2) :=
      heq1.mp h.1
    have h2 : 1 / x - 1 / (2 * y) = 2 * (y ^ 4 - x ^ 4) := heq2.mp h.2
    have hA : x ^ 5 + 10 * x ^ 3 * y ^ 2 + 5 * x * y ^ 4 = 2 := by
      have hsum0 :
          (1 / x + 1 / (2 * y)) + (1 / x - 1 / (2 * y)) =
            (x ^ 2 + 3 * y ^ 2) * (3 * x ^ 2 + y ^ 2) + 2 * (y ^ 4 - x ^ 4) := by
        rw [h1, h2]
      have hsum :
          2 / x = (x ^ 2 + 3 * y ^ 2) * (3 * x ^ 2 + y ^ 2) +
            2 * (y ^ 4 - x ^ 4) := by
        rw [← hsum0]
        ring
      have hmul := congrArg (fun t : ℝ => x * t) hsum
      field_simp [hx] at hmul
      ring_nf at hmul ⊢
      nlinarith [hmul]
    have hB : 5 * x ^ 4 * y + 10 * x ^ 2 * y ^ 3 + y ^ 5 = 1 := by
      have hsub0 :
          (1 / x + 1 / (2 * y)) - (1 / x - 1 / (2 * y)) =
            (x ^ 2 + 3 * y ^ 2) * (3 * x ^ 2 + y ^ 2) - 2 * (y ^ 4 - x ^ 4) := by
        rw [h1, h2]
      have hsub :
          1 / y = (x ^ 2 + 3 * y ^ 2) * (3 * x ^ 2 + y ^ 2) -
            2 * (y ^ 4 - x ^ 4) := by
        rw [← hsub0]
        ring
      have hmul := congrArg (fun t : ℝ => y * t) hsub
      field_simp [hy] at hmul
      ring_nf at hmul ⊢
      nlinarith [hmul]
    have hplus : (x + y) ^ (5 : ℕ) = 3 := by
      ring_nf
      nlinarith [hA, hB]
    have hminus : (x - y) ^ (5 : ℕ) = 1 := by
      ring_nf
      nlinarith [hA, hB]
    have hinj : Function.Injective (fun z : ℝ => z ^ (5 : ℕ)) :=
      (show Odd 5 from by norm_num).strictMono_pow.injective
    have hplus_eq : x + y = a := by
      apply hinj
      change (x + y) ^ (5 : ℕ) = a ^ (5 : ℕ)
      rw [hplus, ha5]
    have hminus_eq : x - y = 1 := by
      apply hinj
      change (x - y) ^ (5 : ℕ) = (1 : ℝ) ^ (5 : ℕ)
      rw [hminus]
      norm_num
    have hxv : x = (a + 1) / 2 := by linarith
    have hyv : y = (a - 1) / 2 := by linarith
    rw [Set.mem_singleton_iff]
    exact Prod.ext (by simpa [a] using hxv) (by simpa [a] using hyv)
  · intro hmem
    have hp :
        (x, y) =
          (((3 ^ ((1 : ℝ) / 5) + 1) / 2, (3 ^ ((1 : ℝ) / 5) - 1) / 2) :
            ℝ × ℝ) := by
      simpa using hmem
    have hxv : x = (a + 1) / 2 := by
      dsimp [a]
      simpa using congrArg Prod.fst hp
    have hyv : y = (a - 1) / 2 := by
      dsimp [a]
      simpa [sub_eq_add_neg] using congrArg Prod.snd hp
    have hxc : (a + 1) / 2 ≠ 0 := by simpa [hxv] using hx
    have hyc : (a - 1) / 2 ≠ 0 := by simpa [hyv] using hy
    have ha_add_ne : a + 1 ≠ 0 := by
      intro h
      apply hxc
      rw [h]
      norm_num
    have hone_add_ne : 1 + a ≠ 0 := by simpa [add_comm] using ha_add_ne
    have ha_sub_ne : a - 1 ≠ 0 := by
      intro h
      apply hyc
      rw [h]
      norm_num
    have hneg_add_ne : -1 + a ≠ 0 := by simpa [sub_eq_add_neg, add_comm] using ha_sub_ne
    rw [heq1, heq2]
    constructor
    · rw [hxv, hyv]
      field_simp [hone_add_ne, hneg_add_ne, ha_add_ne, ha_sub_ne]
      ring_nf at ha5 ha6 ⊢
      nlinarith [ha5, ha6]
    · rw [hxv, hyv]
      field_simp [hone_add_ne, hneg_add_ne, ha_add_ne, ha_sub_ne]
      ring_nf at ha5 ha6 ⊢
      nlinarith [ha5, ha6]
