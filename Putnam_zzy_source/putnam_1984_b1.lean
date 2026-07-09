import Mathlib

open Topology Filter Nat

noncomputable abbrev putnam_1984_b1_solution : Polynomial ℝ × Polynomial ℝ :=
  (Polynomial.C 1 + (Polynomial.X + Polynomial.C 2),
    -Polynomial.X - Polynomial.C 2)

/--
Let $n$ be a positive integer, and define $f(n)=1!+2!+\dots+n!$. Find polynomials $P(x)$ and $Q(x)$ such that $f(n+2)=P(n)f(n+1)+Q(n)f(n)$ for all $n \geq 1$.
-/
theorem putnam_1984_b1
(f : ℕ → ℤ)
(hf : ∀ n > 0, f n = ∑ i : Set.Icc 1 n, ((i)! : ℤ))
: let (P, Q) := putnam_1984_b1_solution; ∀ n ≥ 1, f (n + 2) = P.eval (n : ℝ) * f (n + 1) + Q.eval (n : ℝ) * f n :=
by
  dsimp [putnam_1984_b1_solution]
  have hsum_succ : ∀ m : ℕ,
      (∑ i : Set.Icc 1 (m + 1), (((i : ℕ)!) : ℤ)) =
        (∑ i : Set.Icc 1 m, (((i : ℕ)!) : ℤ)) + (((m + 1)!) : ℤ) := by
    intro m
    rw [(Finset.sum_subtype (Finset.Icc 1 (m + 1)) (by intro x; simp [Set.mem_Icc])
      (fun i => (((i)!) : ℤ))).symm]
    rw [(Finset.sum_subtype (Finset.Icc 1 m) (by intro x; simp [Set.mem_Icc])
      (fun i => (((i)!) : ℤ))).symm]
    exact Finset.sum_Icc_succ_top (by omega) (fun i => (((i)!) : ℤ))
  have hstep : ∀ m : ℕ, m > 0 → f (m + 1) = f m + (((m + 1)!) : ℤ) := by
    intro m hm
    calc
      f (m + 1) = ∑ i : Set.Icc 1 (m + 1), ((i)! : ℤ) := hf (m + 1) (by omega)
      _ = (∑ i : Set.Icc 1 m, ((i)! : ℤ)) + (((m + 1)!) : ℤ) := by
        simpa using hsum_succ m
      _ = f m + (((m + 1)!) : ℤ) := by
        rw [← hf m hm]
  intro n hn
  have h1z : f (n + 1) = f n + (((n + 1)!) : ℤ) := hstep n (by omega)
  have h2z : f (n + 2) = f (n + 1) + (((n + 2)!) : ℤ) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep (n + 1) (by omega)
  have h1 : (f (n + 1) : ℝ) = (f n : ℝ) + (((n + 1)!) : ℝ) := by
    exact_mod_cast h1z
  have h2 : (f (n + 2) : ℝ) = (f (n + 1) : ℝ) + (((n + 2)!) : ℝ) := by
    exact_mod_cast h2z
  have hfact : (((n + 2)!) : ℝ) = (n + 2 : ℝ) * (((n + 1)!) : ℝ) := by
    have hnat : (n + 2)! = (n + 2) * (n + 1)! := by
      rw [show n + 2 = (n + 1) + 1 by omega, Nat.factorial_succ]
    exact_mod_cast hnat
  have hdiff : (((n + 1)!) : ℝ) = (f (n + 1) : ℝ) - (f n : ℝ) := by
    linarith
  rw [h2, hfact, hdiff]
  simp [Polynomial.eval_add, Polynomial.eval_neg, Polynomial.eval_X]
  ring
