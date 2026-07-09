import Mathlib

open Topology Filter Nat

-- Note: This problem may have multiple correct answers.
-- (Polynomial.X + 3, -Polynomial.X - 2)
/--
Let $n$ be a positive integer, and define $f(n)=1!+2!+\dots+n!$. Find polynomials $P(x)$ and $Q(x)$ such that $f(n+2)=P(n)f(n+1)+Q(n)f(n)$ for all $n \geq 1$.
-/
theorem putnam_1984_b1
(f : ℕ → ℤ)
(hf : ∀ n > 0, f n = ∑ i : Set.Icc 1 n, ((i)! : ℤ))
: let (P, Q) := ((Polynomial.X + 3, -Polynomial.X - 2) : Polynomial ℝ × Polynomial ℝ ); ∀ n ≥ 1, f (n + 2) = P.eval (n : ℝ) * f (n + 1) + Q.eval (n : ℝ) * f n := by
  intro n hn
  have hsum_succ : ∀ k : ℕ,
      (∑ i : Set.Icc 1 (k + 1), ((i)! : ℤ)) =
        (∑ i : Set.Icc 1 k, ((i)! : ℤ)) + ((k + 1)! : ℤ) := by
    intro k
    rw [show (∑ i : Set.Icc 1 (k + 1), ((i)! : ℤ)) = ∑ i ∈ Finset.Icc 1 (k + 1), ((i)! : ℤ) by
      symm
      exact Finset.sum_subtype (Finset.Icc 1 (k + 1)) (by intro x; simp [Set.mem_Icc]) (fun i => ((i)! : ℤ))]
    rw [show (∑ i : Set.Icc 1 k, ((i)! : ℤ)) = ∑ i ∈ Finset.Icc 1 k, ((i)! : ℤ) by
      symm
      exact Finset.sum_subtype (Finset.Icc 1 k) (by intro x; simp [Set.mem_Icc]) (fun i => ((i)! : ℤ))]
    rw [Finset.sum_Icc_succ_top]
    omega
  have hdiff1 : f (n + 1) = f n + ((n + 1)! : ℤ) := by
    rw [hf (n + 1) (by omega), hf n hn, hsum_succ n]
  have hdiff2 : f (n + 2) = f (n + 1) + ((n + 2)! : ℤ) := by
    rw [show n + 2 = n + 1 + 1 by omega]
    rw [hf (n + 1 + 1) (by omega), hf (n + 1) (by omega), hsum_succ (n + 1)]
  have hfac_nat : (n + 2)! = (n + 2) * (n + 1)! := by
    simpa [show n + 2 = n + 1 + 1 by omega] using (Nat.factorial_succ (n + 1))
  have hfac : ((n + 2)! : ℤ) = ((n : ℤ) + 2) * ((n + 1)! : ℤ) := by
    rw [hfac_nat]
    norm_num
  have hZ : f (n + 2) = ((n : ℤ) + 3) * f (n + 1) + (-(n : ℤ) - 2) * f n := by
    rw [hdiff2, hfac, hdiff1]
    ring
  have hR : (f (n + 2) : ℝ) = ((n : ℝ) + 3) * (f (n + 1) : ℝ) + (-(n : ℝ) - 2) * (f n : ℝ) := by
    exact_mod_cast hZ
  simpa [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_X] using hR
