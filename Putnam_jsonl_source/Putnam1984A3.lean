import Mathlib

open Topology Filter
open Matrix
open scoped Matrix

-- (MvPolynomial.X 2) ^ 2 * ((MvPolynomial.X 0) ^ 2 - (MvPolynomial.X 1) ^ 2)
/--
Let $n$ be a positive integer. Let $a,b,x$ be real numbers, with $a \neq b$, and let $M_n$ denote the $2n \times 2n$ matrix whose $(i,j)$ entry $m_{ij}$ is given by
\[
m_{ij}=\begin{cases}
x & \text{if }i=j, \\
a & \text{if }i \neq j\text{ and }i+j\text{ is even}, \\
b & \text{if }i \neq j\text{ and }i+j\text{ is odd}.
\end{cases}
\]
Thus, for example, $M_2=\begin{pmatrix} x & b & a & b \\ b & x & b & a \\ a & b & x & b \\ b & a & b & x \end{pmatrix}$. Express $\lim_{x \to a} \det M_n/(x-a)^{2n-2}$ as a polynomial in $a$, $b$, and $n$, where $\det M_n$ denotes the determinant of $M_n$.
-/
theorem putnam_1984_a3
(n : ℕ)
(a b : ℝ)
(Mn : ℝ → Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
(polyabn : Fin 3 → ℝ)
(npos : n > 0)
(aneb : a ≠ b)
(hMn : Mn = fun x : ℝ => fun i j : Fin (2 * n) => if i = j then x else if Even (i.1 + j.1) then a else b)
(hpolyabn : polyabn 0 = a ∧ polyabn 1 = b ∧ polyabn 2 = n)
: Tendsto (fun x : ℝ => (Mn x).det / (x - a) ^ (2 * n - 2)) (𝓝[≠] a) (𝓝 (MvPolynomial.eval polyabn ((MvPolynomial.X 2) ^ 2 * ((MvPolynomial.X 0) ^ 2 - (MvPolynomial.X 1) ^ 2) : MvPolynomial (Fin 3) ℝ ))) := by
  classical
  have _haneb : a ≠ b := aneb
  let e : Fin n × Fin 2 ≃ Fin (2 * n) :=
    finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2))
  let U : Matrix (Fin n × Fin 2) (Fin 2) ℝ := fun i p => if i.2 = p then 1 else 0
  let C : Matrix (Fin 2) (Fin 2) ℝ := fun p q => if p = q then a else b
  have hval (i : Fin n × Fin 2) : (e i).val = i.2.val + 2 * i.1.val := by
    rfl
  have hpar (i j : Fin n × Fin 2) : Even ((e i).val + (e j).val) ↔ i.2 = j.2 := by
    rw [hval i, hval j]
    rcases i with ⟨r, p⟩
    rcases j with ⟨s, q⟩
    fin_cases p <;> fin_cases q <;> simp [Nat.even_add]
  have hUC (i j : Fin n × Fin 2) : (U * C * Uᵀ) i j = if i.2 = j.2 then a else b := by
    rcases i with ⟨r, p⟩
    rcases j with ⟨s, q⟩
    fin_cases p <;> fin_cases q <;>
      simp [U, C, Matrix.mul_apply, Fin.sum_univ_two]
  have hmatrix (x : ℝ) :
      (Mn x).submatrix e e =
        (x - a) • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) + (U * C) * Uᵀ := by
    ext i j
    rw [hMn]
    simp only [submatrix_apply]
    by_cases hij : i = j
    · subst j
      simp [hUC]
    · have he_ne : e i ≠ e j := fun h => hij (e.injective h)
      have hparij := hpar i j
      by_cases hbit : i.2 = j.2
      · simp [he_ne, hUC, hbit, hparij.mpr hbit, hij]
      · have hnotpar : ¬ Even ((e i).val + (e j).val) := fun hp => hbit (hparij.mp hp)
        simp [he_ne, hUC, hbit, hnotpar, hij]
  have hUC_entries (p q : Fin 2) :
      (Uᵀ * (U * C)) p q = (n : ℝ) * (if p = q then a else b) := by
    simp only [Matrix.mul_apply, transpose_apply, U, C]
    fin_cases p <;> fin_cases q <;> simp [Fintype.sum_prod_type]
  have hdet_small (t : ℝ) :
      (1 + Uᵀ * ((t⁻¹) • (U * C))).det =
        (1 + t⁻¹ * (n : ℝ) * a) ^ 2 - (t⁻¹ * (n : ℝ) * b) ^ 2 := by
    rw [Matrix.det_fin_two]
    simp [hUC_entries]
    ring_nf
  have hdet_rank (t : ℝ) (ht : t ≠ 0) :
      (t • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) + (U * C) * Uᵀ).det =
        t ^ (2 * n) *
          ((1 + t⁻¹ * (n : ℝ) * a) ^ 2 - (t⁻¹ * (n : ℝ) * b) ^ 2) := by
    have hfactor :
        (t • (1 + ((t⁻¹) • (U * C)) * Uᵀ) :
            Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) =
          t • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) + (U * C) * Uᵀ := by
      rw [smul_add]
      congr 1
      rw [← Matrix.smul_mul, smul_smul, mul_inv_cancel₀ ht, one_smul]
    rw [← hfactor, Matrix.det_smul]
    rw [Matrix.det_one_add_mul_comm ((t⁻¹) • (U * C)) Uᵀ]
    rw [hdet_small]
    simp [Fintype.card_prod, Nat.mul_comm]
  have hquot_rank (t : ℝ) (ht : t ≠ 0) :
      (t • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) + (U * C) * Uᵀ).det /
          t ^ (2 * n - 2) =
        (t + (n : ℝ) * a) ^ 2 - ((n : ℝ) * b) ^ 2 := by
    rw [hdet_rank t ht]
    have hpow : 2 * n = (2 * n - 2) + 2 := by omega
    rw [hpow, pow_add]
    field_simp [ht]
    have hE : 2 * n - 2 + 2 - 2 = 2 * n - 2 := by omega
    rw [hE]
    ring
  have hquot_Mn (x : ℝ) (hx : x ≠ a) :
      (Mn x).det / (x - a) ^ (2 * n - 2) =
        ((x - a) + (n : ℝ) * a) ^ 2 - ((n : ℝ) * b) ^ 2 := by
    have ht : x - a ≠ 0 := sub_ne_zero.mpr hx
    rw [← Matrix.det_submatrix_equiv_self e (Mn x), hmatrix x]
    exact hquot_rank (x - a) ht
  let G : ℝ → ℝ := fun x => ((x - a) + (n : ℝ) * a) ^ 2 - ((n : ℝ) * b) ^ 2
  have heq_event :
      (fun x : ℝ => (Mn x).det / (x - a) ^ (2 * n - 2)) =ᶠ[𝓝[≠] a] G := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hquot_Mn x hx
  have htarget :
      MvPolynomial.eval polyabn
          ((MvPolynomial.X 2) ^ 2 * ((MvPolynomial.X 0) ^ 2 - (MvPolynomial.X 1) ^ 2) :
            MvPolynomial (Fin 3) ℝ) =
        (n : ℝ) ^ 2 * (a ^ 2 - b ^ 2) := by
    rcases hpolyabn with ⟨h0, h1, h2⟩
    simp [h0, h1, h2]
  have hlimG : Tendsto G (𝓝[≠] a) (𝓝 (G a)) := by
    have hcont : ContinuousAt G a := by
      unfold G
      fun_prop
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hGa :
      G a =
        MvPolynomial.eval polyabn
          ((MvPolynomial.X 2) ^ 2 * ((MvPolynomial.X 0) ^ 2 - (MvPolynomial.X 1) ^ 2) :
            MvPolynomial (Fin 3) ℝ) := by
    unfold G
    rw [htarget]
    ring
  rw [hGa] at hlimG
  exact hlimG.congr' heq_event.symm
