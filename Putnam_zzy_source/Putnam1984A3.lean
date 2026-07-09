import Mathlib

open Topology Filter

noncomputable abbrev putnam_1984_a3_solution : MvPolynomial (Fin 3) ℝ :=
  (MvPolynomial.X 2) ^ 2 * ((MvPolynomial.X 0) ^ 2 - (MvPolynomial.X 1) ^ 2)

private def putnam_1984_a3_sgn {n : ℕ} (i : Fin (2 * n)) : ℝ :=
  (-1 : ℝ) ^ i.1

private lemma putnam_1984_a3_sum_sgn (n : ℕ) :
    (∑ i : Fin (2 * n), putnam_1984_a3_sgn i) = 0 := by
  unfold putnam_1984_a3_sgn
  rw [Fin.sum_neg_one_pow]
  simp

private lemma putnam_1984_a3_sum_sgn_sq (n : ℕ) :
    (∑ i : Fin (2 * n), putnam_1984_a3_sgn i * putnam_1984_a3_sgn i) =
      (2 * n : ℝ) := by
  unfold putnam_1984_a3_sgn
  simp_rw [← pow_add]
  have h_even : ∀ i : Fin (2 * n), Even (i.1 + i.1) := by
    intro i
    exact Even.add_self i.1
  simp [h_even]

private noncomputable def putnam_1984_a3_U
    (n : ℕ) (a b : ℝ) : Matrix (Fin (2 * n)) (Fin 2) ℝ :=
  fun i k =>
    if k = 0 then (a + b) / 2 else (a - b) / 2 * putnam_1984_a3_sgn i

private def putnam_1984_a3_V (n : ℕ) : Matrix (Fin 2) (Fin (2 * n)) ℝ :=
  fun k j => if k = 0 then 1 else putnam_1984_a3_sgn j

private lemma putnam_1984_a3_UV_apply
    (n : ℕ) (a b : ℝ) (i j : Fin (2 * n)) :
    (putnam_1984_a3_U n a b * putnam_1984_a3_V n) i j =
      (a + b) / 2 + (a - b) / 2 * ((-1 : ℝ) ^ (i.1 + j.1)) := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  simp [putnam_1984_a3_U, putnam_1984_a3_V, putnam_1984_a3_sgn, pow_add,
    mul_assoc, mul_left_comm, mul_comm]

private lemma putnam_1984_a3_entry_eq_rank_two
    (n : ℕ) (a b x : ℝ) (i j : Fin (2 * n)) :
    (if i = j then x else if Even (i.1 + j.1) then a else b) =
      ((x - a) • (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) +
        putnam_1984_a3_U n a b * putnam_1984_a3_V n) i j := by
  rw [Matrix.add_apply, putnam_1984_a3_UV_apply]
  by_cases hij : i = j
  · subst j
    simp [Even.add_self]
    ring
  · simp [hij]
    by_cases hEven : Even (i.1 + j.1)
    · simp [hEven, hEven.neg_one_pow]
      ring
    · have hOdd : Odd (i.1 + j.1) := Nat.not_even_iff_odd.mp hEven
      simp [hEven, hOdd.neg_one_pow]
      ring

private lemma putnam_1984_a3_matrix_eq_rank_two (n : ℕ) (a b x : ℝ) :
    (fun i j : Fin (2 * n) =>
      if i = j then x else if Even (i.1 + j.1) then a else b) =
      (x - a) • (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) +
        putnam_1984_a3_U n a b * putnam_1984_a3_V n := by
  ext i j
  exact putnam_1984_a3_entry_eq_rank_two n a b x i j

private lemma putnam_1984_a3_scaled_VU (n : ℕ) (a b l : ℝ) :
    putnam_1984_a3_V n * (l⁻¹ • putnam_1984_a3_U n a b) =
      !![ (2 * n : ℝ) * (l⁻¹ * ((a + b) / 2)), 0;
          0, (2 * n : ℝ) * (l⁻¹ * ((a - b) / 2)) ] := by
  ext r c
  fin_cases r <;> fin_cases c
  · simp [Matrix.mul_apply, putnam_1984_a3_U, putnam_1984_a3_V]
  · simp [Matrix.mul_apply, putnam_1984_a3_U, putnam_1984_a3_V]
    calc
      (∑ x : Fin (2 * n), l⁻¹ * ((a - b) / 2 * putnam_1984_a3_sgn x))
          = (l⁻¹ * ((a - b) / 2)) *
              (∑ x : Fin (2 * n), putnam_1984_a3_sgn x) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ = 0 := by rw [putnam_1984_a3_sum_sgn]; ring
  · simp [Matrix.mul_apply, putnam_1984_a3_U, putnam_1984_a3_V]
    rw [← Finset.sum_mul, putnam_1984_a3_sum_sgn, zero_mul]
  · simp [Matrix.mul_apply, putnam_1984_a3_U, putnam_1984_a3_V]
    calc
      (∑ x : Fin (2 * n), putnam_1984_a3_sgn x *
          (l⁻¹ * ((a - b) / 2 * putnam_1984_a3_sgn x)))
          = (∑ x : Fin (2 * n), putnam_1984_a3_sgn x * putnam_1984_a3_sgn x) *
              (l⁻¹ * ((a - b) / 2)) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ = (2 * n : ℝ) * (l⁻¹ * ((a - b) / 2)) := by
            rw [putnam_1984_a3_sum_sgn_sq]

private lemma putnam_1984_a3_det_one_add_scaled_VU (n : ℕ) (a b l : ℝ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) +
        putnam_1984_a3_V n * (l⁻¹ • putnam_1984_a3_U n a b)).det =
      (1 + (2 * n : ℝ) * (l⁻¹ * ((a + b) / 2))) *
        (1 + (2 * n : ℝ) * (l⁻¹ * ((a - b) / 2))) := by
  rw [putnam_1984_a3_scaled_VU]
  let A : ℝ := (2 * n : ℝ) * (l⁻¹ * ((a + b) / 2))
  let B : ℝ := (2 * n : ℝ) * (l⁻¹ * ((a - b) / 2))
  have hmat :
      (1 : Matrix (Fin 2) (Fin 2) ℝ) + !![A, 0; 0, B] =
        !![1 + A, 0; 0, 1 + B] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  change ((1 : Matrix (Fin 2) (Fin 2) ℝ) + !![A, 0; 0, B]).det =
    (1 + A) * (1 + B)
  rw [hmat, Matrix.det_fin_two_of]
  ring

private lemma putnam_1984_a3_scale_identity
    (n : ℕ) (a b l : ℝ) (hl : l ≠ 0) :
    l • ((1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) +
        (l⁻¹ • putnam_1984_a3_U n a b) * putnam_1984_a3_V n) =
      l • (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) +
        putnam_1984_a3_U n a b * putnam_1984_a3_V n := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, smul_eq_mul]
  rw [mul_add, Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · ring
  · apply Finset.sum_congr rfl
    intro k hk
    field_simp [hl]

private lemma putnam_1984_a3_det_rank_two_quotient
    (n : ℕ) (a b x : ℝ) (npos : n > 0) (hx : x ≠ a) :
    (( (x - a) • (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) +
          putnam_1984_a3_U n a b * putnam_1984_a3_V n).det) /
        (x - a) ^ (2 * n - 2)
      = ((x - a) + (n : ℝ) * (a + b)) *
          ((x - a) + (n : ℝ) * (a - b)) := by
  let l : ℝ := x - a
  have hl : l ≠ 0 := by
    dsimp [l]
    exact sub_ne_zero.mpr hx
  have hdet :
      (l • (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) +
          putnam_1984_a3_U n a b * putnam_1984_a3_V n).det =
        l ^ (2 * n) *
          ((1 + (2 * n : ℝ) * (l⁻¹ * ((a + b) / 2))) *
            (1 + (2 * n : ℝ) * (l⁻¹ * ((a - b) / 2)))) := by
    rw [← putnam_1984_a3_scale_identity n a b l hl]
    rw [Matrix.det_smul, Fintype.card_fin, Matrix.det_one_add_mul_comm]
    rw [putnam_1984_a3_det_one_add_scaled_VU]
  change
    (l • (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) +
        putnam_1984_a3_U n a b * putnam_1984_a3_V n).det /
      l ^ (2 * n - 2) =
        (l + (n : ℝ) * (a + b)) * (l + (n : ℝ) * (a - b))
  rw [hdet]
  have hpow : l ^ (2 * n) = l ^ (2 * n - 2) * l ^ 2 := by
    have hle : 2 ≤ 2 * n := by omega
    nth_rewrite 1 [← Nat.sub_add_cancel hle]
    rw [pow_add]
  rw [hpow]
  field_simp [hl]

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
: Tendsto (fun x : ℝ => (Mn x).det / (x - a) ^ (2 * n - 2)) (𝓝[≠] a) (𝓝 (MvPolynomial.eval polyabn putnam_1984_a3_solution)) :=
by
  have _ : a ≠ b := aneb
  have hsol :
      MvPolynomial.eval polyabn putnam_1984_a3_solution =
        (n : ℝ) ^ 2 * (a ^ 2 - b ^ 2) := by
    rcases hpolyabn with ⟨h0, h1, h2⟩
    simp [putnam_1984_a3_solution, h0, h1, h2]
  let g : ℝ → ℝ :=
    fun x => ((x - a) + (n : ℝ) * (a + b)) *
      ((x - a) + (n : ℝ) * (a - b))
  have htarget : g a = MvPolynomial.eval polyabn putnam_1984_a3_solution := by
    rw [hsol]
    dsimp [g]
    ring
  have hg_cont : ContinuousAt g a := by
    dsimp [g]
    fun_prop
  have hg_tend : Tendsto g (𝓝[≠] a)
      (𝓝 (MvPolynomial.eval polyabn putnam_1984_a3_solution)) := by
    simpa [htarget] using hg_cont.tendsto.mono_left nhdsWithin_le_nhds
  have heq :
      (fun x : ℝ => (Mn x).det / (x - a) ^ (2 * n - 2)) =ᶠ[𝓝[≠] a] g := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxne : x ≠ a := by
      simpa using hx
    rw [hMn]
    change Matrix.det (fun i j : Fin (2 * n) =>
        if i = j then x else if Even (i.1 + j.1) then a else b) /
        (x - a) ^ (2 * n - 2) = g x
    rw [putnam_1984_a3_matrix_eq_rank_two n a b x]
    exact putnam_1984_a3_det_rank_two_quotient n a b x npos hxne
  exact hg_tend.congr' heq.symm
