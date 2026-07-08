import Mathlib

open  Real Equiv

noncomputable abbrev putnam_1986_a6_solution : (ℕ → ℕ) → ℕ → ℝ :=
  fun b n =>
    (∏ i ∈ Finset.range n, (b (i + 1) : ℝ)) /
      (∏ i ∈ Finset.range n, (((i + 1 : ℕ) : ℝ)))

noncomputable def putnamEulerLinear (c : ℝ) : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ where
  toFun p := Polynomial.X * Polynomial.derivative p - Polynomial.C c * p
  map_add' p q := by
    simp only [map_add, mul_add]
    abel
  map_smul' r p := by
    simp [Polynomial.smul_eq_C_mul]
    ring

noncomputable def putnamEulerListLinear : List ℝ → Polynomial ℝ →ₗ[ℝ] Polynomial ℝ
  | [] => LinearMap.id
  | c :: cs => (putnamEulerListLinear cs).comp (putnamEulerLinear c)

private lemma putnamEulerLinear_C_mul_X_pow (c A : ℝ) (m : ℕ) :
    putnamEulerLinear c (Polynomial.C A * Polynomial.X ^ m) =
      Polynomial.C (A * ((m : ℝ) - c)) * Polynomial.X ^ m := by
  change Polynomial.X * Polynomial.derivative (Polynomial.C A * Polynomial.X ^ m) -
      Polynomial.C c * (Polynomial.C A * Polynomial.X ^ m) = _
  rw [Polynomial.derivative_C_mul_X_pow]
  by_cases hm : m = 0
  · subst hm
    simp [mul_comm]
  · have hm' : m - 1 + 1 = m := Nat.sub_one_add_one hm
    rw [← mul_assoc, mul_comm Polynomial.X (Polynomial.C (A * (m : ℝ))), mul_assoc,
      mul_comm Polynomial.X (Polynomial.X ^ (m - 1)), ← pow_succ, hm']
    simp only [map_mul, map_sub]
    ring_nf

private lemma putnamEulerListLinear_C_mul_X_pow (cs : List ℝ) (A : ℝ) (m : ℕ) :
    putnamEulerListLinear cs (Polynomial.C A * Polynomial.X ^ m) =
      Polynomial.C (A * (cs.map fun c => (m : ℝ) - c).prod) * Polynomial.X ^ m := by
  induction cs generalizing A with
  | nil => simp [putnamEulerListLinear]
  | cons c cs ih =>
      change putnamEulerListLinear cs
        (putnamEulerLinear c (Polynomial.C A * Polynomial.X ^ m)) = _
      rw [putnamEulerLinear_C_mul_X_pow, ih]
      simp [mul_assoc]

private lemma putnamEulerLinear_one_sub_pow_succ (c : ℝ) (k : ℕ) (q : Polynomial ℝ) :
    let u : Polynomial ℝ := 1 - Polynomial.X
    let qnext : Polynomial ℝ :=
      - Polynomial.C ((k + 1 : ℕ) : ℝ) * Polynomial.X * q +
        u * (Polynomial.X * Polynomial.derivative q - Polynomial.C c * q)
    putnamEulerLinear c (u ^ (k + 1) * q) = u ^ k * qnext := by
  intro u qnext
  have hderu : Polynomial.derivative (u ^ (k + 1)) =
      - Polynomial.C (((k + 1 : ℕ) : ℝ)) * u ^ k := by
    dsimp [u]
    rw [Polynomial.derivative_pow, Nat.add_one_sub_one]
    simp
    ring
  change Polynomial.X * Polynomial.derivative (u ^ (k + 1) * q) -
      Polynomial.C c * (u ^ (k + 1) * q) = u ^ k * qnext
  rw [Polynomial.derivative_mul, hderu]
  dsimp [qnext]
  rw [pow_succ']
  ring

private lemma putnamEulerLinear_one_sub_pow_succ_eval_next
    (c : ℝ) (k : ℕ) (q : Polynomial ℝ) :
    let u : Polynomial ℝ := 1 - Polynomial.X
    let qnext : Polynomial ℝ :=
      - Polynomial.C ((k + 1 : ℕ) : ℝ) * Polynomial.X * q +
        u * (Polynomial.X * Polynomial.derivative q - Polynomial.C c * q)
    qnext.eval 1 = - ((k + 1 : ℕ) : ℝ) * q.eval 1 := by
  intro u qnext
  dsimp [qnext, u]
  simp

private lemma putnamEulerListLinear_one_sub_pow_length (cs : List ℝ) (q : Polynomial ℝ) :
    let u : Polynomial ℝ := 1 - Polynomial.X
    (putnamEulerListLinear cs (u ^ cs.length * q)).eval 1 =
      (-1 : ℝ) ^ cs.length * (cs.length.factorial : ℝ) * q.eval 1 := by
  induction cs generalizing q with
  | nil =>
      intro u
      simp [putnamEulerListLinear]
  | cons c cs ih =>
      intro u
      let qnext : Polynomial ℝ :=
        - Polynomial.C ((cs.length + 1 : ℕ) : ℝ) * Polynomial.X * q +
          u * (Polynomial.X * Polynomial.derivative q - Polynomial.C c * q)
      change (putnamEulerListLinear cs
        (putnamEulerLinear c (u ^ (cs.length + 1) * q))).eval 1 = _
      rw [putnamEulerLinear_one_sub_pow_succ (c := c) (k := cs.length) (q := q)]
      change (putnamEulerListLinear cs (u ^ cs.length * qnext)).eval 1 = _
      rw [ih qnext]
      rw [putnamEulerLinear_one_sub_pow_succ_eval_next (c := c) (k := cs.length) (q := q)]
      simp only [List.length_cons]
      rw [Nat.factorial_succ]
      norm_num [pow_succ]
      ring

/--
Let $a_1, a_2, \dots, a_n$ be real numbers, and let $b_1, b_2, \dots, b_n$ be distinct positive integers. Suppose that there is a polynomial $f(x)$ satisfying the identity
\[
(1-x)^n f(x) = 1 + \sum_{i=1}^n a_i x^{b_i}.
\]
Find a simple expression (not involving any sums) for $f(1)$ in terms of $b_1, b_2, \dots, b_n$ and $n$ (but independent of $a_1, a_2, \dots, a_n$).
-/
theorem putnam_1986_a6
(n : ℕ)
(npos : n > 0)
(a : ℕ → ℝ)
(b : ℕ → ℕ)
(bpos : ∀ i ∈ Finset.Icc 1 n, b i > 0)
(binj : ∀ i ∈ Finset.Icc 1 n, ∀ j ∈ Finset.Icc 1 n, b i = b j → i = j)
(f : Polynomial ℝ)
(hf : ∀ x : ℝ, (1 - x) ^ n * f.eval x = 1 + ∑ i : Finset.Icc 1 n, (a i) * x ^ (b i))
: (f.eval 1 = putnam_1986_a6_solution b n) :=
by
  classical
  have _hbpos := bpos
  have _hbinj := binj
  let s : Finset ℕ := Finset.Icc 1 n
  let cs : List ℝ := s.toList.map fun i => (b i : ℝ)
  let P : Polynomial ℝ :=
    1 + ∑ i : Finset.Icc 1 n, Polynomial.C (a i) * Polynomial.X ^ (b i)
  have hpoly : P = (1 - Polynomial.X) ^ n * f := by
    dsimp [P]
    apply Polynomial.funext
    intro x
    specialize hf x
    simpa only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_finset_sum,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] using hf.symm
  have hlen : cs.length = n := by
    dsimp [cs, s]
    rw [List.length_map, Finset.length_toList, Nat.card_Icc]
    omega
  have hcsprod : cs.prod = ∏ i ∈ s, (b i : ℝ) := by
    dsimp [cs]
    rw [Finset.prod_map_toList]
  have hconst :
      (putnamEulerListLinear cs (1 : Polynomial ℝ)).eval 1 =
        (-1 : ℝ) ^ n * (∏ i ∈ s, (b i : ℝ)) := by
    have hmono := putnamEulerListLinear_C_mul_X_pow cs 1 0
    have hneg : (cs.map fun c => (0 : ℝ) - c).prod = (-1 : ℝ) ^ cs.length * cs.prod := by
      simp
    calc
      (putnamEulerListLinear cs (1 : Polynomial ℝ)).eval 1
          = (putnamEulerListLinear cs (Polynomial.C 1 * Polynomial.X ^ 0)).eval 1 := by simp
      _ = (Polynomial.C (1 * (cs.map fun c => (0 : ℝ) - c).prod) *
            Polynomial.X ^ 0).eval 1 := by
          rw [hmono]
          simp only [Nat.cast_zero]
      _ = (-1 : ℝ) ^ n * (∏ i ∈ s, (b i : ℝ)) := by
          simp only [Polynomial.eval_C, pow_zero, mul_one, one_mul]
          rw [hneg, hlen, hcsprod]
  have hterms :
      (∑ i : Finset.Icc 1 n,
        (putnamEulerListLinear cs (Polynomial.C (a i) * Polynomial.X ^ (b i))).eval 1) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hmem : (b (i : ℕ) : ℝ) ∈ cs := by
      dsimp [cs, s]
      exact List.mem_map.mpr ⟨(i : ℕ), (Finset.mem_toList.mpr i.property), rfl⟩
    have hprod_zero : (cs.map fun c => ((b i : ℕ) : ℝ) - c).prod = 0 := by
      exact List.prod_eq_zero (List.mem_map.mpr ⟨(b (i : ℕ) : ℝ), hmem, by simp⟩)
    rw [putnamEulerListLinear_C_mul_X_pow]
    simp [hprod_zero]
  have hleft :
      (putnamEulerListLinear cs P).eval 1 = (-1 : ℝ) ^ n * (∏ i ∈ s, (b i : ℝ)) := by
    have hsum_eval :
        (putnamEulerListLinear cs (∑ i : Finset.Icc 1 n,
          Polynomial.C (a i) * Polynomial.X ^ (b i))).eval 1 = 0 := by
      rw [map_sum, Polynomial.eval_finset_sum]
      simpa using hterms
    dsimp [P]
    rw [map_add, Polynomial.eval_add, hconst]
    have hsum_eval_attach :
        (putnamEulerListLinear cs (∑ i ∈ (Finset.Icc 1 n).attach,
          Polynomial.C (a i) * Polynomial.X ^ (b i))).eval 1 = 0 := by
      simpa [Finset.univ_eq_attach] using hsum_eval
    rw [hsum_eval_attach, add_zero]
  have hright :
      (putnamEulerListLinear cs ((1 - Polynomial.X) ^ n * f)).eval 1 =
        (-1 : ℝ) ^ n * (n.factorial : ℝ) * f.eval 1 := by
    have h := putnamEulerListLinear_one_sub_pow_length cs f
    simpa [hlen] using h
  have hop := congrArg (fun p : Polynomial ℝ => (putnamEulerListLinear cs p).eval 1) hpoly
  have hmain : (-1 : ℝ) ^ n * (∏ i ∈ s, (b i : ℝ)) =
      (-1 : ℝ) ^ n * (n.factorial : ℝ) * f.eval 1 := by
    calc
      (-1 : ℝ) ^ n * (∏ i ∈ s, (b i : ℝ)) =
          (putnamEulerListLinear cs P).eval 1 := hleft.symm
      _ = (putnamEulerListLinear cs ((1 - Polynomial.X) ^ n * f)).eval 1 := hop
      _ = (-1 : ℝ) ^ n * (n.factorial : ℝ) * f.eval 1 := hright
  have hsign : (-1 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hmain' : (∏ i ∈ s, (b i : ℝ)) = (n.factorial : ℝ) * f.eval 1 := by
    apply mul_left_cancel₀ hsign
    simpa [mul_assoc] using hmain
  have hmain_Icc :
      (∏ i ∈ Finset.Icc 1 n, (b i : ℝ)) = (n.factorial : ℝ) * f.eval 1 := by
    simpa [s] using hmain'
  have hf_eq : f.eval 1 =
      (∏ i ∈ Finset.Icc 1 n, (b i : ℝ)) / (n.factorial : ℝ) := by
    rw [eq_div_iff hfac]
    rw [mul_comm]
    exact hmain_Icc.symm
  have hrange_quot_eq :
      ((∏ i ∈ Finset.range n, (b (i + 1) : ℝ)) /
          (∏ i ∈ Finset.range n, (((i + 1 : ℕ) : ℝ)))) =
        (∏ i ∈ Finset.Icc 1 n, (b i : ℝ)) / (n.factorial : ℝ) := by
    have hIcc :
        (Finset.range n).image (fun i : ℕ => i + 1) = Finset.Icc 1 n := by
      ext k
      simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨by omega, Nat.succ_le_iff.mpr hi⟩
      · intro hk
        refine ⟨k - 1, ?_, ?_⟩
        · omega
        · exact Nat.sub_add_cancel hk.1
    have hnum :
        (∏ i ∈ Finset.range n, (b (i + 1) : ℝ)) =
          ∏ i ∈ Finset.Icc 1 n, (b i : ℝ) := by
      rw [← hIcc, Finset.prod_image]
      intro x hx y hy hxy
      exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using hxy)
    have hden :
        (∏ i ∈ Finset.range n, (((i + 1 : ℕ) : ℝ))) =
          (n.factorial : ℝ) := by
      rw [← Nat.cast_prod]
      rw [Finset.prod_range_add_one_eq_factorial]
    rw [hnum, hden]
  rw [putnam_1986_a6_solution]
  exact hf_eq.trans hrange_quot_eq.symm
