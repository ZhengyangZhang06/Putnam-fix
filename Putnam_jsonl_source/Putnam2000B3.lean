import Mathlib

open Topology Filter Nat Set Function

private lemma putnam_2000_b3_mult_eq_of_first_nonzero
    (mult : (ℝ → ℝ) → ℝ → ℕ)
    (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ,
      (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
        (iteratedDeriv (mult g t) g t ≠ 0 ∧
          ∀ k < (mult g t), iteratedDeriv k g t = 0))
    {g : ℝ → ℝ} {t : ℝ} {n : ℕ}
    (hnz : iteratedDeriv n g t ≠ 0)
    (hz : ∀ k < n, iteratedDeriv k g t = 0) :
    mult g t = n := by
  have h := hmult g t ⟨n, hnz⟩
  apply le_antisymm
  · by_contra hle
    exact hnz (h.2 n (Nat.lt_of_not_ge hle))
  · by_contra hle
    exact h.1 (hz (mult g t) (Nat.lt_of_not_ge hle))

private lemma putnam_2000_b3_mult_eq_zero_of_value_ne_zero
    (mult : (ℝ → ℝ) → ℝ → ℕ)
    (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ,
      (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
        (iteratedDeriv (mult g t) g t ≠ 0 ∧
          ∀ k < (mult g t), iteratedDeriv k g t = 0))
    {g : ℝ → ℝ} {t : ℝ} (hg : g t ≠ 0) :
    mult g t = 0 := by
  exact putnam_2000_b3_mult_eq_of_first_nonzero mult hmult (n := 0)
    (by simpa using hg) (by simp)

private lemma putnam_2000_b3_iteratedDeriv_deriv
    (g : ℝ → ℝ) (n : ℕ) :
    iteratedDeriv n (deriv g) = iteratedDeriv (n + 1) g := by
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate]
  exact (Function.iterate_succ_apply deriv n g).symm

private lemma putnam_2000_b3_iteratedDeriv_iteratedDeriv
    (g : ℝ → ℝ) (m n : ℕ) :
    iteratedDeriv m (iteratedDeriv n g) = iteratedDeriv (m + n) g := by
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
    iteratedDeriv_eq_iterate]
  rw [← Function.iterate_add_apply]

private lemma putnam_2000_b3_mult_deriv_eq_pred
    (mult : (ℝ → ℝ) → ℝ → ℕ)
    (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ,
      (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
        (iteratedDeriv (mult g t) g t ≠ 0 ∧
          ∀ k < (mult g t), iteratedDeriv k g t = 0))
    {g : ℝ → ℝ} {t : ℝ} {n : ℕ}
    (hg : mult g t = n + 1)
    (hex : ∃ c : ℕ, iteratedDeriv c g t ≠ 0) :
    mult (deriv g) t = n := by
  have h := hmult g t hex
  have hnz : iteratedDeriv n (deriv g) t ≠ 0 := by
    rw [putnam_2000_b3_iteratedDeriv_deriv]
    simpa [hg] using h.1
  have hz : ∀ k < n, iteratedDeriv k (deriv g) t = 0 := by
    intro k hk
    rw [putnam_2000_b3_iteratedDeriv_deriv]
    exact h.2 (k + 1) (by omega)
  exact putnam_2000_b3_mult_eq_of_first_nonzero mult hmult hnz hz

private lemma putnam_2000_b3_mult_iteratedDeriv_succ_eq_pred
    (mult : (ℝ → ℝ) → ℝ → ℕ)
    (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ,
      (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
        (iteratedDeriv (mult g t) g t ≠ 0 ∧
          ∀ k < (mult g t), iteratedDeriv k g t = 0))
    {f : ℝ → ℝ} {t : ℝ} {k n : ℕ}
    (hf : mult (iteratedDeriv k f) t = n + 1)
    (hex : ∃ c : ℕ, iteratedDeriv c (iteratedDeriv k f) t ≠ 0) :
    mult (iteratedDeriv (k + 1) f) t = n := by
  rw [iteratedDeriv_succ]
  exact putnam_2000_b3_mult_deriv_eq_pred mult hmult hf hex

private lemma putnam_2000_b3_periodic
    (N : ℕ) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
    (hf : ∀ t, f t = ∑ j : Icc 1 N,
      a j * Real.sin (2 * Real.pi * j * t)) :
    Function.Periodic f 1 := by
  intro t
  rw [hf (t + 1), hf t]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  have harg :
      2 * Real.pi * (j : ℝ) * (t + 1) =
        (2 * Real.pi * (j : ℝ) * t) + (j : ℤ) * (2 * Real.pi) := by
    norm_num [mul_add, Nat.cast_add, Int.cast_natCast]
    ring
  rw [harg]
  exact Real.sin_add_int_mul_two_pi _ _

private lemma putnam_2000_b3_periodic_deriv
    {g : ℝ → ℝ} {p : ℝ} (hg : Function.Periodic g p) :
    Function.Periodic (deriv g) p := by
  intro x
  have hshift : deriv (fun z => g (z + p)) x = deriv g (x + p) := by
    simpa using deriv_comp_add_const g p x
  have heq : (fun z => g (z + p)) = g := funext hg
  rw [← hshift, heq]

private lemma putnam_2000_b3_periodic_iteratedDeriv
    {g : ℝ → ℝ} {p : ℝ} (hg : Function.Periodic g p) (n : ℕ) :
    Function.Periodic (iteratedDeriv n g) p := by
  induction n with
  | zero =>
      simpa [iteratedDeriv_zero] using hg
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact putnam_2000_b3_periodic_deriv ih

private lemma putnam_2000_b3_contDiff
    (N : ℕ) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
    (hf : ∀ t, f t = ∑ j : Icc 1 N,
      a j * Real.sin (2 * Real.pi * j * t))
    (n : WithTop ℕ∞) :
    ContDiff ℝ n f := by
  rw [show f = fun t => ∑ j : Icc 1 N,
    a j * Real.sin (2 * Real.pi * j * t) from funext hf]
  fun_prop

private lemma putnam_2000_b3_contDiff_iteratedDeriv
    (N : ℕ) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
    (hf : ∀ t, f t = ∑ j : Icc 1 N,
      a j * Real.sin (2 * Real.pi * j * t))
    (k : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (iteratedDeriv k f) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv k
    (putnam_2000_b3_contDiff N a f hf ((⊤ : ℕ∞) : WithTop ℕ∞))

private lemma putnam_2000_b3_differentiable_iteratedDeriv
    (N : ℕ) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
    (hf : ∀ t, f t = ∑ j : Icc 1 N,
      a j * Real.sin (2 * Real.pi * j * t))
    (k : ℕ) :
    Differentiable ℝ (iteratedDeriv k f) := by
  exact (putnam_2000_b3_contDiff_iteratedDeriv N a f hf k).differentiable
    (by simp)

private lemma putnam_2000_b3_continuous_iteratedDeriv
    (N : ℕ) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
    (hf : ∀ t, f t = ∑ j : Icc 1 N,
      a j * Real.sin (2 * Real.pi * j * t))
    (k : ℕ) :
    Continuous (iteratedDeriv k f) := by
  exact (putnam_2000_b3_contDiff_iteratedDeriv N a f hf k).continuous

private lemma putnam_2000_b3_iteratedDeriv_finset_sum
    {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℝ) (n : ℕ) (x : ℝ)
    (hF : ∀ i ∈ s, ContDiffAt ℝ (↑n) (F i) x) :
    iteratedDeriv n (fun y : ℝ => ∑ i ∈ s, F i y) x =
      ∑ i ∈ s, iteratedDeriv n (F i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using
        (iteratedDeriv_const (𝕜 := ℝ) (F := ℝ) (n := n) (c := 0) (x := x))
  | insert a s has ih =>
      have ha : ContDiffAt ℝ (↑n) (F a) x := hF a (by simp [has])
      have hs : ContDiffAt ℝ (↑n) (fun y : ℝ => ∑ i ∈ s, F i y) x := by
        apply ContDiffAt.sum
        intro i hi
        exact hF i (by simp [hi])
      have hfun : (fun y : ℝ => ∑ i ∈ insert a s, F i y) =
          F a + fun y : ℝ => ∑ i ∈ s, F i y := by
        ext y
        simp [Finset.sum_insert has]
      rw [hfun]
      rw [iteratedDeriv_add ha hs]
      rw [ih]
      · simp [has]
      · intro i hi
        exact hF i (by simp [hi])

private lemma putnam_2000_b3_iteratedDeriv_sin_const_mul
    (A c : ℝ) (k : ℕ) :
    iteratedDeriv k (fun t : ℝ => A * Real.sin (c * t)) =
      fun t => A * c ^ k * iteratedDeriv k Real.sin (c * t) := by
  ext t
  have hct : ContDiffAt ℝ (↑k) (fun z : ℝ => Real.sin (c * z)) t := by
    fun_prop
  rw [iteratedDeriv_const_mul (h := hct)]
  rw [iteratedDeriv_comp_const_mul (h := Real.contDiff_sin) c]
  ring

private lemma putnam_2000_b3_iteratedDeriv_sum
    (N : ℕ) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
    (hf : ∀ t, f t = ∑ j : Icc 1 N,
      a j * Real.sin (2 * Real.pi * j * t))
    (k : ℕ) (t : ℝ) :
    iteratedDeriv k f t = ∑ j : Icc 1 N,
      a j * (2 * Real.pi * j) ^ k *
        iteratedDeriv k Real.sin ((2 * Real.pi * j) * t) := by
  rw [show f = fun t => ∑ j : Icc 1 N,
    a j * Real.sin (2 * Real.pi * j * t) from funext hf]
  rw [putnam_2000_b3_iteratedDeriv_finset_sum Finset.univ]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [putnam_2000_b3_iteratedDeriv_sin_const_mul]
  · intro j hj
    fun_prop

private lemma putnam_2000_b3_iteratedDeriv_even_sum
    (N : ℕ) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
    (hf : ∀ t, f t = ∑ j : Icc 1 N,
      a j * Real.sin (2 * Real.pi * j * t))
    (r : ℕ) (t : ℝ) :
    iteratedDeriv (2 * r) f t = ∑ j : Icc 1 N,
      a j * (2 * Real.pi * j) ^ (2 * r) *
        ((-1 : ℝ) ^ r * Real.sin ((2 * Real.pi * j) * t)) := by
  rw [putnam_2000_b3_iteratedDeriv_sum N a f hf]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Real.iteratedDeriv_even_sin]
  simp

private lemma putnam_2000_b3_iteratedDeriv_odd_sum
    (N : ℕ) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
    (hf : ∀ t, f t = ∑ j : Icc 1 N,
      a j * Real.sin (2 * Real.pi * j * t))
    (r : ℕ) (t : ℝ) :
    iteratedDeriv (2 * r + 1) f t = ∑ j : Icc 1 N,
      a j * (2 * Real.pi * j) ^ (2 * r + 1) *
        ((-1 : ℝ) ^ r * Real.cos ((2 * Real.pi * j) * t)) := by
  rw [putnam_2000_b3_iteratedDeriv_sum N a f hf]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Real.iteratedDeriv_odd_sin]
  simp

private lemma putnam_2000_b3_chebyshev_U_sin
    {N : ℕ} (j : Icc 1 N) (t : ℝ) :
    (Polynomial.Chebyshev.U ℝ ((j : ℤ) - 1)).eval
        (Real.cos (2 * Real.pi * t)) *
      Real.sin (2 * Real.pi * t) =
        Real.sin (2 * Real.pi * j * t) := by
  calc
    (Polynomial.Chebyshev.U ℝ ((j : ℤ) - 1)).eval
        (Real.cos (2 * Real.pi * t)) *
      Real.sin (2 * Real.pi * t) =
        Real.sin ((j : ℤ) * (2 * Real.pi * t)) := by
          simpa using
            (Polynomial.Chebyshev.U_real_cos (2 * Real.pi * t) ((j : ℤ) - 1))
    _ = Real.sin (2 * Real.pi * j * t) := by
      have hcast : (((j : ℤ) : ℝ) = (j : ℝ)) := by norm_num
      rw [hcast]
      congr 1
      ring

private lemma putnam_2000_b3_chebyshev_T_cos
    {N : ℕ} (j : Icc 1 N) (t : ℝ) :
    (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval
        (Real.cos (2 * Real.pi * t)) =
      Real.cos (2 * Real.pi * j * t) := by
  calc
    (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval
        (Real.cos (2 * Real.pi * t)) =
      Real.cos ((j : ℤ) * (2 * Real.pi * t)) := by
        simpa using Polynomial.Chebyshev.T_real_cos (2 * Real.pi * t) (j : ℤ)
    _ = Real.cos (2 * Real.pi * j * t) := by
      have hcast : (((j : ℤ) : ℝ) = (j : ℝ)) := by norm_num
      rw [hcast]
      congr 1
      ring

private def putnam_2000_b3_top (N : ℕ) (hN : N > 0) : Icc 1 N :=
  ⟨N, by exact ⟨Nat.succ_le_iff.mpr hN, le_rfl⟩⟩

private noncomputable def putnam_2000_b3_evenPoly
    (N : ℕ) (a : Icc 1 N → ℝ) (r : ℕ) : Polynomial ℝ :=
  ∑ j : Icc 1 N,
    Polynomial.C (a j * (2 * Real.pi * (j : ℝ)) ^ (2 * r) *
      ((-1 : ℝ) ^ r)) *
      Polynomial.Chebyshev.U ℝ ((j : ℤ) - 1)

private noncomputable def putnam_2000_b3_oddPoly
    (N : ℕ) (a : Icc 1 N → ℝ) (r : ℕ) : Polynomial ℝ :=
  ∑ j : Icc 1 N,
    Polynomial.C (a j * (2 * Real.pi * (j : ℝ)) ^ (2 * r + 1) *
      ((-1 : ℝ) ^ r)) *
      Polynomial.Chebyshev.T ℝ (j : ℤ)

private lemma putnam_2000_b3_evenPoly_eval
    (N : ℕ) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
    (hf : ∀ t, f t = ∑ j : Icc 1 N,
      a j * Real.sin (2 * Real.pi * j * t))
    (r : ℕ) (t : ℝ) :
    Real.sin (2 * Real.pi * t) *
        (putnam_2000_b3_evenPoly N a r).eval
          (Real.cos (2 * Real.pi * t)) =
      iteratedDeriv (2 * r) f t := by
  rw [putnam_2000_b3_iteratedDeriv_even_sum N a f hf r t]
  simp only [putnam_2000_b3_evenPoly, Polynomial.eval_finset_sum,
    Polynomial.eval_mul, Polynomial.eval_C]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hU := putnam_2000_b3_chebyshev_U_sin j t
  calc
    Real.sin (2 * Real.pi * t) *
        (a j * (2 * Real.pi * (j : ℝ)) ^ (2 * r) * (-1) ^ r *
          (Polynomial.Chebyshev.U ℝ ((j : ℤ) - 1)).eval
            (Real.cos (2 * Real.pi * t))) =
        (a j * (2 * Real.pi * (j : ℝ)) ^ (2 * r) * (-1) ^ r) *
          ((Polynomial.Chebyshev.U ℝ ((j : ℤ) - 1)).eval
            (Real.cos (2 * Real.pi * t)) *
              Real.sin (2 * Real.pi * t)) := by ring
    _ = a j * (2 * Real.pi * (j : ℝ)) ^ (2 * r) *
          ((-1 : ℝ) ^ r * Real.sin (2 * Real.pi * (j : ℝ) * t)) := by
        rw [hU]
        ring

private lemma putnam_2000_b3_oddPoly_eval
    (N : ℕ) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
    (hf : ∀ t, f t = ∑ j : Icc 1 N,
      a j * Real.sin (2 * Real.pi * j * t))
    (r : ℕ) (t : ℝ) :
    (putnam_2000_b3_oddPoly N a r).eval
        (Real.cos (2 * Real.pi * t)) =
      iteratedDeriv (2 * r + 1) f t := by
  rw [putnam_2000_b3_iteratedDeriv_odd_sum N a f hf r t]
  simp only [putnam_2000_b3_oddPoly, Polynomial.eval_finset_sum,
    Polynomial.eval_mul, Polynomial.eval_C]
  apply Finset.sum_congr rfl
  intro j hj
  rw [putnam_2000_b3_chebyshev_T_cos j t]
  ring

private lemma putnam_2000_b3_oddPoly_coeff_top_ne_zero
    (N : ℕ) (hN : N > 0) (a : Icc 1 N → ℝ) (r : ℕ)
    (haN : a (putnam_2000_b3_top N hN) ≠ 0) :
    (putnam_2000_b3_oddPoly N a r).coeff N ≠ 0 := by
  classical
  let top : Icc 1 N := putnam_2000_b3_top N hN
  have htop_coeff :
      (Polynomial.C
          (a top * (2 * Real.pi * (top : ℝ)) ^ (2 * r + 1) *
            ((-1 : ℝ) ^ r)) *
        Polynomial.Chebyshev.T ℝ (top : ℤ)).coeff N ≠ 0 := by
    rw [Polynomial.coeff_C_mul]
    have hdeg :
        (Polynomial.Chebyshev.T ℝ (top : ℤ)).natDegree = N := by
      change (Polynomial.Chebyshev.T ℝ (N : ℤ)).natDegree = N
      simp [Polynomial.Chebyshev.natDegree_T]
    have hcoeff :
        (Polynomial.Chebyshev.T ℝ (top : ℤ)).coeff N =
          (Polynomial.Chebyshev.T ℝ (top : ℤ)).leadingCoeff := by
      simpa [hdeg] using
        (Polynomial.coeff_natDegree (p := Polynomial.Chebyshev.T ℝ (top : ℤ)))
    rw [hcoeff]
    rw [Polynomial.Chebyshev.leadingCoeff_T]
    have hpow : (2 * Real.pi * (top : ℝ)) ^ (2 * r + 1) ≠ 0 := by
      apply pow_ne_zero
      positivity
    have hsign : ((-1 : ℝ) ^ r) ≠ 0 := by
      exact pow_ne_zero _ (by norm_num)
    have hlead : (2 : ℝ) ^ ((top : ℤ).natAbs - 1) ≠ 0 := by
      exact pow_ne_zero _ (by norm_num)
    have hatop : a top ≠ 0 := by
      simpa [top] using haN
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hatop hpow) hsign) hlead
  rw [putnam_2000_b3_oddPoly]
  have hsum :
      (∑ j : Icc 1 N,
        Polynomial.C
          (a j * (2 * Real.pi * (j : ℝ)) ^ (2 * r + 1) *
            ((-1 : ℝ) ^ r)) *
          Polynomial.Chebyshev.T ℝ (j : ℤ)).coeff N =
        ∑ j : Icc 1 N,
          (Polynomial.C
            (a j * (2 * Real.pi * (j : ℝ)) ^ (2 * r + 1) *
              ((-1 : ℝ) ^ r)) *
            Polynomial.Chebyshev.T ℝ (j : ℤ)).coeff N := by
    simp
  rw [hsum]
  change (∑ j : Icc 1 N,
      (Polynomial.C
        (a j * (2 * Real.pi * (j : ℝ)) ^ (2 * r + 1) *
          ((-1 : ℝ) ^ r)) *
        Polynomial.Chebyshev.T ℝ (j : ℤ)).coeff N) ≠ 0
  have hsingle :
      (∑ j : Icc 1 N,
        (Polynomial.C
          (a j * (2 * Real.pi * (j : ℝ)) ^ (2 * r + 1) *
            ((-1 : ℝ) ^ r)) *
          Polynomial.Chebyshev.T ℝ (j : ℤ)).coeff N) =
        (Polynomial.C
          (a top * (2 * Real.pi * (top : ℝ)) ^ (2 * r + 1) *
            ((-1 : ℝ) ^ r)) *
          Polynomial.Chebyshev.T ℝ (top : ℤ)).coeff N := by
    refine Finset.sum_eq_single top ?_ ?_
    · intro j hj hne
      rw [Polynomial.coeff_C_mul]
      have hjlt : (j : ℕ) < N := by
        have hjle : (j : ℕ) ≤ N := j.2.2
        have hjne : (j : ℕ) ≠ N := by
          intro h
          exact hne (Subtype.ext h)
        omega
      have hdeg :
          (Polynomial.Chebyshev.T ℝ (j : ℤ)).natDegree < N := by
        rw [Polynomial.Chebyshev.natDegree_T]
        norm_num
        exact hjlt
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdeg, mul_zero]
    · intro hnot
      exact (hnot (Finset.mem_univ top)).elim
  rw [hsingle]
  exact htop_coeff

private lemma putnam_2000_b3_oddPoly_natDegree_le
    (N : ℕ) (a : Icc 1 N → ℝ) (r : ℕ) :
    (putnam_2000_b3_oddPoly N a r).natDegree ≤ N := by
  classical
  rw [putnam_2000_b3_oddPoly]
  refine Polynomial.natDegree_sum_le_of_forall_le (s := Finset.univ)
    (f := fun j : Icc 1 N =>
      Polynomial.C
        (a j * (2 * Real.pi * (j : ℝ)) ^ (2 * r + 1) *
          ((-1 : ℝ) ^ r)) *
        Polynomial.Chebyshev.T ℝ (j : ℤ)) ?_
  intro j hj
  calc
    (Polynomial.C
        (a j * (2 * Real.pi * (j : ℝ)) ^ (2 * r + 1) *
          ((-1 : ℝ) ^ r)) *
        Polynomial.Chebyshev.T ℝ (j : ℤ)).natDegree
        ≤ (Polynomial.Chebyshev.T ℝ (j : ℤ)).natDegree :=
          Polynomial.natDegree_C_mul_le _ _
    _ = (j : ℤ).natAbs := by
          rw [Polynomial.Chebyshev.natDegree_T]
    _ = (j : ℕ) := by simp
    _ ≤ N := j.2.2

private lemma putnam_2000_b3_evenPoly_coeff_top_ne_zero
    (N : ℕ) (hN : N > 0) (a : Icc 1 N → ℝ) (r : ℕ)
    (haN : a (putnam_2000_b3_top N hN) ≠ 0) :
    (putnam_2000_b3_evenPoly N a r).coeff (N - 1) ≠ 0 := by
  classical
  let top : Icc 1 N := putnam_2000_b3_top N hN
  have htop_index :
      ((top : ℤ) - 1) = (((N - 1 : ℕ) : ℤ)) := by
    change ((N : ℤ) - 1) = (((N - 1 : ℕ) : ℤ))
    omega
  have htop_coeff :
      (Polynomial.C
          (a top * (2 * Real.pi * (top : ℝ)) ^ (2 * r) *
            ((-1 : ℝ) ^ r)) *
        Polynomial.Chebyshev.U ℝ ((top : ℤ) - 1)).coeff (N - 1) ≠ 0 := by
    rw [Polynomial.coeff_C_mul]
    rw [htop_index]
    have hdeg :
        (Polynomial.Chebyshev.U ℝ (((N - 1 : ℕ) : ℤ))).natDegree = N - 1 := by
      simpa using Polynomial.Chebyshev.natDegree_U_natCast (R := ℝ) (N - 1)
    have hcoeff :
        (Polynomial.Chebyshev.U ℝ (((N - 1 : ℕ) : ℤ))).coeff (N - 1) =
          (Polynomial.Chebyshev.U ℝ (((N - 1 : ℕ) : ℤ))).leadingCoeff := by
      simpa [hdeg] using
        (Polynomial.coeff_natDegree
          (p := Polynomial.Chebyshev.U ℝ (((N - 1 : ℕ) : ℤ))))
    rw [hcoeff, Polynomial.Chebyshev.leadingCoeff_U_natCast]
    have hpow : (2 * Real.pi * (top : ℝ)) ^ (2 * r) ≠ 0 := by
      apply pow_ne_zero
      positivity
    have hsign : ((-1 : ℝ) ^ r) ≠ 0 := by
      exact pow_ne_zero _ (by norm_num)
    have hlead : (2 : ℝ) ^ (N - 1) ≠ 0 := by
      exact pow_ne_zero _ (by norm_num)
    have hatop : a top ≠ 0 := by
      simpa [top] using haN
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hatop hpow) hsign) hlead
  rw [putnam_2000_b3_evenPoly]
  have hsum :
      (∑ j : Icc 1 N,
        Polynomial.C
          (a j * (2 * Real.pi * (j : ℝ)) ^ (2 * r) *
            ((-1 : ℝ) ^ r)) *
          Polynomial.Chebyshev.U ℝ ((j : ℤ) - 1)).coeff (N - 1) =
        ∑ j : Icc 1 N,
          (Polynomial.C
            (a j * (2 * Real.pi * (j : ℝ)) ^ (2 * r) *
              ((-1 : ℝ) ^ r)) *
            Polynomial.Chebyshev.U ℝ ((j : ℤ) - 1)).coeff (N - 1) := by
    simp
  rw [hsum]
  change (∑ j : Icc 1 N,
      (Polynomial.C
        (a j * (2 * Real.pi * (j : ℝ)) ^ (2 * r) *
          ((-1 : ℝ) ^ r)) *
        Polynomial.Chebyshev.U ℝ ((j : ℤ) - 1)).coeff (N - 1)) ≠ 0
  have hsingle :
      (∑ j : Icc 1 N,
        (Polynomial.C
          (a j * (2 * Real.pi * (j : ℝ)) ^ (2 * r) *
            ((-1 : ℝ) ^ r)) *
          Polynomial.Chebyshev.U ℝ ((j : ℤ) - 1)).coeff (N - 1)) =
        (Polynomial.C
          (a top * (2 * Real.pi * (top : ℝ)) ^ (2 * r) *
            ((-1 : ℝ) ^ r)) *
          Polynomial.Chebyshev.U ℝ ((top : ℤ) - 1)).coeff (N - 1) := by
    refine Finset.sum_eq_single top ?_ ?_
    · intro j hj hne
      rw [Polynomial.coeff_C_mul]
      have hjlt : (j : ℕ) < N := by
        have hjle : (j : ℕ) ≤ N := j.2.2
        have hjne : (j : ℕ) ≠ N := by
          intro h
          exact hne (Subtype.ext h)
        omega
      have hj_index :
          ((j : ℤ) - 1) = ((((j : ℕ) - 1 : ℕ) : ℤ)) := by
        have hjpos : 1 ≤ (j : ℕ) := j.2.1
        norm_num
        omega
      rw [hj_index]
      have hdeg :
          (Polynomial.Chebyshev.U ℝ ((((j : ℕ) - 1 : ℕ) : ℤ))).natDegree < N - 1 := by
        rw [Polynomial.Chebyshev.natDegree_U_natCast]
        have hjpos : 1 ≤ (j : ℕ) := j.2.1
        omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdeg, mul_zero]
    · intro hnot
      exact (hnot (Finset.mem_univ top)).elim
  rw [hsingle]
  exact htop_coeff

private lemma putnam_2000_b3_evenPoly_natDegree_le
    (N : ℕ) (a : Icc 1 N → ℝ) (r : ℕ) :
    (putnam_2000_b3_evenPoly N a r).natDegree ≤ N - 1 := by
  classical
  rw [putnam_2000_b3_evenPoly]
  refine Polynomial.natDegree_sum_le_of_forall_le (s := Finset.univ)
    (f := fun j : Icc 1 N =>
      Polynomial.C
        (a j * (2 * Real.pi * (j : ℝ)) ^ (2 * r) *
          ((-1 : ℝ) ^ r)) *
        Polynomial.Chebyshev.U ℝ ((j : ℤ) - 1)) ?_
  intro j hj
  have hj_index :
      ((j : ℤ) - 1) = ((((j : ℕ) - 1 : ℕ) : ℤ)) := by
    have hjpos : 1 ≤ (j : ℕ) := j.2.1
    norm_num
    omega
  calc
    (Polynomial.C
        (a j * (2 * Real.pi * (j : ℝ)) ^ (2 * r) *
          ((-1 : ℝ) ^ r)) *
        Polynomial.Chebyshev.U ℝ ((j : ℤ) - 1)).natDegree
        ≤ (Polynomial.Chebyshev.U ℝ ((j : ℤ) - 1)).natDegree :=
          Polynomial.natDegree_C_mul_le _ _
    _ = (Polynomial.Chebyshev.U ℝ ((((j : ℕ) - 1 : ℕ) : ℤ))).natDegree := by
          rw [hj_index]
    _ = (j : ℕ) - 1 := by
          rw [Polynomial.Chebyshev.natDegree_U_natCast]
    _ ≤ N - 1 := by
          exact Nat.sub_le_sub_right j.2.2 1

private lemma putnam_2000_b3_cos_two_pi_inj_left
    {x y : Ico (0 : ℝ) 1}
    (hx : (x : ℝ) ≤ 1 / 2) (hy : (y : ℝ) ≤ 1 / 2)
    (hcos : Real.cos (2 * Real.pi * (x : ℝ)) =
      Real.cos (2 * Real.pi * (y : ℝ))) :
    x = y := by
  have h2pi_nonneg : 0 ≤ 2 * Real.pi := by positivity
  have hxI : 2 * Real.pi * (x : ℝ) ∈ Icc (0 : ℝ) Real.pi := by
    constructor
    · exact mul_nonneg h2pi_nonneg x.2.1
    · have h := mul_le_mul_of_nonneg_left hx h2pi_nonneg
      nlinarith
  have hyI : 2 * Real.pi * (y : ℝ) ∈ Icc (0 : ℝ) Real.pi := by
    constructor
    · exact mul_nonneg h2pi_nonneg y.2.1
    · have h := mul_le_mul_of_nonneg_left hy h2pi_nonneg
      nlinarith
  have harg :
      2 * Real.pi * (x : ℝ) = 2 * Real.pi * (y : ℝ) :=
    Real.injOn_cos hxI hyI hcos
  apply Subtype.ext
  nlinarith [Real.pi_pos]

private lemma putnam_2000_b3_cos_two_pi_inj_right
    {x y : Ico (0 : ℝ) 1}
    (hx : 1 / 2 < (x : ℝ)) (hy : 1 / 2 < (y : ℝ))
    (hcos : Real.cos (2 * Real.pi * (x : ℝ)) =
      Real.cos (2 * Real.pi * (y : ℝ))) :
    x = y := by
  have h2pi_nonneg : 0 ≤ 2 * Real.pi := by positivity
  have hxcos :
      Real.cos (2 * Real.pi * (1 - (x : ℝ))) =
        Real.cos (2 * Real.pi * (x : ℝ)) := by
    have harg : 2 * Real.pi * (1 - (x : ℝ)) =
        2 * Real.pi - 2 * Real.pi * (x : ℝ) := by ring
    rw [harg, Real.cos_two_pi_sub]
  have hycos :
      Real.cos (2 * Real.pi * (1 - (y : ℝ))) =
        Real.cos (2 * Real.pi * (y : ℝ)) := by
    have harg : 2 * Real.pi * (1 - (y : ℝ)) =
        2 * Real.pi - 2 * Real.pi * (y : ℝ) := by ring
    rw [harg, Real.cos_two_pi_sub]
  have hxI : 2 * Real.pi * (1 - (x : ℝ)) ∈ Icc (0 : ℝ) Real.pi := by
    constructor
    · have hxle : (x : ℝ) ≤ 1 := le_of_lt x.2.2
      exact mul_nonneg h2pi_nonneg (sub_nonneg.mpr hxle)
    · have hxhalf : 1 - (x : ℝ) ≤ 1 / 2 := by linarith
      have h := mul_le_mul_of_nonneg_left hxhalf h2pi_nonneg
      nlinarith
  have hyI : 2 * Real.pi * (1 - (y : ℝ)) ∈ Icc (0 : ℝ) Real.pi := by
    constructor
    · have hyle : (y : ℝ) ≤ 1 := le_of_lt y.2.2
      exact mul_nonneg h2pi_nonneg (sub_nonneg.mpr hyle)
    · have hyhalf : 1 - (y : ℝ) ≤ 1 / 2 := by linarith
      have h := mul_le_mul_of_nonneg_left hyhalf h2pi_nonneg
      nlinarith
  have hcos' :
      Real.cos (2 * Real.pi * (1 - (x : ℝ))) =
        Real.cos (2 * Real.pi * (1 - (y : ℝ))) := by
    rw [hxcos, hycos, hcos]
  have harg :
      2 * Real.pi * (1 - (x : ℝ)) =
        2 * Real.pi * (1 - (y : ℝ)) :=
    Real.injOn_cos hxI hyI hcos'
  apply Subtype.ext
  nlinarith [Real.pi_pos]

private lemma putnam_2000_b3_cos_preimage_roots_card_le
    (P : Polynomial ℝ) (hP : P ≠ 0)
    (S : Finset (Ico (0 : ℝ) 1))
    (hroot : ∀ t ∈ S,
      P.IsRoot (Real.cos (2 * Real.pi * (t : ℝ)))) :
    S.card ≤ 2 * P.roots.toFinset.card := by
  classical
  let side : Ico (0 : ℝ) 1 → Bool :=
    fun t => if (t : ℝ) ≤ 1 / 2 then true else false
  let Φ : Ico (0 : ℝ) 1 → ℝ × Bool :=
    fun t => (Real.cos (2 * Real.pi * (t : ℝ)), side t)
  let R : Finset (ℝ × Bool) :=
    P.roots.toFinset ×ˢ (Finset.univ : Finset Bool)
  have hmaps : Set.MapsTo Φ (S : Set (Ico (0 : ℝ) 1)) (R : Set (ℝ × Bool)) := by
    intro t ht
    rw [show Φ t = (Real.cos (2 * Real.pi * (t : ℝ)), side t) by rfl]
    change (Real.cos (2 * Real.pi * (t : ℝ)), side t) ∈
      (P.roots.toFinset ×ˢ (Finset.univ : Finset Bool))
    rw [Finset.mem_product]
    constructor
    · exact Multiset.mem_toFinset.mpr
        ((Polynomial.mem_roots hP).mpr (hroot t ht))
    · simp
  have hinj : Set.InjOn Φ (S : Set (Ico (0 : ℝ) 1)) := by
    intro x hx y hy hxy
    have hcos :
        Real.cos (2 * Real.pi * (x : ℝ)) =
          Real.cos (2 * Real.pi * (y : ℝ)) := by
      exact congrArg Prod.fst hxy
    have hside : side x = side y := congrArg Prod.snd hxy
    by_cases hxhalf : (x : ℝ) ≤ 1 / 2
    · have hyhalf : (y : ℝ) ≤ 1 / 2 := by
        have hside_iff :
            ((x : ℝ) ≤ 1 / 2) ↔ ((y : ℝ) ≤ 1 / 2) := by
          simpa [side] using hside
        exact hside_iff.mp hxhalf
      exact putnam_2000_b3_cos_two_pi_inj_left hxhalf hyhalf hcos
    · have hxgt : 1 / 2 < (x : ℝ) := lt_of_not_ge hxhalf
      have hygt : 1 / 2 < (y : ℝ) := by
        by_contra hyle
        have hyle' : (y : ℝ) ≤ 1 / 2 := le_of_not_gt hyle
        have hside_iff :
            ((x : ℝ) ≤ 1 / 2) ↔ ((y : ℝ) ≤ 1 / 2) := by
          simpa [side] using hside
        exact hxhalf (hside_iff.mpr hyle')
      exact putnam_2000_b3_cos_two_pi_inj_right hxgt hygt hcos
  have hcard := Finset.card_le_card_of_injOn Φ hmaps hinj
  calc
    S.card ≤ R.card := hcard
    _ = P.roots.toFinset.card * 2 := by
      simp [R, Finset.card_product]
    _ = 2 * P.roots.toFinset.card := by omega

private lemma putnam_2000_b3_sin_two_pi_eq_zero
    {t : Ico (0 : ℝ) 1}
    (h : Real.sin (2 * Real.pi * (t : ℝ)) = 0) :
    (t : ℝ) = 0 ∨ (t : ℝ) = 1 / 2 := by
  rcases Real.sin_eq_zero_iff.mp h with ⟨n, hn⟩
  have hn' : (n : ℝ) = 2 * (t : ℝ) := by
    nlinarith [Real.pi_pos]
  have hn_nonneg : (0 : ℤ) ≤ n := by
    exact_mod_cast
      (show (0 : ℝ) ≤ (n : ℝ) by
        rw [hn']
        nlinarith [t.2.1])
  have hn_lt_two : n < (2 : ℤ) := by
    exact_mod_cast
      (show (n : ℝ) < 2 by
        rw [hn']
        nlinarith [t.2.2])
  have hn_int0or1 : n = 0 ∨ n = 1 := by omega
  rcases hn_int0or1 with rfl | rfl
  · left
    norm_num at hn'
    simpa using hn'
  · right
    norm_num at hn'
    linarith

private lemma putnam_2000_b3_sin_zero_card_le_two
    (S : Finset (Ico (0 : ℝ) 1))
    (hzero : ∀ t ∈ S, Real.sin (2 * Real.pi * (t : ℝ)) = 0) :
    S.card ≤ 2 := by
  classical
  let ψ : Ico (0 : ℝ) 1 → Bool :=
    fun t => if (t : ℝ) = 0 then false else true
  have hmaps :
      Set.MapsTo ψ (S : Set (Ico (0 : ℝ) 1))
        ((Finset.univ : Finset Bool) : Set Bool) := by
    intro t ht
    simp
  have hinj : Set.InjOn ψ (S : Set (Ico (0 : ℝ) 1)) := by
    intro x hx y hy hxy
    have hxclass := putnam_2000_b3_sin_two_pi_eq_zero (hzero x hx)
    have hyclass := putnam_2000_b3_sin_two_pi_eq_zero (hzero y hy)
    rcases hxclass with hx0 | hxhalf <;> rcases hyclass with hy0 | hyhalf
    · exact Subtype.ext (hx0.trans hy0.symm)
    · have hiff : ((x : ℝ) = 0) ↔ ((y : ℝ) = 0) := by
        simpa [ψ] using hxy
      have hy0' : (y : ℝ) = 0 := hiff.mp hx0
      have : False := by nlinarith
      exact this.elim
    · have hiff : ((x : ℝ) = 0) ↔ ((y : ℝ) = 0) := by
        simpa [ψ] using hxy
      have hx0' : (x : ℝ) = 0 := hiff.mpr hy0
      have : False := by nlinarith
      exact this.elim
    · exact Subtype.ext (hxhalf.trans hyhalf.symm)
  have hcard := Finset.card_le_card_of_injOn ψ hmaps hinj
  simpa using hcard

private lemma putnam_2000_b3_iteratedDeriv_ne_zero
    (N : ℕ) (hN : N > 0) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
    (haN : a (putnam_2000_b3_top N hN) ≠ 0)
    (hf : ∀ t, f t = ∑ j : Icc 1 N,
      a j * Real.sin (2 * Real.pi * j * t))
    (k : ℕ) :
    iteratedDeriv k f ≠ 0 := by
  classical
  intro hzero
  rcases Nat.even_or_odd k with hk | hk
  · rcases (even_iff_exists_two_mul.mp hk) with ⟨r, rfl⟩
    let P := putnam_2000_b3_evenPoly N a r
    have hroots : Set.Ioo (-1 : ℝ) 1 ⊆ {x : ℝ | P.IsRoot x} := by
      intro x hx
      let t : ℝ := Real.arccos x / (2 * Real.pi)
      have harg : 2 * Real.pi * t = Real.arccos x := by
        change 2 * Real.pi * (Real.arccos x / (2 * Real.pi)) = Real.arccos x
        field_simp [Real.pi_ne_zero]
      have hcos : Real.cos (2 * Real.pi * t) = x := by
        rw [harg]
        exact Real.cos_arccos (le_of_lt hx.1) (le_of_lt hx.2)
      have hsin_ne : Real.sin (2 * Real.pi * t) ≠ 0 := by
        rw [harg, Real.sin_arccos]
        apply (Real.sqrt_pos_of_pos ?_).ne'
        have hxabs : |x| < 1 := abs_lt.mpr ⟨hx.1, hx.2⟩
        have hxsq : x ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one x).2 hxabs
        nlinarith
      have heval := putnam_2000_b3_evenPoly_eval N a f hf r t
      have hzero_t : iteratedDeriv (2 * r) f t = 0 := by
        simpa using congr_fun hzero t
      rw [hzero_t, hcos] at heval
      simpa [Polynomial.IsRoot] using ((mul_eq_zero.mp heval).resolve_left hsin_ne)
    have hPzero : P = 0 := by
      exact Polynomial.eq_zero_of_infinite_isRoot P
        (Set.Infinite.mono hroots (Ioo_infinite (by norm_num : (-1 : ℝ) < 1)))
    have hcoeff : P.coeff (N - 1) ≠ 0 := by
      simpa [P] using putnam_2000_b3_evenPoly_coeff_top_ne_zero N hN a r haN
    rw [hPzero] at hcoeff
    exact hcoeff (by simp)
  · rcases (odd_iff_exists_bit1.mp hk) with ⟨r, rfl⟩
    let P := putnam_2000_b3_oddPoly N a r
    have hroots : Set.Ioo (-1 : ℝ) 1 ⊆ {x : ℝ | P.IsRoot x} := by
      intro x hx
      let t : ℝ := Real.arccos x / (2 * Real.pi)
      have harg : 2 * Real.pi * t = Real.arccos x := by
        change 2 * Real.pi * (Real.arccos x / (2 * Real.pi)) = Real.arccos x
        field_simp [Real.pi_ne_zero]
      have hcos : Real.cos (2 * Real.pi * t) = x := by
        rw [harg]
        exact Real.cos_arccos (le_of_lt hx.1) (le_of_lt hx.2)
      have heval := putnam_2000_b3_oddPoly_eval N a f hf r t
      have hzero_t : iteratedDeriv (2 * r + 1) f t = 0 := by
        simpa using congr_fun hzero t
      rw [hzero_t, hcos] at heval
      simpa [Polynomial.IsRoot] using heval
    have hPzero : P = 0 := by
      exact Polynomial.eq_zero_of_infinite_isRoot P
        (Set.Infinite.mono hroots (Ioo_infinite (by norm_num : (-1 : ℝ) < 1)))
    have hcoeff : P.coeff N ≠ 0 := by
      simpa [P] using putnam_2000_b3_oddPoly_coeff_top_ne_zero N hN a r haN
    rw [hPzero] at hcoeff
    exact hcoeff (by simp)

private lemma putnam_2000_b3_analyticAt
    (N : ℕ) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
    (hf : ∀ t, f t = ∑ j : Icc 1 N,
      a j * Real.sin (2 * Real.pi * j * t))
    (t : ℝ) :
    AnalyticAt ℝ f t := by
  rw [show f = fun t => ∑ j : Icc 1 N,
    a j * Real.sin (2 * Real.pi * j * t) from funext hf]
  fun_prop

private lemma putnam_2000_b3_analyticAt_iteratedDeriv
    (N : ℕ) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
    (hf : ∀ t, f t = ∑ j : Icc 1 N,
      a j * Real.sin (2 * Real.pi * j * t))
    (k : ℕ) (t : ℝ) :
    AnalyticAt ℝ (iteratedDeriv k f) t := by
  induction k with
  | zero =>
      simpa [iteratedDeriv_zero] using
        putnam_2000_b3_analyticAt N a f hf t
  | succ k ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

private lemma putnam_2000_b3_analyticOrderAt_iteratedDeriv_ne_top
    (N : ℕ) (hN : N > 0) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
    (haN : a (putnam_2000_b3_top N hN) ≠ 0)
    (hf : ∀ t, f t = ∑ j : Icc 1 N,
      a j * Real.sin (2 * Real.pi * j * t))
    (k : ℕ) (t : ℝ) :
    analyticOrderAt (iteratedDeriv k f) t ≠ ⊤ := by
  classical
  have han : AnalyticOnNhd ℝ (iteratedDeriv k f) Set.univ := by
    intro x hx
    exact putnam_2000_b3_analyticAt_iteratedDeriv N a f hf k x
  have hnonzero : iteratedDeriv k f ≠ 0 :=
    putnam_2000_b3_iteratedDeriv_ne_zero N hN a f haN hf k
  obtain ⟨x, hx⟩ : ∃ x, iteratedDeriv k f x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hnonzero (funext h)
  have hxfin : analyticOrderAt (iteratedDeriv k f) x ≠ ⊤ := by
    have hxzero :
        analyticOrderAt (iteratedDeriv k f) x = 0 :=
      (putnam_2000_b3_analyticAt_iteratedDeriv N a f hf k x).analyticOrderAt_eq_zero.2 hx
    rw [hxzero]
    exact ENat.zero_ne_top
  exact han.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (Set.mem_univ x) (Set.mem_univ t) hxfin

private lemma putnam_2000_b3_mult_eq_analyticOrderNatAt
    (mult : (ℝ → ℝ) → ℝ → ℕ)
    (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ,
      (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
        (iteratedDeriv (mult g t) g t ≠ 0 ∧
          ∀ k < (mult g t), iteratedDeriv k g t = 0))
    {g : ℝ → ℝ} {t : ℝ} (hg : AnalyticAt ℝ g t)
    (hgtop : analyticOrderAt g t ≠ ⊤) :
    mult g t = analyticOrderNatAt g t := by
  let n := analyticOrderNatAt g t
  have hn : analyticOrderAt g t = (n : ℕ∞) := by
    simpa [n] using (ENat.coe_toNat hgtop).symm
  have hz : ∀ k < n, iteratedDeriv k g t = 0 := by
    have hle : (n : ℕ∞) ≤ analyticOrderAt g t := by
      rw [hn]
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hg).mp hle
  have hnz : iteratedDeriv n g t ≠ 0 := by
    intro hzero
    have hsuccle : ((n + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt g t := by
      rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hg]
      intro i hi
      have hle : i ≤ n := Nat.lt_succ_iff.mp hi
      rcases hle.eq_or_lt with rfl | hlt
      · exact hzero
      · exact hz i hlt
    rw [hn, ENat.coe_le_coe] at hsuccle
    omega
  exact putnam_2000_b3_mult_eq_of_first_nonzero mult hmult hnz hz

private lemma putnam_2000_b3_mult_iteratedDeriv_eq_analyticOrderNatAt
    (N : ℕ) (hN : N > 0) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
    (mult : (ℝ → ℝ) → ℝ → ℕ)
    (haN : a (putnam_2000_b3_top N hN) ≠ 0)
    (hf : ∀ t, f t = ∑ j : Icc 1 N,
      a j * Real.sin (2 * Real.pi * j * t))
    (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ,
      (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
        (iteratedDeriv (mult g t) g t ≠ 0 ∧
          ∀ k < (mult g t), iteratedDeriv k g t = 0))
    (k : ℕ) (t : ℝ) :
    mult (iteratedDeriv k f) t =
      analyticOrderNatAt (iteratedDeriv k f) t := by
  exact putnam_2000_b3_mult_eq_analyticOrderNatAt mult hmult
    (putnam_2000_b3_analyticAt_iteratedDeriv N a f hf k t)
    (putnam_2000_b3_analyticOrderAt_iteratedDeriv_ne_top N hN a f haN hf k t)

private lemma putnam_2000_b3_exists_iteratedDeriv_iteratedDeriv_ne_zero
    (N : ℕ) (hN : N > 0) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
    (haN : a (putnam_2000_b3_top N hN) ≠ 0)
    (hf : ∀ t, f t = ∑ j : Icc 1 N,
      a j * Real.sin (2 * Real.pi * j * t))
    (k : ℕ) (t : ℝ) :
    ∃ c : ℕ, iteratedDeriv c (iteratedDeriv k f) t ≠ 0 := by
  let g : ℝ → ℝ := iteratedDeriv k f
  let n := analyticOrderNatAt g t
  have hg : AnalyticAt ℝ g t :=
    putnam_2000_b3_analyticAt_iteratedDeriv N a f hf k t
  have hgtop : analyticOrderAt g t ≠ ⊤ :=
    putnam_2000_b3_analyticOrderAt_iteratedDeriv_ne_top N hN a f haN hf k t
  have hn : analyticOrderAt g t = (n : ℕ∞) := by
    simpa [n] using (ENat.coe_toNat hgtop).symm
  have hz : ∀ i < n, iteratedDeriv i g t = 0 := by
    have hle : (n : ℕ∞) ≤ analyticOrderAt g t := by
      rw [hn]
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hg).mp hle
  refine ⟨n, ?_⟩
  intro hzero
  have hsuccle : ((n + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt g t := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hg]
    intro i hi
    have hle : i ≤ n := Nat.lt_succ_iff.mp hi
    rcases hle.eq_or_lt with rfl | hlt
    · exact hzero
    · exact hz i hlt
  rw [hn, ENat.coe_le_coe] at hsuccle
  omega

private lemma putnam_2000_b3_mult_iteratedDeriv_le_succ
    (N : ℕ) (hN : N > 0) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
    (mult : (ℝ → ℝ) → ℝ → ℕ)
    (haN : a (putnam_2000_b3_top N hN) ≠ 0)
    (hf : ∀ t, f t = ∑ j : Icc 1 N,
      a j * Real.sin (2 * Real.pi * j * t))
    (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ,
      (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
        (iteratedDeriv (mult g t) g t ≠ 0 ∧
          ∀ k < (mult g t), iteratedDeriv k g t = 0))
    (k : ℕ) (t : ℝ) :
    mult (iteratedDeriv k f) t ≤
      mult (iteratedDeriv (k + 1) f) t + 1 := by
  by_cases hzero : mult (iteratedDeriv k f) t = 0
  · simp [hzero]
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    have hex :
        ∃ c : ℕ, iteratedDeriv c (iteratedDeriv k f) t ≠ 0 :=
      putnam_2000_b3_exists_iteratedDeriv_iteratedDeriv_ne_zero
        N hN a f haN hf k t
    have hpred :
        mult (iteratedDeriv (k + 1) f) t = n :=
      putnam_2000_b3_mult_iteratedDeriv_succ_eq_pred
        mult hmult (f := f) (t := t) (k := k) (n := n) hn hex
    simp [hn, hpred]

private lemma putnam_2000_b3_polynomial_analyticOrderNatAt_eq_rootMultiplicity
    (P : Polynomial ℝ) (hP : P ≠ 0) (x : ℝ) :
    analyticOrderNatAt (fun y : ℝ => P.eval y) x =
      P.rootMultiplicity x := by
  let m := P.rootMultiplicity x
  let Q := P /ₘ (Polynomial.X - Polynomial.C x) ^ m
  have hQx : Q.eval x ≠ 0 := by
    simpa [Q, m] using
      Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero (p := P) x hP
  have horder :
      analyticOrderAt (fun y : ℝ => P.eval y) x = (m : ℕ∞) := by
    have hPan : AnalyticAt ℝ (fun y : ℝ => P.eval y) x := by
      simpa using (AnalyticOnNhd.eval_polynomial (𝕜 := ℝ) P x (by simp))
    rw [hPan.analyticOrderAt_eq_natCast]
    refine ⟨fun y : ℝ => Q.eval y, ?_, hQx, ?_⟩
    · simpa using (AnalyticOnNhd.eval_polynomial (𝕜 := ℝ) Q x (by simp))
    apply Filter.Eventually.of_forall
    intro y
    have hpoly :
        (((Polynomial.X - Polynomial.C x) ^ m * Q).eval y) = P.eval y := by
      simpa [Q, m] using congrArg (fun R : Polynomial ℝ => R.eval y)
        (Polynomial.pow_mul_divByMonic_rootMultiplicity_eq P x)
    change P.eval y = (y - x) ^ m • Q.eval y
    rw [← hpoly]
    simp [Q, m, smul_eq_mul]
  simp [analyticOrderNatAt, horder, m]

private lemma putnam_2000_b3_zero_set_Icc_finite
    (N : ℕ) (hN : N > 0) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
    (haN : a (putnam_2000_b3_top N hN) ≠ 0)
    (hf : ∀ t, f t = ∑ j : Icc 1 N,
      a j * Real.sin (2 * Real.pi * j * t))
    (k : ℕ) :
    ({t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ iteratedDeriv k f t = 0}).Finite := by
  classical
  let g : ℝ → ℝ := iteratedDeriv k f
  have han : AnalyticOnNhd ℝ g Set.univ := by
    intro x hx
    exact putnam_2000_b3_analyticAt_iteratedDeriv N a f hf k x
  have hnonzero : g ≠ 0 :=
    putnam_2000_b3_iteratedDeriv_ne_zero N hN a f haN hf k
  obtain ⟨x, hx⟩ : ∃ x, g x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hnonzero (funext h)
  have hcod :
      g ⁻¹' ({0}ᶜ : Set ℝ) ∈
        Filter.codiscreteWithin (Set.univ : Set ℝ) := by
    simpa using han.preimage_zero_mem_codiscreteWithin hx
      (Set.mem_univ x) isConnected_univ
  have hdisc_zero : IsDiscrete (g ⁻¹' ({0} : Set ℝ)) := by
    have hdisc :=
      isDiscrete_of_codiscreteWithin
        (U := (Set.univ : Set ℝ)) (s := g ⁻¹' ({0} : Set ℝ))
        (by simpa [Set.preimage_compl] using hcod)
    simpa [Set.inter_univ] using hdisc
  have hclosed_zero : IsClosed (g ⁻¹' ({0} : Set ℝ)) := by
    exact isClosed_singleton.preimage
      (putnam_2000_b3_continuous_iteratedDeriv N a f hf k)
  have hcompact :
      IsCompact ((g ⁻¹' ({0} : Set ℝ)) ∩ Icc (0 : ℝ) 1) :=
    isCompact_Icc.inter_left hclosed_zero
  have hdisc :
      IsDiscrete ((g ⁻¹' ({0} : Set ℝ)) ∩ Icc (0 : ℝ) 1) :=
    hdisc_zero.mono Set.inter_subset_left
  have hfinite :
      ((g ⁻¹' ({0} : Set ℝ)) ∩ Icc (0 : ℝ) 1).Finite :=
    hcompact.finite hdisc
  convert hfinite using 1
  ext t
  simp [g, and_comm]

private lemma putnam_2000_b3_mult_support_finite
    (N : ℕ) (hN : N > 0) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
    (mult : (ℝ → ℝ) → ℝ → ℕ)
    (haN : a (putnam_2000_b3_top N hN) ≠ 0)
    (hf : ∀ t, f t = ∑ j : Icc 1 N,
      a j * Real.sin (2 * Real.pi * j * t))
    (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ,
      (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
        (iteratedDeriv (mult g t) g t ≠ 0 ∧
          ∀ k < (mult g t), iteratedDeriv k g t = 0))
    (k : ℕ) :
    (Function.support fun t : Ico (0 : ℝ) 1 =>
      mult (iteratedDeriv k f) t).Finite := by
  classical
  let g : ℝ → ℝ := iteratedDeriv k f
  let S : Set (Ico (0 : ℝ) 1) :=
    Function.support fun t : Ico (0 : ℝ) 1 => mult g t
  let Z : Set ℝ := {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ g t = 0}
  have hZ : Z.Finite := by
    simpa [Z, g] using
      putnam_2000_b3_zero_set_Icc_finite N hN a f haN hf k
  have himage : ((fun t : Ico (0 : ℝ) 1 => (t : ℝ)) '' S).Finite := by
    refine hZ.subset ?_
    intro x hx
    rcases hx with ⟨t, htS, rfl⟩
    constructor
    · exact Ico_subset_Icc_self t.property
    · by_contra hgt
      have hzero :
          mult g (t : ℝ) = 0 :=
        putnam_2000_b3_mult_eq_zero_of_value_ne_zero mult hmult hgt
      exact htS hzero
  have hS : S.Finite :=
    himage.of_finite_image (Subtype.coe_injective.injOn)
  simpa [S, g] using hS

private lemma putnam_2000_b3_M_eq_support_sum
    (N : ℕ) (hN : N > 0) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
    (mult : (ℝ → ℝ) → ℝ → ℕ) (M : ℕ → ℕ)
    (haN : a (putnam_2000_b3_top N hN) ≠ 0)
    (hf : ∀ t, f t = ∑ j : Icc 1 N,
      a j * Real.sin (2 * Real.pi * j * t))
    (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ,
      (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
        (iteratedDeriv (mult g t) g t ≠ 0 ∧
          ∀ k < (mult g t), iteratedDeriv k g t = 0))
    (hM : ∀ k, M k = ∑' t : Ico (0 : ℝ) 1,
      mult (iteratedDeriv k f) t)
    (k : ℕ) :
    M k =
      ∑ t ∈ (putnam_2000_b3_mult_support_finite
          N hN a f mult haN hf hmult k).toFinset,
        mult (iteratedDeriv k f) t := by
  let F : Ico (0 : ℝ) 1 → ℕ :=
    fun t => mult (iteratedDeriv k f) t
  let hs : (Function.support F).Finite :=
    putnam_2000_b3_mult_support_finite N hN a f mult haN hf hmult k
  calc
    M k = ∑' t : Ico (0 : ℝ) 1, F t := by
      simpa [F] using hM k
    _ = ∑ t ∈ hs.toFinset, F t := by
      exact tsum_eq_sum' (s := hs.toFinset) (f := F)
        (by intro t ht; exact (hs.mem_toFinset).2 ht)
    _ =
      ∑ t ∈ (putnam_2000_b3_mult_support_finite
          N hN a f mult haN hf hmult k).toFinset,
        mult (iteratedDeriv k f) t := by
      rfl

private lemma putnam_2000_b3_zero_of_mem_support
    (N : ℕ) (hN : N > 0) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
    (mult : (ℝ → ℝ) → ℝ → ℕ)
    (haN : a (putnam_2000_b3_top N hN) ≠ 0)
    (hf : ∀ t, f t = ∑ j : Icc 1 N,
      a j * Real.sin (2 * Real.pi * j * t))
    (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ,
      (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
        (iteratedDeriv (mult g t) g t ≠ 0 ∧
          ∀ k < (mult g t), iteratedDeriv k g t = 0))
    {k : ℕ} {t : Ico (0 : ℝ) 1}
    (ht : t ∈ (putnam_2000_b3_mult_support_finite
      N hN a f mult haN hf hmult k).toFinset) :
    iteratedDeriv k f (t : ℝ) = 0 := by
  classical
  have htpos :
      mult (iteratedDeriv k f) (t : ℝ) ≠ 0 := by
    exact (putnam_2000_b3_mult_support_finite
      N hN a f mult haN hf hmult k).mem_toFinset.mp ht
  have hlt : 0 < mult (iteratedDeriv k f) (t : ℝ) :=
    Nat.pos_of_ne_zero htpos
  have hex :
      ∃ c : ℕ, iteratedDeriv c (iteratedDeriv k f) (t : ℝ) ≠ 0 :=
    putnam_2000_b3_exists_iteratedDeriv_iteratedDeriv_ne_zero
      N hN a f haN hf k (t : ℝ)
  have h := hmult (iteratedDeriv k f) (t : ℝ) hex
  simpa [iteratedDeriv_zero] using h.2 0 hlt

private lemma putnam_2000_b3_mem_deriv_support_of_zero
    (N : ℕ) (hN : N > 0) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
    (mult : (ℝ → ℝ) → ℝ → ℕ)
    (haN : a (putnam_2000_b3_top N hN) ≠ 0)
    (hf : ∀ t, f t = ∑ j : Icc 1 N,
      a j * Real.sin (2 * Real.pi * j * t))
    (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ,
      (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
        (iteratedDeriv (mult g t) g t ≠ 0 ∧
          ∀ k < (mult g t), iteratedDeriv k g t = 0))
    {k : ℕ} {t : Ico (0 : ℝ) 1}
    (htzero : iteratedDeriv (k + 1) f (t : ℝ) = 0) :
    t ∈ (putnam_2000_b3_mult_support_finite
      N hN a f mult haN hf hmult (k + 1)).toFinset := by
  classical
  rw [(putnam_2000_b3_mult_support_finite
      N hN a f mult haN hf hmult (k + 1)).mem_toFinset]
  intro hzero
  have hex :
      ∃ c : ℕ, iteratedDeriv c (iteratedDeriv (k + 1) f) (t : ℝ) ≠ 0 :=
    putnam_2000_b3_exists_iteratedDeriv_iteratedDeriv_ne_zero
      N hN a f haN hf (k + 1) (t : ℝ)
  have h := hmult (iteratedDeriv (k + 1) f) (t : ℝ) hex
  have hval : iteratedDeriv 0 (iteratedDeriv (k + 1) f) (t : ℝ) ≠ 0 := by
    simpa [hzero] using h.1
  exact hval (by simpa [iteratedDeriv_zero] using htzero)

private lemma putnam_2000_b3_mem_support_of_zero
    (N : ℕ) (hN : N > 0) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
    (mult : (ℝ → ℝ) → ℝ → ℕ)
    (haN : a (putnam_2000_b3_top N hN) ≠ 0)
    (hf : ∀ t, f t = ∑ j : Icc 1 N,
      a j * Real.sin (2 * Real.pi * j * t))
    (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ,
      (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
        (iteratedDeriv (mult g t) g t ≠ 0 ∧
          ∀ k < (mult g t), iteratedDeriv k g t = 0))
    {k : ℕ} {t : Ico (0 : ℝ) 1}
    (htzero : iteratedDeriv k f (t : ℝ) = 0) :
    t ∈ (putnam_2000_b3_mult_support_finite
      N hN a f mult haN hf hmult k).toFinset := by
  classical
  rw [(putnam_2000_b3_mult_support_finite
      N hN a f mult haN hf hmult k).mem_toFinset]
  intro hzero
  have hex :
      ∃ c : ℕ, iteratedDeriv c (iteratedDeriv k f) (t : ℝ) ≠ 0 :=
    putnam_2000_b3_exists_iteratedDeriv_iteratedDeriv_ne_zero
      N hN a f haN hf k (t : ℝ)
  have h := hmult (iteratedDeriv k f) (t : ℝ) hex
  have hval : iteratedDeriv 0 (iteratedDeriv k f) (t : ℝ) ≠ 0 := by
    simpa [hzero] using h.1
  exact hval (by simpa [iteratedDeriv_zero] using htzero)

private noncomputable def putnam_2000_b3_oddEndpointNorm
    (N : ℕ) (a : Icc 1 N → ℝ) (r m : ℕ) : ℝ :=
  ∑ j : Icc 1 N,
    a j *
      (((2 * Real.pi * (j : ℝ)) ^ (2 * r + 1)) /
        ((2 * Real.pi * (N : ℝ)) ^ (2 * r + 1))) *
      Real.cos ((2 * Real.pi * (j : ℝ)) *
        ((m : ℝ) / (2 * (N : ℝ))))

private lemma putnam_2000_b3_top_endpoint_cos
    (N : ℕ) (hN : N > 0) (m : ℕ) :
    Real.cos ((2 * Real.pi * (putnam_2000_b3_top N hN : ℝ)) *
        ((m : ℝ) / (2 * (N : ℝ)))) =
      (-1 : ℝ) ^ m := by
  change Real.cos ((2 * Real.pi * (N : ℝ)) *
      ((m : ℝ) / (2 * (N : ℝ)))) = (-1 : ℝ) ^ m
  have hN0 : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hN)
  have harg :
      (2 * Real.pi * (N : ℝ)) * ((m : ℝ) / (2 * (N : ℝ))) =
        (m : ℝ) * Real.pi := by
    field_simp [hN0]
  rw [harg, Real.cos_nat_mul_pi]

private lemma putnam_2000_b3_oddEndpointNorm_tendsto
    (N : ℕ) (hN : N > 0) (a : Icc 1 N → ℝ) (m : ℕ) :
    Tendsto (fun r : ℕ => putnam_2000_b3_oddEndpointNorm N a r m)
      atTop (𝓝 (a (putnam_2000_b3_top N hN) * (-1 : ℝ) ^ m)) := by
  classical
  let top : Icc 1 N := putnam_2000_b3_top N hN
  have hcomp : Tendsto (fun r : ℕ => 2 * r + 1) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨b, ?_⟩
    intro r hr
    omega
  have hterms :
      ∀ j ∈ (Finset.univ : Finset (Icc 1 N)),
        Tendsto
          (fun r : ℕ =>
            a j *
              (((2 * Real.pi * (j : ℝ)) ^ (2 * r + 1)) /
                ((2 * Real.pi * (N : ℝ)) ^ (2 * r + 1))) *
              Real.cos ((2 * Real.pi * (j : ℝ)) *
                ((m : ℝ) / (2 * (N : ℝ)))))
          atTop
          (𝓝 (if j = top then a top * (-1 : ℝ) ^ m else 0)) := by
    intro j hj
    by_cases hjtop : j = top
    · subst j
      refine tendsto_const_nhds.congr' ?_
      filter_upwards with r
      have hden : (2 * Real.pi * (N : ℝ)) ≠ 0 := by positivity
      have hdenpow :
          (2 * Real.pi * (N : ℝ)) ^ (2 * r + 1) ≠ 0 :=
        pow_ne_zero _ hden
      have hratio :
          ((2 * Real.pi * (top : ℝ)) ^ (2 * r + 1)) /
              ((2 * Real.pi * (N : ℝ)) ^ (2 * r + 1)) =
            1 := by
        change ((2 * Real.pi * (N : ℝ)) ^ (2 * r + 1)) /
            ((2 * Real.pi * (N : ℝ)) ^ (2 * r + 1)) = 1
        field_simp [hdenpow]
      simp [top, hratio, putnam_2000_b3_top_endpoint_cos]
    · have hjlt : (j : ℕ) < N := by
        have hjle : (j : ℕ) ≤ N := j.2.2
        have hjne : (j : ℕ) ≠ N := by
          intro h
          exact hjtop (Subtype.ext h)
        omega
      let q : ℝ := (2 * Real.pi * (j : ℝ)) / (2 * Real.pi * (N : ℝ))
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      have hdenpos : 0 < 2 * Real.pi * (N : ℝ) := by positivity
      have hq0 : 0 ≤ q := by
        have hnum_nonneg : 0 ≤ 2 * Real.pi * (j : ℝ) := by positivity
        exact div_nonneg hnum_nonneg hdenpos.le
      have hq1 : q < 1 := by
        have hjltR : (j : ℝ) < (N : ℝ) := by exact_mod_cast hjlt
        have hnumlt :
            2 * Real.pi * (j : ℝ) < 2 * Real.pi * (N : ℝ) := by
          nlinarith [Real.pi_pos]
        exact (div_lt_one hdenpos).mpr hnumlt
      have hpow :
          Tendsto (fun r : ℕ => q ^ (2 * r + 1)) atTop (𝓝 0) := by
        simpa [Function.comp_def] using
          (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp hcomp
      have hterm :
          Tendsto
            (fun r : ℕ =>
              a j * (q ^ (2 * r + 1)) *
                Real.cos ((2 * Real.pi * (j : ℝ)) *
                  ((m : ℝ) / (2 * (N : ℝ)))))
            atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds.mul hpow).mul tendsto_const_nhds
      have hterm' :
          Tendsto
            (fun r : ℕ =>
              a j *
                (((2 * Real.pi * (j : ℝ)) ^ (2 * r + 1)) /
                  ((2 * Real.pi * (N : ℝ)) ^ (2 * r + 1))) *
                Real.cos ((2 * Real.pi * (j : ℝ)) *
                  ((m : ℝ) / (2 * (N : ℝ)))))
            atTop (𝓝 0) := by
        refine hterm.congr' ?_
        filter_upwards with r
        simp [q, div_pow]
      simpa [hjtop] using hterm'
  have hsum := tendsto_finset_sum
    (s := (Finset.univ : Finset (Icc 1 N))) hterms
  simpa [putnam_2000_b3_oddEndpointNorm, top] using hsum

private lemma putnam_2000_b3_odd_endpoint_scaled_eq
    (N : ℕ) (hN : N > 0) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
    (hf : ∀ t, f t = ∑ j : Icc 1 N,
      a j * Real.sin (2 * Real.pi * j * t))
    (r m : ℕ) :
    (((-1 : ℝ) ^ r * (-1 : ℝ) ^ m *
        a (putnam_2000_b3_top N hN)) *
      iteratedDeriv (2 * r + 1) f ((m : ℝ) / (2 * (N : ℝ)))) =
      ((2 * Real.pi * (N : ℝ)) ^ (2 * r + 1)) *
        (((-1 : ℝ) ^ m * a (putnam_2000_b3_top N hN)) *
          putnam_2000_b3_oddEndpointNorm N a r m) := by
  classical
  rw [putnam_2000_b3_iteratedDeriv_odd_sum N a f hf r]
  rw [putnam_2000_b3_oddEndpointNorm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hscale :
      (2 * Real.pi * (N : ℝ)) ^ (2 * r + 1) ≠ 0 := by
    apply pow_ne_zero
    positivity
  have hsign :
      ((-1 : ℝ) ^ r) * ((-1 : ℝ) ^ r) = 1 := by
    rw [← pow_add]
    have hrr : r + r = 2 * r := by omega
    rw [hrr, pow_mul]
    norm_num
  field_simp [hscale]
  have hsign2 : ((-1 : ℝ) ^ r) ^ 2 = 1 := by
    simpa [sq] using hsign
  rw [hsign2]
  ring

private lemma putnam_2000_b3_odd_endpoint_sign_eventually
    (N : ℕ) (hN : N > 0) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
    (haN : a (putnam_2000_b3_top N hN) ≠ 0)
    (hf : ∀ t, f t = ∑ j : Icc 1 N,
      a j * Real.sin (2 * Real.pi * j * t)) :
    ∀ᶠ r in atTop, ∀ m ∈ Finset.range (2 * N + 1),
      0 < (((-1 : ℝ) ^ r * (-1 : ℝ) ^ m *
          a (putnam_2000_b3_top N hN)) *
        iteratedDeriv (2 * r + 1) f
          ((m : ℝ) / (2 * (N : ℝ)))) := by
  classical
  rw [Filter.eventually_all_finset]
  intro m hm
  have hnorm :
      Tendsto
        (fun r : ℕ =>
          ((-1 : ℝ) ^ m * a (putnam_2000_b3_top N hN)) *
            putnam_2000_b3_oddEndpointNorm N a r m)
        atTop
        (𝓝 (((-1 : ℝ) ^ m * a (putnam_2000_b3_top N hN)) *
          (a (putnam_2000_b3_top N hN) * (-1 : ℝ) ^ m))) := by
    exact tendsto_const_nhds.mul
      (putnam_2000_b3_oddEndpointNorm_tendsto N hN a m)
  have hlimpos :
      0 < (((-1 : ℝ) ^ m * a (putnam_2000_b3_top N hN)) *
        (a (putnam_2000_b3_top N hN) * (-1 : ℝ) ^ m)) := by
    have hsign_ne : ((-1 : ℝ) ^ m) ≠ 0 :=
      pow_ne_zero _ (by norm_num)
    have hsq :
        0 < (((-1 : ℝ) ^ m * a (putnam_2000_b3_top N hN)) ^ 2) :=
      sq_pos_of_ne_zero (mul_ne_zero hsign_ne haN)
    nlinarith
  have hevent :
      ∀ᶠ r in atTop,
        0 < ((-1 : ℝ) ^ m * a (putnam_2000_b3_top N hN)) *
          putnam_2000_b3_oddEndpointNorm N a r m :=
    hnorm.eventually_const_lt hlimpos
  filter_upwards [hevent] with r hr
  have hscale_pos :
      0 < (2 * Real.pi * (N : ℝ)) ^ (2 * r + 1) := by
    positivity
  have hscaled := putnam_2000_b3_odd_endpoint_scaled_eq
    N hN a f hf r m
  rw [hscaled]
  positivity
private lemma putnam_2000_b3_odd_support_card_le
    (N : ℕ) (hN : N > 0) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
    (mult : (ℝ → ℝ) → ℝ → ℕ)
    (haN : a (putnam_2000_b3_top N hN) ≠ 0)
    (hf : ∀ t, f t = ∑ j : Icc 1 N,
      a j * Real.sin (2 * Real.pi * j * t))
    (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ,
      (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
        (iteratedDeriv (mult g t) g t ≠ 0 ∧
          ∀ k < (mult g t), iteratedDeriv k g t = 0))
    (r : ℕ) :
    ((putnam_2000_b3_mult_support_finite
      N hN a f mult haN hf hmult (2 * r + 1)).toFinset).card ≤ 2 * N := by
  classical
  let S := (putnam_2000_b3_mult_support_finite
      N hN a f mult haN hf hmult (2 * r + 1)).toFinset
  let P := putnam_2000_b3_oddPoly N a r
  change S.card ≤ 2 * N
  have hP : P ≠ 0 := by
    intro hzero
    have hcoeff : P.coeff N ≠ 0 := by
      simpa [P] using putnam_2000_b3_oddPoly_coeff_top_ne_zero N hN a r haN
    rw [hzero] at hcoeff
    exact hcoeff (by simp)
  have hroot : ∀ t ∈ S,
      P.IsRoot (Real.cos (2 * Real.pi * (t : ℝ))) := by
    intro t ht
    have hzero : iteratedDeriv (2 * r + 1) f (t : ℝ) = 0 :=
      putnam_2000_b3_zero_of_mem_support
        N hN a f mult haN hf hmult (k := 2 * r + 1) (by simpa [S] using ht)
    have heval := putnam_2000_b3_oddPoly_eval N a f hf r (t : ℝ)
    rw [hzero] at heval
    simpa [P, Polynomial.IsRoot] using heval
  have hpre :
      S.card ≤ 2 * P.roots.toFinset.card :=
    putnam_2000_b3_cos_preimage_roots_card_le P hP S hroot
  have hrootcard₁ : P.roots.toFinset.card ≤ Multiset.card P.roots :=
    Multiset.toFinset_card_le P.roots
  have hrootcard₂ : Multiset.card P.roots ≤ P.natDegree :=
    Polynomial.card_roots' P
  have hroots : P.roots.toFinset.card ≤ N :=
    (hrootcard₁.trans hrootcard₂).trans
      (by simpa [P] using putnam_2000_b3_oddPoly_natDegree_le N a r)
  omega

private lemma putnam_2000_b3_even_support_card_le
    (N : ℕ) (hN : N > 0) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
    (mult : (ℝ → ℝ) → ℝ → ℕ)
    (haN : a (putnam_2000_b3_top N hN) ≠ 0)
    (hf : ∀ t, f t = ∑ j : Icc 1 N,
      a j * Real.sin (2 * Real.pi * j * t))
    (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ,
      (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
        (iteratedDeriv (mult g t) g t ≠ 0 ∧
          ∀ k < (mult g t), iteratedDeriv k g t = 0))
    (r : ℕ) :
    ((putnam_2000_b3_mult_support_finite
      N hN a f mult haN hf hmult (2 * r)).toFinset).card ≤ 2 * N := by
  classical
  let S := (putnam_2000_b3_mult_support_finite
      N hN a f mult haN hf hmult (2 * r)).toFinset
  let P := putnam_2000_b3_evenPoly N a r
  let A := S.filter fun t : Ico (0 : ℝ) 1 =>
    Real.sin (2 * Real.pi * (t : ℝ)) = 0
  let B := S.filter fun t : Ico (0 : ℝ) 1 =>
    P.IsRoot (Real.cos (2 * Real.pi * (t : ℝ)))
  change S.card ≤ 2 * N
  have hP : P ≠ 0 := by
    intro hzero
    have hcoeff : P.coeff (N - 1) ≠ 0 := by
      simpa [P] using putnam_2000_b3_evenPoly_coeff_top_ne_zero N hN a r haN
    rw [hzero] at hcoeff
    exact hcoeff (by simp)
  have hsubset : S ⊆ A ∪ B := by
    intro t ht
    have hzero : iteratedDeriv (2 * r) f (t : ℝ) = 0 :=
      putnam_2000_b3_zero_of_mem_support
        N hN a f mult haN hf hmult (k := 2 * r) (by simpa [S] using ht)
    have heval := putnam_2000_b3_evenPoly_eval N a f hf r (t : ℝ)
    rw [hzero] at heval
    rcases mul_eq_zero.mp heval with hsin | hpoly
    · exact Finset.mem_union.mpr (Or.inl (by simpa [A, ht] using hsin))
    · exact Finset.mem_union.mpr (Or.inr (by simpa [B, P, ht, Polynomial.IsRoot] using hpoly))
  have hA : A.card ≤ 2 := by
    apply putnam_2000_b3_sin_zero_card_le_two
    intro t ht
    exact (Finset.mem_filter.mp ht).2
  have hrootB : ∀ t ∈ B,
      P.IsRoot (Real.cos (2 * Real.pi * (t : ℝ))) := by
    intro t ht
    exact (Finset.mem_filter.mp ht).2
  have hBpre : B.card ≤ 2 * P.roots.toFinset.card :=
    putnam_2000_b3_cos_preimage_roots_card_le P hP B hrootB
  have hrootcard₁ : P.roots.toFinset.card ≤ Multiset.card P.roots :=
    Multiset.toFinset_card_le P.roots
  have hrootcard₂ : Multiset.card P.roots ≤ P.natDegree :=
    Polynomial.card_roots' P
  have hroots : P.roots.toFinset.card ≤ N - 1 :=
    (hrootcard₁.trans hrootcard₂).trans
      (by simpa [P] using putnam_2000_b3_evenPoly_natDegree_le N a r)
  have hS : S.card ≤ A.card + B.card := by
    calc
      S.card ≤ (A ∪ B).card := Finset.card_le_card hsubset
      _ ≤ A.card + B.card := Finset.card_union_le A B
  omega

private lemma putnam_2000_b3_eventually_odd_support_card_ge
    (N : ℕ) (hN : N > 0) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
    (mult : (ℝ → ℝ) → ℝ → ℕ)
    (haN : a (putnam_2000_b3_top N hN) ≠ 0)
    (hf : ∀ t, f t = ∑ j : Icc 1 N,
      a j * Real.sin (2 * Real.pi * j * t))
    (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ,
      (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
        (iteratedDeriv (mult g t) g t ≠ 0 ∧
          ∀ k < (mult g t), iteratedDeriv k g t = 0)) :
    ∀ᶠ r in atTop,
      2 * N ≤
        ((putnam_2000_b3_mult_support_finite
          N hN a f mult haN hf hmult (2 * r + 1)).toFinset).card := by
  classical
  have hsign_event :=
    putnam_2000_b3_odd_endpoint_sign_eventually N hN a f haN hf
  filter_upwards [hsign_event] with r hsign
  let S := (putnam_2000_b3_mult_support_finite
      N hN a f mult haN hf hmult (2 * r + 1)).toFinset
  have hzero_interval :
      ∀ m ∈ Finset.range (2 * N),
        ∃ t : Ico (0 : ℝ) 1, t ∈ S ∧
          (m : ℝ) / (2 * (N : ℝ)) < (t : ℝ) ∧
          (t : ℝ) < ((m + 1 : ℕ) : ℝ) / (2 * (N : ℝ)) := by
    intro m hm
    have hm_lt : m < 2 * N := Finset.mem_range.mp hm
    let x : ℝ := (m : ℝ) / (2 * (N : ℝ))
    let y : ℝ := ((m + 1 : ℕ) : ℝ) / (2 * (N : ℝ))
    have hdenpos : 0 < 2 * (N : ℝ) := by positivity
    have hxy : x < y := by
      have hmxy : (m : ℝ) < ((m + 1 : ℕ) : ℝ) := by norm_num
      exact div_lt_div_of_pos_right hmxy hdenpos
    have hm_left : m ∈ Finset.range (2 * N + 1) := by
      exact Finset.mem_range.mpr (by omega)
    have hm_right : m + 1 ∈ Finset.range (2 * N + 1) := by
      exact Finset.mem_range.mpr (by omega)
    let s : ℝ :=
      (-1 : ℝ) ^ r * (-1 : ℝ) ^ m *
        a (putnam_2000_b3_top N hN)
    have hxpos :
        0 < s * iteratedDeriv (2 * r + 1) f x := by
      simpa [s, x] using hsign m hm_left
    have hyneg :
        s * iteratedDeriv (2 * r + 1) f y < 0 := by
      have hcoef :
          ((-1 : ℝ) ^ r * (-1 : ℝ) ^ (m + 1) *
              a (putnam_2000_b3_top N hN)) = -s := by
        simp [s, pow_succ]
      have hypos :
          0 < (-s) * iteratedDeriv (2 * r + 1) f y := by
        simpa [y, hcoef] using hsign (m + 1) hm_right
      nlinarith
    have hs_ne : s ≠ 0 := by
      dsimp [s]
      exact mul_ne_zero
        (mul_ne_zero (pow_ne_zero _ (by norm_num))
          (pow_ne_zero _ (by norm_num))) haN
    let G : ℝ → ℝ := fun z => s * iteratedDeriv (2 * r + 1) f z
    have hcontG : ContinuousOn G (Icc x y) := by
      dsimp [G]
      exact (continuous_const.mul
        (putnam_2000_b3_continuous_iteratedDeriv N a f hf
          (2 * r + 1))).continuousOn
    have hzero_between : (0 : ℝ) ∈ Ioo (G y) (G x) := by
      exact ⟨by simpa [G] using hyneg, by simpa [G] using hxpos⟩
    rcases intermediate_value_Ioo' (le_of_lt hxy) hcontG hzero_between with
      ⟨z, hzI, hzG⟩
    have hzD : iteratedDeriv (2 * r + 1) f z = 0 := by
      have hzG' : s * iteratedDeriv (2 * r + 1) f z = 0 := by
        simpa [G] using hzG
      exact (mul_eq_zero.mp hzG').resolve_left hs_ne
    have hx_nonneg : 0 ≤ x := by
      dsimp [x]
      exact div_nonneg (by positivity) hdenpos.le
    have hy_le_one : y ≤ 1 := by
      have hm1le : m + 1 ≤ 2 * N := by omega
      have hm1leR' :
          (((m + 1 : ℕ) : ℝ) : ℝ) ≤ (((2 * N : ℕ) : ℝ) : ℝ) := by
        exact_mod_cast hm1le
      have hm1leR : ((m + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
        simpa [Nat.cast_mul] using hm1leR'
      have hdiv :
          ((m + 1 : ℕ) : ℝ) / (2 * (N : ℝ)) ≤
            (2 * (N : ℝ)) / (2 * (N : ℝ)) :=
        div_le_div_of_nonneg_right hm1leR hdenpos.le
      have hden_ne : 2 * (N : ℝ) ≠ 0 := by positivity
      dsimp [y]
      calc
        ((m + 1 : ℕ) : ℝ) / (2 * (N : ℝ)) ≤
            (2 * (N : ℝ)) / (2 * (N : ℝ)) := hdiv
        _ = 1 := by field_simp [hden_ne]
    let t : Ico (0 : ℝ) 1 :=
      ⟨z, ⟨le_trans hx_nonneg (le_of_lt hzI.1),
        lt_of_lt_of_le hzI.2 hy_le_one⟩⟩
    have htS : t ∈ S := by
      exact putnam_2000_b3_mem_support_of_zero
        N hN a f mult haN hf hmult (k := 2 * r + 1) (t := t)
        (by simpa [t] using hzD)
    exact ⟨t, htS, by simpa [t, x] using hzI.1,
      by simpa [t, y] using hzI.2⟩
  let R := (Finset.range (2 * N)).attach
  let zpt : {m // m ∈ Finset.range (2 * N)} → Ico (0 : ℝ) 1 :=
    fun m => Classical.choose (hzero_interval m m.property)
  have hzpt :
      ∀ m : {m // m ∈ Finset.range (2 * N)},
        zpt m ∈ S ∧
          ((m : ℕ) : ℝ) / (2 * (N : ℝ)) < (zpt m : ℝ) ∧
          (zpt m : ℝ) < ((((m : ℕ) + 1 : ℕ) : ℝ)) / (2 * (N : ℝ)) := by
    intro m
    exact Classical.choose_spec (hzero_interval m m.property)
  have hmaps : Set.MapsTo zpt (R : Set {m // m ∈ Finset.range (2 * N)})
      (S : Set (Ico (0 : ℝ) 1)) := by
    intro m hm
    exact (hzpt m).1
  have hinj : Set.InjOn zpt (R : Set {m // m ∈ Finset.range (2 * N)}) := by
    intro p hp q hq hpq
    have hdenpos : 0 < 2 * (N : ℝ) := by positivity
    by_cases hpq_lt : (p : ℕ) < (q : ℕ)
    · have hsuccle : (p : ℕ) + 1 ≤ (q : ℕ) :=
        Nat.succ_le_of_lt hpq_lt
      have hsuccleR :
          (((p : ℕ) + 1 : ℕ) : ℝ) ≤ ((q : ℕ) : ℝ) := by
        exact_mod_cast hsuccle
      have hsep :
          (((p : ℕ) + 1 : ℕ) : ℝ) / (2 * (N : ℝ)) ≤
            ((q : ℕ) : ℝ) / (2 * (N : ℝ)) :=
        div_le_div_of_nonneg_right hsuccleR hdenpos.le
      have hp_upper := (hzpt p).2.2
      have hq_lower := (hzpt q).2.1
      have hreal : (zpt p : ℝ) = (zpt q : ℝ) := by
        simpa using congrArg (fun t : Ico (0 : ℝ) 1 => (t : ℝ)) hpq
      nlinarith
    · by_cases hqp_lt : (q : ℕ) < (p : ℕ)
      · have hsuccle : (q : ℕ) + 1 ≤ (p : ℕ) :=
          Nat.succ_le_of_lt hqp_lt
        have hsuccleR :
            (((q : ℕ) + 1 : ℕ) : ℝ) ≤ ((p : ℕ) : ℝ) := by
          exact_mod_cast hsuccle
        have hsep :
            (((q : ℕ) + 1 : ℕ) : ℝ) / (2 * (N : ℝ)) ≤
              ((p : ℕ) : ℝ) / (2 * (N : ℝ)) :=
          div_le_div_of_nonneg_right hsuccleR hdenpos.le
        have hq_upper := (hzpt q).2.2
        have hp_lower := (hzpt p).2.1
        have hreal : (zpt q : ℝ) = (zpt p : ℝ) := by
          simpa using congrArg (fun t : Ico (0 : ℝ) 1 => (t : ℝ)) hpq.symm
        nlinarith
      · apply Subtype.ext
        omega
  have hcard := Finset.card_le_card_of_injOn zpt hmaps hinj
  calc
    2 * N = (Finset.range (2 * N)).card := by simp
    _ = R.card := by simp [R]
    _ ≤ S.card := hcard

private lemma putnam_2000_b3_support_card_le_deriv_support_sdiff
    (N : ℕ) (hN : N > 0) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
    (mult : (ℝ → ℝ) → ℝ → ℕ)
    (haN : a (putnam_2000_b3_top N hN) ≠ 0)
    (hf : ∀ t, f t = ∑ j : Icc 1 N,
      a j * Real.sin (2 * Real.pi * j * t))
    (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ,
      (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
        (iteratedDeriv (mult g t) g t ≠ 0 ∧
          ∀ k < (mult g t), iteratedDeriv k g t = 0))
    (k : ℕ) :
    let S := (putnam_2000_b3_mult_support_finite
      N hN a f mult haN hf hmult k).toFinset
    let T := (putnam_2000_b3_mult_support_finite
      N hN a f mult haN hf hmult (k + 1)).toFinset
    S.card ≤ (T \ S).card := by
  classical
  intro S T
  by_cases hS : S.Nonempty
  · let xmin : Ico (0 : ℝ) 1 := S.min' hS
    let xmax : Ico (0 : ℝ) 1 := S.max' hS
    have hxmin : xmin ∈ S := S.min'_mem hS
    have hxmax : xmax ∈ S := S.max'_mem hS
    have hper :
        Function.Periodic (iteratedDeriv k f) 1 :=
      putnam_2000_b3_periodic_iteratedDeriv
        (putnam_2000_b3_periodic N a f hf) k
    have hperD :
        Function.Periodic (iteratedDeriv (k + 1) f) 1 :=
      putnam_2000_b3_periodic_iteratedDeriv
        (putnam_2000_b3_periodic N a f hf) (k + 1)
    have hxmax_zero : iteratedDeriv k f (xmax : ℝ) = 0 :=
      putnam_2000_b3_zero_of_mem_support
        N hN a f mult haN hf hmult (k := k) hxmax
    have hxmin_zero : iteratedDeriv k f (xmin : ℝ) = 0 :=
      putnam_2000_b3_zero_of_mem_support
        N hN a f mult haN hf hmult (k := k) hxmin
    have hwrap_lt : (xmax : ℝ) < (xmin : ℝ) + 1 := by
      have hx1 : (xmax : ℝ) < 1 := xmax.2.2
      have hx0 : 0 ≤ (xmin : ℝ) := xmin.2.1
      nlinarith
    have hwrap_eq :
        iteratedDeriv k f (xmax : ℝ) =
          iteratedDeriv k f ((xmin : ℝ) + 1) := by
      have hshift : iteratedDeriv k f ((xmin : ℝ) + 1) =
          iteratedDeriv k f (xmin : ℝ) := hper (xmin : ℝ)
      rw [hxmax_zero, hshift, hxmin_zero]
    obtain ⟨c, hcI, hcderiv⟩ :=
      exists_deriv_eq_zero hwrap_lt
        (putnam_2000_b3_continuous_iteratedDeriv N a f hf k).continuousOn
        hwrap_eq
    have hcD : iteratedDeriv (k + 1) f c = 0 := by
      simpa [iteratedDeriv_succ] using hcderiv
    obtain ⟨w, hwT, hwS, hwouter⟩ :
        ∃ w : Ico (0 : ℝ) 1, w ∈ T ∧ w ∉ S ∧
          ∀ x ∈ S, ∀ y ∈ S, x < y → w ∉ Ioo x y := by
      by_cases hc1 : c < 1
      · let w : Ico (0 : ℝ) 1 :=
          ⟨c, by
            constructor
            · exact le_trans xmax.2.1 (le_of_lt hcI.1)
            · exact hc1⟩
        have hwT : w ∈ T :=
          putnam_2000_b3_mem_deriv_support_of_zero
            N hN a f mult haN hf hmult (k := k) (t := w) (by simpa [w] using hcD)
        have hxw : xmax < w := by
          simpa [w] using hcI.1
        have hwS : w ∉ S := by
          intro hws
          exact (not_le_of_gt hxw) (S.le_max' w hws)
        have hwouter :
            ∀ x ∈ S, ∀ y ∈ S, x < y → w ∉ Ioo x y := by
          intro x hx y hy hxy hwy
          have hymax : y ≤ xmax := S.le_max' y hy
          exact (not_lt_of_ge (le_of_lt hxw)) (lt_of_lt_of_le hwy.2 hymax)
        exact ⟨w, hwT, hwS, hwouter⟩
      · have hcge : 1 ≤ c := le_of_not_gt hc1
        let w : Ico (0 : ℝ) 1 :=
          ⟨c - 1, by
            constructor
            · linarith
            · have hltmin : c - 1 < (xmin : ℝ) := by linarith [hcI.2]
              exact lt_trans hltmin xmin.2.2⟩
        have hwD : iteratedDeriv (k + 1) f (w : ℝ) = 0 := by
          have hp : iteratedDeriv (k + 1) f c =
              iteratedDeriv (k + 1) f (c - 1) := by
            simpa [sub_add_cancel] using hperD (c - 1)
          simpa [w] using hp.symm.trans hcD
        have hwT : w ∈ T :=
          putnam_2000_b3_mem_deriv_support_of_zero
            N hN a f mult haN hf hmult (k := k) (t := w) hwD
        have hwltmin : w < xmin := by
          change c - 1 < (xmin : ℝ)
          linarith [hcI.2]
        have hwS : w ∉ S := by
          intro hws
          exact (not_lt_of_ge (S.min'_le w hws)) hwltmin
        have hwouter :
            ∀ x ∈ S, ∀ y ∈ S, x < y → w ∉ Ioo x y := by
          intro x hx y hy hxy hwy
          have hminx : xmin ≤ x := S.min'_le x hx
          exact (not_lt_of_ge (le_trans (le_of_lt hwltmin) hminx)) hwy.1
        exact ⟨w, hwT, hwS, hwouter⟩
    have hwDiff : w ∈ T \ S := by
      exact Finset.mem_sdiff.mpr ⟨hwT, hwS⟩
    have hinter :
        S.card ≤ ((T \ S).erase w).card + 1 := by
      refine Finset.card_le_of_interleaved ?_
      intro x hx y hy hxy hconsec
      have hxzero : iteratedDeriv k f (x : ℝ) = 0 :=
        putnam_2000_b3_zero_of_mem_support
          N hN a f mult haN hf hmult (k := k) hx
      have hyzero : iteratedDeriv k f (y : ℝ) = 0 :=
        putnam_2000_b3_zero_of_mem_support
          N hN a f mult haN hf hmult (k := k) hy
      have hxyreal : (x : ℝ) < (y : ℝ) := hxy
      obtain ⟨z, hzI, hzderiv⟩ :=
        exists_deriv_eq_zero hxyreal
          (putnam_2000_b3_continuous_iteratedDeriv N a f hf k).continuousOn
          (by rw [hxzero, hyzero])
      let z' : Ico (0 : ℝ) 1 :=
        ⟨z, by
          constructor
          · exact le_trans x.2.1 (le_of_lt hzI.1)
          · exact lt_trans hzI.2 y.2.2⟩
      have hzD : iteratedDeriv (k + 1) f (z' : ℝ) = 0 := by
        simpa [z', iteratedDeriv_succ] using hzderiv
      have hzT : z' ∈ T :=
        putnam_2000_b3_mem_deriv_support_of_zero
          N hN a f mult haN hf hmult (k := k) (t := z') hzD
      have hzS : z' ∉ S := by
        intro hzS
        exact hconsec z' hzS (by simpa [z'] using hzI)
      have hzw : z' ≠ w := by
        intro hzw
        have hwI : w ∈ Ioo x y := by
          simpa [hzw] using (by simpa [z'] using hzI : z' ∈ Ioo x y)
        exact hwouter x hx y hy hxy hwI
      exact ⟨z', Finset.mem_erase.mpr
        ⟨hzw, Finset.mem_sdiff.mpr ⟨hzT, hzS⟩⟩,
        by simpa [z'] using hzI.1, by simpa [z'] using hzI.2⟩
    have herase : ((T \ S).erase w).card + 1 = (T \ S).card :=
      Finset.card_erase_add_one hwDiff
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    simp

private lemma putnam_2000_b3_M_le_M_succ
    (N : ℕ) (hN : N > 0) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
    (mult : (ℝ → ℝ) → ℝ → ℕ) (M : ℕ → ℕ)
    (haN : a (putnam_2000_b3_top N hN) ≠ 0)
    (hf : ∀ t, f t = ∑ j : Icc 1 N,
      a j * Real.sin (2 * Real.pi * j * t))
    (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ,
      (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
        (iteratedDeriv (mult g t) g t ≠ 0 ∧
          ∀ k < (mult g t), iteratedDeriv k g t = 0))
    (hM : ∀ k, M k = ∑' t : Ico (0 : ℝ) 1,
      mult (iteratedDeriv k f) t)
    (k : ℕ) :
    M k ≤ M (k + 1) := by
  classical
  let S := (putnam_2000_b3_mult_support_finite
      N hN a f mult haN hf hmult k).toFinset
  let T := (putnam_2000_b3_mult_support_finite
      N hN a f mult haN hf hmult (k + 1)).toFinset
  let F : Ico (0 : ℝ) 1 → ℕ :=
    fun t => mult (iteratedDeriv k f) t
  let D : Ico (0 : ℝ) 1 → ℕ :=
    fun t => mult (iteratedDeriv (k + 1) f) t
  have hMk :
      M k = ∑ t ∈ S, F t := by
    simpa [S, F] using
      putnam_2000_b3_M_eq_support_sum
        N hN a f mult M haN hf hmult hM k
  have hMsk :
      M (k + 1) = ∑ t ∈ T, D t := by
    simpa [T, D] using
      putnam_2000_b3_M_eq_support_sum
        N hN a f mult M haN hf hmult hM (k + 1)
  rw [hMk, hMsk]
  have hpoint : ∀ t ∈ S, F t ≤ D t + 1 := by
    intro t ht
    simpa [F, D] using
      putnam_2000_b3_mult_iteratedDeriv_le_succ
        N hN a f mult haN hf hmult k (t : ℝ)
  have hcard : S.card ≤ (T \ S).card := by
    simpa [S, T] using
      putnam_2000_b3_support_card_le_deriv_support_sdiff
        N hN a f mult haN hf hmult k
  have hTpos : ∀ t ∈ T \ S, 1 ≤ D t := by
    intro t ht
    have htT : t ∈ T := (Finset.mem_sdiff.mp ht).1
    have hne : D t ≠ 0 := by
      simpa [T, D] using
        (putnam_2000_b3_mult_support_finite
          N hN a f mult haN hf hmult (k + 1)).mem_toFinset.mp htT
    exact Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hne)
  have hS_inter :
      ∑ t ∈ S ∩ T, D t = ∑ t ∈ S, D t := by
    refine Finset.sum_subset (Finset.inter_subset_left) ?_
    intro t htS htNot
    have htT : t ∉ T := by
      intro htT
      exact htNot (Finset.mem_inter.mpr ⟨htS, htT⟩)
    have htSupport : t ∉ Function.support D := by
      intro htSupp
      exact htT (by
        simpa [T] using
          (putnam_2000_b3_mult_support_finite
          N hN a f mult haN hf hmult (k + 1)).mem_toFinset.mpr
            (by simpa [D] using htSupp))
    exact Function.notMem_support.mp htSupport
  have hdiff :
      T \ (S ∩ T) = T \ S := by
    ext t
    by_cases htT : t ∈ T <;> by_cases htS : t ∈ S <;> simp [htT, htS]
  have hpartition :
      ∑ t ∈ S, D t + ∑ t ∈ T \ S, D t = ∑ t ∈ T, D t := by
    have hpart := Finset.sum_sdiff
      (s₁ := S ∩ T) (s₂ := T) (f := D)
      (by intro t ht; exact (Finset.mem_inter.mp ht).2)
    calc
      ∑ t ∈ S, D t + ∑ t ∈ T \ S, D t
          = ∑ t ∈ S ∩ T, D t + ∑ t ∈ T \ S, D t := by
              rw [hS_inter]
      _ = ∑ t ∈ T \ S, D t + ∑ t ∈ S ∩ T, D t := by
              rw [add_comm]
      _ = ∑ t ∈ T, D t := by
              simpa [hdiff] using hpart
  calc
    ∑ t ∈ S, F t ≤ ∑ t ∈ S, (D t + 1) := by
      exact Finset.sum_le_sum fun t ht => hpoint t ht
    _ = ∑ t ∈ S, D t + S.card := by
      simp [Finset.sum_add_distrib]
    _ ≤ ∑ t ∈ S, D t + (T \ S).card := by
      exact Nat.add_le_add_left hcard _
    _ = ∑ t ∈ S, D t + ∑ t ∈ T \ S, 1 := by
      simp
    _ ≤ ∑ t ∈ S, D t + ∑ t ∈ T \ S, D t := by
      exact Nat.add_le_add_left
        (Finset.sum_le_sum fun t ht => hTpos t ht) _
    _ = ∑ t ∈ T, D t := hpartition

private lemma putnam_2000_b3_eventually_M_odd_eq
    (N : ℕ) (hN : N > 0) (a : Icc 1 N → ℝ) (f : ℝ → ℝ)
    (mult : (ℝ → ℝ) → ℝ → ℕ) (M : ℕ → ℕ)
    (haN : a (putnam_2000_b3_top N hN) ≠ 0)
    (hf : ∀ t, f t = ∑ j : Icc 1 N,
      a j * Real.sin (2 * Real.pi * j * t))
    (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ,
      (∃ c : ℕ, iteratedDeriv c g t ≠ 0) →
        (iteratedDeriv (mult g t) g t ≠ 0 ∧
          ∀ k < (mult g t), iteratedDeriv k g t = 0))
    (hM : ∀ k, M k = ∑' t : Ico (0 : ℝ) 1,
      mult (iteratedDeriv k f) t) :
    ∀ᶠ r in atTop, M (2 * r + 1) = 2 * N := by
  classical
  have hge_event :=
    putnam_2000_b3_eventually_odd_support_card_ge
      N hN a f mult haN hf hmult
  filter_upwards [hge_event] with r hSge
  let S := (putnam_2000_b3_mult_support_finite
      N hN a f mult haN hf hmult (2 * r + 1)).toFinset
  let T := (putnam_2000_b3_mult_support_finite
      N hN a f mult haN hf hmult (2 * r + 2)).toFinset
  let F : Ico (0 : ℝ) 1 → ℕ :=
    fun t => mult (iteratedDeriv (2 * r + 1) f) t
  let D : Ico (0 : ℝ) 1 → ℕ :=
    fun t => mult (iteratedDeriv (2 * r + 2) f) t
  have hSle : S.card ≤ 2 * N := by
    simpa [S] using
      putnam_2000_b3_odd_support_card_le
        N hN a f mult haN hf hmult r
  have hScard : S.card = 2 * N := le_antisymm hSle hSge
  have hTle : T.card ≤ 2 * N := by
    have h := putnam_2000_b3_even_support_card_le
      N hN a f mult haN hf hmult (r + 1)
    have hk : 2 * (r + 1) = 2 * r + 2 := by omega
    simpa [T, hk] using h
  have hcyclic : S.card ≤ (T \ S).card := by
    have h := putnam_2000_b3_support_card_le_deriv_support_sdiff
      N hN a f mult haN hf hmult (2 * r + 1)
    simpa [S, T, Nat.add_assoc] using h
  have hdiff_le_T : (T \ S).card ≤ T.card :=
    Finset.card_le_card Finset.sdiff_subset
  have hT_le_diff : T.card ≤ (T \ S).card := by omega
  have hdiff_eq_T : T \ S = T :=
    Finset.eq_of_subset_of_card_le Finset.sdiff_subset hT_le_diff
  have hFone : ∀ t ∈ S, F t = 1 := by
    intro t ht
    have hFne : F t ≠ 0 := by
      simpa [S, F] using
        (putnam_2000_b3_mult_support_finite
          N hN a f mult haN hf hmult (2 * r + 1)).mem_toFinset.mp ht
    have htNotT : t ∉ T := by
      intro htT
      have htDiff : t ∈ T \ S := by
        simpa [hdiff_eq_T] using htT
      exact (Finset.mem_sdiff.mp htDiff).2 ht
    have hD0 : D t = 0 := by
      by_contra hDne
      exact htNotT (by
        simpa [T, D] using
          (putnam_2000_b3_mult_support_finite
            N hN a f mult haN hf hmult (2 * r + 2)).mem_toFinset.mpr hDne)
    have hle : F t ≤ D t + 1 := by
      simpa [F, D, Nat.add_assoc] using
        putnam_2000_b3_mult_iteratedDeriv_le_succ
          N hN a f mult haN hf hmult (2 * r + 1) (t : ℝ)
    have hle1 : F t ≤ 1 := by
      simpa [hD0] using hle
    have hge1 : 1 ≤ F t :=
      Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hFne)
    exact le_antisymm hle1 hge1
  have hMval :
      M (2 * r + 1) = ∑ t ∈ S, F t := by
    simpa [S, F] using
      putnam_2000_b3_M_eq_support_sum
        N hN a f mult M haN hf hmult hM (2 * r + 1)
  calc
    M (2 * r + 1) = ∑ t ∈ S, F t := hMval
    _ = S.card := by
      calc
        ∑ t ∈ S, F t = ∑ t ∈ S, (1 : ℕ) := by
          apply Finset.sum_congr rfl
          intro t ht
          simp [hFone t ht]
        _ = S.card := by simp
    _ = 2 * N := hScard

/--
Let $f(t)=\sum_{j=1}^N a_j \sin(2\pi jt)$, where each $a_j$ is real and $a_N$ is not equal to $0$. Let $N_k$ denote the number of zeroes (including multiplicities) of $\frac{d^k f}{dt^k}$. Prove that
\[
N_0\leq N_1\leq N_2\leq \cdots \mbox{ and } \lim_{k\to\infty} N_k = 2N.
\]
-/
theorem putnam_2000_b3
  (N : ℕ) (hN : N > 0)
  (a : Icc 1 N → ℝ)
  (f : ℝ → ℝ)
  (mult : (ℝ → ℝ) → ℝ → ℕ)
  (M : ℕ → ℕ)
  (haN : a ⟨N, by simp; omega⟩ ≠ 0)
  (hf : ∀ t, f t = ∑ j : Icc 1 N, a j * Real.sin (2 * Real.pi * j * t))
  (hmult : ∀ g : ℝ → ℝ, ∀ t : ℝ, (∃ c : ℕ, iteratedDeriv c g t ≠ 0) → (iteratedDeriv (mult g t) g t ≠ 0 ∧ ∀ k < (mult g t), iteratedDeriv k g t = 0))
  (hM : ∀ k, M k = ∑' t : Ico (0 : ℝ) 1, mult (iteratedDeriv k f) t) :
  ((∀ i j : ℕ, i ≤ j → M i ≤ M j) ∧ Tendsto M atTop (𝓝 (2 * N))) := by
  classical
  have haNtop : a (putnam_2000_b3_top N hN) ≠ 0 := by
    simpa [putnam_2000_b3_top] using haN
  have hmono_succ : ∀ k, M k ≤ M (k + 1) := by
    intro k
    exact putnam_2000_b3_M_le_M_succ
      N hN a f mult M haNtop hf hmult hM k
  have hmono : ∀ i j : ℕ, i ≤ j → M i ≤ M j := by
    intro i j hij
    exact Nat.le_induction (m := i) (P := fun n _ => M i ≤ M n)
      (by exact le_rfl) (fun n hn ih => le_trans ih (hmono_succ n)) j hij
  have hodd_event :
      ∀ᶠ r in atTop, M (2 * r + 1) = 2 * N :=
    putnam_2000_b3_eventually_M_odd_eq
      N hN a f mult M haNtop hf hmult hM
  rw [Filter.eventually_atTop] at hodd_event
  rcases hodd_event with ⟨R, hR⟩
  have hevent_const : ∀ k ≥ 2 * R + 1, M k = 2 * N := by
    intro k hk
    have hlow : M (2 * R + 1) = 2 * N := hR R le_rfl
    have hhigh : M (2 * k + 1) = 2 * N := hR k (by omega)
    have hle_low : M (2 * R + 1) ≤ M k := hmono (2 * R + 1) k hk
    have hle_high : M k ≤ M (2 * k + 1) := hmono k (2 * k + 1) (by omega)
    omega
  exact ⟨hmono, tendsto_atTop_of_eventually_const hevent_const⟩
