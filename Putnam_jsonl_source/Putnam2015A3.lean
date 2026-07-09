import Mathlib

open Finset Polynomial

lemma putnam_2015_a3_prod_range_mul_periodic {M : Type*} [CommMonoid M] (f : ℕ → M)
    (d g : ℕ) (hper : ∀ k, f (k + d) = f k) :
    (∏ k ∈ Finset.range (g * d), f k) = (∏ k ∈ Finset.range d, f k) ^ g := by
  have hper_mul : ∀ t k, f (t * d + k) = f k := by
    intro t
    induction t with
    | zero =>
        intro k
        simp
    | succ t ih =>
        intro k
        rw [show (t + 1) * d + k = (t * d + k) + d by
          rw [Nat.succ_mul]
          omega]
        rw [hper, ih]
  induction g with
  | zero =>
      simp
  | succ g ih =>
      rw [show (g + 1) * d = g * d + d by
        rw [Nat.succ_mul, Nat.add_comm]]
      rw [Finset.prod_range_add, ih]
      have hblock : (∏ x ∈ Finset.range d, f (g * d + x)) = ∏ x ∈ Finset.range d, f x := by
        refine Finset.prod_congr rfl ?_
        intro x _hx
        exact hper_mul g x
      rw [hblock, pow_succ]

lemma putnam_2015_a3_prod_range_shift_one_of_pow_eq_one {R : Type*} [CommSemiring R]
    (μ : R) {d : ℕ} (hd : μ ^ d = 1) :
    (∏ k ∈ Finset.range d, (1 + μ ^ (k + 1))) = ∏ k ∈ Finset.range d, (1 + μ ^ k) := by
  cases d with
  | zero =>
      simp
  | succ n =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ']
      rw [hd]
      simp

lemma putnam_2015_a3_prod_one_add_powers_of_primitiveRoot {R : Type*} [CommRing R]
    [IsDomain R] {d : ℕ} {μ : R} (hμ : IsPrimitiveRoot μ d) (hodd : Odd d) :
    ∏ k ∈ Finset.range d, (1 + μ ^ k) = (2 : R) := by
  have hdpos : 0 < d := by
    rcases hodd with ⟨t, rfl⟩
    omega
  have hpoly := X_pow_sub_C_eq_prod hμ hdpos (one_pow d : (1 : R) ^ d = 1)
  have hprod_neg : (-1 : R) ^ d - 1 = ∏ i ∈ Finset.range d, ((-1 : R) - μ ^ i) := by
    simpa [Polynomial.eval_prod] using congrArg (Polynomial.eval (-1 : R)) hpoly
  let P : R := ∏ i ∈ Finset.range d, (1 + μ ^ i)
  have hprod_neg' : ∏ i ∈ Finset.range d, ((-1 : R) - μ ^ i) = (-1 : R) ^ d * P := by
    calc
      ∏ i ∈ Finset.range d, ((-1 : R) - μ ^ i)
          = ∏ i ∈ Finset.range d, ((-1 : R) * (1 + μ ^ i)) := by
              refine Finset.prod_congr rfl ?_
              intro i _hi
              ring
      _ = (∏ i ∈ Finset.range d, (-1 : R)) * ∏ i ∈ Finset.range d, (1 + μ ^ i) := by
              rw [Finset.prod_mul_distrib]
      _ = (-1 : R) ^ d * P := by
              simp [P]
  have hneg : -(2 : R) = -P := by
    calc
      -(2 : R) = (-1 : R) ^ d - 1 := by
        rw [hodd.neg_one_pow]
        ring
      _ = ∏ i ∈ Finset.range d, ((-1 : R) - μ ^ i) := hprod_neg
      _ = (-1 : R) ^ d * P := hprod_neg'
      _ = -P := by
        rw [hodd.neg_one_pow]
        ring
  change P = (2 : R)
  exact neg_injective hneg.symm

lemma putnam_2015_a3_primitiveRoot_row_product {R : Type*} [CommRing R] [IsDomain R]
    {n m : ℕ} {ζ : R} (hζ : IsPrimitiveRoot ζ n) (hnodd : Odd n) :
    (∏ b : Fin n, (1 + (ζ ^ m) ^ (b.1 + 1))) = (2 : R) ^ (m.gcd n) := by
  let g := m.gcd n
  let d := n / g
  let c := m / g
  have hnpos : 0 < n := by
    rcases hnodd with ⟨t, rfl⟩
    omega
  have hg_dvd_n : g ∣ n := Nat.gcd_dvd_right m n
  have hg_ne : g ≠ 0 := Nat.gcd_ne_zero_right (Nat.ne_of_gt hnpos)
  have hgd : g * d = n := by
    dsimp [g, d]
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_right m n)
  have hcop : c.Coprime d := by
    dsimp [c, d, g]
    exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right m hnpos)
  have hm_eq : m = g * c := by
    dsimp [g, c]
    exact (Nat.mul_div_cancel' (Nat.gcd_dvd_left m n)).symm
  have hprim_g : IsPrimitiveRoot (ζ ^ g) d := by
    dsimp [d]
    exact hζ.pow_of_dvd hg_ne hg_dvd_n
  have hμeq : ζ ^ m = (ζ ^ g) ^ c := by
    rw [hm_eq, pow_mul]
  have hprim_mu : IsPrimitiveRoot (ζ ^ m) d := by
    rw [hμeq]
    exact hprim_g.pow_of_coprime c hcop
  have hodd_d : Odd d := by
    exact Odd.of_dvd_nat hnodd (by dsimp [d]; exact Nat.div_dvd_of_dvd hg_dvd_n)
  let μ : R := ζ ^ m
  have hcycle : (∏ k ∈ Finset.range d, (1 + μ ^ (k + 1))) = (2 : R) := by
    calc
      (∏ k ∈ Finset.range d, (1 + μ ^ (k + 1)))
          = ∏ k ∈ Finset.range d, (1 + μ ^ k) := by
              exact putnam_2015_a3_prod_range_shift_one_of_pow_eq_one μ hprim_mu.pow_eq_one
      _ = (2 : R) := putnam_2015_a3_prod_one_add_powers_of_primitiveRoot hprim_mu hodd_d
  have hper : ∀ k, (1 + μ ^ (k + d + 1)) = (1 + μ ^ (k + 1)) := by
    intro k
    rw [show k + d + 1 = (k + 1) + d by omega]
    rw [pow_add, hprim_mu.pow_eq_one, mul_one]
  calc
    (∏ b : Fin n, (1 + (ζ ^ m) ^ (b.1 + 1)))
        = ∏ k ∈ Finset.range n, (1 + μ ^ (k + 1)) := by
            dsimp [μ]
            exact (Finset.prod_range (n := n)
              (f := fun k => (1 + (ζ ^ m) ^ (k + 1)))).symm
    _ = ∏ k ∈ Finset.range (g * d), (1 + μ ^ (k + 1)) := by rw [hgd]
    _ = (∏ k ∈ Finset.range d, (1 + μ ^ (k + 1))) ^ g := by
            exact putnam_2015_a3_prod_range_mul_periodic
              (fun k => (1 + μ ^ (k + 1))) d g hper
    _ = (2 : R) ^ (m.gcd n) := by
            rw [hcycle]

-- 13725
/--
Compute $\log_2 \left( \prod_{a=1}^{2015}\prod_{b=1}^{2015}(1+e^{2\pi iab/2015}) \right)$. Here $i$ is the imaginary unit (that is, $i^2=-1$).
-/
theorem putnam_2015_a3 :
    Complex.log (∏ a : Fin 2015, ∏ b : Fin 2015, (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015))) / Complex.log 2 = ((13725) : ℂ ) := by
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 2015)
  have hζ : IsPrimitiveRoot ζ 2015 := by
    dsimp [ζ]
    exact Complex.isPrimitiveRoot_exp 2015 (by norm_num)
  have hodd2015 : Odd 2015 := by
    norm_num
  have hterm (a b : Fin 2015) :
      Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015) =
        (ζ ^ (a.1 + 1)) ^ (b.1 + 1) := by
    dsimp [ζ]
    rw [← pow_mul]
    rw [← Complex.exp_nat_mul]
    congr 1
    norm_num
    ring_nf
  have hsum : (∑ a : Fin 2015, Nat.gcd (a.1 + 1) 2015) = 13725 := by
    set_option maxRecDepth 100000 in
    decide
  have hprod :
      (∏ a : Fin 2015, ∏ b : Fin 2015,
        (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015))) =
        (2 : ℂ) ^ 13725 := by
    calc
      (∏ a : Fin 2015, ∏ b : Fin 2015,
          (1 + Complex.exp (2 * Real.pi * Complex.I * (a.1 + 1) * (b.1 + 1) / 2015)))
          = ∏ a : Fin 2015, ∏ b : Fin 2015, (1 + (ζ ^ (a.1 + 1)) ^ (b.1 + 1)) := by
              refine Finset.prod_congr rfl ?_
              intro a _ha
              refine Finset.prod_congr rfl ?_
              intro b _hb
              rw [hterm a b]
      _ = ∏ a : Fin 2015, (2 : ℂ) ^ Nat.gcd (a.1 + 1) 2015 := by
              refine Finset.prod_congr rfl ?_
              intro a _ha
              exact putnam_2015_a3_primitiveRoot_row_product
                (R := ℂ) (n := 2015) (m := a.1 + 1) (ζ := ζ) hζ hodd2015
      _ = (2 : ℂ) ^ (∑ a : Fin 2015, Nat.gcd (a.1 + 1) 2015) := by
              simpa using
                (Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (Fin 2015))
                  (fun a => Nat.gcd (a.1 + 1) 2015) (2 : ℂ))
      _ = (2 : ℂ) ^ 13725 := by
              rw [hsum]
  have hlogpow : Complex.log ((2 : ℂ) ^ 13725) = (13725 : ℂ) * Complex.log 2 := by
    change Complex.log (((2 : ℝ) : ℂ) ^ 13725) = (13725 : ℂ) * Complex.log 2
    rw [← Complex.ofReal_pow]
    rw [← Complex.ofReal_log (by positivity : 0 ≤ (2 : ℝ) ^ 13725)]
    rw [Real.log_pow]
    norm_num [Complex.ofNat_log]
  have hlog2_ne : Complex.log 2 ≠ 0 := by
    rw [← Complex.ofNat_log (n := 2)]
    exact Complex.ofReal_ne_zero.mpr (Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num))
  rw [hprod, hlogpow]
  field_simp [hlog2_ne]
