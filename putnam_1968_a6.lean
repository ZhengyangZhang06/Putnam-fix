import Mathlib

open Finset Polynomial

abbrev putnam_1968_a6_solution : Set ℂ[X] :=
  {C (1 : ℂ) * X ^ 1 + C (1 : ℂ),
    C (1 : ℂ) * X ^ 1 + C (-1 : ℂ),
    C (-1 : ℂ) * X ^ 1 + C (1 : ℂ),
    C (-1 : ℂ) * X ^ 1 + C (-1 : ℂ),
    C (1 : ℂ) * X ^ 2 + C (1 : ℂ) * X ^ 1 + C (-1 : ℂ),
    C (1 : ℂ) * X ^ 2 + C (-1 : ℂ) * X ^ 1 + C (-1 : ℂ),
    C (-1 : ℂ) * X ^ 2 + C (1 : ℂ) * X ^ 1 + C (1 : ℂ),
    C (-1 : ℂ) * X ^ 2 + C (-1 : ℂ) * X ^ 1 + C (1 : ℂ),
    C (1 : ℂ) * X ^ 3 + C (1 : ℂ) * X ^ 2 + C (-1 : ℂ) * X ^ 1 + C (-1 : ℂ),
    C (1 : ℂ) * X ^ 3 + C (-1 : ℂ) * X ^ 2 + C (-1 : ℂ) * X ^ 1 + C (1 : ℂ),
    C (-1 : ℂ) * X ^ 3 + C (1 : ℂ) * X ^ 2 + C (1 : ℂ) * X ^ 1 + C (-1 : ℂ),
    C (-1 : ℂ) * X ^ 3 + C (-1 : ℂ) * X ^ 2 + C (1 : ℂ) * X ^ 1 + C (1 : ℂ)}

private lemma putnam_1968_a6_sum_sq_eq (s : Multiset ℂ) :
    (s.map (fun z => z ^ 2)).sum = s.sum ^ 2 - 2 * s.esymm 2 := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm]
  | cons a s ih =>
      simp [Multiset.esymm, Multiset.powersetCard_one, ih]
      rw [Multiset.sum_map_mul_left]
      simp
      ring

private lemma putnam_1968_a6_root_re (P : ℂ[X]) (hP0 : P ≠ 0)
    (hroot : ∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z) (x : P.roots) :
    (((x : ℂ).re : ℂ) = (x : ℂ)) := by
  have hxmem : (x : ℂ) ∈ P.roots := Multiset.coe_mem
  have hxzero : P.eval (x : ℂ) = 0 := (Polynomial.mem_roots hP0).mp hxmem
  rcases hroot (x : ℂ) hxzero with ⟨r, hr⟩
  rw [← hr]
  change ((r : ℂ).re : ℂ) = (r : ℂ)
  rw [Complex.ofReal_re]

private lemma putnam_1968_a6_roots_sum_sq (P : ℂ[X]) (hdeg : P.natDegree ≥ 1)
    (hcoeff : ∀ k ∈ Set.Icc 0 P.natDegree, P.coeff k = 1 ∨ P.coeff k = -1) :
    P.roots.sum ^ 2 = 1 := by
  classical
  let n := P.natDegree
  have hnpos : 0 < n := by omega
  have hsplit : P.Splits := IsAlgClosed.splits P
  have hlc_sign : P.leadingCoeff = 1 ∨ P.leadingCoeff = -1 := by
    have h := hcoeff P.natDegree (by simp)
    simpa [coeff_natDegree] using h
  have hlc_sq : P.leadingCoeff ^ 2 = 1 := by
    rcases hlc_sign with h | h <;> simp [h]
  have hnext_sign : P.nextCoeff = 1 ∨ P.nextCoeff = -1 := by
    have hm : n - 1 ∈ Set.Icc 0 P.natDegree := by simp [n]
    simpa [nextCoeff_of_natDegree_pos hnpos] using hcoeff (n - 1) hm
  have hnext_sq : P.nextCoeff ^ 2 = 1 := by
    rcases hnext_sign with h | h <;> simp [h]
  have hv := hsplit.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  have hsq : P.nextCoeff ^ 2 = P.roots.sum ^ 2 := by
    calc
      P.nextCoeff ^ 2 = (-P.leadingCoeff * P.roots.sum) ^ 2 := by rw [hv]
      _ = P.leadingCoeff ^ 2 * P.roots.sum ^ 2 := by ring
      _ = P.roots.sum ^ 2 := by rw [hlc_sq, one_mul]
  rw [hnext_sq] at hsq
  exact hsq.symm

private lemma putnam_1968_a6_esymm_two (P : ℂ[X]) (hdeg : 2 ≤ P.natDegree)
    (hcoeff : ∀ k ∈ Set.Icc 0 P.natDegree, P.coeff k = 1 ∨ P.coeff k = -1)
    (hroot : ∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z) :
    P.roots.esymm 2 = -1 := by
  classical
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  let n := P.natDegree
  have hdeg1 : P.natDegree ≥ 1 := by omega
  have hsplit : P.Splits := IsAlgClosed.splits P
  have hlc_sign : P.leadingCoeff = 1 ∨ P.leadingCoeff = -1 := by
    have h := hcoeff P.natDegree (by simp)
    simpa [coeff_natDegree] using h
  have hsum_sq : P.roots.sum ^ 2 = 1 :=
    putnam_1968_a6_roots_sum_sq P hdeg1 hcoeff
  have hcoeff2_sign := hcoeff (n - 2) (by simp [n])
  have hv2 := Polynomial.coeff_eq_esymm_roots_of_splits hsplit (k := n - 2) (by omega)
  have hdiff2 : P.natDegree - (n - 2) = 2 := by omega
  rw [hdiff2] at hv2
  norm_num at hv2
  have he2_sign : P.roots.esymm 2 = 1 ∨ P.roots.esymm 2 = -1 := by
    rcases hcoeff2_sign with hc | hc <;> rcases hlc_sign with hlc | hlc
    · left
      have htmp : (1 : ℂ) = P.roots.esymm 2 := by simpa [hc, hlc] using hv2
      exact htmp.symm
    · right
      have htmp : (1 : ℂ) = -P.roots.esymm 2 := by simpa [hc, hlc] using hv2
      rw [← neg_inj]
      simpa using htmp.symm
    · right
      have htmp : (-1 : ℂ) = P.roots.esymm 2 := by simpa [hc, hlc] using hv2
      exact htmp.symm
    · left
      have htmp : (-1 : ℂ) = -P.roots.esymm 2 := by simpa [hc, hlc] using hv2
      rw [← neg_inj]
      simpa using htmp.symm
  have hroot_re := putnam_1968_a6_root_re P hP0 hroot
  have hsumsqC_as_real :
      (P.roots.map (fun z => z ^ 2)).sum =
        ((∑ x : P.roots, (x : ℂ).re ^ 2 : ℝ) : ℂ) := by
    rw [← Multiset.map_univ P.roots (fun z => z ^ 2)]
    change (∑ x : P.roots, (x : ℂ) ^ 2) =
      ((∑ x : P.roots, (x : ℂ).re ^ 2 : ℝ) : ℂ)
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro x hx
    calc
      (x : ℂ) ^ 2 = (((x : ℂ).re : ℂ)) ^ 2 := by rw [hroot_re x]
      _ = (((x : ℂ).re ^ 2 : ℝ) : ℂ) := by rw [Complex.ofReal_pow]
  have hsq_nonneg : 0 ≤ ∑ x : P.roots, (x : ℂ).re ^ 2 :=
    Finset.sum_nonneg fun x hx => sq_nonneg _
  rcases he2_sign with he2pos | he2neg
  · have hbadC : ((∑ x : P.roots, (x : ℂ).re ^ 2 : ℝ) : ℂ) = (-1 : ℂ) := by
      rw [← hsumsqC_as_real, putnam_1968_a6_sum_sq_eq, hsum_sq, he2pos]
      norm_num
    have hbadC' : ((∑ x : P.roots, (x : ℂ).re ^ 2 : ℝ) : ℂ) =
        ((-1 : ℝ) : ℂ) := by
      simpa using hbadC
    have hbadR : (∑ x : P.roots, (x : ℂ).re ^ 2 : ℝ) = -1 :=
      Complex.ofReal_injective hbadC'
    nlinarith
  · exact he2neg

private lemma putnam_1968_a6_sum_re_sq (P : ℂ[X]) (hdeg : 2 ≤ P.natDegree)
    (hcoeff : ∀ k ∈ Set.Icc 0 P.natDegree, P.coeff k = 1 ∨ P.coeff k = -1)
    (hroot : ∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z) :
    (∑ x : P.roots, (x : ℂ).re ^ 2 : ℝ) = 3 := by
  classical
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hdeg1 : P.natDegree ≥ 1 := by omega
  have hsum_sq : P.roots.sum ^ 2 = 1 :=
    putnam_1968_a6_roots_sum_sq P hdeg1 hcoeff
  have he2 : P.roots.esymm 2 = -1 :=
    putnam_1968_a6_esymm_two P hdeg hcoeff hroot
  have hroot_re := putnam_1968_a6_root_re P hP0 hroot
  have hsumsqC_as_real :
      (P.roots.map (fun z => z ^ 2)).sum =
        ((∑ x : P.roots, (x : ℂ).re ^ 2 : ℝ) : ℂ) := by
    rw [← Multiset.map_univ P.roots (fun z => z ^ 2)]
    change (∑ x : P.roots, (x : ℂ) ^ 2) =
      ((∑ x : P.roots, (x : ℂ).re ^ 2 : ℝ) : ℂ)
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro x hx
    calc
      (x : ℂ) ^ 2 = (((x : ℂ).re : ℂ)) ^ 2 := by rw [hroot_re x]
      _ = (((x : ℂ).re ^ 2 : ℝ) : ℂ) := by rw [Complex.ofReal_pow]
  apply Complex.ofReal_injective
  rw [← hsumsqC_as_real, putnam_1968_a6_sum_sq_eq, hsum_sq, he2]
  norm_num

private lemma putnam_1968_a6_prod_re_sq (P : ℂ[X]) (hdeg : P.natDegree ≥ 1)
    (hcoeff : ∀ k ∈ Set.Icc 0 P.natDegree, P.coeff k = 1 ∨ P.coeff k = -1)
    (hroot : ∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z) :
    (∏ x : P.roots, (x : ℂ).re ^ 2 : ℝ) = 1 := by
  classical
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hsplit : P.Splits := IsAlgClosed.splits P
  have hlc_sign : P.leadingCoeff = 1 ∨ P.leadingCoeff = -1 := by
    have h := hcoeff P.natDegree (by simp)
    simpa [coeff_natDegree] using h
  have hlc_norm : Complex.normSq P.leadingCoeff = 1 := by
    rcases hlc_sign with h | h <;> simp [h]
  have hroot_re := putnam_1968_a6_root_re P hP0 hroot
  have hprod_norm : ∏ x : P.roots, Complex.normSq (x : ℂ) = 1 := by
    have hconst_sign := hcoeff 0 (by simp)
    have hconst_norm : Complex.normSq (P.coeff 0) = 1 := by
      rcases hconst_sign with h | h <;> simp [h]
    have hv0 := hsplit.coeff_zero_eq_leadingCoeff_mul_prod_roots
    have hnorm := congrArg Complex.normSq hv0
    rw [Complex.normSq_mul, Complex.normSq_mul] at hnorm
    have hnegpow : Complex.normSq ((-1 : ℂ) ^ P.natDegree) = 1 := by
      rw [map_pow, Complex.normSq_neg, Complex.normSq_one, one_pow]
    have hprodnorm : Complex.normSq P.roots.prod = 1 := by
      have htmp : (1 : ℝ) = Complex.normSq P.roots.prod := by
        simpa [hconst_norm, hnegpow, hlc_norm] using hnorm
      exact htmp.symm
    rw [← map_prod Complex.normSq (fun x : P.roots => (x : ℂ)) Finset.univ]
    rw [← Multiset.prod_eq_prod_coe P.roots]
    exact hprodnorm
  rw [← hprod_norm]
  apply Finset.prod_congr rfl
  intro x hx
  calc
    (x : ℂ).re ^ 2 = Complex.normSq (((x : ℂ).re : ℂ)) := by
      rw [Complex.normSq_ofReal]
      ring
    _ = Complex.normSq (x : ℂ) := by rw [hroot_re x]

private lemma putnam_1968_a6_degree_le_three (P : ℂ[X])
    (hdeg : P.natDegree ≥ 1)
    (hcoeff : ∀ k ∈ Set.Icc 0 P.natDegree, P.coeff k = 1 ∨ P.coeff k = -1)
    (hroot : ∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z) :
    P.natDegree ≤ 3 := by
  classical
  by_cases hn2 : 2 ≤ P.natDegree
  · have hsumsqR := putnam_1968_a6_sum_re_sq P hn2 hcoeff hroot
    have hprodR := putnam_1968_a6_prod_re_sq P hdeg hcoeff hroot
    have hsplit : P.Splits := IsAlgClosed.splits P
    have hcard : Fintype.card P.roots = P.natDegree := by
      rw [Multiset.card_coe, ← hsplit.natDegree_eq_card_roots]
    have hcardposR : (0 : ℝ) < Fintype.card P.roots := by
      rw [hcard]
      exact_mod_cast hdeg
    have hamgm : (1 : ℝ) ≤ 3 / (Fintype.card P.roots : ℝ) := by
      have h := Real.geom_mean_le_arith_mean (Finset.univ : Finset P.roots) (fun _ => (1 : ℝ))
        (fun x => (x : ℂ).re ^ 2) (by intro i hi; positivity) (by simpa using hcardposR)
        (by intro i hi; exact sq_nonneg _)
      simpa [hprodR, hsumsqR] using h
    rw [hcard] at hamgm
    have hnposR : (0 : ℝ) < (P.natDegree : ℝ) := by exact_mod_cast hdeg
    have hleR : (P.natDegree : ℝ) ≤ 3 := by
      have hmul := mul_le_mul_of_nonneg_right hamgm (le_of_lt hnposR)
      field_simp [ne_of_gt hnposR] at hmul
      linarith
    exact_mod_cast hleR
  · omega

private lemma putnam_1968_a6_cubic_const (P : ℂ[X]) (hdeg3 : P.natDegree = 3)
    (hcoeff : ∀ k ∈ Set.Icc 0 P.natDegree, P.coeff k = 1 ∨ P.coeff k = -1)
    (hroot : ∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z) :
    P.coeff 0 = -P.coeff 2 := by
  classical
  have hdeg1 : P.natDegree ≥ 1 := by omega
  have hdeg2 : 2 ≤ P.natDegree := by omega
  have hsplit : P.Splits := IsAlgClosed.splits P
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg3
    norm_num at hdeg3
  have hroot_re := putnam_1968_a6_root_re P hP0 hroot
  have he2 : P.roots.esymm 2 = -1 :=
    putnam_1968_a6_esymm_two P hdeg2 hcoeff hroot
  have hsumsqR := putnam_1968_a6_sum_re_sq P hdeg2 hcoeff hroot
  have hprodR := putnam_1968_a6_prod_re_sq P hdeg1 hcoeff hroot
  have hcard : Fintype.card P.roots = 3 := by
    rw [Multiset.card_coe, ← hsplit.natDegree_eq_card_roots, hdeg3]
  have hgeom : ∏ x : P.roots, ((x : ℂ).re ^ 2) ^ (1 / 3 : ℝ) = 1 := by
    rw [Real.finset_prod_rpow]
    · rw [hprodR]
      norm_num
    · intro i hi
      exact sq_nonneg _
  have harith : ∑ x : P.roots, (1 / 3 : ℝ) * ((x : ℂ).re ^ 2) = 1 := by
    rw [← Finset.mul_sum, hsumsqR]
    norm_num
  have hw' : ∑ x : P.roots, (1 / 3 : ℝ) = 1 := by
    simp [hcard]
  have hsquares : ∀ x : P.roots, (x : ℂ).re ^ 2 = 1 := by
    have hEq :
        ∏ x : P.roots, ((x : ℂ).re ^ 2) ^ (fun _ : P.roots => (1 / 3 : ℝ)) x =
          ∑ x : P.roots, (fun _ : P.roots => (1 / 3 : ℝ)) x * ((x : ℂ).re ^ 2) := by
      simpa using hgeom.trans harith.symm
    have hconst := (Real.geom_mean_eq_arith_mean_weighted_iff'
      (s := (Finset.univ : Finset P.roots))
      (w := fun _ : P.roots => (1 / 3 : ℝ))
      (z := fun x : P.roots => (x : ℂ).re ^ 2)
      (by intro i hi; norm_num) hw' (by intro i hi; exact sq_nonneg _)).mp hEq
    intro x
    have hx := hconst x (by simp)
    exact hx.trans harith
  have hsq_mem : ∀ z ∈ P.roots, z ^ 2 = 1 := by
    intro z hz
    let x : P.roots := ⟨z, ⟨0, Multiset.count_pos.mpr hz⟩⟩
    have hxreal := hroot_re x
    have hxsq := hsquares x
    calc
      z ^ 2 = (((z.re : ℝ) : ℂ)) ^ 2 := by
        change z ^ 2 = (((x : ℂ).re : ℂ)) ^ 2
        rw [hxreal]
      _ = ((z.re ^ 2 : ℝ) : ℂ) := by rw [Complex.ofReal_pow]
      _ = 1 := by
        change ((x : ℂ).re ^ 2 : ℝ) = 1 at hxsq
        rw [hxsq]
        norm_num
  have hroots_card : P.roots.card = 3 := by
    rw [← hsplit.natDegree_eq_card_roots, hdeg3]
  rcases Multiset.card_eq_three.mp hroots_card with ⟨x, y, z, hroots⟩
  have hx : x ^ 2 = 1 := hsq_mem x (by rw [hroots]; simp)
  have hy : y ^ 2 = 1 := hsq_mem y (by rw [hroots]; simp)
  have hz : z ^ 2 = 1 := hsq_mem z (by rw [hroots]; simp)
  have he2xyz : x * y + x * z + y * z = -1 := by
    simpa [hroots, Multiset.esymm, Multiset.powersetCard_one, add_assoc, add_comm,
      add_left_comm, mul_comm, mul_left_comm, mul_assoc] using he2
  have hprodxyz : x * y * z = -(x + y + z) := by
    have hprod_sum : x * y * z * (x * y + x * z + y * z) = x + y + z := by
      calc
        x * y * z * (x * y + x * z + y * z) =
            x ^ 2 * y ^ 2 * z + x ^ 2 * y * z ^ 2 + x * y ^ 2 * z ^ 2 := by ring
        _ = x + y + z := by rw [hx, hy, hz]; ring
    have hsum : x + y + z = -(x * y * z) := by
      calc
        x + y + z = x * y * z * (x * y + x * z + y * z) := hprod_sum.symm
        _ = x * y * z * (-1) := by rw [he2xyz]
        _ = -(x * y * z) := by ring
    rw [hsum]
    ring
  have hprod_sum_roots : P.roots.prod = -P.roots.sum := by
    rw [hroots]
    simpa [add_assoc, add_comm, add_left_comm, mul_assoc] using hprodxyz
  have hcoeff2 : P.coeff 2 = -P.leadingCoeff * P.roots.sum := by
    have hv := hsplit.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
    simpa [nextCoeff_of_natDegree_pos (by omega : 0 < P.natDegree), hdeg3] using hv
  have hv0 := hsplit.coeff_zero_eq_leadingCoeff_mul_prod_roots
  calc
    P.coeff 0 = (-1) ^ P.natDegree * P.leadingCoeff * P.roots.prod := hv0
    _ = P.leadingCoeff * P.roots.sum := by
      rw [hdeg3, hprod_sum_roots]
      norm_num
    _ = -P.coeff 2 := by
      rw [hcoeff2]
      ring

private lemma putnam_1968_a6_quad_add_real {z : ℂ} (hz : z ^ 2 + z - 1 = 0) :
    ∃ r : ℝ, r = z := by
  have him := congrArg Complex.im hz
  simp [Complex.mul_im, pow_two] at him
  have hre := congrArg Complex.re hz
  simp [Complex.mul_re, pow_two] at hre
  have hfac : z.im * (2 * z.re + 1) = 0 := by nlinarith
  have hz_im : z.im = 0 := by
    rcases mul_eq_zero.mp hfac with hzero | hlin
    · exact hzero
    · have hsq : z.im ^ 2 = -(5 / 4 : ℝ) := by nlinarith
      have hnonneg : 0 ≤ z.im ^ 2 := sq_nonneg z.im
      nlinarith
  use z.re
  apply Complex.ext <;> simp [hz_im]

private lemma putnam_1968_a6_quad_sub_real {z : ℂ} (hz : z ^ 2 - z - 1 = 0) :
    ∃ r : ℝ, r = z := by
  have him := congrArg Complex.im hz
  simp [Complex.sub_im, Complex.mul_im, pow_two] at him
  have hre := congrArg Complex.re hz
  simp [Complex.sub_re, Complex.mul_re, pow_two] at hre
  have hfac : z.im * (2 * z.re - 1) = 0 := by nlinarith
  have hz_im : z.im = 0 := by
    rcases mul_eq_zero.mp hfac with hzero | hlin
    · exact hzero
    · have hsq : z.im ^ 2 = -(5 / 4 : ℝ) := by nlinarith
      have hnonneg : 0 ≤ z.im ^ 2 := sq_nonneg z.im
      nlinarith
  use z.re
  apply Complex.ext <;> simp [hz_im]

private lemma putnam_1968_a6_cubic_minus_real {z : ℂ}
    (hz : eval z (X ^ 3 - X ^ 2 - X + 1 : ℂ[X]) = 0) :
    ∃ r : ℝ, r = z := by
  have hz' : z ^ 3 - z ^ 2 - z + 1 = 0 := by simpa [eval_pow] using hz
  have hfac : (z - 1) * (z - 1) * (z + 1) = 0 := by
    calc
      (z - 1) * (z - 1) * (z + 1) = z ^ 3 - z ^ 2 - z + 1 := by ring
      _ = 0 := hz'
  rcases mul_eq_zero.mp hfac with h | h
  · rcases mul_eq_zero.mp h with h1 | h1
    · use (1 : ℝ); exact (sub_eq_zero.mp h1).symm
    · use (1 : ℝ); exact (sub_eq_zero.mp h1).symm
  · have hzneg : z = (-1 : ℂ) := eq_neg_of_add_eq_zero_left h
    use (-1 : ℝ)
    rw [hzneg]
    norm_num

private lemma putnam_1968_a6_cubic_plus_real {z : ℂ}
    (hz : eval z (X ^ 3 + X ^ 2 - X - 1 : ℂ[X]) = 0) :
    ∃ r : ℝ, r = z := by
  have hz' : z ^ 3 + z ^ 2 - z - 1 = 0 := by simpa [eval_pow] using hz
  have hfac : (z + 1) * (z + 1) * (z - 1) = 0 := by
    calc
      (z + 1) * (z + 1) * (z - 1) = z ^ 3 + z ^ 2 - z - 1 := by ring
      _ = 0 := hz'
  rcases mul_eq_zero.mp hfac with h | h
  · rcases mul_eq_zero.mp h with h1 | h1
    · have hzneg : z = (-1 : ℂ) := eq_neg_of_add_eq_zero_left h1
      use (-1 : ℝ)
      rw [hzneg]
      norm_num
    · have hzneg : z = (-1 : ℂ) := eq_neg_of_add_eq_zero_left h1
      use (-1 : ℝ)
      rw [hzneg]
      norm_num
  · use (1 : ℝ); exact (sub_eq_zero.mp h).symm

private lemma putnam_1968_a6_mem_sol_1 :
    (X + 1 : ℂ[X]) ∈ putnam_1968_a6_solution := by
  rw [show (X + 1 : ℂ[X]) = C (1 : ℂ) * X ^ 1 + C (1 : ℂ) by
    ring_nf
    simp
    try ring]
  simp [putnam_1968_a6_solution]

private lemma putnam_1968_a6_mem_sol_2 :
    (-(X + 1) : ℂ[X]) ∈ putnam_1968_a6_solution := by
  rw [show (-(X + 1) : ℂ[X]) = C (-1 : ℂ) * X ^ 1 + C (-1 : ℂ) by
    ring_nf
    simp
    try ring]
  simp [putnam_1968_a6_solution]

private lemma putnam_1968_a6_mem_sol_3 :
    (X - 1 : ℂ[X]) ∈ putnam_1968_a6_solution := by
  rw [show (X - 1 : ℂ[X]) = C (1 : ℂ) * X ^ 1 + C (-1 : ℂ) by
    ring_nf
    simp
    try ring]
  simp [putnam_1968_a6_solution]

private lemma putnam_1968_a6_mem_sol_4 :
    (-(X - 1) : ℂ[X]) ∈ putnam_1968_a6_solution := by
  rw [show (-(X - 1) : ℂ[X]) = C (-1 : ℂ) * X ^ 1 + C (1 : ℂ) by
    ring_nf
    simp
    try ring]
  simp [putnam_1968_a6_solution]

private lemma putnam_1968_a6_mem_sol_5 :
    (X ^ 2 + X - 1 : ℂ[X]) ∈ putnam_1968_a6_solution := by
  rw [show (X ^ 2 + X - 1 : ℂ[X]) =
    C (1 : ℂ) * X ^ 2 + C (1 : ℂ) * X ^ 1 + C (-1 : ℂ) by
      ring_nf
      simp
      try ring]
  simp [putnam_1968_a6_solution]

private lemma putnam_1968_a6_mem_sol_6 :
    (-(X ^ 2 + X - 1) : ℂ[X]) ∈ putnam_1968_a6_solution := by
  rw [show (-(X ^ 2 + X - 1) : ℂ[X]) =
    C (-1 : ℂ) * X ^ 2 + C (-1 : ℂ) * X ^ 1 + C (1 : ℂ) by
      ring_nf
      simp
      try ring]
  simp [putnam_1968_a6_solution]

private lemma putnam_1968_a6_mem_sol_7 :
    (X ^ 2 - X - 1 : ℂ[X]) ∈ putnam_1968_a6_solution := by
  rw [show (X ^ 2 - X - 1 : ℂ[X]) =
    C (1 : ℂ) * X ^ 2 + C (-1 : ℂ) * X ^ 1 + C (-1 : ℂ) by
      ring_nf
      simp
      try ring]
  simp [putnam_1968_a6_solution]

private lemma putnam_1968_a6_mem_sol_8 :
    (-(X ^ 2 - X - 1) : ℂ[X]) ∈ putnam_1968_a6_solution := by
  rw [show (-(X ^ 2 - X - 1) : ℂ[X]) =
    C (-1 : ℂ) * X ^ 2 + C (1 : ℂ) * X ^ 1 + C (1 : ℂ) by
      ring_nf
      simp
      try ring]
  simp [putnam_1968_a6_solution]

private lemma putnam_1968_a6_mem_sol_9 :
    ((X + 1) ^ 2 * (X - 1) : ℂ[X]) ∈ putnam_1968_a6_solution := by
  rw [show ((X + 1) ^ 2 * (X - 1) : ℂ[X]) =
    C (1 : ℂ) * X ^ 3 + C (1 : ℂ) * X ^ 2 + C (-1 : ℂ) * X ^ 1 + C (-1 : ℂ) by
      ring_nf
      simp
      try ring]
  simp [putnam_1968_a6_solution]

private lemma putnam_1968_a6_mem_sol_10 :
    (-((X + 1) ^ 2 * (X - 1)) : ℂ[X]) ∈ putnam_1968_a6_solution := by
  rw [show (-((X + 1) ^ 2 * (X - 1)) : ℂ[X]) =
    C (-1 : ℂ) * X ^ 3 + C (-1 : ℂ) * X ^ 2 + C (1 : ℂ) * X ^ 1 + C (1 : ℂ) by
      ring_nf
      simp
      try ring]
  simp [putnam_1968_a6_solution]

private lemma putnam_1968_a6_mem_sol_11 :
    ((X - 1) ^ 2 * (X + 1) : ℂ[X]) ∈ putnam_1968_a6_solution := by
  rw [show ((X - 1) ^ 2 * (X + 1) : ℂ[X]) =
    C (1 : ℂ) * X ^ 3 + C (-1 : ℂ) * X ^ 2 + C (-1 : ℂ) * X ^ 1 + C (1 : ℂ) by
      ring_nf
      simp
      try ring]
  simp [putnam_1968_a6_solution]

private lemma putnam_1968_a6_mem_sol_12 :
    (-((X - 1) ^ 2 * (X + 1)) : ℂ[X]) ∈ putnam_1968_a6_solution := by
  rw [show (-((X - 1) ^ 2 * (X + 1)) : ℂ[X]) =
    C (-1 : ℂ) * X ^ 3 + C (1 : ℂ) * X ^ 2 + C (1 : ℂ) * X ^ 1 + C (-1 : ℂ) by
      ring_nf
      simp
      try ring]
  simp [putnam_1968_a6_solution]

private lemma putnam_1968_a6_lhs_mem_1 :
    (C (1 : ℂ) * X ^ 1 + C (1 : ℂ) : ℂ[X]) ∈
      {P : ℂ[X] | P.natDegree ≥ 1 ∧
        (∀ k ∈ Set.Icc 0 P.natDegree, P.coeff k = 1 ∨ P.coeff k = -1) ∧
        ∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z} := by
  have hnd : (C (1 : ℂ) * X ^ 1 + C (1 : ℂ) : ℂ[X]).natDegree = 1 := by
    compute_degree
    norm_num
  refine ⟨by rw [hnd], ?_, ?_⟩
  · intro k hk
    rw [hnd] at hk
    simp only [Set.mem_Icc] at hk
    have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with rfl | rfl <;> norm_num [coeff_X, coeff_one, coeff_C]
  · intro z hz
    use (-1 : ℝ)
    have hz' : z + 1 = 0 := by simpa [eval_pow] using hz
    have hzneg : z = (-1 : ℂ) := eq_neg_of_add_eq_zero_left hz'
    rw [hzneg]
    norm_num

private lemma putnam_1968_a6_lhs_mem_2 :
    (C (1 : ℂ) * X ^ 1 + C (-1 : ℂ) : ℂ[X]) ∈
      {P : ℂ[X] | P.natDegree ≥ 1 ∧
        (∀ k ∈ Set.Icc 0 P.natDegree, P.coeff k = 1 ∨ P.coeff k = -1) ∧
        ∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z} := by
  have hnd : (C (1 : ℂ) * X ^ 1 + C (-1 : ℂ) : ℂ[X]).natDegree = 1 := by
    compute_degree
    norm_num
  refine ⟨by rw [hnd], ?_, ?_⟩
  · intro k hk
    rw [hnd] at hk
    simp only [Set.mem_Icc] at hk
    have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with rfl | rfl <;> norm_num [coeff_X, coeff_one, coeff_C]
  · intro z hz
    use (1 : ℝ)
    have hz' : z - 1 = 0 := by simpa [eval_pow] using hz
    exact (sub_eq_zero.mp hz').symm

private lemma putnam_1968_a6_lhs_mem_3 :
    (C (-1 : ℂ) * X ^ 1 + C (1 : ℂ) : ℂ[X]) ∈
      {P : ℂ[X] | P.natDegree ≥ 1 ∧
        (∀ k ∈ Set.Icc 0 P.natDegree, P.coeff k = 1 ∨ P.coeff k = -1) ∧
        ∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z} := by
  have hnd : (C (-1 : ℂ) * X ^ 1 + C (1 : ℂ) : ℂ[X]).natDegree = 1 := by
    compute_degree
    norm_num
  refine ⟨by rw [hnd], ?_, ?_⟩
  · intro k hk
    rw [hnd] at hk
    simp only [Set.mem_Icc] at hk
    have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with rfl | rfl <;> norm_num [coeff_X, coeff_one, coeff_C]
  · intro z hz
    use (1 : ℝ)
    have hz' : -z + 1 = 0 := by simpa [eval_pow] using hz
    have hz1 : z = 1 := by linear_combination -hz'
    exact hz1.symm

private lemma putnam_1968_a6_lhs_mem_4 :
    (C (-1 : ℂ) * X ^ 1 + C (-1 : ℂ) : ℂ[X]) ∈
      {P : ℂ[X] | P.natDegree ≥ 1 ∧
        (∀ k ∈ Set.Icc 0 P.natDegree, P.coeff k = 1 ∨ P.coeff k = -1) ∧
        ∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z} := by
  have hnd : (C (-1 : ℂ) * X ^ 1 + C (-1 : ℂ) : ℂ[X]).natDegree = 1 := by
    compute_degree
    norm_num
  refine ⟨by rw [hnd], ?_, ?_⟩
  · intro k hk
    rw [hnd] at hk
    simp only [Set.mem_Icc] at hk
    have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with rfl | rfl <;> norm_num [coeff_X, coeff_one, coeff_C]
  · intro z hz
    use (-1 : ℝ)
    have hz' : -z - 1 = 0 := by simpa [eval_pow] using hz
    have hzneg : z = (-1 : ℂ) := by linear_combination -hz'
    rw [hzneg]
    norm_num

private lemma putnam_1968_a6_lhs_mem_5 :
    (C (1 : ℂ) * X ^ 2 + C (1 : ℂ) * X ^ 1 + C (-1 : ℂ) : ℂ[X]) ∈
      {P : ℂ[X] | P.natDegree ≥ 1 ∧
        (∀ k ∈ Set.Icc 0 P.natDegree, P.coeff k = 1 ∨ P.coeff k = -1) ∧
        ∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z} := by
  have hnd :
      (C (1 : ℂ) * X ^ 2 + C (1 : ℂ) * X ^ 1 + C (-1 : ℂ) : ℂ[X]).natDegree = 2 := by
    compute_degree <;> norm_num
  refine ⟨by rw [hnd]; norm_num, ?_, ?_⟩
  · intro k hk
    rw [hnd] at hk
    simp only [Set.mem_Icc] at hk
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk' with rfl | rfl | rfl <;> norm_num [coeff_X, coeff_one, coeff_C]
  · intro z hz
    apply putnam_1968_a6_quad_add_real
    simpa [eval_pow] using hz

private lemma putnam_1968_a6_lhs_mem_6 :
    (C (1 : ℂ) * X ^ 2 + C (-1 : ℂ) * X ^ 1 + C (-1 : ℂ) : ℂ[X]) ∈
      {P : ℂ[X] | P.natDegree ≥ 1 ∧
        (∀ k ∈ Set.Icc 0 P.natDegree, P.coeff k = 1 ∨ P.coeff k = -1) ∧
        ∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z} := by
  have hnd :
      (C (1 : ℂ) * X ^ 2 + C (-1 : ℂ) * X ^ 1 + C (-1 : ℂ) : ℂ[X]).natDegree = 2 := by
    compute_degree <;> norm_num
  refine ⟨by rw [hnd]; norm_num, ?_, ?_⟩
  · intro k hk
    rw [hnd] at hk
    simp only [Set.mem_Icc] at hk
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk' with rfl | rfl | rfl <;> norm_num [coeff_X, coeff_one, coeff_C]
  · intro z hz
    apply putnam_1968_a6_quad_sub_real
    simpa [eval_pow] using hz

private lemma putnam_1968_a6_lhs_mem_7 :
    (C (-1 : ℂ) * X ^ 2 + C (1 : ℂ) * X ^ 1 + C (1 : ℂ) : ℂ[X]) ∈
      {P : ℂ[X] | P.natDegree ≥ 1 ∧
        (∀ k ∈ Set.Icc 0 P.natDegree, P.coeff k = 1 ∨ P.coeff k = -1) ∧
        ∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z} := by
  have hnd :
      (C (-1 : ℂ) * X ^ 2 + C (1 : ℂ) * X ^ 1 + C (1 : ℂ) : ℂ[X]).natDegree = 2 := by
    compute_degree <;> norm_num
  refine ⟨by rw [hnd]; norm_num, ?_, ?_⟩
  · intro k hk
    rw [hnd] at hk
    simp only [Set.mem_Icc] at hk
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk' with rfl | rfl | rfl <;> norm_num [coeff_X, coeff_one, coeff_C]
  · intro z hz
    apply putnam_1968_a6_quad_sub_real
    have hzpoly : -z ^ 2 + z + 1 = 0 := by simpa [eval_pow] using hz
    linear_combination -hzpoly

private lemma putnam_1968_a6_lhs_mem_8 :
    (C (-1 : ℂ) * X ^ 2 + C (-1 : ℂ) * X ^ 1 + C (1 : ℂ) : ℂ[X]) ∈
      {P : ℂ[X] | P.natDegree ≥ 1 ∧
        (∀ k ∈ Set.Icc 0 P.natDegree, P.coeff k = 1 ∨ P.coeff k = -1) ∧
        ∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z} := by
  have hnd :
      (C (-1 : ℂ) * X ^ 2 + C (-1 : ℂ) * X ^ 1 + C (1 : ℂ) : ℂ[X]).natDegree = 2 := by
    compute_degree <;> norm_num
  refine ⟨by rw [hnd]; norm_num, ?_, ?_⟩
  · intro k hk
    rw [hnd] at hk
    simp only [Set.mem_Icc] at hk
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk' with rfl | rfl | rfl <;> norm_num [coeff_X, coeff_one, coeff_C]
  · intro z hz
    apply putnam_1968_a6_quad_add_real
    have hzpoly : -z ^ 2 - z + 1 = 0 := by simpa [eval_pow] using hz
    linear_combination -hzpoly

private lemma putnam_1968_a6_lhs_mem_9 :
    (C (1 : ℂ) * X ^ 3 + C (1 : ℂ) * X ^ 2 + C (-1 : ℂ) * X ^ 1 +
        C (-1 : ℂ) : ℂ[X]) ∈
      {P : ℂ[X] | P.natDegree ≥ 1 ∧
        (∀ k ∈ Set.Icc 0 P.natDegree, P.coeff k = 1 ∨ P.coeff k = -1) ∧
        ∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z} := by
  have hnd :
      (C (1 : ℂ) * X ^ 3 + C (1 : ℂ) * X ^ 2 + C (-1 : ℂ) * X ^ 1 +
          C (-1 : ℂ) : ℂ[X]).natDegree = 3 := by
    compute_degree <;> norm_num
  refine ⟨by rw [hnd]; norm_num, ?_, ?_⟩
  · intro k hk
    rw [hnd] at hk
    simp only [Set.mem_Icc] at hk
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk' with rfl | rfl | rfl | rfl <;> norm_num [coeff_X, coeff_one, coeff_C]
  · intro z hz
    apply putnam_1968_a6_cubic_plus_real
    simpa [eval_pow] using hz

private lemma putnam_1968_a6_lhs_mem_10 :
    (C (1 : ℂ) * X ^ 3 + C (-1 : ℂ) * X ^ 2 + C (-1 : ℂ) * X ^ 1 +
        C (1 : ℂ) : ℂ[X]) ∈
      {P : ℂ[X] | P.natDegree ≥ 1 ∧
        (∀ k ∈ Set.Icc 0 P.natDegree, P.coeff k = 1 ∨ P.coeff k = -1) ∧
        ∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z} := by
  have hnd :
      (C (1 : ℂ) * X ^ 3 + C (-1 : ℂ) * X ^ 2 + C (-1 : ℂ) * X ^ 1 +
          C (1 : ℂ) : ℂ[X]).natDegree = 3 := by
    compute_degree <;> norm_num
  refine ⟨by rw [hnd]; norm_num, ?_, ?_⟩
  · intro k hk
    rw [hnd] at hk
    simp only [Set.mem_Icc] at hk
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk' with rfl | rfl | rfl | rfl <;> norm_num [coeff_X, coeff_one, coeff_C]
  · intro z hz
    apply putnam_1968_a6_cubic_minus_real
    simpa [eval_pow] using hz

private lemma putnam_1968_a6_lhs_mem_11 :
    (C (-1 : ℂ) * X ^ 3 + C (1 : ℂ) * X ^ 2 + C (1 : ℂ) * X ^ 1 +
        C (-1 : ℂ) : ℂ[X]) ∈
      {P : ℂ[X] | P.natDegree ≥ 1 ∧
        (∀ k ∈ Set.Icc 0 P.natDegree, P.coeff k = 1 ∨ P.coeff k = -1) ∧
        ∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z} := by
  have hnd :
      (C (-1 : ℂ) * X ^ 3 + C (1 : ℂ) * X ^ 2 + C (1 : ℂ) * X ^ 1 +
          C (-1 : ℂ) : ℂ[X]).natDegree = 3 := by
    compute_degree <;> norm_num
  refine ⟨by rw [hnd]; norm_num, ?_, ?_⟩
  · intro k hk
    rw [hnd] at hk
    simp only [Set.mem_Icc] at hk
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk' with rfl | rfl | rfl | rfl <;> norm_num [coeff_X, coeff_one, coeff_C]
  · intro z hz
    apply putnam_1968_a6_cubic_minus_real
    have hzpoly : -z ^ 3 + z ^ 2 + z - 1 = 0 := by simpa [eval_pow] using hz
    have hzpos : z ^ 3 - z ^ 2 - z + 1 = 0 := by linear_combination -hzpoly
    simpa [eval_pow] using hzpos

private lemma putnam_1968_a6_lhs_mem_12 :
    (C (-1 : ℂ) * X ^ 3 + C (-1 : ℂ) * X ^ 2 + C (1 : ℂ) * X ^ 1 +
        C (1 : ℂ) : ℂ[X]) ∈
      {P : ℂ[X] | P.natDegree ≥ 1 ∧
        (∀ k ∈ Set.Icc 0 P.natDegree, P.coeff k = 1 ∨ P.coeff k = -1) ∧
        ∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z} := by
  have hnd :
      (C (-1 : ℂ) * X ^ 3 + C (-1 : ℂ) * X ^ 2 + C (1 : ℂ) * X ^ 1 +
          C (1 : ℂ) : ℂ[X]).natDegree = 3 := by
    compute_degree <;> norm_num
  refine ⟨by rw [hnd]; norm_num, ?_, ?_⟩
  · intro k hk
    rw [hnd] at hk
    simp only [Set.mem_Icc] at hk
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk' with rfl | rfl | rfl | rfl <;> norm_num [coeff_X, coeff_one, coeff_C]
  · intro z hz
    apply putnam_1968_a6_cubic_plus_real
    have hzpoly : -z ^ 3 - z ^ 2 + z + 1 = 0 := by simpa [eval_pow] using hz
    have hzpos : z ^ 3 + z ^ 2 - z - 1 = 0 := by linear_combination -hzpoly
    simpa [eval_pow] using hzpos

/--
Find all polynomials of the form $\sum_{0}^{n} a_{i} x^{n-i}$ with $n \ge 1$ and $a_i = \pm 1$ for all $0 \le i \le n$ whose roots are all real.
-/
theorem putnam_1968_a6
: {P : ℂ[X] | P.natDegree ≥ 1 ∧ (∀ k ∈ Set.Icc 0 P.natDegree, P.coeff k = 1 ∨ P.coeff k = -1) ∧
∀ z : ℂ, P.eval z = 0 → ∃ r : ℝ, r = z} = putnam_1968_a6_solution :=
by
  classical
  ext P
  constructor
  · intro hP
    rcases hP with ⟨hdeg, hcoeff, hroot⟩
    have hle3 := putnam_1968_a6_degree_le_three P hdeg hcoeff hroot
    interval_cases hnd : P.natDegree
    · have h0 := hcoeff 0 (by simp)
      have h1 := hcoeff 1 (by simp)
      rcases h1 with h1 | h1 <;> rcases h0 with h0 | h0
      · have hp : P = X + 1 := by
          apply (Polynomial.ext_iff_natDegree_le (by rw [hnd]) (by compute_degree)).2
          intro k hk
          interval_cases k <;> norm_num [h0, h1, coeff_X, coeff_one, coeff_C]
        rw [hp]
        exact putnam_1968_a6_mem_sol_1
      · have hp : P = X - 1 := by
          apply (Polynomial.ext_iff_natDegree_le (by rw [hnd]) (by compute_degree)).2
          intro k hk
          interval_cases k <;> norm_num [h0, h1, coeff_X, coeff_one, coeff_C]
        rw [hp]
        exact putnam_1968_a6_mem_sol_3
      · have hp : P = -X + 1 := by
          apply (Polynomial.ext_iff_natDegree_le (by rw [hnd]) (by compute_degree)).2
          intro k hk
          interval_cases k <;> norm_num [h0, h1, coeff_X, coeff_one, coeff_C]
        rw [hp]
        have hsame : (-X + 1 : ℂ[X]) = -(X - 1) := by ring
        rw [hsame]
        exact putnam_1968_a6_mem_sol_4
      · have hp : P = -X - 1 := by
          apply (Polynomial.ext_iff_natDegree_le (by rw [hnd]) (by compute_degree)).2
          intro k hk
          interval_cases k <;> norm_num [h0, h1, coeff_X, coeff_one, coeff_C]
        rw [hp]
        have hsame : (-X - 1 : ℂ[X]) = -(X + 1) := by ring
        rw [hsame]
        exact putnam_1968_a6_mem_sol_2
    · have hcoeffP : ∀ k ∈ Set.Icc 0 P.natDegree,
          P.coeff k = 1 ∨ P.coeff k = -1 := by
        simpa [hnd] using hcoeff
      have he2 := putnam_1968_a6_esymm_two P (by omega) hcoeffP hroot
      have hv2 := Polynomial.coeff_eq_esymm_roots_of_splits (IsAlgClosed.splits P) (k := 0)
        (by omega : 0 ≤ P.natDegree)
      have h02 : P.coeff 0 = -P.coeff 2 := by
        have hlc : P.coeff 2 = P.leadingCoeff := by
          simpa [hnd] using (coeff_natDegree (p := P))
        rw [hnd] at hv2
        norm_num at hv2
        calc
          P.coeff 0 = -P.leadingCoeff := by simpa [he2] using hv2
          _ = -P.coeff 2 := by rw [hlc]
      have h1s := hcoeff 1 (by simp)
      have h2s := hcoeff 2 (by simp)
      rcases h2s with h2 | h2 <;> rcases h1s with h1 | h1
      · have h0 : P.coeff 0 = -1 := by simpa [h2] using h02
        have hp : P = X ^ 2 + X - 1 := by
          apply (Polynomial.ext_iff_natDegree_le (by rw [hnd]) (by compute_degree)).2
          intro k hk
          interval_cases k <;> norm_num [h0, h1, h2, coeff_X, coeff_one, coeff_C]
        rw [hp]
        exact putnam_1968_a6_mem_sol_5
      · have h0 : P.coeff 0 = -1 := by simpa [h2] using h02
        have hp : P = X ^ 2 - X - 1 := by
          apply (Polynomial.ext_iff_natDegree_le (by rw [hnd]) (by compute_degree)).2
          intro k hk
          interval_cases k <;> norm_num [h0, h1, h2, coeff_X, coeff_one, coeff_C]
        rw [hp]
        exact putnam_1968_a6_mem_sol_7
      · have h0 : P.coeff 0 = 1 := by simpa [h2] using h02
        have hp : P = -X ^ 2 + X + 1 := by
          apply (Polynomial.ext_iff_natDegree_le (by rw [hnd]) (by compute_degree)).2
          intro k hk
          interval_cases k <;> norm_num [h0, h1, h2, coeff_X, coeff_one, coeff_C]
        rw [hp]
        have hsame : (-X ^ 2 + X + 1 : ℂ[X]) = -(X ^ 2 - X - 1) := by ring
        rw [hsame]
        exact putnam_1968_a6_mem_sol_8
      · have h0 : P.coeff 0 = 1 := by simpa [h2] using h02
        have hp : P = -X ^ 2 - X + 1 := by
          apply (Polynomial.ext_iff_natDegree_le (by rw [hnd]) (by compute_degree)).2
          intro k hk
          interval_cases k <;> norm_num [h0, h1, h2, coeff_X, coeff_one, coeff_C]
        rw [hp]
        have hsame : (-X ^ 2 - X + 1 : ℂ[X]) = -(X ^ 2 + X - 1) := by ring
        rw [hsame]
        exact putnam_1968_a6_mem_sol_6
    · have hcoeffP : ∀ k ∈ Set.Icc 0 P.natDegree,
          P.coeff k = 1 ∨ P.coeff k = -1 := by
        simpa [hnd] using hcoeff
      have he2 := putnam_1968_a6_esymm_two P (by omega) hcoeffP hroot
      have hv2 := Polynomial.coeff_eq_esymm_roots_of_splits (IsAlgClosed.splits P) (k := 1)
        (by omega : 1 ≤ P.natDegree)
      have h13 : P.coeff 1 = -P.coeff 3 := by
        have hlc : P.coeff 3 = P.leadingCoeff := by
          simpa [hnd] using (coeff_natDegree (p := P))
        rw [hnd] at hv2
        norm_num at hv2
        calc
          P.coeff 1 = -P.leadingCoeff := by simpa [he2] using hv2
          _ = -P.coeff 3 := by rw [hlc]
      have h02 := putnam_1968_a6_cubic_const P hnd hcoeffP hroot
      have h2s := hcoeff 2 (by simp)
      have h3s := hcoeff 3 (by simp)
      rcases h3s with h3 | h3 <;> rcases h2s with h2 | h2
      · have h1 : P.coeff 1 = -1 := by simpa [h3] using h13
        have h0 : P.coeff 0 = -1 := by simpa [h2] using h02
        have hp : P = X ^ 3 + X ^ 2 - X - 1 := by
          apply (Polynomial.ext_iff_natDegree_le (by rw [hnd]) (by compute_degree)).2
          intro k hk
          interval_cases k <;> norm_num [h0, h1, h2, h3, coeff_X, coeff_one, coeff_C]
        rw [hp]
        have hsame : (X ^ 3 + X ^ 2 - X - 1 : ℂ[X]) = (X + 1) ^ 2 * (X - 1) := by
          ring
        rw [hsame]
        exact putnam_1968_a6_mem_sol_9
      · have h1 : P.coeff 1 = -1 := by simpa [h3] using h13
        have h0 : P.coeff 0 = 1 := by simpa [h2] using h02
        have hp : P = X ^ 3 - X ^ 2 - X + 1 := by
          apply (Polynomial.ext_iff_natDegree_le (by rw [hnd]) (by compute_degree)).2
          intro k hk
          interval_cases k <;> norm_num [h0, h1, h2, h3, coeff_X, coeff_one, coeff_C]
        rw [hp]
        have hsame : (X ^ 3 - X ^ 2 - X + 1 : ℂ[X]) = (X - 1) ^ 2 * (X + 1) := by
          ring
        rw [hsame]
        exact putnam_1968_a6_mem_sol_11
      · have h1 : P.coeff 1 = 1 := by simpa [h3] using h13
        have h0 : P.coeff 0 = -1 := by simpa [h2] using h02
        have hp : P = -X ^ 3 + X ^ 2 + X - 1 := by
          apply (Polynomial.ext_iff_natDegree_le (by rw [hnd]) (by compute_degree)).2
          intro k hk
          interval_cases k <;> norm_num [h0, h1, h2, h3, coeff_X, coeff_one, coeff_C]
        rw [hp]
        have hsame : (-X ^ 3 + X ^ 2 + X - 1 : ℂ[X]) = -((X - 1) ^ 2 * (X + 1)) := by
          ring
        rw [hsame]
        exact putnam_1968_a6_mem_sol_12
      · have h1 : P.coeff 1 = 1 := by simpa [h3] using h13
        have h0 : P.coeff 0 = 1 := by simpa [h2] using h02
        have hp : P = -X ^ 3 - X ^ 2 + X + 1 := by
          apply (Polynomial.ext_iff_natDegree_le (by rw [hnd]) (by compute_degree)).2
          intro k hk
          interval_cases k <;> norm_num [h0, h1, h2, h3, coeff_X, coeff_one, coeff_C]
        rw [hp]
        have hsame : (-X ^ 3 - X ^ 2 + X + 1 : ℂ[X]) = -((X + 1) ^ 2 * (X - 1)) := by
          ring
        rw [hsame]
        exact putnam_1968_a6_mem_sol_10
  · intro hP
    simp only [putnam_1968_a6_solution] at hP
    rcases hP with hP | hP | hP | hP | hP | hP | hP | hP | hP | hP | hP | hP
    · rw [hP]
      exact putnam_1968_a6_lhs_mem_1
    · rw [hP]
      exact putnam_1968_a6_lhs_mem_2
    · rw [hP]
      exact putnam_1968_a6_lhs_mem_3
    · rw [hP]
      exact putnam_1968_a6_lhs_mem_4
    · rw [hP]
      exact putnam_1968_a6_lhs_mem_5
    · rw [hP]
      exact putnam_1968_a6_lhs_mem_6
    · rw [hP]
      exact putnam_1968_a6_lhs_mem_7
    · rw [hP]
      exact putnam_1968_a6_lhs_mem_8
    · rw [hP]
      exact putnam_1968_a6_lhs_mem_9
    · rw [hP]
      exact putnam_1968_a6_lhs_mem_10
    · rw [hP]
      exact putnam_1968_a6_lhs_mem_11
    · rw [hP]
      exact putnam_1968_a6_lhs_mem_12
