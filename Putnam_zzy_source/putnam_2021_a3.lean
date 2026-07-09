import Mathlib

open Filter Topology
open BigOperators

abbrev putnam_2021_a3_solution : Set ℕ :=
  {N | ∃ k : ℕ, 0 < k ∧ 3 * k ^ 2 = N}

private def putnam2021A3Point (x y z : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![x, y, z]

private def putnam2021A3Dot (x y : Fin 3 → ℤ) : ℤ :=
  ∑ i, x i * y i

private lemma putnam2021A3_norm_sq (p : EuclideanSpace ℝ (Fin 3)) :
    ‖p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 := by
  rw [EuclideanSpace.norm_eq]
  rw [Real.sq_sqrt]
  · simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  · positivity

private lemma putnam2021A3_inner_int
    (p q : EuclideanSpace ℝ (Fin 3)) (zp zq : Fin 3 → ℤ)
    (hp : ∀ i, p i = (zp i : ℝ)) (hq : ∀ i, q i = (zq i : ℝ)) :
    inner ℝ p q = ((putnam2021A3Dot zp zq : ℤ) : ℝ) := by
  rw [PiLp.inner_apply]
  simp [putnam2021A3Dot, RCLike.inner_apply, hp, hq, Fin.sum_univ_three, mul_comm]

private lemma putnam2021A3_inner_eq_of_dist_eq
    {x y u v : EuclideanSpace ℝ (Fin 3)} {R : ℝ}
    (hx : ‖x‖ ^ 2 = R) (hy : ‖y‖ ^ 2 = R)
    (hu : ‖u‖ ^ 2 = R) (hv : ‖v‖ ^ 2 = R)
    (hd : dist x y = dist u v) :
    inner ℝ x y = inner ℝ u v := by
  have hsq : ‖x - y‖ ^ 2 = ‖u - v‖ ^ 2 := by
    have := congrArg (fun t : ℝ => t ^ 2) hd
    simpa [dist_eq_norm] using this
  have h1 := norm_sub_sq_real x y
  have h2 := norm_sub_sq_real u v
  nlinarith

private lemma putnam2021A3_dot_comm (x y : Fin 3 → ℤ) :
    putnam2021A3Dot x y = putnam2021A3Dot y x := by
  simp [putnam2021A3Dot, Fin.sum_univ_three, mul_comm]

private lemma putnam2021A3_dot_sub_sub
    (a b c d : Fin 3 → ℤ) :
    putnam2021A3Dot (fun i => a i - b i) (fun i => c i - d i) =
      putnam2021A3Dot a c - putnam2021A3Dot a d -
        putnam2021A3Dot b c + putnam2021A3Dot b d := by
  simp [putnam2021A3Dot, Fin.sum_univ_three]
  ring

private lemma putnam2021A3_model_det (r : ℕ) :
    (Matrix.det
      (fun j k : Fin 3 => if j = k then (8 * (r : ℤ)) else (4 * (r : ℤ)))) =
      256 * (r : ℤ) ^ 3 := by
  rw [Matrix.det_fin_three]
  simp
  ring

private lemma putnam2021A3_nat_square_of_sq_eq_sq_mul_cube
    (d r c : ℕ) (hc : 0 < c) (h : d ^ 2 = c ^ 2 * r ^ 3) :
    ∃ k, r = k ^ 2 := by
  have hc2dvd : c ^ 2 ∣ d ^ 2 := by
    rw [h]
    exact dvd_mul_right _ _
  have hcd : c ∣ d := (Nat.pow_dvd_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hc2dvd
  rcases hcd with ⟨e, rfl⟩
  have hcancel : e ^ 2 = r ^ 3 := by
    have h1 : c ^ 2 * e ^ 2 = c ^ 2 * r ^ 3 := by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using h
    exact Nat.mul_left_cancel (pow_pos hc 2) h1
  have hpow : r ^ 3 = e ^ 2 := hcancel.symm
  obtain ⟨k, hk, _⟩ :=
    Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow
      (by decide : Nat.Coprime 3 2) hpow
  exact ⟨k, hk⟩

private lemma putnam2021A3_square_of_det_eq (d : ℤ) (r : ℕ)
    (h : d ^ 2 = (256 : ℤ) * (r : ℤ) ^ 3) :
    ∃ k, r = k ^ 2 := by
  have hnat : d.natAbs ^ 2 = 256 * r ^ 3 := by
    have := congrArg Int.natAbs h
    simpa [Int.natAbs_pow, Int.natAbs_mul, Int.natAbs_natCast] using this
  exact putnam2021A3_nat_square_of_sq_eq_sq_mul_cube d.natAbs r 16 (by norm_num) (by
    simpa using hnat)

private lemma putnam2021A3_round_neg_natCast (k : ℕ) :
    round (-(k : ℝ)) = -(k : ℤ) := by
  rw [show (-(k : ℝ)) = ((-(k : ℤ) : ℤ) : ℝ) by norm_num]
  exact round_intCast _

private lemma putnam2021A3_round_neg_intCast (k : ℤ) :
    round (-(k : ℝ)) = -k := by
  rw [show (-(k : ℝ)) = ((-k : ℤ) : ℝ) by norm_num]
  exact round_intCast _

/--
Determine all positive integers $N$ for which the sphere $x^2+y^2+z^2=N$ has an inscribed regular tetrahedron whose vertices have integer coordinates.
-/
theorem putnam_2021_a3
  (N : ℕ)
  (Nsphere : Set (EuclideanSpace ℝ (Fin 3)))
  (hNsphere : Nsphere = {p | (p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 = (N : ℝ)})
  (intcoords : (EuclideanSpace ℝ (Fin 3)) → Prop)
  (intcoords_def : ∀ p, intcoords p ↔ ∀ i : Fin 3, p i = round (p i)) :
  (0 < N ∧ ∃ A B C D : EuclideanSpace ℝ (Fin 3),
    A ∈ Nsphere ∧ B ∈ Nsphere ∧ C ∈ Nsphere ∧ D ∈ Nsphere ∧
    intcoords A ∧ intcoords B ∧ intcoords C ∧ intcoords D ∧
    (∃ s > 0, dist A B = s ∧ dist A C = s ∧ dist A D = s ∧ dist B C = s ∧ dist B D = s ∧ dist C D = s))
  ↔ N ∈ putnam_2021_a3_solution :=
by
  constructor
  · rintro ⟨hNpos, A, B, C, D, hA, hB, hC, hD,
      hAint, hBint, hCint, hDint, s, hspos,
      hABdist, hACdist, hADdist, hBCdist, hBDdist, hCDdist⟩
    have hAsphere : (A 0) ^ 2 + (A 1) ^ 2 + (A 2) ^ 2 = (N : ℝ) := by
      simpa [hNsphere] using hA
    have hBsphere : (B 0) ^ 2 + (B 1) ^ 2 + (B 2) ^ 2 = (N : ℝ) := by
      simpa [hNsphere] using hB
    have hCsphere : (C 0) ^ 2 + (C 1) ^ 2 + (C 2) ^ 2 = (N : ℝ) := by
      simpa [hNsphere] using hC
    have hDsphere : (D 0) ^ 2 + (D 1) ^ 2 + (D 2) ^ 2 = (N : ℝ) := by
      simpa [hNsphere] using hD
    have hAnorm : ‖A‖ ^ 2 = (N : ℝ) := by
      rw [putnam2021A3_norm_sq, hAsphere]
    have hBnorm : ‖B‖ ^ 2 = (N : ℝ) := by
      rw [putnam2021A3_norm_sq, hBsphere]
    have hCnorm : ‖C‖ ^ 2 = (N : ℝ) := by
      rw [putnam2021A3_norm_sq, hCsphere]
    have hDnorm : ‖D‖ ^ 2 = (N : ℝ) := by
      rw [putnam2021A3_norm_sq, hDsphere]
    have hAA : inner ℝ A A = (N : ℝ) := by
      rw [real_inner_self_eq_norm_sq, hAnorm]
    have hBB : inner ℝ B B = (N : ℝ) := by
      rw [real_inner_self_eq_norm_sq, hBnorm]
    have hCC : inner ℝ C C = (N : ℝ) := by
      rw [real_inner_self_eq_norm_sq, hCnorm]
    have hDD : inner ℝ D D = (N : ℝ) := by
      rw [real_inner_self_eq_norm_sq, hDnorm]
    let t : ℝ := inner ℝ A B
    have hAB : inner ℝ A B = t := rfl
    have hAC : inner ℝ A C = t :=
      putnam2021A3_inner_eq_of_dist_eq hAnorm hCnorm hAnorm hBnorm
        (hACdist.trans hABdist.symm)
    have hAD : inner ℝ A D = t :=
      putnam2021A3_inner_eq_of_dist_eq hAnorm hDnorm hAnorm hBnorm
        (hADdist.trans hABdist.symm)
    have hBC : inner ℝ B C = t :=
      putnam2021A3_inner_eq_of_dist_eq hBnorm hCnorm hAnorm hBnorm
        (hBCdist.trans hABdist.symm)
    have hBD : inner ℝ B D = t :=
      putnam2021A3_inner_eq_of_dist_eq hBnorm hDnorm hAnorm hBnorm
        (hBDdist.trans hABdist.symm)
    have hCD : inner ℝ C D = t :=
      putnam2021A3_inner_eq_of_dist_eq hCnorm hDnorm hAnorm hBnorm
        (hCDdist.trans hABdist.symm)
    have hBA : inner ℝ B A = t := by rw [real_inner_comm, hAB]
    have hCA : inner ℝ C A = t := by rw [real_inner_comm, hAC]
    have hDA : inner ℝ D A = t := by rw [real_inner_comm, hAD]
    have hCB : inner ℝ C B = t := by rw [real_inner_comm, hBC]
    have hDB : inner ℝ D B = t := by rw [real_inner_comm, hBD]
    have hDC : inner ℝ D C = t := by rw [real_inner_comm, hCD]
    let T : Fin 4 → EuclideanSpace ℝ (Fin 3) := ![A, B, C, D]
    have hnotli : ¬ LinearIndependent ℝ T := by
      intro hli
      have hc := hli.fintype_card_le_finrank
      norm_num [Module.finrank_fin_fun] at hc
    rcases (Fintype.not_linearIndependent_iff.mp hnotli) with ⟨g, hgrel, hgnz⟩
    have hgrel4 : g 0 • A + g 1 • B + g 2 • C + g 3 • D = 0 := by
      simpa [T, Fin.sum_univ_four] using hgrel
    have hdotA : g 0 * (N : ℝ) + g 1 * t + g 2 * t + g 3 * t = 0 := by
      have := congrArg (fun w => inner ℝ A w) hgrel4
      simpa [inner_add_right, real_inner_smul_right, hAnorm, hAB, hAC, hAD] using this
    have hdotB : g 0 * t + g 1 * (N : ℝ) + g 2 * t + g 3 * t = 0 := by
      have := congrArg (fun w => inner ℝ B w) hgrel4
      simpa [inner_add_right, real_inner_smul_right, hBA, hBnorm, hBC, hBD] using this
    have hdotC : g 0 * t + g 1 * t + g 2 * (N : ℝ) + g 3 * t = 0 := by
      have := congrArg (fun w => inner ℝ C w) hgrel4
      simpa [inner_add_right, real_inner_smul_right, hCA, hCB, hCnorm, hCD] using this
    have hdotD : g 0 * t + g 1 * t + g 2 * t + g 3 * (N : ℝ) = 0 := by
      have := congrArg (fun w => inner ℝ D w) hgrel4
      simpa [inner_add_right, real_inner_smul_right, hDA, hDB, hDC, hDnorm] using this
    have hNt : (N : ℝ) ≠ t := by
      intro hNt
      have hnormAB : ‖A - B‖ ^ 2 = 0 := by
        rw [norm_sub_sq_real, hAnorm, hBnorm, hAB, hNt]
        ring
      have hnormAB0 : ‖A - B‖ = 0 := sq_eq_zero_iff.mp hnormAB
      have hdistAB0 : dist A B = 0 := by
        simpa [dist_eq_norm] using hnormAB0
      nlinarith only [hdistAB0, hABdist, hspos]
    have hg01 : g 0 = g 1 := by
      have hmul : ((N : ℝ) - t) * (g 0 - g 1) = 0 := by
        nlinarith only [hdotA, hdotB]
      rcases mul_eq_zero.mp hmul with hleft | hright
      · exact False.elim (hNt (sub_eq_zero.mp hleft))
      · exact sub_eq_zero.mp hright
    have hg02 : g 0 = g 2 := by
      have hmul : ((N : ℝ) - t) * (g 0 - g 2) = 0 := by
        nlinarith only [hdotA, hdotC]
      rcases mul_eq_zero.mp hmul with hleft | hright
      · exact False.elim (hNt (sub_eq_zero.mp hleft))
      · exact sub_eq_zero.mp hright
    have hg03 : g 0 = g 3 := by
      have hmul : ((N : ℝ) - t) * (g 0 - g 3) = 0 := by
        nlinarith only [hdotA, hdotD]
      rcases mul_eq_zero.mp hmul with hleft | hright
      · exact False.elim (hNt (sub_eq_zero.mp hleft))
      · exact sub_eq_zero.mp hright
    have hg0nz : g 0 ≠ 0 := by
      rcases hgnz with ⟨i, hi⟩
      fin_cases i <;> simpa [← hg01, ← hg02, ← hg03] using hi
    have hN3t : (N : ℝ) + 3 * t = 0 := by
      have hdotA' : g 0 * (N : ℝ) + g 0 * t + g 0 * t + g 0 * t = 0 := by
        simpa [← hg01, ← hg02, ← hg03] using hdotA
      have hmul : g 0 * ((N : ℝ) + 3 * t) = 0 := by
        convert hdotA' using 1
        ring
      rcases mul_eq_zero.mp hmul with hleft | hright
      · exact False.elim (hg0nz hleft)
      · exact hright
    let zA : Fin 3 → ℤ := fun i => round (A i)
    let zB : Fin 3 → ℤ := fun i => round (B i)
    let zC : Fin 3 → ℤ := fun i => round (C i)
    let zD : Fin 3 → ℤ := fun i => round (D i)
    have hzA : ∀ i, A i = (zA i : ℝ) := by
      simpa [zA] using (intcoords_def A).1 hAint
    have hzB : ∀ i, B i = (zB i : ℝ) := by
      simpa [zB] using (intcoords_def B).1 hBint
    have hzC : ∀ i, C i = (zC i : ℝ) := by
      simpa [zC] using (intcoords_def C).1 hCint
    have hzD : ∀ i, D i = (zD i : ℝ) := by
      simpa [zD] using (intcoords_def D).1 hDint
    let tZ : ℤ := putnam2021A3Dot zA zB
    have htZcast : ((tZ : ℤ) : ℝ) = t := by
      simpa [tZ, t] using (putnam2021A3_inner_int A B zA zB hzA hzB).symm
    have hN3tZreal : (N : ℝ) + 3 * (tZ : ℝ) = 0 := by
      nlinarith only [hN3t, htZcast]
    have hN3tZ : (N : ℤ) + 3 * tZ = 0 := by
      exact_mod_cast hN3tZreal
    have h3dvd : (3 : ℕ) ∣ N := by
      rw [← Int.natCast_dvd_natCast]
      use -tZ
      omega
    rcases h3dvd with ⟨r, hr⟩
    have htZneg : tZ = -(r : ℤ) := by
      have hrZ : (N : ℤ) = 3 * (r : ℤ) := by exact_mod_cast hr
      omega
    have hAAZ : putnam2021A3Dot zA zA = (N : ℤ) := by
      have hreal : ((putnam2021A3Dot zA zA : ℤ) : ℝ) = (N : ℝ) := by
        rw [← putnam2021A3_inner_int A A zA zA hzA hzA, hAA]
      exact_mod_cast hreal
    have hBBZ : putnam2021A3Dot zB zB = (N : ℤ) := by
      have hreal : ((putnam2021A3Dot zB zB : ℤ) : ℝ) = (N : ℝ) := by
        rw [← putnam2021A3_inner_int B B zB zB hzB hzB, hBB]
      exact_mod_cast hreal
    have hCCZ : putnam2021A3Dot zC zC = (N : ℤ) := by
      have hreal : ((putnam2021A3Dot zC zC : ℤ) : ℝ) = (N : ℝ) := by
        rw [← putnam2021A3_inner_int C C zC zC hzC hzC, hCC]
      exact_mod_cast hreal
    have hDDZ : putnam2021A3Dot zD zD = (N : ℤ) := by
      have hreal : ((putnam2021A3Dot zD zD : ℤ) : ℝ) = (N : ℝ) := by
        rw [← putnam2021A3_inner_int D D zD zD hzD hzD, hDD]
      exact_mod_cast hreal
    have hdot_eq :
        ∀ (P Q : EuclideanSpace ℝ (Fin 3)) (zP zQ : Fin 3 → ℤ),
          (∀ i, P i = (zP i : ℝ)) → (∀ i, Q i = (zQ i : ℝ)) →
          inner ℝ P Q = t → putnam2021A3Dot zP zQ = tZ := by
      intro P Q zP zQ hzP hzQ hPQ
      have hreal : ((putnam2021A3Dot zP zQ : ℤ) : ℝ) = ((tZ : ℤ) : ℝ) := by
        calc
          ((putnam2021A3Dot zP zQ : ℤ) : ℝ) = inner ℝ P Q :=
            (putnam2021A3_inner_int P Q zP zQ hzP hzQ).symm
          _ = t := hPQ
          _ = ((tZ : ℤ) : ℝ) := htZcast.symm
      exact_mod_cast hreal
    have hABZ : putnam2021A3Dot zA zB = tZ := rfl
    have hACZ : putnam2021A3Dot zA zC = tZ :=
      hdot_eq A C zA zC hzA hzC hAC
    have hADZ : putnam2021A3Dot zA zD = tZ :=
      hdot_eq A D zA zD hzA hzD hAD
    have hBCZ : putnam2021A3Dot zB zC = tZ :=
      hdot_eq B C zB zC hzB hzC hBC
    have hBDZ : putnam2021A3Dot zB zD = tZ :=
      hdot_eq B D zB zD hzB hzD hBD
    have hCDZ : putnam2021A3Dot zC zD = tZ :=
      hdot_eq C D zC zD hzC hzD hCD
    let U : Fin 3 → ℤ := fun i => zA i - zD i
    let V : Fin 3 → ℤ := fun i => zB i - zD i
    let W : Fin 3 → ℤ := fun i => zC i - zD i
    have hUU : putnam2021A3Dot U U = 8 * (r : ℤ) := by
      change putnam2021A3Dot (fun i => zA i - zD i) (fun i => zA i - zD i) = 8 * (r : ℤ)
      rw [putnam2021A3_dot_sub_sub]
      rw [hAAZ, hADZ, putnam2021A3_dot_comm zD zA, hADZ, hDDZ]
      omega
    have hVV : putnam2021A3Dot V V = 8 * (r : ℤ) := by
      change putnam2021A3Dot (fun i => zB i - zD i) (fun i => zB i - zD i) = 8 * (r : ℤ)
      rw [putnam2021A3_dot_sub_sub]
      rw [hBBZ, hBDZ, putnam2021A3_dot_comm zD zB, hBDZ, hDDZ]
      omega
    have hWW : putnam2021A3Dot W W = 8 * (r : ℤ) := by
      change putnam2021A3Dot (fun i => zC i - zD i) (fun i => zC i - zD i) = 8 * (r : ℤ)
      rw [putnam2021A3_dot_sub_sub]
      rw [hCCZ, hCDZ, putnam2021A3_dot_comm zD zC, hCDZ, hDDZ]
      omega
    have hUV : putnam2021A3Dot U V = 4 * (r : ℤ) := by
      change putnam2021A3Dot (fun i => zA i - zD i) (fun i => zB i - zD i) = 4 * (r : ℤ)
      rw [putnam2021A3_dot_sub_sub]
      rw [hABZ, hADZ, putnam2021A3_dot_comm zD zB, hBDZ, hDDZ]
      omega
    have hUW : putnam2021A3Dot U W = 4 * (r : ℤ) := by
      change putnam2021A3Dot (fun i => zA i - zD i) (fun i => zC i - zD i) = 4 * (r : ℤ)
      rw [putnam2021A3_dot_sub_sub]
      rw [hACZ, hADZ, putnam2021A3_dot_comm zD zC, hCDZ, hDDZ]
      omega
    have hVW : putnam2021A3Dot V W = 4 * (r : ℤ) := by
      change putnam2021A3Dot (fun i => zB i - zD i) (fun i => zC i - zD i) = 4 * (r : ℤ)
      rw [putnam2021A3_dot_sub_sub]
      rw [hBCZ, hBDZ, putnam2021A3_dot_comm zD zC, hCDZ, hDDZ]
      omega
    have hVU : putnam2021A3Dot V U = 4 * (r : ℤ) := by
      rw [putnam2021A3_dot_comm, hUV]
    have hWU : putnam2021A3Dot W U = 4 * (r : ℤ) := by
      rw [putnam2021A3_dot_comm, hUW]
    have hWV : putnam2021A3Dot W V = 4 * (r : ℤ) := by
      rw [putnam2021A3_dot_comm, hVW]
    let M : Matrix (Fin 3) (Fin 3) ℤ := fun i j => ![U i, V i, W i] j
    have hgram :
        M.transpose * M =
          fun j k : Fin 3 => if j = k then (8 * (r : ℤ)) else (4 * (r : ℤ)) := by
      ext j k
      fin_cases j <;> fin_cases k
      · simpa [M, Matrix.mul_apply, putnam2021A3Dot] using hUU
      · simpa [M, Matrix.mul_apply, putnam2021A3Dot] using hUV
      · simpa [M, Matrix.mul_apply, putnam2021A3Dot] using hUW
      · simpa [M, Matrix.mul_apply, putnam2021A3Dot] using hVU
      · simpa [M, Matrix.mul_apply, putnam2021A3Dot] using hVV
      · simpa [M, Matrix.mul_apply, putnam2021A3Dot] using hVW
      · simpa [M, Matrix.mul_apply, putnam2021A3Dot] using hWU
      · simpa [M, Matrix.mul_apply, putnam2021A3Dot] using hWV
      · simpa [M, Matrix.mul_apply, putnam2021A3Dot] using hWW
    have hdetInt : M.det ^ 2 = (256 : ℤ) * (r : ℤ) ^ 3 := by
      calc
        M.det ^ 2 = (M.transpose * M).det := by
          rw [Matrix.det_mul, Matrix.det_transpose, pow_two]
        _ = (Matrix.det
              (fun j k : Fin 3 =>
                if j = k then (8 * (r : ℤ)) else (4 * (r : ℤ)))) := by
          rw [hgram]
        _ = 256 * (r : ℤ) ^ 3 := putnam2021A3_model_det r
    rcases putnam2021A3_square_of_det_eq M.det r hdetInt with ⟨k, hk⟩
    have hNnat : N = 3 * k ^ 2 := by
      rw [hr, hk]
    have hkne_nat : k ≠ 0 := by
      intro hk0
      have hN0 : N = 0 := by
        rw [hNnat, hk0]
        norm_num
      omega
    refine ⟨k, Nat.pos_of_ne_zero hkne_nat, hNnat.symm⟩
  · rintro ⟨k, hkpos, hNk⟩
    have hNnat : N = 3 * k ^ 2 := hNk.symm
    have hkne : k ≠ 0 := ne_of_gt hkpos
    have hNpos : 0 < N := by
      rw [hNnat]
      positivity
    have hkRne : (k : ℝ) ≠ 0 := by
      exact_mod_cast hkne
    have hNkR : (N : ℝ) = 3 * (k : ℝ) ^ 2 := by
      exact_mod_cast hNnat
    let A : EuclideanSpace ℝ (Fin 3) := putnam2021A3Point (k : ℝ) (k : ℝ) (k : ℝ)
    let B : EuclideanSpace ℝ (Fin 3) := putnam2021A3Point (k : ℝ) (-(k : ℝ)) (-(k : ℝ))
    let C : EuclideanSpace ℝ (Fin 3) := putnam2021A3Point (-(k : ℝ)) (k : ℝ) (-(k : ℝ))
    let D : EuclideanSpace ℝ (Fin 3) := putnam2021A3Point (-(k : ℝ)) (-(k : ℝ)) (k : ℝ)
    have hAmem : A ∈ Nsphere := by
      rw [hNsphere]
      simp [A, putnam2021A3Point]
      rw [hNkR]
      ring
    have hBmem : B ∈ Nsphere := by
      rw [hNsphere]
      simp [B, putnam2021A3Point]
      rw [hNkR]
      ring
    have hCmem : C ∈ Nsphere := by
      rw [hNsphere]
      simp [C, putnam2021A3Point]
      rw [hNkR]
      ring
    have hDmem : D ∈ Nsphere := by
      rw [hNsphere]
      simp [D, putnam2021A3Point]
      rw [hNkR]
      ring
    have hroundNeg : -(k : ℝ) = (round (-(k : ℝ)) : ℝ) := by
      rw [putnam2021A3_round_neg_natCast k]
      norm_num
    have hAint' : intcoords A := by
      rw [intcoords_def]
      intro i
      fin_cases i <;> simp [A, putnam2021A3Point]
    have hBint' : intcoords B := by
      rw [intcoords_def]
      intro i
      fin_cases i
      · simp [B, putnam2021A3Point]
      · simpa [B, putnam2021A3Point] using hroundNeg
      · simpa [B, putnam2021A3Point] using hroundNeg
    have hCint' : intcoords C := by
      rw [intcoords_def]
      intro i
      fin_cases i
      · simpa [C, putnam2021A3Point] using hroundNeg
      · simp [C, putnam2021A3Point]
      · simpa [C, putnam2021A3Point] using hroundNeg
    have hDint' : intcoords D := by
      rw [intcoords_def]
      intro i
      fin_cases i
      · simpa [D, putnam2021A3Point] using hroundNeg
      · simpa [D, putnam2021A3Point] using hroundNeg
      · simp [D, putnam2021A3Point]
    let s : ℝ := Real.sqrt (8 * (k : ℝ) ^ 2)
    have hspos : 0 < s := by
      dsimp [s]
      apply Real.sqrt_pos.2
      nlinarith [sq_pos_of_ne_zero hkRne]
    have hABd : dist A B = s := by
      rw [dist_eq_norm, EuclideanSpace.norm_eq]
      dsimp [s]
      congr 1
      simp [A, B, putnam2021A3Point, Fin.sum_univ_three, sq_abs]
      ring
    have hACd : dist A C = s := by
      rw [dist_eq_norm, EuclideanSpace.norm_eq]
      dsimp [s]
      congr 1
      simp [A, C, putnam2021A3Point, Fin.sum_univ_three, sq_abs]
      ring
    have hADd : dist A D = s := by
      rw [dist_eq_norm, EuclideanSpace.norm_eq]
      dsimp [s]
      congr 1
      simp [A, D, putnam2021A3Point, Fin.sum_univ_three, sq_abs]
      ring
    have hBCd : dist B C = s := by
      rw [dist_eq_norm, EuclideanSpace.norm_eq]
      dsimp [s]
      congr 1
      simp [B, C, putnam2021A3Point, Fin.sum_univ_three, sq_abs]
      ring
    have hBDd : dist B D = s := by
      rw [dist_eq_norm, EuclideanSpace.norm_eq]
      dsimp [s]
      congr 1
      simp [B, D, putnam2021A3Point, Fin.sum_univ_three, sq_abs]
      ring
    have hCDd : dist C D = s := by
      rw [dist_eq_norm, EuclideanSpace.norm_eq]
      dsimp [s]
      congr 1
      simp [C, D, putnam2021A3Point, Fin.sum_univ_three, sq_abs]
      ring
    exact ⟨hNpos, A, B, C, D, hAmem, hBmem, hCmem, hDmem,
      hAint', hBint', hCint', hDint',
      s, hspos, hABd, hACd, hADd, hBCd, hBDd, hCDd⟩
