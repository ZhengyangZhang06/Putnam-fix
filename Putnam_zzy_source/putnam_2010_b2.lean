import Mathlib

open Filter Topology Set
abbrev putnam_2010_b2_solution : ℕ := 3

private lemma dist_sq_eq_int_coords
    (P Q : EuclideanSpace ℝ (Fin 2)) (p0 p1 q0 q1 : ℤ)
    (hP0 : P 0 = (p0 : ℝ)) (hP1 : P 1 = (p1 : ℝ))
    (hQ0 : Q 0 = (q0 : ℝ)) (hQ1 : Q 1 = (q1 : ℝ)) :
    dist P Q ^ 2 = (((q0 - p0) ^ 2 + (q1 - p1) ^ 2 : ℤ) : ℝ) := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  simp [Real.dist_eq, hP0, hP1, hQ0, hQ1]
  ring

private lemma int_sq_add_eq_four_cases {u v : ℤ} (h : u ^ 2 + v ^ 2 = 4) :
    (u = 2 ∧ v = 0) ∨ (u = -2 ∧ v = 0) ∨
      (u = 0 ∧ v = 2) ∨ (u = 0 ∧ v = -2) := by
  have hu_le4 : u ^ 2 ≤ 4 := by nlinarith [sq_nonneg v]
  have hv_le4 : v ^ 2 ≤ 4 := by nlinarith [sq_nonneg u]
  have hu_low : -2 ≤ u := by nlinarith [sq_nonneg (u + 2), hu_le4]
  have hu_high : u ≤ 2 := by nlinarith [sq_nonneg (u - 2), hu_le4]
  have hv_low : -2 ≤ v := by nlinarith [sq_nonneg (v + 2), hv_le4]
  have hv_high : v ≤ 2 := by nlinarith [sq_nonneg (v - 2), hv_le4]
  interval_cases u <;> interval_cases v <;> omega

private lemma int_sq_eq_sq_add_one_false {q r : ℤ}
    (h : r ^ 2 = 1 + q ^ 2) (hr : 1 < r) : False := by
  have hq_lt_r : q < r := by
    by_contra hn
    have hqr : r ≤ q := by omega
    nlinarith [sq_nonneg (q - r)]
  have hneg_lt : -r < q := by
    by_contra hn
    have hqr : q ≤ -r := by omega
    nlinarith [sq_nonneg (q + r)]
  have hmul : (r - q) * (r + q) = 1 := by
    ring_nf
    omega
  have hright : r + q = 1 := Int.eq_one_of_mul_eq_one_left (by omega) hmul
  have hleft : r - q = 1 := by
    apply Int.eq_one_of_mul_eq_one_left (b := r - q) (a := r + q) (by omega)
    rw [mul_comm]
    exact hmul
  omega

private lemma no_side_one {u v p q r s : ℤ}
    (hAB : u ^ 2 + v ^ 2 = 1)
    (hAC : r ^ 2 = p ^ 2 + q ^ 2)
    (hBC : s ^ 2 = (p - u) ^ 2 + (q - v) ^ 2)
    (hr_lt : r < 1 + s) (hs_lt : s < 1 + r) : False := by
  have hrs : r = s := by omega
  rw [hrs] at hAC
  have hdiff : p ^ 2 + q ^ 2 = (p - u) ^ 2 + (q - v) ^ 2 :=
    hAC.symm.trans hBC
  have hparity : 2 * (p * u + q * v) = 1 := by
    have h := hdiff
    ring_nf at h hAB ⊢
    omega
  omega

private lemma no_side_two {u v p q r s : ℤ}
    (hAB : u ^ 2 + v ^ 2 = 4)
    (hAC : r ^ 2 = p ^ 2 + q ^ 2)
    (hBC : s ^ 2 = (p - u) ^ 2 + (q - v) ^ 2)
    (hr_lt : r < 2 + s) (hs_lt : s < 2 + r) (hbase_lt : 2 < r + s) :
    False := by
  have hcases : r = s ∨ r = s + 1 ∨ s = r + 1 := by omega
  rcases hcases with hrs | hrs | hsr
  · subst r
    have hdot : p * u + q * v = 2 := by
      have hdiff : p ^ 2 + q ^ 2 = (p - u) ^ 2 + (q - v) ^ 2 :=
        hAC.symm.trans hBC
      have h := hdiff
      ring_nf at h hAB ⊢
      omega
    have hs_gt : 1 < s := by omega
    rcases int_sq_add_eq_four_cases hAB with huv | huv | huv | huv
    · rcases huv with ⟨rfl, rfl⟩
      have hp : p = 1 := by omega
      subst p
      have hsq : s ^ 2 = 1 + q ^ 2 := by omega
      exact int_sq_eq_sq_add_one_false hsq hs_gt
    · rcases huv with ⟨rfl, rfl⟩
      have hp : p = -1 := by omega
      subst p
      have hsq : s ^ 2 = 1 + q ^ 2 := by omega
      exact int_sq_eq_sq_add_one_false hsq hs_gt
    · rcases huv with ⟨rfl, rfl⟩
      have hq : q = 1 := by omega
      subst q
      have hsq : s ^ 2 = 1 + p ^ 2 := by omega
      exact int_sq_eq_sq_add_one_false hsq hs_gt
    · rcases huv with ⟨rfl, rfl⟩
      have hq : q = -1 := by omega
      subst q
      have hsq : s ^ 2 = 1 + p ^ 2 := by omega
      exact int_sq_eq_sq_add_one_false hsq hs_gt
  · subst r
    have hparity : 2 * (p * u + q * v - 2) = 2 * s + 1 := by
      ring_nf at hAB hAC hBC ⊢
      omega
    omega
  · subst s
    have hparity : 2 * (p * u + q * v - 2) = -(2 * r + 1) := by
      ring_nf at hAB hAC hBC ⊢
      omega
    omega

private lemma strict_triangle_AC {A B C : EuclideanSpace ℝ (Fin 2)}
    (hnoncol : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2)))) :
    dist A C < dist A B + dist B C := by
  have hle : dist A C ≤ dist A B + dist B C := by
    simpa [dist_comm, add_comm, add_left_comm, add_assoc] using dist_triangle A B C
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hsum : dist A B + dist B C = dist A C := by linarith
  have hbtw : Wbtw ℝ A B C := (dist_add_dist_eq_iff).1 hsum
  exact hnoncol hbtw.collinear

private lemma strict_triangle_BC {A B C : EuclideanSpace ℝ (Fin 2)}
    (hnoncol : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2)))) :
    dist B C < dist A B + dist A C := by
  have hle : dist B C ≤ dist B A + dist A C := dist_triangle B A C
  have hle' : dist B C ≤ dist A B + dist A C := by simpa [dist_comm] using hle
  refine lt_of_le_of_ne hle' ?_
  intro heq
  have hsum : dist B A + dist A C = dist B C := by
    simpa [dist_comm] using (show dist A B + dist A C = dist B C by linarith)
  have hbtw : Wbtw ℝ B A C := (dist_add_dist_eq_iff).1 hsum
  have hset : ({B, A, C} : Set (EuclideanSpace ℝ (Fin 2))) =
      ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))) := by
    ext x
    simp
    tauto
  exact hnoncol (hset ▸ hbtw.collinear)

private lemma strict_triangle_AB {A B C : EuclideanSpace ℝ (Fin 2)}
    (hnoncol : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2)))) :
    dist A B < dist A C + dist B C := by
  have hle : dist A B ≤ dist A C + dist C B := dist_triangle A C B
  have hle' : dist A B ≤ dist A C + dist B C := by simpa [dist_comm] using hle
  refine lt_of_le_of_ne hle' ?_
  intro heq
  have hsum : dist A C + dist C B = dist A B := by
    simpa [dist_comm] using (show dist A C + dist B C = dist A B by linarith)
  have hbtw : Wbtw ℝ A C B := (dist_add_dist_eq_iff).1 hsum
  have hset : ({A, C, B} : Set (EuclideanSpace ℝ (Fin 2))) =
      ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))) := by
    ext x
    simp
    tauto
  exact hnoncol (hset ▸ hbtw.collinear)

private lemma three_le_dist_of_lattice_intdist_not_collinear
    {A B C : EuclideanSpace ℝ (Fin 2)}
    (hcoords : ∀ i : Fin 2,
      A i = round (A i) ∧ B i = round (B i) ∧ C i = round (C i))
    (hdists : dist A B = round (dist A B) ∧
      dist A C = round (dist A C) ∧ dist B C = round (dist B C))
    (hnoncol : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2)))) :
    (3 : ℝ) ≤ dist A B := by
  let a0 : ℤ := round (A 0)
  let a1 : ℤ := round (A 1)
  let b0 : ℤ := round (B 0)
  let b1 : ℤ := round (B 1)
  let c0 : ℤ := round (C 0)
  let c1 : ℤ := round (C 1)
  let u : ℤ := b0 - a0
  let v : ℤ := b1 - a1
  let p : ℤ := c0 - a0
  let q : ℤ := c1 - a1
  let m : ℤ := round (dist A B)
  let r : ℤ := round (dist A C)
  let s : ℤ := round (dist B C)
  have hA0 : A 0 = (a0 : ℝ) := (hcoords 0).1
  have hA1 : A 1 = (a1 : ℝ) := (hcoords 1).1
  have hB0 : B 0 = (b0 : ℝ) := (hcoords 0).2.1
  have hB1 : B 1 = (b1 : ℝ) := (hcoords 1).2.1
  have hC0 : C 0 = (c0 : ℝ) := (hcoords 0).2.2
  have hC1 : C 1 = (c1 : ℝ) := (hcoords 1).2.2
  have hABdist : dist A B = (m : ℝ) := hdists.1
  have hACdist : dist A C = (r : ℝ) := hdists.2.1
  have hBCdist : dist B C = (s : ℝ) := hdists.2.2
  have hABsq_real := dist_sq_eq_int_coords A B a0 a1 b0 b1 hA0 hA1 hB0 hB1
  have hACsq_real := dist_sq_eq_int_coords A C a0 a1 c0 c1 hA0 hA1 hC0 hC1
  have hBCsq_real := dist_sq_eq_int_coords B C b0 b1 c0 c1 hB0 hB1 hC0 hC1
  have hABsq : u ^ 2 + v ^ 2 = m ^ 2 := by
    have h : ((m ^ 2 : ℤ) : ℝ) = (((u ^ 2 + v ^ 2 : ℤ)) : ℝ) := by
      calc
        ((m ^ 2 : ℤ) : ℝ) = dist A B ^ 2 := by
          rw [hABdist]
          norm_num
        _ = (((b0 - a0) ^ 2 + (b1 - a1) ^ 2 : ℤ) : ℝ) := hABsq_real
        _ = (((u ^ 2 + v ^ 2 : ℤ)) : ℝ) := by simp [u, v]
    exact_mod_cast h.symm
  have hACsq : r ^ 2 = p ^ 2 + q ^ 2 := by
    have h : ((r ^ 2 : ℤ) : ℝ) = (((p ^ 2 + q ^ 2 : ℤ)) : ℝ) := by
      calc
        ((r ^ 2 : ℤ) : ℝ) = dist A C ^ 2 := by
          rw [hACdist]
          norm_num
        _ = (((c0 - a0) ^ 2 + (c1 - a1) ^ 2 : ℤ) : ℝ) := hACsq_real
        _ = (((p ^ 2 + q ^ 2 : ℤ)) : ℝ) := by simp [p, q]
    exact_mod_cast h
  have hBCsq : s ^ 2 = (p - u) ^ 2 + (q - v) ^ 2 := by
    have h : ((s ^ 2 : ℤ) : ℝ) =
        ((((c0 - b0) ^ 2 + (c1 - b1) ^ 2 : ℤ)) : ℝ) := by
      calc
        ((s ^ 2 : ℤ) : ℝ) = dist B C ^ 2 := by
          rw [hBCdist]
          norm_num
        _ = (((c0 - b0) ^ 2 + (c1 - b1) ^ 2 : ℤ) : ℝ) := hBCsq_real
    have hint : s ^ 2 = (c0 - b0) ^ 2 + (c1 - b1) ^ 2 := by exact_mod_cast h
    dsimp [p, q, u, v]
    ring_nf at hint ⊢
    exact hint
  by_contra hnot
  have hlt_real : dist A B < 3 := not_le.mp hnot
  have hm_lt_real : (m : ℝ) < 3 := by simpa [hABdist] using hlt_real
  have hm_lt : m < 3 := by exact_mod_cast hm_lt_real
  have hm_pos_real : (0 : ℝ) < (m : ℝ) := by
    have hpos : 0 < dist A B := dist_pos.mpr (ne₁₂_of_not_collinear hnoncol)
    simpa [hABdist] using hpos
  have hm_pos : 0 < m := by exact_mod_cast hm_pos_real
  have hAC_lt_real := strict_triangle_AC hnoncol
  have hBC_lt_real := strict_triangle_BC hnoncol
  have hAB_lt_real := strict_triangle_AB hnoncol
  have hr_lt_m_s : r < m + s := by
    have : (r : ℝ) < (m : ℝ) + (s : ℝ) := by
      simpa [hABdist, hACdist, hBCdist] using hAC_lt_real
    exact_mod_cast this
  have hs_lt_m_r : s < m + r := by
    have : (s : ℝ) < (m : ℝ) + (r : ℝ) := by
      simpa [hABdist, hACdist, hBCdist] using hBC_lt_real
    exact_mod_cast this
  have hm_lt_r_s : m < r + s := by
    have : (m : ℝ) < (r : ℝ) + (s : ℝ) := by
      simpa [hABdist, hACdist, hBCdist] using hAB_lt_real
    exact_mod_cast this
  interval_cases m
  · have hAB1 : u ^ 2 + v ^ 2 = 1 := by omega
    exact no_side_one hAB1 hACsq hBCsq hr_lt_m_s hs_lt_m_r
  · have hAB2 : u ^ 2 + v ^ 2 = 4 := by omega
    exact no_side_two hAB2 hACsq hBCsq hr_lt_m_s hs_lt_m_r hm_lt_r_s

/--
Given that $A$, $B$, and $C$ are noncollinear points in the plane with integer coordinates such that the distances $AB$, $AC$, and $BC$ are integers, what is the smallest possible value of $AB$?
-/
theorem putnam_2010_b2
  (ABCintcoords ABCintdists ABCall: EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → Prop)
  (hABCintcoords : ∀ A B C, ABCintcoords A B C ↔ (∀ i : Fin 2, A i = round (A i) ∧ B i = round (B i) ∧ C i = round (C i)))
  (hABCintdists : ∀ A B C, ABCintdists A B C ↔ (dist A B = round (dist A B) ∧ dist A C = round (dist A C) ∧ dist B C = round (dist B C)))
  (hABCall : ∀ A B C, ABCall A B C ↔ (¬Collinear ℝ {A, B, C} ∧ ABCintcoords A B C ∧ ABCintdists A B C)) :
  IsLeast {y | ∃ A B C, ABCall A B C ∧ y = dist A B} putnam_2010_b2_solution :=
by
  constructor
  · dsimp [putnam_2010_b2_solution]
    let A : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (![0, 0] : Fin 2 → ℝ)
    let B : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (![3, 0] : Fin 2 → ℝ)
    let C : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (![0, 4] : Fin 2 → ℝ)
    have hABdist : dist A B = 3 := by
      rw [EuclideanSpace.dist_eq]
      norm_num [Real.dist_eq, A, B]
    have hACdist : dist A C = 4 := by
      rw [EuclideanSpace.dist_eq]
      norm_num [Real.dist_eq, A, C]
    have hBCdist : dist B C = 5 := by
      rw [EuclideanSpace.dist_eq]
      norm_num [Real.dist_eq, B, C]
    refine ⟨A, B, C, ?_, hABdist.symm⟩
    refine (hABCall A B C).2 ⟨?_, ?_, ?_⟩
    · intro hcol
      have hA : A ∈ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))) := by simp
      have hB : B ∈ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))) := by simp
      have hC : C ∈ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))) := by simp
      have hAB : A ≠ B := by
        intro h
        have hc := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) h
        norm_num [A, B] at hc
      have hmem : C ∈ affineSpan ℝ ({A, B} : Set (EuclideanSpace ℝ (Fin 2))) :=
        hcol.mem_affineSpan_of_mem_of_ne hA hB hC hAB
      rw [← vsub_vadd C A, vadd_left_mem_affineSpan_pair] at hmem
      rcases hmem with ⟨r, hr⟩
      have hy := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) hr
      norm_num [A, B, C] at hy
    · exact (hABCintcoords A B C).2 (by
        intro i
        fin_cases i <;> norm_num [A, B, C, round])
    · exact (hABCintdists A B C).2 (by
        constructor
        · rw [hABdist]
          norm_num [round]
        constructor
        · rw [hACdist]
          norm_num [round]
        · rw [hBCdist]
          norm_num [round])
  · intro y hy
    dsimp [putnam_2010_b2_solution]
    rcases hy with ⟨A, B, C, hcall, hy_eq⟩
    have hall := (hABCall A B C).1 hcall
    have hcoords := (hABCintcoords A B C).1 hall.2.1
    have hdists := (hABCintdists A B C).1 hall.2.2
    rw [hy_eq]
    exact three_le_dist_of_lattice_intdist_not_collinear hcoords hdists hall.1
