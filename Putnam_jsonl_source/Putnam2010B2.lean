import Mathlib

open Filter Topology Set
-- 3
/--
Given that $A$, $B$, and $C$ are noncollinear points in the plane with integer coordinates such that the distances $AB$, $AC$, and $BC$ are integers, what is the smallest possible value of $AB$?
-/
theorem putnam_2010_b2
  (ABCintcoords ABCintdists ABCall: EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → Prop)
  (hABCintcoords : ∀ A B C, ABCintcoords A B C ↔ (∀ i : Fin 2, A i = round (A i) ∧ B i = round (B i) ∧ C i = round (C i)))
  (hABCintdists : ∀ A B C, ABCintdists A B C ↔ (dist A B = round (dist A B) ∧ dist A C = round (dist A C) ∧ dist B C = round (dist B C)))
  (hABCall : ∀ A B C, ABCall A B C ↔ (¬Collinear ℝ {A, B, C} ∧ ABCintcoords A B C ∧ ABCintdists A B C)) :
  IsLeast {y | ∃ A B C, ABCall A B C ∧ y = dist A B} ((3) : ℕ ) := by
  classical
  have int_sq_add_one_eq_sq : ∀ a b : ℤ, a ^ 2 + 1 = b ^ 2 → a = 0 := by
    intro a b h
    have hfac : (b - a) * (b + a) = 1 := by nlinarith
    obtain (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) := Int.mul_eq_one_iff_eq_one_or_neg_one.mp hfac
    · nlinarith
    · nlinarith
  have sq_len_four_cases :
      ∀ u0 u1 : ℤ, (2 : ℤ) ^ 2 = u0 ^ 2 + u1 ^ 2 →
        (u0 = 2 ∧ u1 = 0) ∨ (u0 = -2 ∧ u1 = 0) ∨
          (u0 = 0 ∧ u1 = 2) ∨ (u0 = 0 ∧ u1 = -2) := by
    intro u0 u1 h
    have hu0le : u0 ≤ 2 := by nlinarith [h, sq_nonneg u1, sq_nonneg (u0 - 2)]
    have hu0ge : -2 ≤ u0 := by nlinarith [h, sq_nonneg u1, sq_nonneg (u0 + 2)]
    have hu1le : u1 ≤ 2 := by nlinarith [h, sq_nonneg u0, sq_nonneg (u1 - 2)]
    have hu1ge : -2 ≤ u1 := by nlinarith [h, sq_nonneg u0, sq_nonneg (u1 + 2)]
    interval_cases u0 <;> interval_cases u1 <;> omega
  have odd_contra_add : ∀ a b : ℤ, a * 2 = 5 + b * 2 → False := by
    intro a b h
    omega
  have odd_contra_sub : ∀ a b : ℤ, a * 2 = 3 - b * 2 → False := by
    intro a b h
    omega
  have dist_sq_round :
      ∀ X Y : EuclideanSpace ℝ (Fin 2),
        (∀ i : Fin 2, X i = (round (X i) : ℝ)) →
        (∀ i : Fin 2, Y i = (round (Y i) : ℝ)) →
        dist X Y = (round (dist X Y) : ℝ) →
        (round (dist X Y)) ^ 2 =
          (round (X 0) - round (Y 0)) ^ 2 + (round (X 1) - round (Y 1)) ^ 2 := by
    intro X Y hX hY hdist
    have hsqR : dist X Y ^ 2 = (X 0 - Y 0) ^ 2 + (X 1 - Y 1) ^ 2 := by
      rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
      simp [Real.dist_eq, sq_abs]
    have hsqR' :
        ((round (dist X Y) : ℤ) : ℝ) ^ 2 =
          ((round (X 0) - round (Y 0) : ℤ) : ℝ) ^ 2 +
            ((round (X 1) - round (Y 1) : ℤ) : ℝ) ^ 2 := by
      rw [Int.cast_sub, Int.cast_sub]
      rw [← hdist, ← hX 0, ← hY 0, ← hX 1, ← hY 1]
      exact hsqR
    exact_mod_cast hsqR'
  have collinear_same_second :
      ∀ A B C : EuclideanSpace ℝ (Fin 2),
        (∀ i : Fin 2, A i = (round (A i) : ℝ)) →
        (∀ i : Fin 2, B i = (round (B i) : ℝ)) →
        (∀ i : Fin 2, C i = (round (C i) : ℝ)) →
        round (A 1) - round (B 1) = 0 →
        round (A 1) - round (C 1) = 0 →
        Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro A B C hA hB hC hAB hAC
    rw [collinear_iff_exists_forall_eq_smul_vadd]
    refine ⟨A, (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)), ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with hpA | hpB | hpC
    · subst p
      refine ⟨0, ?_⟩
      simp
    · subst p
      refine ⟨B 0 - A 0, ?_⟩
      ext i
      fin_cases i
      · simp
      · have hBA1 : B 1 = A 1 := by
          have hround : round (A 1) = round (B 1) := by omega
          calc
            B 1 = ((round (B 1) : ℤ) : ℝ) := hB 1
            _ = ((round (A 1) : ℤ) : ℝ) := by rw [hround]
            _ = A 1 := (hA 1).symm
        simp [hBA1]
    · subst p
      refine ⟨C 0 - A 0, ?_⟩
      ext i
      fin_cases i
      · simp
      · have hCA1 : C 1 = A 1 := by
          have hround : round (A 1) = round (C 1) := by omega
          calc
            C 1 = ((round (C 1) : ℤ) : ℝ) := hC 1
            _ = ((round (A 1) : ℤ) : ℝ) := by rw [hround]
            _ = A 1 := (hA 1).symm
        simp [hCA1]
  have collinear_same_first :
      ∀ A B C : EuclideanSpace ℝ (Fin 2),
        (∀ i : Fin 2, A i = (round (A i) : ℝ)) →
        (∀ i : Fin 2, B i = (round (B i) : ℝ)) →
        (∀ i : Fin 2, C i = (round (C i) : ℝ)) →
        round (A 0) - round (B 0) = 0 →
        round (A 0) - round (C 0) = 0 →
        Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro A B C hA hB hC hAB hAC
    rw [collinear_iff_exists_forall_eq_smul_vadd]
    refine ⟨A, (!₂[0, 1] : EuclideanSpace ℝ (Fin 2)), ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with hpA | hpB | hpC
    · subst p
      refine ⟨0, ?_⟩
      simp
    · subst p
      refine ⟨B 1 - A 1, ?_⟩
      ext i
      fin_cases i
      · have hBA0 : B 0 = A 0 := by
          have hround : round (A 0) = round (B 0) := by omega
          calc
            B 0 = ((round (B 0) : ℤ) : ℝ) := hB 0
            _ = ((round (A 0) : ℤ) : ℝ) := by rw [hround]
            _ = A 0 := (hA 0).symm
        simp [hBA0]
      · simp
    · subst p
      refine ⟨C 1 - A 1, ?_⟩
      ext i
      fin_cases i
      · have hCA0 : C 0 = A 0 := by
          have hround : round (A 0) = round (C 0) := by omega
          calc
            C 0 = ((round (C 0) : ℤ) : ℝ) := hC 0
            _ = ((round (A 0) : ℤ) : ℝ) := by rw [hround]
            _ = A 0 := (hA 0).symm
        simp [hCA0]
      · simp
  constructor
  · let A0 : EuclideanSpace ℝ (Fin 2) := !₂[0, 0]
    let B0 : EuclideanSpace ℝ (Fin 2) := !₂[3, 0]
    let C0 : EuclideanSpace ℝ (Fin 2) := !₂[0, 4]
    have hAB3 : dist A0 B0 = 3 := by
      rw [EuclideanSpace.dist_eq]
      norm_num [A0, B0, Fin.sum_univ_two, Real.sqrt_sq_eq_abs]
    have hAC4 : dist A0 C0 = 4 := by
      rw [EuclideanSpace.dist_eq]
      norm_num [A0, C0, Fin.sum_univ_two, Real.sqrt_sq_eq_abs]
    have hBC5 : dist B0 C0 = 5 := by
      rw [EuclideanSpace.dist_eq]
      norm_num [B0, C0, Fin.sum_univ_two, Real.sqrt_sq_eq_abs]
    have hnotcol :
        ¬Collinear ℝ ({A0, B0, C0} : Set (EuclideanSpace ℝ (Fin 2))) := by
      intro hcol
      have hA0 : A0 ∈ ({A0, B0, C0} : Set (EuclideanSpace ℝ (Fin 2))) := by simp
      rcases (collinear_iff_of_mem (k := ℝ) hA0).mp hcol with ⟨v, hv⟩
      have hB0 : B0 ∈ ({A0, B0, C0} : Set (EuclideanSpace ℝ (Fin 2))) := by simp
      have hC0 : C0 ∈ ({A0, B0, C0} : Set (EuclideanSpace ℝ (Fin 2))) := by simp
      rcases hv B0 hB0 with ⟨r, hr⟩
      rcases hv C0 hC0 with ⟨s, hs⟩
      have hr0 : r * v 0 = 3 := by
        simpa [A0, B0] using (congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) hr).symm
      have hr1 : r * v 1 = 0 := by
        simpa [A0, B0] using (congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 1) hr).symm
      have hs1 : s * v 1 = 4 := by
        simpa [A0, C0] using (congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 1) hs).symm
      have hr_ne : r ≠ 0 := by
        intro hrz
        rw [hrz] at hr0
        norm_num at hr0
      have hv1 : v 1 = 0 := (mul_eq_zero.mp hr1).resolve_left hr_ne
      rw [hv1] at hs1
      norm_num at hs1
    exact ⟨A0, B0, C0,
      (hABCall A0 B0 C0).mpr
        ⟨hnotcol,
          (hABCintcoords A0 B0 C0).mpr (by
            intro i
            fin_cases i <;> norm_num [A0, B0, C0, round]),
          (hABCintdists A0 B0 C0).mpr (by
            refine ⟨?_, ?_, ?_⟩
            · rw [hAB3]
              norm_num [round]
            · rw [hAC4]
              norm_num [round]
            · rw [hBC5]
              norm_num [round])⟩,
      by norm_num [hAB3]⟩
  · rintro y ⟨A, B, C, hABC, rfl⟩
    change (3 : ℝ) ≤ dist A B
    by_contra hlt_not
    have hltAB : dist A B < 3 := not_le.mp hlt_not
    rcases (hABCall A B C).mp hABC with ⟨hnotcol, hcoordsPred, hdistsPred⟩
    have hcoords := (hABCintcoords A B C).mp hcoordsPred
    have hA : ∀ i : Fin 2, A i = (round (A i) : ℝ) := fun i => (hcoords i).1
    have hB : ∀ i : Fin 2, B i = (round (B i) : ℝ) := fun i => (hcoords i).2.1
    have hC : ∀ i : Fin 2, C i = (round (C i) : ℝ) := fun i => (hcoords i).2.2
    have hdists := (hABCintdists A B C).mp hdistsPred
    have hABdist : dist A B = (round (dist A B) : ℝ) := hdists.1
    have hACdist : dist A C = (round (dist A C) : ℝ) := hdists.2.1
    have hBCdist : dist B C = (round (dist B C) : ℝ) := hdists.2.2
    let m : ℤ := round (dist A B)
    let n : ℤ := round (dist A C)
    let p : ℤ := round (dist B C)
    let u0 : ℤ := round (A 0) - round (B 0)
    let u1 : ℤ := round (A 1) - round (B 1)
    let v0 : ℤ := round (A 0) - round (C 0)
    let v1 : ℤ := round (A 1) - round (C 1)
    have hmposR : (0 : ℝ) < (m : ℝ) := by
      change (0 : ℝ) < ((round (dist A B) : ℤ) : ℝ)
      rw [← hABdist]
      exact dist_pos.mpr (ne₁₂_of_not_collinear hnotcol)
    have hmltR : (m : ℝ) < (3 : ℝ) := by
      change ((round (dist A B) : ℤ) : ℝ) < (3 : ℝ)
      rw [← hABdist]
      exact hltAB
    have hmpos : 0 < m := Int.cast_pos.mp hmposR
    have hmltR' : (m : ℝ) < ((3 : ℤ) : ℝ) := by simpa using hmltR
    have hmlt : m < 3 := Int.cast_lt.mp hmltR'
    have hm_cases : m = 1 ∨ m = 2 := by omega
    have hAC_lt : dist A C < dist A B + dist B C :=
      (dist_lt_dist_add_dist_iff (a := A) (b := B) (c := C)).2
        (fun hw => hnotcol hw.collinear)
    have hBC_lt : dist B C < dist A B + dist A C := by
      have hnotcol' : ¬Collinear ℝ ({B, A, C} : Set (EuclideanSpace ℝ (Fin 2))) := by
        intro hc
        apply hnotcol
        have hset :
            ({B, A, C} : Set (EuclideanSpace ℝ (Fin 2))) = {A, B, C} := by
          ext x
          simp [or_left_comm]
        simpa [hset] using hc
      have h := (dist_lt_dist_add_dist_iff (a := B) (b := A) (c := C)).2
        (fun hw => hnotcol' hw.collinear)
      simpa [dist_comm, add_comm, add_left_comm, add_assoc] using h
    have hn_lt_mp : n < m + p := by
      have hR : (n : ℝ) < (m : ℝ) + (p : ℝ) := by
        change ((round (dist A C) : ℤ) : ℝ) <
          ((round (dist A B) : ℤ) : ℝ) + ((round (dist B C) : ℤ) : ℝ)
        rw [← hACdist, ← hABdist, ← hBCdist]
        exact hAC_lt
      exact_mod_cast hR
    have hp_lt_mn : p < m + n := by
      have hR : (p : ℝ) < (m : ℝ) + (n : ℝ) := by
        change ((round (dist B C) : ℤ) : ℝ) <
          ((round (dist A B) : ℤ) : ℝ) + ((round (dist A C) : ℤ) : ℝ)
        rw [← hBCdist, ← hABdist, ← hACdist]
        exact hBC_lt
      exact_mod_cast hR
    have hnp_lt : n - p < m := by omega
    have hpn_lt : p - n < m := by omega
    have hm_sq : m ^ 2 = u0 ^ 2 + u1 ^ 2 := by
      dsimp [m, u0, u1]
      exact dist_sq_round A B hA hB hABdist
    have hn_sq : n ^ 2 = v0 ^ 2 + v1 ^ 2 := by
      dsimp [n, v0, v1]
      exact dist_sq_round A C hA hC hACdist
    have hp_sq_raw :
        p ^ 2 =
          (round (B 0) - round (C 0)) ^ 2 + (round (B 1) - round (C 1)) ^ 2 := by
      dsimp [p]
      exact dist_sq_round B C hB hC hBCdist
    have hp_sq : p ^ 2 = (v0 - u0) ^ 2 + (v1 - u1) ^ 2 := by
      dsimp [u0, u1, v0, v1] at *
      nlinarith [hp_sq_raw]
    let dot : ℤ := u0 * v0 + u1 * v1
    have hdot : 2 * dot = m ^ 2 + n ^ 2 - p ^ 2 := by
      dsimp [dot]
      nlinarith [hm_sq, hn_sq, hp_sq]
    rcases hm_cases with hm1 | hm2
    · have hnp1 : n - p < 1 := by omega
      have hpn1 : p - n < 1 := by omega
      have hnp_eq : n = p := by omega
      have hdot1 := hdot
      rw [hm1] at hdot1
      rw [hnp_eq] at hdot1
      ring_nf at hdot1
      omega
    · have hnp2 : n - p < 2 := by omega
      have hpn2 : p - n < 2 := by omega
      have hdiff_cases : n = p ∨ n - p = 1 ∨ p - n = 1 := by omega
      rcases hdiff_cases with hnp_eq | hdiff | hdiff
      · have hdot_eq : 2 * dot = 4 := by
          have hdot2 := hdot
          rw [hm2] at hdot2
          rw [hnp_eq] at hdot2
          ring_nf at hdot2
          simpa [mul_comm] using hdot2
        have hdot_eq' : 2 * (u0 * v0 + u1 * v1) = 4 := by
          simpa [dot] using hdot_eq
        have humsq : (2 : ℤ) ^ 2 = u0 ^ 2 + u1 ^ 2 := by
          simpa [hm2] using hm_sq
        have hu_cases :
            (u0 = 2 ∧ u1 = 0) ∨ (u0 = -2 ∧ u1 = 0) ∨
              (u0 = 0 ∧ u1 = 2) ∨ (u0 = 0 ∧ u1 = -2) :=
          sq_len_four_cases u0 u1 humsq
        rcases hu_cases with ⟨hu0, hu1⟩ | ⟨hu0, hu1⟩ | ⟨hu0, hu1⟩ | ⟨hu0, hu1⟩
        · have hv0 : v0 = 1 := by
            have h := hdot_eq'
            rw [hu0, hu1] at h
            ring_nf at h
            omega
          have hv1 : v1 = 0 := by
            have hsq : v1 ^ 2 + 1 = n ^ 2 := by
              have h := hn_sq
              rw [hv0] at h
              ring_nf at h
              simpa [add_comm] using h.symm
            exact int_sq_add_one_eq_sq v1 n hsq
          have hu1' : round (A 1) - round (B 1) = 0 := by simpa [u1] using hu1
          have hv1' : round (A 1) - round (C 1) = 0 := by simpa [v1] using hv1
          exact hnotcol (collinear_same_second A B C hA hB hC hu1' hv1')
        · have hv0 : v0 = -1 := by
            have h := hdot_eq'
            rw [hu0, hu1] at h
            ring_nf at h
            omega
          have hv1 : v1 = 0 := by
            have hsq : v1 ^ 2 + 1 = n ^ 2 := by
              have h := hn_sq
              rw [hv0] at h
              ring_nf at h
              simpa [add_comm] using h.symm
            exact int_sq_add_one_eq_sq v1 n hsq
          have hu1' : round (A 1) - round (B 1) = 0 := by simpa [u1] using hu1
          have hv1' : round (A 1) - round (C 1) = 0 := by simpa [v1] using hv1
          exact hnotcol (collinear_same_second A B C hA hB hC hu1' hv1')
        · have hv1 : v1 = 1 := by
            have h := hdot_eq'
            rw [hu0, hu1] at h
            ring_nf at h
            omega
          have hv0 : v0 = 0 := by
            have hsq : v0 ^ 2 + 1 = n ^ 2 := by
              have h := hn_sq
              rw [hv1] at h
              ring_nf at h
              simpa [add_comm] using h.symm
            exact int_sq_add_one_eq_sq v0 n hsq
          have hu0' : round (A 0) - round (B 0) = 0 := by simpa [u0] using hu0
          have hv0' : round (A 0) - round (C 0) = 0 := by simpa [v0] using hv0
          exact hnotcol (collinear_same_first A B C hA hB hC hu0' hv0')
        · have hv1 : v1 = -1 := by
            have h := hdot_eq'
            rw [hu0, hu1] at h
            ring_nf at h
            omega
          have hv0 : v0 = 0 := by
            have hsq : v0 ^ 2 + 1 = n ^ 2 := by
              have h := hn_sq
              rw [hv1] at h
              ring_nf at h
              simpa [add_comm] using h.symm
            exact int_sq_add_one_eq_sq v0 n hsq
          have hu0' : round (A 0) - round (B 0) = 0 := by simpa [u0] using hu0
          have hv0' : round (A 0) - round (C 0) = 0 := by simpa [v0] using hv0
          exact hnotcol (collinear_same_first A B C hA hB hC hu0' hv0')
      · have hdot2 := hdot
        rw [hm2] at hdot2
        have hn : n = p + 1 := by omega
        rw [hn] at hdot2
        ring_nf at hdot2
        exact odd_contra_add dot p hdot2
      · have hdot2 := hdot
        rw [hm2] at hdot2
        have hp : p = n + 1 := by omega
        rw [hp] at hdot2
        ring_nf at hdot2
        exact odd_contra_sub dot n hdot2
