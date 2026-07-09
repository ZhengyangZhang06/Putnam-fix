import Mathlib

noncomputable abbrev putnam_2010_a1_solution : ℕ → ℕ :=
  fun n => (n + n % 2) / 2

private lemma putnam_2010_a1_solution_eq (n : ℕ) :
    putnam_2010_a1_solution n = (n + 1) / 2 := by
  unfold putnam_2010_a1_solution
  rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
  · rw [h0]
    have hEven : Even n := Nat.even_iff.mpr h0
    rcases (even_iff_exists_two_mul.mp hEven) with ⟨r, rfl⟩
    omega
  · rw [h1]

private lemma putnam_2010_a1_total (n : ℕ) :
    (∑ x : Finset.Icc 1 n, (x : ℕ)) = n * (n + 1) / 2 := by
  rw [Finset.univ_eq_attach (Finset.Icc 1 n)]
  have hattach : (∑ x ∈ (Finset.Icc 1 n).attach, (x : ℕ)) =
      ∑ x ∈ Finset.Icc 1 n, x := by
    simpa using (Finset.sum_attach (Finset.Icc 1 n) (fun x : ℕ => x))
  rw [hattach]
  have hsr : (∑ x ∈ Finset.range (n + 1), x) = n * (n + 1) / 2 := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (Finset.sum_range_id (n + 1))
  rw [← hsr]
  rw [Nat.range_succ_eq_Icc_zero n]
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le n)]
  rw [Finset.sum_cons]
  have hIoc : Finset.Ioc 0 n = Finset.Icc 1 n := by
    ext x
    simp [Finset.mem_Ioc, Finset.mem_Icc, Nat.succ_le_iff]
  rw [hIoc]
  simp

private lemma putnam_2010_a1_upper (n k : ℕ) (npos : n > 0)
    (boxes : Finset.Icc 1 n → Fin k)
    (heq : ∀ i j : Fin k,
      ∑ x ∈ Finset.univ.filter (boxes · = i), (x : ℕ) =
      ∑ x ∈ Finset.univ.filter (boxes · = j), (x : ℕ)) :
    k ≤ (n + 1) / 2 := by
  let a : Finset.Icc 1 n :=
    ⟨n, by exact Finset.mem_Icc.mpr ⟨Nat.succ_le_iff.mpr npos, le_rfl⟩⟩
  let i0 : Fin k := boxes a
  let S : ℕ := ∑ x ∈ Finset.univ.filter (boxes · = i0), (x : ℕ)
  have ha_mem : a ∈ Finset.univ.filter (boxes · = i0) := by
    simp [a, i0]
  have hSge : n ≤ S := by
    simpa [S, a] using
      (Finset.single_le_sum (s := Finset.univ.filter (boxes · = i0))
        (f := fun x : Finset.Icc 1 n => (x : ℕ)) (fun x _ => Nat.zero_le _) ha_mem)
  have hfiber :
      (∑ j : Fin k, ∑ x ∈ Finset.univ.filter (boxes · = j), (x : ℕ)) =
        ∑ x : Finset.Icc 1 n, (x : ℕ) := by
    simpa using
      (Finset.sum_fiberwise (s := (Finset.univ : Finset (Finset.Icc 1 n)))
        (g := boxes) (f := fun x : Finset.Icc 1 n => (x : ℕ)))
  have hconst :
      (∑ j : Fin k, ∑ x ∈ Finset.univ.filter (boxes · = j), (x : ℕ)) =
        k * S := by
    calc
      (∑ j : Fin k, ∑ x ∈ Finset.univ.filter (boxes · = j), (x : ℕ))
          = ∑ _j : Fin k, S := by
            apply Finset.sum_congr rfl
            intro j _
            exact heq j i0
      _ = k * S := by
            simp [S]
  have hks : k * S = n * (n + 1) / 2 := by
    rw [← hconst, hfiber, putnam_2010_a1_total]
  have hkn : k * n ≤ n * (n + 1) / 2 := by
    exact (Nat.mul_le_mul_left k hSge).trans_eq hks
  have hdouble : (k * n) * 2 ≤ n * (n + 1) := by
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).1 hkn
  have hcancel_arg : n * (k * 2) ≤ n * (n + 1) := by
    nlinarith
  have hk2 : k * 2 ≤ n + 1 := Nat.le_of_mul_le_mul_left hcancel_arg npos
  exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 hk2

private lemma putnam_2010_a1_lower_even (r : ℕ) (hr : 0 < r) :
    ∃ boxes : Finset.Icc 1 (2 * r) → Fin r, ∀ i j : Fin r,
      ∑ x ∈ Finset.univ.filter (boxes · = i), (x : ℕ) =
      ∑ x ∈ Finset.univ.filter (boxes · = j), (x : ℕ) := by
  classical
  let boxes : Finset.Icc 1 (2 * r) → Fin r := fun x =>
    if hx : (x : ℕ) ≤ r then
      ⟨(x : ℕ) - 1, by
        have hxmem := x.2
        rw [Finset.mem_Icc] at hxmem
        omega⟩
    else
      ⟨2 * r - (x : ℕ), by
        have hxmem := x.2
        rw [Finset.mem_Icc] at hxmem
        omega⟩
  refine ⟨boxes, ?_⟩
  intro i j
  have hfiber (i : Fin r) :
      Finset.univ.filter (boxes · = i) =
        ({(⟨i.val + 1, by
            rw [Finset.mem_Icc]
            have hi := i.isLt
            omega⟩ : Finset.Icc 1 (2 * r)),
          (⟨2 * r - i.val, by
            rw [Finset.mem_Icc]
            have hi := i.isLt
            omega⟩ : Finset.Icc 1 (2 * r))} : Finset (Finset.Icc 1 (2 * r))) := by
    ext x
    have hxmem := x.2
    rw [Finset.mem_Icc] at hxmem
    have hi := i.isLt
    by_cases hxle : (x : ℕ) ≤ r
    · have hiff : boxes x = i ↔ (x : ℕ) = i.val + 1 := by
        simp [boxes, hxle, Fin.ext_iff]
        omega
      simp [hiff]
      constructor
      · intro hxval
        left
        apply Subtype.ext
        exact hxval
      · intro hxval
        rcases hxval with hxval | hxval
        · exact congrArg Subtype.val hxval
        · have hv : (x : ℕ) = 2 * r - i.val := by
            simpa using congrArg Subtype.val hxval
          omega
    · have hiff : boxes x = i ↔ (x : ℕ) = 2 * r - i.val := by
        simp [boxes, hxle, Fin.ext_iff]
        omega
      simp [hiff]
      constructor
      · intro hxval
        right
        apply Subtype.ext
        exact hxval
      · intro hxval
        rcases hxval with hxval | hxval
        · have hv : (x : ℕ) = i.val + 1 := by
            simpa using congrArg Subtype.val hxval
          omega
        · exact congrArg Subtype.val hxval
  have hsum (i : Fin r) :
      ∑ x ∈ Finset.univ.filter (boxes · = i), (x : ℕ) = 2 * r + 1 := by
    rw [hfiber i]
    have hne : (⟨i.val + 1, by
            rw [Finset.mem_Icc]
            have hi := i.isLt
            omega⟩ : Finset.Icc 1 (2 * r)) ≠
          (⟨2 * r - i.val, by
            rw [Finset.mem_Icc]
            have hi := i.isLt
            omega⟩ : Finset.Icc 1 (2 * r)) := by
      intro h
      have hv : i.val + 1 = 2 * r - i.val := by
        simpa using congrArg Subtype.val h
      have hi := i.isLt
      omega
    rw [Finset.sum_pair hne]
    change (i.val + 1) + (2 * r - i.val) = 2 * r + 1
    have hi := i.isLt
    omega
  rw [hsum i, hsum j]

private lemma putnam_2010_a1_lower_odd (r : ℕ) :
    ∃ boxes : Finset.Icc 1 (2 * r + 1) → Fin (r + 1), ∀ i j : Fin (r + 1),
      ∑ x ∈ Finset.univ.filter (boxes · = i), (x : ℕ) =
      ∑ x ∈ Finset.univ.filter (boxes · = j), (x : ℕ) := by
  classical
  let boxes : Finset.Icc 1 (2 * r + 1) → Fin (r + 1) := fun x =>
    if hlast : (x : ℕ) = 2 * r + 1 then
      ⟨r, by omega⟩
    else if hx : (x : ℕ) ≤ r then
      ⟨(x : ℕ) - 1, by
        have hxmem := x.2
        rw [Finset.mem_Icc] at hxmem
        omega⟩
    else
      ⟨2 * r - (x : ℕ), by
        have hxmem := x.2
        rw [Finset.mem_Icc] at hxmem
        omega⟩
  refine ⟨boxes, ?_⟩
  intro i j
  have hpair (i : Fin (r + 1)) (hi : i.val < r) :
      Finset.univ.filter (boxes · = i) =
        ({(⟨i.val + 1, by
            rw [Finset.mem_Icc]
            omega⟩ : Finset.Icc 1 (2 * r + 1)),
          (⟨2 * r - i.val, by
            rw [Finset.mem_Icc]
            omega⟩ : Finset.Icc 1 (2 * r + 1))} :
          Finset (Finset.Icc 1 (2 * r + 1))) := by
    ext x
    have hxmem := x.2
    rw [Finset.mem_Icc] at hxmem
    by_cases hlast : (x : ℕ) = 2 * r + 1
    · have hnot_box : boxes x ≠ i := by
        simp [boxes, hlast, Fin.ext_iff]
        omega
      have hnot_low : x ≠ (⟨i.val + 1, by
            rw [Finset.mem_Icc]
            omega⟩ : Finset.Icc 1 (2 * r + 1)) := by
        intro h
        have hv : (x : ℕ) = i.val + 1 := by simpa using congrArg Subtype.val h
        omega
      have hnot_high : x ≠ (⟨2 * r - i.val, by
            rw [Finset.mem_Icc]
            omega⟩ : Finset.Icc 1 (2 * r + 1)) := by
        intro h
        have hv : (x : ℕ) = 2 * r - i.val := by simpa using congrArg Subtype.val h
        omega
      simp [hnot_box, hnot_low, hnot_high]
    · by_cases hxle : (x : ℕ) ≤ r
      · have hiff : boxes x = i ↔ (x : ℕ) = i.val + 1 := by
          simp [boxes, hlast, hxle, Fin.ext_iff]
          omega
        simp [hiff]
        constructor
        · intro hxval
          left
          apply Subtype.ext
          exact hxval
        · intro hxval
          rcases hxval with hxval | hxval
          · exact congrArg Subtype.val hxval
          · have hv : (x : ℕ) = 2 * r - i.val := by
              simpa using congrArg Subtype.val hxval
            omega
      · have hiff : boxes x = i ↔ (x : ℕ) = 2 * r - i.val := by
          simp [boxes, hlast, hxle, Fin.ext_iff]
          omega
        simp [hiff]
        constructor
        · intro hxval
          right
          apply Subtype.ext
          exact hxval
        · intro hxval
          rcases hxval with hxval | hxval
          · have hv : (x : ℕ) = i.val + 1 := by
              simpa using congrArg Subtype.val hxval
            omega
          · exact congrArg Subtype.val hxval
  have hlast_fiber :
      Finset.univ.filter (boxes · = (⟨r, by omega⟩ : Fin (r + 1))) =
        ({(⟨2 * r + 1, by
            rw [Finset.mem_Icc]
            omega⟩ : Finset.Icc 1 (2 * r + 1))} :
          Finset (Finset.Icc 1 (2 * r + 1))) := by
    ext x
    have hxmem := x.2
    rw [Finset.mem_Icc] at hxmem
    by_cases hlast : (x : ℕ) = 2 * r + 1
    · have hxeq : x = (⟨2 * r + 1, by
            rw [Finset.mem_Icc]
            omega⟩ : Finset.Icc 1 (2 * r + 1)) := by
        apply Subtype.ext
        exact hlast
      simp [boxes, hxeq]
    · by_cases hxle : (x : ℕ) ≤ r
      · have hnot_box : boxes x ≠ (⟨r, by omega⟩ : Fin (r + 1)) := by
          simp [boxes, hlast, hxle, Fin.ext_iff]
          omega
        have hnot_last : x ≠ (⟨2 * r + 1, by
            rw [Finset.mem_Icc]
            omega⟩ : Finset.Icc 1 (2 * r + 1)) := by
          intro h
          have hv : (x : ℕ) = 2 * r + 1 := by simpa using congrArg Subtype.val h
          exact hlast hv
        simp [hnot_box, hnot_last]
      · have hnot_box : boxes x ≠ (⟨r, by omega⟩ : Fin (r + 1)) := by
          simp [boxes, hlast, hxle, Fin.ext_iff]
          omega
        have hnot_last : x ≠ (⟨2 * r + 1, by
            rw [Finset.mem_Icc]
            omega⟩ : Finset.Icc 1 (2 * r + 1)) := by
          intro h
          have hv : (x : ℕ) = 2 * r + 1 := by simpa using congrArg Subtype.val h
          exact hlast hv
        simp [hnot_box, hnot_last]
  have hsum (i : Fin (r + 1)) :
      ∑ x ∈ Finset.univ.filter (boxes · = i), (x : ℕ) = 2 * r + 1 := by
    by_cases hi : i.val = r
    · have hieq : i = (⟨r, by omega⟩ : Fin (r + 1)) := by
        apply Fin.ext
        exact hi
      rw [hieq, hlast_fiber]
      simp
    · have hilt : i.val < r := by
        have hi2 := i.isLt
        omega
      rw [hpair i hilt]
      have hne : (⟨i.val + 1, by
              rw [Finset.mem_Icc]
              omega⟩ : Finset.Icc 1 (2 * r + 1)) ≠
            (⟨2 * r - i.val, by
              rw [Finset.mem_Icc]
              omega⟩ : Finset.Icc 1 (2 * r + 1)) := by
        intro h
        have hv : i.val + 1 = 2 * r - i.val := by
          simpa using congrArg Subtype.val h
        omega
      rw [Finset.sum_pair hne]
      change (i.val + 1) + (2 * r - i.val) = 2 * r + 1
      omega
  rw [hsum i, hsum j]

private lemma putnam_2010_a1_lower (n : ℕ) (npos : n > 0) :
    ∃ boxes : Finset.Icc 1 n → Fin ((n + 1) / 2),
      ∀ i j : Fin ((n + 1) / 2),
        ∑ x ∈ Finset.univ.filter (boxes · = i), (x : ℕ) =
        ∑ x ∈ Finset.univ.filter (boxes · = j), (x : ℕ) := by
  rcases Nat.even_or_odd n with hEven | hOdd
  · rcases (even_iff_exists_two_mul.mp hEven) with ⟨r, rfl⟩
    have hr : 0 < r := by omega
    have hk : (2 * r + 1) / 2 = r := by omega
    rw [hk]
    exact putnam_2010_a1_lower_even r hr
  · rcases (odd_iff_exists_bit1.mp hOdd) with ⟨r, rfl⟩
    have hk : (2 * r + 1 + 1) / 2 = r + 1 := by omega
    rw [hk]
    exact putnam_2010_a1_lower_odd r

/--
Given a positive integer $n$, what is the largest $k$ such that the numbers $1,2,\dots,n$ can be put into $k$ boxes so that the sum of the numbers in each box is the same? [When $n=8$, the example $\{1,2,3,6\},\{4,8\},\{5,7\}$ shows that the largest $k$ is \emph{at least} $3$.]
-/
theorem putnam_2010_a1
    (n : ℕ)
    (kboxes : ℕ → Prop)
    (npos : n > 0)
    (hkboxes : ∀ k : ℕ, kboxes k =
      (∃ boxes : Finset.Icc 1 n → Fin k, ∀ i j : Fin k,
        ∑ x ∈ Finset.univ.filter (boxes · = i), (x : ℕ) =
        ∑ x ∈ Finset.univ.filter (boxes · = j), (x : ℕ))) :
    IsGreatest kboxes (putnam_2010_a1_solution n) :=
  by
  constructor
  · rw [putnam_2010_a1_solution_eq n]
    change kboxes ((n + 1) / 2)
    rw [hkboxes ((n + 1) / 2)]
    exact putnam_2010_a1_lower n npos
  · intro k hk
    rw [putnam_2010_a1_solution_eq n]
    change kboxes k at hk
    rw [hkboxes k] at hk
    rcases hk with ⟨boxes, heq⟩
    exact putnam_2010_a1_upper n k npos boxes heq
