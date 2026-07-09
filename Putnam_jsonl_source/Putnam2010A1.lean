import Mathlib

private lemma putnam_2010_a1_ceil_half_nat :
    ∀ n : ℕ, Nat.ceil ((n : ℝ) / 2) = (n + 1) / 2
  | 0 => by norm_num
  | 1 => by norm_num
  | n + 2 => by
      have hnonneg : 0 ≤ (n : ℝ) / 2 := by positivity
      rw [show (((n + 2 : ℕ) : ℝ) / 2) = (n : ℝ) / 2 + 1 by
        push_cast
        ring]
      rw [Nat.ceil_add_one hnonneg, putnam_2010_a1_ceil_half_nat n]
      omega

private lemma putnam_2010_a1_sum_Icc_one_id (n : ℕ) :
    (∑ x ∈ Finset.Icc 1 n, x) = n * (n + 1) / 2 := by
  calc
    (∑ x ∈ Finset.Icc 1 n, x) = ∑ x ∈ Finset.range (n + 1), x := by
      apply Finset.sum_subset
      · intro x hx
        have hx' : 1 ≤ x ∧ x ≤ n := by simpa using hx
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le hx'.2)
      · intro x hxrange hxnot
        by_cases hx0 : x = 0
        · simp [hx0]
        · exfalso
          have hxlt : x < n + 1 := Finset.mem_range.mp hxrange
          have hxle : x ≤ n := Nat.lt_succ_iff.mp hxlt
          have hxge : 1 ≤ x := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hx0)
          exact hxnot (by simp [hxge, hxle])
    _ = (n + 1) * ((n + 1) - 1) / 2 := by rw [Finset.sum_range_id]
    _ = n * (n + 1) / 2 := by
      have h : (n + 1) - 1 = n := by omega
      rw [h, Nat.mul_comm]

private def putnam_2010_a1_evenBoxes
    (m : ℕ) (x : Finset.Icc 1 (2 * m)) : Fin m :=
  if hx : (x : ℕ) ≤ m then
    ⟨(x : ℕ) - 1, by
      have hxmem := x.2
      simp only [Finset.mem_Icc] at hxmem
      omega⟩
  else
    ⟨2 * m - (x : ℕ), by
      have hxmem := x.2
      simp only [Finset.mem_Icc] at hxmem
      omega⟩

private lemma putnam_2010_a1_evenBoxes_fiber (m : ℕ) (i : Fin m) :
    (Finset.univ.filter (putnam_2010_a1_evenBoxes m · = i)) =
      ({⟨i.val + 1, by
          simp only [Finset.mem_Icc]
          omega⟩,
        ⟨2 * m - i.val, by
          simp only [Finset.mem_Icc]
          omega⟩} : Finset (Finset.Icc 1 (2 * m))) := by
  classical
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro hx
    by_cases hxm : (x : ℕ) ≤ m
    · have hx' : (⟨(x : ℕ) - 1, by
          have hxmem := x.2
          simp only [Finset.mem_Icc] at hxmem
          omega⟩ : Fin m) = i := by
        simpa [putnam_2010_a1_evenBoxes, hxm] using hx
      have hxval : (x : ℕ) - 1 = i.val := by simpa using congrArg Fin.val hx'
      left
      apply Subtype.ext
      change (x : ℕ) = i.val + 1
      have hxmem := x.2
      simp only [Finset.mem_Icc] at hxmem
      omega
    · have hx' : (⟨2 * m - (x : ℕ), by
          have hxmem := x.2
          simp only [Finset.mem_Icc] at hxmem
          omega⟩ : Fin m) = i := by
        simpa [putnam_2010_a1_evenBoxes, hxm] using hx
      have hxval : 2 * m - (x : ℕ) = i.val := by simpa using congrArg Fin.val hx'
      right
      apply Subtype.ext
      change (x : ℕ) = 2 * m - i.val
      have hxmem := x.2
      simp only [Finset.mem_Icc] at hxmem
      omega
  · intro hx
    rcases hx with hx | hx
    · subst x
      have hle : i.val + 1 ≤ m := by omega
      simp [putnam_2010_a1_evenBoxes, hle]
    · subst x
      have hle : ¬ 2 * m - i.val ≤ m := by omega
      simp [putnam_2010_a1_evenBoxes, hle]
      apply Fin.ext
      exact Nat.sub_sub_self (by omega : i.val ≤ 2 * m)

private lemma putnam_2010_a1_evenBoxes_sum (m : ℕ) (i : Fin m) :
    (∑ x ∈ Finset.univ.filter (putnam_2010_a1_evenBoxes m · = i), (x : ℕ)) =
      2 * m + 1 := by
  classical
  rw [putnam_2010_a1_evenBoxes_fiber]
  have hne : (⟨i.val + 1, by
          simp only [Finset.mem_Icc]
          omega⟩ : Finset.Icc 1 (2 * m)) ≠
        ⟨2 * m - i.val, by
          simp only [Finset.mem_Icc]
          omega⟩ := by
    intro h
    have hv : i.val + 1 = 2 * m - i.val := by simpa using congrArg Subtype.val h
    omega
  rw [Finset.sum_insert]
  · simp
    omega
  · simpa using hne

private def putnam_2010_a1_oddBoxes
    (m : ℕ) (x : Finset.Icc 1 (2 * m + 1)) : Fin (m + 1) :=
  if hlast : (x : ℕ) = 2 * m + 1 then
    ⟨m, by omega⟩
  else if hx : (x : ℕ) ≤ m then
    ⟨(x : ℕ) - 1, by
      have hxmem := x.2
      simp only [Finset.mem_Icc] at hxmem
      omega⟩
  else
    ⟨2 * m - (x : ℕ), by
      have hxmem := x.2
      simp only [Finset.mem_Icc] at hxmem
      omega⟩

private lemma putnam_2010_a1_oddBoxes_fiber_last (m : ℕ) :
    (Finset.univ.filter
        (putnam_2010_a1_oddBoxes m · = (⟨m, by omega⟩ : Fin (m + 1)))) =
      ({⟨2 * m + 1, by
          simp only [Finset.mem_Icc]
          omega⟩} : Finset (Finset.Icc 1 (2 * m + 1))) := by
  classical
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hx
    by_cases hlast : (x : ℕ) = 2 * m + 1
    · apply Subtype.ext
      change (x : ℕ) = 2 * m + 1
      exact hlast
    · by_cases hxm : (x : ℕ) ≤ m
      · have hx' : (⟨(x : ℕ) - 1, by
            have hxmem := x.2
            simp only [Finset.mem_Icc] at hxmem
            omega⟩ : Fin (m + 1)) = ⟨m, by omega⟩ := by
          simpa [putnam_2010_a1_oddBoxes, hlast, hxm] using hx
        have hxval : (x : ℕ) - 1 = m := by simpa using congrArg Fin.val hx'
        have hxmem := x.2
        simp only [Finset.mem_Icc] at hxmem
        omega
      · have hx' : (⟨2 * m - (x : ℕ), by
            have hxmem := x.2
            simp only [Finset.mem_Icc] at hxmem
            omega⟩ : Fin (m + 1)) = ⟨m, by omega⟩ := by
          simpa [putnam_2010_a1_oddBoxes, hlast, hxm] using hx
        have hxval : 2 * m - (x : ℕ) = m := by simpa using congrArg Fin.val hx'
        have hxmem := x.2
        simp only [Finset.mem_Icc] at hxmem
        omega
  · intro hx
    subst x
    simp [putnam_2010_a1_oddBoxes]

private lemma putnam_2010_a1_oddBoxes_fiber_pair
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val < m) :
    (Finset.univ.filter (putnam_2010_a1_oddBoxes m · = i)) =
      ({⟨i.val + 1, by
          simp only [Finset.mem_Icc]
          omega⟩,
        ⟨2 * m - i.val, by
          simp only [Finset.mem_Icc]
          omega⟩} : Finset (Finset.Icc 1 (2 * m + 1))) := by
  classical
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro hx
    by_cases hlast : (x : ℕ) = 2 * m + 1
    · have hx' : (⟨m, by omega⟩ : Fin (m + 1)) = i := by
        simpa [putnam_2010_a1_oddBoxes, hlast] using hx
      have hxval : m = i.val := by simpa using congrArg Fin.val hx'
      omega
    · by_cases hxm : (x : ℕ) ≤ m
      · have hx' : (⟨(x : ℕ) - 1, by
            have hxmem := x.2
            simp only [Finset.mem_Icc] at hxmem
            omega⟩ : Fin (m + 1)) = i := by
          simpa [putnam_2010_a1_oddBoxes, hlast, hxm] using hx
        have hxval : (x : ℕ) - 1 = i.val := by simpa using congrArg Fin.val hx'
        left
        apply Subtype.ext
        change (x : ℕ) = i.val + 1
        have hxmem := x.2
        simp only [Finset.mem_Icc] at hxmem
        omega
      · have hx' : (⟨2 * m - (x : ℕ), by
            have hxmem := x.2
            simp only [Finset.mem_Icc] at hxmem
            omega⟩ : Fin (m + 1)) = i := by
          simpa [putnam_2010_a1_oddBoxes, hlast, hxm] using hx
        have hxval : 2 * m - (x : ℕ) = i.val := by simpa using congrArg Fin.val hx'
        right
        apply Subtype.ext
        change (x : ℕ) = 2 * m - i.val
        have hxmem := x.2
        simp only [Finset.mem_Icc] at hxmem
        omega
  · intro hx
    rcases hx with hx | hx
    · subst x
      apply Fin.ext
      change (putnam_2010_a1_oddBoxes m (⟨i.val + 1, by
          simp only [Finset.mem_Icc]
          omega⟩ : Finset.Icc 1 (2 * m + 1))).val = i.val
      have hle : ((⟨i.val + 1, by
          simp only [Finset.mem_Icc]
          omega⟩ : Finset.Icc 1 (2 * m + 1)) : ℕ) ≤ m := by
        change i.val + 1 ≤ m
        omega
      simp [putnam_2010_a1_oddBoxes, hle]
      by_cases hbad : i.val = 2 * m
      · omega
      · simp [hbad]
    · subst x
      apply Fin.ext
      change (putnam_2010_a1_oddBoxes m (⟨2 * m - i.val, by
          simp only [Finset.mem_Icc]
          omega⟩ : Finset.Icc 1 (2 * m + 1))).val = i.val
      have hlast : ¬ ((⟨2 * m - i.val, by
          simp only [Finset.mem_Icc]
          omega⟩ : Finset.Icc 1 (2 * m + 1)) : ℕ) = 2 * m + 1 := by
        change ¬ 2 * m - i.val = 2 * m + 1
        omega
      have hle : ¬ ((⟨2 * m - i.val, by
          simp only [Finset.mem_Icc]
          omega⟩ : Finset.Icc 1 (2 * m + 1)) : ℕ) ≤ m := by
        change ¬ 2 * m - i.val ≤ m
        omega
      simp [putnam_2010_a1_oddBoxes, hlast, hle]
      exact Nat.sub_sub_self (by omega : i.val ≤ 2 * m)

private lemma putnam_2010_a1_oddBoxes_sum (m : ℕ) (i : Fin (m + 1)) :
    (∑ x ∈ Finset.univ.filter (putnam_2010_a1_oddBoxes m · = i), (x : ℕ)) =
      2 * m + 1 := by
  classical
  by_cases hi : i.val = m
  · have hi' : i = (⟨m, by omega⟩ : Fin (m + 1)) := by
      apply Fin.ext
      exact hi
    rw [hi']
    rw [putnam_2010_a1_oddBoxes_fiber_last]
    simp
  · have hilt : i.val < m := by omega
    rw [putnam_2010_a1_oddBoxes_fiber_pair m i hilt]
    have hne : (⟨i.val + 1, by
          simp only [Finset.mem_Icc]
          omega⟩ : Finset.Icc 1 (2 * m + 1)) ≠
        ⟨2 * m - i.val, by
          simp only [Finset.mem_Icc]
          omega⟩ := by
      intro h
      have hv : i.val + 1 = 2 * m - i.val := by simpa using congrArg Subtype.val h
      omega
    rw [Finset.sum_insert]
    · simp
      omega
    · simpa using hne

-- (fun n : ℕ => Nat.ceil ((n : ℝ) / 2))
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
    IsGreatest kboxes (((fun n : ℕ => Nat.ceil ((n : ℝ) / 2)) : ℕ → ℕ ) n) := by
  classical
  change IsGreatest kboxes (Nat.ceil ((n : ℝ) / 2))
  constructor
  · rw [putnam_2010_a1_ceil_half_nat]
    change kboxes ((n + 1) / 2)
    rw [hkboxes]
    rcases Nat.mod_two_eq_zero_or_one n with heven | hodd
    · have hn_eq : n = 2 * (n / 2) := by omega
      rw [hn_eq]
      have hk_eq : (2 * (n / 2) + 1) / 2 = n / 2 := by omega
      rw [hk_eq]
      use putnam_2010_a1_evenBoxes (n / 2)
      intro i j
      rw [putnam_2010_a1_evenBoxes_sum, putnam_2010_a1_evenBoxes_sum]
    · have hn_eq : n = 2 * (n / 2) + 1 := by omega
      rw [hn_eq]
      have hk_eq : (2 * (n / 2) + 1 + 1) / 2 = n / 2 + 1 := by omega
      rw [hk_eq]
      use putnam_2010_a1_oddBoxes (n / 2)
      intro i j
      rw [putnam_2010_a1_oddBoxes_sum, putnam_2010_a1_oddBoxes_sum]
  · intro k hk
    change kboxes k at hk
    rw [hkboxes k] at hk
    rcases hk with ⟨boxes, hboxes⟩
    rw [putnam_2010_a1_ceil_half_nat]
    let xn : Finset.Icc 1 n := ⟨n, by
      simp only [Finset.mem_Icc]
      omega⟩
    let i0 : Fin k := boxes xn
    let common : ℕ := ∑ x ∈ Finset.univ.filter (boxes · = i0), (x : ℕ)
    have hcommon_ge : n ≤ common := by
      have hxmem : xn ∈ Finset.univ.filter (boxes · = boxes xn) := by simp [xn]
      have hle : (xn : ℕ) ≤
          ∑ x ∈ Finset.univ.filter (boxes · = boxes xn), (x : ℕ) :=
        Finset.single_le_sum (fun x hx => by exact Nat.zero_le _) hxmem
      simpa [common, i0, xn] using hle
    have hsum_const :
        (∑ i : Fin k, ∑ x ∈ Finset.univ.filter (boxes · = i), (x : ℕ)) =
          k * common := by
      let S : Fin k → ℕ :=
        fun i => ∑ x ∈ Finset.univ.filter (boxes · = i), (x : ℕ)
      have hconst : ∀ i ∈ (Finset.univ : Finset (Fin k)), S i = common := by
        intro i hi
        exact hboxes i i0
      calc
        (∑ i : Fin k, ∑ x ∈ Finset.univ.filter (boxes · = i), (x : ℕ)) =
            ∑ i : Fin k, S i := rfl
        _ = (Finset.univ : Finset (Fin k)).card * common := by
          exact Finset.sum_const_nat (s := (Finset.univ : Finset (Fin k))) hconst
        _ = k * common := by simp [common]
    have hsum_fibers :
        (∑ i : Fin k, ∑ x ∈ Finset.univ.filter (boxes · = i), (x : ℕ)) =
          ∑ x : Finset.Icc 1 n, (x : ℕ) := by
      simpa using (Finset.sum_fiberwise_of_maps_to
        (s := (Finset.univ : Finset (Finset.Icc 1 n)))
        (t := (Finset.univ : Finset (Fin k)))
        (g := boxes)
        (by intro x hx; simp)
        (fun x : Finset.Icc 1 n => (x : ℕ)))
    have hdomain :
        (∑ x : Finset.Icc 1 n, (x : ℕ)) = ∑ x ∈ Finset.Icc 1 n, x := by
      rw [Finset.univ_eq_attach]
      simpa using (Finset.sum_attach (Finset.Icc 1 n) (fun x : ℕ => x))
    have htotal : k * common = n * (n + 1) / 2 := by
      calc
        k * common =
            (∑ i : Fin k, ∑ x ∈ Finset.univ.filter (boxes · = i), (x : ℕ)) :=
          hsum_const.symm
        _ = ∑ x : Finset.Icc 1 n, (x : ℕ) := hsum_fibers
        _ = ∑ x ∈ Finset.Icc 1 n, x := hdomain
        _ = n * (n + 1) / 2 := putnam_2010_a1_sum_Icc_one_id n
    have hkn : k * n ≤ n * (n + 1) / 2 := by
      calc
        k * n ≤ k * common := Nat.mul_le_mul_left k hcommon_ge
        _ = n * (n + 1) / 2 := htotal
    have htwice : 2 * (k * n) ≤ n * (n + 1) := by omega
    have hcancel : n * (2 * k) ≤ n * (n + 1) := by nlinarith
    have hk_le : 2 * k ≤ n + 1 := Nat.le_of_mul_le_mul_left hcancel npos
    omega
