import Mathlib

noncomputable abbrev putnam_2011_a1_solution : ℕ :=
  ({p : Fin 2 → Fin 2012 |
      p 0 = 0 ∨ (p 1 ≤ p 0 ∧ p 1 ≤ 3)} : Set (Fin 2 → Fin 2012)).ncard

set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false
set_option linter.constructorNameAsVariable false

def putnam_2011_a1_pt (x y : ℤ) : Fin 2 → ℤ := ![x, y]

def putnam_2011_a1_dx (a : ℕ → ℕ) (n : ℕ) : ℤ :=
  if n % 4 = 0 then (a n : ℤ) else if n % 4 = 2 then - (a n : ℤ) else 0

def putnam_2011_a1_dy (a : ℕ → ℕ) (n : ℕ) : ℤ :=
  if n % 4 = 1 then (a n : ℤ) else if n % 4 = 3 then - (a n : ℤ) else 0

def putnam_2011_a1_xval (a : ℕ → ℕ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => putnam_2011_a1_xval a n + putnam_2011_a1_dx a n

def putnam_2011_a1_yval (a : ℕ → ℕ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => putnam_2011_a1_yval a n + putnam_2011_a1_dy a n

def putnam_2011_a1_cur (P : List (Fin 2 → ℤ)) (i : Fin (P.length - 1)) : Fin 2 → ℤ :=
  P[(⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩ : Fin P.length)]

def putnam_2011_a1_cur_m (P : List (Fin 2 → ℤ)) (m : ℕ) (hm : m ≤ P.length)
    (i : Fin m) : Fin 2 → ℤ :=
  P[(⟨i.1, Nat.lt_of_lt_of_le i.2 hm⟩ : Fin P.length)]

abbrev putnam_2011_a1_IsSpiral_def_explicit
    (IsSpiral : List (Fin 2 → ℤ) → Prop) : Prop :=
  ∀ P, IsSpiral P ↔ P.length ≥ 3 ∧ P[0]! = 0 ∧
  (∃ l : Fin (P.length - 1) → ℕ, (∀ i, 0 < l i) ∧ StrictMono l ∧ (∀ i : Fin (P.length - 1),
    (i.1 % 4 = 0 → (putnam_2011_a1_cur P i 0 + l i = P[i.1 + 1]! 0 ∧ putnam_2011_a1_cur P i 1 = P[i.1 + 1]! 1)) ∧
    (i.1 % 4 = 1 → (putnam_2011_a1_cur P i 0 = P[i.1 + 1]! 0 ∧ putnam_2011_a1_cur P i 1 + l i = P[i.1 + 1]! 1)) ∧
    (i.1 % 4 = 2 → (putnam_2011_a1_cur P i 0 - l i = P[i.1 + 1]! 0 ∧ putnam_2011_a1_cur P i 1 = P[i.1 + 1]! 1)) ∧
    (i.1 % 4 = 3 → (putnam_2011_a1_cur P i 0 = P[i.1 + 1]! 0 ∧ putnam_2011_a1_cur P i 1 - l i = P[i.1 + 1]! 1))))

lemma putnam_2011_a1_getElem_fin_eq_getElem!
    {α : Type*} [Inhabited α] (P : List α) {n : ℕ} (h : n < P.length) :
    P[(⟨n, h⟩ : Fin P.length)] = P[n]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

lemma putnam_2011_a1_getLast!_eq_getElem!
    {α : Type*} [Inhabited α] (P : List α) :
    P.getLast! = P[P.length - 1]! := by
  cases P with
  | nil => rfl
  | cons a as =>
      change (a :: as).getLast (by simp) = (a :: as)[(a :: as).length - 1]!
      rw [List.getLast_eq_getElem]
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem]
      rfl

lemma putnam_2011_a1_coords
  (P : List (Fin 2 → ℤ)) (m : ℕ) (hm : m = P.length - 1)
  (hmle : m ≤ P.length)
  (h0 : P[0]! = 0)
  (l : Fin m → ℕ) (a : ℕ → ℕ)
  (ha : ∀ j (hj : j < m), a j = l ⟨j,hj⟩)
  (hsteps : ∀ i : Fin m,
    (i.1 % 4 = 0 → (putnam_2011_a1_cur_m P m hmle i 0 + l i = P[i.1 + 1]! 0 ∧
      putnam_2011_a1_cur_m P m hmle i 1 = P[i.1 + 1]! 1)) ∧
    (i.1 % 4 = 1 → (putnam_2011_a1_cur_m P m hmle i 0 = P[i.1 + 1]! 0 ∧
      putnam_2011_a1_cur_m P m hmle i 1 + l i = P[i.1 + 1]! 1)) ∧
    (i.1 % 4 = 2 → (putnam_2011_a1_cur_m P m hmle i 0 - l i = P[i.1 + 1]! 0 ∧
      putnam_2011_a1_cur_m P m hmle i 1 = P[i.1 + 1]! 1)) ∧
    (i.1 % 4 = 3 → (putnam_2011_a1_cur_m P m hmle i 0 = P[i.1 + 1]! 0 ∧
      putnam_2011_a1_cur_m P m hmle i 1 - l i = P[i.1 + 1]! 1))) :
  ∀ n, n ≤ m → P[n]! 0 = putnam_2011_a1_xval a n ∧
    P[n]! 1 = putnam_2011_a1_yval a n := by
  intro n hn
  induction n with
  | zero =>
      constructor
      · have hx := congr_fun h0 0
        simpa [putnam_2011_a1_xval] using hx
      · have hy := congr_fun h0 1
        simpa [putnam_2011_a1_yval] using hy
  | succ n ih =>
      have hnle : n ≤ m := Nat.le_of_succ_le hn
      have hnlt : n < m := Nat.lt_of_succ_le hn
      have hnPlt : n < P.length := by omega
      have hcur0 : P[(⟨n, hnPlt⟩ : Fin P.length)] 0 = P[n]! 0 := by
        rw [putnam_2011_a1_getElem_fin_eq_getElem! P hnPlt]
      have hcur1 : P[(⟨n, hnPlt⟩ : Fin P.length)] 1 = P[n]! 1 := by
        rw [putnam_2011_a1_getElem_fin_eq_getElem! P hnPlt]
      have hcurm0 :
          putnam_2011_a1_cur_m P m hmle ⟨n, hnlt⟩ 0 =
            P[(⟨n, hnPlt⟩ : Fin P.length)] 0 := by
        simp [putnam_2011_a1_cur_m]
      have hcurm1 :
          putnam_2011_a1_cur_m P m hmle ⟨n, hnlt⟩ 1 =
            P[(⟨n, hnPlt⟩ : Fin P.length)] 1 := by
        simp [putnam_2011_a1_cur_m]
      have ih' := ih hnle
      have hs := hsteps ⟨n, hnlt⟩
      have ha' : a n = l ⟨n, hnlt⟩ := ha n hnlt
      have hmodlt : n % 4 < 4 := Nat.mod_lt n (by norm_num)
      interval_cases hmod : n % 4
      · have he := hs.1 rfl
        constructor
        · calc
            P[n + 1]! 0 = putnam_2011_a1_cur_m P m hmle ⟨n, hnlt⟩ 0 + l ⟨n, hnlt⟩ := he.1.symm
            _ = P[(⟨n, hnPlt⟩ : Fin P.length)] 0 + l ⟨n, hnlt⟩ := by rw [hcurm0]
            _ = P[n]! 0 + l ⟨n, hnlt⟩ := by rw [hcur0]
            _ = putnam_2011_a1_xval a n + a n := by rw [ih'.1, ha']
            _ = putnam_2011_a1_xval a (n + 1) := by
              simp [putnam_2011_a1_xval, putnam_2011_a1_dx, hmod]
        · calc
            P[n + 1]! 1 = putnam_2011_a1_cur_m P m hmle ⟨n, hnlt⟩ 1 := he.2.symm
            _ = P[(⟨n, hnPlt⟩ : Fin P.length)] 1 := by rw [hcurm1]
            _ = P[n]! 1 := by rw [hcur1]
            _ = putnam_2011_a1_yval a n := ih'.2
            _ = putnam_2011_a1_yval a (n + 1) := by
              simp [putnam_2011_a1_yval, putnam_2011_a1_dy, hmod]
      · have he := hs.2.1 rfl
        constructor
        · calc
            P[n + 1]! 0 = putnam_2011_a1_cur_m P m hmle ⟨n, hnlt⟩ 0 := he.1.symm
            _ = P[(⟨n, hnPlt⟩ : Fin P.length)] 0 := by rw [hcurm0]
            _ = P[n]! 0 := by rw [hcur0]
            _ = putnam_2011_a1_xval a n := ih'.1
            _ = putnam_2011_a1_xval a (n + 1) := by
              simp [putnam_2011_a1_xval, putnam_2011_a1_dx, hmod]
        · calc
            P[n + 1]! 1 = putnam_2011_a1_cur_m P m hmle ⟨n, hnlt⟩ 1 + l ⟨n, hnlt⟩ := he.2.symm
            _ = P[(⟨n, hnPlt⟩ : Fin P.length)] 1 + l ⟨n, hnlt⟩ := by rw [hcurm1]
            _ = P[n]! 1 + l ⟨n, hnlt⟩ := by rw [hcur1]
            _ = putnam_2011_a1_yval a n + a n := by rw [ih'.2, ha']
            _ = putnam_2011_a1_yval a (n + 1) := by
              simp [putnam_2011_a1_yval, putnam_2011_a1_dy, hmod]
      · have he := hs.2.2.1 rfl
        constructor
        · calc
            P[n + 1]! 0 = putnam_2011_a1_cur_m P m hmle ⟨n, hnlt⟩ 0 - l ⟨n, hnlt⟩ := he.1.symm
            _ = P[(⟨n, hnPlt⟩ : Fin P.length)] 0 - l ⟨n, hnlt⟩ := by rw [hcurm0]
            _ = P[n]! 0 - l ⟨n, hnlt⟩ := by rw [hcur0]
            _ = putnam_2011_a1_xval a n - a n := by rw [ih'.1, ha']
            _ = putnam_2011_a1_xval a (n + 1) := by
              simp [putnam_2011_a1_xval, putnam_2011_a1_dx, hmod, sub_eq_add_neg]
        · calc
            P[n + 1]! 1 = putnam_2011_a1_cur_m P m hmle ⟨n, hnlt⟩ 1 := he.2.symm
            _ = P[(⟨n, hnPlt⟩ : Fin P.length)] 1 := by rw [hcurm1]
            _ = P[n]! 1 := by rw [hcur1]
            _ = putnam_2011_a1_yval a n := ih'.2
            _ = putnam_2011_a1_yval a (n + 1) := by
              simp [putnam_2011_a1_yval, putnam_2011_a1_dy, hmod]
      · have he := hs.2.2.2 rfl
        constructor
        · calc
            P[n + 1]! 0 = putnam_2011_a1_cur_m P m hmle ⟨n, hnlt⟩ 0 := he.1.symm
            _ = P[(⟨n, hnPlt⟩ : Fin P.length)] 0 := by rw [hcurm0]
            _ = P[n]! 0 := by rw [hcur0]
            _ = putnam_2011_a1_xval a n := ih'.1
            _ = putnam_2011_a1_xval a (n + 1) := by
              simp [putnam_2011_a1_xval, putnam_2011_a1_dx, hmod]
        · calc
            P[n + 1]! 1 = putnam_2011_a1_cur_m P m hmle ⟨n, hnlt⟩ 1 - l ⟨n, hnlt⟩ := he.2.symm
            _ = P[(⟨n, hnPlt⟩ : Fin P.length)] 1 - l ⟨n, hnlt⟩ := by rw [hcurm1]
            _ = P[n]! 1 - l ⟨n, hnlt⟩ := by rw [hcur1]
            _ = putnam_2011_a1_yval a n - a n := by rw [ih'.2, ha']
            _ = putnam_2011_a1_yval a (n + 1) := by
              simp [putnam_2011_a1_yval, putnam_2011_a1_dy, hmod, sub_eq_add_neg]

lemma putnam_2011_a1_xval_step_pos (a : ℕ → ℕ) (k : ℕ) :
    putnam_2011_a1_xval a (4 * k + 5) =
      putnam_2011_a1_xval a (4 * k + 1) - (a (4 * k + 2) : ℤ) + a (4 * k + 4) := by
  simp [putnam_2011_a1_xval, putnam_2011_a1_dx]
  ring

lemma putnam_2011_a1_xval_step_neg (a : ℕ → ℕ) (k : ℕ) :
    putnam_2011_a1_xval a (4 * k + 7) =
      putnam_2011_a1_xval a (4 * k + 3) + (a (4 * k + 4) : ℤ) - a (4 * k + 6) := by
  simp [putnam_2011_a1_xval, putnam_2011_a1_dx]
  ring

lemma putnam_2011_a1_yval_step_pos (a : ℕ → ℕ) (k : ℕ) :
    putnam_2011_a1_yval a (4 * k + 6) =
      putnam_2011_a1_yval a (4 * k + 2) - (a (4 * k + 3) : ℤ) + a (4 * k + 5) := by
  simp [putnam_2011_a1_yval, putnam_2011_a1_dy]
  ring

lemma putnam_2011_a1_yval_step_neg (a : ℕ → ℕ) (k : ℕ) :
    putnam_2011_a1_yval a (4 * k + 8) =
      putnam_2011_a1_yval a (4 * k + 4) + (a (4 * k + 5) : ℤ) - a (4 * k + 7) := by
  simp [putnam_2011_a1_yval, putnam_2011_a1_dy]
  ring

lemma putnam_2011_a1_xval_pos_1 (a : ℕ → ℕ)
    (hpos : ∀ i, 0 < a i) (hmono : StrictMono a) :
    ∀ k : ℕ, 0 < putnam_2011_a1_xval a (4 * k + 1)
  | 0 => by simpa [putnam_2011_a1_xval, putnam_2011_a1_dx] using hpos 0
  | k + 1 => by
      rw [show 4 * (k + 1) + 1 = 4 * k + 5 by omega]
      rw [putnam_2011_a1_xval_step_pos]
      have ih := putnam_2011_a1_xval_pos_1 a hpos hmono k
      have hlt : (a (4 * k + 2) : ℤ) < a (4 * k + 4) := by
        exact_mod_cast hmono (by omega : 4 * k + 2 < 4 * k + 4)
      linarith

lemma putnam_2011_a1_xval_pos_2 (a : ℕ → ℕ)
    (hpos : ∀ i, 0 < a i) (hmono : StrictMono a) :
    ∀ k : ℕ, 0 < putnam_2011_a1_xval a (4 * k + 2) := by
  intro k
  have h := putnam_2011_a1_xval_pos_1 a hpos hmono k
  convert h using 1
  simp [putnam_2011_a1_xval, putnam_2011_a1_dx]

lemma putnam_2011_a1_xval_neg_3 (a : ℕ → ℕ) (hmono : StrictMono a) :
    ∀ k : ℕ, putnam_2011_a1_xval a (4 * k + 3) < 0
  | 0 => by
      have hlt : (a 0 : ℤ) < a 2 := by
        exact_mod_cast hmono (by norm_num : 0 < 2)
      simp [putnam_2011_a1_xval, putnam_2011_a1_dx]
      linarith
  | k + 1 => by
      rw [show 4 * (k + 1) + 3 = 4 * k + 7 by omega]
      rw [putnam_2011_a1_xval_step_neg]
      have ih := putnam_2011_a1_xval_neg_3 a hmono k
      have hlt : (a (4 * k + 4) : ℤ) < a (4 * k + 6) := by
        exact_mod_cast hmono (by omega : 4 * k + 4 < 4 * k + 6)
      linarith

lemma putnam_2011_a1_xval_neg_4 (a : ℕ → ℕ) (hmono : StrictMono a) :
    ∀ k : ℕ, putnam_2011_a1_xval a (4 * k + 4) < 0 := by
  intro k
  have h := putnam_2011_a1_xval_neg_3 a hmono k
  convert h using 1
  simp [putnam_2011_a1_xval, putnam_2011_a1_dx]

lemma putnam_2011_a1_yval_pos_2 (a : ℕ → ℕ)
    (hpos : ∀ i, 0 < a i) (hmono : StrictMono a) :
    ∀ k : ℕ, 0 < putnam_2011_a1_yval a (4 * k + 2)
  | 0 => by
      have hlt : (0 : ℤ) < a 1 := by exact_mod_cast hpos 1
      simpa [putnam_2011_a1_yval, putnam_2011_a1_dy] using hlt
  | k + 1 => by
      rw [show 4 * (k + 1) + 2 = 4 * k + 6 by omega]
      rw [putnam_2011_a1_yval_step_pos]
      have ih := putnam_2011_a1_yval_pos_2 a hpos hmono k
      have hlt : (a (4 * k + 3) : ℤ) < a (4 * k + 5) := by
        exact_mod_cast hmono (by omega : 4 * k + 3 < 4 * k + 5)
      linarith

lemma putnam_2011_a1_yval_neg_4 (a : ℕ → ℕ) (hmono : StrictMono a) :
    ∀ k : ℕ, putnam_2011_a1_yval a (4 * k + 4) < 0
  | 0 => by
      have hlt : (a 1 : ℤ) < a 3 := by
        exact_mod_cast hmono (by norm_num : 1 < 3)
      simp [putnam_2011_a1_yval, putnam_2011_a1_dy]
      linarith
  | k + 1 => by
      rw [show 4 * (k + 1) + 4 = 4 * k + 8 by omega]
      rw [putnam_2011_a1_yval_step_neg]
      have ih := putnam_2011_a1_yval_neg_4 a hmono k
      have hlt : (a (4 * k + 5) : ℤ) < a (4 * k + 7) := by
        exact_mod_cast hmono (by omega : 4 * k + 5 < 4 * k + 7)
      linarith

lemma putnam_2011_a1_yval_neg_5 (a : ℕ → ℕ) (hmono : StrictMono a) :
    ∀ k : ℕ, putnam_2011_a1_yval a (4 * k + 5) < 0 := by
  intro k
  have h := putnam_2011_a1_yval_neg_4 a hmono k
  convert h using 1
  simp [putnam_2011_a1_yval, putnam_2011_a1_dy]

lemma putnam_2011_a1_yval_lower_2 (a : ℕ → ℕ)
    (hpos : ∀ i, 0 < a i) (hmono : StrictMono a) :
    ∀ k : ℕ, (2 + 2 * k : ℤ) ≤ putnam_2011_a1_yval a (4 * k + 2)
  | 0 => by
      have h0 : 0 < a 0 := hpos 0
      have h01 : a 0 < a 1 := hmono (by norm_num : 0 < 1)
      simp [putnam_2011_a1_yval, putnam_2011_a1_dy]
      omega
  | k + 1 => by
      rw [show 4 * (k + 1) + 2 = 4 * k + 6 by omega]
      rw [putnam_2011_a1_yval_step_pos]
      have ih := putnam_2011_a1_yval_lower_2 a hpos hmono k
      have h34 : a (4 * k + 3) < a (4 * k + 4) := hmono (by omega)
      have h45 : a (4 * k + 4) < a (4 * k + 5) := hmono (by omega)
      have hdiff : (2 : ℤ) ≤ (a (4 * k + 5) : ℤ) - a (4 * k + 3) := by
        omega
      have hks : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by norm_num
      nlinarith

lemma putnam_2011_a1_yval_two_gt_xval_two
    (a : ℕ → ℕ) (hmono : StrictMono a) :
    putnam_2011_a1_yval a 2 > putnam_2011_a1_xval a 2 := by
  have h01 : a 0 < a 1 := hmono (by norm_num : 0 < 1)
  simpa [putnam_2011_a1_xval, putnam_2011_a1_yval,
    putnam_2011_a1_dx, putnam_2011_a1_dy] using h01

lemma putnam_2011_a1_extend_strict {m : ℕ} (hm : 2 ≤ m) (l : Fin m → ℕ)
    (hpos : ∀ i, 0 < l i) (hl : StrictMono l) :
  let last : Fin m := ⟨m - 1, by omega⟩
  let a : ℕ → ℕ := fun j => if h : j < m then l ⟨j,h⟩ else l last + (j - m + 1)
  (∀ j, 0 < a j) ∧ StrictMono a ∧ (∀ j (hj : j < m), a j = l ⟨j,hj⟩) := by
  intro last a
  have hlastpos : 0 < l last := hpos last
  refine ⟨?_, ?_, ?_⟩
  · intro j
    by_cases hj : j < m
    · simpa [a, hj] using hpos ⟨j,hj⟩
    · simp [a, hj, hlastpos]
  · intro i j hij
    by_cases hj : j < m
    · have hi : i < m := lt_trans hij hj
      simpa [a, hi, hj] using hl (show (⟨i,hi⟩ : Fin m) < ⟨j,hj⟩ from hij)
    · by_cases hi : i < m
      · have hle_last : l ⟨i,hi⟩ ≤ l last := by
          by_cases heq : i = m - 1
          · subst heq
            rfl
          · have hilt : i < m - 1 := by omega
            exact le_of_lt (hl (show (⟨i,hi⟩ : Fin m) < last from hilt))
        simp [a, hi, hj]
        omega
      · simp [a, hi, hj]
        omega
  · intro j hj
    simp [a, hj]

lemma putnam_2011_a1_endpoint_restriction
  (IsSpiral : List (Fin 2 → ℤ) → Prop)
  (IsSpiral_def : putnam_2011_a1_IsSpiral_def_explicit IsSpiral)
  {p : Fin 2 → ℤ} (hp0 : 0 ≤ p 0) (hp1 : 0 ≤ p 1)
  (hex : ∃ spiral, IsSpiral spiral ∧ spiral.getLast! = p) :
  0 < p 0 ∧ 0 < p 1 ∧ (p 1 ≤ 3 → p 0 < p 1) := by
  rcases hex with ⟨P, hP, hlast⟩
  rcases (IsSpiral_def P).mp hP with ⟨hlen, hzero, l, hposl, hmonol, hsteps⟩
  let m := P.length - 1
  have hmdef : m = P.length - 1 := rfl
  have hm2 : 2 ≤ m := by omega
  let lastFin : Fin m := ⟨m - 1, by omega⟩
  let a : ℕ → ℕ := fun j => if h : j < m then l ⟨j,h⟩ else l lastFin + (j - m + 1)
  have ha_pack := putnam_2011_a1_extend_strict hm2 l hposl hmonol
  have hposa : ∀ j, 0 < a j := by simpa [lastFin, a] using ha_pack.1
  have hmonoa : StrictMono a := by simpa [lastFin, a] using ha_pack.2.1
  have haa : ∀ j (hj : j < m), a j = l ⟨j,hj⟩ := by
    simpa [lastFin, a] using ha_pack.2.2
  have hmle : m ≤ P.length := by
    rw [hmdef]
    exact Nat.sub_le P.length 1
  have hsteps_for_coords : ∀ i : Fin m,
    (i.1 % 4 = 0 → (putnam_2011_a1_cur_m P m hmle i 0 + l i = P[i.1 + 1]! 0 ∧
      putnam_2011_a1_cur_m P m hmle i 1 = P[i.1 + 1]! 1)) ∧
    (i.1 % 4 = 1 → (putnam_2011_a1_cur_m P m hmle i 0 = P[i.1 + 1]! 0 ∧
      putnam_2011_a1_cur_m P m hmle i 1 + l i = P[i.1 + 1]! 1)) ∧
    (i.1 % 4 = 2 → (putnam_2011_a1_cur_m P m hmle i 0 - l i = P[i.1 + 1]! 0 ∧
      putnam_2011_a1_cur_m P m hmle i 1 = P[i.1 + 1]! 1)) ∧
    (i.1 % 4 = 3 → (putnam_2011_a1_cur_m P m hmle i 0 = P[i.1 + 1]! 0 ∧
      putnam_2011_a1_cur_m P m hmle i 1 - l i = P[i.1 + 1]! 1)) := by
    simpa [m, putnam_2011_a1_cur, putnam_2011_a1_cur_m] using hsteps
  have hcoord := putnam_2011_a1_coords P m hmdef hmle hzero l a haa hsteps_for_coords m (le_refl m)
  have hlastidx : P.getLast! = P[m]! := by
    simpa [m] using putnam_2011_a1_getLast!_eq_getElem! P
  have hPm : P[m]! = p := by
    rw [← hlastidx]
    exact hlast
  have hx : p 0 = putnam_2011_a1_xval a m := by
    rw [← congr_fun hPm 0]
    exact hcoord.1
  have hy : p 1 = putnam_2011_a1_yval a m := by
    rw [← congr_fun hPm 1]
    exact hcoord.2
  have hmodlt : m % 4 < 4 := Nat.mod_lt m (by norm_num)
  interval_cases hmod : m % 4
  · obtain ⟨k, hk⟩ : ∃ k, m = 4 * k + 4 := by
      use m / 4 - 1
      omega
    have hxneg : putnam_2011_a1_xval a m < 0 := by
      rw [hk]
      exact putnam_2011_a1_xval_neg_4 a hmonoa k
    have : p 0 < 0 := by rwa [hx]
    omega
  · obtain ⟨k, hk⟩ : ∃ k, m = 4 * k + 5 := by
      use m / 4 - 1
      omega
    have hyneg : putnam_2011_a1_yval a m < 0 := by
      rw [hk]
      exact putnam_2011_a1_yval_neg_5 a hmonoa k
    have : p 1 < 0 := by rwa [hy]
    omega
  · obtain ⟨k, hk⟩ : ∃ k, m = 4 * k + 2 := by
      use m / 4
      omega
    have hxpos : 0 < p 0 := by
      rw [hx, hk]
      exact putnam_2011_a1_xval_pos_2 a hposa hmonoa k
    have hypos : 0 < p 1 := by
      rw [hy, hk]
      exact putnam_2011_a1_yval_pos_2 a hposa hmonoa k
    refine ⟨hxpos, hypos, ?_⟩
    intro hyle
    by_cases hk0 : k = 0
    · subst hk0
      have hgt : putnam_2011_a1_xval a 2 < putnam_2011_a1_yval a 2 :=
        putnam_2011_a1_yval_two_gt_xval_two a hmonoa
      rw [hk] at hx hy
      have hx2 : p 0 = putnam_2011_a1_xval a 2 := by simpa using hx
      have hy2 : p 1 = putnam_2011_a1_yval a 2 := by simpa using hy
      omega
    · have hylower : (4 : ℤ) ≤ p 1 := by
        rw [hy, hk]
        have hlow := putnam_2011_a1_yval_lower_2 a hposa hmonoa k
        omega
      omega
  · obtain ⟨k, hk⟩ : ∃ k, m = 4 * k + 3 := by
      use m / 4
      omega
    have hxneg : putnam_2011_a1_xval a m < 0 := by
      rw [hk]
      exact putnam_2011_a1_xval_neg_3 a hmonoa k
    have : p 0 < 0 := by rwa [hx]
    omega

def putnam_2011_a1_spiral2 (x y : ℕ) : List (Fin 2 → ℤ) :=
  [putnam_2011_a1_pt 0 0, putnam_2011_a1_pt x 0, putnam_2011_a1_pt x y]

def putnam_2011_a1_spiral6 (x y : ℕ) : List (Fin 2 → ℤ) :=
  [ putnam_2011_a1_pt 0 0,
    putnam_2011_a1_pt 1 0,
    putnam_2011_a1_pt 1 2,
    putnam_2011_a1_pt (-2) 2,
    putnam_2011_a1_pt (-2) ((y : ℤ) - (x : ℤ) - 3),
    putnam_2011_a1_pt x ((y : ℤ) - (x : ℤ) - 3),
    putnam_2011_a1_pt x y]

lemma putnam_2011_a1_exists_spiral2
  (IsSpiral : List (Fin 2 → ℤ) → Prop)
  (IsSpiral_def : putnam_2011_a1_IsSpiral_def_explicit IsSpiral)
  {x y : ℕ} (hx : 0 < x) (hxy : x < y) :
  ∃ spiral, IsSpiral spiral ∧ spiral.getLast! = putnam_2011_a1_pt x y := by
  refine ⟨putnam_2011_a1_spiral2 x y, ?_, ?_⟩
  · rw [IsSpiral_def]
    refine ⟨by simp [putnam_2011_a1_spiral2], ?_, ?_⟩
    · ext i <;> fin_cases i <;> simp [putnam_2011_a1_spiral2, putnam_2011_a1_pt]
    · refine ⟨(![x, y] : Fin 2 → ℕ), ?_, ?_, ?_⟩
      · intro i
        fin_cases i <;> simp [hx, Nat.lt_trans hx hxy]
      · intro a b hab
        fin_cases a <;> fin_cases b <;> simp at hab ⊢
        exact hxy
      · intro i
        fin_cases i <;> simp [putnam_2011_a1_spiral2, putnam_2011_a1_pt, putnam_2011_a1_cur]
  · simp [putnam_2011_a1_spiral2, putnam_2011_a1_pt]

lemma putnam_2011_a1_exists_spiral6
  (IsSpiral : List (Fin 2 → ℤ) → Prop)
  (IsSpiral_def : putnam_2011_a1_IsSpiral_def_explicit IsSpiral)
  {x y : ℕ} (hx : 3 ≤ x) (hy : 4 ≤ y) (hyx : y ≤ x) :
  ∃ spiral, IsSpiral spiral ∧ spiral.getLast! = putnam_2011_a1_pt x y := by
  refine ⟨putnam_2011_a1_spiral6 x y, ?_, ?_⟩
  · rw [IsSpiral_def]
    refine ⟨by simp [putnam_2011_a1_spiral6], ?_, ?_⟩
    · ext i <;> fin_cases i <;> simp [putnam_2011_a1_spiral6, putnam_2011_a1_pt]
    · refine ⟨(![1, 2, 3, x - y + 5, x + 2, x + 3] : Fin 6 → ℕ), ?_, ?_, ?_⟩
      · intro i
        fin_cases i <;> simp
      · intro a b hab
        fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> omega
      · intro i
        fin_cases i <;> simp [putnam_2011_a1_spiral6, putnam_2011_a1_pt, putnam_2011_a1_cur] <;> omega
  · simp [putnam_2011_a1_spiral6, putnam_2011_a1_pt]

lemma putnam_2011_a1_reachable_of_lt
  (IsSpiral : List (Fin 2 → ℤ) → Prop)
  (IsSpiral_def : putnam_2011_a1_IsSpiral_def_explicit IsSpiral)
  {p : Fin 2 → ℤ} (hx : 0 < p 0) (hxy : p 0 < p 1) :
  ∃ spiral, IsSpiral spiral ∧ spiral.getLast! = p := by
  let x := (p 0).toNat
  let y := (p 1).toNat
  have hxcast : (x : ℤ) = p 0 := Int.toNat_of_nonneg (le_of_lt hx)
  have hycast : (y : ℤ) = p 1 := Int.toNat_of_nonneg (by omega)
  have hxnat : 0 < x := by omega
  have hxynat : x < y := by omega
  rcases putnam_2011_a1_exists_spiral2 IsSpiral IsSpiral_def hxnat hxynat with ⟨s, hs, hlast⟩
  refine ⟨s, hs, ?_⟩
  rw [hlast]
  ext i <;> fin_cases i <;> simp [putnam_2011_a1_pt, hxcast, hycast]

lemma putnam_2011_a1_reachable_of_large
  (IsSpiral : List (Fin 2 → ℤ) → Prop)
  (IsSpiral_def : putnam_2011_a1_IsSpiral_def_explicit IsSpiral)
  {p : Fin 2 → ℤ} (hx : 3 ≤ p 0) (hy : 4 ≤ p 1) (hyx : p 1 ≤ p 0) :
  ∃ spiral, IsSpiral spiral ∧ spiral.getLast! = p := by
  let x := (p 0).toNat
  let y := (p 1).toNat
  have hxcast : (x : ℤ) = p 0 := Int.toNat_of_nonneg (by omega)
  have hycast : (y : ℤ) = p 1 := Int.toNat_of_nonneg (by omega)
  have hxnat : 3 ≤ x := by omega
  have hynat : 4 ≤ y := by omega
  have hyxnat : y ≤ x := by omega
  rcases putnam_2011_a1_exists_spiral6 IsSpiral IsSpiral_def hxnat hynat hyxnat with ⟨s, hs, hlast⟩
  refine ⟨s, hs, ?_⟩
  rw [hlast]
  ext i <;> fin_cases i <;> simp [putnam_2011_a1_pt, hxcast, hycast]

abbrev putnam_2011_a1_badIndex :=
  Fin 2012 ⊕ (Fin 2011 ⊕ (Fin 2011 ⊕ (Fin 2010 ⊕ Fin 2009)))

def putnam_2011_a1_badPoint : putnam_2011_a1_badIndex → Fin 2 → ℤ
  | Sum.inl y => putnam_2011_a1_pt 0 y.1
  | Sum.inr (Sum.inl x) => putnam_2011_a1_pt (x.1 + 1) 0
  | Sum.inr (Sum.inr (Sum.inl x)) => putnam_2011_a1_pt (x.1 + 1) 1
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl x))) => putnam_2011_a1_pt (x.1 + 2) 2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr x))) => putnam_2011_a1_pt (x.1 + 3) 3

def putnam_2011_a1_badFinset : Finset (Fin 2 → ℤ) :=
  Finset.univ.image putnam_2011_a1_badPoint

def putnam_2011_a1_badPred (p : Fin 2 → ℤ) : Prop :=
  (p 0 = 0 ∧ 0 ≤ p 1 ∧ p 1 ≤ 2011) ∨
  (p 1 = 0 ∧ 1 ≤ p 0 ∧ p 0 ≤ 2011) ∨
  (p 1 = 1 ∧ 1 ≤ p 0 ∧ p 0 ≤ 2011) ∨
  (p 1 = 2 ∧ 2 ≤ p 0 ∧ p 0 ≤ 2011) ∨
  (p 1 = 3 ∧ 3 ≤ p 0 ∧ p 0 ≤ 2011)

lemma putnam_2011_a1_badPoint_inj :
    Function.Injective putnam_2011_a1_badPoint := by
  intro a b h
  cases a with
  | inl ya =>
      cases b with
      | inl yb =>
          congr
          have hy := congr_fun h 1
          simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt] at hy
          exact Fin.ext (by omega)
      | inr rb =>
          cases rb with
          | inl xb =>
              have hx := congr_fun h 0
              simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt] at hx
              omega
          | inr rb2 =>
              cases rb2 with
              | inl xb =>
                  have hx := congr_fun h 0
                  simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt] at hx
                  omega
              | inr rb3 =>
                  cases rb3 with
                  | inl xb =>
                      have hx := congr_fun h 0
                      simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt] at hx
                      omega
                  | inr xb =>
                      have hx := congr_fun h 0
                      simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt] at hx
                      omega
  | inr ra =>
      cases ra with
      | inl xa =>
          cases b with
          | inl yb =>
              have hx := congr_fun h 0
              simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt] at hx
              omega
          | inr rb =>
              cases rb with
              | inl xb =>
                  congr
                  have hx := congr_fun h 0
                  simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt] at hx
                  exact Fin.ext (by omega)
              | inr rb2 =>
                  cases rb2 with
                  | inl xb =>
                      have hy := congr_fun h 1
                      simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt] at hy
                  | inr rb3 =>
                      cases rb3 with
                      | inl xb =>
                          have hy := congr_fun h 1
                          simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt] at hy
                      | inr xb =>
                          have hy := congr_fun h 1
                          simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt] at hy
      | inr ra2 =>
          cases ra2 with
          | inl xa =>
              cases b with
              | inl yb =>
                  have hx := congr_fun h 0
                  simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt] at hx
                  omega
              | inr rb =>
                  cases rb with
                  | inl xb =>
                      have hy := congr_fun h 1
                      simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt] at hy
                  | inr rb2 =>
                      cases rb2 with
                      | inl xb =>
                          congr
                          have hx := congr_fun h 0
                          simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt] at hx
                          exact Fin.ext (by omega)
                      | inr rb3 =>
                          cases rb3 with
                          | inl xb =>
                              have hy := congr_fun h 1
                              simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt] at hy
                          | inr xb =>
                              have hy := congr_fun h 1
                              simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt] at hy
          | inr ra3 =>
              cases ra3 with
              | inl xa =>
                  cases b with
                  | inl yb =>
                      have hx := congr_fun h 0
                      simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt] at hx
                      omega
                  | inr rb =>
                      cases rb with
                      | inl xb =>
                          have hy := congr_fun h 1
                          simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt] at hy
                      | inr rb2 =>
                          cases rb2 with
                          | inl xb =>
                              have hy := congr_fun h 1
                              simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt] at hy
                          | inr rb3 =>
                              cases rb3 with
                              | inl xb =>
                                  congr
                                  have hx := congr_fun h 0
                                  simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt] at hx
                                  exact Fin.ext (by omega)
                              | inr xb =>
                                  have hy := congr_fun h 1
                                  simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt] at hy
              | inr xa =>
                  cases b with
                  | inl yb =>
                      have hx := congr_fun h 0
                      simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt] at hx
                      omega
                  | inr rb =>
                      cases rb with
                      | inl xb =>
                          have hy := congr_fun h 1
                          simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt] at hy
                      | inr rb2 =>
                          cases rb2 with
                          | inl xb =>
                              have hy := congr_fun h 1
                              simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt] at hy
                          | inr rb3 =>
                              cases rb3 with
                              | inl xb =>
                                  have hy := congr_fun h 1
                                  simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt] at hy
                              | inr xb =>
                                  congr
                                  have hx := congr_fun h 0
                                  simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt] at hx
                                  exact Fin.ext (by omega)

lemma putnam_2011_a1_mem_badFinset_iff (p : Fin 2 → ℤ) :
    p ∈ putnam_2011_a1_badFinset ↔ putnam_2011_a1_badPred p := by
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨i, -, rfl⟩
    cases i with
    | inl y =>
        left
        simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt] <;> omega
    | inr r =>
        cases r with
        | inl x =>
            right; left
            simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt] <;> omega
        | inr r2 =>
            cases r2 with
            | inl x =>
                right; right; left
                simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt] <;> omega
            | inr r3 =>
                cases r3 with
                | inl x =>
                    right; right; right; left
                    simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt] <;> omega
                | inr x =>
                    right; right; right; right
                    simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt] <;> omega
  · intro hp
    rcases hp with h | h | h | h | h
    · rcases h with ⟨hx, hy0, hy1⟩
      refine Finset.mem_image.mpr ⟨Sum.inl ⟨(p 1).toNat, ?_⟩, by simp, ?_⟩
      · have hyNat : (p 1).toNat ≤ 2011 := by omega
        omega
      · have hyEq : ((p 1).toNat : ℤ) = p 1 := Int.toNat_of_nonneg hy0
        ext i <;> fin_cases i <;> simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt, hx, hyEq]
    · rcases h with ⟨hy, hx0, hx1⟩
      refine Finset.mem_image.mpr ⟨Sum.inr (Sum.inl ⟨(p 0 - 1).toNat, ?_⟩), by simp, ?_⟩
      · have : (p 0 - 1).toNat ≤ 2010 := by omega
        omega
      · have hxnon : 0 ≤ p 0 - 1 := by omega
        have hxEq : ((p 0 - 1).toNat : ℤ) = p 0 - 1 := Int.toNat_of_nonneg hxnon
        ext i <;> fin_cases i <;> simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt, hy] <;> omega
    · rcases h with ⟨hy, hx0, hx1⟩
      refine Finset.mem_image.mpr ⟨Sum.inr (Sum.inr (Sum.inl ⟨(p 0 - 1).toNat, ?_⟩)), by simp, ?_⟩
      · have : (p 0 - 1).toNat ≤ 2010 := by omega
        omega
      · have hxnon : 0 ≤ p 0 - 1 := by omega
        have hxEq : ((p 0 - 1).toNat : ℤ) = p 0 - 1 := Int.toNat_of_nonneg hxnon
        ext i <;> fin_cases i <;> simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt, hy] <;> omega
    · rcases h with ⟨hy, hx0, hx1⟩
      refine Finset.mem_image.mpr
        ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨(p 0 - 2).toNat, ?_⟩))), by simp, ?_⟩
      · have : (p 0 - 2).toNat ≤ 2009 := by omega
        omega
      · have hxnon : 0 ≤ p 0 - 2 := by omega
        have hxEq : ((p 0 - 2).toNat : ℤ) = p 0 - 2 := Int.toNat_of_nonneg hxnon
        ext i <;> fin_cases i <;> simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt, hy] <;> omega
    · rcases h with ⟨hy, hx0, hx1⟩
      refine Finset.mem_image.mpr
        ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨(p 0 - 3).toNat, ?_⟩))), by simp, ?_⟩
      · have : (p 0 - 3).toNat ≤ 2008 := by omega
        omega
      · have hxnon : 0 ≤ p 0 - 3 := by omega
        have hxEq : ((p 0 - 3).toNat : ℤ) = p 0 - 3 := Int.toNat_of_nonneg hxnon
        ext i <;> fin_cases i <;> simp [putnam_2011_a1_badPoint, putnam_2011_a1_pt, hy] <;> omega

lemma putnam_2011_a1_badFinset_card :
    putnam_2011_a1_badFinset.card = 10053 := by
  rw [putnam_2011_a1_badFinset, Finset.card_image_of_injective _ putnam_2011_a1_badPoint_inj]
  simp [putnam_2011_a1_badIndex]

def putnam_2011_a1_badFinPoint : putnam_2011_a1_badIndex → Fin 2 → Fin 2012
  | Sum.inl y => ![0, y]
  | Sum.inr (Sum.inl x) => ![⟨x.1 + 1, by omega⟩, 0]
  | Sum.inr (Sum.inr (Sum.inl x)) => ![⟨x.1 + 1, by omega⟩, 1]
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl x))) => ![⟨x.1 + 2, by omega⟩, 2]
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr x))) => ![⟨x.1 + 3, by omega⟩, 3]

lemma putnam_2011_a1_badFinPoint_cast
    (i : putnam_2011_a1_badIndex) (j : Fin 2) :
    ((putnam_2011_a1_badFinPoint i j : Fin 2012) : ℤ) =
      putnam_2011_a1_badPoint i j := by
  cases i with
  | inl y =>
      fin_cases j <;> simp [putnam_2011_a1_badFinPoint, putnam_2011_a1_badPoint,
        putnam_2011_a1_pt]
  | inr r =>
      cases r with
      | inl x =>
          fin_cases j <;> simp [putnam_2011_a1_badFinPoint, putnam_2011_a1_badPoint,
            putnam_2011_a1_pt]
      | inr r2 =>
          cases r2 with
          | inl x =>
              fin_cases j <;> simp [putnam_2011_a1_badFinPoint, putnam_2011_a1_badPoint,
                putnam_2011_a1_pt]
          | inr r3 =>
              cases r3 with
              | inl x =>
                  fin_cases j <;> simp [putnam_2011_a1_badFinPoint,
                    putnam_2011_a1_badPoint, putnam_2011_a1_pt]
              | inr x =>
                  fin_cases j <;> simp [putnam_2011_a1_badFinPoint,
                    putnam_2011_a1_badPoint, putnam_2011_a1_pt]

def putnam_2011_a1_badIndexSubtype :
    putnam_2011_a1_badIndex →
      {p : Fin 2 → Fin 2012 //
        p 0 = 0 ∨ p 1 = 0 ∨ p 1 = 1 ∨
          (p 1 = 2 ∧ 2 ≤ p 0) ∨ (p 1 = 3 ∧ 3 ≤ p 0)}
  | Sum.inl y => ⟨putnam_2011_a1_badFinPoint (Sum.inl y), by simp [putnam_2011_a1_badFinPoint]⟩
  | Sum.inr (Sum.inl x) =>
      ⟨putnam_2011_a1_badFinPoint (Sum.inr (Sum.inl x)), by
        right
        left
        simp [putnam_2011_a1_badFinPoint]⟩
  | Sum.inr (Sum.inr (Sum.inl x)) =>
      ⟨putnam_2011_a1_badFinPoint (Sum.inr (Sum.inr (Sum.inl x))), by
        right
        right
        left
        simp [putnam_2011_a1_badFinPoint]⟩
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl x))) =>
      ⟨putnam_2011_a1_badFinPoint (Sum.inr (Sum.inr (Sum.inr (Sum.inl x)))), by
        right
        right
        right
        left
        constructor
        · simp [putnam_2011_a1_badFinPoint]
        · change (2 : ℕ) ≤ x.1 + 2
          omega
        ⟩
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr x))) =>
      ⟨putnam_2011_a1_badFinPoint (Sum.inr (Sum.inr (Sum.inr (Sum.inr x)))), by
        right
        right
        right
        right
        constructor
        · simp [putnam_2011_a1_badFinPoint]
        · change (3 : ℕ) ≤ x.1 + 3
          omega
        ⟩

lemma putnam_2011_a1_badIndexSubtype_val
    (i : putnam_2011_a1_badIndex) :
    (putnam_2011_a1_badIndexSubtype i).1 = putnam_2011_a1_badFinPoint i := by
  cases i with
  | inl y => rfl
  | inr r =>
      cases r with
      | inl x => rfl
      | inr r2 =>
          cases r2 with
          | inl x => rfl
          | inr r3 =>
              cases r3 with
              | inl x => rfl
              | inr x => rfl

lemma putnam_2011_a1_badIndexSubtype_inj :
    Function.Injective putnam_2011_a1_badIndexSubtype := by
  intro a b h
  apply putnam_2011_a1_badPoint_inj
  ext j
  have hval := congr_arg Subtype.val h
  have hj := congr_fun hval j
  rw [putnam_2011_a1_badIndexSubtype_val] at hj
  rw [putnam_2011_a1_badIndexSubtype_val] at hj
  calc
    putnam_2011_a1_badPoint a j =
        ((putnam_2011_a1_badFinPoint a j : Fin 2012) : ℤ) := by
          rw [putnam_2011_a1_badFinPoint_cast]
    _ = ((putnam_2011_a1_badFinPoint b j : Fin 2012) : ℤ) := by rw [hj]
    _ = putnam_2011_a1_badPoint b j := by
          rw [putnam_2011_a1_badFinPoint_cast]

lemma putnam_2011_a1_badIndexSubtype_surj :
    Function.Surjective putnam_2011_a1_badIndexSubtype := by
  intro q
  by_cases hx0 : q.1 0 = 0
  · refine ⟨Sum.inl (q.1 1), ?_⟩
    apply Subtype.ext
    ext j <;> fin_cases j
    · simp [putnam_2011_a1_badIndexSubtype, putnam_2011_a1_badFinPoint, hx0]
    · simp [putnam_2011_a1_badIndexSubtype, putnam_2011_a1_badFinPoint]
  · rcases q.2 with hzero | hrow0 | hrow1 | hrow2 | hrow3
    · exact False.elim (hx0 hzero)
    · have hxpos : 0 < (q.1 0).1 := by
        have hxne : (q.1 0).1 ≠ 0 := by
          intro hval
          apply hx0
          exact Fin.ext hval
        omega
      · refine ⟨Sum.inr (Sum.inl ⟨(q.1 0).1 - 1, by omega⟩), ?_⟩
        apply Subtype.ext
        ext j <;> fin_cases j
        · simp [putnam_2011_a1_badIndexSubtype, putnam_2011_a1_badFinPoint]
          omega
        · simp [putnam_2011_a1_badIndexSubtype, putnam_2011_a1_badFinPoint, hrow0]
    · have hxpos : 0 < (q.1 0).1 := by
        have hxne : (q.1 0).1 ≠ 0 := by
          intro hval
          apply hx0
          exact Fin.ext hval
        omega
      · refine ⟨Sum.inr (Sum.inr (Sum.inl ⟨(q.1 0).1 - 1, by omega⟩)), ?_⟩
        apply Subtype.ext
        ext j <;> fin_cases j
        · simp [putnam_2011_a1_badIndexSubtype, putnam_2011_a1_badFinPoint]
          omega
        · simp [putnam_2011_a1_badIndexSubtype, putnam_2011_a1_badFinPoint, hrow1]
    · have hxge2 : 2 ≤ (q.1 0).1 := by
        exact_mod_cast hrow2.2
      · refine ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨(q.1 0).1 - 2, by omega⟩))), ?_⟩
        apply Subtype.ext
        ext j <;> fin_cases j
        · simp [putnam_2011_a1_badIndexSubtype, putnam_2011_a1_badFinPoint]
          omega
        · simp [putnam_2011_a1_badIndexSubtype, putnam_2011_a1_badFinPoint, hrow2.1]
    · have hxge3 : 3 ≤ (q.1 0).1 := by
        exact_mod_cast hrow3.2
      · refine ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨(q.1 0).1 - 3, by omega⟩))), ?_⟩
        apply Subtype.ext
        ext j <;> fin_cases j
        · simp [putnam_2011_a1_badIndexSubtype, putnam_2011_a1_badFinPoint]
          omega
        · simp [putnam_2011_a1_badIndexSubtype, putnam_2011_a1_badFinPoint, hrow3.1]

lemma putnam_2011_a1_badIndexSubtype_bijective :
    Function.Bijective putnam_2011_a1_badIndexSubtype :=
  ⟨putnam_2011_a1_badIndexSubtype_inj, putnam_2011_a1_badIndexSubtype_surj⟩

lemma putnam_2011_a1_badRow_iff_solutionSet
    (p : Fin 2 → Fin 2012) :
    (p 0 = 0 ∨ p 1 = 0 ∨ p 1 = 1 ∨
        (p 1 = 2 ∧ 2 ≤ p 0) ∨ (p 1 = 3 ∧ 3 ≤ p 0)) ↔
      p 0 = 0 ∨ (p 1 ≤ p 0 ∧ p 1 ≤ 3) := by
  constructor
  · intro hrow
    rcases hrow with hx0 | hy0 | hy1 | hy2 | hy3
    · exact Or.inl hx0
    · exact Or.inr ⟨by omega, by omega⟩
    · by_cases hx0 : p 0 = 0
      · exact Or.inl hx0
      · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  · intro hrow
    rcases hrow with hx0 | hsmall
    · exact Or.inl hx0
    · rcases hsmall with ⟨hylex, hyle3⟩
      rcases (show p 1 = 0 ∨ p 1 = 1 ∨ p 1 = 2 ∨ p 1 = 3 by omega) with
        hy0 | hy1 | hy2 | hy3
      · exact Or.inr (Or.inl hy0)
      · exact Or.inr (Or.inr (Or.inl hy1))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hy2, by omega⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hy3, by omega⟩)))

def putnam_2011_a1_badSubtypeSolutionEquiv :
    {p : Fin 2 → Fin 2012 //
      p 0 = 0 ∨ p 1 = 0 ∨ p 1 = 1 ∨
        (p 1 = 2 ∧ 2 ≤ p 0) ∨ (p 1 = 3 ∧ 3 ≤ p 0)} ≃
      {p : Fin 2 → Fin 2012 //
        p 0 = 0 ∨ (p 1 ≤ p 0 ∧ p 1 ≤ 3)} where
  toFun q := ⟨q.1, (putnam_2011_a1_badRow_iff_solutionSet q.1).1 q.2⟩
  invFun q := ⟨q.1, (putnam_2011_a1_badRow_iff_solutionSet q.1).2 q.2⟩
  left_inv q := by
    cases q
    rfl
  right_inv q := by
    cases q
    rfl

lemma putnam_2011_a1_badIndexSubtype_solution_card :
    Fintype.card putnam_2011_a1_badIndex =
      Fintype.card {p : Fin 2 → Fin 2012 //
        p 0 = 0 ∨ (p 1 ≤ p 0 ∧ p 1 ≤ 3)} := by
  exact Fintype.card_congr
    ((Equiv.ofBijective putnam_2011_a1_badIndexSubtype
      putnam_2011_a1_badIndexSubtype_bijective).trans
        putnam_2011_a1_badSubtypeSolutionEquiv)

lemma putnam_2011_a1_badRow_iff_not_reachable
    (p : Fin 2 → Fin 2012) :
    (p 0 = 0 ∨ p 1 = 0 ∨ p 1 = 1 ∨
        (p 1 = 2 ∧ 2 ≤ p 0) ∨ (p 1 = 3 ∧ 3 ≤ p 0)) ↔
      ¬ ((0 < p 0 ∧ p 0 < p 1) ∨ (4 ≤ p 1 ∧ p 1 ≤ p 0)) := by
  constructor
  · intro hrow hreach
    rcases hrow with hx0 | hy0 | hy1 | hy2 | hy3 <;>
      rcases hreach with hlt | hge <;> omega
  · intro hnot
    by_cases hx0 : p 0 = 0
    · exact Or.inl hx0
    · right
      have hxpos : 0 < p 0 := by
        by_contra hxle
        apply hx0
        exact le_antisymm (le_of_not_gt hxle) (by omega)
      have hylex : p 1 ≤ p 0 := by
        by_contra hygt
        exact hnot (Or.inl ⟨hxpos, lt_of_not_ge hygt⟩)
      have hylt4 : p 1 < 4 := by
        by_contra hyge
        exact hnot (Or.inr ⟨le_of_not_gt hyge, hylex⟩)
      rcases (show p 1 = 0 ∨ p 1 = 1 ∨ p 1 = 2 ∨ p 1 = 3 by omega) with
        hy0 | hy1 | hy2 | hy3
      · exact Or.inl hy0
      · exact Or.inr (Or.inl hy1)
      · exact Or.inr (Or.inr (Or.inl ⟨hy2, by simpa [hy2] using hylex⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hy3, by simpa [hy3] using hylex⟩))

def putnam_2011_a1_badSubtypeEquiv :
    {p : Fin 2 → Fin 2012 //
      p 0 = 0 ∨ p 1 = 0 ∨ p 1 = 1 ∨
        (p 1 = 2 ∧ 2 ≤ p 0) ∨ (p 1 = 3 ∧ 3 ≤ p 0)} ≃
      {p : Fin 2 → Fin 2012 //
        ¬ ((0 < p 0 ∧ p 0 < p 1) ∨ (4 ≤ p 1 ∧ p 1 ≤ p 0))} where
  toFun q := ⟨q.1, (putnam_2011_a1_badRow_iff_not_reachable q.1).1 q.2⟩
  invFun q := ⟨q.1, (putnam_2011_a1_badRow_iff_not_reachable q.1).2 q.2⟩
  left_inv q := by
    cases q
    rfl
  right_inv q := by
    cases q
    rfl

lemma putnam_2011_a1_badIndexSubtype_card :
    Fintype.card putnam_2011_a1_badIndex =
      Fintype.card {p : Fin 2 → Fin 2012 //
        ¬ ((0 < p 0 ∧ p 0 < p 1) ∨ (4 ≤ p 1 ∧ p 1 ≤ p 0))} := by
  exact Fintype.card_congr
    ((Equiv.ofBijective putnam_2011_a1_badIndexSubtype
      putnam_2011_a1_badIndexSubtype_bijective).trans putnam_2011_a1_badSubtypeEquiv)

lemma putnam_2011_a1_badFinset_card_index :
    putnam_2011_a1_badFinset.card = Fintype.card putnam_2011_a1_badIndex := by
  rw [putnam_2011_a1_badFinset,
    Finset.card_image_of_injective _ putnam_2011_a1_badPoint_inj]
  simp

lemma putnam_2011_a1_badFinset_solutionSet_ncard :
    putnam_2011_a1_badFinset.card =
      ({p : Fin 2 → Fin 2012 |
        p 0 = 0 ∨ (p 1 ≤ p 0 ∧ p 1 ≤ 3)} : Set (Fin 2 → Fin 2012)).ncard := by
  rw [putnam_2011_a1_badFinset_card_index,
    putnam_2011_a1_badIndexSubtype_solution_card]
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
  change Fintype.card {p : Fin 2 → Fin 2012 //
      p 0 = 0 ∨ (p 1 ≤ p 0 ∧ p 1 ≤ 3)} =
    Fintype.card {p : Fin 2 → Fin 2012 //
      p 0 = 0 ∨ (p 1 ≤ p 0 ∧ p 1 ≤ 3)}
  rfl

lemma putnam_2011_a1_badPred_pt_iff_not_reachable
    {x y : ℤ} (hx0 : 0 ≤ x) (hx1 : x ≤ 2011)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 2011) :
    putnam_2011_a1_badPred (putnam_2011_a1_pt x y) ↔
      ¬ ((0 < x ∧ x < y) ∨ (4 ≤ y ∧ y ≤ x)) := by
  constructor
  · intro hbad hreach
    rcases hbad with h | h | h | h | h <;>
      rcases hreach with hlt | hge <;>
      simp [putnam_2011_a1_pt] at h <;> omega
  · intro hnot
    by_cases hx : x = 0
    · exact Or.inl (by simp [putnam_2011_a1_pt, hx, hy0, hy1])
    · right
      have hxpos : 0 < x := by omega
      have hylex : y ≤ x := by
        by_contra hygt
        exact hnot (Or.inl ⟨hxpos, by omega⟩)
      have hylt4 : y < 4 := by
        by_contra hyge
        exact hnot (Or.inr ⟨by omega, hylex⟩)
      rcases (show y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 by omega) with hy | hy | hy | hy
      · exact Or.inl (by simp [putnam_2011_a1_pt, hy] <;> omega)
      · exact Or.inr (Or.inl (by simp [putnam_2011_a1_pt, hy] <;> omega))
      · exact Or.inr (Or.inr (Or.inl (by simp [putnam_2011_a1_pt, hy] <;> omega)))
      · exact Or.inr (Or.inr (Or.inr (by simp [putnam_2011_a1_pt, hy] <;> omega)))

lemma putnam_2011_a1_badFinset_pair_card :
    putnam_2011_a1_badFinset.card =
      (((Finset.Icc (0 : ℤ) 2011).product (Finset.Icc (0 : ℤ) 2011)).filter
        (fun p : ℤ × ℤ =>
          ¬ ((0 < p.1 ∧ p.1 < p.2) ∨ (4 ≤ p.2 ∧ p.2 ≤ p.1)))).card := by
  classical
  refine Finset.card_bij'
    (s := putnam_2011_a1_badFinset)
    (t := (((Finset.Icc (0 : ℤ) 2011).product (Finset.Icc (0 : ℤ) 2011)).filter
      (fun p : ℤ × ℤ =>
        ¬ ((0 < p.1 ∧ p.1 < p.2) ∨ (4 ≤ p.2 ∧ p.2 ≤ p.1)))))
    (fun p _ => (p 0, p 1))
    (fun p _ => putnam_2011_a1_pt p.1 p.2) ?_ ?_ ?_ ?_
  · intro p hp
    have hpbad : putnam_2011_a1_badPred p :=
      (putnam_2011_a1_mem_badFinset_iff p).1 hp
    have hbox : 0 ≤ p 0 ∧ p 0 ≤ 2011 ∧ 0 ≤ p 1 ∧ p 1 ≤ 2011 := by
      rcases hpbad with h | h | h | h | h <;> omega
    have hpeq : p = putnam_2011_a1_pt (p 0) (p 1) := by
      ext i <;> fin_cases i <;> simp [putnam_2011_a1_pt]
    have hpbad_pt : putnam_2011_a1_badPred (putnam_2011_a1_pt (p 0) (p 1)) := by
      simpa [← hpeq] using hpbad
    have hnot :
        ¬ ((0 < p 0 ∧ p 0 < p 1) ∨ (4 ≤ p 1 ∧ p 1 ≤ p 0)) :=
      (putnam_2011_a1_badPred_pt_iff_not_reachable
        hbox.1 hbox.2.1 hbox.2.2.1 hbox.2.2.2).1 hpbad_pt
    rw [Finset.mem_filter]
    refine ⟨?_, hnot⟩
    rw [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨⟨hbox.1, hbox.2.1⟩, ⟨hbox.2.2.1, hbox.2.2.2⟩⟩
  · intro p hp
    rw [Finset.mem_filter] at hp
    rcases hp with ⟨hpbox, hnot⟩
    rw [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hpbox
    rcases hpbox with ⟨hx, hy⟩
    rw [putnam_2011_a1_mem_badFinset_iff]
    exact (putnam_2011_a1_badPred_pt_iff_not_reachable
      hx.1 hx.2 hy.1 hy.2).2 hnot
  · intro p hp
    ext i <;> fin_cases i <;> simp [putnam_2011_a1_pt]
  · intro p hp
    cases p
    simp [putnam_2011_a1_pt]

lemma putnam_2011_a1_mem_badPairRows_iff (p : ℤ × ℤ) :
    p ∈ (((Finset.Icc (0 : ℤ) 2011).image (fun y : ℤ => ((0 : ℤ), y))) ∪
      ((Finset.Icc (1 : ℤ) 2011).image (fun x : ℤ => (x, (0 : ℤ)))) ∪
      ((Finset.Icc (1 : ℤ) 2011).image (fun x : ℤ => (x, (1 : ℤ)))) ∪
      ((Finset.Icc (2 : ℤ) 2011).image (fun x : ℤ => (x, (2 : ℤ)))) ∪
      ((Finset.Icc (3 : ℤ) 2011).image (fun x : ℤ => (x, (3 : ℤ))))) ↔
      putnam_2011_a1_badPred (putnam_2011_a1_pt p.1 p.2) := by
  constructor
  · intro hp
    simp [Finset.mem_union, Finset.mem_image, Finset.mem_Icc] at hp
    rw [putnam_2011_a1_badPred]
    rcases hp with h | h | h | h | h
    · rcases h with ⟨y, ⟨hy0, hy1⟩, hpeq⟩
      rcases hpeq
      left
      simp [putnam_2011_a1_pt, hy0, hy1]
    · rcases h with ⟨x, ⟨hx0, hx1⟩, hpeq⟩
      rcases hpeq
      right
      left
      simp [putnam_2011_a1_pt, hx0, hx1]
    · rcases h with ⟨x, ⟨hx0, hx1⟩, hpeq⟩
      rcases hpeq
      right
      right
      left
      simp [putnam_2011_a1_pt, hx0, hx1]
    · rcases h with ⟨x, ⟨hx0, hx1⟩, hpeq⟩
      rcases hpeq
      right
      right
      right
      left
      simp [putnam_2011_a1_pt, hx0, hx1]
    · rcases h with ⟨x, ⟨hx0, hx1⟩, hpeq⟩
      rcases hpeq
      right
      right
      right
      right
      simp [putnam_2011_a1_pt, hx0, hx1]
  · intro hp
    rw [putnam_2011_a1_badPred] at hp
    simp [putnam_2011_a1_pt] at hp
    simp [Finset.mem_union, Finset.mem_image, Finset.mem_Icc]
    rcases hp with h | h | h | h | h
    · rcases h with ⟨hx, hy0, hy1⟩
      left
      refine ⟨p.2, ⟨hy0, hy1⟩, ?_⟩
      ext <;> simp [hx]
    · rcases h with ⟨hy, hx0, hx1⟩
      right
      left
      refine ⟨p.1, ⟨hx0, hx1⟩, ?_⟩
      ext <;> simp [hy]
    · rcases h with ⟨hy, hx0, hx1⟩
      right
      right
      left
      refine ⟨p.1, ⟨hx0, hx1⟩, ?_⟩
      ext <;> simp [hy]
    · rcases h with ⟨hy, hx0, hx1⟩
      right
      right
      right
      left
      refine ⟨p.1, ⟨hx0, hx1⟩, ?_⟩
      ext <;> simp [hy]
    · rcases h with ⟨hy, hx0, hx1⟩
      right
      right
      right
      right
      refine ⟨p.1, ⟨hx0, hx1⟩, ?_⟩
      ext <;> simp [hy]

lemma putnam_2011_a1_badFinset_pair_rows_card :
    putnam_2011_a1_badFinset.card =
      (((Finset.Icc (0 : ℤ) 2011).image (fun y : ℤ => ((0 : ℤ), y))) ∪
        ((Finset.Icc (1 : ℤ) 2011).image (fun x : ℤ => (x, (0 : ℤ)))) ∪
        ((Finset.Icc (1 : ℤ) 2011).image (fun x : ℤ => (x, (1 : ℤ)))) ∪
        ((Finset.Icc (2 : ℤ) 2011).image (fun x : ℤ => (x, (2 : ℤ)))) ∪
        ((Finset.Icc (3 : ℤ) 2011).image (fun x : ℤ => (x, (3 : ℤ))))).card := by
  classical
  refine Finset.card_bij'
    (s := putnam_2011_a1_badFinset)
    (t := (((Finset.Icc (0 : ℤ) 2011).image (fun y : ℤ => ((0 : ℤ), y))) ∪
      ((Finset.Icc (1 : ℤ) 2011).image (fun x : ℤ => (x, (0 : ℤ)))) ∪
      ((Finset.Icc (1 : ℤ) 2011).image (fun x : ℤ => (x, (1 : ℤ)))) ∪
      ((Finset.Icc (2 : ℤ) 2011).image (fun x : ℤ => (x, (2 : ℤ)))) ∪
      ((Finset.Icc (3 : ℤ) 2011).image (fun x : ℤ => (x, (3 : ℤ))))))
    (fun p _ => (p 0, p 1))
    (fun p _ => putnam_2011_a1_pt p.1 p.2) ?_ ?_ ?_ ?_
  · intro p hp
    rw [putnam_2011_a1_mem_badPairRows_iff]
    have hpbad : putnam_2011_a1_badPred p :=
      (putnam_2011_a1_mem_badFinset_iff p).1 hp
    have hpeq : p = putnam_2011_a1_pt (p 0) (p 1) := by
      ext i <;> fin_cases i <;> simp [putnam_2011_a1_pt]
    simpa [← hpeq] using hpbad
  · intro p hp
    rw [putnam_2011_a1_mem_badFinset_iff]
    exact (putnam_2011_a1_mem_badPairRows_iff p).1 hp
  · intro p hp
    ext i <;> fin_cases i <;> simp [putnam_2011_a1_pt]
  · intro p hp
    cases p
    simp [putnam_2011_a1_pt]

lemma putnam_2011_a1_encard_coe_finset
    {α : Type*} [DecidableEq α] (s : Finset α) :
    (s : Set α).encard = s.card := by
  simpa using (Finset.finite_toSet s).encard_eq_coe_toFinset_card

/--
Define a \emph{growing spiral} in the plane to be a sequence of points with integer coordinates $P_0=(0,0),P_1,\dots,P_n$ such that $n \geq 2$ and:
\begin{itemize}
\item the directed line segments $P_0P_1,P_1P_2,\dots,P_{n-1}P_n$ are in the successive coordinate directions east (for $P_0P_1$), north, west, south, east, etc.;
\item the lengths of these line segments are positive and strictly increasing.
\end{itemize}
How many of the points $(x,y)$ with integer coordinates $0 \leq x \leq 2011,0 \leq y \leq 2011$ \emph{cannot} be the last point, $P_n$ of any growing spiral?
-/
theorem putnam_2011_a1
  (IsSpiral : List (Fin 2 → ℤ) → Prop)
  (IsSpiral_def : ∀ P, IsSpiral P ↔ P.length ≥ 3 ∧ P[0]! = 0 ∧
  (∃ l : Fin (P.length - 1) → ℕ, (∀ i, 0 < l i) ∧ StrictMono l ∧ (∀ i : Fin (P.length - 1),
    (i.1 % 4 = 0 → (P[i] 0 + l i = P[i.1 + 1]! 0 ∧ P[i] 1 = P[i.1 + 1]! 1)) ∧
    (i.1 % 4 = 1 → (P[i] 0 = P[i.1 + 1]! 0 ∧ P[i] 1 + l i = P[i.1 + 1]! 1)) ∧
    (i.1 % 4 = 2 → (P[i] 0 - l i = P[i.1 + 1]! 0 ∧ P[i] 1 = P[i.1 + 1]! 1)) ∧
    (i.1 % 4 = 3 → (P[i] 0 = P[i.1 + 1]! 0 ∧ P[i] 1 - l i = P[i.1 + 1]! 1))))) :
  {p | 0 ≤ p 0 ∧ p 0 ≤ 2011 ∧ 0 ≤ p 1 ∧ p 1 ≤ 2011 ∧ ¬∃ spiral, IsSpiral spiral ∧ spiral.getLast! = p}.encard = putnam_2011_a1_solution := by
  classical
  have IsSpiral_def_explicit : putnam_2011_a1_IsSpiral_def_explicit IsSpiral := by
    intro P
    simpa [putnam_2011_a1_IsSpiral_def_explicit, putnam_2011_a1_cur] using IsSpiral_def P
  let target : Set (Fin 2 → ℤ) :=
    {p | 0 ≤ p 0 ∧ p 0 ≤ 2011 ∧ 0 ≤ p 1 ∧ p 1 ≤ 2011 ∧
      ¬∃ spiral, IsSpiral spiral ∧ spiral.getLast! = p}
  have hset : target = (putnam_2011_a1_badFinset : Set (Fin 2 → ℤ)) := by
    ext p
    rw [Finset.mem_coe, putnam_2011_a1_mem_badFinset_iff]
    constructor
    · intro hp
      rcases hp with ⟨hp0, hp0le, hp1, hp1le, hnreach⟩
      by_cases hx0 : p 0 = 0
      · exact Or.inl ⟨hx0, hp1, hp1le⟩
      · have hxpos : 0 < p 0 := by omega
        by_cases hy3 : p 1 ≤ 3
        · have hy_le_x : p 1 ≤ p 0 := by
            by_contra hcontra
            have hreach := putnam_2011_a1_reachable_of_lt IsSpiral IsSpiral_def_explicit hxpos (by omega)
            exact hnreach hreach
          rcases (show p 1 = 0 ∨ p 1 = 1 ∨ p 1 = 2 ∨ p 1 = 3 by omega) with h0 | h1 | h2 | h3
          · exact Or.inr (Or.inl ⟨h0, by omega, hp0le⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨h1, by omega, hp0le⟩))
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, by omega, hp0le⟩)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h3, by omega, hp0le⟩)))
        · have hy4 : 4 ≤ p 1 := by omega
          by_cases hxy : p 0 < p 1
          · have hreach := putnam_2011_a1_reachable_of_lt IsSpiral IsSpiral_def_explicit hxpos hxy
            exact False.elim (hnreach hreach)
          · have hx3 : 3 ≤ p 0 := by omega
            have hreach := putnam_2011_a1_reachable_of_large IsSpiral IsSpiral_def_explicit hx3 hy4 (by omega)
            exact False.elim (hnreach hreach)
    · intro hp
      have hbox : 0 ≤ p 0 ∧ p 0 ≤ 2011 ∧ 0 ≤ p 1 ∧ p 1 ≤ 2011 := by
        rcases hp with h | h | h | h | h
        · rcases h with ⟨hx, hy0, hy1⟩
          omega
        · rcases h with ⟨hy, hx0, hx1⟩
          omega
        · rcases h with ⟨hy, hx0, hx1⟩
          omega
        · rcases h with ⟨hy, hx0, hx1⟩
          omega
        · rcases h with ⟨hy, hx0, hx1⟩
          omega
      refine ⟨hbox.1, hbox.2.1, hbox.2.2.1, hbox.2.2.2, ?_⟩
      intro hreach
      have hres := putnam_2011_a1_endpoint_restriction
        IsSpiral IsSpiral_def_explicit hbox.1 hbox.2.2.1 hreach
      rcases hp with h | h | h | h | h
      · rcases h with ⟨hx, hy0, hy1⟩
        omega
      · rcases h with ⟨hy, hx0, hx1⟩
        omega
      · rcases h with ⟨hy, hx0, hx1⟩
        have hlt := hres.2.2 (by omega)
        omega
      · rcases h with ⟨hy, hx0, hx1⟩
        have hlt := hres.2.2 (by omega)
        omega
      · rcases h with ⟨hy, hx0, hx1⟩
        have hlt := hres.2.2 (by omega)
        omega
  change target.encard = putnam_2011_a1_solution
  rw [hset]
  have hencard : (putnam_2011_a1_badFinset : Set (Fin 2 → ℤ)).encard =
      putnam_2011_a1_badFinset.card := by
    exact putnam_2011_a1_encard_coe_finset putnam_2011_a1_badFinset
  rw [hencard]
  unfold putnam_2011_a1_solution
  rw [putnam_2011_a1_badFinset_solutionSet_ncard]
