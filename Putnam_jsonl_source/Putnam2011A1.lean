import Mathlib

namespace Putnam2011A1

abbrev Point := Fin 2 → ℤ

def zpt (x y : ℤ) : Point := ![x, y]

def StepSpec (P : List Point) (l : Fin (P.length - 1) → ℕ) : Prop :=
  ∀ i : Fin (P.length - 1),
    (i.1 % 4 = 0 → (P[i] 0 + l i = P[i.1 + 1]! 0 ∧ P[i] 1 = P[i.1 + 1]! 1)) ∧
    (i.1 % 4 = 1 → (P[i] 0 = P[i.1 + 1]! 0 ∧ P[i] 1 + l i = P[i.1 + 1]! 1)) ∧
    (i.1 % 4 = 2 → (P[i] 0 - l i = P[i.1 + 1]! 0 ∧ P[i] 1 = P[i.1 + 1]! 1)) ∧
    (i.1 % 4 = 3 → (P[i] 0 = P[i.1 + 1]! 0 ∧ P[i] 1 - l i = P[i.1 + 1]! 1))

lemma get_fin_eq_getBang (P : List Point) {j : ℕ} (hj : j < P.length - 1) :
    P[(⟨j, hj⟩ : Fin (P.length - 1))] = P[j]! := by
  rw [getElem!_pos P j (by omega)]
  rfl

lemma getLast!_eq_getElem! {α : Type*} [Inhabited α] (l : List α) (h : 0 < l.length) :
    l.getLast! = l[l.length - 1]! := by
  cases l with
  | nil => simp at h
  | cons a t => simp [List.getLast!, List.getLast_eq_getElem]

lemma step0 {P : List Point} {l : Fin (P.length - 1) → ℕ}
    (hsteps : StepSpec P l) {j : ℕ} (hj : j < P.length - 1) (hmod : j % 4 = 0) :
    P[j]! 0 + (l ⟨j, hj⟩ : ℤ) = P[j + 1]! 0 ∧
    P[j]! 1 = P[j + 1]! 1 := by
  have h := (hsteps ⟨j, hj⟩).1 hmod
  rwa [get_fin_eq_getBang P hj] at h

lemma step1 {P : List Point} {l : Fin (P.length - 1) → ℕ}
    (hsteps : StepSpec P l) {j : ℕ} (hj : j < P.length - 1) (hmod : j % 4 = 1) :
    P[j]! 0 = P[j + 1]! 0 ∧
    P[j]! 1 + (l ⟨j, hj⟩ : ℤ) = P[j + 1]! 1 := by
  have h := (hsteps ⟨j, hj⟩).2.1 hmod
  rwa [get_fin_eq_getBang P hj] at h

lemma step2 {P : List Point} {l : Fin (P.length - 1) → ℕ}
    (hsteps : StepSpec P l) {j : ℕ} (hj : j < P.length - 1) (hmod : j % 4 = 2) :
    P[j]! 0 - (l ⟨j, hj⟩ : ℤ) = P[j + 1]! 0 ∧
    P[j]! 1 = P[j + 1]! 1 := by
  have h := (hsteps ⟨j, hj⟩).2.2.1 hmod
  rwa [get_fin_eq_getBang P hj] at h

lemma step3 {P : List Point} {l : Fin (P.length - 1) → ℕ}
    (hsteps : StepSpec P l) {j : ℕ} (hj : j < P.length - 1) (hmod : j % 4 = 3) :
    P[j]! 0 = P[j + 1]! 0 ∧
    P[j]! 1 - (l ⟨j, hj⟩ : ℤ) = P[j + 1]! 1 := by
  have h := (hsteps ⟨j, hj⟩).2.2.2 hmod
  rwa [get_fin_eq_getBang P hj] at h

lemma block0_decrease {P : List Point} {l : Fin (P.length - 1) → ℕ}
    (hmono : StrictMono l) (hsteps : StepSpec P l)
    {j : ℕ} (hj : j + 4 ≤ P.length - 1) (hmod : j % 4 = 0) :
    P[j + 4]! 0 < P[j]! 0 ∧ P[j + 4]! 1 < P[j]! 1 := by
  have hj0 : j < P.length - 1 := by omega
  have hj1 : j + 1 < P.length - 1 := by omega
  have hj2 : j + 2 < P.length - 1 := by omega
  have hj3 : j + 3 < P.length - 1 := by omega
  rcases step0 hsteps hj0 hmod with ⟨s0x, s0y⟩
  rcases step1 hsteps hj1 (by omega) with ⟨s1x, s1y⟩
  rcases step2 hsteps hj2 (by omega) with ⟨s2x, s2y⟩
  rcases step3 hsteps hj3 (by omega) with ⟨s3x, s3y⟩
  have s1x' : P[j + 1]! 0 = P[j + 2]! 0 := by simpa [Nat.add_assoc] using s1x
  have s2x' : P[j + 2]! 0 - (l ⟨j + 2, hj2⟩ : ℤ) = P[j + 3]! 0 := by
    simpa [Nat.add_assoc] using s2x
  have s3x' : P[j + 3]! 0 = P[j + 4]! 0 := by simpa [Nat.add_assoc] using s3x
  have s1y' : P[j + 1]! 1 + (l ⟨j + 1, hj1⟩ : ℤ) = P[j + 2]! 1 := by
    simpa [Nat.add_assoc] using s1y
  have s2y' : P[j + 2]! 1 = P[j + 3]! 1 := by simpa [Nat.add_assoc] using s2y
  have s3y' : P[j + 3]! 1 - (l ⟨j + 3, hj3⟩ : ℤ) = P[j + 4]! 1 := by
    simpa [Nat.add_assoc] using s3y
  have hxltNat : l ⟨j, hj0⟩ < l ⟨j + 2, hj2⟩ := hmono (by simp)
  have hyltNat : l ⟨j + 1, hj1⟩ < l ⟨j + 3, hj3⟩ := hmono (by simp)
  constructor <;> omega

lemma block2_increase {P : List Point} {l : Fin (P.length - 1) → ℕ}
    (hmono : StrictMono l) (hsteps : StepSpec P l)
    {j : ℕ} (hj : j + 4 ≤ P.length - 1) (hmod : j % 4 = 2) :
    P[j]! 0 < P[j + 4]! 0 ∧ P[j]! 1 + 2 ≤ P[j + 4]! 1 := by
  have hj0 : j < P.length - 1 := by omega
  have hj1 : j + 1 < P.length - 1 := by omega
  have hj2 : j + 2 < P.length - 1 := by omega
  have hj3 : j + 3 < P.length - 1 := by omega
  rcases step2 hsteps hj0 hmod with ⟨s0x, s0y⟩
  rcases step3 hsteps hj1 (by omega) with ⟨s1x, s1y⟩
  rcases step0 hsteps hj2 (by omega) with ⟨s2x, s2y⟩
  rcases step1 hsteps hj3 (by omega) with ⟨s3x, s3y⟩
  have s1x' : P[j + 1]! 0 = P[j + 2]! 0 := by simpa [Nat.add_assoc] using s1x
  have s2x' : P[j + 2]! 0 + (l ⟨j + 2, hj2⟩ : ℤ) = P[j + 3]! 0 := by
    simpa [Nat.add_assoc] using s2x
  have s3x' : P[j + 3]! 0 = P[j + 4]! 0 := by simpa [Nat.add_assoc] using s3x
  have s1y' : P[j + 1]! 1 - (l ⟨j + 1, hj1⟩ : ℤ) = P[j + 2]! 1 := by
    simpa [Nat.add_assoc] using s1y
  have s2y' : P[j + 2]! 1 = P[j + 3]! 1 := by simpa [Nat.add_assoc] using s2y
  have s3y' : P[j + 3]! 1 + (l ⟨j + 3, hj3⟩ : ℤ) = P[j + 4]! 1 := by
    simpa [Nat.add_assoc] using s3y
  have hxltNat : l ⟨j, hj0⟩ < l ⟨j + 2, hj2⟩ := hmono (by simp)
  have hyltNat1 : l ⟨j + 1, hj1⟩ < l ⟨j + 2, hj2⟩ := hmono (by simp)
  have hyltNat2 : l ⟨j + 2, hj2⟩ < l ⟨j + 3, hj3⟩ := hmono (by simp)
  constructor <;> omega

lemma point4_neg {P : List Point} {l : Fin (P.length - 1) → ℕ}
    (h0 : P[0]! = 0) (hmono : StrictMono l) (hsteps : StepSpec P l)
    (k : ℕ) (hk : 1 ≤ k) (hend : 4 * k ≤ P.length - 1) :
    P[4 * k]! 0 < 0 ∧ P[4 * k]! 1 < 0 := by
  have h0x : P[0]! 0 = 0 := by simpa using congrFun h0 0
  have h0y : P[0]! 1 = 0 := by simpa using congrFun h0 1
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases hk0 : k = 0
      · subst k
        have hb := block0_decrease hmono hsteps (j := 0) (by simpa using hend) (by norm_num)
        have hx : P[4 * (0 + 1)]! 0 < P[0]! 0 := by simpa using hb.1
        have hy : P[4 * (0 + 1)]! 1 < P[0]! 1 := by simpa using hb.2
        constructor <;> omega
      · have hkpos : 1 ≤ k := by omega
        have hprev := ih hkpos (by omega)
        have hb := block0_decrease hmono hsteps (j := 4 * k) (by omega) (by omega)
        have hbx : P[4 * (k + 1)]! 0 < P[4 * k]! 0 := by
          simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb.1
        have hby : P[4 * (k + 1)]! 1 < P[4 * k]! 1 := by
          simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb.2
        constructor <;> omega

lemma point4p2_pos {P : List Point} {l : Fin (P.length - 1) → ℕ}
    (h0 : P[0]! = 0) (hpos : ∀ i, 0 < l i) (hmono : StrictMono l)
    (hsteps : StepSpec P l) (k : ℕ) (hend : 4 * k + 2 ≤ P.length - 1) :
    0 < P[4 * k + 2]! 0 ∧
      ((2 + 2 * k : ℕ) : ℤ) ≤ P[4 * k + 2]! 1 ∧
      (k = 0 → P[4 * k + 2]! 0 < P[4 * k + 2]! 1) := by
  have h0x : P[0]! 0 = 0 := by simpa using congrFun h0 0
  have h0y : P[0]! 1 = 0 := by simpa using congrFun h0 1
  induction k with
  | zero =>
      have hj0 : 0 < P.length - 1 := by omega
      have hj1 : 1 < P.length - 1 := by omega
      rcases step0 hsteps hj0 (by norm_num) with ⟨s0x, s0y⟩
      rcases step1 hsteps hj1 (by norm_num) with ⟨s1x, s1y⟩
      have s0x' : P[0]! 0 + (l ⟨0, hj0⟩ : ℤ) = P[1]! 0 := by simpa using s0x
      have s0y' : P[0]! 1 = P[1]! 1 := by simpa using s0y
      have s1x' : P[1]! 0 = P[2]! 0 := by simpa using s1x
      have s1y' : P[1]! 1 + (l ⟨1, hj1⟩ : ℤ) = P[2]! 1 := by simpa using s1y
      have hlt01 : l ⟨0, hj0⟩ < l ⟨1, hj1⟩ := hmono (by simp)
      have hpos0 := hpos ⟨0, hj0⟩
      have hx2 : 0 < P[2]! 0 := by omega
      have hy2 : (2 : ℤ) ≤ P[2]! 1 := by omega
      have hlt2 : P[2]! 0 < P[2]! 1 := by omega
      constructor
      · simpa using hx2
      constructor
      · simpa using hy2
      · intro _; simpa using hlt2
  | succ k ih =>
      have hprev := ih (by omega)
      rcases hprev with ⟨hprevx, hprevy, hprevlt⟩
      have hb := block2_increase hmono hsteps (j := 4 * k + 2) (by omega) (by omega)
      have hbx : P[4 * k + 2]! 0 < P[4 * (k + 1) + 2]! 0 := by
        simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb.1
      have hby : P[4 * k + 2]! 1 + 2 ≤ P[4 * (k + 1) + 2]! 1 := by
        simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb.2
      constructor
      · omega
      constructor
      · omega
      · intro hzero; omega

lemma point4p1_y_neg {P : List Point} {l : Fin (P.length - 1) → ℕ}
    (h0 : P[0]! = 0) (hmono : StrictMono l) (hsteps : StepSpec P l)
    (k : ℕ) (hk : 1 ≤ k) (hend : 4 * k + 1 ≤ P.length - 1) :
    P[4 * k + 1]! 1 < 0 := by
  have hprev := point4_neg h0 hmono hsteps k hk (by omega)
  have hj : 4 * k < P.length - 1 := by omega
  rcases step0 hsteps hj (by omega) with ⟨sx, sy⟩
  have sy' : P[4 * k]! 1 = P[4 * k + 1]! 1 := by simpa [Nat.add_assoc] using sy
  omega

lemma point4p3_x_neg {P : List Point} {l : Fin (P.length - 1) → ℕ}
    (h0 : P[0]! = 0) (hmono : StrictMono l) (hsteps : StepSpec P l)
    (k : ℕ) (hend : 4 * k + 3 ≤ P.length - 1) :
    P[4 * k + 3]! 0 < 0 := by
  have h0x : P[0]! 0 = 0 := by simpa using congrFun h0 0
  by_cases hk0 : k = 0
  · subst k
    have hj0 : 0 < P.length - 1 := by omega
    have hj1 : 1 < P.length - 1 := by omega
    have hj2 : 2 < P.length - 1 := by omega
    rcases step0 hsteps hj0 (by norm_num) with ⟨s0x, s0y⟩
    rcases step1 hsteps hj1 (by norm_num) with ⟨s1x, s1y⟩
    rcases step2 hsteps hj2 (by norm_num) with ⟨s2x, s2y⟩
    have s0x' : P[0]! 0 + (l ⟨0, hj0⟩ : ℤ) = P[1]! 0 := by simpa using s0x
    have s1x' : P[1]! 0 = P[2]! 0 := by simpa using s1x
    have s2x' : P[2]! 0 - (l ⟨2, hj2⟩ : ℤ) = P[3]! 0 := by simpa using s2x
    have hlt02 : l ⟨0, hj0⟩ < l ⟨2, hj2⟩ := hmono (by simp)
    have hx3 : P[3]! 0 < 0 := by omega
    simpa using hx3
  · have hkpos : 1 ≤ k := by omega
    have hprev := point4_neg h0 hmono hsteps k hkpos (by omega)
    have hj0 : 4 * k < P.length - 1 := by omega
    have hj1 : 4 * k + 1 < P.length - 1 := by omega
    have hj2 : 4 * k + 2 < P.length - 1 := by omega
    rcases step0 hsteps hj0 (by omega) with ⟨s0x, s0y⟩
    rcases step1 hsteps hj1 (by omega) with ⟨s1x, s1y⟩
    rcases step2 hsteps hj2 (by omega) with ⟨s2x, s2y⟩
    have s1x' : P[4 * k + 1]! 0 = P[4 * k + 2]! 0 := by
      simpa [Nat.add_assoc] using s1x
    have s2x' : P[4 * k + 2]! 0 - (l ⟨4 * k + 2, hj2⟩ : ℤ) =
        P[4 * k + 3]! 0 := by
      simpa [Nat.add_assoc] using s2x
    have hlt02 : l ⟨4 * k, hj0⟩ < l ⟨4 * k + 2, hj2⟩ := hmono (by simp)
    omega

lemma endpoint_good {P : List Point} {l : Fin (P.length - 1) → ℕ}
    (hlen : P.length ≥ 3) (h0 : P[0]! = 0) (hpos : ∀ i, 0 < l i)
    (hmono : StrictMono l) (hsteps : StepSpec P l)
    (hxnon : 0 ≤ P.getLast! 0) (hynon : 0 ≤ P.getLast! 1) :
    0 < P.getLast! 0 ∧ (3 < P.getLast! 1 ∨ P.getLast! 0 < P.getLast! 1) := by
  let m := P.length - 1
  have hmge : 2 ≤ m := by omega
  have hlast : P.getLast! = P[m]! := by
    have hp : 0 < P.length := by omega
    simpa [m] using getLast!_eq_getElem! P hp
  have hxnon' : 0 ≤ P[m]! 0 := by
    rw [← hlast]
    exact hxnon
  have hynon' : 0 ≤ P[m]! 1 := by
    rw [← hlast]
    exact hynon
  let k := m / 4
  have hdecomp : 4 * k + m % 4 = m := by simpa [k] using Nat.div_add_mod m 4
  have hmodlt : m % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases hmod : m % 4
  · have hm0 : m = 4 * k := by omega
    have hk : 1 ≤ k := by omega
    have hneg := point4_neg h0 hmono hsteps k hk (by omega)
    have hxneg : P[m]! 0 < 0 := by simpa [hm0] using hneg.1
    omega
  · have hm1 : m = 4 * k + 1 := by omega
    have hk : 1 ≤ k := by omega
    have hyneg := point4p1_y_neg h0 hmono hsteps k hk (by omega)
    have hyneg' : P[m]! 1 < 0 := by simpa [hm1] using hyneg
    omega
  · have hm2 : m = 4 * k + 2 := by omega
    have hg := point4p2_pos h0 hpos hmono hsteps k (by omega)
    have hxpos : 0 < P[m]! 0 := by simpa [hm2] using hg.1
    have hybd : ((2 + 2 * k : ℕ) : ℤ) ≤ P[m]! 1 := by simpa [hm2] using hg.2.1
    have hlt0 : k = 0 → P[m]! 0 < P[m]! 1 := by
      intro hk0
      simpa [hm2] using hg.2.2 hk0
    constructor
    · rw [hlast]
      exact hxpos
    · by_cases hk0 : k = 0
      · right
        rw [hlast]
        exact hlt0 hk0
      · left
        have hkpos : 1 ≤ k := by omega
        have : (3 : ℤ) < P[m]! 1 := by omega
        rw [hlast]
        exact this
  · have hm3 : m = 4 * k + 3 := by omega
    have hxneg := point4p3_x_neg h0 hmono hsteps k (by omega)
    have hxneg' : P[m]! 0 < 0 := by simpa [hm3] using hxneg
    omega

def spiral2 (x y : ℕ) : List Point := [zpt 0 0, zpt x 0, zpt x y]

def spiral6 (x y : ℕ) : List Point :=
  [zpt 0 0, zpt 1 0, zpt 1 2, zpt (-2) 2,
    zpt (-2) ((y : ℤ) - x - 3), zpt x ((y : ℤ) - x - 3), zpt x y]

def len6 (x y : ℕ) : Fin 6 → ℕ := ![1, 2, 3, x - y + 5, x + 2, x + 3]

lemma isSpiral_spiral2 (IsSpiral : List Point → Prop)
    (IsSpiral_def : ∀ P, IsSpiral P ↔ P.length ≥ 3 ∧ P[0]! = 0 ∧
  (∃ l : Fin (P.length - 1) → ℕ, (∀ i, 0 < l i) ∧ StrictMono l ∧ (∀ i : Fin (P.length - 1),
    (i.1 % 4 = 0 → (P[i] 0 + l i = P[i.1 + 1]! 0 ∧ P[i] 1 = P[i.1 + 1]! 1)) ∧
    (i.1 % 4 = 1 → (P[i] 0 = P[i.1 + 1]! 0 ∧ P[i] 1 + l i = P[i.1 + 1]! 1)) ∧
    (i.1 % 4 = 2 → (P[i] 0 - l i = P[i.1 + 1]! 0 ∧ P[i] 1 = P[i.1 + 1]! 1)) ∧
    (i.1 % 4 = 3 → (P[i] 0 = P[i.1 + 1]! 0 ∧ P[i] 1 - l i = P[i.1 + 1]! 1)))))
    {x y : ℕ} (hx : 0 < x) (hxy : x < y) : IsSpiral (spiral2 x y) := by
  rw [IsSpiral_def]
  refine ⟨?_, ?_, ?_⟩
  · norm_num [spiral2]
  · ext i <;> fin_cases i <;> norm_num [spiral2, zpt]
  · change ∃ l : Fin 2 → ℕ, (∀ i, 0 < l i) ∧ StrictMono l ∧ _
    refine ⟨![x, y], ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [hx, Nat.lt_trans hx hxy]
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    · intro i
      fin_cases i <;> simp [spiral2, zpt]

lemma isSpiral_spiral6 (IsSpiral : List Point → Prop)
    (IsSpiral_def : ∀ P, IsSpiral P ↔ P.length ≥ 3 ∧ P[0]! = 0 ∧
  (∃ l : Fin (P.length - 1) → ℕ, (∀ i, 0 < l i) ∧ StrictMono l ∧ (∀ i : Fin (P.length - 1),
    (i.1 % 4 = 0 → (P[i] 0 + l i = P[i.1 + 1]! 0 ∧ P[i] 1 = P[i.1 + 1]! 1)) ∧
    (i.1 % 4 = 1 → (P[i] 0 = P[i.1 + 1]! 0 ∧ P[i] 1 + l i = P[i.1 + 1]! 1)) ∧
    (i.1 % 4 = 2 → (P[i] 0 - l i = P[i.1 + 1]! 0 ∧ P[i] 1 = P[i.1 + 1]! 1)) ∧
    (i.1 % 4 = 3 → (P[i] 0 = P[i.1 + 1]! 0 ∧ P[i] 1 - l i = P[i.1 + 1]! 1)))))
    {x y : ℕ} (hy : 4 ≤ y) (hyx : y ≤ x) : IsSpiral (spiral6 x y) := by
  rw [IsSpiral_def]
  refine ⟨?_, ?_, ?_⟩
  · norm_num [spiral6]
  · ext i <;> fin_cases i <;> norm_num [spiral6, zpt]
  · change ∃ l : Fin 6 → ℕ, (∀ i, 0 < l i) ∧ StrictMono l ∧ _
    refine ⟨len6 x y, ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [len6] <;> omega
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp [len6] at hij ⊢ <;> omega
    · intro i
      fin_cases i <;> simp [spiral6, zpt, len6] <;> omega

def badColumn : Finset Point := (Finset.Icc (0 : ℤ) 2011).image fun y => zpt 0 y

def badRow (y lo : ℤ) : Finset Point := (Finset.Icc lo 2011).image fun x => zpt x y

def Bad (p : Point) : Prop := p 0 = 0 ∨ (p 1 ≤ 3 ∧ p 1 ≤ p 0)

def badFinset : Finset Point :=
  badColumn ∪ badRow 0 1 ∪ badRow 1 1 ∪ badRow 2 2 ∪ badRow 3 3

lemma badColumn_card : badColumn.card = 2012 := by
  rw [badColumn, Finset.card_image_of_injOn]
  · rw [Int.card_Icc]
    rfl
  · intro a ha b hb h
    have hcoord := congrFun h 1
    simpa [zpt] using hcoord

lemma badRow_card (y lo : ℤ) :
    (badRow y lo).card = (2012 - lo).toNat := by
  rw [badRow, Finset.card_image_of_injOn]
  · rw [Int.card_Icc]
    ring_nf
  · intro a ha b hb h
    have hcoord := congrFun h 0
    simpa [zpt] using hcoord

lemma badColumn_disjoint_badRow {y lo : ℤ} (hlo : 1 ≤ lo) :
    Disjoint badColumn (badRow y lo) := by
  rw [Finset.disjoint_iff_ne]
  intro p hp q hq hpq
  rcases Finset.mem_image.mp hp with ⟨yp, hyp, rfl⟩
  rcases Finset.mem_image.mp hq with ⟨xq, hxq, rfl⟩
  have hxlo : lo ≤ xq := (Finset.mem_Icc.mp hxq).1
  have hcoord := congrFun hpq 0
  simp [zpt] at hcoord
  omega

lemma badRow_disjoint {y₁ y₂ lo₁ lo₂ : ℤ} (hy : y₁ ≠ y₂) :
    Disjoint (badRow y₁ lo₁) (badRow y₂ lo₂) := by
  rw [Finset.disjoint_iff_ne]
  intro p hp q hq hpq
  rcases Finset.mem_image.mp hp with ⟨xp, hxp, rfl⟩
  rcases Finset.mem_image.mp hq with ⟨xq, hxq, rfl⟩
  have hcoord := congrFun hpq 1
  exact hy (by simpa [zpt] using hcoord)

lemma badFinset_card : badFinset.card = 10053 := by
  have hc := badColumn_card
  have hr0 : (badRow 0 1).card = 2011 := by
    simpa using badRow_card 0 1
  have hr1 : (badRow 1 1).card = 2011 := by
    simpa using badRow_card 1 1
  have hr2 : (badRow 2 2).card = 2010 := by
    simpa using badRow_card 2 2
  have hr3 : (badRow 3 3).card = 2009 := by
    simpa using badRow_card 3 3
  have hd01 : Disjoint badColumn (badRow 0 1) := badColumn_disjoint_badRow (by norm_num)
  have hd02 : Disjoint badColumn (badRow 1 1) := badColumn_disjoint_badRow (by norm_num)
  have hd03 : Disjoint badColumn (badRow 2 2) := badColumn_disjoint_badRow (by norm_num)
  have hd04 : Disjoint badColumn (badRow 3 3) := badColumn_disjoint_badRow (by norm_num)
  have hd12 : Disjoint (badRow 0 1) (badRow 1 1) := badRow_disjoint (by norm_num)
  have hd13 : Disjoint (badRow 0 1) (badRow 2 2) := badRow_disjoint (by norm_num)
  have hd14 : Disjoint (badRow 0 1) (badRow 3 3) := badRow_disjoint (by norm_num)
  have hd23 : Disjoint (badRow 1 1) (badRow 2 2) := badRow_disjoint (by norm_num)
  have hd24 : Disjoint (badRow 1 1) (badRow 3 3) := badRow_disjoint (by norm_num)
  have hd34 : Disjoint (badRow 2 2) (badRow 3 3) := badRow_disjoint (by norm_num)
  have hd_u01_2 : Disjoint (badColumn ∪ badRow 0 1) (badRow 1 1) := by
    rw [Finset.disjoint_union_left]
    exact ⟨hd02, hd12⟩
  have hd_u012_3 : Disjoint ((badColumn ∪ badRow 0 1) ∪ badRow 1 1) (badRow 2 2) := by
    rw [Finset.disjoint_union_left]
    refine ⟨?_, hd23⟩
    rw [Finset.disjoint_union_left]
    exact ⟨hd03, hd13⟩
  have hd_u0123_4 :
      Disjoint (((badColumn ∪ badRow 0 1) ∪ badRow 1 1) ∪ badRow 2 2) (badRow 3 3) := by
    rw [Finset.disjoint_union_left]
    refine ⟨?_, hd34⟩
    rw [Finset.disjoint_union_left]
    refine ⟨?_, hd24⟩
    rw [Finset.disjoint_union_left]
    exact ⟨hd04, hd14⟩
  rw [badFinset]
  rw [Finset.card_union_of_disjoint hd_u0123_4]
  rw [Finset.card_union_of_disjoint hd_u012_3]
  rw [Finset.card_union_of_disjoint hd_u01_2]
  rw [Finset.card_union_of_disjoint hd01]
  rw [hc, hr0, hr1, hr2, hr3]

lemma mem_badColumn_iff (p : Point) :
    p ∈ badColumn ↔ p 0 = 0 ∧ 0 ≤ p 1 ∧ p 1 ≤ 2011 := by
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨y, hy, rfl⟩
    have hy' := Finset.mem_Icc.mp hy
    simp [zpt, hy']
  · intro hp
    rcases hp with ⟨hx, hy0, hy1⟩
    refine Finset.mem_image.mpr ⟨p 1, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨hy0, hy1⟩
    · ext i <;> fin_cases i <;> simp [zpt, hx]

lemma mem_badRow_iff (p : Point) (y lo : ℤ) :
    p ∈ badRow y lo ↔ lo ≤ p 0 ∧ p 0 ≤ 2011 ∧ p 1 = y := by
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨x, hx, rfl⟩
    have hx' := Finset.mem_Icc.mp hx
    simp [zpt, hx']
  · intro hp
    rcases hp with ⟨hx0, hx1, hy⟩
    refine Finset.mem_image.mpr ⟨p 0, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨hx0, hx1⟩
    · ext i <;> fin_cases i <;> simp [zpt, hy]

lemma mem_badFinset_iff (p : Point) :
    p ∈ badFinset ↔
      0 ≤ p 0 ∧ p 0 ≤ 2011 ∧ 0 ≤ p 1 ∧ p 1 ≤ 2011 ∧ Bad p := by
  constructor
  · intro hp
    rw [badFinset] at hp
    simp only [Finset.mem_union] at hp
    rcases hp with hp0123 | hp
    · rcases hp0123 with hp012 | hp
      · rcases hp012 with hp01 | hp
        · rcases hp01 with hp | hp
          · rw [mem_badColumn_iff] at hp
            rcases hp with ⟨hx, hy0, hy1⟩
            exact ⟨by omega, by omega, hy0, hy1, Or.inl hx⟩
          · rw [mem_badRow_iff] at hp
            rcases hp with ⟨hx0, hx1, hy⟩
            exact ⟨by omega, hx1, by omega, by omega, Or.inr ⟨by omega, by omega⟩⟩
        · rw [mem_badRow_iff] at hp
          rcases hp with ⟨hx0, hx1, hy⟩
          exact ⟨by omega, hx1, by omega, by omega, Or.inr ⟨by omega, by omega⟩⟩
      · rw [mem_badRow_iff] at hp
        rcases hp with ⟨hx0, hx1, hy⟩
        exact ⟨by omega, hx1, by omega, by omega, Or.inr ⟨by omega, by omega⟩⟩
    · rw [mem_badRow_iff] at hp
      rcases hp with ⟨hx, hy0, hy1⟩
      exact ⟨by omega, hy0, by omega, by omega, Or.inr ⟨by omega, by omega⟩⟩
  · intro hp
    rcases hp with ⟨hx0, hx1, hy0, hy1, hbad⟩
    rw [badFinset]
    simp only [Finset.mem_union]
    by_cases hxzero : p 0 = 0
    · exact Or.inl (Or.inl (Or.inl (Or.inl ((mem_badColumn_iff p).2 ⟨hxzero, hy0, hy1⟩))))
    rcases hbad with hx | ⟨hy3, hyx⟩
    · exact (False.elim (hxzero hx))
    · have hxpos : 1 ≤ p 0 := by omega
      have hy_cases : p 1 = 0 ∨ p 1 = 1 ∨ p 1 = 2 ∨ p 1 = 3 := by omega
      rcases hy_cases with hy | hy | hy | hy
      · exact Or.inl (Or.inl (Or.inl (Or.inr ((mem_badRow_iff p 0 1).2 ⟨hxpos, hx1, hy⟩))))
      · exact Or.inl (Or.inl (Or.inr ((mem_badRow_iff p 1 1).2 ⟨hxpos, hx1, hy⟩)))
      · exact Or.inl (Or.inr ((mem_badRow_iff p 2 2).2 ⟨by omega, hx1, hy⟩))
      · exact Or.inr ((mem_badRow_iff p 3 3).2 ⟨by omega, hx1, hy⟩)

end Putnam2011A1

-- 10053
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
  {p | 0 ≤ p 0 ∧ p 0 ≤ 2011 ∧ 0 ≤ p 1 ∧ p 1 ≤ 2011 ∧ ¬∃ spiral, IsSpiral spiral ∧ spiral.getLast! = p}.encard = ((10053) : ℕ ) := by
  classical
  have hset :
      {p | 0 ≤ p 0 ∧ p 0 ≤ 2011 ∧ 0 ≤ p 1 ∧ p 1 ≤ 2011 ∧
        ¬∃ spiral, IsSpiral spiral ∧ spiral.getLast! = p} =
        (Putnam2011A1.badFinset : Set (Fin 2 → ℤ)) := by
    ext p
    constructor
    · intro hp
      rcases hp with ⟨hx0, hx1, hy0, hy1, hnot⟩
      have hbad : Putnam2011A1.Bad p := by
        by_contra hnotbad
        have hxne : p 0 ≠ 0 := by
          intro hx
          exact hnotbad (Or.inl hx)
        have hxpos : 0 < p 0 := by omega
        have hnot_small : ¬(p 1 ≤ 3 ∧ p 1 ≤ p 0) := by
          intro hsmall
          exact hnotbad (Or.inr hsmall)
        let x : ℕ := (p 0).toNat
        let y : ℕ := (p 1).toNat
        have hxcast : (x : ℤ) = p 0 := by
          simpa [x] using Int.toNat_of_nonneg hx0
        have hycast : (y : ℤ) = p 1 := by
          simpa [y] using Int.toNat_of_nonneg hy0
        by_cases hxy : p 0 < p 1
        · have hxnat : 0 < x := by omega
          have hxynat : x < y := by omega
          have hspiral := Putnam2011A1.isSpiral_spiral2 IsSpiral IsSpiral_def hxnat hxynat
          exact hnot ⟨Putnam2011A1.spiral2 x y, hspiral, by
            ext i <;> fin_cases i <;> simp [Putnam2011A1.spiral2, Putnam2011A1.zpt, hxcast, hycast]⟩
        · have hylarge : 4 ≤ p 1 := by omega
          have hyx : p 1 ≤ p 0 := by omega
          have hynat : 4 ≤ y := by omega
          have hyxnat : y ≤ x := by omega
          have hspiral := Putnam2011A1.isSpiral_spiral6 IsSpiral IsSpiral_def hynat hyxnat
          exact hnot ⟨Putnam2011A1.spiral6 x y, hspiral, by
            ext i <;> fin_cases i <;> simp [Putnam2011A1.spiral6, Putnam2011A1.zpt, hxcast, hycast]⟩
      exact (Putnam2011A1.mem_badFinset_iff p).2 ⟨hx0, hx1, hy0, hy1, hbad⟩
    · intro hp
      have hmem := (Putnam2011A1.mem_badFinset_iff p).1 hp
      rcases hmem with ⟨hx0, hx1, hy0, hy1, hbad⟩
      refine ⟨hx0, hx1, hy0, hy1, ?_⟩
      intro hex
      rcases hex with ⟨spiral, hspiral, hlast⟩
      rw [IsSpiral_def] at hspiral
      rcases hspiral with ⟨hlen, hzero, l, hpos, hmono, hsteps⟩
      have hsteps' : Putnam2011A1.StepSpec spiral l := by
        simpa [Putnam2011A1.StepSpec] using hsteps
      have hxlast : 0 ≤ spiral.getLast! 0 := by
        rw [hlast]
        exact hx0
      have hylast : 0 ≤ spiral.getLast! 1 := by
        rw [hlast]
        exact hy0
      have hgood := Putnam2011A1.endpoint_good hlen hzero hpos hmono hsteps' hxlast hylast
      rw [hlast] at hgood
      rcases hbad with hxzero | ⟨hy3, hyx⟩
      · omega
      · rcases hgood.2 with hygt | hxlt
        · omega
        · omega
  rw [hset]
  simpa [Putnam2011A1.badFinset_card] using
    (Set.encard_coe_eq_coe_finsetCard Putnam2011A1.badFinset)
