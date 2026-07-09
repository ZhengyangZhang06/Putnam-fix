import Mathlib

open Filter Topology Set

abbrev putnam_2020_a5_solution : ℤ :=
  ((∑ k ∈ Finset.Icc 2 2020, Nat.fib (2 * k - 1) : ℕ) : ℤ)

private abbrev fibSum (S : Finset ℕ) : ℕ := ∑ k ∈ S, Nat.fib k

private abbrev pref (m : ℕ) : Finset ℕ := Finset.Icc 1 m

private def repsBounded (m n : ℕ) : Finset (Finset ℕ) :=
  (pref m).powerset.filter fun S => fibSum S = n

private def C (m n : ℕ) : ℕ := (repsBounded m n).card

private def A (n : ℕ) : ℕ := C (Nat.greatestFib n) n

private lemma mem_repsBounded {m n : ℕ} {S : Finset ℕ} :
    S ∈ repsBounded m n ↔ S ⊆ pref m ∧ fibSum S = n := by
  simp [repsBounded]

private lemma fibSum_pref (m : ℕ) : fibSum (pref m) = Nat.fib (m + 2) - 1 := by
  induction m with
  | zero => simp [fibSum, pref]
  | succ m ih =>
      dsimp [fibSum, pref] at ih ⊢
      rw [Finset.sum_Icc_succ_top]
      · rw [ih]
        rw [show Nat.fib (m + 1 + 2) = Nat.fib (m + 1) + Nat.fib (m + 2) by
          simpa [add_assoc] using (Nat.fib_add_two (n := m + 1))]
        have hpos : 0 < Nat.fib (m + 2) := by simp
        omega
      · omega

private lemma C_eq_A_of_lt {m n : ℕ} (h : n < Nat.fib (m + 1)) :
    C m n = A n := by
  unfold C A
  congr 1
  ext S
  rw [mem_repsBounded, mem_repsBounded]
  constructor
  · intro hS
    constructor
    · intro k hk
      have hkpos : 1 ≤ k := (Finset.mem_Icc.mp (hS.1 hk)).1
      have hle_sum : Nat.fib k ≤ fibSum S :=
        Finset.single_le_sum (by intro i hi; exact Nat.zero_le _) hk
      have hle_n : Nat.fib k ≤ n := by simpa [hS.2] using hle_sum
      exact Finset.mem_Icc.mpr ⟨hkpos, Nat.le_greatestFib.mpr hle_n⟩
    · exact hS.2
  · intro hS
    constructor
    · intro k hk
      have hgf : Nat.greatestFib n ≤ m :=
        Nat.lt_succ_iff.mp (Nat.greatestFib_lt.mpr h)
      have hk' := hS.1 hk
      exact Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hk').1, le_trans (Finset.mem_Icc.mp hk').2 hgf⟩
    · exact hS.2

private lemma erase_top_mem_reps {m n : ℕ} {S : Finset ℕ}
    (hm : 1 ≤ m) (hn : Nat.fib m ≤ n)
    (hS : S ∈ repsBounded m n) (hmem : m ∈ S) :
    S.erase m ∈ repsBounded (m - 1) (n - Nat.fib m) := by
  rw [mem_repsBounded] at hS ⊢
  constructor
  · intro k hk
    have hkS : k ∈ S := Finset.mem_of_mem_erase hk
    have hkm : k ≠ m := (Finset.mem_erase.mp hk).1
    have hp := Finset.mem_Icc.mp (hS.1 hkS)
    exact Finset.mem_Icc.mpr ⟨hp.1, by omega⟩
  · have hsum := Finset.sum_erase_add S Nat.fib hmem
    dsimp [fibSum] at hsum hS ⊢
    omega

private lemma with_top_card_eq {m n : ℕ} (hm : 1 ≤ m) (hn : Nat.fib m ≤ n) :
    ((repsBounded m n).filter (fun S => m ∈ S)).card =
      C (m - 1) (n - Nat.fib m) := by
  unfold C
  refine Finset.card_bij (fun S _ => S.erase m) ?_ ?_ ?_
  · intro S hS
    rw [Finset.mem_filter] at hS
    exact erase_top_mem_reps hm hn hS.1 hS.2
  · intro S hS T hT hEq
    rw [Finset.mem_filter] at hS hT
    change S.erase m = T.erase m at hEq
    calc
      S = insert m (S.erase m) := (Finset.insert_erase hS.2).symm
      _ = insert m (T.erase m) := by rw [hEq]
      _ = T := Finset.insert_erase hT.2
  · intro T hT
    refine ⟨insert m T, ?_, ?_⟩
    · rw [Finset.mem_filter]
      constructor
      · rw [mem_repsBounded] at hT ⊢
        constructor
        · intro k hk
          rw [Finset.mem_insert] at hk
          rcases hk with rfl | hkT
          · exact Finset.mem_Icc.mpr ⟨hm, le_rfl⟩
          · have hp := Finset.mem_Icc.mp (hT.1 hkT)
            exact Finset.mem_Icc.mpr ⟨hp.1, by omega⟩
        · have hnot : m ∉ T := by
            intro hmT
            have hp := Finset.mem_Icc.mp (hT.1 hmT)
            omega
          dsimp [fibSum] at hT ⊢
          rw [Finset.sum_insert hnot]
          omega
      · simp
    · have hnot : m ∉ T := by
        rw [mem_repsBounded] at hT
        intro hmT
        have hp := Finset.mem_Icc.mp (hT.1 hmT)
        omega
      simp [hnot]

private lemma subset_pref_pred_of_not_top {m : ℕ} {S : Finset ℕ}
    (hS : S ⊆ pref m) (hnot : m ∉ S) : S ⊆ pref (m - 1) := by
  intro k hk
  have hp := Finset.mem_Icc.mp (hS hk)
  have hkm : k ≠ m := by rintro rfl; exact hnot hk
  exact Finset.mem_Icc.mpr ⟨hp.1, by omega⟩

private lemma without_top_card_eq {m n : ℕ} (hm : 1 ≤ m)
    (hnhi : n < Nat.fib (m + 1)) :
    ((repsBounded m n).filter (fun S => m ∉ S)).card =
      C (m - 1) (Nat.fib (m + 1) - 1 - n) := by
  unfold C
  let P := pref (m - 1)
  refine Finset.card_bij (fun S _ => P \ S) ?_ ?_ ?_
  · intro S hS
    rw [Finset.mem_filter] at hS
    rw [mem_repsBounded] at hS
    rw [mem_repsBounded]
    have hsubP : S ⊆ P := subset_pref_pred_of_not_top hS.1.1 hS.2
    constructor
    · exact Finset.sdiff_subset
    · have hsum := Finset.sum_sdiff hsubP (f := Nat.fib)
      have htotal := fibSum_pref (m - 1)
      dsimp [fibSum, P] at hsum htotal hS ⊢
      have hmadd : m - 1 + 2 = m + 1 := by omega
      rw [hmadd] at htotal
      omega
  · intro S hS T hT hEq
    rw [Finset.mem_filter] at hS hT
    rw [mem_repsBounded] at hS hT
    change P \ S = P \ T at hEq
    have hSsub : S ⊆ P := subset_pref_pred_of_not_top hS.1.1 hS.2
    have hTsub : T ⊆ P := subset_pref_pred_of_not_top hT.1.1 hT.2
    calc
      S = P \ (P \ S) := (Finset.sdiff_sdiff_eq_self hSsub).symm
      _ = P \ (P \ T) := by rw [hEq]
      _ = T := Finset.sdiff_sdiff_eq_self hTsub
  · intro T hT
    refine ⟨P \ T, ?_, ?_⟩
    · rw [Finset.mem_filter]
      constructor
      · rw [mem_repsBounded] at hT ⊢
        have hTsub : T ⊆ P := hT.1
        constructor
        · intro k hk
          have hkP := Finset.sdiff_subset hk
          have hp := Finset.mem_Icc.mp hkP
          exact Finset.mem_Icc.mpr ⟨hp.1, by omega⟩
        · have hsum := Finset.sum_sdiff hTsub (f := Nat.fib)
          have htotal := fibSum_pref (m - 1)
          dsimp [fibSum, P] at hsum htotal hT ⊢
          have hmadd : m - 1 + 2 = m + 1 := by omega
          rw [hmadd] at htotal
          omega
      · intro hmP
        have hp := Finset.mem_sdiff.mp hmP
        have hmemP := Finset.mem_Icc.mp hp.1
        omega
    · rw [mem_repsBounded] at hT
      change P \ (P \ T) = T
      exact Finset.sdiff_sdiff_eq_self hT.1

private lemma A_rec {m n : ℕ} (hm : 1 ≤ m)
    (hnlo : Nat.fib m ≤ n) (hnhi : n < Nat.fib (m + 1)) :
    A n = A (n - Nat.fib m) + A (Nat.fib (m + 1) - 1 - n) := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := repsBounded m n) (p := fun S => m ∈ S)
  have hsplit' : (repsBounded m n).card =
      ((repsBounded m n).filter (fun S => m ∈ S)).card +
        ((repsBounded m n).filter (fun S => m ∉ S)).card := by
    omega
  have hwith := with_top_card_eq (m := m) (n := n) hm hnlo
  have hwithout := without_top_card_eq (m := m) (n := n) hm hnhi
  have hmne : m ≠ 0 := by omega
  have hfib : Nat.fib (m + 1) = Nat.fib (m - 1) + Nat.fib m :=
    Nat.fib_add_one hmne
  have hle_fib : Nat.fib (m - 1) ≤ Nat.fib m := Nat.fib_mono (by omega)
  have hmadd : m - 1 + 1 = m := by omega
  have htlt : n - Nat.fib m < Nat.fib ((m - 1) + 1) := by
    rw [hmadd]
    omega
  have hvlt : Nat.fib (m + 1) - 1 - n < Nat.fib ((m - 1) + 1) := by
    rw [hmadd]
    omega
  have htA := C_eq_A_of_lt (m := m - 1) (n := n - Nat.fib m) htlt
  have hvA := C_eq_A_of_lt
    (m := m - 1) (n := Nat.fib (m + 1) - 1 - n) hvlt
  calc
    A n = C m n := (C_eq_A_of_lt (m := m) (n := n) hnhi).symm
    _ = (repsBounded m n).card := rfl
    _ = ((repsBounded m n).filter (fun S => m ∈ S)).card +
        ((repsBounded m n).filter (fun S => m ∉ S)).card := hsplit'
    _ = C (m - 1) (n - Nat.fib m) +
        C (m - 1) (Nat.fib (m + 1) - 1 - n) := by
      rw [hwith, hwithout]
    _ = A (n - Nat.fib m) + A (Nat.fib (m + 1) - 1 - n) := by
      rw [htA, hvA]

private lemma A_zero : A 0 = 1 := by
  decide

private lemma A_fib_even_sub_one_succ (r : ℕ) :
    A (Nat.fib (2 * (r + 1)) - 1) = r + 1 := by
  induction r with
  | zero =>
      simpa using A_zero
  | succ r ih =>
      change A (Nat.fib (2 * r + 4) - 1) = r + 2
      have hmlo : 1 ≤ 2 * r + 3 := by omega
      have hltfib : Nat.fib (2 * r + 3) < Nat.fib (2 * r + 4) := by
        simpa [show 2 * r + 3 + 1 = 2 * r + 4 by omega] using
          (Nat.fib_lt_fib_succ (n := 2 * r + 3) (by omega))
      have hnlo : Nat.fib (2 * r + 3) ≤ Nat.fib (2 * r + 4) - 1 := by
        omega
      have hnhi : Nat.fib (2 * r + 4) - 1 < Nat.fib ((2 * r + 3) + 1) := by
        rw [show (2 * r + 3) + 1 = 2 * r + 4 by omega]
        have hpos : 0 < Nat.fib (2 * r + 4) := by simp
        omega
      have hrec := A_rec (m := 2 * r + 3) (n := Nat.fib (2 * r + 4) - 1)
        hmlo hnlo hnhi
      have hfib : Nat.fib (2 * r + 4) =
          Nat.fib (2 * r + 2) + Nat.fib (2 * r + 3) := by
        have h := Nat.fib_add_two (n := 2 * r + 2)
        rw [show 2 * r + 2 + 2 = 2 * r + 4 by omega,
          show 2 * r + 2 + 1 = 2 * r + 3 by omega] at h
        exact h
      have ht : Nat.fib (2 * r + 4) - 1 - Nat.fib (2 * r + 3) =
          Nat.fib (2 * r + 2) - 1 := by
        omega
      have hv : Nat.fib ((2 * r + 3) + 1) - 1 -
          (Nat.fib (2 * r + 4) - 1) = 0 := by
        rw [show (2 * r + 3) + 1 = 2 * r + 4 by omega]
        omega
      rw [ht, hv, A_zero] at hrec
      have ih' : A (Nat.fib (2 * r + 2) - 1) = r + 1 := by
        simpa [show 2 * (r + 1) = 2 * r + 2 by ring] using ih
      rw [ih'] at hrec
      omega

private lemma A_pos (n : ℕ) : 0 < A n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        rw [A_zero]
        norm_num
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        let m := Nat.greatestFib n
        have hm2 : 2 ≤ m := by
          rw [Nat.le_greatestFib]
          simpa using hnpos
        have hm1 : 1 ≤ m := by omega
        have hnlo : Nat.fib m ≤ n := Nat.fib_greatestFib_le n
        have hnhi : n < Nat.fib (m + 1) := Nat.lt_fib_greatestFib_add_one n
        have hrec := A_rec (m := m) (n := n) hm1 hnlo hnhi
        have hfgpos : 0 < Nat.fib m := by
          simpa using (Nat.fib_pos.mpr (by omega : 0 < m))
        have htlt : n - Nat.fib m < n := by omega
        have hmne : m ≠ 0 := by omega
        have hfib : Nat.fib (m + 1) = Nat.fib (m - 1) + Nat.fib m :=
          Nat.fib_add_one hmne
        have hle_fib : Nat.fib (m - 1) ≤ Nat.fib m := Nat.fib_mono (by omega)
        have hvlt : Nat.fib (m + 1) - 1 - n < n := by omega
        have htpos := ih (n - Nat.fib m) htlt
        have hvpos := ih (Nat.fib (m + 1) - 1 - n) hvlt
        omega

private lemma fib_even_add_le {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    Nat.fib (2 * p) + Nat.fib (2 * q) ≤ Nat.fib (2 * (p + q) - 1) := by
  wlog hpq : p ≤ q generalizing p q with H
  · have hqp : q ≤ p := le_of_not_ge hpq
    simpa [Nat.add_comm, add_comm] using H hq hp hqp
  by_cases hp1 : p = 1
  · subst p
    have hfib : Nat.fib (2 * q + 1) = Nat.fib (2 * q - 1) + Nat.fib (2 * q) :=
      Nat.fib_add_one (n := 2 * q) (by omega)
    have hpos : 0 < Nat.fib (2 * q - 1) := by
      rw [Nat.fib_pos]
      omega
    rw [show 2 * (1 + q) - 1 = 2 * q + 1 by omega, hfib]
    norm_num
    omega
  · have hp2 : 2 ≤ p := by omega
    have hmono₁ : Nat.fib (2 * p) ≤ Nat.fib (2 * q) := Nat.fib_mono (by omega)
    have hmono₂ : Nat.fib (2 * q) ≤ Nat.fib (2 * q + 1) := Nat.fib_mono (by omega)
    have htwo : Nat.fib (2 * p) + Nat.fib (2 * q) ≤ Nat.fib (2 * q + 2) := by
      rw [Nat.fib_add_two]
      omega
    exact le_trans htwo (Nat.fib_mono (by omega))

private lemma A_eq_bound_succ (R n : ℕ) (hA : A n = R + 1) :
    n ≤ Nat.fib (2 * (R + 1)) - 1 := by
  induction R using Nat.strong_induction_on generalizing n with
  | h R ih =>
      by_contra hnot
      have hlarge : Nat.fib (2 * (R + 1)) ≤ n := by
        have hpos : 0 < Nat.fib (2 * (R + 1)) := by
          rw [Nat.fib_pos]
          omega
        omega
      let m := Nat.greatestFib n
      have hmge : 2 * (R + 1) ≤ m := Nat.le_greatestFib.mpr hlarge
      have hm1 : 1 ≤ m := by omega
      have hnlo : Nat.fib m ≤ n := Nat.fib_greatestFib_le n
      have hnhi : n < Nat.fib (m + 1) := Nat.lt_fib_greatestFib_add_one n
      let t := n - Nat.fib m
      let v := Nat.fib (m + 1) - 1 - n
      have hrec := A_rec (m := m) (n := n) hm1 hnlo hnhi
      have hpq : A t + A v = R + 1 := by
        change A n = A t + A v at hrec
        omega
      have htpos : 1 ≤ A t := A_pos t
      have hvpos : 1 ≤ A v := A_pos v
      have hRpos : 1 ≤ R := by omega
      have htltR : A t - 1 < R := by omega
      have hvltR : A v - 1 < R := by omega
      have htcount : A t - 1 + 1 = A t := by omega
      have hvcount : A v - 1 + 1 = A v := by omega
      have htbound : t ≤ Nat.fib (2 * A t) - 1 := by
        simpa [htcount] using ih (A t - 1) htltR t (by simp [htcount])
      have hvbound : v ≤ Nat.fib (2 * A v) - 1 := by
        simpa [hvcount] using ih (A v - 1) hvltR v (by simp [hvcount])
      have hmne : m ≠ 0 := by omega
      have hfibm : Nat.fib (m + 1) = Nat.fib (m - 1) + Nat.fib m :=
        Nat.fib_add_one hmne
      have hsum_eq : t + v = Nat.fib (m - 1) - 1 := by
        dsimp [t, v]
        omega
      have hidx : 2 * R + 1 ≤ m - 1 := by omega
      have hsum_lower : Nat.fib (2 * R + 1) - 1 ≤ t + v := by
        have hfib_le : Nat.fib (2 * R + 1) ≤ Nat.fib (m - 1) :=
          Nat.fib_mono hidx
        omega
      have hpair := fib_even_add_le (p := A t) (q := A v) htpos hvpos
      rw [hpq] at hpair
      have hpair' : Nat.fib (2 * A t) + Nat.fib (2 * A v) ≤
          Nat.fib (2 * R + 1) := by
        simpa [show 2 * (R + 1) - 1 = 2 * R + 1 by omega] using hpair
      have hsum_upper : t + v ≤ Nat.fib (2 * R + 1) - 2 := by
        have hftpos : 0 < Nat.fib (2 * A t) := by
          rw [Nat.fib_pos]
          omega
        have hfvpos : 0 < Nat.fib (2 * A v) := by
          rw [Nat.fib_pos]
          omega
        omega
      have hfibR : 2 ≤ Nat.fib (2 * R + 1) := by
        have hidx3 : 3 ≤ 2 * R + 1 := by omega
        have hmono : Nat.fib 3 ≤ Nat.fib (2 * R + 1) := Nat.fib_mono hidx3
        norm_num at hmono
        exact hmono
      omega

private lemma original_count_eq_A (n : ℕ) :
    ({S : Finset ℕ |
      (∀ k ∈ S, k > 0) ∧ ∑ k : S, Nat.fib k = (n : ℤ)} : Set (Finset ℕ)).ncard = A n := by
  have hset :
      ({S : Finset ℕ |
        (∀ k ∈ S, k > 0) ∧ ∑ k : S, Nat.fib k = (n : ℤ)} : Set (Finset ℕ)) =
        (repsBounded (Nat.greatestFib n) n : Set (Finset ℕ)) := by
    ext S
    constructor
    · intro hS
      change S ∈ repsBounded (Nat.greatestFib n) n
      rw [mem_repsBounded]
      have hsum_int : (∑ k ∈ S, (Nat.fib k : ℤ)) = (n : ℤ) := by
        simpa [Finset.sum_attach S (fun k => (Nat.fib k : ℤ))] using hS.2
      have hsum_nat : fibSum S = n := by
        apply Int.ofNat.inj
        dsimp [fibSum]
        rw [Nat.cast_sum]
        exact hsum_int
      constructor
      · intro k hk
        have hkpos' : k > 0 := hS.1 k hk
        have hkpos : 1 ≤ k := by omega
        have hle_sum : Nat.fib k ≤ fibSum S :=
          Finset.single_le_sum (by intro i hi; exact Nat.zero_le _) hk
        have hle_n : Nat.fib k ≤ n := by simpa [hsum_nat] using hle_sum
        exact Finset.mem_Icc.mpr ⟨hkpos, Nat.le_greatestFib.mpr hle_n⟩
      · exact hsum_nat
    · intro hS
      change S ∈ repsBounded (Nat.greatestFib n) n at hS
      rw [mem_repsBounded] at hS
      constructor
      · intro k hk
        have hp := Finset.mem_Icc.mp (hS.1 hk)
        omega
      · have hsum_int : (∑ k ∈ S, (Nat.fib k : ℤ)) = (n : ℤ) := by
          rw [← hS.2]
          dsimp [fibSum]
          rw [Nat.cast_sum]
        simpa [Finset.sum_attach S (fun k => (Nat.fib k : ℤ))] using hsum_int
  rw [hset]
  unfold A C
  exact Set.ncard_coe_finset (repsBounded (Nat.greatestFib n) n)

private lemma a_nat_eq_A
    (a : ℤ → ℕ)
    (ha : a = fun n : ℤ =>
      {S : Finset ℕ | (∀ k ∈ S, k > 0) ∧ ∑ k : S, Nat.fib k = n}.ncard)
    (n : ℕ) : a (n : ℤ) = A n := by
  rw [ha]
  exact original_count_eq_A n

private lemma fib_odd_sum_range (m : ℕ) :
    (∑ k ∈ Finset.range m, Nat.fib (2 * k + 1)) = Nat.fib (2 * m) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      have hrec : Nat.fib (2 * m + 2) =
          Nat.fib (2 * m) + Nat.fib (2 * m + 1) := by
        simpa using (Nat.fib_add_two (n := 2 * m))
      rw [show 2 * (m + 1) = 2 * m + 2 by omega, hrec]

private lemma fib_odd_tail_sum_range (m : ℕ) :
    (∑ k ∈ Finset.range m, Nat.fib (2 * k + 3)) =
      Nat.fib (2 * (m + 1)) - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      have hrec : Nat.fib (2 * m + 4) =
          Nat.fib (2 * m + 2) + Nat.fib (2 * m + 3) := by
        have h := Nat.fib_add_two (n := 2 * m + 2)
        rw [show 2 * m + 2 + 2 = 2 * m + 4 by omega,
          show 2 * m + 2 + 1 = 2 * m + 3 by omega] at h
        exact h
      rw [show 2 * (m + 1 + 1) = 2 * m + 4 by omega, hrec]
      rw [show 2 * (m + 1) = 2 * m + 2 by omega]
      have hpos : 0 < Nat.fib (2 * m + 2) := by simp
      omega

private lemma fib_odd_tail_sum_Icc (m : ℕ) :
    (∑ k ∈ Finset.Icc 1 m, Nat.fib (2 * k + 1)) =
      Nat.fib (2 * (m + 1)) - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_Icc_succ_top]
      · rw [ih]
        have hrec : Nat.fib (2 * m + 4) =
            Nat.fib (2 * m + 2) + Nat.fib (2 * m + 3) := by
          have h := Nat.fib_add_two (n := 2 * m + 2)
          rw [show 2 * m + 2 + 2 = 2 * m + 4 by omega,
            show 2 * m + 2 + 1 = 2 * m + 3 by omega] at h
          exact h
        rw [show 2 * (m + 1 + 1) = 2 * m + 4 by omega, hrec]
        rw [show 2 * (m + 1) = 2 * m + 2 by omega]
        rw [show 2 * m + 2 + 1 = 2 * m + 3 by omega]
        have hpos : 0 < Nat.fib (2 * m + 2) := by simp
        omega
      · omega

private lemma fib_odd_sum_Icc_zero (m : ℕ) :
    (∑ k ∈ Finset.Icc 0 m, Nat.fib (2 * k + 1)) =
      Nat.fib (2 * (m + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_Icc_succ_top]
      · rw [ih]
        have hrec : Nat.fib (2 * (m + 1) + 2) =
            Nat.fib (2 * (m + 1)) + Nat.fib (2 * (m + 1) + 1) := by
          exact Nat.fib_add_two (n := 2 * (m + 1))
        rw [show 2 * (m + 1 + 1) = 2 * (m + 1) + 2 by omega, hrec]
      · omega

private lemma fib_odd_tail_sum_Icc_shift (m : ℕ) :
    (∑ k ∈ Finset.Icc 2 (m + 1), Nat.fib (2 * k - 1)) =
      Nat.fib (2 * (m + 1)) - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_Icc_succ_top]
      · rw [ih]
        have hrec : Nat.fib (2 * (m + 1) + 2) =
            Nat.fib (2 * (m + 1)) + Nat.fib (2 * (m + 1) + 1) := by
          exact Nat.fib_add_two (n := 2 * (m + 1))
        rw [show 2 * (m + 1 + 1) = 2 * (m + 1) + 2 by omega, hrec]
        rw [show 2 * (m + 1) + 2 - 1 = 2 * (m + 1) + 1 by omega]
        have hpos : 0 < Nat.fib (2 * (m + 1)) := by simp
        omega
      · omega

/--
Let $a_n$ be the number of sets $S$ of positive integers for which
\[
\sum_{k \in S} F_k = n,
\]
where the Fibonacci sequence $(F_k)_{k \geq 1}$ satisfies $F_{k+2} = F_{k+1} + F_k$ and begins $F_1 = 1, F_2 = 1, F_3 = 2, F_4 = 3$. Find the largest integer $n$ such that $a_n = 2020$.
-/
theorem putnam_2020_a5
  (a : ℤ → ℕ)
  (ha : a = fun n : ℤ => {S : Finset ℕ | (∀ k ∈ S, k > 0) ∧ ∑ k : S, Nat.fib k = n}.ncard) :
  IsGreatest {n | a n = 2020} putnam_2020_a5_solution :=
by
  have hsol_nat : putnam_2020_a5_solution = ((Nat.fib 4040 - 1 : ℕ) : ℤ) := by
    change (((∑ k ∈ Finset.Icc 2 2020, Nat.fib (2 * k - 1) : ℕ) : ℤ)) =
      ((Nat.fib 4040 - 1 : ℕ) : ℤ)
    have hsum_nat :
        (∑ k ∈ Finset.Icc 2 2020, Nat.fib (2 * k - 1)) = Nat.fib 4040 - 1 := by
      simpa [show 2019 + 1 = 2020 by norm_num,
        show 2 * (2019 + 1) = 4040 by norm_num] using
        (fib_odd_tail_sum_Icc_shift 2019)
    exact_mod_cast hsum_nat
  have hsol_nonneg : 0 ≤ putnam_2020_a5_solution := by
    rw [hsol_nat]
    exact Int.natCast_nonneg _
  constructor
  · change a putnam_2020_a5_solution = 2020
    rw [hsol_nat, a_nat_eq_A a ha]
    simpa using (A_fib_even_sub_one_succ 2019)
  · intro y hy
    change a y = 2020 at hy
    by_cases hyneg : y < 0
    · omega
    · have hy_nonneg : 0 ≤ y := le_of_not_gt hyneg
      let m : ℕ := y.toNat
      have hy_cast : (m : ℤ) = y := Int.toNat_of_nonneg hy_nonneg
      have hy' : a (m : ℤ) = 2020 := by simpa [hy_cast] using hy
      have hAm : A m = 2020 := by
        rw [← a_nat_eq_A a ha m]
        exact hy'
      have hbound := A_eq_bound_succ 2019 m (by simpa using hAm)
      have hbound_nat : m ≤ Nat.fib 4040 - 1 := by
        simpa using hbound
      have hbound_int : (m : ℤ) ≤ ((Nat.fib 4040 - 1 : ℕ) : ℤ) := by
        exact_mod_cast hbound_nat
      calc
        y = (m : ℤ) := hy_cast.symm
        _ ≤ ((Nat.fib 4040 - 1 : ℕ) : ℤ) := hbound_int
        _ = putnam_2020_a5_solution := hsol_nat.symm
