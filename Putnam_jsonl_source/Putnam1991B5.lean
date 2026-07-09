import Mathlib

open Filter Topology

-- (fun p : ℕ => Nat.ceil ((p : ℝ) / 4))
/--
Let $p$ be an odd prime and let $\mathbb{Z}_p$ denote (the field of) integers modulo $p$. How many elements are in the set $\{x^2:x \in \mathbb{Z}_p\} \cap \{y^2+1:y \in \mathbb{Z}_p\}$?
-/
theorem putnam_1991_b5
(p : ℕ)
(podd : Odd p)
(pprime : Prime p)
: ({z : ZMod p | ∃ x : ZMod p, z = x ^ 2} ∩ {z : ZMod p | ∃ y : ZMod p, z = y ^ 2 + 1}).encard = ((fun p : ℕ => Nat.ceil ((p : ℝ) / 4)) : ℕ → ℕ ) p := by
  classical
  have hpNat : Nat.Prime p := pprime.nat_prime
  haveI : Fact p.Prime := ⟨hpNat⟩
  haveI : NeZero p := ⟨hpNat.ne_zero⟩
  have hp2 : p ≠ 2 := by
    intro hp
    subst hp
    norm_num at podd
  have hchar : ringChar (ZMod p) ≠ 2 := (ZMod.ringChar_zmod_n p).substr hp2
  have htwo : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero hchar
  let P : Set (ZMod p × ZMod p) := {q | q.1 ^ 2 = q.2 ^ 2 + 1}
  let T : Set (ZMod p) := {z | (∃ x : ZMod p, z = x ^ 2) ∧ ∃ y : ZMod p, z = y ^ 2 + 1}
  have hcardP : Fintype.card P = p - 1 := by
    let e : {u : ZMod p // u ≠ 0} ≃ ↥P :=
    { toFun := fun u => by
        refine ⟨(((u : ZMod p) + (u : ZMod p)⁻¹) / 2, ((u : ZMod p)⁻¹ - (u : ZMod p)) / 2), ?_⟩
        dsimp [P]
        field_simp [htwo, u.property]
        ring_nf
      invFun := fun q => by
        refine ⟨q.1.1 - q.1.2, ?_⟩
        have hmul : (q.1.1 - q.1.2) * (q.1.1 + q.1.2) = 1 := by
          calc
            (q.1.1 - q.1.2) * (q.1.1 + q.1.2) = q.1.1 ^ 2 - q.1.2 ^ 2 := by ring
            _ = 1 := by rw [q.2]; ring
        intro hzero
        rw [hzero, zero_mul] at hmul
        exact zero_ne_one hmul
      left_inv := fun u => by
        apply Subtype.ext
        dsimp [P]
        field_simp [htwo, u.property]
        ring_nf
      right_inv := fun q => by
        apply Subtype.ext
        dsimp [P]
        have hmul : (q.1.1 - q.1.2) * (q.1.1 + q.1.2) = 1 := by
          calc
            (q.1.1 - q.1.2) * (q.1.1 + q.1.2) = q.1.1 ^ 2 - q.1.2 ^ 2 := by ring
            _ = 1 := by rw [q.2]; ring
        have hinv : (q.1.1 - q.1.2)⁻¹ = q.1.1 + q.1.2 := by
          exact inv_eq_of_mul_eq_one_right hmul
        ext <;> rw [hinv]
        · field_simp [htwo]
          ring
        · field_simp [htwo]
          ring }
    calc
      Fintype.card P = Fintype.card {u : ZMod p // u ≠ 0} := Fintype.card_congr e.symm
      _ = Fintype.card (ZMod p) - 1 := by simp
      _ = p - 1 := by simp [ZMod.card]
  have rootCard (a : ZMod p) (haSq : ∃ r : ZMod p, a = r ^ 2) :
      Fintype.card {x : ZMod p // a = x ^ 2} = if a = 0 then 1 else 2 := by
    by_cases ha0 : a = 0
    · subst a
      have hroots := quadraticChar_card_sqrts (F := ZMod p) hchar (0 : ZMod p)
      have hcard_set : ({x : ZMod p | x ^ 2 = (0 : ZMod p)}.toFinset.card) = 1 := by
        have hInt : (({x : ZMod p | x ^ 2 = (0 : ZMod p)}.toFinset.card : ℤ) = 1) := by
          simpa using hroots
        exact_mod_cast hInt
      simpa [Fintype.card_subtype, Set.toFinset_setOf, eq_comm] using hcard_set.symm
    · have hχ : quadraticChar (ZMod p) a = 1 := by
        exact (quadraticChar_one_iff_isSquare ha0).mpr (by simpa [isSquare_iff_exists_sq] using haSq)
      have hroots := quadraticChar_card_sqrts (F := ZMod p) hchar a
      have hcard_set : ({x : ZMod p | x ^ 2 = a}.toFinset.card) = 2 := by
        have hInt : (({x : ZMod p | x ^ 2 = a}.toFinset.card : ℤ) = 2) := by
          simpa [hχ] using hroots
        exact_mod_cast hInt
      simpa [ha0, Fintype.card_subtype, Set.toFinset_setOf, eq_comm] using hcard_set.symm
  have hxcard (z : T) : Fintype.card {x : ZMod p // z.1 = x ^ 2} = if z.1 = 0 then 1 else 2 :=
    rootCard z.1 z.2.1
  have hycard (z : T) : Fintype.card {y : ZMod p // z.1 = y ^ 2 + 1} = if z.1 = 1 then 1 else 2 := by
    have hySq : ∃ y : ZMod p, z.1 - 1 = y ^ 2 := by
      rcases z.2.2 with ⟨y, hy⟩
      refine ⟨y, ?_⟩
      have := congrArg (fun t : ZMod p => t - 1) hy
      simpa using this
    have hbase := rootCard (z.1 - 1) hySq
    let e : {y : ZMod p // z.1 = y ^ 2 + 1} ≃ {y : ZMod p // z.1 - 1 = y ^ 2} :=
    { toFun := fun y => by
        refine ⟨y.1, ?_⟩
        have := congrArg (fun t : ZMod p => t - 1) y.2
        simpa using this
      invFun := fun y => by
        refine ⟨y.1, ?_⟩
        calc
          z.1 = (z.1 - 1) + 1 := by ring
          _ = y.1 ^ 2 + 1 := congrArg (fun t : ZMod p => t + 1) y.2
      left_inv := fun y => by apply Subtype.ext; rfl
      right_inv := fun y => by apply Subtype.ext; rfl }
    calc
      Fintype.card {y : ZMod p // z.1 = y ^ 2 + 1} = Fintype.card {y : ZMod p // z.1 - 1 = y ^ 2} := Fintype.card_congr e
      _ = (if z.1 - 1 = 0 then 1 else 2) := hbase
      _ = (if z.1 = 1 then 1 else 2) := by
        by_cases hz : z.1 = 1
        · simp [hz]
        · have hzsub : z.1 - 1 ≠ 0 := by
            intro h
            exact hz (sub_eq_zero.mp h)
          simp [hz, hzsub]
  have hsum : Fintype.card P = ∑ z : T, Fintype.card {x : ZMod p // z.1 = x ^ 2} * Fintype.card {y : ZMod p // z.1 = y ^ 2 + 1} := by
    let eFib : ↥P ≃ Sigma (fun z : ↥T => ({x : ZMod p // z.1 = x ^ 2} × {y : ZMod p // z.1 = y ^ 2 + 1})) :=
    { toFun := fun q => by
        refine ⟨⟨q.1.1 ^ 2, ?_⟩, ⟨⟨q.1.1, rfl⟩, ⟨q.1.2, ?_⟩⟩⟩
        · dsimp [T]
          exact ⟨⟨q.1.1, rfl⟩, ⟨q.1.2, q.2⟩⟩
        · exact q.2
      invFun := fun s => by
        refine ⟨(s.2.1.1, s.2.2.1), ?_⟩
        dsimp [P]
        exact (s.2.1.2.symm.trans s.2.2.2)
      left_inv := fun q => by
        apply Subtype.ext
        rfl
      right_inv := fun s => by
        rcases s with ⟨⟨z, hzT⟩, ⟨⟨x, hx⟩, ⟨y, hy⟩⟩⟩
        dsimp at hx hy
        subst z
        simp }
    calc
      Fintype.card P = Fintype.card (Sigma (fun z : ↥T => ({x : ZMod p // z.1 = x ^ 2} × {y : ZMod p // z.1 = y ^ 2 + 1}))) := Fintype.card_congr eFib
      _ = ∑ z : T, Fintype.card ({x : ZMod p // z.1 = x ^ 2} × {y : ZMod p // z.1 = y ^ 2 + 1}) := by rw [Fintype.card_sigma]
      _ = ∑ z : T, Fintype.card {x : ZMod p // z.1 = x ^ 2} * Fintype.card {y : ZMod p // z.1 = y ^ 2 + 1} := by simp
  have hsumTermNat : p - 1 = ∑ z : T, (if z.1 = 0 then 1 else 2) * (if z.1 = 1 then 1 else 2) := by
    rw [← hcardP, hsum]
    apply Finset.sum_congr rfl
    intro z hz
    rw [hxcard z, hycard z]
  have h1T : (1 : ZMod p) ∈ T := by
    dsimp [T]
    exact ⟨⟨1, by ring⟩, ⟨0, by ring⟩⟩
  have h01 : (0 : ZMod p) ≠ 1 := zero_ne_one
  have h10 : (1 : ZMod p) ≠ 0 := by simpa [eq_comm] using h01
  have hsum0 :
      (∑ z : T, if (z : ZMod p) = 0 then (1 : ℤ) else 0) = if (0 : ZMod p) ∈ T then 1 else 0 := by
    by_cases h0T : (0 : ZMod p) ∈ T
    · rw [if_pos h0T]
      let z0 : T := ⟨0, h0T⟩
      calc
        (∑ z : T, if (z : ZMod p) = 0 then (1 : ℤ) else 0)
            = ∑ z : T, if z = z0 then (1 : ℤ) else 0 := by
              apply Finset.sum_congr rfl
              intro z hz
              by_cases h : (z : ZMod p) = 0
              · have hz_eq : z = z0 := by apply Subtype.ext; exact h
                subst z
                simp [z0]
              · have hz_ne : z ≠ z0 := by intro hz'; exact h (congrArg Subtype.val hz')
                simp [h, hz_ne]
        _ = 1 := by simp [z0]
    · rw [if_neg h0T]
      apply Finset.sum_eq_zero
      intro z hz
      have hz_ne : (z : ZMod p) ≠ 0 := by
        intro h
        exact h0T (by simpa [h] using z.2)
      simp [hz_ne]
  have hsum1 :
      (∑ z : T, if (z : ZMod p) = 1 then (1 : ℤ) else 0) = 1 := by
    let z1 : T := ⟨1, h1T⟩
    calc
      (∑ z : T, if (z : ZMod p) = 1 then (1 : ℤ) else 0)
          = ∑ z : T, if z = z1 then (1 : ℤ) else 0 := by
            apply Finset.sum_congr rfl
            intro z hz
            by_cases h : (z : ZMod p) = 1
            · have hz_eq : z = z1 := by apply Subtype.ext; exact h
              subst z
              simp [z1]
            · have hz_ne : z ≠ z1 := by intro hz'; exact h (congrArg Subtype.val hz')
              simp [h, hz_ne]
      _ = 1 := by simp [z1]
  have hterm (z : T) :
      ((if (z : ZMod p) = 0 then (1 : ℤ) else 2) * (if (z : ZMod p) = 1 then (1 : ℤ) else 2))
        = 4 - 2 * (if (z : ZMod p) = 0 then (1 : ℤ) else 0) - 2 * (if (z : ZMod p) = 1 then (1 : ℤ) else 0) := by
    by_cases hz0 : (z : ZMod p) = 0
    · by_cases hz1 : (z : ZMod p) = 1
      · rw [hz0] at hz1
        exact (h01 hz1).elim
      · simp [hz0, h01]
    · by_cases hz1 : (z : ZMod p) = 1
      · simp [hz1, h10]
      · simp [hz0, hz1]
  have hsumEval :
    (∑ z : T, ((if (z : ZMod p) = 0 then (1 : ℤ) else 2) * (if (z : ZMod p) = 1 then (1 : ℤ) else 2)))
      = (4 : ℤ) * Fintype.card T - 2 * (if (0 : ZMod p) ∈ T then (1 : ℤ) else 0) - 2 := by
    calc
      (∑ z : T, ((if (z : ZMod p) = 0 then (1 : ℤ) else 2) * (if (z : ZMod p) = 1 then (1 : ℤ) else 2)))
          = ∑ z : T, (4 - 2 * (if (z : ZMod p) = 0 then (1 : ℤ) else 0) - 2 * (if (z : ZMod p) = 1 then (1 : ℤ) else 0)) := by
            apply Finset.sum_congr rfl
            intro z hz
            exact hterm z
      _ = (4 : ℤ) * Fintype.card T - 2 * (if (0 : ZMod p) ∈ T then (1 : ℤ) else 0) - 2 := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
        rw [← Finset.mul_sum, ← Finset.mul_sum, hsum0, hsum1]
        simp [mul_comm]
  have hEqInt : ((p - 1 : ℕ) : ℤ) = (4 : ℤ) * Fintype.card T - 2 * (if (0 : ZMod p) ∈ T then (1 : ℤ) else 0) - 2 := by
    have hEqInt0 : ((p - 1 : ℕ) : ℤ) = ∑ z : T, ((if (z : ZMod p) = 0 then (1 : ℤ) else 2) * (if (z : ZMod p) = 1 then (1 : ℤ) else 2)) := by
      exact_mod_cast hsumTermNat
    exact hEqInt0.trans hsumEval
  have h0T_iff_square : (0 : ZMod p) ∈ T ↔ IsSquare (-1 : ZMod p) := by
    rw [isSquare_iff_exists_sq]
    constructor
    · intro h0T
      rcases h0T.2 with ⟨y, hy⟩
      refine ⟨y, ?_⟩
      have := congrArg (fun t : ZMod p => t - 1) hy
      simpa using this
    · rintro ⟨y, hy⟩
      dsimp [T]
      refine ⟨⟨0, by ring⟩, ⟨y, ?_⟩⟩
      calc
        (0 : ZMod p) = (-1) + 1 := by ring
        _ = y ^ 2 + 1 := by rw [hy]
  have h0T_iff_mod : (0 : ZMod p) ∈ T ↔ p % 4 ≠ 3 :=
    h0T_iff_square.trans ZMod.exists_sq_eq_neg_one_iff
  have hp_mod_odd : p % 4 = 1 ∨ p % 4 = 3 :=
    Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp podd)
  have hceil : Nat.ceil ((p : ℝ) / 4) = (p + 3) / 4 := by
    let m := (p + 3) / 4
    have hmpos : 0 < m := by
      dsimp [m]
      omega
    have hmne : m ≠ 0 := Nat.ne_of_gt hmpos
    rw [Nat.ceil_eq_iff hmne]
    constructor
    · have hlt : 4 * (m - 1) < p := by
        dsimp [m]
        omega
      have hltR : (4 : ℝ) * (m - 1 : ℕ) < p := by exact_mod_cast hlt
      nlinarith
    · have hle : p ≤ 4 * m := by
        dsimp [m]
        omega
      have hleR : (p : ℝ) ≤ (4 : ℝ) * m := by exact_mod_cast hle
      nlinarith
  have hcardT : Fintype.card T = Nat.ceil ((p : ℝ) / 4) := by
    by_cases h0T : (0 : ZMod p) ∈ T
    · have hN : Fintype.card T = (p + 3) / 4 := by
        have hEq : ((p - 1 : ℕ) : ℤ) = (4 : ℤ) * Fintype.card T - 2 - 2 := by
          simpa [h0T] using hEqInt
        omega
      exact hN.trans hceil.symm
    · have hpmod : p % 4 = 3 := by
        rcases hp_mod_odd with hmod | hmod
        · exfalso
          apply h0T
          exact h0T_iff_mod.mpr (by omega)
        · exact hmod
      have hN : Fintype.card T = (p + 3) / 4 := by
        have hEq : ((p - 1 : ℕ) : ℤ) = (4 : ℤ) * Fintype.card T - 2 := by
          simpa [h0T] using hEqInt
        omega
      exact hN.trans hceil.symm
  have hSet : ({z : ZMod p | ∃ x : ZMod p, z = x ^ 2} ∩ {z : ZMod p | ∃ y : ZMod p, z = y ^ 2 + 1}) = T := by
    ext z
    simp [T]
  rw [hSet]
  rw [← Set.coe_fintypeCard T]
  exact_mod_cast hcardT
