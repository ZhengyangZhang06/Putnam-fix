import Mathlib

open Topology Filter Real Function Nat

namespace Putnam2017B6

noncomputable section

local notation "p" => 2017
local notation "F" => ZMod p

instance fact_prime_2017 : Fact (Nat.Prime 2017) := ⟨by norm_num [Nat.Prime]⟩

def range64Equiv : Fin 64 ≃ Finset.range 64 where
  toFun i := ⟨i, Finset.mem_range.mpr i.isLt⟩
  invFun i := ⟨i, Finset.mem_range.mp i.property⟩
  left_inv i := by ext; rfl
  right_inv i := by ext; rfl

def iccToZMod (x : Finset.Icc 1 2017) : F := (x : ℕ)

theorem iccToZMod_injective : Function.Injective iccToZMod := by
  intro x y hxy
  apply Subtype.ext
  have hxmem := Finset.mem_Icc.mp x.property
  have hymem := Finset.mem_Icc.mp y.property
  have hmod : (x : ℕ) % 2017 = (y : ℕ) % 2017 := by
    exact (ZMod.natCast_eq_natCast_iff' (x : ℕ) (y : ℕ) 2017).mp hxy
  by_cases hx : (x : ℕ) = 2017
  · have hy0 : (y : ℕ) % 2017 = 0 := by
      simpa [hx] using hmod.symm
    have hydvd : 2017 ∣ (y : ℕ) := Nat.dvd_of_mod_eq_zero hy0
    rcases hydvd with ⟨k, hk⟩
    omega
  · have hxlt : (x : ℕ) < 2017 := lt_of_le_of_ne hxmem.2 hx
    by_cases hy : (y : ℕ) = 2017
    · have hx0 : (x : ℕ) % 2017 = 0 := by
        simpa [hy] using hmod
      have hxdvd : 2017 ∣ (x : ℕ) := Nat.dvd_of_mod_eq_zero hx0
      rcases hxdvd with ⟨k, hk⟩
      omega
    · have hylt : (y : ℕ) < 2017 := lt_of_le_of_ne hymem.2 hy
      rwa [Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] at hmod

def iccEquivZMod : Finset.Icc 1 2017 ≃ F :=
  Equiv.ofBijective iccToZMod <| by
    refine (Fintype.bijective_iff_injective_and_card iccToZMod).mpr ⟨iccToZMod_injective, ?_⟩
    rw [Fintype.card_coe, Nat.card_Icc, ZMod.card]

def coeff64 (i : Fin 64) : ℕ := if (i : ℕ) ≤ 1 then 1 else (i : ℕ)

def coeff63 (i : Fin 63) : ℕ := (i : ℕ) + 1

abbrev ZeroEmb (n q : ℕ) [Fact q.Prime] (a : Fin n → ℕ) :=
  {f : Fin n ↪ (ZMod q)ˣ // ∑ i : Fin n, (a i : ZMod q) * (f i : ZMod q) = 0}

theorem zmod_natCast_ne_zero_of_pos_lt {q m : ℕ} (hm0 : 0 < m) (hmq : m < q) :
    (m : ZMod q) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  exact (not_le_of_gt hmq) (Nat.le_of_dvd hm0 h)

def tailSum {q n : ℕ} [Fact q.Prime] (a : Fin (n + 1) → ℕ)
    (f : Fin n ↪ (ZMod q)ˣ) : ZMod q :=
  ∑ i : Fin n, (a i.succ : ZMod q) * (f i : ZMod q)

abbrev GoodTail (q n : ℕ) [Fact q.Prime] (a : Fin (n + 1) → ℕ) :=
  {f : Fin n ↪ (ZMod q)ˣ //
    tailSum (q := q) (n := n) a f ≠ 0 ∧
      ∀ i : Fin n, tailSum (q := q) (n := n) a f +
        (a 0 : ZMod q) * (f i : ZMod q) ≠ 0}

def tailCoeff {n : ℕ} (a : Fin (n + 1) → ℕ) : Fin n → ℕ :=
  fun i => a i.succ

def mergeCoeff {n : ℕ} (a : Fin (n + 1) → ℕ) (j : Fin n) : Fin n → ℕ :=
  fun i => if i = j then a 0 + a i.succ else a i.succ

theorem sum_mergeCoeff {n : ℕ} (a : Fin (n + 1) → ℕ) (j : Fin n) :
    (∑ i : Fin n, mergeCoeff a j i) = ∑ i : Fin (n + 1), a i := by
  classical
  have hsum :
      (∑ i : Fin n, mergeCoeff a j i) =
        (∑ i : Fin n, a i.succ) + ∑ i : Fin n, if i = j then a 0 else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    by_cases hij : i = j <;> simp [mergeCoeff, hij, add_comm]
  rw [hsum, Finset.sum_ite_eq']
  rw [Fin.sum_univ_succ]
  simp [add_comm]

theorem zeroEmb_tailCoeff_iff {q n : ℕ} [Fact q.Prime] (a : Fin (n + 1) → ℕ)
    (f : Fin n ↪ (ZMod q)ˣ) :
    (∑ i : Fin n, (tailCoeff a i : ZMod q) * (f i : ZMod q) = 0) ↔
      tailSum (q := q) (n := n) a f = 0 := by
  simp [tailCoeff, tailSum]

theorem zeroEmb_mergeCoeff_iff {q n : ℕ} [Fact q.Prime] (a : Fin (n + 1) → ℕ)
    (j : Fin n) (f : Fin n ↪ (ZMod q)ˣ) :
    (∑ i : Fin n, (mergeCoeff a j i : ZMod q) * (f i : ZMod q) = 0) ↔
      tailSum (q := q) (n := n) a f + (a 0 : ZMod q) * (f j : ZMod q) = 0 := by
  classical
  have hsum :
      (∑ i : Fin n, (mergeCoeff a j i : ZMod q) * (f i : ZMod q)) =
        tailSum (q := q) (n := n) a f + (a 0 : ZMod q) * (f j : ZMod q) := by
    calc
      (∑ i : Fin n, (mergeCoeff a j i : ZMod q) * (f i : ZMod q))
          =
          (∑ i : Fin n, (a i.succ : ZMod q) * (f i : ZMod q)) +
            ∑ i : Fin n, if i = j then (a 0 : ZMod q) * (f i : ZMod q) else 0 := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro i _
            by_cases hij : i = j <;> simp [mergeCoeff, hij, add_mul, add_comm]
      _ = tailSum (q := q) (n := n) a f + (a 0 : ZMod q) * (f j : ZMod q) := by
            rw [Finset.sum_ite_eq']
            simp [tailSum]
  rw [hsum]

theorem goodTail_partition_card {q n : ℕ} [Fact q.Prime] (a : Fin (n + 1) → ℕ)
    (ha0 : (a 0 : ZMod q) ≠ 0) :
    Fintype.card (GoodTail q n a) + Fintype.card (ZeroEmb n q (tailCoeff a)) +
      (∑ j : Fin n, Fintype.card (ZeroEmb n q (mergeCoeff a j))) =
        Fintype.card (Fin n ↪ (ZMod q)ˣ) := by
  classical
  let U : Finset (Fin n ↪ (ZMod q)ˣ) := Finset.univ
  let G : Finset (Fin n ↪ (ZMod q)ˣ) :=
    U.filter fun f => tailSum (q := q) (n := n) a f ≠ 0 ∧
      ∀ i : Fin n, tailSum (q := q) (n := n) a f +
        (a 0 : ZMod q) * (f i : ZMod q) ≠ 0
  let B0 : Finset (Fin n ↪ (ZMod q)ˣ) :=
    U.filter fun f => tailSum (q := q) (n := n) a f = 0
  let Bj : Fin n → Finset (Fin n ↪ (ZMod q)ˣ) := fun j =>
    U.filter fun f => tailSum (q := q) (n := n) a f +
      (a 0 : ZMod q) * (f j : ZMod q) = 0
  let BU : Finset (Fin n ↪ (ZMod q)ˣ) := Finset.univ.biUnion Bj
  have hGcard : Fintype.card (GoodTail q n a) = G.card := by
    simpa [GoodTail, G, U] using
      (Fintype.card_subtype
        (fun f : Fin n ↪ (ZMod q)ˣ => tailSum (q := q) (n := n) a f ≠ 0 ∧
          ∀ i : Fin n, tailSum (q := q) (n := n) a f +
            (a 0 : ZMod q) * (f i : ZMod q) ≠ 0))
  have hB0card : Fintype.card (ZeroEmb n q (tailCoeff a)) = B0.card := by
    simpa [ZeroEmb, B0, U, zeroEmb_tailCoeff_iff] using
      (Fintype.card_subtype
        (fun f : Fin n ↪ (ZMod q)ˣ =>
          ∑ i : Fin n, (tailCoeff a i : ZMod q) * (f i : ZMod q) = 0))
  have hBjcard (j : Fin n) :
      Fintype.card (ZeroEmb n q (mergeCoeff a j)) = (Bj j).card := by
    simpa [ZeroEmb, Bj, U, zeroEmb_mergeCoeff_iff] using
      (Fintype.card_subtype
        (fun f : Fin n ↪ (ZMod q)ˣ =>
          ∑ i : Fin n, (mergeCoeff a j i : ZMod q) * (f i : ZMod q) = 0))
  have hpair : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint Bj := by
    intro i _ j _ hij
    change Disjoint (Bj i) (Bj j)
    rw [Finset.disjoint_left]
    intro f hfi hfj
    simp [Bj, U] at hfi hfj
    have hsub : (a 0 : ZMod q) * ((f i : ZMod q) - (f j : ZMod q)) = 0 := by
      linear_combination hfi - hfj
    have heq : (f i : ZMod q) = (f j : ZMod q) :=
      sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_left ha0)
    have hunit : f i = f j := Units.ext heq
    exact hij (f.injective hunit)
  have hBUcard : BU.card = ∑ j : Fin n, (Bj j).card := by
    simpa [BU] using Finset.card_biUnion hpair
  have hG_B0 : Disjoint G B0 := by
    rw [Finset.disjoint_left]
    intro f hfG hfB
    simp [G, B0, U] at hfG hfB
    exact hfG.1 hfB
  have hG_BU : Disjoint G BU := by
    rw [Finset.disjoint_left]
    intro f hfG hfBU
    simp [G, BU, Bj, U] at hfG hfBU
    rcases hfBU with ⟨j, hj⟩
    exact hfG.2 j hj
  have hB0_BU : Disjoint B0 BU := by
    rw [Finset.disjoint_left]
    intro f hf0 hfBU
    simp [B0, BU, Bj, U] at hf0 hfBU
    rcases hfBU with ⟨j, hj⟩
    have hmul : (a 0 : ZMod q) * (f j : ZMod q) = 0 := by
      linear_combination hj - hf0
    exact mul_ne_zero ha0 (Units.ne_zero (f j)) hmul
  have hcover : G ∪ B0 ∪ BU = U := by
    ext f
    simp [G, B0, BU, Bj, U]
    by_cases h0 : tailSum (q := q) (n := n) a f = 0
    · simp [h0]
    · by_cases h : ∃ j : Fin n, tailSum (q := q) (n := n) a f +
          (a 0 : ZMod q) * (f j : ZMod q) = 0
      · simp [h0, h]
      · simp [h0]
        left
        exact fun i hi => h ⟨i, hi⟩
  have hUcard : U.card = G.card + B0.card + BU.card := by
    have hGB : Disjoint (G ∪ B0) BU := Finset.disjoint_union_left.mpr ⟨hG_BU, hB0_BU⟩
    have hGBcard : (G ∪ B0).card = G.card + B0.card :=
      Finset.card_union_of_disjoint hG_B0
    have hall : ((G ∪ B0) ∪ BU).card = (G ∪ B0).card + BU.card :=
      Finset.card_union_of_disjoint hGB
    rw [← hcover, hall, hGBcard]
  rw [hGcard, hB0card]
  simp_rw [hBjcard]
  rw [← hBUcard]
  simpa [U] using hUcard.symm

noncomputable def zeroSuccToGood {q n : ℕ} [Fact q.Prime] (a : Fin (n + 1) → ℕ)
    (ha0 : (a 0 : ZMod q) ≠ 0) : ZeroEmb (n + 1) q a → GoodTail q n a := by
  intro e
  let sp := Equiv.embeddingFinSucc n (ZMod q)ˣ e.1
  refine ⟨sp.1, ?_⟩
  have hsum : (a 0 : ZMod q) * (sp.2.1 : ZMod q) +
      tailSum (q := q) (n := n) a sp.1 = 0 := by
    have h := e.2
    rw [Fin.sum_univ_succ] at h
    simpa [sp, tailSum, Equiv.embeddingFinSucc_fst, Equiv.embeddingFinSucc_snd] using h
  constructor
  · intro hzero
    rw [hzero, add_zero] at hsum
    exact mul_ne_zero ha0 (Units.ne_zero sp.2.1) hsum
  · intro i hbad
    have h1 : (a 0 : ZMod q) * (sp.2.1 : ZMod q) =
        -tailSum (q := q) (n := n) a sp.1 := by
      rw [eq_neg_iff_add_eq_zero]
      exact hsum
    have h2 : (a 0 : ZMod q) * (sp.1 i : ZMod q) =
        -tailSum (q := q) (n := n) a sp.1 := by
      rw [eq_neg_iff_add_eq_zero]
      simpa [add_comm, add_left_comm, add_assoc] using hbad
    have hu : (sp.2.1 : ZMod q) = (sp.1 i : ZMod q) :=
      mul_left_cancel₀ ha0 (h1.trans h2.symm)
    exact sp.2.2 ⟨i, Units.ext hu.symm⟩

noncomputable def goodToZeroSucc {q n : ℕ} [Fact q.Prime] (a : Fin (n + 1) → ℕ)
    (ha0 : (a 0 : ZMod q) ≠ 0) : GoodTail q n a → ZeroEmb (n + 1) q a := by
  intro g
  let s : ZMod q := tailSum (q := q) (n := n) a g.1
  let c : ZMod q := -(a 0 : ZMod q)⁻¹ * s
  have hcne : c ≠ 0 := by
    intro hc
    have hmul := (mul_eq_zero.mp hc)
    have hleft : -(a 0 : ZMod q)⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero ha0)
    exact g.2.1 (hmul.resolve_left hleft)
  let u : (ZMod q)ˣ := Units.mk0 c hcne
  have hunrange : u ∉ Set.range g.1 := by
    rintro ⟨i, hi⟩
    have hc_eq : c = (g.1 i : ZMod q) := by
      simpa [u] using congrArg (fun x : (ZMod q)ˣ => (x : ZMod q)) hi.symm
    have hbad : s + (a 0 : ZMod q) * (g.1 i : ZMod q) = 0 := by
      rw [← hc_eq]
      simp [c, s]
      field_simp [ha0]
      ring
    exact g.2.2 i hbad
  refine ⟨(Equiv.embeddingFinSucc n (ZMod q)ˣ).symm ⟨g.1, ⟨u, hunrange⟩⟩, ?_⟩
  rw [Fin.sum_univ_succ]
  simp [tailSum, Equiv.coe_embeddingFinSucc_symm, u, c, s]
  field_simp [ha0]
  ring

noncomputable def zeroSuccGoodEquiv {q n : ℕ} [Fact q.Prime] (a : Fin (n + 1) → ℕ)
    (ha0 : (a 0 : ZMod q) ≠ 0) : ZeroEmb (n + 1) q a ≃ GoodTail q n a where
  toFun := zeroSuccToGood a ha0
  invFun := goodToZeroSucc a ha0
  left_inv e := by
    apply Subtype.ext
    apply (Equiv.embeddingFinSucc n (ZMod q)ˣ).injective
    let sp := Equiv.embeddingFinSucc n (ZMod q)ˣ e.1
    have hsum : (a 0 : ZMod q) * (sp.2.1 : ZMod q) +
        tailSum (q := q) (n := n) a sp.1 = 0 := by
      have h := e.2
      rw [Fin.sum_univ_succ] at h
      simpa [sp, tailSum, Equiv.embeddingFinSucc_fst, Equiv.embeddingFinSucc_snd] using h
    have hc : -(a 0 : ZMod q)⁻¹ * tailSum (q := q) (n := n) a sp.1 =
        (sp.2.1 : ZMod q) := by
      have htail : tailSum (q := q) (n := n) a sp.1 =
          -((a 0 : ZMod q) * (sp.2.1 : ZMod q)) := by
        rw [eq_neg_iff_add_eq_zero]
        simpa [add_comm] using hsum
      rw [htail]
      field_simp [ha0]
    ext i <;> simp [zeroSuccToGood, goodToZeroSucc, sp, hc]
  right_inv g := by
    apply Subtype.ext
    simp [zeroSuccToGood, goodToZeroSucc]

def countAux (q : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => (q - 1).descFactorial n - (n + 1) * countAux q n

theorem zeroEmb_card_countAux {q : ℕ} [Fact q.Prime] :
    ∀ n (a : Fin n → ℕ),
      (∀ i, 0 < a i) →
      (∑ i : Fin n, a i) < q →
      Fintype.card (ZeroEmb n q a) = countAux q n := by
  intro n
  induction n with
  | zero =>
      intro a hpos hsum
      simp [ZeroEmb, countAux]
  | succ n ih =>
      intro a hpos hsum
      have ha0lt : a 0 < q := by
        have hle : a 0 ≤ ∑ i : Fin (n + 1), a i :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
        exact lt_of_le_of_lt hle hsum
      have ha0ne : (a 0 : ZMod q) ≠ 0 :=
        zmod_natCast_ne_zero_of_pos_lt (hpos 0) ha0lt
      have htailpos : ∀ i : Fin n, 0 < tailCoeff a i := fun i => hpos i.succ
      have htailsum : (∑ i : Fin n, tailCoeff a i) < q := by
        have hsplit : (∑ i : Fin (n + 1), a i) =
            a 0 + ∑ i : Fin n, tailCoeff a i := by
          rw [Fin.sum_univ_succ]
          simp [tailCoeff]
        omega
      have htail : Fintype.card (ZeroEmb n q (tailCoeff a)) = countAux q n :=
        ih (tailCoeff a) htailpos htailsum
      have hmergepos (j : Fin n) : ∀ i : Fin n, 0 < mergeCoeff a j i := by
        intro i
        by_cases hij : i = j
        · have h : 0 < a 0 + a i.succ := Nat.add_pos_left (hpos 0) _
          simpa [mergeCoeff, hij] using h
        · simp [mergeCoeff, hij, hpos i.succ]
      have hmergesum (j : Fin n) : (∑ i : Fin n, mergeCoeff a j i) < q := by
        rw [sum_mergeCoeff]
        exact hsum
      have hmerge (j : Fin n) :
          Fintype.card (ZeroEmb n q (mergeCoeff a j)) = countAux q n :=
        ih (mergeCoeff a j) (hmergepos j) (hmergesum j)
      have hgood :
          Fintype.card (ZeroEmb (n + 1) q a) =
            Fintype.card (GoodTail q n a) :=
        Fintype.card_congr (zeroSuccGoodEquiv a ha0ne)
      have hpart := goodTail_partition_card a ha0ne
      have htotal : Fintype.card (Fin n ↪ (ZMod q)ˣ) = (q - 1).descFactorial n := by
        rw [Fintype.card_embedding_eq, Fintype.card_units, ZMod.card, Fintype.card_fin]
      have hrec :
          Fintype.card (ZeroEmb (n + 1) q a) + countAux q n +
            n * countAux q n = (q - 1).descFactorial n := by
        rw [hgood]
        rw [htail] at hpart
        simp_rw [hmerge] at hpart
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hpart
        rw [htotal] at hpart
        omega
      rw [countAux]
      have hrec' :
          Fintype.card (ZeroEmb (n + 1) q a) +
            (n + 1) * countAux q n = (q - 1).descFactorial n := by
        calc
          Fintype.card (ZeroEmb (n + 1) q a) + (n + 1) * countAux q n
              = Fintype.card (ZeroEmb (n + 1) q a) +
                  (countAux q n + n * countAux q n) := by ring
          _ = Fintype.card (ZeroEmb (n + 1) q a) + countAux q n +
                n * countAux q n := by rw [add_assoc]
          _ = (q - 1).descFactorial n := hrec
      exact Nat.eq_sub_of_add_eq hrec'

theorem coeff64_succ (i : Fin 63) : coeff64 i.succ = coeff63 i := by
  simp [coeff64, coeff63]

theorem sum_coeff63_zmod : (∑ i : Fin 63, (coeff63 i : F)) = -1 := by
  rw [show (∑ i : Fin 63, (coeff63 i : F)) =
      ∑ k ∈ Finset.range 63, (((k + 1 : ℕ) : F)) by
    simpa [coeff63] using
      Fin.sum_univ_eq_sum_range (fun k => (((k + 1 : ℕ) : F))) 63]
  norm_num
  have h : (2017 : F) = 0 := by simpa using ZMod.natCast_self 2017
  linear_combination h

theorem normalized_sum_eq (f : Fin 64 → F) :
    (∑ i : Fin 63, (coeff63 i : F) * (f i.succ - f 0)) =
      ∑ i : Fin 64, (coeff64 i : F) * f i := by
  have hleft : (∑ i : Fin 63, (coeff63 i : F) * (f i.succ - f 0)) =
      (∑ i : Fin 63, (coeff63 i : F) * f i.succ) -
        (∑ i : Fin 63, (coeff63 i : F)) * f 0 := by
    calc
      (∑ i : Fin 63, (coeff63 i : F) * (f i.succ - f 0))
          = ∑ i : Fin 63, ((coeff63 i : F) * f i.succ - (coeff63 i : F) * f 0) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            ring_nf
      _ = (∑ i : Fin 63, (coeff63 i : F) * f i.succ) -
            ∑ i : Fin 63, (coeff63 i : F) * f 0 := by
            rw [Finset.sum_sub_distrib]
      _ = (∑ i : Fin 63, (coeff63 i : F) * f i.succ) -
            (∑ i : Fin 63, (coeff63 i : F)) * f 0 := by
            rw [Finset.sum_mul]
  rw [hleft]
  conv_rhs => rw [Fin.sum_univ_succ]
  simp only [coeff64_succ]
  simp [coeff64]
  rw [sum_coeff63_zmod]
  ring

abbrev Orig64 :=
  {f : Fin 64 ↪ F // ∑ i : Fin 64, (coeff64 i : F) * f i = 0}

noncomputable def origToNorm : Orig64 → F × ZeroEmb 63 p coeff63 := by
  intro e
  let y : Fin 63 ↪ Fˣ :=
    { toFun := fun i => Units.mk0 (e.1 i.succ - e.1 0) (by
        intro hzero
        exact Fin.succ_ne_zero i (e.1.injective (sub_eq_zero.mp hzero))),
      inj' := by
        intro i j hij
        have hsub : e.1 i.succ - e.1 0 = e.1 j.succ - e.1 0 := by
          simpa using congrArg (fun u : Fˣ => (u : F)) hij
        exact (Fin.succ_injective 63) (e.1.injective (sub_left_injective hsub)) }
  refine ⟨e.1 0, ⟨y, ?_⟩⟩
  change ∑ i : Fin 63, (coeff63 i : F) * (e.1 i.succ - e.1 0) = 0
  rw [normalized_sum_eq]
  exact e.2

noncomputable def normToOrig : F × ZeroEmb 63 p coeff63 → Orig64 := by
  intro z
  let gfun : Fin 64 → F := Fin.cases z.1 (fun i : Fin 63 => z.1 + (z.2.1 i : F))
  let g : Fin 64 ↪ F :=
    { toFun := gfun
      inj' := by
        intro i j hij
        cases i using Fin.cases with
        | zero =>
            cases j using Fin.cases with
            | zero => rfl
            | succ j =>
                exfalso
                have hy0 : (z.2.1 j : F) = 0 := by
                  have h := congrArg (fun x : F => x - z.1) hij.symm
                  simp [gfun] at h
                exact Units.ne_zero (z.2.1 j) hy0
        | succ i =>
            cases j using Fin.cases with
            | zero =>
                exfalso
                have hy0 : (z.2.1 i : F) = 0 := by
                  have h := congrArg (fun x : F => x - z.1) hij
                  simp [gfun] at h
                exact Units.ne_zero (z.2.1 i) hy0
            | succ j =>
                have hy : (z.2.1 i : F) = (z.2.1 j : F) :=
                  add_right_injective z.1 hij
                exact congrArg Fin.succ (z.2.1.injective (Units.ext hy)) }
  refine ⟨g, ?_⟩
  change ∑ i : Fin 64, (coeff64 i : F) * gfun i = 0
  rw [← normalized_sum_eq gfun]
  simpa [gfun] using z.2.2

noncomputable def origNormEquiv : Orig64 ≃ F × ZeroEmb 63 p coeff63 where
  toFun := origToNorm
  invFun := normToOrig
  left_inv e := by
    apply Subtype.ext
    ext i
    cases i using Fin.cases <;> simp [origToNorm, normToOrig]
  right_inv z := by
    ext
    · simp [origToNorm, normToOrig]
    · simp [origToNorm, normToOrig]

def originalSum (x : Finset.range 64 → Finset.Icc 1 2017) : ℤ :=
  ∑ i : Finset.range 64,
    if i ≤ (⟨1, by norm_num⟩ : Finset.range 64) then
      (x i : ℤ)
    else
      i * (x i : ℤ)

set_option maxHeartbeats 800000 in
theorem original_sum_cast_eq (x : Finset.range 64 → Finset.Icc 1 2017) :
    ((originalSum x : ℤ) : F) =
      ∑ i : Fin 64, (coeff64 i : F) * iccEquivZMod (x (range64Equiv i)) := by
  calc
    ((originalSum x : ℤ) : F)
        = ∑ i : Fin 64,
          (((if range64Equiv i ≤ (⟨1, by norm_num⟩ : Finset.range 64) then
            (x (range64Equiv i) : ℤ)
          else
            (range64Equiv i) * (x (range64Equiv i) : ℤ)) : ℤ) : F) := by
          dsimp [originalSum]
          rw [Int.cast_sum]
          exact (Equiv.sum_comp range64Equiv
            (fun i : Finset.range 64 =>
              (((if i ≤ (⟨1, by norm_num⟩ : Finset.range 64) then
                (x i : ℤ)
              else
                i * (x i : ℤ)) : ℤ) : F))).symm
    _ = ∑ i : Fin 64, (coeff64 i : F) * iccEquivZMod (x (range64Equiv i)) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          simp [range64Equiv, coeff64, iccEquivZMod, iccToZMod]

abbrev RawGood :=
  {x : Finset.range 64 → Finset.Icc 1 2017 //
    Injective x ∧ 2017 ∣ originalSum x}

noncomputable def rawToOrig : RawGood → Orig64 := by
  intro x
  let f : Fin 64 ↪ F :=
    { toFun := fun i => iccEquivZMod (x.1 (range64Equiv i))
      inj' := by
        intro i j hij
        have hidx : range64Equiv i = range64Equiv j :=
          x.2.1 (iccEquivZMod.injective hij)
        exact range64Equiv.injective hidx }
  refine ⟨f, ?_⟩
  have hz : ((originalSum x.1 : ℤ) : F) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (originalSum x.1) 2017).mpr x.2.2
  rw [original_sum_cast_eq] at hz
  simpa [f] using hz

noncomputable def origToRaw : Orig64 → RawGood := by
  intro e
  let xfun : Finset.range 64 → Finset.Icc 1 2017 :=
    fun i => iccEquivZMod.symm (e.1 (range64Equiv.symm i))
  refine ⟨xfun, ?_⟩
  constructor
  · intro i j hij
    have hf : e.1 (range64Equiv.symm i) = e.1 (range64Equiv.symm j) := by
      simpa [xfun] using congrArg iccEquivZMod hij
    exact range64Equiv.symm.injective (e.1.injective hf)
  · have hz : ((originalSum xfun : ℤ) : F) = 0 := by
      rw [original_sum_cast_eq]
      simpa [xfun] using e.2
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (originalSum xfun) 2017).mp hz

noncomputable def rawGoodOrigEquiv : RawGood ≃ Orig64 where
  toFun := rawToOrig
  invFun := origToRaw
  left_inv x := by
    apply Subtype.ext
    ext i
    simp [rawToOrig, origToRaw]
  right_inv e := by
    apply Subtype.ext
    ext i
    simp [rawToOrig, origToRaw]

end

end Putnam2017B6

-- 2016! / 1953! - 63! * 2016
/--
Find the number of ordered $64$-tuples $(x_0,x_1,\dots,x_{63})$ such that $x_0,x_1,\dots,x_{63}$ are distinct elements of $\{1,2,\dots,2017\}$ and
\[
x_0 + x_1 + 2x_2 + 3x_3 + \cdots + 63 x_{63}
\]
is divisible by 2017.
-/
theorem putnam_2017_b6
  (S : Finset (Finset.range 64 → Finset.Icc 1 2017))
  (hs : ∀ x, x ∈ S ↔ (Injective x ∧ (2017 ∣ (∑ i : Finset.range 64, if i ≤ (⟨1, by norm_num⟩ : Finset.range 64) then (x i : ℤ) else i * (x i : ℤ))))) :
  S.card = ((2016! / 1953! - 63! * 2016) : ℕ ) := by
  classical
  have hH :
      ∀ x : Finset.range 64 → Finset.Icc 1 2017,
        x ∈ S ↔ (Injective x ∧ 2017 ∣ Putnam2017B6.originalSum x) := by
    intro x
    simpa [Putnam2017B6.originalSum] using hs x
  have hSraw : S.card = Fintype.card Putnam2017B6.RawGood :=
    (Fintype.card_of_subtype S hH).symm
  have hRawOrig :
      Fintype.card Putnam2017B6.RawGood = Fintype.card Putnam2017B6.Orig64 :=
    Fintype.card_congr Putnam2017B6.rawGoodOrigEquiv
  have hpos : ∀ i : Fin 63, 0 < Putnam2017B6.coeff63 i := by
    intro i
    simp [Putnam2017B6.coeff63]
  have hsum : (∑ i : Fin 63, Putnam2017B6.coeff63 i) < 2017 := by
    rw [show (∑ i : Fin 63, Putnam2017B6.coeff63 i) =
        ∑ k ∈ Finset.range 63, (k + 1 : ℕ) by
      simpa [Putnam2017B6.coeff63] using
        Fin.sum_univ_eq_sum_range (fun k => (k + 1 : ℕ)) 63]
    norm_num
  have hZero :
      Fintype.card (Putnam2017B6.ZeroEmb 63 2017 Putnam2017B6.coeff63) =
        Putnam2017B6.countAux 2017 63 :=
    Putnam2017B6.zeroEmb_card_countAux 63 Putnam2017B6.coeff63 hpos hsum
  have hOrig :
      Fintype.card Putnam2017B6.Orig64 = 2017 * Putnam2017B6.countAux 2017 63 := by
    calc
      Fintype.card Putnam2017B6.Orig64
          = Fintype.card (ZMod 2017 ×
              Putnam2017B6.ZeroEmb 63 2017 Putnam2017B6.coeff63) :=
            Fintype.card_congr Putnam2017B6.origNormEquiv
      _ = Fintype.card (ZMod 2017) *
            Fintype.card (Putnam2017B6.ZeroEmb 63 2017 Putnam2017B6.coeff63) := by
            rw [Fintype.card_prod]
      _ = 2017 * Putnam2017B6.countAux 2017 63 := by
            rw [ZMod.card, hZero]
  calc
    S.card = Fintype.card Putnam2017B6.RawGood := hSraw
    _ = Fintype.card Putnam2017B6.Orig64 := hRawOrig
    _ = 2017 * Putnam2017B6.countAux 2017 63 := hOrig
    _ = ((2016! / 1953! - 63! * 2016) : ℕ) := by
      norm_num [Putnam2017B6.countAux, Nat.descFactorial]
