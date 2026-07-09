import Mathlib

namespace Putnam2024A3

inductive Step where
  | A
  | B
  | C
  deriving DecidableEq, Fintype

open Step

lemma length_eq_counts (l : List Step) :
    l.length = l.count A + l.count B + l.count C := by
  induction l with
  | nil => simp
  | cons s t ih =>
      cases s <;> simp [ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

def SuffixGood (l : List Step) : Prop :=
  ∀ t, t <:+ l → t.count B ≤ t.count A ∧ t.count C ≤ t.count B

def Ballot (x y z : ℕ) : Set (List Step) :=
  {l | SuffixGood l ∧ l.count A = x + y + z ∧ l.count B = y + z ∧ l.count C = z}

lemma Ballot_length {x y z : ℕ} {l : List Step} (hl : l ∈ Ballot x y z) :
    l.length = x + 2 * y + 3 * z := by
  rcases hl with ⟨_, hA, hB, hC⟩
  rw [length_eq_counts l, hA, hB, hC]
  omega

lemma finite_length_set (n : ℕ) : ({l : List Step | l.length = n} : Set (List Step)).Finite := by
  let f : List.Vector Step n → List Step := fun v => v.toList
  have h_eq : ({l : List Step | l.length = n} : Set (List Step)) = f '' Set.univ := by
    ext l
    constructor
    · intro hl
      exact ⟨⟨l, hl⟩, trivial, rfl⟩
    · rintro ⟨v, _, rfl⟩
      exact v.2
  rw [h_eq]
  exact Set.finite_univ.image f

lemma Ballot_finite (x y z : ℕ) : (Ballot x y z).Finite := by
  exact (finite_length_set (x + 2 * y + 3 * z)).subset (by
    intro l hl
    exact Ballot_length hl)

lemma suffixGood_cons (s : Step) (l : List Step) :
    SuffixGood (s :: l) ↔
      SuffixGood l ∧ (s :: l).count B ≤ (s :: l).count A ∧
        (s :: l).count C ≤ (s :: l).count B := by
  unfold SuffixGood
  constructor
  · intro h
    refine ⟨?_, h (s :: l) List.suffix_rfl⟩
    intro t ht
    exact h t (ht.trans (List.suffix_cons _ _))
  · rintro ⟨hl, hfull⟩ t ht
    rw [List.suffix_cons_iff] at ht
    rcases ht with rfl | ht
    · exact hfull
    · exact hl t ht

lemma suffixGood_cons_A {l : List Step} (hl : SuffixGood l) : SuffixGood (A :: l) := by
  rw [suffixGood_cons]
  refine ⟨hl, ?_, ?_⟩
  · have h := (hl l List.suffix_rfl).1
    simpa using Nat.le_succ_of_le h
  · simpa using (hl l List.suffix_rfl).2

lemma suffixGood_cons_B {l : List Step} (hl : SuffixGood l)
    (h : l.count B + 1 ≤ l.count A) : SuffixGood (B :: l) := by
  rw [suffixGood_cons]
  refine ⟨hl, ?_, ?_⟩
  · simpa using h
  · have hc := (hl l List.suffix_rfl).2
    simpa using Nat.le_trans hc (Nat.le_succ (l.count B))

lemma suffixGood_cons_C {l : List Step} (hl : SuffixGood l)
    (h : l.count C + 1 ≤ l.count B) : SuffixGood (C :: l) := by
  rw [suffixGood_cons]
  refine ⟨hl, ?_, ?_⟩
  · simpa using (hl l List.suffix_rfl).1
  · simpa using h

lemma Ballot_cons_A {x y z : ℕ} (hx : 0 < x) :
    (List.cons A) '' Ballot (x - 1) y z ⊆ Ballot x y z := by
  rintro _ ⟨t, ht, rfl⟩
  rcases ht with ⟨hg, hA, hB, hC⟩
  refine ⟨suffixGood_cons_A hg, ?_, ?_, ?_⟩
  · simp [hA]
    omega
  · simp [hB]
  · simp [hC]

lemma Ballot_cons_B {x y z : ℕ} (hy : 0 < y) :
    (List.cons B) '' Ballot (x + 1) (y - 1) z ⊆ Ballot x y z := by
  rintro _ ⟨t, ht, rfl⟩
  rcases ht with ⟨hg, hA, hB, hC⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply suffixGood_cons_B hg
    rw [hA, hB]
    omega
  · simp [hA]
    omega
  · simp [hB]
    omega
  · simp [hC]

lemma Ballot_cons_C {x y z : ℕ} (hz : 0 < z) :
    (List.cons C) '' Ballot x (y + 1) (z - 1) ⊆ Ballot x y z := by
  rintro _ ⟨t, ht, rfl⟩
  rcases ht with ⟨hg, hA, hB, hC⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply suffixGood_cons_C hg
    rw [hB, hC]
    omega
  · simp [hA]
    omega
  · simp [hB]
    omega
  · simp [hC]
    omega

lemma Ballot_subset_cons (x y z : ℕ) (hpos : 0 < x + 2 * y + 3 * z) :
    Ballot x y z ⊆
      (if x = 0 then ∅ else (List.cons A) '' Ballot (x - 1) y z) ∪
      (if y = 0 then ∅ else (List.cons B) '' Ballot (x + 1) (y - 1) z) ∪
      (if z = 0 then ∅ else (List.cons C) '' Ballot x (y + 1) (z - 1)) := by
  intro l hl
  rcases hl with ⟨hg, hA, hB, hC⟩
  cases l with
  | nil =>
      simp at hA hB hC
      omega
  | cons s t =>
      cases s
      · have hx : 0 < x := by
          have htgood := (hg t (List.suffix_cons _ _)).1
          simp at hA hB hC htgood
          omega
        simp [hx.ne']
        refine ⟨(suffixGood_cons A t).1 hg |>.1, ?_, ?_, ?_⟩
        · simp at hA ⊢
          omega
        · simpa using hB
        · simpa using hC
      · have hy : 0 < y := by
          have htgood := (hg t (List.suffix_cons _ _)).2
          simp at hA hB hC htgood
          omega
        simp [hy.ne']
        refine ⟨(suffixGood_cons B t).1 hg |>.1, ?_, ?_, ?_⟩
        · simp at hA ⊢
          omega
        · simp at hB ⊢
          omega
        · simpa using hC
      · have hz : 0 < z := by
          simp at hC
          omega
        simp [hz.ne']
        refine ⟨(suffixGood_cons C t).1 hg |>.1, ?_, ?_, ?_⟩
        · simp at hA ⊢
          omega
        · simp at hB ⊢
          omega
        · simp at hC ⊢
          omega

lemma Ballot_cons_eq (x y z : ℕ) (hpos : 0 < x + 2 * y + 3 * z) :
    Ballot x y z =
      (if x = 0 then ∅ else (List.cons A) '' Ballot (x - 1) y z) ∪
      (if y = 0 then ∅ else (List.cons B) '' Ballot (x + 1) (y - 1) z) ∪
      (if z = 0 then ∅ else (List.cons C) '' Ballot x (y + 1) (z - 1)) := by
  apply le_antisymm
  · exact Ballot_subset_cons x y z hpos
  · intro l hl
    rcases hl with (hl | hl) | hl
    · by_cases hx : x = 0
      · simp [hx] at hl
      · simp [hx] at hl
        exact Ballot_cons_A (Nat.pos_of_ne_zero hx) hl
    · by_cases hy : y = 0
      · simp [hy] at hl
      · simp [hy] at hl
        exact Ballot_cons_B (Nat.pos_of_ne_zero hy) hl
    · by_cases hz : z = 0
      · simp [hz] at hl
      · simp [hz] at hl
        exact Ballot_cons_C (Nat.pos_of_ne_zero hz) hl

lemma disjoint_cons_ne {a b : Step} (hab : a ≠ b) (s t : Set (List Step)) :
    Disjoint ((List.cons a) '' s) ((List.cons b) '' t) := by
  rw [Set.disjoint_left]
  rintro _ ⟨u, _, rfl⟩ ⟨v, _, h⟩
  exact hab (List.cons.inj h).1.symm

lemma Ballot_ncard_rec (x y z : ℕ) (hpos : 0 < x + 2 * y + 3 * z) :
    (Ballot x y z).ncard =
      (if x = 0 then 0 else (Ballot (x - 1) y z).ncard) +
      (if y = 0 then 0 else (Ballot (x + 1) (y - 1) z).ncard) +
      (if z = 0 then 0 else (Ballot x (y + 1) (z - 1)).ncard) := by
  let SA : Set (List Step) := if x = 0 then ∅ else (List.cons A) '' Ballot (x - 1) y z
  let SB : Set (List Step) := if y = 0 then ∅ else (List.cons B) '' Ballot (x + 1) (y - 1) z
  let SC : Set (List Step) := if z = 0 then ∅ else (List.cons C) '' Ballot x (y + 1) (z - 1)
  have hEq : Ballot x y z = SA ∪ SB ∪ SC := by
    dsimp [SA, SB, SC]
    exact Ballot_cons_eq x y z hpos
  have hSAfin : SA.Finite := by
    dsimp [SA]
    by_cases hx : x = 0
    · simp [hx]
    · simpa [hx] using (Ballot_finite (x - 1) y z).image (List.cons A)
  have hSBfin : SB.Finite := by
    dsimp [SB]
    by_cases hy : y = 0
    · simp [hy]
    · simpa [hy] using (Ballot_finite (x + 1) (y - 1) z).image (List.cons B)
  have hSCfin : SC.Finite := by
    dsimp [SC]
    by_cases hz : z = 0
    · simp [hz]
    · simpa [hz] using (Ballot_finite x (y + 1) (z - 1)).image (List.cons C)
  have hAB : Disjoint SA SB := by
    dsimp [SA, SB]
    by_cases hx : x = 0 <;> by_cases hy : y = 0 <;>
      simp [hx, hy, disjoint_cons_ne (by decide : A ≠ B)]
  have hA_C : Disjoint SA SC := by
    dsimp [SA, SC]
    by_cases hx : x = 0 <;> by_cases hz : z = 0 <;>
      simp [hx, hz, disjoint_cons_ne (by decide : A ≠ C)]
  have hB_C : Disjoint SB SC := by
    dsimp [SB, SC]
    by_cases hy : y = 0 <;> by_cases hz : z = 0 <;>
      simp [hy, hz, disjoint_cons_ne (by decide : B ≠ C)]
  have hUnion : Disjoint (SA ∪ SB) SC := hA_C.union_left hB_C
  rw [hEq]
  rw [Set.ncard_union_eq hUnion (hSAfin.union hSBfin) hSCfin]
  rw [Set.ncard_union_eq hAB hSAfin hSBfin]
  dsimp [SA, SB, SC]
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> by_cases hz : z = 0 <;>
    simp [hx, hy, hz, Set.ncard_image_of_injective _ List.cons_injective]

lemma factorial_cast_pred (n : ℕ) (h : 0 < n) :
    (n.factorial : ℚ) = (n : ℚ) * ((n - 1).factorial : ℚ) := by
  rw [show n = (n - 1) + 1 by omega, Nat.factorial_succ]
  norm_num

noncomputable def ballotCountQ (x y z : ℕ) : ℚ :=
  ((Nat.factorial (x + 2 * y + 3 * z) : ℚ) * ((x : ℚ) + 1) *
      ((x : ℚ) + (y : ℚ) + 2) * ((y : ℚ) + 1)) /
    ((Nat.factorial (x + y + z + 2) : ℚ) * (Nat.factorial (y + z + 1) : ℚ) *
      (Nat.factorial z : ℚ))

noncomputable def removeAWeight (x y z : ℕ) : ℚ :=
  ((((x + y + z + 2 : ℕ) : ℚ) * (x : ℚ) * ((x : ℚ) + (y : ℚ) + 1)) /
    (((x + 2 * y + 3 * z : ℕ) : ℚ) * ((x : ℚ) + 1) *
      ((x : ℚ) + (y : ℚ) + 2)))

noncomputable def removeBWeight (x y z : ℕ) : ℚ :=
  ((((y + z + 1 : ℕ) : ℚ) * ((x : ℚ) + 2) * (y : ℚ)) /
    (((x + 2 * y + 3 * z : ℕ) : ℚ) * ((x : ℚ) + 1) * ((y : ℚ) + 1)))

noncomputable def removeCWeight (x y z : ℕ) : ℚ :=
  (((z : ℚ) * ((x : ℚ) + (y : ℚ) + 3) * ((y : ℚ) + 2)) /
    (((x + 2 * y + 3 * z : ℕ) : ℚ) * ((x : ℚ) + (y : ℚ) + 2) *
      ((y : ℚ) + 1)))

lemma ballotCountQ_removeA (x y z : ℕ) :
    ballotCountQ x y z = ballotCountQ (x + 1) y z * removeAWeight (x + 1) y z := by
  unfold ballotCountQ removeAWeight
  field_simp
  rw [factorial_cast_pred (x + 1 + 2 * y + 3 * z) (by omega)]
  rw [show x + 1 + 2 * y + 3 * z - 1 = x + 2 * y + 3 * z by omega]
  rw [factorial_cast_pred (x + 1 + y + z + 2) (by omega)]
  rw [show x + 1 + y + z + 2 - 1 = x + y + z + 2 by omega]
  norm_num [Nat.cast_add, Nat.cast_mul]
  ring_nf

lemma ballotCountQ_removeB (x y z : ℕ) :
    ballotCountQ (x + 1) y z = ballotCountQ x (y + 1) z * removeBWeight x (y + 1) z := by
  unfold ballotCountQ removeBWeight
  field_simp
  rw [factorial_cast_pred (x + 2 * (y + 1) + 3 * z) (by omega)]
  rw [show x + 2 * (y + 1) + 3 * z - 1 = x + 1 + 2 * y + 3 * z by omega]
  rw [factorial_cast_pred (y + 1 + z + 1) (by omega)]
  rw [show y + 1 + z + 1 - 1 = y + z + 1 by omega]
  norm_num [Nat.cast_add, Nat.cast_mul]
  ring_nf

lemma ballotCountQ_removeC (x y z : ℕ) :
    ballotCountQ x (y + 1) z = ballotCountQ x y (z + 1) * removeCWeight x y (z + 1) := by
  unfold ballotCountQ removeCWeight
  field_simp
  rw [factorial_cast_pred (x + 2 * y + 3 * (z + 1)) (by omega)]
  rw [show x + 2 * y + 3 * (z + 1) - 1 = x + 2 * (y + 1) + 3 * z by omega]
  rw [factorial_cast_pred (z + 1) (by omega)]
  rw [show z + 1 - 1 = z by omega]
  norm_num [Nat.cast_add, Nat.cast_mul]
  ring_nf

lemma removeWeight_sum (x y z : ℕ) (hpos : 0 < x + 2 * y + 3 * z) :
    (if x = 0 then 0 else removeAWeight x y z) +
      (if y = 0 then 0 else removeBWeight x y z) +
        (if z = 0 then 0 else removeCWeight x y z) = 1 := by
  unfold removeAWeight removeBWeight removeCWeight
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> by_cases hz : z = 0
  all_goals simp [hx, hy, hz]
  all_goals try omega
  all_goals field_simp [hpos]
  all_goals ring_nf

lemma Ballot_ncard_zero : (Ballot 0 0 0).ncard = 1 := by
  have hset : Ballot 0 0 0 = {([] : List Step)} := by
    ext l
    constructor
    · intro hl
      rcases hl with ⟨_, hA, hB, hC⟩
      have hlen := length_eq_counts l
      simp [hA, hB, hC] at hlen
      exact hlen
    · intro hl
      rw [hl]
      simp [Ballot, SuffixGood]
  rw [hset]
  simp

lemma Ballot_ncard_eq_ballotCountQ (x y z : ℕ) :
    ((Ballot x y z).ncard : ℚ) = ballotCountQ x y z := by
  generalize hn : x + 2 * y + 3 * z = n
  revert x y z
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro x y z hn
      by_cases hzero : n = 0
      · subst n
        have hx : x = 0 := by omega
        have hy : y = 0 := by omega
        have hz : z = 0 := by omega
        subst x
        subst y
        subst z
        rw [Ballot_ncard_zero]
        unfold ballotCountQ
        norm_num
      · have hpos : 0 < x + 2 * y + 3 * z := by omega
        have hrec := Ballot_ncard_rec x y z hpos
        rw [hrec]
        norm_num [Nat.cast_add]
        have hA : (if x = 0 then (0 : ℚ) else ↑(Ballot (x - 1) y z).ncard) =
            (if x = 0 then 0 else ballotCountQ (x - 1) y z) := by
          by_cases hx : x = 0
          · simp [hx]
          · simp [hx]
            rw [ih (n - 1) (by omega) (x - 1) y z]
            omega
        have hB : (if y = 0 then (0 : ℚ) else ↑(Ballot (x + 1) (y - 1) z).ncard) =
            (if y = 0 then 0 else ballotCountQ (x + 1) (y - 1) z) := by
          by_cases hy : y = 0
          · simp [hy]
          · simp [hy]
            rw [ih (n - 1) (by omega) (x + 1) (y - 1) z]
            omega
        have hC : (if z = 0 then (0 : ℚ) else ↑(Ballot x (y + 1) (z - 1)).ncard) =
            (if z = 0 then 0 else ballotCountQ x (y + 1) (z - 1)) := by
          by_cases hz : z = 0
          · simp [hz]
          · simp [hz]
            rw [ih (n - 1) (by omega) x (y + 1) (z - 1)]
            omega
        rw [hA, hB, hC]
        have hAr : (if x = 0 then (0 : ℚ) else ballotCountQ (x - 1) y z) =
            ballotCountQ x y z * (if x = 0 then 0 else removeAWeight x y z) := by
          by_cases hx : x = 0
          · simp [hx]
          · rcases x with _ | x
            · contradiction
            · simp
              rw [ballotCountQ_removeA x y z]
        have hBr : (if y = 0 then (0 : ℚ) else ballotCountQ (x + 1) (y - 1) z) =
            ballotCountQ x y z * (if y = 0 then 0 else removeBWeight x y z) := by
          by_cases hy : y = 0
          · simp [hy]
          · rcases y with _ | y
            · contradiction
            · simp
              rw [ballotCountQ_removeB x y z]
        have hCr : (if z = 0 then (0 : ℚ) else ballotCountQ x (y + 1) (z - 1)) =
            ballotCountQ x y z * (if z = 0 then 0 else removeCWeight x y z) := by
          by_cases hz : z = 0
          · simp [hz]
          · rcases z with _ | z
            · contradiction
            · simp
              rw [ballotCountQ_removeC x y z]
        rw [hAr, hBr, hCr]
        rw [← mul_add, ← mul_add, removeWeight_sum x y z hpos]
        ring

lemma ballot_target_ratio :
    (((Ballot 0 2 2022).ncard : ℚ) / (Ballot 0 0 2024).ncard) = (4046 : ℚ) / 6071 := by
  rw [Ballot_ncard_eq_ballotCountQ 0 2 2022, Ballot_ncard_eq_ballotCountQ 0 0 2024]
  unfold ballotCountQ
  field_simp
  rw [factorial_cast_pred 6072 (by norm_num)]
  rw [factorial_cast_pred 6071 (by norm_num)]
  rw [factorial_cast_pred 2024 (by norm_num)]
  rw [factorial_cast_pred 2023 (by norm_num)]
  norm_num

lemma ballot_target_ratio_mem_Icc : ((4046 : ℚ) / 6071) ∈ Set.Icc (1 / 3) (2 / 3) := by
  norm_num

def PrefixGood (l : List Step) : Prop :=
  ∀ t, t <+: l → t.count B ≤ t.count A ∧ t.count C ≤ t.count B

lemma prefixGood_reverse {l : List Step} : PrefixGood l.reverse ↔ SuffixGood l := by
  unfold PrefixGood SuffixGood
  constructor
  · intro h t ht
    have ht' : t.reverse <+: l.reverse := by
      rw [List.reverse_prefix]
      simpa using ht
    have := h t.reverse ht'
    simpa [List.count_reverse] using this
  · intro h t ht
    have ht' : t.reverse <:+ l := by
      rw [← List.reverse_prefix]
      simpa using ht
    have := h t.reverse ht'
    simpa [List.count_reverse] using this

def cellsOfWordAux : ℕ → ℕ → ℕ → List Step → List (ℕ × ℕ)
  | _, _, _, [] => []
  | a, b, c, A :: t => (1, a + 1) :: cellsOfWordAux (a + 1) b c t
  | a, b, c, B :: t => (2, b + 1) :: cellsOfWordAux a (b + 1) c t
  | a, b, c, C :: t => (3, c + 1) :: cellsOfWordAux a b (c + 1) t

def cellsOfWord (l : List Step) : List (ℕ × ℕ) :=
  cellsOfWordAux 0 0 0 l

def rowOfStep : Step → ℕ
  | A => 1
  | B => 2
  | C => 3

def stepOfRow (i : ℕ) : Step :=
  if i = 1 then A else if i = 2 then B else C

def rowWordOfCells (cs : List (ℕ × ℕ)) : List Step :=
  cs.map fun p => stepOfRow p.1

lemma stepOfRow_rowOfStep (s : Step) : stepOfRow (rowOfStep s) = s := by
  cases s <;> simp [stepOfRow, rowOfStep]

lemma cellsOfWordAux_length (a b c : ℕ) (l : List Step) :
    (cellsOfWordAux a b c l).length = l.length := by
  induction l generalizing a b c with
  | nil => simp [cellsOfWordAux]
  | cons s t ih =>
      cases s <;> simp [cellsOfWordAux, ih]

lemma cellsOfWord_length (l : List Step) :
    (cellsOfWord l).length = l.length := by
  simp [cellsOfWord, cellsOfWordAux_length]

lemma cellsOfWordAux_rowWord (a b c : ℕ) (l : List Step) :
    rowWordOfCells (cellsOfWordAux a b c l) = l := by
  induction l generalizing a b c with
  | nil => simp [rowWordOfCells, cellsOfWordAux]
  | cons s t ih =>
      cases s
      · change A :: rowWordOfCells (cellsOfWordAux (a + 1) b c t) = A :: t
        rw [ih]
      · change B :: rowWordOfCells (cellsOfWordAux a (b + 1) c t) = B :: t
        rw [ih]
      · change C :: rowWordOfCells (cellsOfWordAux a b (c + 1) t) = C :: t
        rw [ih]

lemma cellsOfWord_rowWord (l : List Step) :
    rowWordOfCells (cellsOfWord l) = l := by
  simpa [cellsOfWord] using cellsOfWordAux_rowWord 0 0 0 l

lemma rowWord_take (cs : List (ℕ × ℕ)) (n : ℕ) :
    (rowWordOfCells cs).take n = rowWordOfCells (cs.take n) := by
  simp [rowWordOfCells, List.map_take]

lemma mem_cellsOfWordAux_one {a b c : ℕ} {l : List Step} {j : ℕ} :
    (1, j) ∈ cellsOfWordAux a b c l ↔ a < j ∧ j ≤ a + l.count A := by
  induction l generalizing a b c with
  | nil =>
      simp [cellsOfWordAux]
  | cons s t ih =>
      cases s <;> simp [cellsOfWordAux, ih, Nat.add_assoc] <;> omega

lemma mem_cellsOfWordAux_two {a b c : ℕ} {l : List Step} {j : ℕ} :
    (2, j) ∈ cellsOfWordAux a b c l ↔ b < j ∧ j ≤ b + l.count B := by
  induction l generalizing a b c with
  | nil =>
      simp [cellsOfWordAux]
  | cons s t ih =>
      cases s <;> simp [cellsOfWordAux, ih, Nat.add_assoc] <;> omega

lemma mem_cellsOfWordAux_three {a b c : ℕ} {l : List Step} {j : ℕ} :
    (3, j) ∈ cellsOfWordAux a b c l ↔ c < j ∧ j ≤ c + l.count C := by
  induction l generalizing a b c with
  | nil =>
      simp [cellsOfWordAux]
  | cons s t ih =>
      cases s <;> simp [cellsOfWordAux, ih, Nat.add_assoc] <;> omega

lemma cellsOfWordAux_nodup (a b c : ℕ) (l : List Step) :
    (cellsOfWordAux a b c l).Nodup := by
  induction l generalizing a b c with
  | nil => simp [cellsOfWordAux]
  | cons s t ih =>
      cases s
      · simp [cellsOfWordAux, ih, mem_cellsOfWordAux_one]
      · simp [cellsOfWordAux, ih, mem_cellsOfWordAux_two]
      · simp [cellsOfWordAux, ih, mem_cellsOfWordAux_three]

lemma cellsOfWord_nodup (l : List Step) : (cellsOfWord l).Nodup := by
  exact cellsOfWordAux_nodup 0 0 0 l

lemma mem_cellsOfWord_one {l : List Step} {j : ℕ} :
    (1, j) ∈ cellsOfWord l ↔ 0 < j ∧ j ≤ l.count A := by
  simpa [cellsOfWord] using (mem_cellsOfWordAux_one (a := 0) (b := 0) (c := 0) (l := l) (j := j))

lemma mem_cellsOfWord_two {l : List Step} {j : ℕ} :
    (2, j) ∈ cellsOfWord l ↔ 0 < j ∧ j ≤ l.count B := by
  simpa [cellsOfWord] using (mem_cellsOfWordAux_two (a := 0) (b := 0) (c := 0) (l := l) (j := j))

lemma mem_cellsOfWord_three {l : List Step} {j : ℕ} :
    (3, j) ∈ cellsOfWord l ↔ 0 < j ∧ j ≤ l.count C := by
  simpa [cellsOfWord] using (mem_cellsOfWordAux_three (a := 0) (b := 0) (c := 0) (l := l) (j := j))

lemma mem_cellsOfWordAux_row {a b c : ℕ} {l : List Step} {p : ℕ × ℕ}
    (hp : p ∈ cellsOfWordAux a b c l) : p.1 = 1 ∨ p.1 = 2 ∨ p.1 = 3 := by
  induction l generalizing a b c with
  | nil => simpa [cellsOfWordAux] using hp
  | cons s t ih =>
      cases s
      · simp [cellsOfWordAux] at hp
        rcases hp with hp | hp
        · subst p
          simp
        · exact ih hp
      · simp [cellsOfWordAux] at hp
        rcases hp with hp | hp
        · subst p
          simp
        · exact ih hp
      · simp [cellsOfWordAux] at hp
        rcases hp with hp | hp
        · subst p
          simp
        · exact ih hp

lemma mem_cellsOfWord_iff {l : List Step} {p : ℕ × ℕ} :
    p ∈ cellsOfWord l ↔
      (p.1 = 1 ∧ 0 < p.2 ∧ p.2 ≤ l.count A) ∨
        (p.1 = 2 ∧ 0 < p.2 ∧ p.2 ≤ l.count B) ∨
          (p.1 = 3 ∧ 0 < p.2 ∧ p.2 ≤ l.count C) := by
  constructor
  · intro hp
    rcases p with ⟨i, j⟩
    have hrow := mem_cellsOfWordAux_row (a := 0) (b := 0) (c := 0) (l := l) hp
    rcases hrow with hrow | hrow | hrow
    · simp at hrow
      subst i
      left
      simpa using (mem_cellsOfWord_one (l := l) (j := j)).1 hp
    · simp at hrow
      subst i
      right; left
      simpa using (mem_cellsOfWord_two (l := l) (j := j)).1 hp
    · simp at hrow
      subst i
      right; right
      simpa using (mem_cellsOfWord_three (l := l) (j := j)).1 hp
  · intro hp
    rcases p with ⟨i, j⟩
    rcases hp with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩
    · simp at hi
      subst i
      exact (mem_cellsOfWord_one (l := l) (j := j)).2 hj
    · simp at hi
      subst i
      exact (mem_cellsOfWord_two (l := l) (j := j)).2 hj
    · simp at hi
      subst i
      exact (mem_cellsOfWord_three (l := l) (j := j)).2 hj

lemma mem_cellsOfWord_step {l : List Step} {s : Step} {j : ℕ} :
    (rowOfStep s, j) ∈ cellsOfWord l ↔ 0 < j ∧ j ≤ l.count s := by
  cases s <;> simp [rowOfStep, mem_cellsOfWord_one, mem_cellsOfWord_two,
    mem_cellsOfWord_three]

lemma cellsOfWordAux_take (a b c n : ℕ) (l : List Step) :
    (cellsOfWordAux a b c l).take n = cellsOfWordAux a b c (l.take n) := by
  induction l generalizing a b c n with
  | nil => simp [cellsOfWordAux]
  | cons s t ih =>
      cases n with
      | zero => simp [cellsOfWordAux]
      | succ n =>
          cases s <;> simp [cellsOfWordAux, ih]

lemma cellsOfWord_take (n : ℕ) (l : List Step) :
    (cellsOfWord l).take n = cellsOfWord (l.take n) := by
  simpa [cellsOfWord] using cellsOfWordAux_take 0 0 0 n l

lemma count_take_succ_of_eq {l : List Step} {s : Step} {n : ℕ}
    (hn : n < l.length) (hs : l[n] = s) :
    (l.take (n + 1)).count s = (l.take n).count s + 1 := by
  rw [← List.take_concat_get' l n hn, List.count_append]
  simp [hs]

lemma count_take_succ_of_ne {l : List Step} {s : Step} {n : ℕ}
    (hn : n < l.length) (hs : l[n] ≠ s) :
    (l.take (n + 1)).count s = (l.take n).count s := by
  rw [← List.take_concat_get' l n hn, List.count_append]
  simp [hs]

lemma count_take_succ_le (l : List Step) (s : Step) {n : ℕ} (hn : n < l.length) :
    (l.take (n + 1)).count s ≤ (l.take n).count s + 1 := by
  by_cases hs : l[n] = s
  · rw [count_take_succ_of_eq hn hs]
  · rw [count_take_succ_of_ne hn hs]
    omega

lemma count_take_idxOf_cell {l : List Step} {s : Step} {j : ℕ}
    (hj : 0 < j) (hmem : (rowOfStep s, j) ∈ cellsOfWord l) :
    (l.take ((cellsOfWord l).idxOf (rowOfStep s, j))).count s = j - 1 := by
  let cs := cellsOfWord l
  let n := cs.idxOf (rowOfStep s, j)
  have hncs : n < cs.length := List.idxOf_lt_length_of_mem hmem
  have hnl : n < l.length := by
    simpa [cs, cellsOfWord_length] using hncs
  have hnot : (rowOfStep s, j) ∉ cs.take n := by
    intro h
    have := (List.mem_take_iff_idxOf_lt hmem).1 h
    simp [n, cs] at this
  have hbefore_lt : (l.take n).count s < j := by
    by_contra h
    have hle : j ≤ (l.take n).count s := Nat.le_of_not_gt h
    have : (rowOfStep s, j) ∈ cs.take n := by
      rw [show cs.take n = cellsOfWord (l.take n) by simp [cs, cellsOfWord_take]]
      exact (mem_cellsOfWord_step (l := l.take n) (s := s) (j := j)).2 ⟨hj, hle⟩
    exact hnot this
  have htake : (rowOfStep s, j) ∈ cs.take (n + 1) := by
    rw [List.mem_take_iff_idxOf_lt hmem]
    simp [n, cs]
  have hafter_ge : j ≤ (l.take (n + 1)).count s := by
    have h := htake
    rw [show cs.take (n + 1) = cellsOfWord (l.take (n + 1)) by
      simp [cs, cellsOfWord_take]] at h
    exact ((mem_cellsOfWord_step (l := l.take (n + 1)) (s := s) (j := j)).1 h).2
  have hafter_le : (l.take (n + 1)).count s ≤ (l.take n).count s + 1 :=
    count_take_succ_le l s hnl
  change (l.take n).count s = j - 1
  omega

lemma getElem?_idxOf_cell_eq_step {l : List Step} {s : Step} {j : ℕ}
    (hj : 0 < j) (hmem : (rowOfStep s, j) ∈ cellsOfWord l) :
    l[(cellsOfWord l).idxOf (rowOfStep s, j)]? = some s := by
  let cs := cellsOfWord l
  let n := cs.idxOf (rowOfStep s, j)
  have hncs : n < cs.length := List.idxOf_lt_length_of_mem hmem
  have hnl : n < l.length := by
    simpa [cs, cellsOfWord_length] using hncs
  change l[n]? = some s
  rw [List.getElem?_eq_getElem hnl]
  have hbefore := count_take_idxOf_cell (l := l) (s := s) (j := j) hj hmem
  have htake : (rowOfStep s, j) ∈ cs.take (n + 1) := by
    rw [List.mem_take_iff_idxOf_lt hmem]
    simp [n, cs]
  have hafter_ge : j ≤ (l.take (n + 1)).count s := by
    have h := htake
    rw [show cs.take (n + 1) = cellsOfWord (l.take (n + 1)) by
      simp [cs, cellsOfWord_take]] at h
    exact ((mem_cellsOfWord_step (l := l.take (n + 1)) (s := s) (j := j)).1 h).2
  by_contra hs
  have hs' : l[n] ≠ s := by
    intro h
    exact hs (by simp [h])
  have hsame := count_take_succ_of_ne (l := l) (s := s) (n := n) hnl hs'
  rw [hsame, hbefore] at hafter_ge
  omega

lemma cellsOfWord_idx_same_row_lt {l : List Step} {s : Step} {j₁ j₂ : ℕ}
    (hj₁ : 0 < j₁) (hj : j₁ < j₂)
    (hmem₂ : (rowOfStep s, j₂) ∈ cellsOfWord l) :
    (cellsOfWord l).idxOf (rowOfStep s, j₁) <
      (cellsOfWord l).idxOf (rowOfStep s, j₂) := by
  let cs := cellsOfWord l
  let n := cs.idxOf (rowOfStep s, j₂)
  have hj₂ : 0 < j₂ := lt_trans hj₁ hj
  have hbefore := count_take_idxOf_cell (l := l) (s := s) (j := j₂) hj₂ hmem₂
  have hmem₁ : (rowOfStep s, j₁) ∈ cs := by
    have hcount : j₁ ≤ l.count s := by
      have := ((mem_cellsOfWord_step (l := l) (s := s) (j := j₂)).1 hmem₂).2
      omega
    exact (mem_cellsOfWord_step (l := l) (s := s) (j := j₁)).2 ⟨hj₁, hcount⟩
  have htake : (rowOfStep s, j₁) ∈ cs.take n := by
    rw [show cs.take n = cellsOfWord (l.take n) by simp [cs, cellsOfWord_take]]
    apply (mem_cellsOfWord_step (l := l.take n) (s := s) (j := j₁)).2
    constructor
    · exact hj₁
    · rw [hbefore]
      omega
  exact (List.mem_take_iff_idxOf_lt hmem₁).1 htake

lemma cellsOfWord_idx_col12_lt {l : List Step} (hg : PrefixGood l) {j : ℕ}
    (hmemB : (2, j) ∈ cellsOfWord l) :
    (cellsOfWord l).idxOf (1, j) < (cellsOfWord l).idxOf (2, j) := by
  let cs := cellsOfWord l
  let n := cs.idxOf (2, j)
  have hj : 0 < j := ((mem_cellsOfWord_two (l := l) (j := j)).1 hmemB).1
  have hmemB' : (rowOfStep B, j) ∈ cellsOfWord l := by simpa [rowOfStep] using hmemB
  have hBbefore := count_take_idxOf_cell (l := l) (s := B) (j := j) hj hmemB'
  have hncs : n < cs.length := List.idxOf_lt_length_of_mem hmemB
  have hnl : n < l.length := by simpa [cs, cellsOfWord_length] using hncs
  have hgetB : l[n] = B := by
    have hopt : l[n]? = some B := by
      simpa [n, cs, rowOfStep] using
        getElem?_idxOf_cell_eq_step (l := l) (s := B) (j := j) hj hmemB'
    rw [List.getElem?_eq_getElem hnl] at hopt
    exact Option.some.inj hopt
  have hBbefore_n : (l.take n).count B = j - 1 := by
    simpa [n, cs, rowOfStep] using hBbefore
  have hBafter : (l.take (n + 1)).count B = j := by
    rw [count_take_succ_of_eq hnl hgetB, hBbefore_n]
    omega
  have hAunchanged : (l.take (n + 1)).count A = (l.take n).count A := by
    exact count_take_succ_of_ne (l := l) (s := A) (n := n) hnl (by simpa [hgetB])
  have hgood := (hg (l.take (n + 1)) (List.take_prefix _ _)).1
  have hAbefore_ge : j ≤ (l.take n).count A := by
    rw [← hAunchanged]
    omega
  have hAfull : (1, j) ∈ cs := by
    rw [mem_cellsOfWord_one]
    exact ⟨hj, le_trans hAbefore_ge (List.Sublist.count_le A (List.take_sublist n l))⟩
  have hAtake : (1, j) ∈ cs.take n := by
    rw [show cs.take n = cellsOfWord (l.take n) by simp [cs, cellsOfWord_take]]
    exact (mem_cellsOfWord_one (l := l.take n) (j := j)).2 ⟨hj, hAbefore_ge⟩
  exact (List.mem_take_iff_idxOf_lt hAfull).1 hAtake

lemma cellsOfWord_idx_col23_lt {l : List Step} (hg : PrefixGood l) {j : ℕ}
    (hmemC : (3, j) ∈ cellsOfWord l) :
    (cellsOfWord l).idxOf (2, j) < (cellsOfWord l).idxOf (3, j) := by
  let cs := cellsOfWord l
  let n := cs.idxOf (3, j)
  have hj : 0 < j := ((mem_cellsOfWord_three (l := l) (j := j)).1 hmemC).1
  have hmemC' : (rowOfStep C, j) ∈ cellsOfWord l := by simpa [rowOfStep] using hmemC
  have hCbefore := count_take_idxOf_cell (l := l) (s := C) (j := j) hj hmemC'
  have hncs : n < cs.length := List.idxOf_lt_length_of_mem hmemC
  have hnl : n < l.length := by simpa [cs, cellsOfWord_length] using hncs
  have hgetC : l[n] = C := by
    have hopt : l[n]? = some C := by
      simpa [n, cs, rowOfStep] using
        getElem?_idxOf_cell_eq_step (l := l) (s := C) (j := j) hj hmemC'
    rw [List.getElem?_eq_getElem hnl] at hopt
    exact Option.some.inj hopt
  have hCbefore_n : (l.take n).count C = j - 1 := by
    simpa [n, cs, rowOfStep] using hCbefore
  have hCafter : (l.take (n + 1)).count C = j := by
    rw [count_take_succ_of_eq hnl hgetC, hCbefore_n]
    omega
  have hBunchanged : (l.take (n + 1)).count B = (l.take n).count B := by
    exact count_take_succ_of_ne (l := l) (s := B) (n := n) hnl (by simpa [hgetC])
  have hgood := (hg (l.take (n + 1)) (List.take_prefix _ _)).2
  have hBbefore_ge : j ≤ (l.take n).count B := by
    rw [← hBunchanged]
    omega
  have hBfull : (2, j) ∈ cs := by
    rw [mem_cellsOfWord_two]
    exact ⟨hj, le_trans hBbefore_ge (List.Sublist.count_le B (List.take_sublist n l))⟩
  have hBtake : (2, j) ∈ cs.take n := by
    rw [show cs.take n = cellsOfWord (l.take n) by simp [cs, cellsOfWord_take]]
    exact (mem_cellsOfWord_two (l := l.take n) (j := j)).2 ⟨hj, hBbefore_ge⟩
  exact (List.mem_take_iff_idxOf_lt hBfull).1 hBtake

noncomputable def tableauOfCellList (cs : List (ℕ × ℕ)) (p : ℕ × ℕ) : ℕ :=
  if p ∈ cs then cs.idxOf p + 1 else 0

lemma tableauOfCellList_apply_mem {cs : List (ℕ × ℕ)} {p : ℕ × ℕ} (hp : p ∈ cs) :
    tableauOfCellList cs p = cs.idxOf p + 1 := by
  simp [tableauOfCellList, hp]

lemma tableauOfCellList_bijOn {cs : List (ℕ × ℕ)} {s : Set (ℕ × ℕ)} {n : ℕ}
    (hmem : ∀ p, p ∈ cs ↔ p ∈ s) (hlen : cs.length = n) (hnodup : cs.Nodup) :
    Set.BijOn (tableauOfCellList cs) s (Finset.Icc 1 n) := by
  refine Set.BijOn.mk ?maps ?inj ?surj
  · intro p hp
    have hpcs : p ∈ cs := (hmem p).2 hp
    have hidx : cs.idxOf p < n := by
      rw [← hlen]
      exact List.idxOf_lt_length_of_mem hpcs
    simp [tableauOfCellList, hpcs, Finset.mem_Icc]
    omega
  · intro p hp q hq heq
    have hpcs : p ∈ cs := (hmem p).2 hp
    have hqcs : q ∈ cs := (hmem q).2 hq
    simp [tableauOfCellList, hpcs, hqcs] at heq
    have hidx : cs.idxOf p = cs.idxOf q := by omega
    exact (List.idxOf_inj hpcs).1 hidx
  · intro k hk
    have hk' : 1 ≤ k ∧ k ≤ n := by
      simpa [Finset.mem_Icc] using hk
    have hlt : k - 1 < cs.length := by
      rw [hlen]
      omega
    let p : ℕ × ℕ := cs[k - 1]
    have hpcs : p ∈ cs := List.getElem_mem hlt
    refine ⟨p, (hmem p).1 hpcs, ?_⟩
    have hidx : cs.idxOf p = k - 1 := by
      simpa [p] using hnodup.idxOf_getElem (k - 1) hlt
    simp [tableauOfCellList, hpcs, hidx]
    omega

noncomputable def tableauOfBallotWord (l : List Step) : ℕ × ℕ → ℕ :=
  tableauOfCellList (cellsOfWord l.reverse)

lemma Ballot_full_cells {l : List Step} (hl : l ∈ Ballot 0 0 2024) :
    ∀ p : ℕ × ℕ,
      p ∈ cellsOfWord l.reverse ↔
        p ∈ (Finset.Icc 1 3 ×ˢ Finset.Icc 1 2024 : Finset (ℕ × ℕ)) := by
  rcases hl with ⟨_, hA, hB, hC⟩
  intro p
  rcases p with ⟨i, j⟩
  have hAr : (l.reverse.count A) = 2024 := by simpa [List.count_reverse] using hA
  have hBr : (l.reverse.count B) = 2024 := by simpa [List.count_reverse] using hB
  have hCr : (l.reverse.count C) = 2024 := by simpa [List.count_reverse] using hC
  rw [mem_cellsOfWord_iff]
  simp [Finset.mem_product, Finset.mem_Icc, hAr, hBr, hCr]
  omega

lemma tableauOfCellList_lt_of_idx_lt {cs : List (ℕ × ℕ)} {p q : ℕ × ℕ}
    (hp : p ∈ cs) (hq : q ∈ cs) (hidx : cs.idxOf p < cs.idxOf q) :
    tableauOfCellList cs p < tableauOfCellList cs q := by
  simp [tableauOfCellList, hp, hq]
  omega

lemma tableauOfBallotWord_mem_full {l : List Step} (hl : l ∈ Ballot 0 0 2024) :
    tableauOfBallotWord l ∈
      {T : ℕ × ℕ → ℕ | Set.BijOn T (Finset.Icc 1 3 ×ˢ Finset.Icc 1 2024) (Finset.Icc 1 6072) ∧
        (∀ j ∈ Finset.Icc 1 2024, StrictMonoOn (fun i => T (i, j)) (Set.Icc 1 3)) ∧
        (∀ i ∈ Finset.Icc 1 3, StrictMonoOn (fun j => T (i, j)) (Set.Icc 1 2024)) ∧
        (∀ x, x ∉ Finset.Icc 1 3 ×ˢ Finset.Icc 1 2024 → T x = 0)} := by
  let w := l.reverse
  let cs := cellsOfWord w
  have hcellsFin : ∀ p : ℕ × ℕ,
      p ∈ cs ↔ p ∈ (Finset.Icc 1 3 ×ˢ Finset.Icc 1 2024 : Finset (ℕ × ℕ)) := by
    intro p
    simpa [cs, w] using Ballot_full_cells (l := l) hl p
  have hcells : ∀ p : ℕ × ℕ,
      p ∈ cs ↔ p ∈ Set.Icc (1, 1) (3, 2024) := by
    intro p
    rw [hcellsFin p]
    rcases p with ⟨i, j⟩
    simp [Finset.mem_product, Finset.mem_Icc, Set.mem_Icc, Prod.le_def]
    omega
  have hlen : cs.length = 6072 := by
    have hlenl := Ballot_length (x := 0) (y := 0) (z := 2024) hl
    simp [cs, w, cellsOfWord_length, hlenl]
  have hnodup : cs.Nodup := by
    simpa [cs] using cellsOfWord_nodup w
  have hprefix : PrefixGood w := by
    simpa [w, prefixGood_reverse] using hl.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [tableauOfBallotWord, cs, w] using
      tableauOfCellList_bijOn (cs := cs)
        (s := Set.Icc (1, 1) (3, 2024)) hcells hlen hnodup
  · intro j hj
    intro i hi k hk hik
    have hj' : 1 ≤ j ∧ j ≤ 2024 := by simpa [Finset.mem_Icc] using hj
    have hi' : 1 ≤ i ∧ i ≤ 3 := by simpa [Set.mem_Icc] using hi
    have hk' : 1 ≤ k ∧ k ≤ 3 := by simpa [Set.mem_Icc] using hk
    have hmem1 : (1, j) ∈ cs := (hcellsFin (1, j)).2 (by simp [Finset.mem_product, Finset.mem_Icc, hj'])
    have hmem2 : (2, j) ∈ cs := (hcellsFin (2, j)).2 (by simp [Finset.mem_product, Finset.mem_Icc, hj'])
    have hmem3 : (3, j) ∈ cs := (hcellsFin (3, j)).2 (by simp [Finset.mem_product, Finset.mem_Icc, hj'])
    have h12 : cs.idxOf (1, j) < cs.idxOf (2, j) := by
      simpa [cs] using cellsOfWord_idx_col12_lt (l := w) hprefix (j := j) (by simpa [cs] using hmem2)
    have h23 : cs.idxOf (2, j) < cs.idxOf (3, j) := by
      simpa [cs] using cellsOfWord_idx_col23_lt (l := w) hprefix (j := j) (by simpa [cs] using hmem3)
    have h13 : cs.idxOf (1, j) < cs.idxOf (3, j) := lt_trans h12 h23
    have hi_cases : i = 1 ∨ i = 2 ∨ i = 3 := by omega
    have hk_cases : k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hi_cases with rfl | rfl | rfl <;> rcases hk_cases with rfl | rfl | rfl
    all_goals try omega
    · simpa [tableauOfBallotWord, cs, w] using
        tableauOfCellList_lt_of_idx_lt (cs := cs) hmem1 hmem2 h12
    · simpa [tableauOfBallotWord, cs, w] using
        tableauOfCellList_lt_of_idx_lt (cs := cs) hmem1 hmem3 h13
    · simpa [tableauOfBallotWord, cs, w] using
        tableauOfCellList_lt_of_idx_lt (cs := cs) hmem2 hmem3 h23
  · intro i hi
    intro j hj k hk hjk
    have hi' : 1 ≤ i ∧ i ≤ 3 := by simpa [Finset.mem_Icc] using hi
    have hj' : 1 ≤ j ∧ j ≤ 2024 := by simpa [Set.mem_Icc] using hj
    have hk' : 1 ≤ k ∧ k ≤ 2024 := by simpa [Set.mem_Icc] using hk
    have hmem1 : (i, j) ∈ cs := (hcellsFin (i, j)).2 (by simp [Finset.mem_product, Finset.mem_Icc, hi', hj'])
    have hmem2 : (i, k) ∈ cs := (hcellsFin (i, k)).2 (by simp [Finset.mem_product, Finset.mem_Icc, hi', hk'])
    have hi_cases : i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi_cases with rfl | rfl | rfl
    · have hidx : cs.idxOf (1, j) < cs.idxOf (1, k) := by
        simpa [cs, rowOfStep] using
          cellsOfWord_idx_same_row_lt (l := w) (s := A) (j₁ := j) (j₂ := k) hj'.1 hjk
            (by simpa [cs, rowOfStep] using hmem2)
      simpa [tableauOfBallotWord, cs, w] using
        tableauOfCellList_lt_of_idx_lt (cs := cs) hmem1 hmem2 hidx
    · have hidx : cs.idxOf (2, j) < cs.idxOf (2, k) := by
        simpa [cs, rowOfStep] using
          cellsOfWord_idx_same_row_lt (l := w) (s := B) (j₁ := j) (j₂ := k) hj'.1 hjk
            (by simpa [cs, rowOfStep] using hmem2)
      simpa [tableauOfBallotWord, cs, w] using
        tableauOfCellList_lt_of_idx_lt (cs := cs) hmem1 hmem2 hidx
    · have hidx : cs.idxOf (3, j) < cs.idxOf (3, k) := by
        simpa [cs, rowOfStep] using
          cellsOfWord_idx_same_row_lt (l := w) (s := C) (j₁ := j) (j₂ := k) hj'.1 hjk
            (by simpa [cs, rowOfStep] using hmem2)
      simpa [tableauOfBallotWord, cs, w] using
        tableauOfCellList_lt_of_idx_lt (cs := cs) hmem1 hmem2 hidx
  · intro x hx
    have hxcs : x ∉ cs := by
      intro h
      exact hx ((hcellsFin x).1 h)
    simp [tableauOfBallotWord, tableauOfCellList, cs, w, hxcs]

def rectSet : Set (ℕ × ℕ) := Set.Icc (1, 1) (3, 2024)

def valueSet : Set ℕ := Set.Icc 1 6072

lemma mem_rectSet_iff_finset (p : ℕ × ℕ) :
    p ∈ rectSet ↔ p ∈ (Finset.Icc 1 3 ×ˢ Finset.Icc 1 2024 : Finset (ℕ × ℕ)) := by
  rcases p with ⟨i, j⟩
  simp [rectSet, Set.mem_Icc, Prod.le_def, Finset.mem_product, Finset.mem_Icc]
  omega

lemma mem_valueSet_iff_finset (n : ℕ) :
    n ∈ valueSet ↔ n ∈ Finset.Icc 1 6072 := by
  simp [valueSet, Set.mem_Icc, Finset.mem_Icc]

noncomputable def cellsOfTableau (T : ℕ × ℕ → ℕ) : List (ℕ × ℕ) :=
  (List.range 6072).map fun n => Function.invFunOn T rectSet (n + 1)

lemma cellsOfTableau_length (T : ℕ × ℕ → ℕ) :
    (cellsOfTableau T).length = 6072 := by
  simp [cellsOfTableau]

lemma cellsOfTableau_mem {T : ℕ × ℕ → ℕ}
    (hbij : Set.BijOn T rectSet valueSet) :
    ∀ p : ℕ × ℕ, p ∈ cellsOfTableau T ↔ p ∈ rectSet := by
  intro p
  constructor
  · intro hp
    rcases List.mem_map.1 hp with ⟨n, hn, rfl⟩
    have hnval : n + 1 ∈ valueSet := by
      rw [mem_valueSet_iff_finset]
      rw [Finset.mem_Icc]
      have hn' : n < 6072 := by simpa [List.mem_range] using hn
      omega
    exact (hbij.invOn_invFunOn.1.mapsTo hbij.surjOn) hnval
  · intro hp
    have hTval : T p ∈ valueSet := hbij.mapsTo hp
    have hTbounds : 1 ≤ T p ∧ T p ≤ 6072 := by simpa [valueSet, Set.mem_Icc] using hTval
    have hpre : T p - 1 < 6072 := by omega
    refine List.mem_map.2 ⟨T p - 1, by simpa [List.mem_range] using hpre, ?_⟩
    have hleft := hbij.invOn_invFunOn.1.eq hp
    have harg : T p - 1 + 1 = T p := by omega
    rw [harg]
    exact hleft

lemma cellsOfTableau_nodup {T : ℕ × ℕ → ℕ}
    (hbij : Set.BijOn T rectSet valueSet) :
    (cellsOfTableau T).Nodup := by
  unfold cellsOfTableau
  apply List.Nodup.map_on
  · intro m hm n hn hmn
    have hm_lt : m < 6072 := by simpa [List.mem_range] using hm
    have hn_lt : n < 6072 := by simpa [List.mem_range] using hn
    have hmval : m + 1 ∈ valueSet := by
      rw [mem_valueSet_iff_finset, Finset.mem_Icc]
      omega
    have hnval : n + 1 ∈ valueSet := by
      rw [mem_valueSet_iff_finset, Finset.mem_Icc]
      omega
    have hmright := hbij.invOn_invFunOn.2.eq hmval
    have hnright := hbij.invOn_invFunOn.2.eq hnval
    have hT := congrArg T hmn
    rw [hmright, hnright] at hT
    omega
  · exact List.nodup_range

lemma cellsOfTableau_idxOf {T : ℕ × ℕ → ℕ}
    (hbij : Set.BijOn T rectSet valueSet) {p : ℕ × ℕ} (hp : p ∈ rectSet) :
    (cellsOfTableau T).idxOf p = T p - 1 := by
  have hTval : T p ∈ valueSet := hbij.mapsTo hp
  have hTbounds : 1 ≤ T p ∧ T p ≤ 6072 := by
    simpa [valueSet, Set.mem_Icc] using hTval
  have hidx : T p - 1 < (cellsOfTableau T).length := by
    rw [cellsOfTableau_length]
    omega
  have hget : (cellsOfTableau T)[T p - 1] = p := by
    unfold cellsOfTableau
    rw [List.getElem_map]
    rw [List.getElem_range]
    · have harg : T p - 1 + 1 = T p := by omega
      rw [harg]
      exact hbij.invOn_invFunOn.1.eq hp
  simpa [hget] using (cellsOfTableau_nodup hbij).idxOf_getElem (T p - 1) hidx

lemma mem_cellsOfTableau_take_iff {T : ℕ × ℕ → ℕ}
    (hbij : Set.BijOn T rectSet valueSet) {p : ℕ × ℕ} {n : ℕ} :
    p ∈ (cellsOfTableau T).take n ↔ p ∈ rectSet ∧ T p ≤ n := by
  constructor
  · intro hp
    have hpfull : p ∈ cellsOfTableau T := List.mem_of_mem_take hp
    have hprect : p ∈ rectSet := (cellsOfTableau_mem hbij p).1 hpfull
    have hidxlt := (List.mem_take_iff_idxOf_lt hpfull).1 hp
    rw [cellsOfTableau_idxOf hbij hprect] at hidxlt
    have hTval : T p ∈ valueSet := hbij.mapsTo hprect
    have hTbounds : 1 ≤ T p ∧ T p ≤ 6072 := by
      simpa [valueSet, Set.mem_Icc] using hTval
    exact ⟨hprect, by omega⟩
  · rintro ⟨hprect, hTle⟩
    have hpfull : p ∈ cellsOfTableau T := (cellsOfTableau_mem hbij p).2 hprect
    rw [List.mem_take_iff_idxOf_lt hpfull]
    rw [cellsOfTableau_idxOf hbij hprect]
    have hTval : T p ∈ valueSet := hbij.mapsTo hprect
    have hTbounds : 1 ≤ T p ∧ T p ≤ 6072 := by
      simpa [valueSet, Set.mem_Icc] using hTval
    omega

lemma rowWord_count_one (cs : List (ℕ × ℕ)) :
    (rowWordOfCells cs).count A = (cs.filter fun p => p.1 == 1).length := by
  induction cs with
  | nil => simp [rowWordOfCells]
  | cons p t ih =>
      rcases p with ⟨i, j⟩
      by_cases h1 : i = 1
      · subst i
        simp [rowWordOfCells, stepOfRow]
        simpa [rowWordOfCells] using ih
      · have hne : stepOfRow i ≠ A := by
          by_cases h2 : i = 2 <;> simp [stepOfRow, h1, h2]
        change (stepOfRow i :: rowWordOfCells t).count A =
          (List.filter (fun p => p.1 == 1) ((i, j) :: t)).length
        rw [List.count_cons_of_ne hne]
        simp [h1]
        simpa [rowWordOfCells] using ih

lemma rowWord_count_two (cs : List (ℕ × ℕ)) :
    (rowWordOfCells cs).count B = (cs.filter fun p => p.1 == 2).length := by
  induction cs with
  | nil => simp [rowWordOfCells]
  | cons p t ih =>
      rcases p with ⟨i, j⟩
      by_cases h1 : i = 1
      · subst i
        simp [rowWordOfCells, stepOfRow]
        simpa [rowWordOfCells] using ih
      · by_cases h2 : i = 2
        · subst i
          simp [rowWordOfCells, stepOfRow]
          simpa [rowWordOfCells] using ih
        · simp [rowWordOfCells, stepOfRow, h1, h2]
          simpa [rowWordOfCells] using ih

lemma rowWord_count_three_of_rows {cs : List (ℕ × ℕ)}
    (hrows : ∀ p ∈ cs, p.1 = 1 ∨ p.1 = 2 ∨ p.1 = 3) :
    (rowWordOfCells cs).count C = (cs.filter fun p => p.1 == 3).length := by
  induction cs with
  | nil => simp [rowWordOfCells]
  | cons p t ih =>
      have htail : ∀ q ∈ t, q.1 = 1 ∨ q.1 = 2 ∨ q.1 = 3 := by
        intro q hq
        exact hrows q (by simp [hq])
      rcases p with ⟨i, j⟩
      have hp := hrows (i, j) (by simp)
      rcases hp with h1 | h2 | h3
      · simp at h1
        subst i
        change (A :: rowWordOfCells t).count C =
          (List.filter (fun p => p.1 == 3) ((1, j) :: t)).length
        simp [stepOfRow]
        simpa [rowWordOfCells] using ih htail
      · simp at h2
        subst i
        change (B :: rowWordOfCells t).count C =
          (List.filter (fun p => p.1 == 3) ((2, j) :: t)).length
        simp [stepOfRow]
        simpa [rowWordOfCells] using ih htail
      · simp at h3
        subst i
        change (C :: rowWordOfCells t).count C =
          (List.filter (fun p => p.1 == 3) ((3, j) :: t)).length
        simp [stepOfRow]
        simpa [rowWordOfCells] using ih htail

lemma filter_row_two_length_le_one {cs : List (ℕ × ℕ)} (hnodup : cs.Nodup)
    (hup : ∀ j, (2, j) ∈ cs → (1, j) ∈ cs) :
    (cs.filter fun p => p.1 == 2).length ≤ (cs.filter fun p => p.1 == 1).length := by
  let bs := cs.filter fun p => p.1 == 2
  let as := cs.filter fun p => p.1 == 1
  let f : ℕ × ℕ → ℕ × ℕ := fun p => (1, p.2)
  have hbsnodup : bs.Nodup := by
    simpa [bs] using hnodup.filter (fun p => p.1 == 2)
  have hmapnodup : (bs.map f).Nodup := by
    apply hbsnodup.map_on
    intro p hp q hq hpq
    have hp2 : p.1 = 2 := by
      exact (by simpa [bs] using hp : p ∈ cs ∧ p.1 = 2).2
    have hq2 : q.1 = 2 := by
      exact (by simpa [bs] using hq : q ∈ cs ∧ q.1 = 2).2
    rcases p with ⟨pi, pj⟩
    rcases q with ⟨qi, qj⟩
    simp [f] at hpq hp2 hq2 ⊢
    omega
  have hsubset : bs.map f ⊆ as := by
    intro x hx
    rcases List.mem_map.1 hx with ⟨p, hp, rfl⟩
    rcases p with ⟨pi, pj⟩
    have hpf : (pi, pj) ∈ cs ∧ pi = 2 := by
      simpa [bs] using hp
    have hp_cs : (pi, pj) ∈ cs := hpf.1
    have hpi : pi = 2 := by
      exact hpf.2
    subst pi
    have htarget : (1, pj) ∈ cs := hup pj hp_cs
    change (1, pj) ∈ as
    simp [as, htarget]
  have hsubperm := List.subperm_of_subset hmapnodup hsubset
  have hlen := hsubperm.length_le
  simpa [bs, as, f] using hlen

lemma filter_row_three_length_le_two {cs : List (ℕ × ℕ)} (hnodup : cs.Nodup)
    (hup : ∀ j, (3, j) ∈ cs → (2, j) ∈ cs) :
    (cs.filter fun p => p.1 == 3).length ≤ (cs.filter fun p => p.1 == 2).length := by
  let cs3 := cs.filter fun p => p.1 == 3
  let cs2 := cs.filter fun p => p.1 == 2
  let f : ℕ × ℕ → ℕ × ℕ := fun p => (2, p.2)
  have h3nodup : cs3.Nodup := by
    simpa [cs3] using hnodup.filter (fun p => p.1 == 3)
  have hmapnodup : (cs3.map f).Nodup := by
    apply h3nodup.map_on
    intro p hp q hq hpq
    have hp3 : p.1 = 3 := by
      exact (by simpa [cs3] using hp : p ∈ cs ∧ p.1 = 3).2
    have hq3 : q.1 = 3 := by
      exact (by simpa [cs3] using hq : q ∈ cs ∧ q.1 = 3).2
    rcases p with ⟨pi, pj⟩
    rcases q with ⟨qi, qj⟩
    simp [f] at hpq hp3 hq3 ⊢
    omega
  have hsubset : cs3.map f ⊆ cs2 := by
    intro x hx
    rcases List.mem_map.1 hx with ⟨p, hp, rfl⟩
    rcases p with ⟨pi, pj⟩
    have hpf : (pi, pj) ∈ cs ∧ pi = 3 := by
      simpa [cs3] using hp
    have hp_cs : (pi, pj) ∈ cs := hpf.1
    have hpi : pi = 3 := by
      exact hpf.2
    subst pi
    have htarget : (2, pj) ∈ cs := hup pj hp_cs
    change (2, pj) ∈ cs2
    simp [cs2, htarget]
  have hsubperm := List.subperm_of_subset hmapnodup hsubset
  have hlen := hsubperm.length_le
  simpa [cs3, cs2, f] using hlen

lemma tableau_prefix_counts {T : ℕ × ℕ → ℕ}
    (hbij : Set.BijOn T rectSet valueSet)
    (hcol : ∀ j ∈ Finset.Icc 1 2024, StrictMonoOn (fun i => T (i, j)) (Set.Icc 1 3))
    (n : ℕ) :
    (rowWordOfCells ((cellsOfTableau T).take n)).count B ≤
        (rowWordOfCells ((cellsOfTableau T).take n)).count A ∧
      (rowWordOfCells ((cellsOfTableau T).take n)).count C ≤
        (rowWordOfCells ((cellsOfTableau T).take n)).count B := by
  let pref := (cellsOfTableau T).take n
  have hnodup : pref.Nodup := by
    exact (cellsOfTableau_nodup hbij).sublist (List.take_sublist n (cellsOfTableau T))
  have hrows : ∀ p ∈ pref, p.1 = 1 ∨ p.1 = 2 ∨ p.1 = 3 := by
    intro p hp
    have hrect := (mem_cellsOfTableau_take_iff hbij).1 (by simpa [pref] using hp) |>.1
    rcases p with ⟨i, j⟩
    simp [rectSet, Set.mem_Icc, Prod.le_def] at hrect
    omega
  have hup12 : ∀ j, (2, j) ∈ pref → (1, j) ∈ pref := by
    intro j hp
    have hpinfo := (mem_cellsOfTableau_take_iff hbij).1 (by simpa [pref] using hp)
    have hjbounds : 1 ≤ j ∧ j ≤ 2024 := by
      simpa [rectSet, Set.mem_Icc, Prod.le_def] using hpinfo.1
    have hrect1 : (1, j) ∈ rectSet := by
      simp [rectSet, Set.mem_Icc, Prod.le_def, hjbounds]
    have hlt : T (1, j) < T (2, j) := by
      exact hcol j (by simpa [Finset.mem_Icc] using hjbounds)
        (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num)
    exact (mem_cellsOfTableau_take_iff hbij).2 ⟨hrect1, le_trans (le_of_lt hlt) hpinfo.2⟩
  have hup23 : ∀ j, (3, j) ∈ pref → (2, j) ∈ pref := by
    intro j hp
    have hpinfo := (mem_cellsOfTableau_take_iff hbij).1 (by simpa [pref] using hp)
    have hjbounds : 1 ≤ j ∧ j ≤ 2024 := by
      simpa [rectSet, Set.mem_Icc, Prod.le_def] using hpinfo.1
    have hrect2 : (2, j) ∈ rectSet := by
      simp [rectSet, Set.mem_Icc, Prod.le_def, hjbounds]
    have hlt : T (2, j) < T (3, j) := by
      exact hcol j (by simpa [Finset.mem_Icc] using hjbounds)
        (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num)
    exact (mem_cellsOfTableau_take_iff hbij).2 ⟨hrect2, le_trans (le_of_lt hlt) hpinfo.2⟩
  have h12 := filter_row_two_length_le_one hnodup hup12
  have h23 := filter_row_three_length_le_two hnodup hup23
  have hA := rowWord_count_one pref
  have hB := rowWord_count_two pref
  have hC := rowWord_count_three_of_rows hrows
  constructor
  · rw [hA, hB]
    exact h12
  · rw [hB, hC]
    exact h23

def canonicalFullWord : List Step :=
  List.replicate 2024 A ++ List.replicate 2024 B ++ List.replicate 2024 C

lemma canonicalFullWord_counts :
    canonicalFullWord.count A = 2024 ∧
      canonicalFullWord.count B = 2024 ∧
        canonicalFullWord.count C = 2024 := by
  unfold canonicalFullWord
  simp only [List.count_append, List.count_replicate]
  decide

lemma canonicalFullCells_mem :
    ∀ p : ℕ × ℕ, p ∈ cellsOfWord canonicalFullWord ↔ p ∈ rectSet := by
  intro p
  rcases p with ⟨i, j⟩
  have hcounts := canonicalFullWord_counts
  rw [mem_cellsOfWord_iff]
  simp [rectSet, Set.mem_Icc, Prod.le_def, hcounts.1, hcounts.2.1, hcounts.2.2]
  omega

lemma rowWord_counts_of_rect {cs : List (ℕ × ℕ)}
    (hnodup : cs.Nodup) (hmem : ∀ p : ℕ × ℕ, p ∈ cs ↔ p ∈ rectSet) :
    (rowWordOfCells cs).count A = 2024 ∧
      (rowWordOfCells cs).count B = 2024 ∧
        (rowWordOfCells cs).count C = 2024 := by
  let canonCells := cellsOfWord canonicalFullWord
  have hcanonNodup : canonCells.Nodup := by
    simpa [canonCells] using cellsOfWord_nodup canonicalFullWord
  have hperm : cs.Perm canonCells := by
    apply (List.perm_ext_iff_of_nodup hnodup hcanonNodup).2
    intro p
    rw [hmem p, canonicalFullCells_mem p]
  have hmap := hperm.map (fun p : ℕ × ℕ => stepOfRow p.1)
  have hcanonRow : rowWordOfCells canonCells = canonicalFullWord := by
    simpa [canonCells] using cellsOfWord_rowWord canonicalFullWord
  have hA : (rowWordOfCells cs).count A = (rowWordOfCells canonCells).count A := by
    simpa [rowWordOfCells] using hmap.count_eq A
  have hB : (rowWordOfCells cs).count B = (rowWordOfCells canonCells).count B := by
    simpa [rowWordOfCells] using hmap.count_eq B
  have hC : (rowWordOfCells cs).count C = (rowWordOfCells canonCells).count C := by
    simpa [rowWordOfCells] using hmap.count_eq C
  rw [hcanonRow] at hA hB hC
  rw [canonicalFullWord_counts.1] at hA
  rw [canonicalFullWord_counts.2.1] at hB
  rw [canonicalFullWord_counts.2.2] at hC
  exact ⟨hA, hB, hC⟩

noncomputable def ballotWordOfTableau (T : ℕ × ℕ → ℕ) : List Step :=
  (rowWordOfCells (cellsOfTableau T)).reverse

lemma ballotWordOfTableau_mem {T : ℕ × ℕ → ℕ}
    (hbij : Set.BijOn T rectSet valueSet)
    (hcol : ∀ j ∈ Finset.Icc 1 2024, StrictMonoOn (fun i => T (i, j)) (Set.Icc 1 3)) :
    ballotWordOfTableau T ∈ Ballot 0 0 2024 := by
  let w := rowWordOfCells (cellsOfTableau T)
  have hcounts := rowWord_counts_of_rect (cellsOfTableau_nodup hbij) (cellsOfTableau_mem hbij)
  have hpref : PrefixGood w := by
    intro t ht
    have ht' := (List.prefix_iff_eq_take).1 ht
    rw [ht']
    rw [show (rowWordOfCells (cellsOfTableau T)).take t.length =
        rowWordOfCells ((cellsOfTableau T).take t.length) by
      simpa [w] using rowWord_take (cellsOfTableau T) t.length]
    exact tableau_prefix_counts hbij hcol t.length
  have hsuff : SuffixGood (ballotWordOfTableau T) := by
    unfold ballotWordOfTableau
    rw [← prefixGood_reverse]
    simpa [w] using hpref
  refine ⟨hsuff, ?_, ?_, ?_⟩
  · unfold ballotWordOfTableau
    rw [List.count_reverse]
    simpa [w] using hcounts.1
  · unfold ballotWordOfTableau
    rw [List.count_reverse]
    simpa [w] using hcounts.2.1
  · unfold ballotWordOfTableau
    rw [List.count_reverse]
    simpa [w] using hcounts.2.2

lemma rowOfStep_stepOfRow {i : ℕ} (hi : i = 1 ∨ i = 2 ∨ i = 3) :
    rowOfStep (stepOfRow i) = i := by
  rcases hi with rfl | rfl | rfl <;> simp [rowOfStep, stepOfRow]

def rowStartCount (a b c : ℕ) : Step → ℕ
  | A => a
  | B => b
  | C => c

lemma cellsOfWordAux_getElem (a b c : ℕ) (l : List Step) {n : ℕ}
    (hn : n < l.length) :
    (cellsOfWordAux a b c l)[n]'(by simpa [cellsOfWordAux_length] using hn) =
      (rowOfStep l[n], rowStartCount a b c l[n] + (l.take n).count l[n] + 1) := by
  induction l generalizing a b c n with
  | nil =>
      simp at hn
  | cons s t ih =>
      cases n with
      | zero =>
          cases s <;> simp [cellsOfWordAux, rowStartCount, rowOfStep]
      | succ n =>
          have hnt : n < t.length := by simpa using hn
          cases s <;> cases htn : t[n] <;>
            simp [cellsOfWordAux, rowStartCount, rowOfStep, ih, hnt,
              htn, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma cellsOfWord_getElem (l : List Step) {n : ℕ} (hn : n < l.length) :
    (cellsOfWord l)[n]'(by simpa [cellsOfWord_length] using hn) =
      (rowOfStep l[n], (l.take n).count l[n] + 1) := by
  have h := cellsOfWordAux_getElem 0 0 0 l hn
  cases hs : l[n] <;> simpa [cellsOfWord, rowStartCount, hs, Nat.add_assoc] using h

lemma cellsOfWord_get (l : List Step) (i : Fin l.length) :
    (cellsOfWord l).get ⟨i, by simpa [cellsOfWord_length] using i.2⟩ =
      (rowOfStep (l.get i), (l.take i).count (l.get i) + 1) := by
  rw [List.get_eq_getElem]
  rw [List.get_eq_getElem]
  exact cellsOfWord_getElem l i.2

lemma rowWordOfCells_get (cs : List (ℕ × ℕ)) (i : Fin cs.length) :
    (rowWordOfCells cs).get ⟨i, by simpa [rowWordOfCells] using i.2⟩ =
      stepOfRow (cs.get i).1 := by
  unfold rowWordOfCells
  rw [List.get_eq_getElem]
  rw [List.get_eq_getElem]
  rw [List.getElem_map]

lemma nodup_idxOf_get {α : Type*} [BEq α] [LawfulBEq α] {l : List α}
    (h : l.Nodup) (i : Fin l.length) :
    l.idxOf (l.get i) = i := by
  rw [List.get_eq_getElem]
  exact h.idxOf_getElem i i.2

def rowCellsBefore (i j : ℕ) : List (ℕ × ℕ) :=
  (List.range (j - 1)).map fun k => (i, k + 1)

lemma rowCellsBefore_length (i j : ℕ) :
    (rowCellsBefore i j).length = j - 1 := by
  simp [rowCellsBefore]

lemma rowCellsBefore_nodup (i j : ℕ) :
    (rowCellsBefore i j).Nodup := by
  unfold rowCellsBefore
  apply List.Nodup.map_on
  · intro m hm n hn hmn
    simp at hmn
    omega
  · exact List.nodup_range

lemma mem_rowCellsBefore {i j : ℕ} (hj : 0 < j) (p : ℕ × ℕ) :
    p ∈ rowCellsBefore i j ↔ p.1 = i ∧ 0 < p.2 ∧ p.2 < j := by
  rcases p with ⟨r, c⟩
  constructor
  · intro hp
    rcases List.mem_map.1 hp with ⟨k, hk, hkp⟩
    simp [rowCellsBefore] at hk
    simp at hkp
    rcases hkp with ⟨hr, hc⟩
    subst r
    subst c
    omega
  · rintro ⟨hr, hcpos, hclt⟩
    simp at hr
    subst r
    refine List.mem_map.2 ⟨c - 1, ?_, ?_⟩
    · simp [rowCellsBefore]
      omega
    · simp
      omega

lemma filter_row_take_cellsOfTableau_perm {T : ℕ × ℕ → ℕ}
    (hbij : Set.BijOn T rectSet valueSet)
    (hrow : ∀ i ∈ Finset.Icc 1 3, StrictMonoOn (fun j => T (i, j)) (Set.Icc 1 2024))
    {i j : ℕ} (hi : 1 ≤ i ∧ i ≤ 3) (hj : 1 ≤ j ∧ j ≤ 2024) :
    (((cellsOfTableau T).take (T (i, j) - 1)).filter fun p => p.1 == i).Perm
      (rowCellsBefore i j) := by
  apply (List.perm_ext_iff_of_nodup ?left ?right).2
  · intro p
    rw [mem_rowCellsBefore (by omega : 0 < j) p]
    rcases p with ⟨r, c⟩
    constructor
    · intro hp
      have hp' : (r, c) ∈ (cellsOfTableau T).take (T (i, j) - 1) ∧ r = i := by
        simpa using hp
      rcases hp' with ⟨hptake, hr⟩
      have hpinfo := (mem_cellsOfTableau_take_iff hbij).1 hptake
      have hrect : 1 ≤ r ∧ r ≤ 3 ∧ 1 ≤ c ∧ c ≤ 2024 := by
        have hrect' : (1 ≤ r ∧ 1 ≤ c) ∧ r ≤ 3 ∧ c ≤ 2024 := by
          simpa [rectSet, Set.mem_Icc, Prod.le_def] using hpinfo.1
        omega
      subst r
      have hTlt : T (i, c) < T (i, j) := by
        have hTij : 1 ≤ T (i, j) := by
          have hrectij : (i, j) ∈ rectSet := by
            simp [rectSet, Set.mem_Icc, Prod.le_def, hi, hj]
          have hval := hbij.mapsTo hrectij
          have hval' : 1 ≤ T (i, j) ∧ T (i, j) ≤ 6072 := by
            simpa [valueSet, Set.mem_Icc] using hval
          exact hval'.1
        omega
      have hcne : c ≠ j := by
        intro hc
        subst c
        exact (lt_irrefl (T (i, j))) hTlt
      have hclt : c < j := by
        by_contra hnot
        have hjlt : j < c := by omega
        have hlt' : T (i, j) < T (i, c) := by
          exact hrow i (by simpa [Finset.mem_Icc] using hi)
            (by simpa [Set.mem_Icc] using hj)
            (by simpa [Set.mem_Icc] using ⟨hrect.2.2.1, hrect.2.2.2⟩)
            hjlt
        exact (lt_asymm hlt' hTlt)
      exact ⟨rfl, hrect.2.2.1, hclt⟩
    · rintro ⟨hr, hcpos, hclt⟩
      simp at hr
      simp at hcpos hclt
      subst r
      have hrectc : (i, c) ∈ rectSet := by
        have hc_bounds : 1 ≤ c ∧ c ≤ 2024 := by omega
        simp [rectSet, Set.mem_Icc, Prod.le_def, hi, hc_bounds]
      have hlt : T (i, c) < T (i, j) := by
        exact hrow i (by simpa [Finset.mem_Icc] using hi)
          (by simpa [Set.mem_Icc] using ⟨hcpos, le_trans (Nat.le_of_lt hclt) hj.2⟩)
          (by simpa [Set.mem_Icc] using hj) hclt
      have hle : T (i, c) ≤ T (i, j) - 1 := by
        omega
      have htake : (i, c) ∈ (cellsOfTableau T).take (T (i, j) - 1) :=
        (mem_cellsOfTableau_take_iff hbij).2 ⟨hrectc, hle⟩
      simp [htake]
  · exact ((cellsOfTableau_nodup hbij).sublist
      (List.take_sublist (T (i, j) - 1) (cellsOfTableau T))).filter _
  · exact rowCellsBefore_nodup i j

lemma rowWord_take_count_cellsOfTableau {T : ℕ × ℕ → ℕ}
    (hbij : Set.BijOn T rectSet valueSet)
    (hrow : ∀ i ∈ Finset.Icc 1 3, StrictMonoOn (fun j => T (i, j)) (Set.Icc 1 2024))
    {i j : ℕ} (hi : 1 ≤ i ∧ i ≤ 3) (hj : 1 ≤ j ∧ j ≤ 2024) :
    (rowWordOfCells ((cellsOfTableau T).take (T (i, j) - 1))).count (stepOfRow i) =
      j - 1 := by
  have hperm := filter_row_take_cellsOfTableau_perm hbij hrow hi hj
  have hlen := hperm.length_eq
  have hrows : ∀ p ∈ (cellsOfTableau T).take (T (i, j) - 1),
      p.1 = 1 ∨ p.1 = 2 ∨ p.1 = 3 := by
    intro p hp
    have hrect := (mem_cellsOfTableau_take_iff hbij).1 hp |>.1
    rcases p with ⟨r, c⟩
    simp [rectSet, Set.mem_Icc, Prod.le_def] at hrect
    omega
  have hi_cases : i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi_cases with rfl | rfl | rfl
  · rw [show stepOfRow 1 = A by simp [stepOfRow]]
    rw [rowWord_count_one]
    simpa [rowCellsBefore_length] using hlen
  · rw [show stepOfRow 2 = B by simp [stepOfRow]]
    rw [rowWord_count_two]
    simpa [rowCellsBefore_length] using hlen
  · rw [show stepOfRow 3 = C by simp [stepOfRow]]
    rw [rowWord_count_three_of_rows hrows]
    simpa [rowCellsBefore_length] using hlen

lemma cellsOfWord_rowWord_cellsOfTableau {T : ℕ × ℕ → ℕ}
    (hbij : Set.BijOn T rectSet valueSet)
    (hrow : ∀ i ∈ Finset.Icc 1 3, StrictMonoOn (fun j => T (i, j)) (Set.Icc 1 2024)) :
    cellsOfWord (rowWordOfCells (cellsOfTableau T)) = cellsOfTableau T := by
  apply List.ext_get
  · simp [rowWordOfCells, cellsOfWord_length]
  · intro n hnleft hnright
    let baseIdx : Fin (cellsOfTableau T).length := ⟨n, hnright⟩
    let w := rowWordOfCells (cellsOfTableau T)
    have hnw : n < w.length := by
      simpa [w, rowWordOfCells] using hnright
    let wordIdx : Fin w.length := ⟨n, hnw⟩
    let cell := (cellsOfTableau T).get baseIdx
    have hp : cell ∈ cellsOfTableau T := List.get_mem (cellsOfTableau T) ⟨n, hnright⟩
    have hprect := (cellsOfTableau_mem hbij cell).1 hp
    rcases hcsn : cell with ⟨i, j⟩
    have hprect_pair : (i, j) ∈ rectSet := by
      simpa [hcsn] using hprect
    have hbounds : 1 ≤ i ∧ i ≤ 3 ∧ 1 ≤ j ∧ j ≤ 2024 := by
      have hbounds' : (1 ≤ i ∧ 1 ≤ j) ∧ i ≤ 3 ∧ j ≤ 2024 := by
        simpa [rectSet, Set.mem_Icc, Prod.le_def] using hprect_pair
      omega
    have hidx_n : (cellsOfTableau T).idxOf (i, j) = n := by
      have hraw := nodup_idxOf_get (cellsOfTableau_nodup hbij) baseIdx
      rw [← hcsn]
      exact hraw
    have hidx_T : (cellsOfTableau T).idxOf (i, j) = T (i, j) - 1 := by
      exact cellsOfTableau_idxOf (T := T) hbij (p := (i, j)) hprect_pair
    have hn_eq : n = T (i, j) - 1 := by omega
    have hwget : w.get wordIdx = stepOfRow i := by
      change (rowWordOfCells (cellsOfTableau T)).get
          ⟨n, by simpa [rowWordOfCells] using hnright⟩ = stepOfRow i
      have hraw := rowWordOfCells_get (cellsOfTableau T) ⟨n, hnright⟩
      have hcell_pair : (cellsOfTableau T).get ⟨n, hnright⟩ = (i, j) := hcsn
      rw [hraw, hcell_pair]
    have hcount : (w.take n).count (stepOfRow i) = j - 1 := by
      rw [hn_eq]
      rw [show w.take (T (i, j) - 1) =
          rowWordOfCells ((cellsOfTableau T).take (T (i, j) - 1)) by
        simpa [w] using rowWord_take (cellsOfTableau T) (T (i, j) - 1)]
      exact rowWord_take_count_cellsOfTableau hbij hrow
        ⟨hbounds.1, hbounds.2.1⟩ ⟨hbounds.2.2.1, hbounds.2.2.2⟩
    rw [cellsOfWord_get w wordIdx, hwget, hcount]
    have hi_cases : i = 1 ∨ i = 2 ∨ i = 3 := by omega
    have hjpos : 0 < j := by omega
    change (rowOfStep (stepOfRow i), j - 1 + 1) = cell
    rw [hcsn]
    simp [rowOfStep_stepOfRow hi_cases]
    omega

lemma cellsOfTableau_tableauOfCellList {cs : List (ℕ × ℕ)}
    (hmem : ∀ p : ℕ × ℕ, p ∈ cs ↔ p ∈ rectSet)
    (hlen : cs.length = 6072) (hnodup : cs.Nodup) :
    cellsOfTableau (tableauOfCellList cs) = cs := by
  let T := tableauOfCellList cs
  have hbijFin : Set.BijOn T rectSet (Finset.Icc 1 6072) := by
    simpa [T] using tableauOfCellList_bijOn (cs := cs) (s := rectSet) hmem hlen hnodup
  apply List.ext_getElem
  · simp [cellsOfTableau_length, hlen]
  · intro n hnleft hnright
    have hp : cs[n] ∈ cs := List.getElem_mem hnright
    have hprect : cs[n] ∈ rectSet := (hmem cs[n]).1 hp
    have hidx : cs.idxOf cs[n] = n := hnodup.idxOf_getElem n hnright
    have hT : T cs[n] = n + 1 := by
      simp [T, tableauOfCellList, hp, hidx]
    unfold cellsOfTableau
    rw [List.getElem_map]
    rw [List.getElem_range]
    rw [← hT]
    exact hbijFin.invOn_invFunOn.1.eq hprect

lemma cellsOfTableau_tableauOfBallotWord {l : List Step} (hl : l ∈ Ballot 0 0 2024) :
    cellsOfTableau (tableauOfBallotWord l) = cellsOfWord l.reverse := by
  let cs := cellsOfWord l.reverse
  have hmem : ∀ p : ℕ × ℕ, p ∈ cs ↔ p ∈ rectSet := by
    intro p
    rw [show p ∈ cs ↔
        p ∈ (Finset.Icc 1 3 ×ˢ Finset.Icc 1 2024 : Finset (ℕ × ℕ)) by
      simpa [cs] using Ballot_full_cells (l := l) hl p]
    exact (mem_rectSet_iff_finset p).symm
  have hlen : cs.length = 6072 := by
    have hlenl := Ballot_length (x := 0) (y := 0) (z := 2024) hl
    simp [cs, cellsOfWord_length, hlenl]
  have hnodup : cs.Nodup := by
    simpa [cs] using cellsOfWord_nodup l.reverse
  simpa [tableauOfBallotWord, cs] using
    cellsOfTableau_tableauOfCellList hmem hlen hnodup

lemma ballotWordOfTableau_tableauOfBallotWord {l : List Step} (hl : l ∈ Ballot 0 0 2024) :
    ballotWordOfTableau (tableauOfBallotWord l) = l := by
  unfold ballotWordOfTableau
  rw [cellsOfTableau_tableauOfBallotWord hl]
  rw [cellsOfWord_rowWord]
  simp

lemma tableauOfBallotWord_injOn :
    Set.InjOn tableauOfBallotWord (Ballot 0 0 2024) := by
  intro l hl m hm h
  have hballot := congrArg ballotWordOfTableau h
  rw [ballotWordOfTableau_tableauOfBallotWord hl,
    ballotWordOfTableau_tableauOfBallotWord hm] at hballot
  exact hballot

lemma tableauOfCellList_cellsOfTableau {T : ℕ × ℕ → ℕ}
    (hbij : Set.BijOn T rectSet valueSet)
    (hzero : ∀ x, x ∉ Finset.Icc 1 3 ×ˢ Finset.Icc 1 2024 → T x = 0) :
    tableauOfCellList (cellsOfTableau T) = T := by
  funext p
  by_cases hp : p ∈ rectSet
  · have hpmem : p ∈ cellsOfTableau T := (cellsOfTableau_mem hbij p).2 hp
    rw [tableauOfCellList_apply_mem hpmem]
    rw [cellsOfTableau_idxOf hbij hp]
    have hval := hbij.mapsTo hp
    have hbounds : 1 ≤ T p ∧ T p ≤ 6072 := by
      simpa [valueSet, Set.mem_Icc] using hval
    omega
  · have hpmem : p ∉ cellsOfTableau T := by
      intro h
      exact hp ((cellsOfTableau_mem hbij p).1 h)
    have hpfin : p ∉ Finset.Icc 1 3 ×ˢ Finset.Icc 1 2024 := by
      intro h
      exact hp ((mem_rectSet_iff_finset p).2 h)
    simp [tableauOfCellList, hpmem, hzero p hpfin]

lemma tableauOfBallotWord_ballotWordOfTableau {T : ℕ × ℕ → ℕ}
    (hbij : Set.BijOn T rectSet valueSet)
    (hrow : ∀ i ∈ Finset.Icc 1 3, StrictMonoOn (fun j => T (i, j)) (Set.Icc 1 2024))
    (hzero : ∀ x, x ∉ Finset.Icc 1 3 ×ˢ Finset.Icc 1 2024 → T x = 0) :
    tableauOfBallotWord (ballotWordOfTableau T) = T := by
  unfold tableauOfBallotWord ballotWordOfTableau
  rw [List.reverse_reverse]
  rw [cellsOfWord_rowWord_cellsOfTableau hbij hrow]
  exact tableauOfCellList_cellsOfTableau hbij hzero

def FullTableaux : Set (ℕ × ℕ → ℕ) :=
  {T | Set.BijOn T (Finset.Icc 1 3 ×ˢ Finset.Icc 1 2024) (Finset.Icc 1 6072) ∧
    (∀ j ∈ Finset.Icc 1 2024, StrictMonoOn (fun i => T (i, j)) (Set.Icc 1 3)) ∧
    (∀ i ∈ Finset.Icc 1 3, StrictMonoOn (fun j => T (i, j)) (Set.Icc 1 2024)) ∧
    (∀ x, x ∉ Finset.Icc 1 3 ×ˢ Finset.Icc 1 2024 → T x = 0)}

lemma bijOn_rect_value_of_finset {T : ℕ × ℕ → ℕ}
    (hbij : Set.BijOn T (Finset.Icc 1 3 ×ˢ Finset.Icc 1 2024) (Finset.Icc 1 6072)) :
    Set.BijOn T rectSet valueSet := by
  simpa [rectSet, valueSet, Set.mem_Icc, Prod.le_def, Finset.mem_product, Finset.mem_Icc]
    using hbij

lemma fullTableaux_ncard :
    FullTableaux.ncard = (Ballot 0 0 2024).ncard := by
  have himage : FullTableaux = tableauOfBallotWord '' Ballot 0 0 2024 := by
    ext T
    constructor
    · intro hT
      rcases hT with ⟨hbijFin, hcol, hrow, hzero⟩
      have hbij := bijOn_rect_value_of_finset hbijFin
      refine ⟨ballotWordOfTableau T, ballotWordOfTableau_mem hbij hcol, ?_⟩
      have hrecon : tableauOfBallotWord (ballotWordOfTableau T) = T :=
        tableauOfBallotWord_ballotWordOfTableau (T := T) hbij hrow hzero
      exact hrecon
    · rintro ⟨l, hl, rfl⟩
      simpa [FullTableaux] using tableauOfBallotWord_mem_full (l := l) hl
  rw [himage]
  exact Set.ncard_image_of_injOn tableauOfBallotWord_injOn

lemma cellsOfWordAux_append (a b c : ℕ) (l₁ l₂ : List Step) :
    cellsOfWordAux a b c (l₁ ++ l₂) =
      cellsOfWordAux a b c l₁ ++
        cellsOfWordAux (a + l₁.count A) (b + l₁.count B) (c + l₁.count C) l₂ := by
  induction l₁ generalizing a b c with
  | nil =>
      simp [cellsOfWordAux]
  | cons s t ih =>
      cases s <;> simp [cellsOfWordAux, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma cellsOfWord_append (l₁ l₂ : List Step) :
    cellsOfWord (l₁ ++ l₂) =
      cellsOfWord l₁ ++ cellsOfWordAux (l₁.count A) (l₁.count B) (l₁.count C) l₂ := by
  simpa [cellsOfWord] using cellsOfWordAux_append 0 0 0 l₁ l₂

lemma ballot_cons_CC_mem {u : List Step} :
    C :: C :: u ∈ Ballot 0 0 2024 ↔ u ∈ Ballot 0 2 2022 := by
  constructor
  · intro hl
    rcases hl with ⟨hg, hA, hB, hC⟩
    have hg1 : SuffixGood (C :: u) := (suffixGood_cons C (C :: u)).1 hg |>.1
    have hg2 : SuffixGood u := (suffixGood_cons C u).1 hg1 |>.1
    refine ⟨hg2, ?_, ?_, ?_⟩ <;> simp at hA hB hC ⊢ <;> omega
  · intro hu
    have h1 : C :: u ∈ Ballot 0 1 2023 := by
      exact Ballot_cons_C (x := 0) (y := 1) (z := 2023) (by norm_num) ⟨u, hu, rfl⟩
    exact Ballot_cons_C (x := 0) (y := 0) (z := 2024) (by norm_num) ⟨C :: u, h1, rfl⟩

lemma tableauOfBallotWord_CC_event {u : List Step} (hu : u ∈ Ballot 0 2 2022) :
    tableauOfBallotWord (C :: C :: u) (2, 2024) <
      tableauOfBallotWord (C :: C :: u) (3, 2023) := by
  let w := (C :: C :: u).reverse
  let pref := cellsOfWord u.reverse
  let cs := cellsOfWord w
  have hcounts : u.count A = 2024 ∧ u.count B = 2024 ∧ u.count C = 2022 := by
    rcases hu with ⟨_, hA, hB, hC⟩
    omega
  have hcountsR : u.reverse.count A = 2024 ∧
      u.reverse.count B = 2024 ∧ u.reverse.count C = 2022 := by
    simpa [List.count_reverse] using hcounts
  have hcs : cs = pref ++ [(3, 2023), (3, 2024)] := by
    simp [cs, pref, w, List.reverse_cons, cellsOfWord_append, hcountsR,
      cellsOfWordAux]
  have hmemBpref : (2, 2024) ∈ pref := by
    rw [mem_cellsOfWord_two]
    exact ⟨by norm_num, by simp [pref, hcountsR.2.1]⟩
  have hmemB : (2, 2024) ∈ cs := by
    rw [hcs]
    simp [hmemBpref]
  have hmemC : (3, 2023) ∈ cs := by
    rw [hcs]
    simp
  have hnotCpref : (3, 2023) ∉ pref := by
    intro hp
    have hc := (mem_cellsOfWord_three (l := u.reverse) (j := 2023)).1 (by simpa [pref] using hp)
    omega
  have hidxC : cs.idxOf (3, 2023) = pref.length := by
    rw [hcs, List.idxOf_append]
    simp [hnotCpref]
  have hidxB : cs.idxOf (2, 2024) < pref.length := by
    rw [hcs, List.idxOf_append_of_mem hmemBpref]
    exact List.idxOf_lt_length_of_mem hmemBpref
  have hidx : cs.idxOf (2, 2024) < cs.idxOf (3, 2023) := by
    rw [hidxC]
    exact hidxB
  have hT_B : tableauOfBallotWord (C :: C :: u) (2, 2024) = cs.idxOf (2, 2024) + 1 := by
    simpa [tableauOfBallotWord, cs, w] using tableauOfCellList_apply_mem (cs := cs) hmemB
  have hT_C : tableauOfBallotWord (C :: C :: u) (3, 2023) = cs.idxOf (3, 2023) + 1 := by
    simpa [tableauOfBallotWord, cs, w] using tableauOfCellList_apply_mem (cs := cs) hmemC
  omega

lemma ballot_event_imp_CC {l : List Step} (hl : l ∈ Ballot 0 0 2024)
    (he : tableauOfBallotWord l (2, 2024) < tableauOfBallotWord l (3, 2023)) :
    ∃ u, u ∈ Ballot 0 2 2022 ∧ l = C :: C :: u := by
  let w := l.reverse
  let cs := cellsOfWord w
  have hprefix : PrefixGood w := by
    simpa [w, prefixGood_reverse] using hl.1
  have hcounts : w.count A = 2024 ∧ w.count B = 2024 ∧ w.count C = 2024 := by
    rcases hl with ⟨_, hA, hB, hC⟩
    simpa [w, List.count_reverse] using And.intro hA (And.intro hB hC)
  have hmemB : (2, 2024) ∈ cs := by
    simpa [cs] using (mem_cellsOfWord_two (l := w) (j := 2024)).2
      ⟨by norm_num, by simp [hcounts.2.1]⟩
  have hmemC23 : (3, 2023) ∈ cs := by
    simpa [cs] using (mem_cellsOfWord_three (l := w) (j := 2023)).2
      ⟨by norm_num, by simp [hcounts.2.2]⟩
  have hmemC24 : (3, 2024) ∈ cs := by
    simpa [cs] using (mem_cellsOfWord_three (l := w) (j := 2024)).2
      ⟨by norm_num, by simp [hcounts.2.2]⟩
  have hidx : cs.idxOf (2, 2024) < cs.idxOf (3, 2023) := by
    have hBval : tableauOfBallotWord l (2, 2024) = cs.idxOf (2, 2024) + 1 := by
      simpa [tableauOfBallotWord, cs, w] using tableauOfCellList_apply_mem (cs := cs) hmemB
    have hCval : tableauOfBallotWord l (3, 2023) = cs.idxOf (3, 2023) + 1 := by
      simpa [tableauOfBallotWord, cs, w] using tableauOfCellList_apply_mem (cs := cs) hmemC23
    omega
  let n := cs.idxOf (3, 2023)
  have hncs : n < cs.length := List.idxOf_lt_length_of_mem hmemC23
  have hnw : n < w.length := by simpa [cs, cellsOfWord_length] using hncs
  have hCbefore : (w.take n).count C = 2022 := by
    have h := count_take_idxOf_cell (l := w) (s := C) (j := 2023) (by norm_num)
      (by simpa [cs, rowOfStep] using hmemC23)
    simpa [n, cs, rowOfStep] using h
  have hBtake : (2, 2024) ∈ cs.take n := by
    rw [List.mem_take_iff_idxOf_lt hmemB]
    exact hidx
  have hBbefore_ge : 2024 ≤ (w.take n).count B := by
    have hb := (mem_cellsOfWord_two (l := w.take n) (j := 2024)).1
      (by simpa [cs, cellsOfWord_take] using hBtake)
    exact hb.2
  have hBbefore : (w.take n).count B = 2024 := by
    have hle := List.Sublist.count_le B (List.take_sublist n w)
    omega
  have hgood := (hprefix (w.take n) (List.take_prefix _ _)).1
  have hAbefore : (w.take n).count A = 2024 := by
    have hle := List.Sublist.count_le A (List.take_sublist n w)
    omega
  have hlen_take : (w.take n).length = 6070 := by
    rw [length_eq_counts (w.take n), hAbefore, hBbefore, hCbefore]
  have hn_eq : n = 6070 := by
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hnw)] at hlen_take
    omega
  have hidxC23 : cs.idxOf (3, 2023) = 6070 := by simpa [n] using hn_eq
  have hidxC24_gt : cs.idxOf (3, 2023) < cs.idxOf (3, 2024) := by
    simpa [cs, rowOfStep] using
      cellsOfWord_idx_same_row_lt (l := w) (s := C) (j₁ := 2023) (j₂ := 2024)
        (by norm_num) (by norm_num) (by simpa [cs, rowOfStep] using hmemC24)
  have hidxC24 : cs.idxOf (3, 2024) = 6071 := by
    have hlt := List.idxOf_lt_length_of_mem hmemC24
    have hlenw := Ballot_length (x := 0) (y := 0) (z := 2024) hl
    have hlt' : cs.idxOf (3, 2024) < 6072 := by
      simpa [cs, cellsOfWord_length, w, List.length_reverse, hlenw] using hlt
    omega
  have hgetC23 : w.get ⟨6070, by
      have hlenw := Ballot_length (x := 0) (y := 0) (z := 2024) hl
      simp [w, hlenw]⟩ = C := by
    have hopt := getElem?_idxOf_cell_eq_step (l := w) (s := C) (j := 2023)
      (by norm_num) (by simpa [cs, rowOfStep] using hmemC23)
    simp [cs, hidxC23, rowOfStep] at hopt
    have hsome := List.getElem?_eq_getElem (l := w) (i := 6070)
      (by
        have hlenw := Ballot_length (x := 0) (y := 0) (z := 2024) hl
        simp [w, hlenw])
    rw [hsome] at hopt
    exact Option.some.inj hopt
  have hgetC24 : w.get ⟨6071, by
      have hlenw := Ballot_length (x := 0) (y := 0) (z := 2024) hl
      simp [w, hlenw]⟩ = C := by
    have hopt := getElem?_idxOf_cell_eq_step (l := w) (s := C) (j := 2024)
      (by norm_num) (by simpa [cs, rowOfStep] using hmemC24)
    simp [cs, hidxC24, rowOfStep] at hopt
    have hsome := List.getElem?_eq_getElem (l := w) (i := 6071)
      (by
        have hlenw := Ballot_length (x := 0) (y := 0) (z := 2024) hl
        simp [w, hlenw])
    rw [hsome] at hopt
    exact Option.some.inj hopt
  let u := (w.take 6070).reverse
  have hw_decomp : w = w.take 6070 ++ [C, C] := by
    have hlenw := Ballot_length (x := 0) (y := 0) (z := 2024) hl
    have h6070 : 6070 < w.length := by simp [w, hlenw]
    have h6071 : 6071 < w.length := by simp [w, hlenw]
    have hgetE23 : w[6070]'h6070 = C := by
      simpa [List.get_eq_getElem] using hgetC23
    have hgetE24 : w[6071]'h6071 = C := by
      simpa [List.get_eq_getElem] using hgetC24
    calc
      w = w.take 6072 := by simp [w, hlenw]
      _ = w.take 6071 ++ [w[6071]'h6071] := by
        rw [← List.take_concat_get' w 6071 h6071]
      _ = (w.take 6070 ++ [w[6070]'h6070]) ++ [w[6071]'h6071] := by
        rw [← List.take_concat_get' w 6070 h6070]
      _ = w.take 6070 ++ [C, C] := by
        simp [hgetE23, hgetE24]
  have hl_eq : l = C :: C :: u := by
    have := congrArg List.reverse hw_decomp
    simpa [u, w] using this
  refine ⟨u, ?_, hl_eq⟩
  exact (ballot_cons_CC_mem).1 (by simpa [hl_eq] using hl)

def EventTableaux : Set (ℕ × ℕ → ℕ) :=
  {T | T ∈ FullTableaux ∧ T (2, 2024) < T (3, 2023)}

lemma eventTableaux_ncard :
    EventTableaux.ncard = (Ballot 0 2 2022).ncard := by
  let f : List Step → (ℕ × ℕ → ℕ) := fun u => tableauOfBallotWord (C :: C :: u)
  have hf : Set.InjOn f (Ballot 0 2 2022) := by
    intro u hu v hv h
    have hufull : C :: C :: u ∈ Ballot 0 0 2024 := (ballot_cons_CC_mem).2 hu
    have hvfull : C :: C :: v ∈ Ballot 0 0 2024 := (ballot_cons_CC_mem).2 hv
    have hwords := tableauOfBallotWord_injOn hufull hvfull h
    exact (List.cons.inj ((List.cons.inj hwords).2)).2
  have himage : EventTableaux = f '' Ballot 0 2 2022 := by
    ext T
    constructor
    · rintro ⟨hT, he⟩
      rcases hT with ⟨hbijFin, hcol, hrow, hzero⟩
      have hbij := bijOn_rect_value_of_finset hbijFin
      let l := ballotWordOfTableau T
      have hl : l ∈ Ballot 0 0 2024 := ballotWordOfTableau_mem hbij hcol
      have hrecon : tableauOfBallotWord l = T :=
        tableauOfBallotWord_ballotWordOfTableau (T := T) hbij hrow hzero
      have he' : tableauOfBallotWord l (2, 2024) <
          tableauOfBallotWord l (3, 2023) := by simpa [hrecon] using he
      rcases ballot_event_imp_CC hl he' with ⟨u, hu, hlu⟩
      refine ⟨u, hu, ?_⟩
      simp [f, ← hlu, hrecon]
    · rintro ⟨u, hu, rfl⟩
      have hfull : C :: C :: u ∈ Ballot 0 0 2024 := (ballot_cons_CC_mem).2 hu
      refine ⟨?_, tableauOfBallotWord_CC_event hu⟩
      simpa [FullTableaux] using tableauOfBallotWord_mem_full (l := C :: C :: u) hfull
  rw [himage]
  exact Set.ncard_image_of_injOn hf

end Putnam2024A3

--True
/--
Let $S$ be the set of bijections $$T : \{1, 2, 3\} \times \{1, 2, ..., 2024\} \to \{1, 2, ..., 6072\}$$
such that $T(1, j) < T(2, j) < T(3, j)$ for all $j \in \{1, 2, ..., 2024\}$ and
$T(i, j) < T(i, j + 1)$ for all $i \in \{1, 2, 3\}$ and $j \in \{1, 2, ..., 2023\}$.
Do there exist $a, c$ in $\{1, 2, 3\}$ and $b$ and $d$ in $\{1, 2, ..., 2024\}$ such that
the fraction of elements $T$ in $S$ for which $T(a, b) < T(c, d)$ is at least $1/3$ and at most $2/3$?
-/
theorem putnam_2024_a3
    (S : Set (ℕ × ℕ → ℕ))
    (hS : S = {T | Set.BijOn T (Finset.Icc 1 3 ×ˢ Finset.Icc 1 2024) (Finset.Icc 1 6072) ∧
      (∀ j ∈ Finset.Icc 1 2024, StrictMonoOn (fun i => T (i, j)) (Set.Icc 1 3)) ∧
      (∀ i ∈ Finset.Icc 1 3, StrictMonoOn (fun j => T (i, j)) (Set.Icc 1 2024)) ∧
      (∀ x, x ∉ Finset.Icc 1 3 ×ˢ Finset.Icc 1 2024 → T x = 0)}) :
    (∃ a ∈ Finset.Icc 1 3, ∃ b ∈ Finset.Icc 1 2024, ∃ c ∈ Finset.Icc 1 3, ∃ d ∈ Finset.Icc 1 2024,
      ({T | T ∈ S ∧ T (a, b) < T (c, d)}.ncard  / S.ncard : ℚ) ∈ Set.Icc (1/3) (2/3))
    ↔ ((True) : Prop ) := by
  constructor
  · intro _
    trivial
  · intro _
    refine ⟨2, by norm_num, 2024, by norm_num, 3, by norm_num, 2023, by norm_num, ?_⟩
    have hSfull : S = Putnam2024A3.FullTableaux := by
      simpa [Putnam2024A3.FullTableaux] using hS
    have hEvent :
        {T | T ∈ S ∧ T (2, 2024) < T (3, 2023)} = Putnam2024A3.EventTableaux := by
      ext T
      simp [Putnam2024A3.EventTableaux, hSfull]
    have hnum :
        ({T | T ∈ S ∧ T (2, 2024) < T (3, 2023)} : Set (ℕ × ℕ → ℕ)).ncard =
          (Putnam2024A3.Ballot 0 2 2022).ncard := by
      rw [hEvent, Putnam2024A3.eventTableaux_ncard]
    have hden : S.ncard = (Putnam2024A3.Ballot 0 0 2024).ncard := by
      rw [hSfull, Putnam2024A3.fullTableaux_ncard]
    rw [hnum, hden, Putnam2024A3.ballot_target_ratio]
    exact Putnam2024A3.ballot_target_ratio_mem_Icc
