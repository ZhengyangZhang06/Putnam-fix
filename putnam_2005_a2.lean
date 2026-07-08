import Mathlib

open Nat Set

abbrev putnam_2005_a2_solution : ℕ → ℕ := fun n ↦
  if n = 1 then 0 else 2 ^ (n - 2)

private def putnam_2005_a2_board (n : ℕ) : Set (ℤ × ℤ) :=
  prod (Icc (1 : ℤ) (n : ℤ)) (Icc (1 : ℤ) 3)

private def putnam_2005_a2_unit (P Q : ℤ × ℤ) : Prop :=
  P.1 = Q.1 ∧ |Q.2 - P.2| = 1 ∨ P.2 = Q.2 ∧ |Q.1 - P.1| = 1

private lemma putnam_2005_a2_unit_symm (P Q : ℤ × ℤ) :
    putnam_2005_a2_unit P Q ↔ putnam_2005_a2_unit Q P := by
  rcases P with ⟨a, b⟩
  rcases Q with ⟨c, d⟩
  unfold putnam_2005_a2_unit
  simp [eq_comm, abs_sub_comm, or_comm]

private def putnam_2005_a2_rooktour (n : ℕ) : (ℕ → ℤ × ℤ) → Prop := fun p ↦
  (∀ P ∈ putnam_2005_a2_board n, ∃! i, i ∈ Icc 1 (3 * n) ∧ p i = P) ∧
    (∀ i ∈ Icc 1 (3 * n - 1), putnam_2005_a2_unit (p i) (p (i + 1))) ∧
    p 0 = 0 ∧ ∀ i > 3 * n, p i = 0

private def putnam_2005_a2_tourSet (n : ℕ) : Set (ℕ → ℤ × ℤ) :=
  {p | putnam_2005_a2_rooktour n p ∧ p 1 = (1, 1) ∧ p (3 * n) = ((n : ℤ), 1)}

private def putnam_2005_a2_allowed (n : ℕ) : Set (ℤ × ℤ) :=
  {P | P = 0 ∨ P ∈ putnam_2005_a2_board n}

private lemma putnam_2005_a2_mem_of_unique_all
    {α : Type} {A : Set α} {m : ℕ} (p : ℕ → α)
    [Fintype A] [Fintype {i : ℕ // i ∈ Icc 1 m}]
    (hcard : Fintype.card A = Fintype.card {i : ℕ // i ∈ Icc 1 m})
    (huniq : ∀ P ∈ A, ∃! i, i ∈ Icc 1 m ∧ p i = P)
    {i : ℕ} (hi : i ∈ Icc 1 m) : p i ∈ A := by
  classical
  let idx : A → {i : ℕ // i ∈ Icc 1 m} := fun P ↦
    ⟨Classical.choose (huniq P.1 P.2), (Classical.choose_spec (huniq P.1 P.2)).1.1⟩
  have hidx_val : ∀ P : A, p (idx P).1 = P.1 := by
    intro P
    exact (Classical.choose_spec (huniq P.1 P.2)).1.2
  have hinj : Function.Injective idx := by
    intro P Q hPQ
    apply Subtype.ext
    calc
      P.1 = p (idx P).1 := (hidx_val P).symm
      _ = p (idx Q).1 := by rw [hPQ]
      _ = Q.1 := hidx_val Q
  have hbij : Function.Bijective idx :=
    (Fintype.bijective_iff_injective_and_card idx).2 ⟨hinj, hcard⟩
  obtain ⟨P, hP⟩ := hbij.2 ⟨i, hi⟩
  have : p i = P.1 := by
    calc
      p i = p (idx P).1 := by rw [hP]
      _ = P.1 := hidx_val P
  exact this.symm ▸ P.2

private lemma putnam_2005_a2_slot_mem_board
    (n : ℕ) (p : ℕ → ℤ × ℤ)
    (huniq : ∀ P ∈ putnam_2005_a2_board n,
      ∃! i, i ∈ Icc 1 (3 * n) ∧ p i = P)
    {i : ℕ} (hi : i ∈ Icc 1 (3 * n)) : p i ∈ putnam_2005_a2_board n := by
  classical
  haveI : Fintype (↑(Icc (1 : ℤ) (n : ℤ)) : Type) :=
    (Set.finite_Icc (1 : ℤ) (n : ℤ)).fintype
  haveI : Fintype (↑(Icc (1 : ℤ) 3) : Type) :=
    (Set.finite_Icc (1 : ℤ) 3).fintype
  haveI : Fintype
      (↑((Icc (1 : ℤ) (n : ℤ)).prod (Icc (1 : ℤ) 3)) : Type) :=
    ((Set.finite_Icc (1 : ℤ) (n : ℤ)).prod (Set.finite_Icc (1 : ℤ) 3)).fintype
  haveI : Fintype (putnam_2005_a2_board n) :=
    ((Set.finite_Icc (1 : ℤ) (n : ℤ)).prod (Set.finite_Icc (1 : ℤ) 3)).fintype
  haveI : Fintype ({i : ℕ // i ∈ Icc 1 (3 * n)} : Type) :=
    (Set.finite_Icc (1 : ℕ) (3 * n)).fintype
  have hA : Fintype.card (↑(Icc (1 : ℤ) (n : ℤ)) : Type) = n := by
    rw [Fintype.card_Icc, Int.card_Icc]
    simp
  have hB : Fintype.card (↑(Icc (1 : ℤ) 3) : Type) = 3 := by
    rw [Fintype.card_Icc, Int.card_Icc]
    simp
  have hcardBoard : Fintype.card (putnam_2005_a2_board n) = 3 * n := by
    calc
      Fintype.card (putnam_2005_a2_board n) =
          Fintype.card
            (↑((Icc (1 : ℤ) (n : ℤ)).prod (Icc (1 : ℤ) 3)) : Type) :=
        Fintype.card_congr
          (Equiv.setCongr
            (by rfl :
              putnam_2005_a2_board n =
                (Icc (1 : ℤ) (n : ℤ)).prod (Icc (1 : ℤ) 3)))
      _ =
          Fintype.card
            ((↑(Icc (1 : ℤ) (n : ℤ)) : Type) × (↑(Icc (1 : ℤ) 3) : Type)) :=
        Fintype.card_congr
          (Equiv.Set.prod (Icc (1 : ℤ) (n : ℤ)) (Icc (1 : ℤ) 3))
      _ =
          Fintype.card (↑(Icc (1 : ℤ) (n : ℤ)) : Type) *
            Fintype.card (↑(Icc (1 : ℤ) 3) : Type) := Fintype.card_prod _ _
      _ = n * 3 := by rw [hA, hB]
      _ = 3 * n := by omega
  have hcardIndex :
      Fintype.card ({i : ℕ // i ∈ Icc 1 (3 * n)} : Type) = 3 * n := by
    rw [Fintype.card_Icc, Nat.card_Icc]
    omega
  exact putnam_2005_a2_mem_of_unique_all p (by omega) huniq hi

private lemma putnam_2005_a2_board_finite (n : ℕ) :
    (putnam_2005_a2_board n).Finite := by
  unfold putnam_2005_a2_board
  exact (Set.finite_Icc (1 : ℤ) (n : ℤ)).prod (Set.finite_Icc (1 : ℤ) 3)

private lemma putnam_2005_a2_allowed_finite (n : ℕ) :
    (putnam_2005_a2_allowed n).Finite := by
  have h : ({0} : Set (ℤ × ℤ)).Finite := Set.finite_singleton 0
  simpa [putnam_2005_a2_allowed, Set.union_def, or_comm, eq_comm] using
    h.union (putnam_2005_a2_board_finite n)

private lemma putnam_2005_a2_tour_mem_allowed
    (n : ℕ) {p : ℕ → ℤ × ℤ} (hp : p ∈ putnam_2005_a2_tourSet n)
    (j : Fin (3 * n + 1)) : p j.1 ∈ putnam_2005_a2_allowed n := by
  rcases hp with ⟨⟨huniq, _hadj, hp0, _hafter⟩, _hstart, _hend⟩
  have hjle : j.1 ≤ 3 * n := Nat.lt_succ_iff.mp j.2
  by_cases h0 : j.1 = 0
  · left
    rw [h0, hp0]
  · right
    exact putnam_2005_a2_slot_mem_board n p huniq (by constructor <;> omega)

private lemma putnam_2005_a2_tourSet_finite (n : ℕ) :
    (putnam_2005_a2_tourSet n).Finite := by
  classical
  haveI : Fintype (putnam_2005_a2_allowed n) :=
    (putnam_2005_a2_allowed_finite n).fintype
  let encode : putnam_2005_a2_tourSet n →
      (Fin (3 * n + 1) → putnam_2005_a2_allowed n) := fun q j ↦
    ⟨q.1 j.1, putnam_2005_a2_tour_mem_allowed n q.2 j⟩
  have hencode : Function.Injective encode := by
    intro q r hqr
    apply Subtype.ext
    funext i
    by_cases hi : i ≤ 3 * n
    · have hlt : i < 3 * n + 1 := by omega
      exact congrArg Subtype.val (congrFun hqr ⟨i, hlt⟩)
    · have hgt : i > 3 * n := by omega
      rcases q.2 with ⟨⟨_, _, _, hqafter⟩, _, _⟩
      rcases r.2 with ⟨⟨_, _, _, hrafter⟩, _, _⟩
      rw [hqafter i hgt, hrafter i hgt]
  haveI : Finite (Fin (3 * n + 1) → putnam_2005_a2_allowed n) := inferInstance
  haveI : Finite (putnam_2005_a2_tourSet n) := Finite.of_injective encode hencode
  exact Set.toFinite (putnam_2005_a2_tourSet n)

private lemma putnam_2005_a2_tourSet_one_eq_empty :
    putnam_2005_a2_tourSet 1 = ∅ := by
  ext p
  constructor
  · intro hp
    rcases hp with ⟨⟨huniq, _hadj, _hp0, _hafter⟩, hstart, hend⟩
    have hP : ((1 : ℤ), (1 : ℤ)) ∈ putnam_2005_a2_board 1 := by
      change ((1 : ℤ), (1 : ℤ)) ∈
        (Icc (1 : ℤ) (1 : ℤ)).prod (Icc (1 : ℤ) 3)
      exact ⟨by simp, by simp⟩
    rcases huniq ((1 : ℤ), (1 : ℤ)) hP with ⟨i, _hi, huniq_i⟩
    have hslot1 : 1 ∈ Icc 1 (3 * 1) ∧ p 1 = ((1 : ℤ), (1 : ℤ)) := by
      constructor
      · simp
      · simpa using hstart
    have hslot3 : 3 ∈ Icc 1 (3 * 1) ∧ p 3 = ((1 : ℤ), (1 : ℤ)) := by
      constructor
      · simp
      · simpa using hend
    have h1 : (1 : ℕ) = i := huniq_i 1 hslot1
    have h3 : (3 : ℕ) = i := huniq_i 3 hslot3
    omega
  · intro hp
    simp at hp

private abbrev putnam_2005_a2_Point := ℤ × ℤ

private def putnam_2005_a2_side (top : Bool) : ℤ :=
  if top then 3 else 1

private def putnam_2005_a2_mid : ℤ := 2

private def putnam_2005_a2_pt (a : ℤ) (b : ℤ) : putnam_2005_a2_Point :=
  (a, b)

private lemma putnam_2005_a2_neighbor_bottom_left {n : ℕ}
    {P : putnam_2005_a2_Point} (hP : P ∈ putnam_2005_a2_board n)
    (hunit : putnam_2005_a2_unit (putnam_2005_a2_pt 1 1) P) :
    P = putnam_2005_a2_pt 2 1 ∨ P = putnam_2005_a2_pt 1 2 := by
  rcases P with ⟨x, y⟩
  unfold putnam_2005_a2_board at hP
  change x ∈ Icc (1 : ℤ) (n : ℤ) ∧ y ∈ Icc (1 : ℤ) 3 at hP
  simp [putnam_2005_a2_unit, putnam_2005_a2_pt,
    abs_eq (by norm_num : (0 : ℤ) ≤ 1)] at hP hunit ⊢
  omega

private lemma putnam_2005_a2_neighbor_top_left {n : ℕ}
    {P : putnam_2005_a2_Point} (hP : P ∈ putnam_2005_a2_board n)
    (hunit : putnam_2005_a2_unit (putnam_2005_a2_pt 1 3) P) :
    P = putnam_2005_a2_pt 2 3 ∨ P = putnam_2005_a2_pt 1 2 := by
  rcases P with ⟨x, y⟩
  unfold putnam_2005_a2_board at hP
  change x ∈ Icc (1 : ℤ) (n : ℤ) ∧ y ∈ Icc (1 : ℤ) 3 at hP
  simp [putnam_2005_a2_unit, putnam_2005_a2_pt,
    abs_eq (by norm_num : (0 : ℤ) ≤ 1)] at hP hunit ⊢
  omega

private lemma putnam_2005_a2_neighbor_left_middle {n : ℕ}
    {P : putnam_2005_a2_Point} (hP : P ∈ putnam_2005_a2_board n)
    (hunit : putnam_2005_a2_unit (putnam_2005_a2_pt 1 2) P) :
    P = putnam_2005_a2_pt 1 1 ∨
      P = putnam_2005_a2_pt 1 3 ∨
      P = putnam_2005_a2_pt 2 2 := by
  rcases P with ⟨x, y⟩
  unfold putnam_2005_a2_board at hP
  change x ∈ Icc (1 : ℤ) (n : ℤ) ∧ y ∈ Icc (1 : ℤ) 3 at hP
  simp [putnam_2005_a2_unit, putnam_2005_a2_pt,
    abs_eq (by norm_num : (0 : ℤ) ≤ 1)] at hP hunit ⊢
  omega

private lemma putnam_2005_a2_neighbor_left_top {n : ℕ}
    {P : putnam_2005_a2_Point} (hP : P ∈ putnam_2005_a2_board n)
    (hunit : putnam_2005_a2_unit (putnam_2005_a2_pt 1 3) P) :
    P = putnam_2005_a2_pt 1 2 ∨ P = putnam_2005_a2_pt 2 3 := by
  have h := putnam_2005_a2_neighbor_top_left hP hunit
  tauto

private lemma putnam_2005_a2_neighbor_right_bottom {n : ℕ}
    {P : putnam_2005_a2_Point} (hP : P ∈ putnam_2005_a2_board (n + 1))
    (hunit : putnam_2005_a2_unit (putnam_2005_a2_pt ((n : ℤ) + 1) 1) P) :
    P = putnam_2005_a2_pt (n : ℤ) 1 ∨
      P = putnam_2005_a2_pt ((n : ℤ) + 1) 2 := by
  rcases P with ⟨x, y⟩
  unfold putnam_2005_a2_board at hP
  change x ∈ Icc (1 : ℤ) ((n + 1 : ℕ) : ℤ) ∧ y ∈ Icc (1 : ℤ) 3 at hP
  simp [putnam_2005_a2_unit, putnam_2005_a2_pt,
    abs_eq (by norm_num : (0 : ℤ) ≤ 1)] at hP hunit ⊢
  omega

private lemma putnam_2005_a2_neighbor_right_top {n : ℕ}
    {P : putnam_2005_a2_Point} (hP : P ∈ putnam_2005_a2_board (n + 1))
    (hunit : putnam_2005_a2_unit (putnam_2005_a2_pt ((n : ℤ) + 1) 3) P) :
    P = putnam_2005_a2_pt (n : ℤ) 3 ∨
      P = putnam_2005_a2_pt ((n : ℤ) + 1) 2 := by
  rcases P with ⟨x, y⟩
  unfold putnam_2005_a2_board at hP
  change x ∈ Icc (1 : ℤ) ((n + 1 : ℕ) : ℤ) ∧ y ∈ Icc (1 : ℤ) 3 at hP
  simp [putnam_2005_a2_unit, putnam_2005_a2_pt,
    abs_eq (by norm_num : (0 : ℤ) ≤ 1)] at hP hunit ⊢
  omega

private lemma putnam_2005_a2_neighbor_right_middle {n : ℕ}
    {P : putnam_2005_a2_Point} (hP : P ∈ putnam_2005_a2_board (n + 1))
    (hunit : putnam_2005_a2_unit (putnam_2005_a2_pt ((n : ℤ) + 1) 2) P) :
    P = putnam_2005_a2_pt ((n : ℤ) + 1) 1 ∨
      P = putnam_2005_a2_pt ((n : ℤ) + 1) 3 ∨
      P = putnam_2005_a2_pt (n : ℤ) 2 := by
  rcases P with ⟨x, y⟩
  unfold putnam_2005_a2_board at hP
  change x ∈ Icc (1 : ℤ) ((n + 1 : ℕ) : ℤ) ∧ y ∈ Icc (1 : ℤ) 3 at hP
  simp [putnam_2005_a2_unit, putnam_2005_a2_pt,
    abs_eq (by norm_num : (0 : ℤ) ≤ 1)] at hP hunit ⊢
  omega

private def putnam_2005_a2_shiftLeft (P : putnam_2005_a2_Point) :
    putnam_2005_a2_Point :=
  (P.1 - 1, P.2)

private def putnam_2005_a2_shiftRight (P : putnam_2005_a2_Point) :
    putnam_2005_a2_Point :=
  (P.1 + 1, P.2)

private lemma putnam_2005_a2_shiftLeft_right (P : putnam_2005_a2_Point) :
    putnam_2005_a2_shiftLeft (putnam_2005_a2_shiftRight P) = P := by
  rcases P with ⟨x, y⟩
  simp [putnam_2005_a2_shiftLeft, putnam_2005_a2_shiftRight]

private lemma putnam_2005_a2_shiftRight_left (P : putnam_2005_a2_Point) :
    putnam_2005_a2_shiftRight (putnam_2005_a2_shiftLeft P) = P := by
  rcases P with ⟨x, y⟩
  simp [putnam_2005_a2_shiftLeft, putnam_2005_a2_shiftRight]

private lemma putnam_2005_a2_shiftRight_injective :
    Function.Injective putnam_2005_a2_shiftRight := by
  intro P Q h
  calc
    P = putnam_2005_a2_shiftLeft (putnam_2005_a2_shiftRight P) :=
      (putnam_2005_a2_shiftLeft_right P).symm
    _ = putnam_2005_a2_shiftLeft (putnam_2005_a2_shiftRight Q) := by rw [h]
    _ = Q := putnam_2005_a2_shiftLeft_right Q

private lemma putnam_2005_a2_shiftLeft_injective :
    Function.Injective putnam_2005_a2_shiftLeft := by
  intro P Q h
  calc
    P = putnam_2005_a2_shiftRight (putnam_2005_a2_shiftLeft P) :=
      (putnam_2005_a2_shiftRight_left P).symm
    _ = putnam_2005_a2_shiftRight (putnam_2005_a2_shiftLeft Q) := by rw [h]
    _ = Q := putnam_2005_a2_shiftRight_left Q

private lemma putnam_2005_a2_unit_shiftRight (P Q : putnam_2005_a2_Point) :
    putnam_2005_a2_unit (putnam_2005_a2_shiftRight P)
        (putnam_2005_a2_shiftRight Q) ↔
      putnam_2005_a2_unit P Q := by
  rcases P with ⟨a, b⟩
  rcases Q with ⟨c, d⟩
  simp [putnam_2005_a2_shiftRight, putnam_2005_a2_unit]

private lemma putnam_2005_a2_unit_shiftLeft (P Q : putnam_2005_a2_Point) :
    putnam_2005_a2_unit (putnam_2005_a2_shiftLeft P)
        (putnam_2005_a2_shiftLeft Q) ↔
      putnam_2005_a2_unit P Q := by
  rcases P with ⟨a, b⟩
  rcases Q with ⟨c, d⟩
  simp [putnam_2005_a2_shiftLeft, putnam_2005_a2_unit]

private def putnam_2005_a2_boardList (n : ℕ) : List putnam_2005_a2_Point :=
  (List.range n).flatMap fun k ↦
    [((k : ℤ) + 1, (1 : ℤ)), ((k : ℤ) + 1, (2 : ℤ)), ((k : ℤ) + 1, (3 : ℤ))]

private lemma putnam_2005_a2_boardList_mem_iff (n : ℕ)
    (P : putnam_2005_a2_Point) :
    P ∈ putnam_2005_a2_boardList n ↔ P ∈ putnam_2005_a2_board n := by
  rcases P with ⟨x, y⟩
  unfold putnam_2005_a2_boardList putnam_2005_a2_board
  simp
  change
    (∃ a < n,
        x = (a : ℤ) + 1 ∧ y = 1 ∨
          x = (a : ℤ) + 1 ∧ y = 2 ∨
          x = (a : ℤ) + 1 ∧ y = 3) ↔
      x ∈ Icc (1 : ℤ) (n : ℤ) ∧ y ∈ Icc (1 : ℤ) 3
  simp only [mem_Icc]
  constructor
  · rintro ⟨k, hk, h⟩
    rcases h with h | h | h <;> rcases h with ⟨rfl, rfl⟩ <;> omega
  · rintro ⟨hx, hy⟩
    have hxnat : 0 ≤ x - 1 := by omega
    let k : ℕ := Int.toNat (x - 1)
    have hkx : (k : ℤ) = x - 1 := by
      dsimp [k]
      rw [Int.toNat_of_nonneg hxnat]
    have hklt : k < n := by
      have : (k : ℤ) < (n : ℤ) := by omega
      exact_mod_cast this
    refine ⟨k, hklt, ?_⟩
    have hx' : (k : ℤ) + 1 = x := by omega
    rcases hy with ⟨hy1, hy3⟩
    interval_cases y <;> simp [hx']

private lemma putnam_2005_a2_boardList_length (n : ℕ) :
    (putnam_2005_a2_boardList n).length = 3 * n := by
  unfold putnam_2005_a2_boardList
  simp
  omega

private def putnam_2005_a2_listTour (n : ℕ) (top : Bool)
    (l : List putnam_2005_a2_Point) : Prop :=
  l.Perm (putnam_2005_a2_boardList n) ∧
    l.IsChain putnam_2005_a2_unit ∧
    l.head? = some (putnam_2005_a2_pt 1 (putnam_2005_a2_side top)) ∧
    l.getLast? = some (putnam_2005_a2_pt (n : ℤ) 1)

private def putnam_2005_a2_listTourSet (n : ℕ) (top : Bool) :
    Set (List putnam_2005_a2_Point) :=
  {l | putnam_2005_a2_listTour n top l}

private def putnam_2005_a2_cornerListTour (n : ℕ) (startTop endTop : Bool)
    (l : List putnam_2005_a2_Point) : Prop :=
  l.Perm (putnam_2005_a2_boardList n) ∧
    l.IsChain putnam_2005_a2_unit ∧
    l.head? = some (putnam_2005_a2_pt 1 (putnam_2005_a2_side startTop)) ∧
    l.getLast? = some (putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side endTop))

private def putnam_2005_a2_cornerListTourSet
    (n : ℕ) (startTop endTop : Bool) : Set (List putnam_2005_a2_Point) :=
  {l | putnam_2005_a2_cornerListTour n startTop endTop l}

private lemma putnam_2005_a2_cornerListTourSet_finite
    (n : ℕ) (startTop endTop : Bool) :
    (putnam_2005_a2_cornerListTourSet n startTop endTop).Finite := by
  classical
  refine (Set.finite_mem_finset (putnam_2005_a2_boardList n).permutations.toFinset).subset ?_
  intro l hl
  have hperm : l.Perm (putnam_2005_a2_boardList n) := hl.1
  simpa [List.mem_toFinset, List.mem_permutations] using hperm

private lemma putnam_2005_a2_listTour_iff_corner_bottom {n : ℕ}
    {l : List putnam_2005_a2_Point} :
    putnam_2005_a2_listTour n false l ↔
      putnam_2005_a2_cornerListTour n false false l := by
  rfl

private lemma putnam_2005_a2_boardList_succ (n : ℕ) :
    putnam_2005_a2_boardList (n + 1) =
      putnam_2005_a2_boardList n ++
        [putnam_2005_a2_pt ((n : ℤ) + 1) 1,
          putnam_2005_a2_pt ((n : ℤ) + 1) 2,
          putnam_2005_a2_pt ((n : ℤ) + 1) 3] := by
  let f : ℤ → List putnam_2005_a2_Point := fun k ↦
    [(k + 1, (1 : ℤ)), (k + 1, (2 : ℤ)), (k + 1, (3 : ℤ))]
  unfold putnam_2005_a2_boardList
  change (((List.range (n + 1)).flatMap fun k : ℕ ↦ [((k : ℤ))]).flatMap f) =
    (((List.range n).flatMap fun k : ℕ ↦ [((k : ℤ))]).flatMap f) ++
      [putnam_2005_a2_pt ((n : ℤ) + 1) 1,
        putnam_2005_a2_pt ((n : ℤ) + 1) 2,
        putnam_2005_a2_pt ((n : ℤ) + 1) 3]
  rw [show n + 1 = n.succ by omega, List.range_succ, List.flatMap_append,
    List.flatMap_append]
  rfl

private def putnam_2005_a2_edgeIn (P Q : putnam_2005_a2_Point)
    (l : List putnam_2005_a2_Point) : Prop :=
  [P, Q] <:+: l ∨ [Q, P] <:+: l

private lemma putnam_2005_a2_edgeIn_symm
    (P Q : putnam_2005_a2_Point) (l : List putnam_2005_a2_Point) :
    putnam_2005_a2_edgeIn P Q l ↔ putnam_2005_a2_edgeIn Q P l := by
  unfold putnam_2005_a2_edgeIn
  tauto

private lemma putnam_2005_a2_edgeIn_left_mem
    {P Q : putnam_2005_a2_Point} {l : List putnam_2005_a2_Point}
    (h : putnam_2005_a2_edgeIn P Q l) : P ∈ l := by
  rcases h with ⟨s, t, hst⟩ | ⟨s, t, hst⟩
  · rw [← hst]
    simp
  · rw [← hst]
    simp

private lemma putnam_2005_a2_edgeIn_right_mem
    {P Q : putnam_2005_a2_Point} {l : List putnam_2005_a2_Point}
    (h : putnam_2005_a2_edgeIn P Q l) : Q ∈ l :=
  putnam_2005_a2_edgeIn_left_mem ((putnam_2005_a2_edgeIn_symm P Q l).1 h)

private lemma putnam_2005_a2_edgeIn_of_get_succ
    {l : List putnam_2005_a2_Point} {i : ℕ}
    (hi : i + 1 < l.length) :
    putnam_2005_a2_edgeIn l[i] l[i + 1] l := by
  left
  refine ⟨l.take i, l.drop (i + 2), ?_⟩
  have hdrop1 : l.drop i = l[i] :: l.drop (i + 1) :=
    List.drop_eq_getElem_cons (by omega)
  have hdrop2 : l.drop (i + 1) = l[i + 1] :: l.drop (i + 2) :=
    List.drop_eq_getElem_cons hi
  calc
    l.take i ++ [l[i], l[i + 1]] ++ l.drop (i + 2)
        = l.take i ++ (l[i] :: l[i + 1] :: l.drop (i + 2)) := by simp
    _ = l.take i ++ l.drop i := by rw [hdrop1, hdrop2]
    _ = l := List.take_append_drop i l

private lemma putnam_2005_a2_unit_of_edgeIn
    {P Q : putnam_2005_a2_Point} {l : List putnam_2005_a2_Point}
    (hchain : l.IsChain putnam_2005_a2_unit)
    (h : putnam_2005_a2_edgeIn P Q l) :
    putnam_2005_a2_unit P Q := by
  rcases h with ⟨s, t, hst⟩ | ⟨s, t, hst⟩
  · have hchain' : (s ++ P :: Q :: t).IsChain putnam_2005_a2_unit := by
      rw [show s ++ P :: Q :: t = l by simpa using hst]
      exact hchain
    exact (List.isChain_append_cons_cons.mp hchain').2.1
  · have hchain' : (s ++ Q :: P :: t).IsChain putnam_2005_a2_unit := by
      rw [show s ++ Q :: P :: t = l by simpa using hst]
      exact hchain
    exact (putnam_2005_a2_unit_symm P Q).2
      (List.isChain_append_cons_cons.mp hchain').2.1

private lemma putnam_2005_a2_edgeIn_idx_adjacent
    {P Q : putnam_2005_a2_Point} {l : List putnam_2005_a2_Point}
    (hnodup : l.Nodup) (h : putnam_2005_a2_edgeIn P Q l) :
    l.idxOf P + 1 = l.idxOf Q ∨ l.idxOf Q + 1 = l.idxOf P := by
  classical
  rcases h with ⟨s, t, hst⟩ | ⟨s, t, hst⟩
  · have hl : l = s ++ P :: Q :: t := by simpa using hst.symm
    have hnodup' : (s ++ P :: Q :: t).Nodup := by
      simpa [hl] using hnodup
    have hPnot_s : P ∉ s := by
      intro hP
      rcases (List.nodup_append.mp hnodup') with ⟨_hs, _hr, hdisj⟩
      exact (hdisj P hP P (by simp)) rfl
    have hQnot_sP : Q ∉ s ++ [P] := by
      intro hQ
      have hnodup'' : ((s ++ [P]) ++ Q :: t).Nodup := by
        simpa [List.append_assoc] using hnodup'
      rcases (List.nodup_append.mp hnodup'') with ⟨_hs, _hr, hdisj⟩
      exact (hdisj Q hQ Q (by simp)) rfl
    have hidxP : l.idxOf P = s.length := by
      rw [hl, List.idxOf_append_of_notMem hPnot_s, List.idxOf_cons_self]
      simp
    have hidxQ : l.idxOf Q = s.length + 1 := by
      rw [hl, show s ++ P :: Q :: t = (s ++ [P]) ++ Q :: t by simp [List.append_assoc]]
      rw [List.idxOf_append_of_notMem hQnot_sP, List.idxOf_cons_self]
      simp
    left
    omega
  · have hl : l = s ++ Q :: P :: t := by simpa using hst.symm
    have hnodup' : (s ++ Q :: P :: t).Nodup := by
      simpa [hl] using hnodup
    have hQnot_s : Q ∉ s := by
      intro hQ
      rcases (List.nodup_append.mp hnodup') with ⟨_hs, _hr, hdisj⟩
      exact (hdisj Q hQ Q (by simp)) rfl
    have hPnot_sQ : P ∉ s ++ [Q] := by
      intro hP
      have hnodup'' : ((s ++ [Q]) ++ P :: t).Nodup := by
        simpa [List.append_assoc] using hnodup'
      rcases (List.nodup_append.mp hnodup'') with ⟨_hs, _hr, hdisj⟩
      exact (hdisj P hP P (by simp)) rfl
    have hidxQ : l.idxOf Q = s.length := by
      rw [hl, List.idxOf_append_of_notMem hQnot_s, List.idxOf_cons_self]
      simp
    have hidxP : l.idxOf P = s.length + 1 := by
      rw [hl, show s ++ Q :: P :: t = (s ++ [Q]) ++ P :: t by simp [List.append_assoc]]
      rw [List.idxOf_append_of_notMem hPnot_sQ, List.idxOf_cons_self]
      simp
    right
    omega

private lemma putnam_2005_a2_eq_append_two_of_idx
    {P Q : putnam_2005_a2_Point} {l : List putnam_2005_a2_Point}
    (hPmem : P ∈ l) (hQmem : Q ∈ l)
    (hidx : l.idxOf P + 1 = l.idxOf Q) :
    ∃ a b, l = a ++ [P, Q] ++ b := by
  classical
  let k := l.idxOf P
  have hklt : k < l.length := by
    dsimp [k]
    exact List.idxOf_lt_length_of_mem hPmem
  have hk1lt : k + 1 < l.length := by
    dsimp [k]
    have hQlt := List.idxOf_lt_length_of_mem hQmem
    omega
  have hgetP : l[k] = P := by
    dsimp [k]
    exact List.getElem_idxOf hklt
  have hgetQ : l[k + 1] = Q := by
    have hQlt := List.idxOf_lt_length_of_mem hQmem
    have hidx' : k + 1 = l.idxOf Q := by
      dsimp [k]
      exact hidx
    simpa [hidx'] using (List.getElem_idxOf hQlt)
  refine ⟨l.take k, l.drop (k + 2), ?_⟩
  have hdrop0 : l.drop k = l[k] :: l.drop (k + 1) :=
    List.drop_eq_getElem_cons hklt
  have hdrop1 : l.drop (k + 1) = l[k + 1] :: l.drop (k + 2) :=
    List.drop_eq_getElem_cons hk1lt
  calc
    l = l.take k ++ l.drop k := (List.take_append_drop k l).symm
    _ = l.take k ++ (P :: Q :: l.drop (k + 2)) := by
      rw [hdrop0, hdrop1, hgetP, hgetQ]
    _ = l.take k ++ [P, Q] ++ l.drop (k + 2) := by simp

private lemma putnam_2005_a2_eq_append_four_of_idx
    {A B C D : putnam_2005_a2_Point} {l : List putnam_2005_a2_Point}
    (hAmem : A ∈ l) (hBmem : B ∈ l) (hCmem : C ∈ l) (hDmem : D ∈ l)
    (hAB : l.idxOf A + 1 = l.idxOf B)
    (hBC : l.idxOf B + 1 = l.idxOf C)
    (hCD : l.idxOf C + 1 = l.idxOf D) :
    ∃ a b, l = a ++ [A, B, C, D] ++ b := by
  classical
  let k := l.idxOf A
  have hklt : k < l.length := by
    dsimp [k]
    exact List.idxOf_lt_length_of_mem hAmem
  have hk1lt : k + 1 < l.length := by
    dsimp [k]
    have hBlt := List.idxOf_lt_length_of_mem hBmem
    omega
  have hk2lt : k + 2 < l.length := by
    dsimp [k]
    have hClt := List.idxOf_lt_length_of_mem hCmem
    omega
  have hk3lt : k + 3 < l.length := by
    dsimp [k]
    have hDlt := List.idxOf_lt_length_of_mem hDmem
    omega
  have hgetA : l[k] = A := by
    dsimp [k]
    exact List.getElem_idxOf hklt
  have hgetB : l[k + 1] = B := by
    have hBlt := List.idxOf_lt_length_of_mem hBmem
    have hidx : k + 1 = l.idxOf B := by
      dsimp [k]
      exact hAB
    simpa [hidx] using (List.getElem_idxOf hBlt)
  have hgetC : l[k + 2] = C := by
    have hClt := List.idxOf_lt_length_of_mem hCmem
    have hidx : k + 2 = l.idxOf C := by
      dsimp [k]
      omega
    simpa [hidx] using (List.getElem_idxOf hClt)
  have hgetD : l[k + 3] = D := by
    have hDlt := List.idxOf_lt_length_of_mem hDmem
    have hidx : k + 3 = l.idxOf D := by
      dsimp [k]
      omega
    simpa [hidx] using (List.getElem_idxOf hDlt)
  refine ⟨l.take k, l.drop (k + 4), ?_⟩
  have hdrop0 : l.drop k = l[k] :: l.drop (k + 1) :=
    List.drop_eq_getElem_cons hklt
  have hdrop1 : l.drop (k + 1) = l[k + 1] :: l.drop (k + 2) :=
    List.drop_eq_getElem_cons hk1lt
  have hdrop2 : l.drop (k + 2) = l[k + 2] :: l.drop (k + 3) :=
    List.drop_eq_getElem_cons hk2lt
  have hdrop3 : l.drop (k + 3) = l[k + 3] :: l.drop (k + 4) :=
    List.drop_eq_getElem_cons hk3lt
  calc
    l = l.take k ++ l.drop k := (List.take_append_drop k l).symm
    _ = l.take k ++ (A :: B :: C :: D :: l.drop (k + 4)) := by
      rw [hdrop0, hdrop1, hdrop2, hdrop3, hgetA, hgetB, hgetC, hgetD]
    _ = l.take k ++ [A, B, C, D] ++ l.drop (k + 4) := by simp

private lemma putnam_2005_a2_idxOf_getLast
    {E : putnam_2005_a2_Point} {l : List putnam_2005_a2_Point}
    (hnodup : l.Nodup) (hlast : l.getLast? = some E) :
    l.idxOf E = l.length - 1 := by
  classical
  rcases List.getLast?_eq_some_iff.mp hlast with ⟨r, rfl⟩
  have hnodup' : (r ++ [E]).Nodup := by simpa using hnodup
  have hEnot : E ∉ r := by
    intro hE
    rcases (List.nodup_append.mp hnodup') with ⟨_hr, _hE, hdisj⟩
    exact (hdisj E hE E (by simp)) rfl
  rw [List.idxOf_append_of_notMem hEnot, List.idxOf_cons_self]
  simp

private lemma putnam_2005_a2_idxOf_penultimate
    {A E : putnam_2005_a2_Point} {r l : List putnam_2005_a2_Point}
    (hnodup : l.Nodup) (hl : l = r ++ [A, E]) :
    l.idxOf A = l.length - 2 := by
  classical
  have hnodup' : (r ++ [A, E]).Nodup := by
    simpa [hl] using hnodup
  have hAnot : A ∉ r := by
    intro hA
    rcases (List.nodup_append.mp hnodup') with ⟨_hr, _ht, hdisj⟩
    exact (hdisj A hA A (by simp)) rfl
  rw [hl, List.idxOf_append_of_notMem hAnot, List.idxOf_cons_self]
  simp

private lemma putnam_2005_a2_eq_append_three_of_last_edges
    {O M E : putnam_2005_a2_Point} {l : List putnam_2005_a2_Point}
    (hnodup : l.Nodup) (hlast : l.getLast? = some E)
    (hEM : putnam_2005_a2_edgeIn E M l)
    (hOM : putnam_2005_a2_edgeIn O M l)
    (hOE : O ≠ E) :
    ∃ r, l = r ++ [O, M, E] := by
  classical
  have hEmem : E ∈ l := by
    rcases List.getLast?_eq_some_iff.mp hlast with ⟨r, rfl⟩
    simp
  have hMmem : M ∈ l := putnam_2005_a2_edgeIn_right_mem hEM
  have hOmem : O ∈ l := putnam_2005_a2_edgeIn_left_mem hOM
  have hEidx : l.idxOf E = l.length - 1 :=
    putnam_2005_a2_idxOf_getLast hnodup hlast
  have hMidx : l.idxOf M + 1 = l.idxOf E := by
    rcases putnam_2005_a2_edgeIn_idx_adjacent hnodup hEM with hbad | hgood
    · have hMlt : l.idxOf M < l.length := List.idxOf_lt_length_of_mem hMmem
      omega
    · exact hgood
  have hOidx : l.idxOf O + 1 = l.idxOf M := by
    rcases putnam_2005_a2_edgeIn_idx_adjacent hnodup hOM with hgood | hbad
    · exact hgood
    · have hOeqE : O = E := by
        have hOlt : l.idxOf O < l.length := List.idxOf_lt_length_of_mem hOmem
        have hElt : l.idxOf E < l.length := List.idxOf_lt_length_of_mem hEmem
        have hidx : l.idxOf O = l.idxOf E := by omega
        have heq :
            l[l.idxOf O] = l[l.idxOf E] :=
          ((List.Nodup.getElem_inj_iff hnodup
            (hi := hOlt) (hj := hElt)).2 hidx)
        calc
          O = l[l.idxOf O] := (List.getElem_idxOf hOlt).symm
          _ = l[l.idxOf E] := heq
          _ = E := List.getElem_idxOf hElt
      exact (hOE hOeqE).elim
  let k := l.idxOf O
  have hklt : k < l.length := List.idxOf_lt_length_of_mem hOmem
  have hk1lt : k + 1 < l.length := by
    dsimp [k]
    omega
  have hk2lt : k + 2 < l.length := by
    dsimp [k]
    omega
  have hlenk : k + 3 = l.length := by
    dsimp [k]
    omega
  have hgetO : l[k] = O := by
    dsimp [k]
    exact List.getElem_idxOf hklt
  have hgetM : l[k + 1] = M := by
    have hidx : k + 1 = l.idxOf M := by
      dsimp [k]
      omega
    have hMlt : l.idxOf M < l.length := List.idxOf_lt_length_of_mem hMmem
    have heq :
        l[k + 1] = l[l.idxOf M] :=
      ((List.Nodup.getElem_inj_iff hnodup
        (hi := hk1lt) (hj := hMlt)).2 hidx)
    exact heq.trans (List.getElem_idxOf hMlt)
  have hgetE : l[k + 2] = E := by
    have hidx : k + 2 = l.idxOf E := by
      dsimp [k]
      omega
    have hElt : l.idxOf E < l.length := List.idxOf_lt_length_of_mem hEmem
    have heq :
        l[k + 2] = l[l.idxOf E] :=
      ((List.Nodup.getElem_inj_iff hnodup
        (hi := hk2lt) (hj := hElt)).2 hidx)
    exact heq.trans (List.getElem_idxOf hElt)
  refine ⟨l.take k, ?_⟩
  have hdrop0 : l.drop k = l[k] :: l.drop (k + 1) :=
    List.drop_eq_getElem_cons hklt
  have hdrop1 : l.drop (k + 1) = l[k + 1] :: l.drop (k + 2) :=
    List.drop_eq_getElem_cons hk1lt
  have hdrop2 : l.drop (k + 2) = l[k + 2] :: l.drop (k + 3) :=
    List.drop_eq_getElem_cons hk2lt
  calc
    l = l.take k ++ l.drop k := (List.take_append_drop k l).symm
    _ = l.take k ++ (O :: M :: E :: ([] : List putnam_2005_a2_Point)) := by
      rw [hdrop0, hdrop1, hdrop2, hgetO, hgetM, hgetE]
      simp [hlenk]
    _ = l.take k ++ [O, M, E] := by simp

private lemma putnam_2005_a2_forced_two_edges
    {l : List putnam_2005_a2_Point} {P A B : putnam_2005_a2_Point}
    (hnodup : l.Nodup) (hchain : l.IsChain putnam_2005_a2_unit)
    (hPmem : P ∈ l)
    (hprev : 0 < l.idxOf P) (hnext : l.idxOf P + 1 < l.length)
    (hneigh : ∀ Q, Q ∈ l → putnam_2005_a2_unit P Q → Q = A ∨ Q = B) :
    putnam_2005_a2_edgeIn P A l ∧ putnam_2005_a2_edgeIn P B l := by
  classical
  let i := l.idxOf P
  have hi : i < l.length := (List.idxOf_lt_length_iff).2 hPmem
  have hget : l[i] = P := List.getElem_idxOf hi
  have him1_succ : (i - 1) + 1 = i := by omega
  have him1_next : (i - 1) + 1 < l.length := by omega
  have hedgePrev0 : putnam_2005_a2_edgeIn l[i - 1] l[(i - 1) + 1] l :=
    putnam_2005_a2_edgeIn_of_get_succ him1_next
  have hoptPrevSucc : l[(i - 1) + 1]? = some P := by
    rw [show (i - 1) + 1 = i by omega]
    rw [List.getElem?_eq_getElem hi, hget]
  rcases (List.getElem?_eq_some_iff.mp hoptPrevSucc) with ⟨_, hgetPrevSucc⟩
  have hedgePrev : putnam_2005_a2_edgeIn P l[i - 1] l := by
    have hsymm := (putnam_2005_a2_edgeIn_symm _ _ _).1 hedgePrev0
    simpa [hgetPrevSucc] using hsymm
  have hedgeNext0 : putnam_2005_a2_edgeIn l[i] l[i + 1] l :=
    putnam_2005_a2_edgeIn_of_get_succ hnext
  have hedgeNext : putnam_2005_a2_edgeIn P l[i + 1] l := by
    simpa [hget] using hedgeNext0
  have hunitPrev : putnam_2005_a2_unit P l[i - 1] :=
    putnam_2005_a2_unit_of_edgeIn hchain hedgePrev
  have hunitNext : putnam_2005_a2_unit P l[i + 1] :=
    putnam_2005_a2_unit_of_edgeIn hchain hedgeNext
  have hmemPrev : l[i - 1] ∈ l := List.getElem_mem (by omega)
  have hmemNext : l[i + 1] ∈ l := List.getElem_mem hnext
  have hprevAB := hneigh l[i - 1] hmemPrev hunitPrev
  have hnextAB := hneigh l[i + 1] hmemNext hunitNext
  have hprev_ne_next : l[i - 1] ≠ l[i + 1] := by
    intro hsame
    have hidx : i - 1 = i + 1 :=
      (List.Nodup.getElem_inj_iff hnodup).1 hsame
    omega
  rcases hprevAB with hprevA | hprevB <;>
    rcases hnextAB with hnextA | hnextB
  · exfalso
    exact hprev_ne_next (by rw [hprevA, hnextA])
  · constructor
    · simpa [hprevA] using hedgePrev
    · simpa [hnextB] using hedgeNext
  · constructor
    · simpa [hnextA] using hedgeNext
    · simpa [hprevB] using hedgePrev
  · exfalso
    exact hprev_ne_next (by rw [hprevB, hnextB])

private lemma putnam_2005_a2_forced_edge_of_three_excluding
    {l : List putnam_2005_a2_Point} {P A B C : putnam_2005_a2_Point}
    (hnodup : l.Nodup) (hchain : l.IsChain putnam_2005_a2_unit)
    (hPmem : P ∈ l)
    (hprev : 0 < l.idxOf P) (hnext : l.idxOf P + 1 < l.length)
    (hneigh : ∀ Q, Q ∈ l → putnam_2005_a2_unit P Q → Q = A ∨ Q = B ∨ Q = C)
    (hnotC : ¬ putnam_2005_a2_edgeIn P C l) :
    putnam_2005_a2_edgeIn P B l := by
  classical
  let i := l.idxOf P
  have hi : i < l.length := (List.idxOf_lt_length_iff).2 hPmem
  have hget : l[i] = P := List.getElem_idxOf hi
  have him1_next : (i - 1) + 1 < l.length := by omega
  have hedgePrev0 : putnam_2005_a2_edgeIn l[i - 1] l[(i - 1) + 1] l :=
    putnam_2005_a2_edgeIn_of_get_succ him1_next
  have hoptPrevSucc : l[(i - 1) + 1]? = some P := by
    rw [show (i - 1) + 1 = i by omega]
    rw [List.getElem?_eq_getElem hi, hget]
  rcases (List.getElem?_eq_some_iff.mp hoptPrevSucc) with ⟨_, hgetPrevSucc⟩
  have hedgePrev : putnam_2005_a2_edgeIn P l[i - 1] l := by
    have hsymm := (putnam_2005_a2_edgeIn_symm _ _ _).1 hedgePrev0
    simpa [hgetPrevSucc] using hsymm
  have hedgeNext0 : putnam_2005_a2_edgeIn l[i] l[i + 1] l :=
    putnam_2005_a2_edgeIn_of_get_succ hnext
  have hedgeNext : putnam_2005_a2_edgeIn P l[i + 1] l := by
    simpa [hget] using hedgeNext0
  have hunitPrev : putnam_2005_a2_unit P l[i - 1] :=
    putnam_2005_a2_unit_of_edgeIn hchain hedgePrev
  have hunitNext : putnam_2005_a2_unit P l[i + 1] :=
    putnam_2005_a2_unit_of_edgeIn hchain hedgeNext
  have hmemPrev : l[i - 1] ∈ l := List.getElem_mem (by omega)
  have hmemNext : l[i + 1] ∈ l := List.getElem_mem hnext
  have hprevABC := hneigh l[i - 1] hmemPrev hunitPrev
  have hnextABC := hneigh l[i + 1] hmemNext hunitNext
  have hprev_ne_next : l[i - 1] ≠ l[i + 1] := by
    intro hsame
    have hidx : i - 1 = i + 1 :=
      (List.Nodup.getElem_inj_iff hnodup).1 hsame
    omega
  have hprevAB : l[i - 1] = A ∨ l[i - 1] = B := by
    rcases hprevABC with hA | hB | hC
    · exact Or.inl hA
    · exact Or.inr hB
    · exact (hnotC (by simpa [hC] using hedgePrev)).elim
  have hnextAB : l[i + 1] = A ∨ l[i + 1] = B := by
    rcases hnextABC with hA | hB | hC
    · exact Or.inl hA
    · exact Or.inr hB
    · exact (hnotC (by simpa [hC] using hedgeNext)).elim
  rcases hprevAB with hprevA | hprevB <;>
    rcases hnextAB with hnextA | hnextB
  · exfalso
    exact hprev_ne_next (by rw [hprevA, hnextA])
  · simpa [hnextB] using hedgeNext
  · simpa [hprevB] using hedgePrev
  · exfalso
    exact hprev_ne_next (by rw [hprevB, hnextB])

private lemma putnam_2005_a2_boardList_nodup (n : ℕ) :
    (putnam_2005_a2_boardList n).Nodup := by
  unfold putnam_2005_a2_boardList
  rw [List.nodup_flatMap]
  constructor
  · intro x hx
    norm_num
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp at hi hj hij ⊢
    intro h
    have hget_i :
        (List.flatMap (fun a : ℕ => [(a : ℤ)]) (List.range n))[i] = (i : ℤ) := by
      have hmap : List.flatMap (fun a : ℕ => [(a : ℤ)]) (List.range n) =
          (List.range n).map (fun a : ℕ => (a : ℤ)) := by
        simpa [Function.comp_def] using
          (List.flatMap_pure_eq_map (fun a : ℕ => (a : ℤ)) (List.range n))
      simp [hmap]
    have hget_j :
        (List.flatMap (fun a : ℕ => [(a : ℤ)]) (List.range n))[j] = (j : ℤ) := by
      have hmap : List.flatMap (fun a : ℕ => [(a : ℤ)]) (List.range n) =
          (List.range n).map (fun a : ℕ => (a : ℤ)) := by
        simpa [Function.comp_def] using
          (List.flatMap_pure_eq_map (fun a : ℕ => (a : ℤ)) (List.range n))
      simp [hmap]
    have : (j : ℤ) = (i : ℤ) := by simpa [hget_i, hget_j] using h
    omega

private lemma putnam_2005_a2_listTour_nodup {n : ℕ} {top : Bool}
    {l : List putnam_2005_a2_Point}
    (hl : putnam_2005_a2_listTour n top l) : l.Nodup :=
  (List.Perm.nodup_iff hl.1).2 (putnam_2005_a2_boardList_nodup n)

private lemma putnam_2005_a2_listTour_length {n : ℕ} {top : Bool}
    {l : List putnam_2005_a2_Point}
    (hl : putnam_2005_a2_listTour n top l) : l.length = 3 * n := by
  rw [hl.1.length_eq, putnam_2005_a2_boardList_length]

private lemma putnam_2005_a2_cornerListTour_nodup {n : ℕ} {startTop endTop : Bool}
    {l : List putnam_2005_a2_Point}
    (hl : putnam_2005_a2_cornerListTour n startTop endTop l) : l.Nodup :=
  (List.Perm.nodup_iff hl.1).2 (putnam_2005_a2_boardList_nodup n)

private lemma putnam_2005_a2_cornerListTour_length {n : ℕ} {startTop endTop : Bool}
    {l : List putnam_2005_a2_Point}
    (hl : putnam_2005_a2_cornerListTour n startTop endTop l) : l.length = 3 * n := by
  rw [hl.1.length_eq, putnam_2005_a2_boardList_length]

private lemma putnam_2005_a2_listTour_mem_board {n : ℕ} {top : Bool}
    {l : List putnam_2005_a2_Point}
    (hl : putnam_2005_a2_listTour n top l)
    {P : putnam_2005_a2_Point} (hP : P ∈ l) :
    P ∈ putnam_2005_a2_board n :=
  (putnam_2005_a2_boardList_mem_iff n P).1 ((hl.1.mem_iff).1 hP)

private lemma putnam_2005_a2_cornerListTour_mem_board {n : ℕ} {startTop endTop : Bool}
    {l : List putnam_2005_a2_Point}
    (hl : putnam_2005_a2_cornerListTour n startTop endTop l)
    {P : putnam_2005_a2_Point} (hP : P ∈ l) :
    P ∈ putnam_2005_a2_board n :=
  (putnam_2005_a2_boardList_mem_iff n P).1 ((hl.1.mem_iff).1 hP)

private lemma putnam_2005_a2_board_mem_listTour {n : ℕ} {top : Bool}
    {l : List putnam_2005_a2_Point}
    (hl : putnam_2005_a2_listTour n top l)
    {P : putnam_2005_a2_Point} (hP : P ∈ putnam_2005_a2_board n) :
    P ∈ l :=
  (hl.1.mem_iff).2 ((putnam_2005_a2_boardList_mem_iff n P).2 hP)

private lemma putnam_2005_a2_board_mem_cornerListTour {n : ℕ} {startTop endTop : Bool}
    {l : List putnam_2005_a2_Point}
    (hl : putnam_2005_a2_cornerListTour n startTop endTop l)
    {P : putnam_2005_a2_Point} (hP : P ∈ putnam_2005_a2_board n) :
    P ∈ l :=
  (hl.1.mem_iff).2 ((putnam_2005_a2_boardList_mem_iff n P).2 hP)

private lemma putnam_2005_a2_corner_right_opposite_edges
    {n : ℕ} {startTop endTop : Bool} {l : List putnam_2005_a2_Point}
    (hn : 0 < n)
    (hl : putnam_2005_a2_cornerListTour (n + 1) startTop endTop l) :
    putnam_2005_a2_edgeIn
        (putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side (!endTop)))
        (putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop))) l ∧
      putnam_2005_a2_edgeIn
        (putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side (!endTop)))
        (putnam_2005_a2_pt ((n : ℤ) + 1) 2) l := by
  classical
  let O := putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side (!endTop))
  let LO := putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop))
  let M := putnam_2005_a2_pt ((n : ℤ) + 1) 2
  have hOboard : O ∈ putnam_2005_a2_board (n + 1) := by
    have hx : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by norm_num
    cases endTop
    · change ((n : ℤ) + 1) ∈ Icc (1 : ℤ) ((n + 1 : ℕ) : ℤ) ∧
        (3 : ℤ) ∈ Icc (1 : ℤ) 3
      constructor
      · rw [hx]
        constructor <;> omega
      · norm_num
    · change ((n : ℤ) + 1) ∈ Icc (1 : ℤ) ((n + 1 : ℕ) : ℤ) ∧
        (1 : ℤ) ∈ Icc (1 : ℤ) 3
      constructor
      · rw [hx]
        constructor <;> omega
      · norm_num
  have hOmem : O ∈ l := putnam_2005_a2_board_mem_cornerListTour hl hOboard
  have hnotHead : O ≠ putnam_2005_a2_pt 1 (putnam_2005_a2_side startTop) := by
    intro h
    cases startTop <;> cases endTop <;>
      simp [O, putnam_2005_a2_pt, putnam_2005_a2_side] at h <;> omega
  have hprev : 0 < l.idxOf O := by
    by_contra h
    have hzero : l.idxOf O = 0 := by omega
    have hO0 : l[0]? = some O := by
      simpa [hzero] using List.getElem?_idxOf hOmem
    have hheadO : l.head? = some O := by
      simpa [List.head?_eq_getElem?] using hO0
    have hhead := hl.2.2.1
    rw [hhead] at hheadO
    exact hnotHead (Option.some.inj hheadO.symm)
  have hnotLast : some O ≠ l.getLast? := by
    intro hlastO
    have hlast := hl.2.2.2
    rw [hlast] at hlastO
    have hOE : O =
        putnam_2005_a2_pt ((n + 1 : ℕ) : ℤ) (putnam_2005_a2_side endTop) :=
      Option.some.inj hlastO
    cases endTop <;>
      simp [O, putnam_2005_a2_pt, putnam_2005_a2_side] at hOE
  have hOdrop : O ∈ l.dropLast :=
    List.mem_dropLast_of_mem_of_ne_getLast? hOmem hnotLast
  have hnext : l.idxOf O + 1 < l.length :=
    List.succ_idxOf_lt_length_of_mem_dropLast hOdrop
  have hneigh : ∀ Q, Q ∈ l → putnam_2005_a2_unit O Q → Q = LO ∨ Q = M := by
    intro Q hQmem hunit
    have hQboard : Q ∈ putnam_2005_a2_board (n + 1) :=
      putnam_2005_a2_cornerListTour_mem_board hl hQmem
    cases endTop
    · simpa [O, LO, M, putnam_2005_a2_side] using
        putnam_2005_a2_neighbor_right_top (n := n) hQboard hunit
    · simpa [O, LO, M, putnam_2005_a2_side] using
        putnam_2005_a2_neighbor_right_bottom (n := n) hQboard hunit
  exact putnam_2005_a2_forced_two_edges
    (putnam_2005_a2_cornerListTour_nodup hl) hl.2.1 hOmem hprev hnext hneigh

private lemma putnam_2005_a2_corner_right_endpoint_edge
    {n : ℕ} {startTop endTop : Bool} {l : List putnam_2005_a2_Point}
    (hn : 0 < n)
    (hl : putnam_2005_a2_cornerListTour (n + 1) startTop endTop l) :
    putnam_2005_a2_edgeIn
        (putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side endTop))
        (putnam_2005_a2_pt ((n : ℤ) + 1) 2) l ∨
      putnam_2005_a2_edgeIn
        (putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side endTop))
        (putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side endTop)) l := by
  classical
  let E := putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side endTop)
  let M := putnam_2005_a2_pt ((n : ℤ) + 1) 2
  let LE := putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side endTop)
  have hlast : l.getLast? = some E := by
    simpa [E, putnam_2005_a2_pt] using hl.2.2.2
  rcases List.getLast?_eq_some_iff.mp hlast with ⟨r, rfl⟩
  have hlen : (r ++ [E]).length = 3 * (n + 1) :=
    putnam_2005_a2_cornerListTour_length hl
  have hrne : r ≠ [] := by
    intro hr
    simp [hr] at hlen
    omega
  let X := r.getLast hrne
  have hprefix : r.dropLast ++ [X] = r := by
    simpa [X] using List.dropLast_append_getLast hrne
  have hchain' :
      (r.dropLast ++ X :: E :: ([] : List putnam_2005_a2_Point)).IsChain
        putnam_2005_a2_unit := by
    rw [show r.dropLast ++ X :: E :: ([] : List putnam_2005_a2_Point) = r ++ [E] by
      calc
        r.dropLast ++ X :: E :: ([] : List putnam_2005_a2_Point)
            = (r.dropLast ++ [X]) ++ [E] := by simp
        _ = r ++ [E] := by rw [hprefix]]
    exact hl.2.1
  have hunitXE : putnam_2005_a2_unit X E :=
    (List.isChain_append_cons_cons.mp hchain').2.1
  have hXmemr : X ∈ r := by
    exact List.getLast_mem hrne
  have hXmem : X ∈ r ++ [E] := by
    exact List.mem_append_left _ hXmemr
  have hXboard : X ∈ putnam_2005_a2_board (n + 1) :=
    putnam_2005_a2_cornerListTour_mem_board hl hXmem
  have hunitEX : putnam_2005_a2_unit E X :=
    (putnam_2005_a2_unit_symm E X).2 hunitXE
  have hclass : X = LE ∨ X = M := by
    cases endTop
    · have h := putnam_2005_a2_neighbor_right_bottom (n := n) hXboard
        (by simpa [E, putnam_2005_a2_side] using hunitEX)
      simpa [LE, M, E, putnam_2005_a2_side] using h
    · have h := putnam_2005_a2_neighbor_right_top (n := n) hXboard
        (by simpa [E, putnam_2005_a2_side] using hunitEX)
      simpa [LE, M, E, putnam_2005_a2_side] using h
  have hedgeEX : putnam_2005_a2_edgeIn E X (r ++ [E]) := by
    right
    refine ⟨r.dropLast, [], ?_⟩
    calc
      r.dropLast ++ [X, E] ++ ([] : List putnam_2005_a2_Point)
          = (r.dropLast ++ [X]) ++ [E] := by simp
      _ = r ++ [E] := by rw [hprefix]
  rcases hclass with hXLE | hXM
  · right
    simpa [hXLE] using hedgeEX
  · left
    simpa [hXM] using hedgeEX

private lemma putnam_2005_a2_corner_right_endpoint_split
    {n : ℕ} {startTop endTop : Bool} {l : List putnam_2005_a2_Point}
    (hn : 0 < n)
    (hl : putnam_2005_a2_cornerListTour (n + 1) startTop endTop l) :
    (∃ r,
      l = r ++
        [putnam_2005_a2_pt ((n : ℤ) + 1) 2,
          putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side endTop)]) ∨
      (∃ r,
        l = r ++
          [putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side endTop),
            putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side endTop)]) := by
  classical
  let E := putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side endTop)
  let M := putnam_2005_a2_pt ((n : ℤ) + 1) 2
  let LE := putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side endTop)
  have hlast : l.getLast? = some E := by
    simpa [E, putnam_2005_a2_pt] using hl.2.2.2
  rcases List.getLast?_eq_some_iff.mp hlast with ⟨r, rfl⟩
  have hlen : (r ++ [E]).length = 3 * (n + 1) :=
    putnam_2005_a2_cornerListTour_length hl
  have hrne : r ≠ [] := by
    intro hr
    simp [hr] at hlen
    omega
  let X := r.getLast hrne
  have hprefix : r.dropLast ++ [X] = r := by
    simpa [X] using List.dropLast_append_getLast hrne
  have hchain' :
      (r.dropLast ++ X :: E :: ([] : List putnam_2005_a2_Point)).IsChain
        putnam_2005_a2_unit := by
    rw [show r.dropLast ++ X :: E :: ([] : List putnam_2005_a2_Point) = r ++ [E] by
      calc
        r.dropLast ++ X :: E :: ([] : List putnam_2005_a2_Point)
            = (r.dropLast ++ [X]) ++ [E] := by simp
        _ = r ++ [E] := by rw [hprefix]]
    exact hl.2.1
  have hunitXE : putnam_2005_a2_unit X E :=
    (List.isChain_append_cons_cons.mp hchain').2.1
  have hXmemr : X ∈ r := List.getLast_mem hrne
  have hXmem : X ∈ r ++ [E] := List.mem_append_left _ hXmemr
  have hXboard : X ∈ putnam_2005_a2_board (n + 1) :=
    putnam_2005_a2_cornerListTour_mem_board hl hXmem
  have hunitEX : putnam_2005_a2_unit E X :=
    (putnam_2005_a2_unit_symm E X).2 hunitXE
  have hclass : X = LE ∨ X = M := by
    cases endTop
    · have h := putnam_2005_a2_neighbor_right_bottom (n := n) hXboard
        (by simpa [E, putnam_2005_a2_side] using hunitEX)
      simpa [LE, M, E, putnam_2005_a2_side] using h
    · have h := putnam_2005_a2_neighbor_right_top (n := n) hXboard
        (by simpa [E, putnam_2005_a2_side] using hunitEX)
      simpa [LE, M, E, putnam_2005_a2_side] using h
  rcases hclass with hXLE | hXM
  · right
    refine ⟨r.dropLast, ?_⟩
    calc
      r ++ [E] = (r.dropLast ++ [X]) ++ [E] := by rw [hprefix]
      _ = r.dropLast ++ [LE, E] := by simp [hXLE]
      _ = r.dropLast ++
          [putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side endTop),
            putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side endTop)] := by
          simp [LE, E]
  · left
    refine ⟨r.dropLast, ?_⟩
    calc
      r ++ [E] = (r.dropLast ++ [X]) ++ [E] := by rw [hprefix]
      _ = r.dropLast ++ [M, E] := by simp [hXM]
      _ = r.dropLast ++
          [putnam_2005_a2_pt ((n : ℤ) + 1) 2,
            putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side endTop)] := by
          simp [M, E]

private def putnam_2005_a2_rightTail
    (n : ℕ) (endTop : Bool) : List putnam_2005_a2_Point :=
  [putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side (!endTop)),
    putnam_2005_a2_pt ((n : ℤ) + 1) 2,
    putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side endTop)]

private lemma putnam_2005_a2_corner_rightTail_of_endpoint_middle
    {n : ℕ} {startTop endTop : Bool} {l r : List putnam_2005_a2_Point}
    (hn : 0 < n)
    (hl : putnam_2005_a2_cornerListTour (n + 1) startTop endTop l)
    (hr :
      l = r ++
        [putnam_2005_a2_pt ((n : ℤ) + 1) 2,
          putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side endTop)]) :
    ∃ s, l = s ++ putnam_2005_a2_rightTail n endTop := by
  classical
  let O := putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side (!endTop))
  let M := putnam_2005_a2_pt ((n : ℤ) + 1) 2
  let E := putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side endTop)
  have hlast : l.getLast? = some E := by
    simpa [E, putnam_2005_a2_pt] using hl.2.2.2
  have hEM : putnam_2005_a2_edgeIn E M l := by
    right
    refine ⟨r, [], ?_⟩
    simpa [M, E] using hr.symm
  have hOM : putnam_2005_a2_edgeIn O M l := by
    simpa [O, M] using
      (putnam_2005_a2_corner_right_opposite_edges
        (n := n) (startTop := startTop) (endTop := endTop) hn hl).2
  have hOE : O ≠ E := by
    intro h
    cases endTop <;>
      simp [O, E, putnam_2005_a2_pt, putnam_2005_a2_side] at h
  rcases putnam_2005_a2_eq_append_three_of_last_edges
      (putnam_2005_a2_cornerListTour_nodup hl) hlast hEM hOM hOE with
    ⟨s, hs⟩
  refine ⟨s, ?_⟩
  simpa [putnam_2005_a2_rightTail, O, M, E] using hs

private lemma putnam_2005_a2_unit_right_horizontal
    (n : ℕ) (y : ℤ) :
    putnam_2005_a2_unit (putnam_2005_a2_pt (n : ℤ) y)
      (putnam_2005_a2_pt ((n : ℤ) + 1) y) := by
  simp [putnam_2005_a2_unit, putnam_2005_a2_pt]

private lemma putnam_2005_a2_unit_same_col_side_mid
    (x : ℤ) (top : Bool) :
    putnam_2005_a2_unit
      (putnam_2005_a2_pt x (putnam_2005_a2_side top))
      (putnam_2005_a2_pt x 2) := by
  cases top <;> simp [putnam_2005_a2_unit, putnam_2005_a2_pt,
    putnam_2005_a2_side]

private lemma putnam_2005_a2_rightTail_chain (n : ℕ) (endTop : Bool) :
    (putnam_2005_a2_rightTail n endTop).IsChain putnam_2005_a2_unit := by
  cases endTop <;>
    simp [putnam_2005_a2_rightTail, putnam_2005_a2_unit,
      putnam_2005_a2_pt, putnam_2005_a2_side]

private lemma putnam_2005_a2_rightTail_perm (n : ℕ) (endTop : Bool) :
    (putnam_2005_a2_rightTail n endTop).Perm
      [putnam_2005_a2_pt ((n : ℤ) + 1) 1,
        putnam_2005_a2_pt ((n : ℤ) + 1) 2,
        putnam_2005_a2_pt ((n : ℤ) + 1) 3] := by
  cases endTop
  · simp only [putnam_2005_a2_rightTail, Bool.not_false, putnam_2005_a2_side,
      Bool.false_eq_true, ↓reduceIte]
    exact
      (List.Perm.swap
        (putnam_2005_a2_pt ((n : ℤ) + 1) 2)
        (putnam_2005_a2_pt ((n : ℤ) + 1) 3)
        [putnam_2005_a2_pt ((n : ℤ) + 1) 1]).trans
      ((List.Perm.cons (putnam_2005_a2_pt ((n : ℤ) + 1) 2)
        (List.Perm.swap
          (putnam_2005_a2_pt ((n : ℤ) + 1) 1)
          (putnam_2005_a2_pt ((n : ℤ) + 1) 3) [])).trans
      (List.Perm.swap
        (putnam_2005_a2_pt ((n : ℤ) + 1) 1)
        (putnam_2005_a2_pt ((n : ℤ) + 1) 2)
        [putnam_2005_a2_pt ((n : ℤ) + 1) 3]))
  · simp [putnam_2005_a2_rightTail, putnam_2005_a2_side]

private lemma putnam_2005_a2_perm_of_perm_append_rightTail
    {n : ℕ} {endTop : Bool}
    {big small : List putnam_2005_a2_Point}
    (hbig : big.Perm (putnam_2005_a2_boardList (n + 1)))
    (hperm : big.Perm (small ++ putnam_2005_a2_rightTail n endTop)) :
    small.Perm (putnam_2005_a2_boardList n) := by
  rw [List.perm_iff_count]
  intro P
  have hbig_count := (List.perm_iff_count.mp hbig P)
  have hperm_count := (List.perm_iff_count.mp hperm P)
  have htail_count :=
    (List.perm_iff_count.mp (putnam_2005_a2_rightTail_perm n endTop) P)
  rw [putnam_2005_a2_boardList_succ, List.count_append] at hbig_count
  rw [List.count_append] at hperm_count
  omega

private lemma putnam_2005_a2_rightTail_mem_iff
    (n : ℕ) (endTop : Bool) (P : putnam_2005_a2_Point) :
    P ∈ putnam_2005_a2_rightTail n endTop ↔
      P = putnam_2005_a2_pt ((n : ℤ) + 1) 1 ∨
        P = putnam_2005_a2_pt ((n : ℤ) + 1) 2 ∨
        P = putnam_2005_a2_pt ((n : ℤ) + 1) 3 := by
  cases endTop <;>
    simp [putnam_2005_a2_rightTail, putnam_2005_a2_pt,
      putnam_2005_a2_side] <;> tauto

private lemma putnam_2005_a2_board_succ_of_board
    {n : ℕ} {P : putnam_2005_a2_Point}
    (hP : P ∈ putnam_2005_a2_board n) :
    P ∈ putnam_2005_a2_board (n + 1) := by
  rcases P with ⟨x, y⟩
  unfold putnam_2005_a2_board at hP ⊢
  change x ∈ Icc (1 : ℤ) (n : ℤ) ∧ y ∈ Icc (1 : ℤ) 3 at hP
  change x ∈ Icc (1 : ℤ) ((n + 1 : ℕ) : ℤ) ∧ y ∈ Icc (1 : ℤ) 3
  constructor
  · constructor
    · exact hP.1.1
    · exact le_trans hP.1.2 (by exact_mod_cast Nat.le_succ n)
  · exact hP.2

private lemma putnam_2005_a2_board_not_rightTail
    {n : ℕ} {endTop : Bool} {P : putnam_2005_a2_Point}
    (hP : P ∈ putnam_2005_a2_board n) :
    P ∉ putnam_2005_a2_rightTail n endTop := by
  rcases P with ⟨x, y⟩
  unfold putnam_2005_a2_board at hP
  change x ∈ Icc (1 : ℤ) (n : ℤ) ∧ y ∈ Icc (1 : ℤ) 3 at hP
  rcases hP with ⟨⟨_hxlo, hxhi⟩, _hy⟩
  intro ht
  rw [putnam_2005_a2_rightTail_mem_iff] at ht
  rcases ht with ht | ht | ht <;>
    simp [putnam_2005_a2_pt] at ht <;>
    rcases ht with ⟨hx, _hy⟩ <;> omega

private lemma putnam_2005_a2_board_of_succ_not_rightTail
    {n : ℕ} {endTop : Bool} {P : putnam_2005_a2_Point}
    (hP : P ∈ putnam_2005_a2_board (n + 1))
    (hnot : P ∉ putnam_2005_a2_rightTail n endTop) :
    P ∈ putnam_2005_a2_board n := by
  rcases P with ⟨x, y⟩
  unfold putnam_2005_a2_board at hP ⊢
  change x ∈ Icc (1 : ℤ) ((n + 1 : ℕ) : ℤ) ∧ y ∈ Icc (1 : ℤ) 3 at hP
  rcases hP with ⟨⟨hxlo, hxhi⟩, hy⟩
  change x ∈ Icc (1 : ℤ) (n : ℤ) ∧ y ∈ Icc (1 : ℤ) 3
  constructor
  · constructor
    · exact hxlo
    · by_contra hxle
      have hcast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by norm_num
      rw [hcast] at hxhi
      have hx : x = (n : ℤ) + 1 := by omega
      rcases hy with ⟨hy1, hy3⟩
      interval_cases y <;> apply hnot <;>
        rw [putnam_2005_a2_rightTail_mem_iff] <;>
        simp [putnam_2005_a2_pt, hx]
  · exact hy

private lemma putnam_2005_a2_cornerListTour_append_rightTail_inv
    {n : ℕ} {startTop endTop : Bool} {l : List putnam_2005_a2_Point}
    (hn : 0 < n)
    (hl : putnam_2005_a2_cornerListTour (n + 1) startTop endTop
      (l ++ putnam_2005_a2_rightTail n endTop)) :
    putnam_2005_a2_cornerListTour n startTop (!endTop) l := by
  classical
  let tail := putnam_2005_a2_rightTail n endTop
  have htail_len : tail.length = 3 := by
    cases endTop <;> simp [tail, putnam_2005_a2_rightTail, putnam_2005_a2_side]
  have hbig_len : (l ++ tail).length = 3 * (n + 1) :=
    putnam_2005_a2_cornerListTour_length hl
  have hlen : l.length = 3 * n := by
    simp [List.length_append, htail_len] at hbig_len
    omega
  have hlne : l ≠ [] := by
    intro h
    rw [h] at hlen
    simp at hlen
    omega
  have hnodupBig : (l ++ tail).Nodup :=
    putnam_2005_a2_cornerListTour_nodup hl
  have hnodupL : l.Nodup := (List.nodup_append.mp hnodupBig).1
  have hmem_iff : ∀ P, P ∈ l ↔ P ∈ putnam_2005_a2_board n := by
    intro P
    constructor
    · intro hP
      have hnotTail : P ∉ tail := by
        intro hPt
        rcases (List.nodup_append.mp hnodupBig) with ⟨_hl, _ht, hdisj⟩
        exact (hdisj P hP P hPt) rfl
      have hPbigmem : P ∈ l ++ tail := List.mem_append_left _ hP
      have hPbigBoard : P ∈ putnam_2005_a2_board (n + 1) :=
        putnam_2005_a2_cornerListTour_mem_board hl hPbigmem
      exact putnam_2005_a2_board_of_succ_not_rightTail
        (endTop := endTop) hPbigBoard (by simpa [tail] using hnotTail)
    · intro hP
      have hPbigBoard : P ∈ putnam_2005_a2_board (n + 1) :=
        putnam_2005_a2_board_succ_of_board hP
      have hPbigmem : P ∈ l ++ tail :=
        putnam_2005_a2_board_mem_cornerListTour hl hPbigBoard
      have hnotTail : P ∉ tail := by
        simpa [tail] using
          (putnam_2005_a2_board_not_rightTail (endTop := endTop) hP)
      rcases List.mem_append.mp hPbigmem with hPl | hPt
      · exact hPl
      · exact (hnotTail hPt).elim
  have hperm : l.Perm (putnam_2005_a2_boardList n) := by
    rw [List.perm_iff_count]
    intro P
    by_cases hP : P ∈ l
    · rw [List.count_eq_one_of_mem hnodupL hP,
        List.count_eq_one_of_mem (putnam_2005_a2_boardList_nodup n)
          ((putnam_2005_a2_boardList_mem_iff n P).2 ((hmem_iff P).1 hP))]
    · have hPnotBoardList : P ∉ putnam_2005_a2_boardList n := by
        intro hPb
        exact hP ((hmem_iff P).2 ((putnam_2005_a2_boardList_mem_iff n P).1 hPb))
      rw [List.count_eq_zero_of_not_mem hP,
        List.count_eq_zero_of_not_mem hPnotBoardList]
  constructor
  · exact hperm
  constructor
  · exact List.IsChain.left_of_append hl.2.1
  constructor
  · have hhead := hl.2.2.1
    have hhead_append : (l ++ tail).head? = l.head? := by
      rw [List.head?_append_of_ne_nil l hlne]
    rw [hhead_append] at hhead
    exact hhead
  · let O := putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side (!endTop))
    let X := l.getLast hlne
    have hlastX : l.getLast? = some X := by
      simpa [X] using List.getLast?_eq_some_getLast hlne
    have hXmem : X ∈ l := by
      exact List.getLast_mem hlne
    have hXboard : X ∈ putnam_2005_a2_board n := (hmem_iff X).1 hXmem
    have hbridge_all := (List.isChain_append.mp hl.2.1).2.2
    have hOhead : O ∈ tail.head? := by
      cases endTop <;>
        simp [tail, O, putnam_2005_a2_rightTail, putnam_2005_a2_side,
          putnam_2005_a2_pt]
    have hunitXO : putnam_2005_a2_unit X O := hbridge_all X (by simpa [hlastX]) O hOhead
    have hunitOX : putnam_2005_a2_unit O X :=
      (putnam_2005_a2_unit_symm O X).2 hunitXO
    have hXclass :
        X = putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop)) ∨
          X = putnam_2005_a2_pt ((n : ℤ) + 1) 2 := by
      cases endTop
      · simpa [O, putnam_2005_a2_side] using
          putnam_2005_a2_neighbor_right_top (n := n)
            (putnam_2005_a2_board_succ_of_board hXboard) hunitOX
      · simpa [O, putnam_2005_a2_side] using
          putnam_2005_a2_neighbor_right_bottom (n := n)
            (putnam_2005_a2_board_succ_of_board hXboard) hunitOX
    rcases hXclass with hX | hX
    · rw [hlastX]
      simpa [hX, putnam_2005_a2_pt]
    · exfalso
      have hnotTail : X ∉ tail := by
        intro hXt
        rcases (List.nodup_append.mp hnodupBig) with ⟨_hl, _ht, hdisj⟩
        exact (hdisj X hXmem X hXt) rfl
      exact hnotTail (by
        rw [putnam_2005_a2_rightTail_mem_iff]
        exact Or.inr (Or.inl hX))

private lemma putnam_2005_a2_cornerListTour_append_rightTail
    {n : ℕ} {startTop endTop : Bool} {l : List putnam_2005_a2_Point}
    (hl : putnam_2005_a2_cornerListTour n startTop (!endTop) l) :
    putnam_2005_a2_cornerListTour (n + 1) startTop endTop
      (l ++ putnam_2005_a2_rightTail n endTop) := by
  rcases hl with ⟨hperm, hchain, hhead, hlast⟩
  constructor
  · rw [putnam_2005_a2_boardList_succ]
    exact hperm.append (putnam_2005_a2_rightTail_perm n endTop)
  constructor
  · refine hchain.append (putnam_2005_a2_rightTail_chain n endTop) ?_
    intro x hx y hy
    have hx' : x = putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop)) := by
      simpa [hlast] using hx.symm
    have hy' :
        y = putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side (!endTop)) := by
      cases endTop <;>
        simpa [putnam_2005_a2_rightTail, putnam_2005_a2_side] using hy.symm
    subst x
    subst y
    exact putnam_2005_a2_unit_right_horizontal n (putnam_2005_a2_side (!endTop))
  constructor
  · have hlne : l ≠ [] := by
      intro h
      simp [h] at hhead
    simpa [List.head?_append_of_ne_nil l hlne] using hhead
  · cases endTop <;> simp [putnam_2005_a2_rightTail, putnam_2005_a2_pt,
      putnam_2005_a2_side]

private lemma putnam_2005_a2_corner_right_opposite_middle_edge
    {n : ℕ} {startTop endTop : Bool} {l : List putnam_2005_a2_Point}
    (hn : 1 < n)
    (hl : putnam_2005_a2_cornerListTour n startTop endTop l) :
    putnam_2005_a2_edgeIn
      (putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop)))
      (putnam_2005_a2_pt (n : ℤ) 2) l := by
  have hn' : 0 < n - 1 := by omega
  have htour :
      putnam_2005_a2_cornerListTour ((n - 1) + 1) startTop endTop l := by
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hl
  have h := putnam_2005_a2_corner_right_opposite_edges
    (n := n - 1) (startTop := startTop) (endTop := endTop) hn' htour
  have hmid := h.2
  have hcast : ((n - 1 : ℕ) : ℤ) + 1 = (n : ℤ) := by omega
  simpa [hcast] using hmid

private def putnam_2005_a2_rightDetourForward
    (n : ℕ) (endTop : Bool)
    (a b : List putnam_2005_a2_Point) : List putnam_2005_a2_Point :=
  a ++
    [putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop)),
      putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side (!endTop)),
      putnam_2005_a2_pt ((n : ℤ) + 1) 2,
      putnam_2005_a2_pt (n : ℤ) 2] ++
    b ++ [putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side endTop)]

private def putnam_2005_a2_rightDetourReverse
    (n : ℕ) (endTop : Bool)
    (a b : List putnam_2005_a2_Point) : List putnam_2005_a2_Point :=
  a ++
    [putnam_2005_a2_pt (n : ℤ) 2,
      putnam_2005_a2_pt ((n : ℤ) + 1) 2,
      putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side (!endTop)),
      putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop))] ++
    b ++ [putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side endTop)]

private lemma putnam_2005_a2_rightDetourForward_perm_append_tail
    (n : ℕ) (endTop : Bool) (a b : List putnam_2005_a2_Point) :
    (putnam_2005_a2_rightDetourForward n endTop a b).Perm
      ((a ++
        [putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop)),
          putnam_2005_a2_pt (n : ℤ) 2] ++ b) ++
        putnam_2005_a2_rightTail n endTop) := by
  let LO := putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop))
  let LM := putnam_2005_a2_pt (n : ℤ) 2
  let O := putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side (!endTop))
  let M := putnam_2005_a2_pt ((n : ℤ) + 1) 2
  let E := putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side endTop)
  have p :
      (([O, M] : List putnam_2005_a2_Point) ++ (LM :: b)).Perm
        ((LM :: b) ++ [O, M]) :=
    List.perm_append_comm
  have p2 := p.append_right [E]
  simpa [putnam_2005_a2_rightDetourForward, putnam_2005_a2_rightTail,
    LO, LM, O, M, E, List.append_assoc] using
    (p2.append_left (a ++ [LO]))

private lemma putnam_2005_a2_rightDetourReverse_perm_append_tail
    (n : ℕ) (endTop : Bool) (a b : List putnam_2005_a2_Point) :
    (putnam_2005_a2_rightDetourReverse n endTop a b).Perm
      ((a ++
        [putnam_2005_a2_pt (n : ℤ) 2,
          putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop))] ++ b) ++
        putnam_2005_a2_rightTail n endTop) := by
  let LO := putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop))
  let LM := putnam_2005_a2_pt (n : ℤ) 2
  let O := putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side (!endTop))
  let M := putnam_2005_a2_pt ((n : ℤ) + 1) 2
  let E := putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side endTop)
  have p :
      (([M, O] : List putnam_2005_a2_Point) ++ (LO :: b)).Perm
        ((LO :: b) ++ [M, O]) :=
    List.perm_append_comm
  have p2 := p.append_right [E]
  have pswap : ([M, O, E] : List putnam_2005_a2_Point).Perm [O, M, E] :=
    List.Perm.swap O M [E]
  have p3 :
      ((([M, O] : List putnam_2005_a2_Point) ++ (LO :: b)) ++ [E]).Perm
        ((LO :: b) ++ [O, M, E]) := by
    exact p2.trans
      (by
        simpa [List.append_assoc] using
          ((List.Perm.refl (LO :: b)).append pswap))
  simpa [putnam_2005_a2_rightDetourReverse, putnam_2005_a2_rightTail,
    LO, LM, O, M, E, List.append_assoc] using
    (p3.append_left (a ++ [LM]))

private lemma putnam_2005_a2_cornerListTour_rightDetourForward
    {n : ℕ} {startTop endTop : Bool}
    {a b : List putnam_2005_a2_Point}
    (hl : putnam_2005_a2_cornerListTour n startTop endTop
      (a ++
        [putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop)),
          putnam_2005_a2_pt (n : ℤ) 2] ++ b)) :
    putnam_2005_a2_cornerListTour (n + 1) startTop endTop
      (putnam_2005_a2_rightDetourForward n endTop a b) := by
  let LO := putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop))
  let LM := putnam_2005_a2_pt (n : ℤ) 2
  let O := putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side (!endTop))
  let M := putnam_2005_a2_pt ((n : ℤ) + 1) 2
  let E := putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side endTop)
  rcases hl with ⟨hperm, hchain, hhead, hlast⟩
  have hsmall :
      a ++ [LO, LM] ++ b =
        a ++
          [putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop)),
            putnam_2005_a2_pt (n : ℤ) 2] ++ b := by
    simp [LO, LM]
  have hperm_insert :
      (putnam_2005_a2_rightDetourForward n endTop a b).Perm
        ((a ++ [LO, LM] ++ b) ++ putnam_2005_a2_rightTail n endTop) := by
    have p :
        (([O, M] : List putnam_2005_a2_Point) ++ (LM :: b)).Perm
          ((LM :: b) ++ [O, M]) :=
      List.perm_append_comm
    have p2 := p.append_right [E]
    simpa [putnam_2005_a2_rightDetourForward, putnam_2005_a2_rightTail,
      LO, LM, O, M, E, List.append_assoc] using
      (p2.append_left (a ++ [LO]))
  constructor
  · rw [putnam_2005_a2_boardList_succ]
    have hpermSmall : (a ++ [LO, LM] ++ b).Perm (putnam_2005_a2_boardList n) := by
      simpa [hsmall] using hperm
    exact hperm_insert.trans
      (hpermSmall.append (putnam_2005_a2_rightTail_perm n endTop))
  constructor
  · have hchain_small : (a ++ LO :: LM :: b).IsChain putnam_2005_a2_unit := by
      simpa [hsmall] using hchain
    have hsplit := List.isChain_append_cons_cons.mp hchain_small
    rcases hsplit with ⟨hleft, _hLOLM, hright⟩
    have hprefix :
        (a ++ LO :: O :: M :: LM :: b).IsChain putnam_2005_a2_unit := by
      apply List.isChain_append_cons_cons.mpr
      constructor
      · exact hleft
      constructor
      · simpa [LO, O] using
          putnam_2005_a2_unit_right_horizontal n (putnam_2005_a2_side (!endTop))
      exact List.IsChain.cons_cons
        (by
          simpa [O, M] using
            putnam_2005_a2_unit_same_col_side_mid
              ((n : ℤ) + 1) (!endTop))
        (List.IsChain.cons_cons
          (by
            have h := putnam_2005_a2_unit_right_horizontal n (2 : ℤ)
            exact (putnam_2005_a2_unit_symm M LM).2 (by simpa [LM, M] using h))
          hright)
    have hchainBig :
        (a ++ LO :: O :: M :: LM :: b ++ [E]).IsChain putnam_2005_a2_unit := by
      refine hprefix.append (List.isChain_singleton E) ?_
      intro x hx y hy
      have hlast_eq :
          (a ++ LO :: O :: M :: LM :: b).getLast? =
            (a ++ LO :: LM :: b).getLast? := by
        rw [show a ++ LO :: O :: M :: LM :: b =
            (a ++ [LO, O, M]) ++ (LM :: b) by simp [List.append_assoc]]
        rw [show a ++ LO :: LM :: b =
            (a ++ [LO]) ++ (LM :: b) by simp [List.append_assoc]]
        rw [List.getLast?_append_of_ne_nil, List.getLast?_append_of_ne_nil]
        · simp
        · simp
      have hx' : x = putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side endTop) := by
        have hxsmall : x ∈ (a ++ LO :: LM :: b).getLast? := by
          simpa [hlast_eq] using hx
        have hlastSmall :
            (a ++ LO :: LM :: b).getLast? =
              some (putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side endTop)) := by
          simpa [hsmall] using hlast
        have hxopt :
            x ∈
              (some (putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side endTop)) :
                Option putnam_2005_a2_Point) := by
          simpa [hlastSmall] using hxsmall
        simpa using hxopt.symm
      have hy' : y = E := by
        simpa [E] using hy.symm
      subst x
      subst y
      simpa [E] using
        putnam_2005_a2_unit_right_horizontal n (putnam_2005_a2_side endTop)
    simpa [putnam_2005_a2_rightDetourForward, LO, LM, O, M, E,
      List.append_assoc] using hchainBig
  constructor
  · have hhead_eq :
        (a ++ LO :: O :: M :: LM :: b).head? =
          (a ++ LO :: LM :: b).head? := by
      rw [show a ++ LO :: O :: M :: LM :: b =
          (a ++ [LO]) ++ (O :: M :: LM :: b) by simp [List.append_assoc]]
      rw [show a ++ LO :: LM :: b =
          (a ++ [LO]) ++ (LM :: b) by simp [List.append_assoc]]
      rw [List.head?_append_of_ne_nil (a ++ [LO]) (by simp),
        List.head?_append_of_ne_nil (a ++ [LO]) (by simp)]
    simpa [putnam_2005_a2_rightDetourForward, LO, LM, O, M, E,
      hhead_eq, hsmall] using hhead
  · rw [show putnam_2005_a2_rightDetourForward n endTop a b =
        (a ++
          [putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop)),
            putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side (!endTop)),
            putnam_2005_a2_pt ((n : ℤ) + 1) 2,
            putnam_2005_a2_pt (n : ℤ) 2] ++ b) ++ [E] by
      simp [putnam_2005_a2_rightDetourForward, E, List.append_assoc]]
    simpa [E] using
      (List.getLast?_concat
        (l := a ++
          [putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop)),
            putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side (!endTop)),
            putnam_2005_a2_pt ((n : ℤ) + 1) 2,
            putnam_2005_a2_pt (n : ℤ) 2] ++ b)
        (a := E))

private lemma putnam_2005_a2_cornerListTour_rightDetourForward_inv
    {n : ℕ} {startTop endTop : Bool}
    {a b : List putnam_2005_a2_Point}
    (hn : 0 < n)
    (hl : putnam_2005_a2_cornerListTour (n + 1) startTop endTop
      (putnam_2005_a2_rightDetourForward n endTop a b)) :
    putnam_2005_a2_cornerListTour n startTop endTop
      (a ++
        [putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop)),
          putnam_2005_a2_pt (n : ℤ) 2] ++ b) := by
  let LO := putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop))
  let LM := putnam_2005_a2_pt (n : ℤ) 2
  let O := putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side (!endTop))
  let M := putnam_2005_a2_pt ((n : ℤ) + 1) 2
  let E := putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side endTop)
  let LE := putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side endTop)
  constructor
  · exact putnam_2005_a2_perm_of_perm_append_rightTail hl.1
      (putnam_2005_a2_rightDetourForward_perm_append_tail n endTop a b)
  constructor
  · have hchainBig :
        (a ++ LO :: O :: M :: LM :: b ++ [E]).IsChain
          putnam_2005_a2_unit := by
      simpa [putnam_2005_a2_rightDetourForward, LO, LM, O, M, E,
        List.append_assoc] using hl.2.1
    have hsplit := (List.isChain_append_cons_cons
      (R := putnam_2005_a2_unit)
      (l₁ := a) (b := LO) (c := O) (l₂ := M :: LM :: b ++ [E])).mp
      (by simpa [List.append_assoc] using hchainBig)
    rcases hsplit with ⟨hleft, _hLOO, hOtail⟩
    have hMtail : (M :: LM :: b ++ [E]).IsChain putnam_2005_a2_unit :=
      (List.isChain_cons_cons.mp hOtail).2
    have hLMtail : (LM :: b ++ [E]).IsChain putnam_2005_a2_unit :=
      (List.isChain_cons_cons.mp hMtail).2
    have hLMb : (LM :: b).IsChain putnam_2005_a2_unit := by
      have htmp : ((LM :: b) ++ [E]).IsChain putnam_2005_a2_unit := by
        simpa [List.append_assoc] using hLMtail
      exact List.IsChain.left_of_append htmp
    have hsmall :
        (a ++ LO :: LM :: b).IsChain putnam_2005_a2_unit := by
      apply List.isChain_append_cons_cons.mpr
      constructor
      · exact hleft
      constructor
      · simpa [LO, LM] using
          putnam_2005_a2_unit_same_col_side_mid
            (n : ℤ) (!endTop)
      · exact hLMb
    simpa [LO, LM, List.append_assoc] using hsmall
  constructor
  · have hhead_eq :
        (a ++ LO :: O :: M :: LM :: b).head? =
          (a ++ LO :: LM :: b).head? := by
      rw [show a ++ LO :: O :: M :: LM :: b =
          (a ++ [LO]) ++ (O :: M :: LM :: b) by simp [List.append_assoc]]
      rw [show a ++ LO :: LM :: b =
          (a ++ [LO]) ++ (LM :: b) by simp [List.append_assoc]]
      rw [List.head?_append_of_ne_nil (a ++ [LO]) (by simp),
        List.head?_append_of_ne_nil (a ++ [LO]) (by simp)]
    have hheadBig := hl.2.2.1
    simpa [putnam_2005_a2_rightDetourForward, LO, LM, O, M, E,
      hhead_eq, List.append_assoc] using hheadBig
  · have hnodupBig := putnam_2005_a2_cornerListTour_nodup hl
    have hMnotTail : M ∉ LM :: b := by
      intro hMtail
      have hnodup' :
          ((a ++ [LO, O, M]) ++ (LM :: b ++ [E])).Nodup := by
        simpa [putnam_2005_a2_rightDetourForward, LO, LM, O, M, E,
          List.append_assoc] using hnodupBig
      rcases List.nodup_append.mp hnodup' with ⟨_hpre, _hsuf, hdisj⟩
      exact (hdisj M (by simp) M (List.mem_append_left _ hMtail)) rfl
    have hsplitEnd := putnam_2005_a2_corner_right_endpoint_split
      (n := n) (startTop := startTop) (endTop := endTop) hn hl
    have hlastBody :
        (a ++ LO :: O :: M :: LM :: b).getLast? = some LE := by
      rcases hsplitEnd with hmid | hside
      · rcases hmid with ⟨r, hr⟩
        exfalso
        have hbody_eq : a ++ LO :: O :: M :: LM :: b = r ++ [M] := by
          apply List.append_cancel_right (bs := [E])
          simpa [putnam_2005_a2_rightDetourForward, LO, LM, O, M, E,
            List.append_assoc] using hr
        have htail_last : (LM :: b).getLast? = some M := by
          have hbody_last : (a ++ LO :: O :: M :: LM :: b).getLast? = some M := by
            rw [hbody_eq]
            simp
          have htail_ne : (LM :: b) ≠ [] := by simp
          rw [show a ++ LO :: O :: M :: LM :: b =
              (a ++ [LO, O, M]) ++ (LM :: b) by simp [List.append_assoc]] at hbody_last
          simpa [List.getLast?_append_of_ne_nil (a ++ [LO, O, M]) htail_ne]
            using hbody_last
        have hMmemTail : M ∈ LM :: b := by
          rcases List.getLast?_eq_some_iff.mp htail_last with ⟨u, hu⟩
          rw [hu]
          simp
        exact hMnotTail hMmemTail
      · rcases hside with ⟨r, hr⟩
        have hbody_eq : a ++ LO :: O :: M :: LM :: b = r ++ [LE] := by
          apply List.append_cancel_right (bs := [E])
          simpa [putnam_2005_a2_rightDetourForward, LO, LM, O, M, E, LE,
            List.append_assoc] using hr
        rw [hbody_eq]
        simp
    have hlast_eq :
        (a ++ LO :: O :: M :: LM :: b).getLast? =
          (a ++ LO :: LM :: b).getLast? := by
      rw [show a ++ LO :: O :: M :: LM :: b =
          (a ++ [LO, O, M]) ++ (LM :: b) by simp [List.append_assoc]]
      rw [show a ++ LO :: LM :: b =
          (a ++ [LO]) ++ (LM :: b) by simp [List.append_assoc]]
      rw [List.getLast?_append_of_ne_nil (a ++ [LO, O, M]) (by simp),
        List.getLast?_append_of_ne_nil (a ++ [LO]) (by simp)]
    have hsmallLast : (a ++ LO :: LM :: b).getLast? = some LE := by
      rw [← hlast_eq]
      exact hlastBody
    simpa [LO, LM, LE, List.append_assoc] using hsmallLast

private lemma putnam_2005_a2_cornerListTour_rightDetourReverse
    {n : ℕ} {startTop endTop : Bool}
    {a b : List putnam_2005_a2_Point}
    (hl : putnam_2005_a2_cornerListTour n startTop endTop
      (a ++
        [putnam_2005_a2_pt (n : ℤ) 2,
          putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop))] ++ b)) :
    putnam_2005_a2_cornerListTour (n + 1) startTop endTop
      (putnam_2005_a2_rightDetourReverse n endTop a b) := by
  let LO := putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop))
  let LM := putnam_2005_a2_pt (n : ℤ) 2
  let O := putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side (!endTop))
  let M := putnam_2005_a2_pt ((n : ℤ) + 1) 2
  let E := putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side endTop)
  rcases hl with ⟨hperm, hchain, hhead, hlast⟩
  have hsmall :
      a ++ [LM, LO] ++ b =
        a ++
          [putnam_2005_a2_pt (n : ℤ) 2,
            putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop))] ++ b := by
    simp [LO, LM]
  have hperm_insert :
      (putnam_2005_a2_rightDetourReverse n endTop a b).Perm
        ((a ++ [LM, LO] ++ b) ++ putnam_2005_a2_rightTail n endTop) := by
    have p :
        (([M, O] : List putnam_2005_a2_Point) ++ (LO :: b)).Perm
          ((LO :: b) ++ [M, O]) :=
      List.perm_append_comm
    have p2 := p.append_right [E]
    have pswap : ([M, O, E] : List putnam_2005_a2_Point).Perm [O, M, E] :=
      List.Perm.swap O M [E]
    have p3 :
        ((([M, O] : List putnam_2005_a2_Point) ++ (LO :: b)) ++ [E]).Perm
          ((LO :: b) ++ [O, M, E]) := by
      exact p2.trans
        (by
          simpa [List.append_assoc] using
            ((List.Perm.refl (LO :: b)).append pswap))
    simpa [putnam_2005_a2_rightDetourReverse, putnam_2005_a2_rightTail,
      LO, LM, O, M, E, List.append_assoc] using
      (p3.append_left (a ++ [LM]))
  constructor
  · rw [putnam_2005_a2_boardList_succ]
    have hpermSmall : (a ++ [LM, LO] ++ b).Perm (putnam_2005_a2_boardList n) := by
      simpa [hsmall] using hperm
    exact hperm_insert.trans
      (hpermSmall.append (putnam_2005_a2_rightTail_perm n endTop))
  constructor
  · have hchain_small : (a ++ LM :: LO :: b).IsChain putnam_2005_a2_unit := by
      simpa [hsmall] using hchain
    have hsplit := List.isChain_append_cons_cons.mp hchain_small
    rcases hsplit with ⟨hleft, _hLMLO, hright⟩
    have hprefix :
        (a ++ LM :: M :: O :: LO :: b).IsChain putnam_2005_a2_unit := by
      apply List.isChain_append_cons_cons.mpr
      constructor
      · exact hleft
      constructor
      · simpa [LM, M] using putnam_2005_a2_unit_right_horizontal n (2 : ℤ)
      exact List.IsChain.cons_cons
        (by
          have h := putnam_2005_a2_unit_same_col_side_mid
            ((n : ℤ) + 1) (!endTop)
          exact (putnam_2005_a2_unit_symm M O).2 (by simpa [O, M] using h))
        (List.IsChain.cons_cons
          (by
            have h := putnam_2005_a2_unit_right_horizontal n
              (putnam_2005_a2_side (!endTop))
            exact (putnam_2005_a2_unit_symm O LO).2 (by simpa [LO, O] using h))
          hright)
    have hchainBig :
        (a ++ LM :: M :: O :: LO :: b ++ [E]).IsChain putnam_2005_a2_unit := by
      refine hprefix.append (List.isChain_singleton E) ?_
      intro x hx y hy
      have hlast_eq :
          (a ++ LM :: M :: O :: LO :: b).getLast? =
            (a ++ LM :: LO :: b).getLast? := by
        rw [show a ++ LM :: M :: O :: LO :: b =
            (a ++ [LM, M, O]) ++ (LO :: b) by simp [List.append_assoc]]
        rw [show a ++ LM :: LO :: b =
            (a ++ [LM]) ++ (LO :: b) by simp [List.append_assoc]]
        rw [List.getLast?_append_of_ne_nil, List.getLast?_append_of_ne_nil]
        · simp
        · simp
      have hx' : x = putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side endTop) := by
        have hxsmall : x ∈ (a ++ LM :: LO :: b).getLast? := by
          simpa [hlast_eq] using hx
        have hlastSmall :
            (a ++ LM :: LO :: b).getLast? =
              some (putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side endTop)) := by
          simpa [hsmall] using hlast
        have hxopt :
            x ∈
              (some (putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side endTop)) :
                Option putnam_2005_a2_Point) := by
          simpa [hlastSmall] using hxsmall
        simpa using hxopt.symm
      have hy' : y = E := by
        simpa [E] using hy.symm
      subst x
      subst y
      simpa [E] using
        putnam_2005_a2_unit_right_horizontal n (putnam_2005_a2_side endTop)
    simpa [putnam_2005_a2_rightDetourReverse, LO, LM, O, M, E,
      List.append_assoc] using hchainBig
  constructor
  · have hhead_eq :
        (a ++ LM :: M :: O :: LO :: b).head? =
          (a ++ LM :: LO :: b).head? := by
      rw [show a ++ LM :: M :: O :: LO :: b =
          (a ++ [LM]) ++ (M :: O :: LO :: b) by simp [List.append_assoc]]
      rw [show a ++ LM :: LO :: b =
          (a ++ [LM]) ++ (LO :: b) by simp [List.append_assoc]]
      rw [List.head?_append_of_ne_nil (a ++ [LM]) (by simp),
        List.head?_append_of_ne_nil (a ++ [LM]) (by simp)]
    simpa [putnam_2005_a2_rightDetourReverse, LO, LM, O, M, E,
      hhead_eq, hsmall] using hhead
  · rw [show putnam_2005_a2_rightDetourReverse n endTop a b =
        (a ++
          [putnam_2005_a2_pt (n : ℤ) 2,
            putnam_2005_a2_pt ((n : ℤ) + 1) 2,
            putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side (!endTop)),
            putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop))] ++ b) ++ [E] by
      simp [putnam_2005_a2_rightDetourReverse, E, List.append_assoc]]
    simpa [E] using
      (List.getLast?_concat
        (l := a ++
          [putnam_2005_a2_pt (n : ℤ) 2,
            putnam_2005_a2_pt ((n : ℤ) + 1) 2,
            putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side (!endTop)),
            putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop))] ++ b)
        (a := E))

private lemma putnam_2005_a2_cornerListTour_rightDetourReverse_inv
    {n : ℕ} {startTop endTop : Bool}
    {a b : List putnam_2005_a2_Point}
    (hn : 0 < n)
    (hl : putnam_2005_a2_cornerListTour (n + 1) startTop endTop
      (putnam_2005_a2_rightDetourReverse n endTop a b)) :
    putnam_2005_a2_cornerListTour n startTop endTop
      (a ++
        [putnam_2005_a2_pt (n : ℤ) 2,
          putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop))] ++ b) := by
  let LO := putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop))
  let LM := putnam_2005_a2_pt (n : ℤ) 2
  let O := putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side (!endTop))
  let M := putnam_2005_a2_pt ((n : ℤ) + 1) 2
  let E := putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side endTop)
  let LE := putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side endTop)
  constructor
  · exact putnam_2005_a2_perm_of_perm_append_rightTail hl.1
      (putnam_2005_a2_rightDetourReverse_perm_append_tail n endTop a b)
  constructor
  · have hchainBig :
        (a ++ LM :: M :: O :: LO :: b ++ [E]).IsChain
          putnam_2005_a2_unit := by
      simpa [putnam_2005_a2_rightDetourReverse, LO, LM, O, M, E,
        List.append_assoc] using hl.2.1
    have hsplit := (List.isChain_append_cons_cons
      (R := putnam_2005_a2_unit)
      (l₁ := a) (b := LM) (c := M) (l₂ := O :: LO :: b ++ [E])).mp
      (by simpa [List.append_assoc] using hchainBig)
    rcases hsplit with ⟨hleft, _hLMM, hMtail⟩
    have hOtail : (O :: LO :: b ++ [E]).IsChain putnam_2005_a2_unit :=
      (List.isChain_cons_cons.mp hMtail).2
    have hLOtail : (LO :: b ++ [E]).IsChain putnam_2005_a2_unit :=
      (List.isChain_cons_cons.mp hOtail).2
    have hLOb : (LO :: b).IsChain putnam_2005_a2_unit := by
      have htmp : ((LO :: b) ++ [E]).IsChain putnam_2005_a2_unit := by
        simpa [List.append_assoc] using hLOtail
      exact List.IsChain.left_of_append htmp
    have hsmall :
        (a ++ LM :: LO :: b).IsChain putnam_2005_a2_unit := by
      apply List.isChain_append_cons_cons.mpr
      constructor
      · exact hleft
      constructor
      · have h := putnam_2005_a2_unit_same_col_side_mid
          (n : ℤ) (!endTop)
        exact (putnam_2005_a2_unit_symm LM LO).2 (by simpa [LO, LM] using h)
      · exact hLOb
    simpa [LO, LM, List.append_assoc] using hsmall
  constructor
  · have hhead_eq :
        (a ++ LM :: M :: O :: LO :: b).head? =
          (a ++ LM :: LO :: b).head? := by
      rw [show a ++ LM :: M :: O :: LO :: b =
          (a ++ [LM]) ++ (M :: O :: LO :: b) by simp [List.append_assoc]]
      rw [show a ++ LM :: LO :: b =
          (a ++ [LM]) ++ (LO :: b) by simp [List.append_assoc]]
      rw [List.head?_append_of_ne_nil (a ++ [LM]) (by simp),
        List.head?_append_of_ne_nil (a ++ [LM]) (by simp)]
    have hheadBig := hl.2.2.1
    simpa [putnam_2005_a2_rightDetourReverse, LO, LM, O, M, E,
      hhead_eq, List.append_assoc] using hheadBig
  · have hnodupBig := putnam_2005_a2_cornerListTour_nodup hl
    have hMnotTail : M ∉ O :: LO :: b := by
      intro hMtail
      have hnodup' :
          ((a ++ [LM, M]) ++ (O :: LO :: b ++ [E])).Nodup := by
        simpa [putnam_2005_a2_rightDetourReverse, LO, LM, O, M, E,
          List.append_assoc] using hnodupBig
      rcases List.nodup_append.mp hnodup' with ⟨_hpre, _hsuf, hdisj⟩
      exact (hdisj M (by simp) M (List.mem_append_left _ hMtail)) rfl
    have hsplitEnd := putnam_2005_a2_corner_right_endpoint_split
      (n := n) (startTop := startTop) (endTop := endTop) hn hl
    have hlastBody :
        (a ++ LM :: M :: O :: LO :: b).getLast? = some LE := by
      rcases hsplitEnd with hmid | hside
      · rcases hmid with ⟨r, hr⟩
        exfalso
        have hbody_eq : a ++ LM :: M :: O :: LO :: b = r ++ [M] := by
          apply List.append_cancel_right (bs := [E])
          simpa [putnam_2005_a2_rightDetourReverse, LO, LM, O, M, E,
            List.append_assoc] using hr
        have htail_last : (O :: LO :: b).getLast? = some M := by
          have hbody_last : (a ++ LM :: M :: O :: LO :: b).getLast? = some M := by
            rw [hbody_eq]
            simp
          have htail_ne : (O :: LO :: b) ≠ [] := by simp
          rw [show a ++ LM :: M :: O :: LO :: b =
              (a ++ [LM, M]) ++ (O :: LO :: b) by simp [List.append_assoc]] at hbody_last
          simpa [List.getLast?_append_of_ne_nil (a ++ [LM, M]) htail_ne]
            using hbody_last
        have hMmemTail : M ∈ O :: LO :: b := by
          rcases List.getLast?_eq_some_iff.mp htail_last with ⟨u, hu⟩
          rw [hu]
          simp
        exact hMnotTail hMmemTail
      · rcases hside with ⟨r, hr⟩
        have hbody_eq : a ++ LM :: M :: O :: LO :: b = r ++ [LE] := by
          apply List.append_cancel_right (bs := [E])
          simpa [putnam_2005_a2_rightDetourReverse, LO, LM, O, M, E, LE,
            List.append_assoc] using hr
        rw [hbody_eq]
        simp
    have hlast_eq :
        (a ++ LM :: M :: O :: LO :: b).getLast? =
          (a ++ LM :: LO :: b).getLast? := by
      rw [show a ++ LM :: M :: O :: LO :: b =
          (a ++ [LM, M, O]) ++ (LO :: b) by simp [List.append_assoc]]
      rw [show a ++ LM :: LO :: b =
          (a ++ [LM]) ++ (LO :: b) by simp [List.append_assoc]]
      rw [List.getLast?_append_of_ne_nil (a ++ [LM, M, O]) (by simp),
        List.getLast?_append_of_ne_nil (a ++ [LM]) (by simp)]
    have hsmallLast : (a ++ LM :: LO :: b).getLast? = some LE := by
      rw [← hlast_eq]
      exact hlastBody
    simpa [LO, LM, LE, List.append_assoc] using hsmallLast

private lemma putnam_2005_a2_corner_right_detour_cases
    {n : ℕ} {startTop endTop : Bool} {l r : List putnam_2005_a2_Point}
    (hn : 0 < n)
    (hl : putnam_2005_a2_cornerListTour (n + 1) startTop endTop l)
    (hr :
      l = r ++
        [putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side endTop),
          putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side endTop)]) :
    (∃ a b,
      l = putnam_2005_a2_rightDetourForward n endTop a b ∧
        putnam_2005_a2_cornerListTour n startTop endTop
          (a ++
            [putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop)),
              putnam_2005_a2_pt (n : ℤ) 2] ++ b)) ∨
      (∃ a b,
        l = putnam_2005_a2_rightDetourReverse n endTop a b ∧
          putnam_2005_a2_cornerListTour n startTop endTop
            (a ++
              [putnam_2005_a2_pt (n : ℤ) 2,
                putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop))] ++ b)) := by
  classical
  let LO := putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop))
  let LM := putnam_2005_a2_pt (n : ℤ) 2
  let LE := putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side endTop)
  let O := putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side (!endTop))
  let M := putnam_2005_a2_pt ((n : ℤ) + 1) 2
  let E := putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side endTop)
  have hnodup := putnam_2005_a2_cornerListTour_nodup hl
  have hlast : l.getLast? = some E := by
    simpa [E, putnam_2005_a2_pt] using hl.2.2.2
  have hOedges := putnam_2005_a2_corner_right_opposite_edges
    (n := n) (startTop := startTop) (endTop := endTop) hn hl
  have hOLO : putnam_2005_a2_edgeIn O LO l := by
    simpa [O, LO] using hOedges.1
  have hOM : putnam_2005_a2_edgeIn O M l := by
    simpa [O, M] using hOedges.2
  have hMmem : M ∈ l := putnam_2005_a2_edgeIn_right_mem hOM
  have hnotME : ¬ putnam_2005_a2_edgeIn M E l := by
    intro hME
    have hAdj := putnam_2005_a2_edgeIn_idx_adjacent hnodup hME
    have hEidx : l.idxOf E = l.length - 1 :=
      putnam_2005_a2_idxOf_getLast hnodup hlast
    have hLEidx : l.idxOf LE = l.length - 2 :=
      putnam_2005_a2_idxOf_penultimate hnodup (by simpa [LE, E] using hr)
    have hMlt : l.idxOf M < l.length :=
      List.idxOf_lt_length_of_mem hMmem
    have hLEmem : LE ∈ l := by
      rw [hr]
      simp [LE, E]
    have hLElt : l.idxOf LE < l.length :=
      List.idxOf_lt_length_of_mem hLEmem
    rcases hAdj with hMEidx | hEMidx
    · have hMidx : l.idxOf M = l.idxOf LE := by omega
      have hEq :
          l[l.idxOf M] = l[l.idxOf LE] :=
        ((List.Nodup.getElem_inj_iff hnodup
          (hi := hMlt) (hj := hLElt)).2 hMidx)
      have hMLE : M = LE := by
        calc
          M = l[l.idxOf M] := (List.getElem_idxOf hMlt).symm
          _ = l[l.idxOf LE] := hEq
          _ = LE := List.getElem_idxOf hLElt
      cases endTop <;>
        simp [M, LE, putnam_2005_a2_pt, putnam_2005_a2_side] at hMLE
    · omega
  have hMdrop : M ∈ l.dropLast := by
    apply List.mem_dropLast_of_mem_of_ne_getLast? hMmem
    intro hlastM
    rw [hlast] at hlastM
    have hMEq : M = E := Option.some.inj hlastM
    cases endTop <;>
      simp [M, E, putnam_2005_a2_pt, putnam_2005_a2_side] at hMEq
  have hMnext : l.idxOf M + 1 < l.length :=
    List.succ_idxOf_lt_length_of_mem_dropLast hMdrop
  have hMprev : 0 < l.idxOf M := by
    by_contra h
    have hzero : l.idxOf M = 0 := by omega
    have hM0 : l[0]? = some M := by
      simpa [hzero] using List.getElem?_idxOf hMmem
    have hheadM : l.head? = some M := by
      simpa [List.head?_eq_getElem?] using hM0
    have hhead := hl.2.2.1
    rw [hhead] at hheadM
    have hEq : M = putnam_2005_a2_pt 1 (putnam_2005_a2_side startTop) :=
      Option.some.inj hheadM.symm
    cases startTop <;> cases endTop <;>
      simp [M, putnam_2005_a2_pt, putnam_2005_a2_side] at hEq <;> omega
  have hneighM : ∀ Q, Q ∈ l → putnam_2005_a2_unit M Q →
      Q = O ∨ Q = LM ∨ Q = E := by
    intro Q hQmem hunit
    have hQboard : Q ∈ putnam_2005_a2_board (n + 1) :=
      putnam_2005_a2_cornerListTour_mem_board hl hQmem
    have hclass := putnam_2005_a2_neighbor_right_middle
      (n := n) hQboard (by simpa [M] using hunit)
    cases endTop
    · rcases hclass with hE | hO | hLM
      · exact Or.inr (Or.inr (by simpa [E, putnam_2005_a2_side] using hE))
      · exact Or.inl (by simpa [O, putnam_2005_a2_side] using hO)
      · exact Or.inr (Or.inl (by simpa [LM] using hLM))
    · rcases hclass with hO | hE | hLM
      · exact Or.inl (by simpa [O, putnam_2005_a2_side] using hO)
      · exact Or.inr (Or.inr (by simpa [E, putnam_2005_a2_side] using hE))
      · exact Or.inr (Or.inl (by simpa [LM] using hLM))
  have hMLM : putnam_2005_a2_edgeIn M LM l :=
    putnam_2005_a2_forced_edge_of_three_excluding
      hnodup hl.2.1 hMmem hMprev hMnext hneighM hnotME
  have hLOmem : LO ∈ l := putnam_2005_a2_edgeIn_right_mem hOLO
  have hOmem : O ∈ l := putnam_2005_a2_edgeIn_left_mem hOLO
  have hLMmem : LM ∈ l := putnam_2005_a2_edgeIn_right_mem hMLM
  have hLO_ne_M : LO ≠ M := by
    intro h
    cases endTop <;>
      simp [LO, M, putnam_2005_a2_pt, putnam_2005_a2_side] at h <;> omega
  have hO_ne_LM : O ≠ LM := by
    intro h
    cases endTop <;>
      simp [O, LM, putnam_2005_a2_pt, putnam_2005_a2_side] at h <;> omega
  have hLO_ne_M_idx : l.idxOf LO ≠ l.idxOf M := by
    intro hidx
    have hLOlt := List.idxOf_lt_length_of_mem hLOmem
    have hMlt := List.idxOf_lt_length_of_mem hMmem
    have hEq :
        l[l.idxOf LO] = l[l.idxOf M] :=
      ((List.Nodup.getElem_inj_iff hnodup
        (hi := hLOlt) (hj := hMlt)).2 hidx)
    exact hLO_ne_M (by
      calc
        LO = l[l.idxOf LO] := (List.getElem_idxOf hLOlt).symm
        _ = l[l.idxOf M] := hEq
        _ = M := List.getElem_idxOf hMlt)
  have hO_ne_LM_idx : l.idxOf O ≠ l.idxOf LM := by
    intro hidx
    have hOlt := List.idxOf_lt_length_of_mem hOmem
    have hLMlt := List.idxOf_lt_length_of_mem hLMmem
    have hEq :
        l[l.idxOf O] = l[l.idxOf LM] :=
      ((List.Nodup.getElem_inj_iff hnodup
        (hi := hOlt) (hj := hLMlt)).2 hidx)
    exact hO_ne_LM (by
      calc
        O = l[l.idxOf O] := (List.getElem_idxOf hOlt).symm
        _ = l[l.idxOf LM] := hEq
        _ = LM := List.getElem_idxOf hLMlt)
  rcases putnam_2005_a2_edgeIn_idx_adjacent hnodup hOLO with hO_LO | hLO_O <;>
    rcases putnam_2005_a2_edgeIn_idx_adjacent hnodup hOM with hO_M | hM_O
  · exfalso
    exact hLO_ne_M_idx (by omega)
  · -- M, O, LO; the old middle must precede M.
    rcases putnam_2005_a2_edgeIn_idx_adjacent hnodup hMLM with hM_LM | hLM_M
    · exfalso
      exact hO_ne_LM_idx (by omega)
    · rcases putnam_2005_a2_eq_append_four_of_idx
        hLMmem hMmem hOmem hLOmem hLM_M hM_O hO_LO with ⟨a, c, hshape⟩
      have hcLast : c.getLast? = some E := by
        by_cases hc : c = []
        · subst c
          rw [hshape] at hlast
          cases endTop <;>
            simp [LO, LM, O, M, E, putnam_2005_a2_pt,
              putnam_2005_a2_side, List.append_assoc] at hlast
        · have hshape' : l = (a ++ [LM, M, O, LO]) ++ c := by
            simpa [List.append_assoc] using hshape
          rw [hshape'] at hlast
          have hlast' : ((a ++ [LM, M, O, LO]) ++ c).getLast? = some E := hlast
          rw [List.getLast?_append_of_ne_nil (a ++ [LM, M, O, LO]) hc] at hlast'
          exact hlast'
      rcases List.getLast?_eq_some_iff.mp hcLast with ⟨b, hb⟩
      right
      refine ⟨a, b, ?_, ?_⟩
      · rw [hshape, hb]
        simp [putnam_2005_a2_rightDetourReverse, LO, LM, O, M, E,
          List.append_assoc]
      · have hbig :
            putnam_2005_a2_cornerListTour (n + 1) startTop endTop
              (putnam_2005_a2_rightDetourReverse n endTop a b) := by
          have hshapeBig :
              l = putnam_2005_a2_rightDetourReverse n endTop a b := by
            rw [hshape, hb]
            simp [putnam_2005_a2_rightDetourReverse, LO, LM, O, M, E,
              List.append_assoc]
          simpa [hshapeBig] using hl
        simpa [LO, LM, List.append_assoc] using
          putnam_2005_a2_cornerListTour_rightDetourReverse_inv
            (n := n) (startTop := startTop) (endTop := endTop)
            (a := a) (b := b) hn hbig
  · -- LO, O, M; the old middle must follow M.
    rcases putnam_2005_a2_edgeIn_idx_adjacent hnodup hMLM with hM_LM | hLM_M
    · rcases putnam_2005_a2_eq_append_four_of_idx
        hLOmem hOmem hMmem hLMmem hLO_O hO_M hM_LM with ⟨a, c, hshape⟩
      have hcLast : c.getLast? = some E := by
        by_cases hc : c = []
        · subst c
          rw [hshape] at hlast
          cases endTop <;>
            simp [LO, LM, O, M, E, putnam_2005_a2_pt,
              putnam_2005_a2_side, List.append_assoc] at hlast
        · have hshape' : l = (a ++ [LO, O, M, LM]) ++ c := by
            simpa [List.append_assoc] using hshape
          rw [hshape'] at hlast
          have hlast' : ((a ++ [LO, O, M, LM]) ++ c).getLast? = some E := hlast
          rw [List.getLast?_append_of_ne_nil (a ++ [LO, O, M, LM]) hc] at hlast'
          exact hlast'
      rcases List.getLast?_eq_some_iff.mp hcLast with ⟨b, hb⟩
      left
      refine ⟨a, b, ?_, ?_⟩
      · rw [hshape, hb]
        simp [putnam_2005_a2_rightDetourForward, LO, LM, O, M, E,
          List.append_assoc]
      · have hbig :
            putnam_2005_a2_cornerListTour (n + 1) startTop endTop
              (putnam_2005_a2_rightDetourForward n endTop a b) := by
          have hshapeBig :
              l = putnam_2005_a2_rightDetourForward n endTop a b := by
            rw [hshape, hb]
            simp [putnam_2005_a2_rightDetourForward, LO, LM, O, M, E,
              List.append_assoc]
          simpa [hshapeBig] using hl
        simpa [LO, LM, List.append_assoc] using
          putnam_2005_a2_cornerListTour_rightDetourForward_inv
            (n := n) (startTop := startTop) (endTop := endTop)
            (a := a) (b := b) hn hbig
    · exfalso
      exact hO_ne_LM_idx (by omega)
  · exfalso
    exact hLO_ne_M_idx (by omega)

private lemma putnam_2005_a2_idxOf_pair_left
    {P Q : putnam_2005_a2_Point} {a b l : List putnam_2005_a2_Point}
    (hnodup : l.Nodup) (hl : l = a ++ [P, Q] ++ b) :
    l.idxOf P = a.length := by
  classical
  have hnodup' : (a ++ P :: Q :: b).Nodup := by
    simpa [hl, List.append_assoc] using hnodup
  have hPnot : P ∉ a := by
    intro hP
    rcases (List.nodup_append.mp hnodup') with ⟨_ha, _ht, hdisj⟩
    exact (hdisj P hP P (by simp)) rfl
  rw [hl, show a ++ [P, Q] ++ b = a ++ P :: Q :: b by simp [List.append_assoc],
    List.idxOf_append_of_notMem hPnot, List.idxOf_cons_self]
  simp

private lemma putnam_2005_a2_idxOf_pair_right
    {P Q : putnam_2005_a2_Point} {a b l : List putnam_2005_a2_Point}
    (hnodup : l.Nodup) (hl : l = a ++ [P, Q] ++ b) :
    l.idxOf Q = a.length + 1 := by
  classical
  have hnodup' : ((a ++ [P]) ++ Q :: b).Nodup := by
    simpa [hl, List.append_assoc] using hnodup
  have hQnot : Q ∉ a ++ [P] := by
    intro hQ
    rcases (List.nodup_append.mp hnodup') with ⟨_ha, _ht, hdisj⟩
    exact (hdisj Q hQ Q (by simp)) rfl
  rw [hl, show a ++ [P, Q] ++ b = (a ++ [P]) ++ Q :: b by simp [List.append_assoc],
    List.idxOf_append_of_notMem hQnot, List.idxOf_cons_self]
  simp

private lemma putnam_2005_a2_pair_decomp_unique
    {P Q : putnam_2005_a2_Point}
    {a b a' b' l : List putnam_2005_a2_Point}
    (hnodup : l.Nodup)
    (hl : l = a ++ [P, Q] ++ b)
    (hl' : l = a' ++ [P, Q] ++ b') :
    a = a' ∧ b = b' := by
  classical
  have ha_len : a.length = a'.length := by
    have h1 := putnam_2005_a2_idxOf_pair_left (P := P) (Q := Q)
      (a := a) (b := b) hnodup hl
    have h2 := putnam_2005_a2_idxOf_pair_left (P := P) (Q := Q)
      (a := a') (b := b') hnodup hl'
    omega
  have htake : l.take a.length = a := by
    rw [hl]
    simpa [List.append_assoc] using
      (List.take_left (l₁ := a) (l₂ := [P, Q] ++ b))
  have htake' : l.take a'.length = a' := by
    rw [hl']
    simpa [List.append_assoc] using
      (List.take_left (l₁ := a') (l₂ := [P, Q] ++ b'))
  have ha : a = a' := by
    calc
      a = l.take a.length := htake.symm
      _ = l.take a'.length := by rw [ha_len]
      _ = a' := htake'
  have hb : b = b' := by
    have htail :
        [P, Q] ++ b = [P, Q] ++ b' := by
      apply List.append_cancel_left (as := a)
      calc
        a ++ ([P, Q] ++ b) = l := by
          rw [hl]
          simp [List.append_assoc]
        _ = a' ++ ([P, Q] ++ b') := by
          rw [hl']
          simp [List.append_assoc]
        _ = a ++ ([P, Q] ++ b') := by rw [ha]
    exact List.append_cancel_left (as := [P, Q]) htail
  exact ⟨ha, hb⟩

private lemma putnam_2005_a2_pair_decomp_forward_reverse_false
    {P Q : putnam_2005_a2_Point}
    {a b a' b' l : List putnam_2005_a2_Point}
    (hnodup : l.Nodup)
    (hl : l = a ++ [P, Q] ++ b)
    (hl' : l = a' ++ [Q, P] ++ b') :
    False := by
  have hPQ_left := putnam_2005_a2_idxOf_pair_left (P := P) (Q := Q)
    (a := a) (b := b) hnodup hl
  have hPQ_right := putnam_2005_a2_idxOf_pair_right (P := P) (Q := Q)
    (a := a) (b := b) hnodup hl
  have hQP_left := putnam_2005_a2_idxOf_pair_left (P := Q) (Q := P)
    (a := a') (b := b') hnodup hl'
  have hQP_right := putnam_2005_a2_idxOf_pair_right (P := Q) (Q := P)
    (a := a') (b := b') hnodup hl'
  omega

private structure putnam_2005_a2_DetourData where
  forward : Bool
  left : List putnam_2005_a2_Point
  right : List putnam_2005_a2_Point

private def putnam_2005_a2_detourSmallList
    (n : ℕ) (endTop : Bool) (d : putnam_2005_a2_DetourData) :
    List putnam_2005_a2_Point :=
  let LO := putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop))
  let LM := putnam_2005_a2_pt (n : ℤ) 2
  if d.forward then
    d.left ++ [LO, LM] ++ d.right
  else
    d.left ++ [LM, LO] ++ d.right

private def putnam_2005_a2_detourBigList
    (n : ℕ) (endTop : Bool) (d : putnam_2005_a2_DetourData) :
    List putnam_2005_a2_Point :=
  if d.forward then
    putnam_2005_a2_rightDetourForward n endTop d.left d.right
  else
    putnam_2005_a2_rightDetourReverse n endTop d.left d.right

private def putnam_2005_a2_detourDataSet
    (n : ℕ) (startTop endTop : Bool) :
    Set putnam_2005_a2_DetourData :=
  {d | putnam_2005_a2_cornerListTour n startTop endTop
      (putnam_2005_a2_detourSmallList n endTop d)}

private def putnam_2005_a2_middleSet
    (n : ℕ) (startTop endTop : Bool) :
    Set (List putnam_2005_a2_Point) :=
  {l | putnam_2005_a2_cornerListTour (n + 1) startTop endTop l ∧
      ∃ r,
        l = r ++
          [putnam_2005_a2_pt ((n : ℤ) + 1) 2,
            putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side endTop)]}

private def putnam_2005_a2_sideSet
    (n : ℕ) (startTop endTop : Bool) :
    Set (List putnam_2005_a2_Point) :=
  {l | putnam_2005_a2_cornerListTour (n + 1) startTop endTop l ∧
      ∃ r,
        l = r ++
          [putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side endTop),
            putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side endTop)]}

private def putnam_2005_a2_oldPart (n : ℕ)
    (l : List putnam_2005_a2_Point) : List putnam_2005_a2_Point :=
  l.filter fun P ↦ decide (P.1 ≤ (n : ℤ))

private lemma putnam_2005_a2_new_col_not_board
    {n : ℕ} {y : ℤ} (hy : y ∈ Icc (1 : ℤ) 3) :
    putnam_2005_a2_pt ((n : ℤ) + 1) y ∉ putnam_2005_a2_board n := by
  intro h
  unfold putnam_2005_a2_board at h
  change ((n : ℤ) + 1) ∈ Icc (1 : ℤ) (n : ℤ) ∧ y ∈ Icc (1 : ℤ) 3 at h
  have hx : (n : ℤ) + 1 ≤ (n : ℤ) := h.1.2
  omega

private lemma putnam_2005_a2_oldPart_of_corner
    {n : ℕ} {startTop endTop : Bool} {l : List putnam_2005_a2_Point}
    (hl : putnam_2005_a2_cornerListTour n startTop endTop l) :
    putnam_2005_a2_oldPart n l = l := by
  unfold putnam_2005_a2_oldPart
  apply List.filter_eq_self.mpr
  intro P hP
  have hboard := putnam_2005_a2_cornerListTour_mem_board hl hP
  rcases P with ⟨x, y⟩
  unfold putnam_2005_a2_board at hboard
  change x ∈ Icc (1 : ℤ) (n : ℤ) ∧ y ∈ Icc (1 : ℤ) 3 at hboard
  simp [hboard.1.2]

private lemma putnam_2005_a2_oldPart_rightDetourForward
    {n : ℕ} {startTop endTop : Bool} {a b : List putnam_2005_a2_Point}
    (hl : putnam_2005_a2_cornerListTour n startTop endTop
      (a ++
        [putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop)),
          putnam_2005_a2_pt (n : ℤ) 2] ++ b)) :
    putnam_2005_a2_oldPart n
        (putnam_2005_a2_rightDetourForward n endTop a b) =
      a ++
        [putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop)),
          putnam_2005_a2_pt (n : ℤ) 2] ++ b := by
  let LO := putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop))
  let LM := putnam_2005_a2_pt (n : ℤ) 2
  let O := putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side (!endTop))
  let M := putnam_2005_a2_pt ((n : ℤ) + 1) 2
  let E := putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side endTop)
  have hsmall :
      putnam_2005_a2_oldPart n (a ++ [LO, LM] ++ b) =
        a ++ [LO, LM] ++ b := by
    exact putnam_2005_a2_oldPart_of_corner (by simpa [LO, LM] using hl)
  calc
    putnam_2005_a2_oldPart n
        (putnam_2005_a2_rightDetourForward n endTop a b) =
      putnam_2005_a2_oldPart n (a ++ [LO, LM] ++ b) := by
        simp [putnam_2005_a2_oldPart, putnam_2005_a2_rightDetourForward,
          LO, LM, O, M, E, putnam_2005_a2_pt, List.filter_append,
          List.append_assoc]
    _ = a ++ [LO, LM] ++ b := hsmall

private lemma putnam_2005_a2_oldPart_rightDetourReverse
    {n : ℕ} {startTop endTop : Bool} {a b : List putnam_2005_a2_Point}
    (hl : putnam_2005_a2_cornerListTour n startTop endTop
      (a ++
        [putnam_2005_a2_pt (n : ℤ) 2,
          putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop))] ++ b)) :
    putnam_2005_a2_oldPart n
        (putnam_2005_a2_rightDetourReverse n endTop a b) =
      a ++
        [putnam_2005_a2_pt (n : ℤ) 2,
          putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop))] ++ b := by
  let LO := putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop))
  let LM := putnam_2005_a2_pt (n : ℤ) 2
  let O := putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side (!endTop))
  let M := putnam_2005_a2_pt ((n : ℤ) + 1) 2
  let E := putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side endTop)
  have hsmall :
      putnam_2005_a2_oldPart n (a ++ [LM, LO] ++ b) =
        a ++ [LM, LO] ++ b := by
    exact putnam_2005_a2_oldPart_of_corner (by simpa [LO, LM] using hl)
  calc
    putnam_2005_a2_oldPart n
        (putnam_2005_a2_rightDetourReverse n endTop a b) =
      putnam_2005_a2_oldPart n (a ++ [LM, LO] ++ b) := by
        simp [putnam_2005_a2_oldPart, putnam_2005_a2_rightDetourReverse,
          LO, LM, O, M, E, putnam_2005_a2_pt, List.filter_append,
          List.append_assoc]
    _ = a ++ [LM, LO] ++ b := hsmall

private lemma putnam_2005_a2_rightDetourForward_side
    {n : ℕ} {startTop endTop : Bool} {a b : List putnam_2005_a2_Point}
    (hl : putnam_2005_a2_cornerListTour n startTop endTop
      (a ++
        [putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop)),
          putnam_2005_a2_pt (n : ℤ) 2] ++ b)) :
    ∃ r,
      putnam_2005_a2_rightDetourForward n endTop a b =
        r ++
          [putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side endTop),
            putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side endTop)] := by
  let LO := putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop))
  let LM := putnam_2005_a2_pt (n : ℤ) 2
  let LE := putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side endTop)
  let O := putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side (!endTop))
  let M := putnam_2005_a2_pt ((n : ℤ) + 1) 2
  let E := putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side endTop)
  have hlast : (a ++ [LO, LM] ++ b).getLast? = some LE := by
    simpa [LO, LM, LE] using hl.2.2.2
  have hbne : b ≠ [] := by
    intro hb
    subst b
    cases endTop <;>
      simp [LO, LM, LE, putnam_2005_a2_pt, putnam_2005_a2_side,
        List.append_assoc] at hlast
  have hbLast : b.getLast? = some LE := by
    have hlast' : ((a ++ [LO, LM]) ++ b).getLast? = some LE := by
      simpa [List.append_assoc] using hlast
    rw [List.getLast?_append_of_ne_nil (a ++ [LO, LM]) hbne] at hlast'
    exact hlast'
  rcases List.getLast?_eq_some_iff.mp hbLast with ⟨c, hc⟩
  refine ⟨a ++ [LO, O, M, LM] ++ c, ?_⟩
  rw [hc]
  simp [putnam_2005_a2_rightDetourForward, LO, LM, LE, O, M, E,
    List.append_assoc]

private lemma putnam_2005_a2_rightDetourReverse_side
    {n : ℕ} {startTop endTop : Bool} {a b : List putnam_2005_a2_Point}
    (hl : putnam_2005_a2_cornerListTour n startTop endTop
      (a ++
        [putnam_2005_a2_pt (n : ℤ) 2,
          putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop))] ++ b)) :
    ∃ r,
      putnam_2005_a2_rightDetourReverse n endTop a b =
        r ++
          [putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side endTop),
            putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side endTop)] := by
  let LO := putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop))
  let LM := putnam_2005_a2_pt (n : ℤ) 2
  let LE := putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side endTop)
  let O := putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side (!endTop))
  let M := putnam_2005_a2_pt ((n : ℤ) + 1) 2
  let E := putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side endTop)
  have hlast : (a ++ [LM, LO] ++ b).getLast? = some LE := by
    simpa [LO, LM, LE] using hl.2.2.2
  have hbne : b ≠ [] := by
    intro hb
    subst b
    cases endTop <;>
      simp [LO, LM, LE, putnam_2005_a2_pt, putnam_2005_a2_side,
        List.append_assoc] at hlast
  have hbLast : b.getLast? = some LE := by
    have hlast' : ((a ++ [LM, LO]) ++ b).getLast? = some LE := by
      simpa [List.append_assoc] using hlast
    rw [List.getLast?_append_of_ne_nil (a ++ [LM, LO]) hbne] at hlast'
    exact hlast'
  rcases List.getLast?_eq_some_iff.mp hbLast with ⟨c, hc⟩
  refine ⟨a ++ [LM, M, O, LO] ++ c, ?_⟩
  rw [hc]
  simp [putnam_2005_a2_rightDetourReverse, LO, LM, LE, O, M, E,
    List.append_assoc]

private lemma putnam_2005_a2_detour_decomp_exists
    {n : ℕ} {startTop endTop : Bool} {l : List putnam_2005_a2_Point}
    (hn : 1 < n)
    (hl : putnam_2005_a2_cornerListTour n startTop endTop l) :
    ∃ d : putnam_2005_a2_DetourData,
      putnam_2005_a2_detourSmallList n endTop d = l ∧
        d ∈ putnam_2005_a2_detourDataSet n startTop endTop := by
  classical
  let LO := putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side (!endTop))
  let LM := putnam_2005_a2_pt (n : ℤ) 2
  have hedge : putnam_2005_a2_edgeIn LO LM l := by
    simpa [LO, LM] using
      putnam_2005_a2_corner_right_opposite_middle_edge
        (n := n) (startTop := startTop) (endTop := endTop) hn hl
  have hnodup := putnam_2005_a2_cornerListTour_nodup hl
  have hLOmem : LO ∈ l := putnam_2005_a2_edgeIn_left_mem hedge
  have hLMmem : LM ∈ l := putnam_2005_a2_edgeIn_right_mem hedge
  rcases putnam_2005_a2_edgeIn_idx_adjacent hnodup hedge with hLOLM | hLMLO
  · rcases putnam_2005_a2_eq_append_two_of_idx hLOmem hLMmem hLOLM with
      ⟨a, b, hshape⟩
    refine ⟨⟨true, a, b⟩, ?_, ?_⟩
    · simpa [putnam_2005_a2_detourSmallList, LO, LM] using hshape.symm
    · change putnam_2005_a2_cornerListTour n startTop endTop
        (putnam_2005_a2_detourSmallList n endTop ⟨true, a, b⟩)
      simpa [putnam_2005_a2_detourSmallList, LO, LM, hshape] using hl
  · rcases putnam_2005_a2_eq_append_two_of_idx hLMmem hLOmem hLMLO with
      ⟨a, b, hshape⟩
    refine ⟨⟨false, a, b⟩, ?_, ?_⟩
    · simpa [putnam_2005_a2_detourSmallList, LO, LM] using hshape.symm
    · change putnam_2005_a2_cornerListTour n startTop endTop
        (putnam_2005_a2_detourSmallList n endTop ⟨false, a, b⟩)
      simpa [putnam_2005_a2_detourSmallList, LO, LM, hshape] using hl

private lemma putnam_2005_a2_detourData_small_bijective
    {n : ℕ} {startTop endTop : Bool} (hn : 1 < n) :
    Function.Bijective
      (fun d : putnam_2005_a2_detourDataSet n startTop endTop ↦
        (⟨putnam_2005_a2_detourSmallList n endTop d.1, d.2⟩ :
          putnam_2005_a2_cornerListTourSet n startTop endTop)) := by
  classical
  constructor
  · intro x y hxy
    rcases x with ⟨dx, hdx⟩
    rcases y with ⟨dy, hdy⟩
    apply Subtype.ext
    dsimp at hxy
    have hlist : putnam_2005_a2_detourSmallList n endTop dx =
        putnam_2005_a2_detourSmallList n endTop dy :=
      congrArg Subtype.val hxy
    have hnodup := putnam_2005_a2_cornerListTour_nodup hdx
    rcases dx with ⟨fx, ax, bx⟩
    rcases dy with ⟨fy, ay, cy⟩
    cases fx <;> cases fy
    · dsimp [putnam_2005_a2_detourSmallList] at hlist hdx hdy ⊢
      rcases putnam_2005_a2_pair_decomp_unique hnodup rfl hlist with
        ⟨ha, hb⟩
      change ax = ay at ha
      change bx = cy at hb
      cases ha
      cases hb
      rfl
    · dsimp [putnam_2005_a2_detourSmallList] at hlist hdx hdy
      exfalso
      exact putnam_2005_a2_pair_decomp_forward_reverse_false hnodup rfl hlist
    · dsimp [putnam_2005_a2_detourSmallList] at hlist hdx hdy
      exfalso
      exact putnam_2005_a2_pair_decomp_forward_reverse_false hnodup rfl hlist
    · dsimp [putnam_2005_a2_detourSmallList] at hlist hdx hdy ⊢
      rcases putnam_2005_a2_pair_decomp_unique hnodup rfl hlist with
        ⟨ha, hb⟩
      change ax = ay at ha
      change bx = cy at hb
      cases ha
      cases hb
      rfl
  · intro l
    rcases putnam_2005_a2_detour_decomp_exists (n := n)
        (startTop := startTop) (endTop := endTop) hn l.2 with
      ⟨d, hdlist, hd⟩
    refine ⟨⟨d, hd⟩, ?_⟩
    apply Subtype.ext
    exact hdlist

private lemma putnam_2005_a2_detourData_side_bijective
    {n : ℕ} {startTop endTop : Bool} (hn : 1 < n) :
    Function.Bijective
      (fun d : putnam_2005_a2_detourDataSet n startTop endTop ↦
        (⟨putnam_2005_a2_detourBigList n endTop d.1, by
          rcases d with ⟨⟨forward, a, b⟩, hd⟩
          cases forward
          · change putnam_2005_a2_cornerListTour n startTop endTop
              (putnam_2005_a2_detourSmallList n endTop ⟨false, a, b⟩) at hd
            constructor
            · exact putnam_2005_a2_cornerListTour_rightDetourReverse
                (by simpa [putnam_2005_a2_detourSmallList] using hd)
            · exact putnam_2005_a2_rightDetourReverse_side
                (by simpa [putnam_2005_a2_detourSmallList] using hd)
          · change putnam_2005_a2_cornerListTour n startTop endTop
              (putnam_2005_a2_detourSmallList n endTop ⟨true, a, b⟩) at hd
            constructor
            · exact putnam_2005_a2_cornerListTour_rightDetourForward
                (by simpa [putnam_2005_a2_detourSmallList] using hd)
            · exact putnam_2005_a2_rightDetourForward_side
                (by simpa [putnam_2005_a2_detourSmallList] using hd)⟩ :
          putnam_2005_a2_sideSet n startTop endTop)) := by
  classical
  constructor
  · intro x y hxy
    rcases x with ⟨dx, hdx⟩
    rcases y with ⟨dy, hdy⟩
    apply Subtype.ext
    dsimp at hxy
    have hbig : putnam_2005_a2_detourBigList n endTop dx =
        putnam_2005_a2_detourBigList n endTop dy :=
      congrArg Subtype.val hxy
    have hsmall :
        putnam_2005_a2_detourSmallList n endTop dx =
          putnam_2005_a2_detourSmallList n endTop dy := by
      have hold := congrArg (putnam_2005_a2_oldPart n) hbig
      rcases dx with ⟨fx, ax, bx⟩
      rcases dy with ⟨fy, ay, cy⟩
      cases fx <;> cases fy
      · dsimp [putnam_2005_a2_detourDataSet, putnam_2005_a2_detourBigList,
          putnam_2005_a2_detourSmallList] at hdx hdy hold ⊢
        simpa [putnam_2005_a2_oldPart_rightDetourReverse hdx,
          putnam_2005_a2_oldPart_rightDetourReverse hdy] using hold
      · dsimp [putnam_2005_a2_detourDataSet, putnam_2005_a2_detourBigList,
          putnam_2005_a2_detourSmallList] at hdx hdy hold ⊢
        simpa [putnam_2005_a2_oldPart_rightDetourReverse hdx,
          putnam_2005_a2_oldPart_rightDetourForward hdy] using hold
      · dsimp [putnam_2005_a2_detourDataSet, putnam_2005_a2_detourBigList,
          putnam_2005_a2_detourSmallList] at hdx hdy hold ⊢
        simpa [putnam_2005_a2_oldPart_rightDetourForward hdx,
          putnam_2005_a2_oldPart_rightDetourReverse hdy] using hold
      · dsimp [putnam_2005_a2_detourDataSet, putnam_2005_a2_detourBigList,
          putnam_2005_a2_detourSmallList] at hdx hdy hold ⊢
        simpa [putnam_2005_a2_oldPart_rightDetourForward hdx,
          putnam_2005_a2_oldPart_rightDetourForward hdy] using hold
    have hsmallSubtype :
        (⟨putnam_2005_a2_detourSmallList n endTop dx, hdx⟩ :
          putnam_2005_a2_cornerListTourSet n startTop endTop) =
        ⟨putnam_2005_a2_detourSmallList n endTop dy, hdy⟩ := by
      exact Subtype.ext hsmall
    exact congrArg Subtype.val
      ((putnam_2005_a2_detourData_small_bijective
        (n := n) (startTop := startTop) (endTop := endTop)
        hn).1 hsmallSubtype)
  · intro l
    rcases l with ⟨l, hl, hside⟩
    rcases hside with ⟨r, hr⟩
    rcases putnam_2005_a2_corner_right_detour_cases
        (n := n) (startTop := startTop) (endTop := endTop)
        (l := l) (r := r) (by omega : 0 < n) hl hr with
      hforward | hreverse
    · rcases hforward with ⟨a, b, hshape, hsmall⟩
      refine ⟨⟨⟨true, a, b⟩, ?_⟩, ?_⟩
      · simpa [putnam_2005_a2_detourDataSet, putnam_2005_a2_detourSmallList] using hsmall
      · apply Subtype.ext
        simpa [putnam_2005_a2_detourBigList] using hshape.symm
    · rcases hreverse with ⟨a, b, hshape, hsmall⟩
      refine ⟨⟨⟨false, a, b⟩, ?_⟩, ?_⟩
      · simpa [putnam_2005_a2_detourDataSet, putnam_2005_a2_detourSmallList] using hsmall
      · apply Subtype.ext
        simpa [putnam_2005_a2_detourBigList] using hshape.symm

private lemma putnam_2005_a2_middle_bijective
    {n : ℕ} {startTop endTop : Bool} (hn : 0 < n) :
    Function.Bijective
      (fun l : putnam_2005_a2_cornerListTourSet n startTop (!endTop) ↦
        (⟨l.1 ++ putnam_2005_a2_rightTail n endTop, by
          constructor
          · exact putnam_2005_a2_cornerListTour_append_rightTail l.2
          · refine ⟨l.1 ++
              [putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side (!endTop))], ?_⟩
            cases endTop <;>
              simp [putnam_2005_a2_rightTail, putnam_2005_a2_pt,
                putnam_2005_a2_side, List.append_assoc]⟩ :
          putnam_2005_a2_middleSet n startTop endTop)) := by
  classical
  constructor
  · intro x y hxy
    apply Subtype.ext
    have hlist := congrArg Subtype.val hxy
    exact List.append_cancel_right hlist
  · intro l
    rcases l with ⟨l, hl, hmiddle⟩
    rcases hmiddle with ⟨r, hr⟩
    rcases putnam_2005_a2_corner_rightTail_of_endpoint_middle
        (n := n) (startTop := startTop) (endTop := endTop)
        (l := l) (r := r) hn hl hr with
      ⟨s, hs⟩
    have hsmall :
        putnam_2005_a2_cornerListTour n startTop (!endTop) s := by
      have hbig :
          putnam_2005_a2_cornerListTour (n + 1) startTop endTop
            (s ++ putnam_2005_a2_rightTail n endTop) := by
        simpa [hs] using hl
      exact putnam_2005_a2_cornerListTour_append_rightTail_inv hn hbig
    refine ⟨⟨s, hsmall⟩, ?_⟩
    apply Subtype.ext
    exact hs.symm

private lemma putnam_2005_a2_corner_big_split
    {n : ℕ} {startTop endTop : Bool} (hn : 0 < n) :
    putnam_2005_a2_cornerListTourSet (n + 1) startTop endTop =
      putnam_2005_a2_middleSet n startTop endTop ∪
        putnam_2005_a2_sideSet n startTop endTop := by
  ext l
  constructor
  · intro hl
    rcases putnam_2005_a2_corner_right_endpoint_split
        (n := n) (startTop := startTop) (endTop := endTop) hn hl with
      hmiddle | hside
    · exact Or.inl ⟨hl, hmiddle⟩
    · exact Or.inr ⟨hl, hside⟩
  · rintro (⟨hl, _⟩ | ⟨hl, _⟩) <;> exact hl

private lemma putnam_2005_a2_middle_side_disjoint
    {n : ℕ} {startTop endTop : Bool} :
    Disjoint (putnam_2005_a2_middleSet n startTop endTop)
      (putnam_2005_a2_sideSet n startTop endTop) := by
  rw [Set.disjoint_left]
  intro l hmiddle hside
  rcases hmiddle with ⟨hl, hmid⟩
  rcases hside with ⟨_hl', hsid⟩
  rcases hmid with ⟨rm, hm⟩
  rcases hsid with ⟨rs, hs⟩
  let M := putnam_2005_a2_pt ((n : ℤ) + 1) 2
  let LE := putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side endTop)
  let E := putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side endTop)
  have hnodup := putnam_2005_a2_cornerListTour_nodup hl
  have hMidx : l.idxOf M = l.length - 2 :=
    putnam_2005_a2_idxOf_penultimate hnodup (by simpa [M, E] using hm)
  have hLEidx : l.idxOf LE = l.length - 2 :=
    putnam_2005_a2_idxOf_penultimate hnodup (by simpa [LE, E] using hs)
  have hMmem : M ∈ l := by
    rw [hm]
    simp [M, E]
  have hLEmem : LE ∈ l := by
    rw [hs]
    simp [LE, E]
  have hMlt := List.idxOf_lt_length_of_mem hMmem
  have hLElt := List.idxOf_lt_length_of_mem hLEmem
  have hEq :
      l[l.idxOf M] = l[l.idxOf LE] :=
    ((List.Nodup.getElem_inj_iff hnodup
      (hi := hMlt) (hj := hLElt)).2 (by omega))
  have hMLE : M = LE := by
    calc
      M = l[l.idxOf M] := (List.getElem_idxOf hMlt).symm
      _ = l[l.idxOf LE] := hEq
      _ = LE := List.getElem_idxOf hLElt
  cases endTop <;>
    simp [M, LE, putnam_2005_a2_pt, putnam_2005_a2_side] at hMLE

private lemma putnam_2005_a2_middle_encard
    {n : ℕ} {startTop endTop : Bool} (hn : 0 < n) :
    (putnam_2005_a2_middleSet n startTop endTop).encard =
      (putnam_2005_a2_cornerListTourSet n startTop (!endTop)).encard := by
  exact (Set.encard_congr
    (Equiv.ofBijective
      (fun l : putnam_2005_a2_cornerListTourSet n startTop (!endTop) ↦
        (⟨l.1 ++ putnam_2005_a2_rightTail n endTop, by
          constructor
          · exact putnam_2005_a2_cornerListTour_append_rightTail l.2
          · refine ⟨l.1 ++
              [putnam_2005_a2_pt ((n : ℤ) + 1) (putnam_2005_a2_side (!endTop))], ?_⟩
            cases endTop <;>
              simp [putnam_2005_a2_rightTail, putnam_2005_a2_pt,
                putnam_2005_a2_side, List.append_assoc]⟩ :
          putnam_2005_a2_middleSet n startTop endTop))
      (putnam_2005_a2_middle_bijective (n := n)
        (startTop := startTop) (endTop := endTop) hn))).symm

private lemma putnam_2005_a2_side_encard
    {n : ℕ} {startTop endTop : Bool} (hn : 1 < n) :
    (putnam_2005_a2_sideSet n startTop endTop).encard =
      (putnam_2005_a2_cornerListTourSet n startTop endTop).encard := by
  have hside :
      (putnam_2005_a2_detourDataSet n startTop endTop).encard =
        (putnam_2005_a2_sideSet n startTop endTop).encard :=
    Set.encard_congr
      (Equiv.ofBijective
        (fun d : putnam_2005_a2_detourDataSet n startTop endTop ↦
          (⟨putnam_2005_a2_detourBigList n endTop d.1, by
            rcases d with ⟨⟨forward, a, b⟩, hd⟩
            cases forward
            · change putnam_2005_a2_cornerListTour n startTop endTop
                (putnam_2005_a2_detourSmallList n endTop ⟨false, a, b⟩) at hd
              constructor
              · exact putnam_2005_a2_cornerListTour_rightDetourReverse
                  (by simpa [putnam_2005_a2_detourSmallList] using hd)
              · exact putnam_2005_a2_rightDetourReverse_side
                  (by simpa [putnam_2005_a2_detourSmallList] using hd)
            · change putnam_2005_a2_cornerListTour n startTop endTop
                (putnam_2005_a2_detourSmallList n endTop ⟨true, a, b⟩) at hd
              constructor
              · exact putnam_2005_a2_cornerListTour_rightDetourForward
                  (by simpa [putnam_2005_a2_detourSmallList] using hd)
              · exact putnam_2005_a2_rightDetourForward_side
                  (by simpa [putnam_2005_a2_detourSmallList] using hd)⟩ :
            putnam_2005_a2_sideSet n startTop endTop))
        (putnam_2005_a2_detourData_side_bijective (n := n)
          (startTop := startTop) (endTop := endTop) hn))
  have hsmall :
      (putnam_2005_a2_detourDataSet n startTop endTop).encard =
        (putnam_2005_a2_cornerListTourSet n startTop endTop).encard :=
    Set.encard_congr
      (Equiv.ofBijective
        (fun d : putnam_2005_a2_detourDataSet n startTop endTop ↦
          (⟨putnam_2005_a2_detourSmallList n endTop d.1, d.2⟩ :
            putnam_2005_a2_cornerListTourSet n startTop endTop))
        (putnam_2005_a2_detourData_small_bijective (n := n)
          (startTop := startTop) (endTop := endTop) hn))
  exact hside.symm.trans hsmall

private lemma putnam_2005_a2_corner_encard_succ
    {n : ℕ} {startTop endTop : Bool} (hn : 1 < n) :
    (putnam_2005_a2_cornerListTourSet (n + 1) startTop endTop).encard =
      (putnam_2005_a2_cornerListTourSet n startTop (!endTop)).encard +
        (putnam_2005_a2_cornerListTourSet n startTop endTop).encard := by
  rw [putnam_2005_a2_corner_big_split (n := n)
    (startTop := startTop) (endTop := endTop) (by omega : 0 < n)]
  rw [Set.encard_union_eq (putnam_2005_a2_middle_side_disjoint
    (n := n) (startTop := startTop) (endTop := endTop))]
  rw [putnam_2005_a2_middle_encard (n := n)
      (startTop := startTop) (endTop := endTop) (by omega : 0 < n),
    putnam_2005_a2_side_encard (n := n)
      (startTop := startTop) (endTop := endTop) hn]

private lemma putnam_2005_a2_corner_two_bottom_mem :
    putnam_2005_a2_cornerListTour 2 false false
      [putnam_2005_a2_pt 1 1, putnam_2005_a2_pt 1 2,
        putnam_2005_a2_pt 1 3, putnam_2005_a2_pt 2 3,
        putnam_2005_a2_pt 2 2, putnam_2005_a2_pt 2 1] := by
  constructor
  · change
      ([putnam_2005_a2_pt 1 1, putnam_2005_a2_pt 1 2,
        putnam_2005_a2_pt 1 3, putnam_2005_a2_pt 2 3,
        putnam_2005_a2_pt 2 2, putnam_2005_a2_pt 2 1] :
          List putnam_2005_a2_Point).Perm
        [putnam_2005_a2_pt 1 1, putnam_2005_a2_pt 1 2,
          putnam_2005_a2_pt 1 3, putnam_2005_a2_pt 2 1,
          putnam_2005_a2_pt 2 2, putnam_2005_a2_pt 2 3]
    exact
      (((List.reverse_perm
        ([putnam_2005_a2_pt 2 1, putnam_2005_a2_pt 2 2,
          putnam_2005_a2_pt 2 3] : List putnam_2005_a2_Point)).cons
        (putnam_2005_a2_pt 1 3)).cons
        (putnam_2005_a2_pt 1 2)).cons
        (putnam_2005_a2_pt 1 1)
  constructor
  · simp [putnam_2005_a2_unit, putnam_2005_a2_pt]
  constructor
  · simp [putnam_2005_a2_pt, putnam_2005_a2_side]
  · simp [putnam_2005_a2_pt, putnam_2005_a2_side]

private lemma putnam_2005_a2_corner_two_top_mem :
    putnam_2005_a2_cornerListTour 2 false true
      [putnam_2005_a2_pt 1 1, putnam_2005_a2_pt 2 1,
        putnam_2005_a2_pt 2 2, putnam_2005_a2_pt 1 2,
        putnam_2005_a2_pt 1 3, putnam_2005_a2_pt 2 3] := by
  constructor
  · change
      ([putnam_2005_a2_pt 1 1, putnam_2005_a2_pt 2 1,
        putnam_2005_a2_pt 2 2, putnam_2005_a2_pt 1 2,
        putnam_2005_a2_pt 1 3, putnam_2005_a2_pt 2 3] :
          List putnam_2005_a2_Point).Perm
        [putnam_2005_a2_pt 1 1, putnam_2005_a2_pt 1 2,
          putnam_2005_a2_pt 1 3, putnam_2005_a2_pt 2 1,
          putnam_2005_a2_pt 2 2, putnam_2005_a2_pt 2 3]
    apply List.Perm.cons
    have h₁ :
        ([putnam_2005_a2_pt 2 1, putnam_2005_a2_pt 2 2,
          putnam_2005_a2_pt 1 2, putnam_2005_a2_pt 1 3,
          putnam_2005_a2_pt 2 3] : List putnam_2005_a2_Point).Perm
          ([putnam_2005_a2_pt 1 2, putnam_2005_a2_pt 1 3,
            putnam_2005_a2_pt 2 3] ++
            [putnam_2005_a2_pt 2 1, putnam_2005_a2_pt 2 2]) := by
      simpa using
        (List.perm_append_comm :
          (([putnam_2005_a2_pt 2 1, putnam_2005_a2_pt 2 2] :
            List putnam_2005_a2_Point) ++
            [putnam_2005_a2_pt 1 2, putnam_2005_a2_pt 1 3,
              putnam_2005_a2_pt 2 3]).Perm
            ([putnam_2005_a2_pt 1 2, putnam_2005_a2_pt 1 3,
              putnam_2005_a2_pt 2 3] ++
              [putnam_2005_a2_pt 2 1, putnam_2005_a2_pt 2 2]))
    have h₂ :
        ([putnam_2005_a2_pt 1 2, putnam_2005_a2_pt 1 3,
          putnam_2005_a2_pt 2 3] ++
          [putnam_2005_a2_pt 2 1, putnam_2005_a2_pt 2 2] :
            List putnam_2005_a2_Point).Perm
          [putnam_2005_a2_pt 1 2, putnam_2005_a2_pt 1 3,
            putnam_2005_a2_pt 2 1, putnam_2005_a2_pt 2 2,
            putnam_2005_a2_pt 2 3] := by
      apply List.Perm.cons
      apply List.Perm.cons
      simpa using
        (List.perm_append_comm :
          (([putnam_2005_a2_pt 2 3] : List putnam_2005_a2_Point) ++
            [putnam_2005_a2_pt 2 1, putnam_2005_a2_pt 2 2]).Perm
            ([putnam_2005_a2_pt 2 1, putnam_2005_a2_pt 2 2] ++
              [putnam_2005_a2_pt 2 3]))
    exact h₁.trans h₂
  constructor
  · simp [putnam_2005_a2_unit, putnam_2005_a2_pt]
  constructor
  · simp [putnam_2005_a2_pt, putnam_2005_a2_side]
  · simp [putnam_2005_a2_pt, putnam_2005_a2_side]

private lemma putnam_2005_a2_corner_two_bottom_unique
    {l : List putnam_2005_a2_Point}
    (hl : putnam_2005_a2_cornerListTour 2 false false l) :
    l =
      [putnam_2005_a2_pt 1 1, putnam_2005_a2_pt 1 2,
        putnam_2005_a2_pt 1 3, putnam_2005_a2_pt 2 3,
        putnam_2005_a2_pt 2 2, putnam_2005_a2_pt 2 1] := by
  classical
  let A := putnam_2005_a2_pt 1 1
  let D := putnam_2005_a2_pt 2 1
  have hlen : l.length = 6 := by
    have := putnam_2005_a2_cornerListTour_length (n := 2)
      (startTop := false) (endTop := false) (l := l) hl
    norm_num at this
    exact this
  rcases hl with ⟨hperm, hchain, hhead, hlast⟩
  rw [List.head?_eq_some_iff] at hhead
  rcases hhead with ⟨t0, rfl⟩
  cases t0 with
  | nil =>
      simp [A, putnam_2005_a2_pt, putnam_2005_a2_side] at hlen
  | cons q1 t1 =>
      cases t1 with
      | nil =>
          simp [A, putnam_2005_a2_pt, putnam_2005_a2_side] at hlen
      | cons q2 t2 =>
          cases t2 with
          | nil =>
              simp [A, putnam_2005_a2_pt, putnam_2005_a2_side] at hlen
          | cons q3 t3 =>
              cases t3 with
              | nil =>
                  simp [A, putnam_2005_a2_pt, putnam_2005_a2_side] at hlen
              | cons q4 t4 =>
                  cases t4 with
                  | nil =>
                      simp [A, putnam_2005_a2_pt, putnam_2005_a2_side] at hlen
                  | cons q5 t5 =>
                      cases t5 with
                      | cons q6 t6 =>
                          simp [A, putnam_2005_a2_pt,
                            putnam_2005_a2_side] at hlen
                      | nil =>
                          have hq5 : q5 = D := by
                            simpa [A, D, putnam_2005_a2_pt,
                              putnam_2005_a2_side] using hlast
                          subst q5
                          have hnodup :
                              ([A, q1, q2, q3, q4, D] :
                                List putnam_2005_a2_Point).Nodup :=
                            (List.Perm.nodup_iff hperm).2
                              (putnam_2005_a2_boardList_nodup 2)
                          have hq1mem : q1 ∈ putnam_2005_a2_boardList 2 :=
                            (hperm.mem_iff).1 (by simp [A, D])
                          have hq2mem : q2 ∈ putnam_2005_a2_boardList 2 :=
                            (hperm.mem_iff).1 (by simp [A, D])
                          have hq3mem : q3 ∈ putnam_2005_a2_boardList 2 :=
                            (hperm.mem_iff).1 (by simp [A, D])
                          have hq4mem : q4 ∈ putnam_2005_a2_boardList 2 :=
                            (hperm.mem_iff).1 (by simp [A, D])
                          have hq1b :=
                            (putnam_2005_a2_boardList_mem_iff 2 q1).1 hq1mem
                          have hq2b :=
                            (putnam_2005_a2_boardList_mem_iff 2 q2).1 hq2mem
                          have hq3b :=
                            (putnam_2005_a2_boardList_mem_iff 2 q3).1 hq3mem
                          have hq4b :=
                            (putnam_2005_a2_boardList_mem_iff 2 q4).1 hq4mem
                          let B := putnam_2005_a2_pt 1 2
                          let C := putnam_2005_a2_pt 1 3
                          let E := putnam_2005_a2_pt 2 2
                          let F := putnam_2005_a2_pt 2 3
                          have hAq1 : putnam_2005_a2_unit A q1 := by
                            simpa [A, putnam_2005_a2_side] using
                              List.rel_of_isChain_cons_cons hchain
                          have htail1 :
                              (q1 :: q2 :: q3 :: q4 :: D :: []).IsChain
                                putnam_2005_a2_unit :=
                            (List.isChain_cons_cons.mp hchain).2
                          have hq1q2 : putnam_2005_a2_unit q1 q2 :=
                            List.rel_of_isChain_cons_cons htail1
                          have htail2 :
                              (q2 :: q3 :: q4 :: D :: []).IsChain
                                putnam_2005_a2_unit :=
                            (List.isChain_cons_cons.mp htail1).2
                          have hq2q3 : putnam_2005_a2_unit q2 q3 :=
                            List.rel_of_isChain_cons_cons htail2
                          have htail3 :
                              (q3 :: q4 :: D :: []).IsChain putnam_2005_a2_unit :=
                            (List.isChain_cons_cons.mp htail2).2
                          have hq3q4 : putnam_2005_a2_unit q3 q4 :=
                            List.rel_of_isChain_cons_cons htail3
                          have htail4 :
                              (q4 :: D :: []).IsChain putnam_2005_a2_unit :=
                            (List.isChain_cons_cons.mp htail3).2
                          have hq4D : putnam_2005_a2_unit q4 D :=
                            List.rel_of_isChain_cons_cons htail4
                          have hq1_ne_D : q1 ≠ D := by
                            intro h
                            subst q1
                            simp [A, D, putnam_2005_a2_pt] at hnodup
                          rcases putnam_2005_a2_neighbor_bottom_left
                              (n := 2) hq1b hAq1 with hq1D | hq1B
                          · exact (hq1_ne_D (by simpa [D] using hq1D)).elim
                          · have hq1 : q1 = B := by simpa [B] using hq1B
                            subst q1
                            have hq2_ne_A : q2 ≠ A := by
                              intro h
                              subst q2
                              simp [A, B, D, putnam_2005_a2_pt] at hnodup
                            have hq2class :
                                q2 = A ∨ q2 = C ∨ q2 = E := by
                              simpa [A, B, C, E] using
                                putnam_2005_a2_neighbor_left_middle
                                  (n := 2) hq2b hq1q2
                            rcases hq2class with hq2A | hq2C | hq2E
                            · exact (hq2_ne_A (by simpa using hq2A)).elim
                            · have hq2 : q2 = C := by simpa [C] using hq2C
                              subst q2
                              have hq3_ne_B : q3 ≠ B := by
                                intro h
                                subst q3
                                simp [A, B, C, D, putnam_2005_a2_pt] at hnodup
                              have hq3class : q3 = B ∨ q3 = F := by
                                simpa [B, C, F] using
                                  putnam_2005_a2_neighbor_left_top
                                    (n := 2) hq3b hq2q3
                              rcases hq3class with hq3B | hq3F
                              · exact (hq3_ne_B (by simpa using hq3B)).elim
                              · have hq3 : q3 = F := by simpa [F] using hq3F
                                subst q3
                                have hq4_ne_C : q4 ≠ C := by
                                  intro h
                                  subst q4
                                  simp [A, B, C, D, F,
                                    putnam_2005_a2_pt] at hnodup
                                have hq4class : q4 = C ∨ q4 = E := by
                                  simpa [C, E, F] using
                                    putnam_2005_a2_neighbor_right_top
                                      (n := 1) hq4b hq3q4
                                rcases hq4class with hq4C | hq4E
                                · exact (hq4_ne_C (by simpa using hq4C)).elim
                                · have hq4 : q4 = E := by simpa [E] using hq4E
                                  subst q4
                                  simp [A, B, C, D, E, F,
                                    putnam_2005_a2_pt, putnam_2005_a2_side]
                            · have hq2 : q2 = E := by simpa [E] using hq2E
                              subst q2
                              have hq3_ne_D : q3 ≠ D := by
                                intro h
                                subst q3
                                simp [A, B, D, E, putnam_2005_a2_pt] at hnodup
                              have hq3_ne_B : q3 ≠ B := by
                                intro h
                                subst q3
                                simp [A, B, D, E, putnam_2005_a2_pt] at hnodup
                              have hq3class : q3 = D ∨ q3 = F ∨ q3 = B := by
                                simpa [B, D, E, F] using
                                  putnam_2005_a2_neighbor_right_middle
                                    (n := 1) hq3b hq2q3
                              rcases hq3class with hq3D | hq3F | hq3B
                              · exact (hq3_ne_D (by simpa using hq3D)).elim
                              · have hq3 : q3 = F := by simpa [F] using hq3F
                                subst q3
                                have hq4_ne_E : q4 ≠ E := by
                                  intro h
                                  subst q4
                                  simp [A, B, D, E, F,
                                    putnam_2005_a2_pt] at hnodup
                                have hq4class : q4 = C ∨ q4 = E := by
                                  simpa [C, E, F] using
                                    putnam_2005_a2_neighbor_right_top
                                      (n := 1) hq4b hq3q4
                                rcases hq4class with hq4C | hq4E
                                · have hq4 : q4 = C := by simpa [C] using hq4C
                                  subst q4
                                  have : False := by
                                    simpa [C, D, putnam_2005_a2_unit,
                                      putnam_2005_a2_pt] using hq4D
                                  exact this.elim
                                · exact (hq4_ne_E (by simpa using hq4E)).elim
                              · exact (hq3_ne_B (by simpa using hq3B)).elim

private lemma putnam_2005_a2_corner_two_top_unique
    {l : List putnam_2005_a2_Point}
    (hl : putnam_2005_a2_cornerListTour 2 false true l) :
    l =
      [putnam_2005_a2_pt 1 1, putnam_2005_a2_pt 2 1,
        putnam_2005_a2_pt 2 2, putnam_2005_a2_pt 1 2,
        putnam_2005_a2_pt 1 3, putnam_2005_a2_pt 2 3] := by
  classical
  let A := putnam_2005_a2_pt 1 1
  let F := putnam_2005_a2_pt 2 3
  have hlen : l.length = 6 := by
    have := putnam_2005_a2_cornerListTour_length (n := 2)
      (startTop := false) (endTop := true) (l := l) hl
    norm_num at this
    exact this
  rcases hl with ⟨hperm, hchain, hhead, hlast⟩
  rw [List.head?_eq_some_iff] at hhead
  rcases hhead with ⟨t0, rfl⟩
  cases t0 with
  | nil =>
      simp [A, putnam_2005_a2_pt, putnam_2005_a2_side] at hlen
  | cons q1 t1 =>
      cases t1 with
      | nil =>
          simp [A, putnam_2005_a2_pt, putnam_2005_a2_side] at hlen
      | cons q2 t2 =>
          cases t2 with
          | nil =>
              simp [A, putnam_2005_a2_pt, putnam_2005_a2_side] at hlen
          | cons q3 t3 =>
              cases t3 with
              | nil =>
                  simp [A, putnam_2005_a2_pt, putnam_2005_a2_side] at hlen
              | cons q4 t4 =>
                  cases t4 with
                  | nil =>
                      simp [A, putnam_2005_a2_pt, putnam_2005_a2_side] at hlen
                  | cons q5 t5 =>
                      cases t5 with
                      | cons q6 t6 =>
                          simp [A, putnam_2005_a2_pt,
                            putnam_2005_a2_side] at hlen
                      | nil =>
                          have hq5 : q5 = F := by
                            simpa [A, F, putnam_2005_a2_pt,
                              putnam_2005_a2_side] using hlast
                          subst q5
                          have hnodup :
                              ([A, q1, q2, q3, q4, F] :
                                List putnam_2005_a2_Point).Nodup :=
                            (List.Perm.nodup_iff hperm).2
                              (putnam_2005_a2_boardList_nodup 2)
                          have hq1mem : q1 ∈ putnam_2005_a2_boardList 2 :=
                            (hperm.mem_iff).1 (by simp [A, F])
                          have hq2mem : q2 ∈ putnam_2005_a2_boardList 2 :=
                            (hperm.mem_iff).1 (by simp [A, F])
                          have hq3mem : q3 ∈ putnam_2005_a2_boardList 2 :=
                            (hperm.mem_iff).1 (by simp [A, F])
                          have hq4mem : q4 ∈ putnam_2005_a2_boardList 2 :=
                            (hperm.mem_iff).1 (by simp [A, F])
                          have hq1b :=
                            (putnam_2005_a2_boardList_mem_iff 2 q1).1 hq1mem
                          have hq2b :=
                            (putnam_2005_a2_boardList_mem_iff 2 q2).1 hq2mem
                          have hq3b :=
                            (putnam_2005_a2_boardList_mem_iff 2 q3).1 hq3mem
                          have hq4b :=
                            (putnam_2005_a2_boardList_mem_iff 2 q4).1 hq4mem
                          let B := putnam_2005_a2_pt 1 2
                          let C := putnam_2005_a2_pt 1 3
                          let D := putnam_2005_a2_pt 2 1
                          let E := putnam_2005_a2_pt 2 2
                          have hAq1 : putnam_2005_a2_unit A q1 := by
                            simpa [A, putnam_2005_a2_side] using
                              List.rel_of_isChain_cons_cons hchain
                          have htail1 :
                              (q1 :: q2 :: q3 :: q4 :: F :: []).IsChain
                                putnam_2005_a2_unit :=
                            (List.isChain_cons_cons.mp hchain).2
                          have hq1q2 : putnam_2005_a2_unit q1 q2 :=
                            List.rel_of_isChain_cons_cons htail1
                          have htail2 :
                              (q2 :: q3 :: q4 :: F :: []).IsChain
                                putnam_2005_a2_unit :=
                            (List.isChain_cons_cons.mp htail1).2
                          have hq2q3 : putnam_2005_a2_unit q2 q3 :=
                            List.rel_of_isChain_cons_cons htail2
                          have htail3 :
                              (q3 :: q4 :: F :: []).IsChain putnam_2005_a2_unit :=
                            (List.isChain_cons_cons.mp htail2).2
                          have hq3q4 : putnam_2005_a2_unit q3 q4 :=
                            List.rel_of_isChain_cons_cons htail3
                          have htail4 :
                              (q4 :: F :: []).IsChain putnam_2005_a2_unit :=
                            (List.isChain_cons_cons.mp htail3).2
                          have hq4F : putnam_2005_a2_unit q4 F :=
                            List.rel_of_isChain_cons_cons htail4
                          rcases putnam_2005_a2_neighbor_bottom_left
                              (n := 2) hq1b hAq1 with hq1D | hq1B
                          · have hq1 : q1 = D := by simpa [D] using hq1D
                            subst q1
                            have hq2_ne_A : q2 ≠ A := by
                              intro h
                              subst q2
                              simp [A, D, F, putnam_2005_a2_pt] at hnodup
                            have hq2class : q2 = A ∨ q2 = E := by
                              simpa [A, D, E] using
                                putnam_2005_a2_neighbor_right_bottom
                                  (n := 1) hq2b hq1q2
                            rcases hq2class with hq2A | hq2E
                            · exact (hq2_ne_A (by simpa using hq2A)).elim
                            · have hq2 : q2 = E := by simpa [E] using hq2E
                              subst q2
                              have hq3_ne_D : q3 ≠ D := by
                                intro h
                                subst q3
                                simp [A, D, E, F, putnam_2005_a2_pt] at hnodup
                              have hq3_ne_F : q3 ≠ F := by
                                intro h
                                subst q3
                                simp [A, D, E, F, putnam_2005_a2_pt] at hnodup
                              have hq3class : q3 = D ∨ q3 = F ∨ q3 = B := by
                                simpa [B, D, E, F] using
                                  putnam_2005_a2_neighbor_right_middle
                                    (n := 1) hq3b hq2q3
                              rcases hq3class with hq3D | hq3F | hq3B
                              · exact (hq3_ne_D (by simpa using hq3D)).elim
                              · exact (hq3_ne_F (by simpa using hq3F)).elim
                              · have hq3 : q3 = B := by simpa [B] using hq3B
                                subst q3
                                have hq4_ne_A : q4 ≠ A := by
                                  intro h
                                  subst q4
                                  simp [A, B, D, E, F,
                                    putnam_2005_a2_pt] at hnodup
                                have hq4_ne_E : q4 ≠ E := by
                                  intro h
                                  subst q4
                                  simp [A, B, D, E, F,
                                    putnam_2005_a2_pt] at hnodup
                                have hq4class : q4 = A ∨ q4 = C ∨ q4 = E := by
                                  simpa [A, B, C, E] using
                                    putnam_2005_a2_neighbor_left_middle
                                      (n := 2) hq4b hq3q4
                                rcases hq4class with hq4A | hq4C | hq4E
                                · exact (hq4_ne_A (by simpa using hq4A)).elim
                                · have hq4 : q4 = C := by simpa [C] using hq4C
                                  subst q4
                                  simp [A, B, C, D, E, F,
                                    putnam_2005_a2_pt, putnam_2005_a2_side]
                                · exact (hq4_ne_E (by simpa using hq4E)).elim
                          · have hq1 : q1 = B := by simpa [B] using hq1B
                            subst q1
                            have hq2_ne_A : q2 ≠ A := by
                              intro h
                              subst q2
                              simp [A, B, F, putnam_2005_a2_pt] at hnodup
                            have hq2class :
                                q2 = A ∨ q2 = C ∨ q2 = E := by
                              simpa [A, B, C, E] using
                                putnam_2005_a2_neighbor_left_middle
                                  (n := 2) hq2b hq1q2
                            rcases hq2class with hq2A | hq2C | hq2E
                            · exact (hq2_ne_A (by simpa using hq2A)).elim
                            · have hq2 : q2 = C := by simpa [C] using hq2C
                              subst q2
                              have hq3_ne_B : q3 ≠ B := by
                                intro h
                                subst q3
                                simp [A, B, C, F, putnam_2005_a2_pt] at hnodup
                              have hq3_ne_F : q3 ≠ F := by
                                intro h
                                subst q3
                                simp [A, B, C, F, putnam_2005_a2_pt] at hnodup
                              have hq3class : q3 = B ∨ q3 = F := by
                                simpa [B, C, F] using
                                  putnam_2005_a2_neighbor_left_top
                                    (n := 2) hq3b hq2q3
                              rcases hq3class with hq3B | hq3F
                              · exact (hq3_ne_B (by simpa using hq3B)).elim
                              · exact (hq3_ne_F (by simpa using hq3F)).elim
                            · have hq2 : q2 = E := by simpa [E] using hq2E
                              subst q2
                              have hq3_ne_B : q3 ≠ B := by
                                intro h
                                subst q3
                                simp [A, B, E, F, putnam_2005_a2_pt] at hnodup
                              have hq3_ne_F : q3 ≠ F := by
                                intro h
                                subst q3
                                simp [A, B, E, F, putnam_2005_a2_pt] at hnodup
                              have hq3class : q3 = D ∨ q3 = F ∨ q3 = B := by
                                simpa [B, D, E, F] using
                                  putnam_2005_a2_neighbor_right_middle
                                    (n := 1) hq3b hq2q3
                              rcases hq3class with hq3D | hq3F | hq3B
                              · have hq3 : q3 = D := by simpa [D] using hq3D
                                subst q3
                                have hq4_ne_A : q4 ≠ A := by
                                  intro h
                                  subst q4
                                  simp [A, B, D, E, F,
                                    putnam_2005_a2_pt] at hnodup
                                have hq4_ne_E : q4 ≠ E := by
                                  intro h
                                  subst q4
                                  simp [A, B, D, E, F,
                                    putnam_2005_a2_pt] at hnodup
                                have hq4class : q4 = A ∨ q4 = E := by
                                  simpa [A, D, E] using
                                    putnam_2005_a2_neighbor_right_bottom
                                      (n := 1) hq4b hq3q4
                                rcases hq4class with hq4A | hq4E
                                · exact (hq4_ne_A (by simpa using hq4A)).elim
                                · exact (hq4_ne_E (by simpa using hq4E)).elim
                              · exact (hq3_ne_F (by simpa using hq3F)).elim
                              · exact (hq3_ne_B (by simpa using hq3B)).elim

private lemma putnam_2005_a2_corner_two_bottom_set :
    putnam_2005_a2_cornerListTourSet 2 false false =
      {[putnam_2005_a2_pt 1 1, putnam_2005_a2_pt 1 2,
        putnam_2005_a2_pt 1 3, putnam_2005_a2_pt 2 3,
        putnam_2005_a2_pt 2 2, putnam_2005_a2_pt 2 1]} := by
  ext l
  constructor
  · intro hl
    exact Set.mem_singleton_iff.mpr
      (putnam_2005_a2_corner_two_bottom_unique
        (by simpa [putnam_2005_a2_cornerListTourSet] using hl))
  · intro hl
    rw [Set.mem_singleton_iff] at hl
    subst l
    simpa [putnam_2005_a2_cornerListTourSet] using
      putnam_2005_a2_corner_two_bottom_mem

private lemma putnam_2005_a2_corner_two_top_set :
    putnam_2005_a2_cornerListTourSet 2 false true =
      {[putnam_2005_a2_pt 1 1, putnam_2005_a2_pt 2 1,
        putnam_2005_a2_pt 2 2, putnam_2005_a2_pt 1 2,
        putnam_2005_a2_pt 1 3, putnam_2005_a2_pt 2 3]} := by
  ext l
  constructor
  · intro hl
    exact Set.mem_singleton_iff.mpr
      (putnam_2005_a2_corner_two_top_unique
        (by simpa [putnam_2005_a2_cornerListTourSet] using hl))
  · intro hl
    rw [Set.mem_singleton_iff] at hl
    subst l
    simpa [putnam_2005_a2_cornerListTourSet] using
      putnam_2005_a2_corner_two_top_mem

private lemma putnam_2005_a2_corner_two_bottom_encard :
    (putnam_2005_a2_cornerListTourSet 2 false false).encard =
      ((1 : ℕ) : ℕ∞) := by
  rw [putnam_2005_a2_corner_two_bottom_set]
  simp

private lemma putnam_2005_a2_corner_two_top_encard :
    (putnam_2005_a2_cornerListTourSet 2 false true).encard =
      ((1 : ℕ) : ℕ∞) := by
  rw [putnam_2005_a2_corner_two_top_set]
  simp

private lemma putnam_2005_a2_corner_false_encard_aux (k : ℕ) :
    (putnam_2005_a2_cornerListTourSet (k + 2) false false).encard =
        ((2 ^ k : ℕ) : ℕ∞) ∧
      (putnam_2005_a2_cornerListTourSet (k + 2) false true).encard =
        ((2 ^ k : ℕ) : ℕ∞) := by
  induction k with
  | zero =>
      constructor
      · simpa using putnam_2005_a2_corner_two_bottom_encard
      · simpa using putnam_2005_a2_corner_two_top_encard
  | succ k ih =>
      have hk : Nat.succ k + 2 = (k + 2) + 1 := by omega
      constructor
      · rw [hk]
        rw [putnam_2005_a2_corner_encard_succ
          (n := k + 2) (startTop := false) (endTop := false) (by omega)]
        simp only [Bool.not_false]
        rw [ih.2, ih.1]
        rw [← Nat.cast_add]
        have hpow : (2 ^ k + 2 ^ k : ℕ) = 2 ^ Nat.succ k := by
          rw [pow_succ]
          omega
        exact congrArg (fun m : ℕ => ((m : ℕ) : ℕ∞)) hpow
      · rw [hk]
        rw [putnam_2005_a2_corner_encard_succ
          (n := k + 2) (startTop := false) (endTop := true) (by omega)]
        simp only [Bool.not_true]
        rw [ih.1, ih.2]
        rw [← Nat.cast_add]
        have hpow : (2 ^ k + 2 ^ k : ℕ) = 2 ^ Nat.succ k := by
          rw [pow_succ]
          omega
        exact congrArg (fun m : ℕ => ((m : ℕ) : ℕ∞)) hpow

private lemma putnam_2005_a2_corner_false_encard
    {n : ℕ} (hn : 2 ≤ n) :
    (putnam_2005_a2_cornerListTourSet n false false).encard =
        ((2 ^ (n - 2) : ℕ) : ℕ∞) ∧
      (putnam_2005_a2_cornerListTourSet n false true).encard =
        ((2 ^ (n - 2) : ℕ) : ℕ∞) := by
  have h := putnam_2005_a2_corner_false_encard_aux (n - 2)
  have hk : n - 2 + 2 = n := by omega
  simpa [hk] using h

private lemma putnam_2005_a2_listTour_bottom_second {n : ℕ}
    {l : List putnam_2005_a2_Point} (hn : 1 < n)
    (hl : putnam_2005_a2_listTour n false l) :
    ∃ t,
      l = putnam_2005_a2_pt 1 1 :: putnam_2005_a2_pt 2 1 :: t ∨
        l = putnam_2005_a2_pt 1 1 :: putnam_2005_a2_pt 1 2 :: t := by
  rcases hl with ⟨hperm, hchain, hhead, hlast⟩
  rw [List.head?_eq_some_iff] at hhead
  rcases hhead with ⟨tail, rfl⟩
  have htail_ne : tail ≠ [] := by
    intro htail
    have hlen := putnam_2005_a2_listTour_length
      (n := n) (top := false)
      (l := putnam_2005_a2_pt 1 1 :: tail)
      ⟨by simpa [putnam_2005_a2_side] using hperm,
        by simpa [putnam_2005_a2_side] using hchain,
        by simp [putnam_2005_a2_pt, putnam_2005_a2_side],
        by simpa [putnam_2005_a2_side] using hlast⟩
    rw [htail] at hlen
    simp at hlen
    omega
  rcases List.exists_cons_of_ne_nil htail_ne with ⟨q, t, rfl⟩
  have hqmem : q ∈ putnam_2005_a2_pt 1 (putnam_2005_a2_side false) :: q :: t := by simp
  have hqboard : q ∈ putnam_2005_a2_board n :=
    putnam_2005_a2_listTour_mem_board
      (n := n) (top := false)
      (l := putnam_2005_a2_pt 1 (putnam_2005_a2_side false) :: q :: t)
      ⟨hperm, hchain, by simp [putnam_2005_a2_pt], hlast⟩ hqmem
  have hunit : putnam_2005_a2_unit (putnam_2005_a2_pt 1 1) q := by
    simpa [putnam_2005_a2_pt, putnam_2005_a2_side] using
      List.rel_of_isChain_cons_cons hchain
  rcases putnam_2005_a2_neighbor_bottom_left hqboard hunit with hq | hq
  · refine ⟨t, Or.inl ?_⟩
    simp [hq, putnam_2005_a2_side]
  · refine ⟨t, Or.inr ?_⟩
    simp [hq, putnam_2005_a2_side]

private lemma putnam_2005_a2_listTour_top_second {n : ℕ}
    {l : List putnam_2005_a2_Point} (hn : 1 < n)
    (hl : putnam_2005_a2_listTour n true l) :
    ∃ t,
      l = putnam_2005_a2_pt 1 3 :: putnam_2005_a2_pt 2 3 :: t ∨
        l = putnam_2005_a2_pt 1 3 :: putnam_2005_a2_pt 1 2 :: t := by
  rcases hl with ⟨hperm, hchain, hhead, hlast⟩
  rw [List.head?_eq_some_iff] at hhead
  rcases hhead with ⟨tail, rfl⟩
  have htail_ne : tail ≠ [] := by
    intro htail
    have hlen := putnam_2005_a2_listTour_length
      (n := n) (top := true)
      (l := putnam_2005_a2_pt 1 3 :: tail)
      ⟨hperm, hchain, by simp [putnam_2005_a2_pt, putnam_2005_a2_side], hlast⟩
    rw [htail] at hlen
    simp at hlen
    omega
  rcases List.exists_cons_of_ne_nil htail_ne with ⟨q, t, rfl⟩
  have hqmem : q ∈ putnam_2005_a2_pt 1 (putnam_2005_a2_side true) :: q :: t := by simp
  have hqboard : q ∈ putnam_2005_a2_board n :=
    putnam_2005_a2_listTour_mem_board
      (n := n) (top := true)
      (l := putnam_2005_a2_pt 1 (putnam_2005_a2_side true) :: q :: t)
      ⟨hperm, hchain, by simp [putnam_2005_a2_pt, putnam_2005_a2_side], hlast⟩ hqmem
  have hunit : putnam_2005_a2_unit (putnam_2005_a2_pt 1 3) q := by
    simpa [putnam_2005_a2_pt, putnam_2005_a2_side] using
      List.rel_of_isChain_cons_cons hchain
  rcases putnam_2005_a2_neighbor_top_left hqboard hunit with hq | hq
  · refine ⟨t, Or.inl ?_⟩
    simp [hq, putnam_2005_a2_side]
  · refine ⟨t, Or.inr ?_⟩
    simp [hq, putnam_2005_a2_side]

private def putnam_2005_a2_pathList (n : ℕ) (p : ℕ → putnam_2005_a2_Point) :
    List putnam_2005_a2_Point :=
  List.ofFn fun i : Fin (3 * n) ↦ p (i.1 + 1)

private lemma putnam_2005_a2_pathList_length
    (n : ℕ) (p : ℕ → putnam_2005_a2_Point) :
    (putnam_2005_a2_pathList n p).length = 3 * n := by
  simp [putnam_2005_a2_pathList]

private lemma putnam_2005_a2_pathList_get
    {n : ℕ} {p : ℕ → putnam_2005_a2_Point} {i : ℕ} (hi : i < 3 * n) :
    (putnam_2005_a2_pathList n p)[i]'(by
      rw [putnam_2005_a2_pathList_length]
      exact hi) = p (i + 1) := by
  simpa [putnam_2005_a2_pathList] using
    (List.getElem_ofFn
      (f := fun i : Fin (3 * n) ↦ p (i.1 + 1))
      (i := i)
      (h := by simpa [putnam_2005_a2_pathList] using hi))

private lemma putnam_2005_a2_pathList_mem_board
    {n : ℕ} {p : ℕ → putnam_2005_a2_Point}
    (hp : putnam_2005_a2_rooktour n p)
    {P : putnam_2005_a2_Point}
    (hP : P ∈ putnam_2005_a2_pathList n p) :
    P ∈ putnam_2005_a2_board n := by
  rcases hp with ⟨huniq, _hadj, _hp0, _hafter⟩
  rw [putnam_2005_a2_pathList, List.mem_ofFn] at hP
  rcases hP with ⟨i, rfl⟩
  exact putnam_2005_a2_slot_mem_board n p huniq (by constructor <;> omega)

private lemma putnam_2005_a2_board_mem_pathList
    {n : ℕ} {p : ℕ → putnam_2005_a2_Point}
    (hp : putnam_2005_a2_rooktour n p)
    {P : putnam_2005_a2_Point}
    (hP : P ∈ putnam_2005_a2_board n) :
    P ∈ putnam_2005_a2_pathList n p := by
  rcases hp with ⟨huniq, _hadj, _hp0, _hafter⟩
  rcases huniq P hP with ⟨i, hiP, _huniq_i⟩
  rcases hiP with ⟨⟨hi1, hile⟩, hpi⟩
  rw [putnam_2005_a2_pathList, List.mem_ofFn]
  refine ⟨⟨i - 1, by omega⟩, ?_⟩
  have hi : (i - 1) + 1 = i := by omega
  simpa [hi] using hpi

private lemma putnam_2005_a2_pathList_nodup
    {n : ℕ} {p : ℕ → putnam_2005_a2_Point}
    (hp : putnam_2005_a2_rooktour n p) :
    (putnam_2005_a2_pathList n p).Nodup := by
  rcases hp with ⟨huniq, _hadj, _hp0, _hafter⟩
  rw [List.nodup_iff_injective_getElem]
  intro i j hij
  apply Fin.ext
  have hi' : i.1 < 3 * n := by
    simpa [putnam_2005_a2_pathList] using i.2
  have hj' : j.1 < 3 * n := by
    simpa [putnam_2005_a2_pathList] using j.2
  have hpij : p (i.1 + 1) = p (j.1 + 1) := by
    simpa [putnam_2005_a2_pathList_get hi',
      putnam_2005_a2_pathList_get hj'] using hij
  have hboard :
      p (i.1 + 1) ∈ putnam_2005_a2_board n :=
    putnam_2005_a2_slot_mem_board n p huniq (by constructor <;> omega)
  rcases huniq (p (i.1 + 1)) hboard with ⟨k, _hk, huniq_k⟩
  have hik : i.1 + 1 = k :=
    huniq_k (i.1 + 1) ⟨by constructor <;> omega, rfl⟩
  have hjk : j.1 + 1 = k :=
    huniq_k (j.1 + 1) ⟨by constructor <;> omega, hpij.symm⟩
  omega

private lemma putnam_2005_a2_pathList_perm
    {n : ℕ} {p : ℕ → putnam_2005_a2_Point}
    (hp : putnam_2005_a2_rooktour n p) :
    (putnam_2005_a2_pathList n p).Perm (putnam_2005_a2_boardList n) := by
  classical
  have hnodupPath := putnam_2005_a2_pathList_nodup hp
  have hnodupBoard := putnam_2005_a2_boardList_nodup n
  rw [List.perm_iff_count]
  intro P
  by_cases hP : P ∈ putnam_2005_a2_pathList n p
  · have hPb : P ∈ putnam_2005_a2_board n :=
      putnam_2005_a2_pathList_mem_board hp hP
    rw [List.count_eq_one_of_mem hnodupPath hP,
      List.count_eq_one_of_mem hnodupBoard
        ((putnam_2005_a2_boardList_mem_iff n P).2 hPb)]
  · have hPnotb : P ∉ putnam_2005_a2_boardList n := by
      intro hPb
      exact hP (putnam_2005_a2_board_mem_pathList hp
        ((putnam_2005_a2_boardList_mem_iff n P).1 hPb))
    rw [List.count_eq_zero_of_not_mem hP,
      List.count_eq_zero_of_not_mem hPnotb]

private lemma putnam_2005_a2_pathList_chain
    {n : ℕ} {p : ℕ → putnam_2005_a2_Point}
    (hp : putnam_2005_a2_rooktour n p) :
    (putnam_2005_a2_pathList n p).IsChain putnam_2005_a2_unit := by
  rcases hp with ⟨_huniq, hadj, _hp0, _hafter⟩
  rw [List.isChain_iff_getElem]
  intro i hi
  have hi' : i + 1 ∈ Icc 1 (3 * n - 1) := by
    have hlen := putnam_2005_a2_pathList_length n p
    constructor <;> omega
  have hunit := hadj (i + 1) hi'
  have hi0 : i < 3 * n := by
    have hlen := putnam_2005_a2_pathList_length n p
    omega
  have hi1 : i + 1 < 3 * n := by
    have hlen := putnam_2005_a2_pathList_length n p
    omega
  simpa [putnam_2005_a2_pathList_get hi0,
    putnam_2005_a2_pathList_get hi1, Nat.add_assoc] using hunit

private lemma putnam_2005_a2_pathList_head
    {n : ℕ} {p : ℕ → putnam_2005_a2_Point} (hn : 0 < n) :
    (putnam_2005_a2_pathList n p).head? = some (p 1) := by
  rw [List.head?_eq_getElem?]
  have h0 : 0 < (putnam_2005_a2_pathList n p).length := by
    rw [putnam_2005_a2_pathList_length]
    omega
  rw [List.getElem?_eq_getElem h0]
  simp [putnam_2005_a2_pathList_get (by omega : 0 < 3 * n)]

private lemma putnam_2005_a2_pathList_getLast
    {n : ℕ} {p : ℕ → putnam_2005_a2_Point} (hn : 0 < n) :
    (putnam_2005_a2_pathList n p).getLast? = some (p (3 * n)) := by
  rw [List.getLast?_eq_getElem?]
  have hlast : (putnam_2005_a2_pathList n p).length - 1 <
      (putnam_2005_a2_pathList n p).length := by
    rw [putnam_2005_a2_pathList_length]
    omega
  rw [List.getElem?_eq_getElem hlast]
  have hidx : (putnam_2005_a2_pathList n p).length - 1 = 3 * n - 1 := by
    rw [putnam_2005_a2_pathList_length]
  have hlt : 3 * n - 1 < 3 * n := by omega
  have hadd : (3 * n - 1) + 1 = 3 * n := by omega
  simpa [hidx, putnam_2005_a2_pathList_get hlt, hadd]

private lemma putnam_2005_a2_pathList_corner
    {n : ℕ} {p : ℕ → putnam_2005_a2_Point} (hn : 0 < n)
    (hp : p ∈ putnam_2005_a2_tourSet n) :
    putnam_2005_a2_cornerListTour n false false
      (putnam_2005_a2_pathList n p) := by
  rcases hp with ⟨hrook, hstart, hend⟩
  constructor
  · exact putnam_2005_a2_pathList_perm hrook
  constructor
  · exact putnam_2005_a2_pathList_chain hrook
  constructor
  · rw [putnam_2005_a2_pathList_head hn]
    simpa [putnam_2005_a2_pt, putnam_2005_a2_side] using congrArg some hstart
  · rw [putnam_2005_a2_pathList_getLast hn]
    simpa [putnam_2005_a2_pt, putnam_2005_a2_side] using congrArg some hend

private def putnam_2005_a2_funOfList
    (l : List putnam_2005_a2_Point) : ℕ → putnam_2005_a2_Point :=
  fun i ↦ if h : 1 ≤ i ∧ i ≤ l.length then l[i - 1] else 0

private lemma putnam_2005_a2_funOfList_of_range
    {l : List putnam_2005_a2_Point} {i : ℕ}
    (hi1 : 1 ≤ i) (hile : i ≤ l.length) :
    putnam_2005_a2_funOfList l i = l[i - 1] := by
  simp [putnam_2005_a2_funOfList, hi1, hile]

private lemma putnam_2005_a2_funOfList_corner_mem
    {n : ℕ} {startTop endTop : Bool} {l : List putnam_2005_a2_Point}
    (hl : putnam_2005_a2_cornerListTour n startTop endTop l)
    {P : putnam_2005_a2_Point} (hP : P ∈ putnam_2005_a2_board n) :
    ∃! i, i ∈ Icc 1 (3 * n) ∧ putnam_2005_a2_funOfList l i = P := by
  have hlen := putnam_2005_a2_cornerListTour_length hl
  have hnodup := putnam_2005_a2_cornerListTour_nodup hl
  have hPmem : P ∈ l := putnam_2005_a2_board_mem_cornerListTour hl hP
  rcases List.getElem_of_mem hPmem with ⟨j, hj, hjP⟩
  refine ⟨j + 1, ?_, ?_⟩
  · constructor
    · constructor <;> omega
    · rw [putnam_2005_a2_funOfList_of_range (by omega) (by omega)]
      simpa using hjP
  · intro i hi
    have hi1 : 1 ≤ i := hi.1.1
    have hile : i ≤ l.length := by
      rw [hlen]
      exact hi.1.2
    have him1 : i - 1 < l.length := by omega
    have hfun :
        putnam_2005_a2_funOfList l i = l[i - 1] :=
      putnam_2005_a2_funOfList_of_range hi1 hile
    have hidx : i - 1 = j := by
      apply (List.Nodup.getElem_inj_iff hnodup).1
      rw [← hfun, hi.2, hjP]
    omega

private lemma putnam_2005_a2_funOfList_chain
    {n : ℕ} {startTop endTop : Bool} {l : List putnam_2005_a2_Point}
    (hl : putnam_2005_a2_cornerListTour n startTop endTop l)
    {i : ℕ} (hi : i ∈ Icc 1 (3 * n - 1)) :
    putnam_2005_a2_unit
      (putnam_2005_a2_funOfList l i)
      (putnam_2005_a2_funOfList l (i + 1)) := by
  have hlen := putnam_2005_a2_cornerListTour_length hl
  have hi1 : 1 ≤ i := hi.1
  have hpos : 0 < 3 * n := by
    by_contra hnot
    have hz : 3 * n = 0 := Nat.eq_zero_of_not_pos hnot
    have hi0 : i ≤ 0 := by simpa [hz] using hi.2
    omega
  have hlt : i < 3 * n := Nat.lt_of_le_pred hpos hi.2
  have hile : i ≤ l.length := by
    rw [hlen]
    exact le_of_lt hlt
  have hi1le : i + 1 ≤ l.length := by
    rw [hlen]
    exact Nat.succ_le_of_lt hlt
  rw [putnam_2005_a2_funOfList_of_range hi1 hile,
    putnam_2005_a2_funOfList_of_range (by omega : 1 ≤ i + 1) hi1le]
  have hsucc : (i - 1) + 1 < l.length := by omega
  have hedge := putnam_2005_a2_edgeIn_of_get_succ (l := l) (i := i - 1) hsucc
  have hunit := putnam_2005_a2_unit_of_edgeIn hl.2.1 hedge
  simpa [show (i - 1) + 1 = i by omega] using hunit

private lemma putnam_2005_a2_funOfList_start
    {n : ℕ} {endTop : Bool} {l : List putnam_2005_a2_Point}
    (hn : 0 < n) (hl : putnam_2005_a2_cornerListTour n false endTop l) :
    putnam_2005_a2_funOfList l 1 = (1, 1) := by
  have hlen := putnam_2005_a2_cornerListTour_length hl
  have h0 : 0 < l.length := by omega
  have hhead := hl.2.2.1
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0] at hhead
  have hget0 :
      l[0] = putnam_2005_a2_pt 1 (putnam_2005_a2_side false) :=
    Option.some.inj hhead
  rw [putnam_2005_a2_funOfList_of_range (by omega) (by omega)]
  simpa [putnam_2005_a2_pt, putnam_2005_a2_side] using hget0

private lemma putnam_2005_a2_funOfList_end
    {n : ℕ} {startTop : Bool} {l : List putnam_2005_a2_Point}
    (hn : 0 < n) (hl : putnam_2005_a2_cornerListTour n startTop false l) :
    putnam_2005_a2_funOfList l (3 * n) = ((n : ℤ), 1) := by
  have hlen := putnam_2005_a2_cornerListTour_length hl
  have hlastidx : l.length - 1 < l.length := by omega
  have hlast := hl.2.2.2
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hlastidx] at hlast
  have hgetLast :
      l[l.length - 1] = putnam_2005_a2_pt (n : ℤ) (putnam_2005_a2_side false) :=
    Option.some.inj hlast
  rw [putnam_2005_a2_funOfList_of_range (by omega) (by omega)]
  have hidx : 3 * n - 1 = l.length - 1 := by omega
  simpa [hidx, putnam_2005_a2_pt, putnam_2005_a2_side] using hgetLast

private lemma putnam_2005_a2_funOfList_tour
    {n : ℕ} {l : List putnam_2005_a2_Point} (hn : 0 < n)
    (hl : putnam_2005_a2_cornerListTour n false false l) :
    putnam_2005_a2_funOfList l ∈ putnam_2005_a2_tourSet n := by
  have hlen := putnam_2005_a2_cornerListTour_length hl
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro P hP
      exact putnam_2005_a2_funOfList_corner_mem hl hP
    constructor
    · intro i hi
      exact putnam_2005_a2_funOfList_chain hl hi
    constructor
    · simp [putnam_2005_a2_funOfList]
    · intro i hi
      have hnot : ¬(1 ≤ i ∧ i ≤ l.length) := by omega
      simp [putnam_2005_a2_funOfList, hnot]
  · exact putnam_2005_a2_funOfList_start hn hl
  · exact putnam_2005_a2_funOfList_end hn hl

private lemma putnam_2005_a2_funOfList_pathList
    {n : ℕ} {p : ℕ → putnam_2005_a2_Point} (hn : 0 < n)
    (hp : p ∈ putnam_2005_a2_tourSet n) :
    putnam_2005_a2_funOfList (putnam_2005_a2_pathList n p) = p := by
  rcases hp with ⟨⟨_huniq, _hadj, hp0, hafter⟩, _hstart, _hend⟩
  funext i
  by_cases h0 : i = 0
  · subst i
    simp [putnam_2005_a2_funOfList, hp0]
  · by_cases hle : i ≤ 3 * n
    · have hi1 : 1 ≤ i := by omega
      have hilen : i ≤ (putnam_2005_a2_pathList n p).length := by
        rw [putnam_2005_a2_pathList_length]
        exact hle
      rw [putnam_2005_a2_funOfList_of_range hi1 hilen]
      have hidx : i - 1 < 3 * n := by omega
      have hadd : (i - 1) + 1 = i := by omega
      simpa [putnam_2005_a2_pathList_get hidx, hadd]
    · have hgt : i > 3 * n := by omega
      have hnot : ¬(1 ≤ i ∧ i ≤ (putnam_2005_a2_pathList n p).length) := by
        rw [putnam_2005_a2_pathList_length]
        omega
      simp [putnam_2005_a2_funOfList, hnot, hafter i hgt]

private lemma putnam_2005_a2_pathList_funOfList
    {n : ℕ} {l : List putnam_2005_a2_Point} (hn : 0 < n)
    (hl : putnam_2005_a2_cornerListTour n false false l) :
    putnam_2005_a2_pathList n (putnam_2005_a2_funOfList l) = l := by
  have hlen := putnam_2005_a2_cornerListTour_length hl
  apply List.ext_getElem
  · rw [putnam_2005_a2_pathList_length, hlen]
  · intro i hiPath hiL
    have hi : i < 3 * n := by
      simpa [putnam_2005_a2_pathList_length] using hiPath
    rw [putnam_2005_a2_pathList_get hi]
    have hile : i + 1 ≤ l.length := by omega
    simpa using
      putnam_2005_a2_funOfList_of_range
        (l := l) (i := i + 1) (by omega) hile

private noncomputable def putnam_2005_a2_tourEquiv_cornerListTour
    (n : ℕ) (hn : 0 < n) :
    putnam_2005_a2_tourSet n ≃
      putnam_2005_a2_cornerListTourSet n false false where
  toFun p := ⟨putnam_2005_a2_pathList n p.1,
    putnam_2005_a2_pathList_corner hn p.2⟩
  invFun l := ⟨putnam_2005_a2_funOfList l.1,
    putnam_2005_a2_funOfList_tour hn l.2⟩
  left_inv p := by
    apply Subtype.ext
    exact putnam_2005_a2_funOfList_pathList hn p.2
  right_inv l := by
    apply Subtype.ext
    exact putnam_2005_a2_pathList_funOfList hn l.2

/--
Let $\mathbf{S} = \{(a,b) | a = 1, 2, \dots,n, b = 1,2,3\}$.
A \emph{rook tour} of $\mathbf{S}$ is a polygonal path made up of line segments connecting points $p_1, p_2, \dots, p_{3n}$ in sequence such that
\begin{enumerate}
\item[(i)] $p_i \in \mathbf{S}$,
\item[(ii)] $p_i$ and $p_{i+1}$ are a unit distance apart, for
$1 \leq i <3n$,
\item[(iii)] for each $p \in \mathbf{S}$ there is a unique $i$ such that
$p_i = p$.
\end{enumerate}
How many rook tours are there that begin at $(1,1)$
and end at $(n,1)$?
-/
theorem putnam_2005_a2
(n : ℕ)
(npos : n > 0)
(S : Set (ℤ × ℤ))
(unit : ℤ × ℤ → ℤ × ℤ → Prop)
(rooktour : (ℕ → ℤ × ℤ) → Prop)
(hS : S = prod (Icc 1 (n : ℤ)) (Icc 1 3))
(hunit : unit = fun (a, b) (c, d) ↦ a = c ∧ |d - b| = 1 ∨ b = d ∧ |c - a| = 1)
(hrooktour : rooktour = fun p ↦ (∀ P ∈ S, ∃! i, i ∈ Icc 1 (3 * n) ∧ p i = P) ∧ (∀ i ∈ Icc 1 (3 * n - 1), unit (p i) (p (i + 1))) ∧ p 0 = 0 ∧ ∀ i > 3 * n, p i = 0)
: ({p : ℕ → ℤ × ℤ | rooktour p ∧ p 1 = (1, 1) ∧ p (3 * n) = ((n : ℤ), 1)}.encard = putnam_2005_a2_solution n) :=
by
  have _hnpos := npos
  subst S
  subst unit
  subst rooktour
  change (putnam_2005_a2_tourSet n).encard = ↑(putnam_2005_a2_solution n)
  by_cases hn : n = 1
  · subst n
    rw [putnam_2005_a2_tourSet_one_eq_empty]
    simp [putnam_2005_a2_solution]
  · have hn2 : 2 ≤ n := by omega
    have hcorner :=
      (putnam_2005_a2_corner_false_encard (n := n) hn2).1
    have htour :
        (putnam_2005_a2_tourSet n).encard =
          ((2 ^ (n - 2) : ℕ) : ℕ∞) := by
      calc
        (putnam_2005_a2_tourSet n).encard =
            (putnam_2005_a2_cornerListTourSet n false false).encard := by
          exact Set.encard_congr
            (putnam_2005_a2_tourEquiv_cornerListTour n npos)
        _ = ((2 ^ (n - 2) : ℕ) : ℕ∞) := hcorner
    simpa [putnam_2005_a2_solution, hn] using htour
