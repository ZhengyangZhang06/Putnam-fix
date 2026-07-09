import Mathlib

open Nat Set

private lemma putnam_2005_a2_index_ncard (n : ℕ) :
    (Set.Icc 1 (3 * n) : Set ℕ).ncard = 3 * n := by
  rw [Set.ncard_eq_toFinset_card _ (Set.finite_Icc 1 (3 * n))]
  simp

private lemma putnam_2005_a2_rect_ncard (n : ℕ) :
    (Set.prod (Set.Icc (1 : ℤ) (n : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ))).ncard = 3 * n := by
  change ((Set.Icc (1 : ℤ) (n : ℤ)) ×ˢ (Set.Icc (1 : ℤ) (3 : ℤ))).ncard = 3 * n
  rw [Set.ncard_prod]
  rw [Set.ncard_eq_toFinset_card _ (Set.finite_Icc (1 : ℤ) (n : ℤ)),
    Set.ncard_eq_toFinset_card _ (Set.finite_Icc (1 : ℤ) (3 : ℤ))]
  simp [Int.card_Icc]
  omega

private lemma putnam_2005_a2_mem_of_unique_hits
    {α β : Type*} {A : Set α} {B : Set β} {f : α → β}
    (hA : A.Finite) (hB : B.Finite) (hcard : A.ncard = B.ncard)
    (huniq : ∀ b ∈ B, ∃! a, a ∈ A ∧ f a = b) :
    ∀ a ∈ A, f a ∈ B := by
  classical
  intro a ha
  by_contra hnot
  let toA : B → A := fun b =>
    ⟨Classical.choose (huniq b b.2), (Classical.choose_spec (huniq b b.2)).1.1⟩
  have htoA_inj : Function.Injective toA := by
    intro b c hbc
    apply Subtype.ext
    have hb := (Classical.choose_spec (huniq b b.2)).1.2
    have hc := (Classical.choose_spec (huniq c c.2)).1.2
    have : (b : β) = c := by
      rw [← hb, ← hc]
      exact congr_arg (fun x : A => f x.1) hbc
    exact this
  let toDiff : B → (A \ {a} : Set α) := fun b =>
    ⟨(toA b).1, ⟨(toA b).2, by
      intro h
      have hb := (Classical.choose_spec (huniq b b.2)).1.2
      have : f a = b := by
        have hval : (toA b).1 = a := by simpa using h
        rw [← hval]
        exact hb
      exact hnot (this.symm ▸ b.2)⟩⟩
  have htoDiff_inj : Function.Injective toDiff := by
    intro b c hbc
    apply htoA_inj
    apply Subtype.ext
    change (toA b).1 = (toA c).1
    exact congr_arg (fun x : (A \ {a} : Set α) => (x : α)) hbc
  haveI : Fintype B := hB.fintype
  haveI : Fintype (A \ {a} : Set α) :=
    (hA.subset (by intro x hx; exact hx.1)).fintype
  have hle_card :
      Fintype.card B ≤ Fintype.card (A \ {a} : Set α) :=
    Fintype.card_le_of_injective toDiff htoDiff_inj
  have hle : B.ncard ≤ (A \ {a} : Set α).ncard := by
    simpa [← Nat.card_coe_set_eq] using hle_card
  have hlt : (A \ {a} : Set α).ncard < B.ncard := by
    rw [← hcard]
    exact Set.ncard_diff_singleton_lt_of_mem ha hA
  exact (not_lt_of_ge hle) hlt

private lemma putnam_2005_a2_unique_hits_of_mem_inj
    {α β : Type*} {A : Set α} {B : Set β} {f : α → β}
    (hA : A.Finite) (hB : B.Finite) (hcard : A.ncard = B.ncard)
    (hmem : ∀ a ∈ A, f a ∈ B)
    (hinj : ∀ ⦃a b : α⦄, a ∈ A → b ∈ A → f a = f b → a = b) :
    ∀ b ∈ B, ∃! a, a ∈ A ∧ f a = b := by
  classical
  haveI : Fintype A := hA.fintype
  haveI : Fintype B := hB.fintype
  let g : A → B := fun a => ⟨f a.1, hmem a.1 a.2⟩
  have hginj : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    exact hinj a.2 b.2 (congr_arg Subtype.val hab)
  have hcardF : Fintype.card A = Fintype.card B := by
    have hcardNat : Nat.card A = Nat.card B := hcard
    exact (Nat.card_eq_fintype_card (α := A)).symm.trans
      (hcardNat.trans (Nat.card_eq_fintype_card (α := B)))
  have hgsurj : Function.Surjective g :=
    hginj.surjective_of_finite (Fintype.equivOfCardEq hcardF)
  intro b hb
  obtain ⟨a, ha⟩ := hgsurj ⟨b, hb⟩
  refine ⟨a.1, ⟨a.2, congr_arg Subtype.val ha⟩, ?_⟩
  intro y hy
  have hfa : f a.1 = b := congr_arg Subtype.val ha
  exact hinj hy.1 a.2 (hy.2.trans hfa.symm)

private lemma putnam_2005_a2_value_mem_rect
    (n : ℕ) (p : ℕ → ℤ × ℤ)
    (huniq : ∀ P ∈ Set.prod (Set.Icc (1 : ℤ) (n : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)),
      ∃! i, i ∈ Set.Icc 1 (3 * n) ∧ p i = P) :
    ∀ i ∈ Set.Icc 1 (3 * n), p i ∈
      Set.prod (Set.Icc (1 : ℤ) (n : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)) := by
  classical
  apply putnam_2005_a2_mem_of_unique_hits
      (A := (Set.Icc 1 (3 * n) : Set ℕ))
      (B := Set.prod (Set.Icc (1 : ℤ) (n : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)))
      (f := p)
  · exact Set.finite_Icc 1 (3 * n)
  · change ((Set.Icc (1 : ℤ) (n : ℤ)) ×ˢ (Set.Icc (1 : ℤ) (3 : ℤ))).Finite
    exact (Set.finite_Icc (1 : ℤ) (n : ℤ)).prod (Set.finite_Icc (1 : ℤ) (3 : ℤ))
  · rw [putnam_2005_a2_index_ncard, putnam_2005_a2_rect_ncard]
  · exact huniq

private lemma putnam_2005_a2_index_injective
    (n : ℕ) (p : ℕ → ℤ × ℤ)
    (huniq : ∀ P ∈ Set.prod (Set.Icc (1 : ℤ) (n : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)),
      ∃! i, i ∈ Set.Icc 1 (3 * n) ∧ p i = P) :
    ∀ ⦃i j : ℕ⦄, i ∈ Set.Icc 1 (3 * n) → j ∈ Set.Icc 1 (3 * n) →
      p i = p j → i = j := by
  intro i j hi hj hij
  have hmem := putnam_2005_a2_value_mem_rect n p huniq i hi
  exact ExistsUnique.unique (huniq (p i) hmem) ⟨hi, rfl⟩ ⟨hj, hij.symm⟩

private def putnam_2005_a2_unit (P Q : ℤ × ℤ) : Prop :=
  (P.1 = Q.1 ∧ |Q.2 - P.2| = 1) ∨ (P.2 = Q.2 ∧ |Q.1 - P.1| = 1)

private def putnam_2005_a2_rook (n : ℕ) (p : ℕ → ℤ × ℤ) : Prop :=
  (∀ P ∈ Set.prod (Set.Icc (1 : ℤ) (n : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)),
      ∃! i, i ∈ Set.Icc 1 (3 * n) ∧ p i = P) ∧
    (∀ i ∈ Set.Icc 1 (3 * n - 1), putnam_2005_a2_unit (p i) (p (i + 1))) ∧
    p 0 = 0 ∧ ∀ i > 3 * n, p i = 0

private def putnam_2005_a2_tours (n : ℕ) (r : ℤ) : Set (ℕ → ℤ × ℤ) :=
  {p | putnam_2005_a2_rook n p ∧ p 1 = ((1 : ℤ), (1 : ℤ)) ∧
    p (3 * n) = ((n : ℤ), r)}

private def putnam_2005_a2_up (P : ℤ × ℤ) : ℤ × ℤ :=
  (P.1 + 1, P.2)

private def putnam_2005_a2_down (P : ℤ × ℤ) : ℤ × ℤ :=
  (P.1 - 1, P.2)

private def putnam_2005_a2_reflectUp (P : ℤ × ℤ) : ℤ × ℤ :=
  (P.1 + 1, 4 - P.2)

private def putnam_2005_a2_reflectDown (P : ℤ × ℤ) : ℤ × ℤ :=
  (P.1 - 1, 4 - P.2)

private lemma putnam_2005_a2_down_up (P : ℤ × ℤ) :
    putnam_2005_a2_down (putnam_2005_a2_up P) = P := by
  rcases P with ⟨a, b⟩
  simp [putnam_2005_a2_down, putnam_2005_a2_up]

private lemma putnam_2005_a2_up_down_of_two_le {P : ℤ × ℤ} (hP : 2 ≤ P.1) :
    putnam_2005_a2_up (putnam_2005_a2_down P) = P := by
  rcases P with ⟨a, b⟩
  simp [putnam_2005_a2_down, putnam_2005_a2_up]

private lemma putnam_2005_a2_reflectDown_reflectUp (P : ℤ × ℤ) :
    putnam_2005_a2_reflectDown (putnam_2005_a2_reflectUp P) = P := by
  rcases P with ⟨a, b⟩
  simp [putnam_2005_a2_reflectDown, putnam_2005_a2_reflectUp]

private lemma putnam_2005_a2_reflectUp_reflectDown_of_two_le {P : ℤ × ℤ} (hP : 2 ≤ P.1) :
    putnam_2005_a2_reflectUp (putnam_2005_a2_reflectDown P) = P := by
  rcases P with ⟨a, b⟩
  simp [putnam_2005_a2_reflectDown, putnam_2005_a2_reflectUp]

private lemma putnam_2005_a2_unit_up_iff (P Q : ℤ × ℤ) :
    putnam_2005_a2_unit (putnam_2005_a2_up P) (putnam_2005_a2_up Q) ↔
      putnam_2005_a2_unit P Q := by
  rcases P with ⟨a, b⟩
  rcases Q with ⟨c, d⟩
  simp [putnam_2005_a2_unit, putnam_2005_a2_up]

private lemma putnam_2005_a2_unit_down_iff (P Q : ℤ × ℤ) :
    putnam_2005_a2_unit (putnam_2005_a2_down P) (putnam_2005_a2_down Q) ↔
      putnam_2005_a2_unit P Q := by
  rcases P with ⟨a, b⟩
  rcases Q with ⟨c, d⟩
  simp [putnam_2005_a2_unit, putnam_2005_a2_down]

private lemma putnam_2005_a2_unit_reflectUp_iff (P Q : ℤ × ℤ) :
    putnam_2005_a2_unit (putnam_2005_a2_reflectUp P) (putnam_2005_a2_reflectUp Q) ↔
      putnam_2005_a2_unit P Q := by
  rcases P with ⟨a, b⟩
  rcases Q with ⟨c, d⟩
  simp [putnam_2005_a2_unit, putnam_2005_a2_reflectUp, abs_sub_comm]

private lemma putnam_2005_a2_unit_reflectDown_iff (P Q : ℤ × ℤ) :
    putnam_2005_a2_unit (putnam_2005_a2_reflectDown P) (putnam_2005_a2_reflectDown Q) ↔
      putnam_2005_a2_unit P Q := by
  rcases P with ⟨a, b⟩
  rcases Q with ⟨c, d⟩
  simp [putnam_2005_a2_unit, putnam_2005_a2_reflectDown, abs_sub_comm]

private lemma putnam_2005_a2_first_move
    {n : ℕ} (hn2 : 2 ≤ n) {p : ℕ → ℤ × ℤ}
    (hrook : putnam_2005_a2_rook n p)
    (hp1 : p 1 = ((1 : ℤ), (1 : ℤ))) :
    p 2 = ((1 : ℤ), (2 : ℤ)) ∨ p 2 = ((2 : ℤ), (1 : ℤ)) := by
  have hp2mem := putnam_2005_a2_value_mem_rect n p hrook.1 2 (by
    constructor <;> omega)
  have hadj := hrook.2.1 1 (by
    constructor <;> omega)
  have hadj' :
      ((1 : ℤ) = (p 2).1 ∧ |(p 2).2 - (1 : ℤ)| = 1) ∨
        ((1 : ℤ) = (p 2).2 ∧ |(p 2).1 - (1 : ℤ)| = 1) := by
    simpa [putnam_2005_a2_unit, hp1] using hadj
  rcases hp2mem with ⟨hx, hy⟩
  rcases hadj' with hvert | hhor
  · left
    apply Prod.ext
    · exact hvert.1.symm
    · have hy2 : (p 2).2 = 2 := by
        have hylo : (1 : ℤ) ≤ (p 2).2 := hy.1
        have hyhi : (p 2).2 ≤ (3 : ℤ) := hy.2
        have habs := (abs_eq (show (0 : ℤ) ≤ 1 by norm_num)).mp hvert.2
        rcases habs with hrow | hrow <;> omega
      exact hy2
  · right
    apply Prod.ext
    · have hx2 : (p 2).1 = 2 := by
        have hxlo : (1 : ℤ) ≤ (p 2).1 := hx.1
        have habs := (abs_eq (show (0 : ℤ) ≤ 1 by norm_num)).mp hhor.2
        rcases habs with hcol | hcol <;> omega
      exact hx2
    · exact hhor.1.symm

private noncomputable def putnam_2005_a2_idx
    (n : ℕ) (p : ℕ → ℤ × ℤ)
    (huniq : ∀ P ∈ Set.prod (Set.Icc (1 : ℤ) (n : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)),
      ∃! i, i ∈ Set.Icc 1 (3 * n) ∧ p i = P)
    (P : ℤ × ℤ) : ℕ := by
  classical
  exact if hP : P ∈ Set.prod (Set.Icc (1 : ℤ) (n : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)) then
    Classical.choose (huniq P hP)
  else 0

private lemma putnam_2005_a2_idx_mem
    (n : ℕ) (p : ℕ → ℤ × ℤ)
    (huniq : ∀ P ∈ Set.prod (Set.Icc (1 : ℤ) (n : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)),
      ∃! i, i ∈ Set.Icc 1 (3 * n) ∧ p i = P)
    (P : ℤ × ℤ)
    (hP : P ∈ Set.prod (Set.Icc (1 : ℤ) (n : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ))) :
    putnam_2005_a2_idx n p huniq P ∈ Set.Icc 1 (3 * n) := by
  classical
  unfold putnam_2005_a2_idx
  rw [dif_pos hP]
  exact (Classical.choose_spec (huniq P hP)).1.1

private lemma putnam_2005_a2_idx_value
    (n : ℕ) (p : ℕ → ℤ × ℤ)
    (huniq : ∀ P ∈ Set.prod (Set.Icc (1 : ℤ) (n : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)),
      ∃! i, i ∈ Set.Icc 1 (3 * n) ∧ p i = P)
    (P : ℤ × ℤ)
    (hP : P ∈ Set.prod (Set.Icc (1 : ℤ) (n : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ))) :
    p (putnam_2005_a2_idx n p huniq P) = P := by
  classical
  unfold putnam_2005_a2_idx
  rw [dif_pos hP]
  exact (Classical.choose_spec (huniq P hP)).1.2

private lemma putnam_2005_a2_idx_eq_of_value
    (n : ℕ) (p : ℕ → ℤ × ℤ)
    (huniq : ∀ P ∈ Set.prod (Set.Icc (1 : ℤ) (n : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)),
      ∃! i, i ∈ Set.Icc 1 (3 * n) ∧ p i = P)
    (P : ℤ × ℤ)
    (hP : P ∈ Set.prod (Set.Icc (1 : ℤ) (n : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)))
    {i : ℕ} (hi : i ∈ Set.Icc 1 (3 * n)) (hiv : p i = P) :
    i = putnam_2005_a2_idx n p huniq P := by
  exact (ExistsUnique.unique (huniq P hP) ⟨hi, hiv⟩
    ⟨putnam_2005_a2_idx_mem n p huniq P hP,
      putnam_2005_a2_idx_value n p huniq P hP⟩)

private lemma putnam_2005_a2_neighbor_from_13
    {n : ℕ} {Q : ℤ × ℤ}
    (hQ : Q ∈ Set.prod (Set.Icc (1 : ℤ) (n : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)))
    (h : putnam_2005_a2_unit ((1 : ℤ), (3 : ℤ)) Q) :
    Q = ((1 : ℤ), (2 : ℤ)) ∨ Q = ((2 : ℤ), (3 : ℤ)) := by
  rcases Q with ⟨a, b⟩
  rcases hQ with ⟨ha, hb⟩
  simp at ha hb
  rcases h with h | h
  · left
    apply Prod.ext
    · exact h.1.symm
    · have habs := (abs_eq (show (0 : ℤ) ≤ 1 by norm_num)).mp h.2
      rcases habs with hb' | hb' <;> omega
  · right
    apply Prod.ext
    · have habs := (abs_eq (show (0 : ℤ) ≤ 1 by norm_num)).mp h.2
      rcases habs with ha' | ha' <;> omega
    · exact h.1.symm

private lemma putnam_2005_a2_neighbor_to_13
    {n : ℕ} {Q : ℤ × ℤ}
    (hQ : Q ∈ Set.prod (Set.Icc (1 : ℤ) (n : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)))
    (h : putnam_2005_a2_unit Q ((1 : ℤ), (3 : ℤ))) :
    Q = ((1 : ℤ), (2 : ℤ)) ∨ Q = ((2 : ℤ), (3 : ℤ)) := by
  rcases Q with ⟨a, b⟩
  rcases hQ with ⟨ha, hb⟩
  simp at ha hb
  rcases h with h | h
  · left
    apply Prod.ext
    · exact h.1
    · have habs := (abs_eq (show (0 : ℤ) ≤ 1 by norm_num)).mp h.2
      rcases habs with hb' | hb' <;> omega
  · right
    apply Prod.ext
    · have habs := (abs_eq (show (0 : ℤ) ≤ 1 by norm_num)).mp h.2
      rcases habs with ha' | ha' <;> omega
    · exact h.1

private lemma putnam_2005_a2_neighbor_to_left_two_right
    {n : ℕ} {Q : ℤ × ℤ}
    (hQ : Q ∈ Set.prod (Set.Icc (1 : ℤ) (n : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)))
    (hcol : (2 : ℤ) ≤ Q.1)
    (h : putnam_2005_a2_unit Q ((1 : ℤ), (2 : ℤ))) :
    Q = ((2 : ℤ), (2 : ℤ)) := by
  rcases Q with ⟨a, b⟩
  rcases hQ with ⟨ha, hb⟩
  simp at ha hb hcol ⊢
  rcases h with h | h
  · omega
  · have habs := (abs_eq (show (0 : ℤ) ≤ 1 by norm_num)).mp h.2
    rcases habs with ha' | ha' <;> omega

private lemma putnam_2005_a2_neighbor_from_left_two_right
    {n : ℕ} {Q : ℤ × ℤ}
    (hQ : Q ∈ Set.prod (Set.Icc (1 : ℤ) (n : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)))
    (hcol : (2 : ℤ) ≤ Q.1)
    (h : putnam_2005_a2_unit ((1 : ℤ), (2 : ℤ)) Q) :
    Q = ((2 : ℤ), (2 : ℤ)) := by
  rcases Q with ⟨a, b⟩
  rcases hQ with ⟨ha, hb⟩
  simp at ha hb hcol ⊢
  rcases h with h | h
  · omega
  · have habs := (abs_eq (show (0 : ℤ) ≤ 1 by norm_num)).mp h.2
    rcases habs with ha' | ha' <;> omega

private lemma putnam_2005_a2_neighbor_to_left_three_right
    {n : ℕ} {Q : ℤ × ℤ}
    (hQ : Q ∈ Set.prod (Set.Icc (1 : ℤ) (n : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)))
    (hcol : (2 : ℤ) ≤ Q.1)
    (h : putnam_2005_a2_unit Q ((1 : ℤ), (3 : ℤ))) :
    Q = ((2 : ℤ), (3 : ℤ)) := by
  rcases Q with ⟨a, b⟩
  rcases hQ with ⟨ha, hb⟩
  simp at ha hb hcol ⊢
  rcases h with h | h
  · omega
  · have habs := (abs_eq (show (0 : ℤ) ≤ 1 by norm_num)).mp h.2
    rcases habs with ha' | ha' <;> omega

private lemma putnam_2005_a2_neighbor_from_left_three_right
    {n : ℕ} {Q : ℤ × ℤ}
    (hQ : Q ∈ Set.prod (Set.Icc (1 : ℤ) (n : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)))
    (hcol : (2 : ℤ) ≤ Q.1)
    (h : putnam_2005_a2_unit ((1 : ℤ), (3 : ℤ)) Q) :
    Q = ((2 : ℤ), (3 : ℤ)) := by
  rcases Q with ⟨a, b⟩
  rcases hQ with ⟨ha, hb⟩
  simp at ha hb hcol ⊢
  rcases h with h | h
  · omega
  · have habs := (abs_eq (show (0 : ℤ) ≤ 1 by norm_num)).mp h.2
    rcases habs with ha' | ha' <;> omega

private lemma putnam_2005_a2_mem_left_two {n : ℕ} (npos : 0 < n) :
    ((1 : ℤ), (2 : ℤ)) ∈
      Set.prod (Set.Icc (1 : ℤ) (n : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)) := by
  constructor
  · constructor
    · norm_num
    · change (1 : ℤ) ≤ (n : ℤ)
      exact_mod_cast (show 1 ≤ n by omega)
  · norm_num

private lemma putnam_2005_a2_mem_left_three {n : ℕ} (npos : 0 < n) :
    ((1 : ℤ), (3 : ℤ)) ∈
      Set.prod (Set.Icc (1 : ℤ) (n : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)) := by
  constructor
  · constructor
    · norm_num
    · change (1 : ℤ) ≤ (n : ℤ)
      exact_mod_cast (show 1 ≤ n by omega)
  · norm_num

private lemma putnam_2005_a2_left_top_adjacent
    {n : ℕ} (npos : 0 < n) {r : ℤ} (hr : r = 1 ∨ r = 3)
    {p : ℕ → ℤ × ℤ} (hrook : putnam_2005_a2_rook n p)
    (hp1 : p 1 = ((1 : ℤ), (1 : ℤ)))
    (hend : p (3 * n) = ((n : ℤ), r)) :
    let i2 := putnam_2005_a2_idx n p hrook.1 ((1 : ℤ), (2 : ℤ))
    let i3 := putnam_2005_a2_idx n p hrook.1 ((1 : ℤ), (3 : ℤ))
    i2 + 1 = i3 ∨ i3 + 1 = i2 := by
  classical
  dsimp
  let h12 : ((1 : ℤ), (2 : ℤ)) ∈
      Set.prod (Set.Icc (1 : ℤ) (n : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)) :=
    putnam_2005_a2_mem_left_two npos
  let h13 : ((1 : ℤ), (3 : ℤ)) ∈
      Set.prod (Set.Icc (1 : ℤ) (n : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)) :=
    putnam_2005_a2_mem_left_three npos
  let i2 := putnam_2005_a2_idx n p hrook.1 ((1 : ℤ), (2 : ℤ))
  let i3 := putnam_2005_a2_idx n p hrook.1 ((1 : ℤ), (3 : ℤ))
  have hi2mem : i2 ∈ Set.Icc 1 (3 * n) :=
    putnam_2005_a2_idx_mem n p hrook.1 ((1 : ℤ), (2 : ℤ)) h12
  have hi3mem : i3 ∈ Set.Icc 1 (3 * n) :=
    putnam_2005_a2_idx_mem n p hrook.1 ((1 : ℤ), (3 : ℤ)) h13
  have hi2val : p i2 = ((1 : ℤ), (2 : ℤ)) :=
    putnam_2005_a2_idx_value n p hrook.1 ((1 : ℤ), (2 : ℤ)) h12
  have hi3val : p i3 = ((1 : ℤ), (3 : ℤ)) :=
    putnam_2005_a2_idx_value n p hrook.1 ((1 : ℤ), (3 : ℤ)) h13
  have hi3_ne_one : i3 ≠ 1 := by
    intro h
    have : ((1 : ℤ), (1 : ℤ)) = ((1 : ℤ), (3 : ℤ)) := by
      calc
        ((1 : ℤ), (1 : ℤ)) = p 1 := hp1.symm
        _ = p i3 := by rw [h]
        _ = ((1 : ℤ), (3 : ℤ)) := hi3val
    norm_num at this
  have hi3lo : 1 ≤ i3 := hi3mem.1
  have hi3hi : i3 ≤ 3 * n := hi3mem.2
  by_cases hendidx : i3 = 3 * n
  · have hn1 : n = 1 := by
      have hp_eq : ((1 : ℤ), (3 : ℤ)) = ((n : ℤ), r) := by
        rw [← hi3val, hendidx, hend]
      rcases hr with rfl | rfl
      · norm_num at hp_eq
      · have hnz : (n : ℤ) = 1 := by
          simpa using (congr_arg Prod.fst hp_eq).symm
        exact_mod_cast hnz
    subst n
    have hi3eq : i3 = 3 := by simpa using hendidx
    have hprev_mem : i3 - 1 ∈ Set.Icc 1 (3 * (1 : ℕ)) := by
      constructor <;> omega
    have hprev_rect := putnam_2005_a2_value_mem_rect 1 p hrook.1 (i3 - 1) hprev_mem
    have hadj := hrook.2.1 (i3 - 1) (by
      constructor <;> omega)
    have hunit_prev : putnam_2005_a2_unit (p (i3 - 1)) ((1 : ℤ), (3 : ℤ)) := by
      have hsub : i3 - 1 + 1 = i3 := by omega
      simpa [hsub, hi3val] using hadj
    have hprev_cases := putnam_2005_a2_neighbor_to_13 hprev_rect hunit_prev
    have hprev : p (i3 - 1) = ((1 : ℤ), (2 : ℤ)) := by
      rcases hprev_cases with h | h
      · exact h
      · rcases hprev_rect with ⟨hx, hy⟩
        have hx' : (p (i3 - 1)).1 = (2 : ℤ) := by simpa [h] using congr_arg Prod.fst h
        simp at hx
        omega
    have hi2eq : i3 - 1 = i2 :=
      putnam_2005_a2_idx_eq_of_value 1 p hrook.1 ((1 : ℤ), (2 : ℤ)) h12 hprev_mem hprev
    left
    omega
  · have hi3gt : 1 < i3 := by omega
    have hi3lt : i3 < 3 * n := by omega
    have hprev_idx_mem : i3 - 1 ∈ Set.Icc 1 (3 * n) := by
      constructor <;> omega
    have hnext_idx_mem : i3 + 1 ∈ Set.Icc 1 (3 * n) := by
      constructor <;> omega
    have hprev_rect := putnam_2005_a2_value_mem_rect n p hrook.1 (i3 - 1) hprev_idx_mem
    have hnext_rect := putnam_2005_a2_value_mem_rect n p hrook.1 (i3 + 1) hnext_idx_mem
    have hadj_prev := hrook.2.1 (i3 - 1) (by
      constructor <;> omega)
    have hunit_prev : putnam_2005_a2_unit (p (i3 - 1)) ((1 : ℤ), (3 : ℤ)) := by
      have hsub : i3 - 1 + 1 = i3 := by omega
      simpa [hsub, hi3val] using hadj_prev
    have hadj_next := hrook.2.1 i3 (by
      constructor <;> omega)
    have hunit_next : putnam_2005_a2_unit ((1 : ℤ), (3 : ℤ)) (p (i3 + 1)) := by
      simpa [hi3val] using hadj_next
    have hprev_cases := putnam_2005_a2_neighbor_to_13 hprev_rect hunit_prev
    have hnext_cases := putnam_2005_a2_neighbor_from_13 hnext_rect hunit_next
    have hprev_ne_next : p (i3 - 1) ≠ p (i3 + 1) := by
      intro hsame
      have hidx := putnam_2005_a2_index_injective n p hrook.1 hprev_idx_mem hnext_idx_mem hsame
      omega
    rcases hprev_cases with hprev | hprev
    · have hi2eq : i3 - 1 = i2 :=
        putnam_2005_a2_idx_eq_of_value n p hrook.1 ((1 : ℤ), (2 : ℤ)) h12
          hprev_idx_mem hprev
      left
      omega
    · rcases hnext_cases with hnext | hnext
      · have hi2eq : i3 + 1 = i2 :=
          putnam_2005_a2_idx_eq_of_value n p hrook.1 ((1 : ℤ), (2 : ℤ)) h12
            hnext_idx_mem hnext
        right
        omega
      · exfalso
        exact hprev_ne_next (by rw [hprev, hnext])

private lemma putnam_2005_a2_first_up_forces_three
    {n : ℕ} (hn2 : 2 ≤ n) {r : ℤ} (hr : r = 1 ∨ r = 3)
    {p : ℕ → ℤ × ℤ} (hrook : putnam_2005_a2_rook n p)
    (hp1 : p 1 = ((1 : ℤ), (1 : ℤ)))
    (hend : p (3 * n) = ((n : ℤ), r))
    (hp2 : p 2 = ((1 : ℤ), (2 : ℤ))) :
    p 3 = ((1 : ℤ), (3 : ℤ)) := by
  classical
  let h12 : ((1 : ℤ), (2 : ℤ)) ∈
      Set.prod (Set.Icc (1 : ℤ) (n : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)) :=
    putnam_2005_a2_mem_left_two (by omega)
  let h13 : ((1 : ℤ), (3 : ℤ)) ∈
      Set.prod (Set.Icc (1 : ℤ) (n : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)) :=
    putnam_2005_a2_mem_left_three (by omega)
  let i2 := putnam_2005_a2_idx n p hrook.1 ((1 : ℤ), (2 : ℤ))
  let i3 := putnam_2005_a2_idx n p hrook.1 ((1 : ℤ), (3 : ℤ))
  have hi2eq : i2 = 2 := by
    have h := putnam_2005_a2_idx_eq_of_value n p hrook.1
      ((1 : ℤ), (2 : ℤ)) h12 (i := 2) (by constructor <;> omega) hp2
    exact h.symm
  have hi3val : p i3 = ((1 : ℤ), (3 : ℤ)) :=
    putnam_2005_a2_idx_value n p hrook.1 ((1 : ℤ), (3 : ℤ)) h13
  have hi3_ne_one : i3 ≠ 1 := by
    intro h
    have : ((1 : ℤ), (1 : ℤ)) = ((1 : ℤ), (3 : ℤ)) := by
      calc
        ((1 : ℤ), (1 : ℤ)) = p 1 := hp1.symm
        _ = p i3 := by rw [h]
        _ = ((1 : ℤ), (3 : ℤ)) := hi3val
    norm_num at this
  have hadj := putnam_2005_a2_left_top_adjacent (n := n) (by omega) (r := r) hr
    hrook hp1 hend
  dsimp only at hadj
  have hi3eq : i3 = 3 := by
    rcases hadj with h | h
    · omega
    · omega
  rw [← hi3eq]
  exact hi3val

private lemma putnam_2005_a2_reflectUp_mem_rect
    {m : ℕ} {P : ℤ × ℤ}
    (hP : P ∈ Set.prod (Set.Icc (1 : ℤ) (m : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ))) :
    putnam_2005_a2_reflectUp P ∈
      Set.prod (Set.Icc (1 : ℤ) ((m + 1 : ℕ) : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)) := by
  rcases P with ⟨a, b⟩
  rcases hP with ⟨ha, hb⟩
  simp [putnam_2005_a2_reflectUp] at ha hb ⊢
  constructor <;> constructor <;> omega

private lemma putnam_2005_a2_reflectDown_mem_rect
    {m : ℕ} {P : ℤ × ℤ}
    (hP : P ∈ Set.prod (Set.Icc (1 : ℤ) ((m + 1 : ℕ) : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)))
    (hcol : 2 ≤ P.1) :
    putnam_2005_a2_reflectDown P ∈
      Set.prod (Set.Icc (1 : ℤ) (m : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)) := by
  rcases P with ⟨a, b⟩
  rcases hP with ⟨ha, hb⟩
  simp [putnam_2005_a2_reflectDown] at ha hb hcol ⊢
  constructor <;> constructor <;> omega

private lemma putnam_2005_a2_up_mem_rect
    {m : ℕ} {P : ℤ × ℤ}
    (hP : P ∈ Set.prod (Set.Icc (1 : ℤ) (m : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ))) :
    putnam_2005_a2_up P ∈
      Set.prod (Set.Icc (1 : ℤ) ((m + 1 : ℕ) : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)) := by
  rcases P with ⟨a, b⟩
  rcases hP with ⟨ha, hb⟩
  simp [putnam_2005_a2_up] at ha hb ⊢
  constructor <;> constructor <;> omega

private lemma putnam_2005_a2_down_mem_rect
    {m : ℕ} {P : ℤ × ℤ}
    (hP : P ∈ Set.prod (Set.Icc (1 : ℤ) ((m + 1 : ℕ) : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)))
    (hcol : 2 ≤ P.1) :
    putnam_2005_a2_down P ∈
      Set.prod (Set.Icc (1 : ℤ) (m : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)) := by
  rcases P with ⟨a, b⟩
  rcases hP with ⟨ha, hb⟩
  simp [putnam_2005_a2_down] at ha hb hcol ⊢
  constructor <;> constructor <;> omega

private lemma putnam_2005_a2_mem_rect_succ
    {m : ℕ} {P : ℤ × ℤ}
    (hP : P ∈ Set.prod (Set.Icc (1 : ℤ) (m : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ))) :
    P ∈ Set.prod (Set.Icc (1 : ℤ) ((m + 1 : ℕ) : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)) := by
  rcases P with ⟨a, b⟩
  rcases hP with ⟨ha, hb⟩
  simp at ha hb ⊢
  constructor <;> constructor <;> omega

private def putnam_2005_a2_prependVertical
    (m : ℕ) (q : ℕ → ℤ × ℤ) : ℕ → ℤ × ℤ :=
  fun i =>
    if i = 0 then 0
    else if i = 1 then ((1 : ℤ), (1 : ℤ))
    else if i = 2 then ((1 : ℤ), (2 : ℤ))
    else if i = 3 then ((1 : ℤ), (3 : ℤ))
    else if i ≤ 3 * (m + 1) then putnam_2005_a2_reflectUp (q (i - 3))
    else 0

private def putnam_2005_a2_stripVertical
    (m : ℕ) (p : ℕ → ℤ × ℤ) : ℕ → ℤ × ℤ :=
  fun i =>
    if i = 0 then 0
    else if i ≤ 3 * m then putnam_2005_a2_reflectDown (p (i + 3))
    else 0

@[simp] private lemma putnam_2005_a2_prependVertical_zero
    (m : ℕ) (q : ℕ → ℤ × ℤ) :
    putnam_2005_a2_prependVertical m q 0 = 0 := by
  simp [putnam_2005_a2_prependVertical]

@[simp] private lemma putnam_2005_a2_prependVertical_one
    (m : ℕ) (q : ℕ → ℤ × ℤ) :
    putnam_2005_a2_prependVertical m q 1 = ((1 : ℤ), (1 : ℤ)) := by
  simp [putnam_2005_a2_prependVertical]

@[simp] private lemma putnam_2005_a2_prependVertical_two
    (m : ℕ) (q : ℕ → ℤ × ℤ) :
    putnam_2005_a2_prependVertical m q 2 = ((1 : ℤ), (2 : ℤ)) := by
  simp [putnam_2005_a2_prependVertical]

@[simp] private lemma putnam_2005_a2_prependVertical_three
    (m : ℕ) (q : ℕ → ℤ × ℤ) :
    putnam_2005_a2_prependVertical m q 3 = ((1 : ℤ), (3 : ℤ)) := by
  simp [putnam_2005_a2_prependVertical]

private lemma putnam_2005_a2_prependVertical_shift
    {m i : ℕ} (q : ℕ → ℤ × ℤ) (hlo : 4 ≤ i) (hhi : i ≤ 3 * (m + 1)) :
    putnam_2005_a2_prependVertical m q i =
      putnam_2005_a2_reflectUp (q (i - 3)) := by
  have h0 : i ≠ 0 := by omega
  have h1 : i ≠ 1 := by omega
  have h2 : i ≠ 2 := by omega
  have h3 : i ≠ 3 := by omega
  simp [putnam_2005_a2_prependVertical, h0, h1, h2, h3, hhi]

private lemma putnam_2005_a2_prependVertical_after
    {m i : ℕ} (q : ℕ → ℤ × ℤ) (hhi : 3 * (m + 1) < i) :
    putnam_2005_a2_prependVertical m q i = 0 := by
  have h0 : i ≠ 0 := by omega
  have h1 : i ≠ 1 := by omega
  have h2 : i ≠ 2 := by omega
  have h3 : i ≠ 3 := by omega
  have hle : ¬ i ≤ 3 * (m + 1) := by omega
  simp [putnam_2005_a2_prependVertical, h0, h1, h2, h3, hle]

@[simp] private lemma putnam_2005_a2_stripVertical_zero
    (m : ℕ) (p : ℕ → ℤ × ℤ) :
    putnam_2005_a2_stripVertical m p 0 = 0 := by
  simp [putnam_2005_a2_stripVertical]

private lemma putnam_2005_a2_stripVertical_shift
    {m i : ℕ} (p : ℕ → ℤ × ℤ) (hlo : 1 ≤ i) (hhi : i ≤ 3 * m) :
    putnam_2005_a2_stripVertical m p i =
      putnam_2005_a2_reflectDown (p (i + 3)) := by
  have h0 : i ≠ 0 := by omega
  simp [putnam_2005_a2_stripVertical, h0, hhi]

private lemma putnam_2005_a2_stripVertical_after
    {m i : ℕ} (p : ℕ → ℤ × ℤ) (hhi : 3 * m < i) :
    putnam_2005_a2_stripVertical m p i = 0 := by
  have h0 : i ≠ 0 := by omega
  have hle : ¬ i ≤ 3 * m := by omega
  simp [putnam_2005_a2_stripVertical, h0, hle]

private lemma putnam_2005_a2_prependVertical_tour
    {m : ℕ} (hmpos : 0 < m) {r : ℤ} {q : ℕ → ℤ × ℤ}
    (hq : q ∈ putnam_2005_a2_tours m (4 - r)) :
    putnam_2005_a2_prependVertical m q ∈ putnam_2005_a2_tours (m + 1) r ∧
      putnam_2005_a2_prependVertical m q 2 = ((1 : ℤ), (2 : ℤ)) := by
  classical
  let p := putnam_2005_a2_prependVertical m q
  rcases hq with ⟨hrookq, hq1, hqend⟩
  have hqmem := putnam_2005_a2_value_mem_rect m q hrookq.1
  have hqinj := putnam_2005_a2_index_injective m q hrookq.1
  have hsub_mem_rect :
      ∀ {j : ℕ}, 4 ≤ j → j ≤ 3 * (m + 1) → j - 3 ∈ Set.Icc 1 (3 * m) := by
    intro j hj4 hjhi
    constructor
    · omega
    · have h := Nat.sub_le_sub_right hjhi 3
      have hcalc : 3 * (m + 1) - 3 = 3 * m := by omega
      simpa [hcalc] using h
  have hsub_mem_adj :
      ∀ {i : ℕ}, 4 ≤ i → i ≤ 3 * (m + 1) - 1 →
        i - 3 ∈ Set.Icc 1 (3 * m - 1) := by
    intro i hi4 hihi
    constructor
    · omega
    · have h := Nat.sub_le_sub_right hihi 3
      have hcalc : 3 * (m + 1) - 1 - 3 = 3 * m - 1 := by omega
      simpa [hcalc] using h
  have hadd_mem_rect :
      ∀ {k : ℕ}, k ∈ Set.Icc 1 (3 * m) → k + 3 ∈ Set.Icc 1 (3 * (m + 1)) := by
    intro k hk
    rcases hk with ⟨hklo, hkhi⟩
    constructor
    · omega
    · have hcalc : 3 * (m + 1) = 3 * m + 3 := by omega
      omega
  have hpuniq :
      ∀ P ∈ Set.prod (Set.Icc (1 : ℤ) ((m + 1 : ℕ) : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)),
        ∃! i, i ∈ Set.Icc 1 (3 * (m + 1)) ∧ p i = P := by
    intro P hP
    rcases P with ⟨a, b⟩
    rcases hP with ⟨ha, hb⟩
    simp at ha hb
    by_cases ha1 : a = 1
    · subst a
      have hblo : (1 : ℤ) ≤ b := hb.1
      have hbhi : b ≤ (3 : ℤ) := hb.2
      interval_cases b
      · refine ⟨1, ?_, ?_⟩
        · constructor
          · constructor <;> omega
          · simp [p]
        · intro j hj
          rcases hj with ⟨hjmem, hjval⟩
          rcases hjmem with ⟨hjlo, hjhi⟩
          by_cases hjle : j ≤ 3
          · interval_cases j <;> simp [p] at hjval ⊢
          · have hj4 : 4 ≤ j := by omega
            have hjshift :
                p j = putnam_2005_a2_reflectUp (q (j - 3)) := by
              exact putnam_2005_a2_prependVertical_shift q hj4 hjhi
            have hjm : j - 3 ∈ Set.Icc 1 (3 * m) := hsub_mem_rect hj4 hjhi
            have hqrect := hqmem (j - 3) hjm
            rcases hqrect with ⟨hx, hy⟩
            have hfst : (p j).1 = (q (j - 3)).1 + 1 := by
              rw [hjshift]
              simp [putnam_2005_a2_reflectUp]
            have : (2 : ℤ) ≤ (p j).1 := by
              rw [hfst]
              have : (1 : ℤ) ≤ (q (j - 3)).1 := hx.1
              omega
            have hjfst : (p j).1 = (1 : ℤ) := by rw [hjval]
            omega
      · refine ⟨2, ?_, ?_⟩
        · constructor
          · constructor <;> omega
          · simp [p]
        · intro j hj
          rcases hj with ⟨hjmem, hjval⟩
          rcases hjmem with ⟨hjlo, hjhi⟩
          by_cases hjle : j ≤ 3
          · interval_cases j <;> simp [p] at hjval ⊢
          · have hj4 : 4 ≤ j := by omega
            have hjshift :
                p j = putnam_2005_a2_reflectUp (q (j - 3)) := by
              exact putnam_2005_a2_prependVertical_shift q hj4 hjhi
            have hjm : j - 3 ∈ Set.Icc 1 (3 * m) := hsub_mem_rect hj4 hjhi
            have hqrect := hqmem (j - 3) hjm
            rcases hqrect with ⟨hx, hy⟩
            have hfst : (p j).1 = (q (j - 3)).1 + 1 := by
              rw [hjshift]
              simp [putnam_2005_a2_reflectUp]
            have : (2 : ℤ) ≤ (p j).1 := by
              rw [hfst]
              have : (1 : ℤ) ≤ (q (j - 3)).1 := hx.1
              omega
            have hjfst : (p j).1 = (1 : ℤ) := by rw [hjval]
            omega
      · refine ⟨3, ?_, ?_⟩
        · constructor
          · constructor <;> omega
          · simp [p]
        · intro j hj
          rcases hj with ⟨hjmem, hjval⟩
          rcases hjmem with ⟨hjlo, hjhi⟩
          by_cases hjle : j ≤ 3
          · interval_cases j <;> simp [p] at hjval ⊢
          · have hj4 : 4 ≤ j := by omega
            have hjshift :
                p j = putnam_2005_a2_reflectUp (q (j - 3)) := by
              exact putnam_2005_a2_prependVertical_shift q hj4 hjhi
            have hjm : j - 3 ∈ Set.Icc 1 (3 * m) := hsub_mem_rect hj4 hjhi
            have hqrect := hqmem (j - 3) hjm
            rcases hqrect with ⟨hx, hy⟩
            have hfst : (p j).1 = (q (j - 3)).1 + 1 := by
              rw [hjshift]
              simp [putnam_2005_a2_reflectUp]
            have : (2 : ℤ) ≤ (p j).1 := by
              rw [hfst]
              have : (1 : ℤ) ≤ (q (j - 3)).1 := hx.1
              omega
            have hjfst : (p j).1 = (1 : ℤ) := by rw [hjval]
            omega
    · have ha2 : (2 : ℤ) ≤ a := by omega
      let Q : ℤ × ℤ := putnam_2005_a2_reflectDown (a, b)
      have hQmem : Q ∈
          Set.prod (Set.Icc (1 : ℤ) (m : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)) := by
        exact putnam_2005_a2_reflectDown_mem_rect (P := (a, b)) ⟨ha, hb⟩ ha2
      obtain ⟨k, hk, hkuniq⟩ := hrookq.1 Q hQmem
      refine ⟨k + 3, ?_, ?_⟩
      · constructor
        · exact hadd_mem_rect hk.1
        · have hkshift :
            p (k + 3) = putnam_2005_a2_reflectUp (q k) := by
            have hklo : 1 ≤ k := hk.1.1
            have hlo : 4 ≤ k + 3 := by omega
            have hhi : k + 3 ≤ 3 * (m + 1) := (hadd_mem_rect hk.1).2
            simpa [p] using putnam_2005_a2_prependVertical_shift q hlo hhi
          have hback : putnam_2005_a2_reflectUp Q = (a, b) := by
            exact putnam_2005_a2_reflectUp_reflectDown_of_two_le ha2
          rw [hkshift, hk.2, hback]
      · intro j hj
        rcases hj with ⟨hjmem, hjval⟩
        rcases hjmem with ⟨hjlo, hjhi⟩
        have hjge4 : 4 ≤ j := by
          by_contra hnot
          have hjle : j ≤ 3 := by omega
          interval_cases j <;> simp [p] at hjval <;> omega
        have hjshift :
            p j = putnam_2005_a2_reflectUp (q (j - 3)) := by
          exact putnam_2005_a2_prependVertical_shift q hjge4 hjhi
        have hjm : j - 3 ∈ Set.Icc 1 (3 * m) := hsub_mem_rect hjge4 hjhi
        have hqval : q (j - 3) = Q := by
          have hdown : putnam_2005_a2_reflectDown (p j) = Q := by
            rw [hjval]
          rw [hjshift] at hdown
          simpa [Q, putnam_2005_a2_reflectDown_reflectUp] using hdown
        have hkeq : j - 3 = k := hkuniq (j - 3) ⟨hjm, hqval⟩
        omega
  have hpadj :
      ∀ i ∈ Set.Icc 1 (3 * (m + 1) - 1), putnam_2005_a2_unit (p i) (p (i + 1)) := by
    intro i hi
    rcases hi with ⟨hilo, hihi⟩
    by_cases hi1 : i = 1
    · subst i
      simp [p, putnam_2005_a2_unit]
    by_cases hi2 : i = 2
    · subst i
      simp [p, putnam_2005_a2_unit]
    by_cases hi3 : i = 3
    · subst i
      have hp4 : p 4 = ((2 : ℤ), (3 : ℤ)) := by
        have hshift : p 4 = putnam_2005_a2_reflectUp (q 1) := by
          simpa [p] using putnam_2005_a2_prependVertical_shift q (m := m) (i := 4)
            (by omega) (by omega)
        rw [hshift, hq1]
        simp [putnam_2005_a2_reflectUp]
      simp [p, hp4, putnam_2005_a2_unit]
    · have hi4 : 4 ≤ i := by omega
      have hiq : i - 3 ∈ Set.Icc 1 (3 * m - 1) := hsub_mem_adj hi4 hihi
      have hile_full : i ≤ 3 * (m + 1) := by omega
      have hi1le_full : i + 1 ≤ 3 * (m + 1) := by omega
      have hshift1 :
          p i = putnam_2005_a2_reflectUp (q (i - 3)) :=
        putnam_2005_a2_prependVertical_shift q hi4 hile_full
      have hshift2 :
          p (i + 1) = putnam_2005_a2_reflectUp (q ((i - 3) + 1)) := by
        have harg : i + 1 - 3 = (i - 3) + 1 := by omega
        calc
          p (i + 1) = putnam_2005_a2_reflectUp (q (i + 1 - 3)) :=
            putnam_2005_a2_prependVertical_shift q (by omega) hi1le_full
          _ = putnam_2005_a2_reflectUp (q ((i - 3) + 1)) := by rw [harg]
      have hqadj := hrookq.2.1 (i - 3) hiq
      rw [hshift1, hshift2]
      exact (putnam_2005_a2_unit_reflectUp_iff _ _).2 hqadj
  have hp0 : p 0 = 0 := by simp [p]
  have hpafter : ∀ i > 3 * (m + 1), p i = 0 := by
    intro i hi
    exact putnam_2005_a2_prependVertical_after q hi
  have hpend : p (3 * (m + 1)) = (((m + 1 : ℕ) : ℤ), r) := by
    have hshift :
        p (3 * (m + 1)) = putnam_2005_a2_reflectUp (q (3 * m)) := by
      have harg : 3 * (m + 1) - 3 = 3 * m := by omega
      calc
        p (3 * (m + 1)) =
            putnam_2005_a2_reflectUp (q (3 * (m + 1) - 3)) :=
          putnam_2005_a2_prependVertical_shift q (by omega) (by omega)
        _ = putnam_2005_a2_reflectUp (q (3 * m)) := by rw [harg]
    rw [hshift, hqend]
    simp [putnam_2005_a2_reflectUp]
  refine ⟨?_, ?_⟩
  · refine ⟨?_, by simp [p], hpend⟩
    exact ⟨hpuniq, hpadj, hp0, hpafter⟩
  · simp [p]

private lemma putnam_2005_a2_first_up_later_two_le
    {n : ℕ} (hn2 : 2 ≤ n) {r : ℤ} (hr : r = 1 ∨ r = 3)
    {p : ℕ → ℤ × ℤ} (hrook : putnam_2005_a2_rook n p)
    (hp1 : p 1 = ((1 : ℤ), (1 : ℤ)))
    (hend : p (3 * n) = ((n : ℤ), r))
    (hp2 : p 2 = ((1 : ℤ), (2 : ℤ)))
    {i : ℕ} (hi4 : 4 ≤ i) (hiend : i ≤ 3 * n) :
    (2 : ℤ) ≤ (p i).1 := by
  classical
  have hp3 := putnam_2005_a2_first_up_forces_three hn2 hr hrook hp1 hend hp2
  have himem : i ∈ Set.Icc 1 (3 * n) := by constructor <;> omega
  have hrect := putnam_2005_a2_value_mem_rect n p hrook.1 i himem
  rcases hrect with ⟨hx, hy⟩
  simp at hx hy
  by_contra hnot
  have hxone : (p i).1 = (1 : ℤ) := by omega
  let b : ℤ := (p i).2
  have hblo : (1 : ℤ) ≤ b := hy.1
  have hbhi : b ≤ (3 : ℤ) := hy.2
  have hb_cases : b = (1 : ℤ) ∨ b = (2 : ℤ) ∨ b = (3 : ℤ) := by omega
  rcases hb_cases with hb | hb | hb
  · have hsame : p i = p 1 := by
      apply Prod.ext
      · rw [hp1]
        exact hxone
      · dsimp [b] at *
        rw [hp1]
        change b = (1 : ℤ)
        exact hb
    have hidx := putnam_2005_a2_index_injective n p hrook.1 himem
      (by constructor <;> omega) hsame
    omega
  · have hsame : p i = p 2 := by
      apply Prod.ext
      · rw [hp2]
        exact hxone
      · dsimp [b] at *
        rw [hp2]
        change b = (2 : ℤ)
        exact hb
    have hidx := putnam_2005_a2_index_injective n p hrook.1 himem
      (by constructor <;> omega) hsame
    omega
  · have hsame : p i = p 3 := by
      apply Prod.ext
      · rw [hp3]
        exact hxone
      · dsimp [b] at *
        rw [hp3]
        change b = (3 : ℤ)
        exact hb
    have hidx := putnam_2005_a2_index_injective n p hrook.1 himem
      (by constructor <;> omega) hsame
    omega

private lemma putnam_2005_a2_stripVertical_tour
    {m : ℕ} (hmpos : 0 < m) {r : ℤ} (hr : r = 1 ∨ r = 3)
    {p : ℕ → ℤ × ℤ}
    (hp : p ∈ putnam_2005_a2_tours (m + 1) r)
    (hp2 : p 2 = ((1 : ℤ), (2 : ℤ))) :
    putnam_2005_a2_stripVertical m p ∈ putnam_2005_a2_tours m (4 - r) := by
  classical
  let q := putnam_2005_a2_stripVertical m p
  rcases hp with ⟨hrookp, hp1, hpend⟩
  have hp3 := putnam_2005_a2_first_up_forces_three (n := m + 1) (by omega) hr hrookp hp1 hpend hp2
  have hpmem := putnam_2005_a2_value_mem_rect (m + 1) p hrookp.1
  have hpinj := putnam_2005_a2_index_injective (m + 1) p hrookp.1
  have hle_later :
      ∀ {i : ℕ}, 4 ≤ i → i ≤ 3 * (m + 1) → (2 : ℤ) ≤ (p i).1 := by
    intro i hi4 hihi
    exact putnam_2005_a2_first_up_later_two_le (n := m + 1) (by omega) hr
      hrookp hp1 hpend hp2 hi4 hihi
  have hp4 : p 4 = ((2 : ℤ), (3 : ℤ)) := by
    have h4mem : 4 ∈ Set.Icc 1 (3 * (m + 1)) := by constructor <;> omega
    have h4rect := hpmem 4 h4mem
    have hunit := hrookp.2.1 3 (by constructor <;> omega)
    have hunit' : putnam_2005_a2_unit ((1 : ℤ), (3 : ℤ)) (p 4) := by
      simpa [hp3] using hunit
    have hcases := putnam_2005_a2_neighbor_from_13 h4rect hunit'
    rcases hcases with h | h
    · have hcol := hle_later (i := 4) (by omega) (by omega)
      rw [h] at hcol
      norm_num at hcol
    · exact h
  have hsub_add_mem :
      ∀ {k : ℕ}, k ∈ Set.Icc 1 (3 * m) → k + 3 ∈ Set.Icc 1 (3 * (m + 1)) := by
    intro k hk
    rcases hk with ⟨hklo, hkhi⟩
    constructor
    · omega
    · have hcalc : 3 * (m + 1) = 3 * m + 3 := by omega
      omega
  have hsub_add_adj :
      ∀ {k : ℕ}, k ∈ Set.Icc 1 (3 * m - 1) →
        k + 3 ∈ Set.Icc 1 (3 * (m + 1) - 1) := by
    intro k hk
    rcases hk with ⟨hklo, hkhi⟩
    constructor
    · omega
    · have hcalc : 3 * (m + 1) - 1 = 3 * m + 2 := by omega
      omega
  have hquniq :
      ∀ Q ∈ Set.prod (Set.Icc (1 : ℤ) (m : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)),
        ∃! k, k ∈ Set.Icc 1 (3 * m) ∧ q k = Q := by
    intro Q hQ
    let P := putnam_2005_a2_reflectUp Q
    have hPmem : P ∈
        Set.prod (Set.Icc (1 : ℤ) ((m + 1 : ℕ) : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)) :=
      putnam_2005_a2_reflectUp_mem_rect hQ
    obtain ⟨j, hj, hjuniq⟩ := hrookp.1 P hPmem
    have hjge4 : 4 ≤ j := by
      by_contra hnot
      have hjle : j ≤ 3 := by omega
      rcases hj with ⟨hjmem, hjval⟩
      rcases hjmem with ⟨hjlo, hjhi⟩
      have hPcol : (2 : ℤ) ≤ P.1 := by
        rcases Q with ⟨a, b⟩
        rcases hQ with ⟨ha, hb⟩
        simp [P, putnam_2005_a2_reflectUp] at ha hb ⊢
        omega
      interval_cases j
      · rw [hp1] at hjval
        have : P.1 = (1 : ℤ) := by simpa using (congr_arg Prod.fst hjval).symm
        omega
      · rw [hp2] at hjval
        have : P.1 = (1 : ℤ) := by simpa using (congr_arg Prod.fst hjval).symm
        omega
      · rw [hp3] at hjval
        have : P.1 = (1 : ℤ) := by simpa using (congr_arg Prod.fst hjval).symm
        omega
    have hjmem' : j ∈ Set.Icc 1 (3 * (m + 1)) := hj.1
    refine ⟨j - 3, ?_, ?_⟩
    · constructor
      · constructor
        · omega
        · have h := Nat.sub_le_sub_right hjmem'.2 3
          have hcalc : 3 * (m + 1) - 3 = 3 * m := by omega
          simpa [hcalc] using h
      · have hstrip :
            q (j - 3) = putnam_2005_a2_reflectDown (p j) := by
          have harg : j - 3 + 3 = j := by omega
          calc
            q (j - 3) = putnam_2005_a2_reflectDown (p ((j - 3) + 3)) := by
              exact putnam_2005_a2_stripVertical_shift p (by omega) (by
                have h := Nat.sub_le_sub_right hjmem'.2 3
                have hcalc : 3 * (m + 1) - 3 = 3 * m := by omega
                simpa [hcalc] using h)
            _ = putnam_2005_a2_reflectDown (p j) := by rw [harg]
        rw [hstrip, hj.2]
        exact putnam_2005_a2_reflectDown_reflectUp Q
    · intro k hk
      rcases hk with ⟨hkmem, hkval⟩
      have hkaddmem := hsub_add_mem hkmem
      have hkshift :
          q k = putnam_2005_a2_reflectDown (p (k + 3)) :=
        putnam_2005_a2_stripVertical_shift p hkmem.1 hkmem.2
      have hpadd_col : (2 : ℤ) ≤ (p (k + 3)).1 :=
        hle_later (i := k + 3) (by
          have hklo : 1 ≤ k := hkmem.1
          omega) hkaddmem.2
      have hpadd_eq : p (k + 3) = P := by
        have hup : putnam_2005_a2_reflectUp (q k) = putnam_2005_a2_reflectUp Q := by
          rw [hkval]
        rw [hkshift] at hup
        simpa [P, putnam_2005_a2_reflectUp_reflectDown_of_two_le hpadd_col] using hup
      have hjeq : k + 3 = j := hjuniq (k + 3) ⟨hkaddmem, hpadd_eq⟩
      omega
  have hqadj :
      ∀ i ∈ Set.Icc 1 (3 * m - 1), putnam_2005_a2_unit (q i) (q (i + 1)) := by
    intro i hi
    rcases hi with ⟨hilo, hihi⟩
    have himem : i ∈ Set.Icc 1 (3 * m - 1) := ⟨hilo, hihi⟩
    have hiadd := hsub_add_adj himem
    have hqi : q i = putnam_2005_a2_reflectDown (p (i + 3)) :=
      putnam_2005_a2_stripVertical_shift p hilo (by omega)
    have hqip1 : q (i + 1) = putnam_2005_a2_reflectDown (p ((i + 3) + 1)) := by
      have harg : i + 1 + 3 = (i + 3) + 1 := by omega
      calc
        q (i + 1) = putnam_2005_a2_reflectDown (p (i + 1 + 3)) :=
          putnam_2005_a2_stripVertical_shift p (by omega) (by omega)
        _ = putnam_2005_a2_reflectDown (p ((i + 3) + 1)) := by rw [harg]
    have hpadj := hrookp.2.1 (i + 3) hiadd
    rw [hqi, hqip1]
    exact (putnam_2005_a2_unit_reflectDown_iff _ _).2 hpadj
  have hq0 : q 0 = 0 := by simp [q]
  have hqafter : ∀ i > 3 * m, q i = 0 := by
    intro i hi
    exact putnam_2005_a2_stripVertical_after p hi
  have hq1 : q 1 = ((1 : ℤ), (1 : ℤ)) := by
    have hstrip : q 1 = putnam_2005_a2_reflectDown (p 4) :=
      putnam_2005_a2_stripVertical_shift p (by omega) (by omega)
    rw [hstrip, hp4]
    simp [putnam_2005_a2_reflectDown]
  have hqend : q (3 * m) = ((m : ℤ), 4 - r) := by
    have hstrip : q (3 * m) =
        putnam_2005_a2_reflectDown (p (3 * (m + 1))) := by
      have harg : 3 * m + 3 = 3 * (m + 1) := by omega
      calc
        q (3 * m) = putnam_2005_a2_reflectDown (p (3 * m + 3)) :=
          putnam_2005_a2_stripVertical_shift p (by omega) (by omega)
        _ = putnam_2005_a2_reflectDown (p (3 * (m + 1))) := by rw [harg]
    rw [hstrip, hpend]
    simp [putnam_2005_a2_reflectDown]
  exact ⟨⟨hquniq, hqadj, hq0, hqafter⟩, hq1, hqend⟩

private lemma putnam_2005_a2_strip_prependVertical
    {m : ℕ} {r : ℤ} {q : ℕ → ℤ × ℤ}
    (hq : q ∈ putnam_2005_a2_tours m r) :
    putnam_2005_a2_stripVertical m (putnam_2005_a2_prependVertical m q) = q := by
  classical
  rcases hq with ⟨hrookq, hq1, hqend⟩
  funext i
  by_cases hi0 : i = 0
  · subst i
    simp [putnam_2005_a2_stripVertical]
    exact hrookq.2.2.1.symm
  by_cases hi : i ≤ 3 * m
  · have hilo : 1 ≤ i := by omega
    have hstrip :
        putnam_2005_a2_stripVertical m (putnam_2005_a2_prependVertical m q) i =
          putnam_2005_a2_reflectDown
            (putnam_2005_a2_prependVertical m q (i + 3)) :=
      putnam_2005_a2_stripVertical_shift _ hilo hi
    have hprep :
        putnam_2005_a2_prependVertical m q (i + 3) =
          putnam_2005_a2_reflectUp (q i) := by
      have harg : i + 3 - 3 = i := by omega
      calc
        putnam_2005_a2_prependVertical m q (i + 3) =
            putnam_2005_a2_reflectUp (q (i + 3 - 3)) :=
          putnam_2005_a2_prependVertical_shift q (by omega) (by
            have hcalc : 3 * (m + 1) = 3 * m + 3 := by omega
            omega)
        _ = putnam_2005_a2_reflectUp (q i) := by rw [harg]
    rw [hstrip, hprep, putnam_2005_a2_reflectDown_reflectUp]
  · have hgt : i > 3 * m := by omega
    rw [putnam_2005_a2_stripVertical_after _ hgt]
    exact (hrookq.2.2.2 i hgt).symm

private lemma putnam_2005_a2_prepend_stripVertical
    {m : ℕ} (hmpos : 0 < m) {r : ℤ} (hr : r = 1 ∨ r = 3)
    {p : ℕ → ℤ × ℤ}
    (hp : p ∈ putnam_2005_a2_tours (m + 1) r)
    (hp2 : p 2 = ((1 : ℤ), (2 : ℤ))) :
    putnam_2005_a2_prependVertical m (putnam_2005_a2_stripVertical m p) = p := by
  classical
  rcases hp with ⟨hrookp, hp1, hpend⟩
  have hp3 := putnam_2005_a2_first_up_forces_three (n := m + 1) (by omega) hr hrookp hp1 hpend hp2
  funext i
  by_cases hi0 : i = 0
  · subst i
    simp [putnam_2005_a2_prependVertical]
    exact hrookp.2.2.1.symm
  by_cases hi1 : i = 1
  · subst i
    simp [putnam_2005_a2_prependVertical, hp1]
  by_cases hi2 : i = 2
  · subst i
    simp [putnam_2005_a2_prependVertical, hp2]
  by_cases hi3 : i = 3
  · subst i
    simp [putnam_2005_a2_prependVertical, hp3]
  by_cases hiend : i ≤ 3 * (m + 1)
  · have hi4 : 4 ≤ i := by omega
    have hprep :
        putnam_2005_a2_prependVertical m (putnam_2005_a2_stripVertical m p) i =
          putnam_2005_a2_reflectUp (putnam_2005_a2_stripVertical m p (i - 3)) :=
      putnam_2005_a2_prependVertical_shift _ hi4 hiend
    have hstrip :
        putnam_2005_a2_stripVertical m p (i - 3) =
          putnam_2005_a2_reflectDown (p i) := by
      have harg : i - 3 + 3 = i := by omega
      calc
        putnam_2005_a2_stripVertical m p (i - 3) =
            putnam_2005_a2_reflectDown (p ((i - 3) + 3)) :=
          putnam_2005_a2_stripVertical_shift p (by omega) (by
            have h := Nat.sub_le_sub_right hiend 3
            have hcalc : 3 * (m + 1) - 3 = 3 * m := by omega
            simpa [hcalc] using h)
        _ = putnam_2005_a2_reflectDown (p i) := by rw [harg]
    have hcol : (2 : ℤ) ≤ (p i).1 :=
      putnam_2005_a2_first_up_later_two_le (n := m + 1) (by omega) hr
        hrookp hp1 hpend hp2 hi4 hiend
    rw [hprep, hstrip, putnam_2005_a2_reflectUp_reflectDown_of_two_le hcol]
  · have hgt : i > 3 * (m + 1) := by omega
    rw [putnam_2005_a2_prependVertical_after _ hgt]
    exact (hrookp.2.2.2 i hgt).symm

private lemma putnam_2005_a2_left_top_block
    {n : ℕ} (npos : 0 < n) {r : ℤ} (hr : r = 1 ∨ r = 3)
    {p : ℕ → ℤ × ℤ} (hrook : putnam_2005_a2_rook n p)
    (hp1 : p 1 = ((1 : ℤ), (1 : ℤ)))
    (hend : p (3 * n) = ((n : ℤ), r)) :
    let i2 := putnam_2005_a2_idx n p hrook.1 ((1 : ℤ), (2 : ℤ))
    let i3 := putnam_2005_a2_idx n p hrook.1 ((1 : ℤ), (3 : ℤ))
    let j := min i2 i3
    (2 ≤ j ∧ j + 1 ≤ 3 * n) ∧
      ((p j = ((1 : ℤ), (2 : ℤ)) ∧ p (j + 1) = ((1 : ℤ), (3 : ℤ))) ∨
        (p j = ((1 : ℤ), (3 : ℤ)) ∧ p (j + 1) = ((1 : ℤ), (2 : ℤ)))) := by
  classical
  dsimp
  let h12 : ((1 : ℤ), (2 : ℤ)) ∈
      Set.prod (Set.Icc (1 : ℤ) (n : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)) :=
    putnam_2005_a2_mem_left_two npos
  let h13 : ((1 : ℤ), (3 : ℤ)) ∈
      Set.prod (Set.Icc (1 : ℤ) (n : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)) :=
    putnam_2005_a2_mem_left_three npos
  let i2 := putnam_2005_a2_idx n p hrook.1 ((1 : ℤ), (2 : ℤ))
  let i3 := putnam_2005_a2_idx n p hrook.1 ((1 : ℤ), (3 : ℤ))
  have hi2mem : i2 ∈ Set.Icc 1 (3 * n) :=
    putnam_2005_a2_idx_mem n p hrook.1 ((1 : ℤ), (2 : ℤ)) h12
  have hi3mem : i3 ∈ Set.Icc 1 (3 * n) :=
    putnam_2005_a2_idx_mem n p hrook.1 ((1 : ℤ), (3 : ℤ)) h13
  have hi2val : p i2 = ((1 : ℤ), (2 : ℤ)) :=
    putnam_2005_a2_idx_value n p hrook.1 ((1 : ℤ), (2 : ℤ)) h12
  have hi3val : p i3 = ((1 : ℤ), (3 : ℤ)) :=
    putnam_2005_a2_idx_value n p hrook.1 ((1 : ℤ), (3 : ℤ)) h13
  have hi2_ne_one : i2 ≠ 1 := by
    intro h
    have : ((1 : ℤ), (1 : ℤ)) = ((1 : ℤ), (2 : ℤ)) := by
      calc
        ((1 : ℤ), (1 : ℤ)) = p 1 := hp1.symm
        _ = p i2 := by rw [h]
        _ = ((1 : ℤ), (2 : ℤ)) := hi2val
    norm_num at this
  have hi3_ne_one : i3 ≠ 1 := by
    intro h
    have : ((1 : ℤ), (1 : ℤ)) = ((1 : ℤ), (3 : ℤ)) := by
      calc
        ((1 : ℤ), (1 : ℤ)) = p 1 := hp1.symm
        _ = p i3 := by rw [h]
        _ = ((1 : ℤ), (3 : ℤ)) := hi3val
    norm_num at this
  have hadj := putnam_2005_a2_left_top_adjacent npos hr hrook hp1 hend
  dsimp only at hadj
  change (2 ≤ min i2 i3 ∧ min i2 i3 + 1 ≤ 3 * n) ∧
      ((p (min i2 i3) = ((1 : ℤ), (2 : ℤ)) ∧
          p (min i2 i3 + 1) = ((1 : ℤ), (3 : ℤ))) ∨
        (p (min i2 i3) = ((1 : ℤ), (3 : ℤ)) ∧
          p (min i2 i3 + 1) = ((1 : ℤ), (2 : ℤ))))
  rcases hadj with h23 | h32
  · change i2 + 1 = i3 at h23
    have hmin : min i2 i3 = i2 := by
      exact Nat.min_eq_left (by omega)
    rw [hmin]
    refine ⟨?_, Or.inl ?_⟩
    · constructor
      · omega
      · rw [h23]
        exact hi3mem.2
    · constructor
      · exact hi2val
      · rw [h23]
        exact hi3val
  · change i3 + 1 = i2 at h32
    have hmin : min i2 i3 = i3 := by
      exact Nat.min_eq_right (by omega)
    rw [hmin]
    refine ⟨?_, Or.inr ?_⟩
    · constructor
      · omega
      · rw [h32]
        exact hi2mem.2
    · constructor
      · exact hi3val
      · rw [h32]
        exact hi2val

private def putnam_2005_a2_expandRightAt
    (m j : ℕ) (q : ℕ → ℤ × ℤ) : ℕ → ℤ × ℤ :=
  fun i =>
    if i = 0 then 0
    else if i = 1 then ((1 : ℤ), (1 : ℤ))
    else if i ≤ j + 1 then putnam_2005_a2_up (q (i - 1))
    else if i = j + 2 then q j
    else if i = j + 3 then q (j + 1)
    else if i ≤ 3 * (m + 1) then putnam_2005_a2_up (q (i - 3))
    else 0

private def putnam_2005_a2_stripRightAt
    (m J : ℕ) (p : ℕ → ℤ × ℤ) : ℕ → ℤ × ℤ :=
  fun i =>
    if i = 0 then 0
    else if i ≤ J - 2 then putnam_2005_a2_down (p (i + 1))
    else if i ≤ 3 * m then putnam_2005_a2_down (p (i + 3))
    else 0

@[simp] private lemma putnam_2005_a2_expandRightAt_zero
    (m j : ℕ) (q : ℕ → ℤ × ℤ) :
    putnam_2005_a2_expandRightAt m j q 0 = 0 := by
  simp [putnam_2005_a2_expandRightAt]

@[simp] private lemma putnam_2005_a2_expandRightAt_one
    (m j : ℕ) (q : ℕ → ℤ × ℤ) :
    putnam_2005_a2_expandRightAt m j q 1 = ((1 : ℤ), (1 : ℤ)) := by
  simp [putnam_2005_a2_expandRightAt]

private lemma putnam_2005_a2_expandRightAt_early
    {m j i : ℕ} (q : ℕ → ℤ × ℤ) (hlo : 2 ≤ i) (hhi : i ≤ j + 1) :
    putnam_2005_a2_expandRightAt m j q i =
      putnam_2005_a2_up (q (i - 1)) := by
  have h0 : i ≠ 0 := by omega
  have h1 : i ≠ 1 := by omega
  simp [putnam_2005_a2_expandRightAt, h0, h1, hhi]

private lemma putnam_2005_a2_expandRightAt_block_first
    {m j : ℕ} (q : ℕ → ℤ × ℤ) :
    putnam_2005_a2_expandRightAt m j q (j + 2) = q j := by
  have h0 : j + 2 ≠ 0 := by omega
  have h1 : j + 2 ≠ 1 := by omega
  have hle : ¬ j + 2 ≤ j + 1 := by omega
  simp [putnam_2005_a2_expandRightAt, h0, h1, hle]

private lemma putnam_2005_a2_expandRightAt_block_second
    {m j : ℕ} (q : ℕ → ℤ × ℤ) :
    putnam_2005_a2_expandRightAt m j q (j + 3) = q (j + 1) := by
  have h0 : j + 3 ≠ 0 := by omega
  have h1 : j + 3 ≠ 1 := by omega
  have hle : ¬ j + 3 ≤ j + 1 := by omega
  have hfirst : j + 3 ≠ j + 2 := by omega
  simp [putnam_2005_a2_expandRightAt, h0, h1, hle, hfirst]

private lemma putnam_2005_a2_expandRightAt_late
    {m j i : ℕ} (q : ℕ → ℤ × ℤ) (hlo : j + 4 ≤ i)
    (hhi : i ≤ 3 * (m + 1)) :
    putnam_2005_a2_expandRightAt m j q i =
      putnam_2005_a2_up (q (i - 3)) := by
  have h0 : i ≠ 0 := by omega
  have h1 : i ≠ 1 := by omega
  have hle : ¬ i ≤ j + 1 := by omega
  have hfirst : i ≠ j + 2 := by omega
  have hsecond : i ≠ j + 3 := by omega
  simp [putnam_2005_a2_expandRightAt, h0, h1, hle, hfirst, hsecond, hhi]

private lemma putnam_2005_a2_expandRightAt_after
    {m j i : ℕ} (q : ℕ → ℤ × ℤ) (hj : j + 3 ≤ 3 * (m + 1))
    (hhi : 3 * (m + 1) < i) :
    putnam_2005_a2_expandRightAt m j q i = 0 := by
  have h0 : i ≠ 0 := by omega
  have h1 : i ≠ 1 := by omega
  have hle_end : ¬ i ≤ 3 * (m + 1) := by omega
  by_cases hle : i ≤ j + 1
  · have hjend : j + 1 ≤ 3 * (m + 1) := by omega
    omega
  · by_cases hfirst : i = j + 2
    · omega
    · by_cases hsecond : i = j + 3
      · omega
      · simp [putnam_2005_a2_expandRightAt, h0, h1, hle, hfirst, hsecond, hle_end]

private lemma putnam_2005_a2_expandRightAt_shift_of_not_block
    {m j i : ℕ} (q : ℕ → ℤ × ℤ)
    (hi : i ∈ Set.Icc 1 (3 * (m + 1)))
    (hi1 : i ≠ 1) (hib1 : i ≠ j + 2) (hib2 : i ≠ j + 3) :
    putnam_2005_a2_expandRightAt m j q i =
      putnam_2005_a2_up (q (if i ≤ j + 1 then i - 1 else i - 3)) := by
  rcases hi with ⟨hilo, hihi⟩
  by_cases hle : i ≤ j + 1
  · have hi2 : 2 ≤ i := by omega
    simp [hle, putnam_2005_a2_expandRightAt_early q hi2 hle]
  · have hlo : j + 4 ≤ i := by omega
    simp [hle, putnam_2005_a2_expandRightAt_late q hlo hihi]

private lemma putnam_2005_a2_expandRightAt_source_mem
    {m j i : ℕ} (hjbounds : 2 ≤ j ∧ j + 1 ≤ 3 * m)
    (hi : i ∈ Set.Icc 1 (3 * (m + 1)))
    (hi1 : i ≠ 1) :
    (if i ≤ j + 1 then i - 1 else i - 3) ∈ Set.Icc 1 (3 * m) := by
  rcases hi with ⟨hilo, hihi⟩
  by_cases hle : i ≤ j + 1
  · simp [hle]
    constructor <;> omega
  · simp [hle]
    constructor <;> omega

private lemma putnam_2005_a2_expandRightAt_source_eq_imp
    {m j i k : ℕ} (hjbounds : 2 ≤ j ∧ j + 1 ≤ 3 * m)
    (hi : i ∈ Set.Icc 1 (3 * (m + 1))) (hk : k ∈ Set.Icc 1 (3 * (m + 1)))
    (hi1 : i ≠ 1) (hib1 : i ≠ j + 2) (hib2 : i ≠ j + 3)
    (hk1 : k ≠ 1) (hkb1 : k ≠ j + 2) (hkb2 : k ≠ j + 3)
    (hsrc :
      (if i ≤ j + 1 then i - 1 else i - 3) =
        (if k ≤ j + 1 then k - 1 else k - 3)) :
    i = k := by
  by_cases hi_le : i ≤ j + 1 <;> by_cases hk_le : k ≤ j + 1
  · simp [hi_le, hk_le] at hsrc
    omega
  · simp [hi_le, hk_le] at hsrc
    have hkge : j + 4 ≤ k := by omega
    omega
  · simp [hi_le, hk_le] at hsrc
    have hige : j + 4 ≤ i := by omega
    omega
  · simp [hi_le, hk_le] at hsrc
    omega

@[simp] private lemma putnam_2005_a2_stripRightAt_zero
    (m J : ℕ) (p : ℕ → ℤ × ℤ) :
    putnam_2005_a2_stripRightAt m J p 0 = 0 := by
  simp [putnam_2005_a2_stripRightAt]

private lemma putnam_2005_a2_stripRightAt_early
    {m J i : ℕ} (p : ℕ → ℤ × ℤ) (hlo : 1 ≤ i) (hhi : i ≤ J - 2) :
    putnam_2005_a2_stripRightAt m J p i =
      putnam_2005_a2_down (p (i + 1)) := by
  have h0 : i ≠ 0 := by omega
  simp [putnam_2005_a2_stripRightAt, h0, hhi]

private lemma putnam_2005_a2_stripRightAt_late
    {m J i : ℕ} (p : ℕ → ℤ × ℤ) (hlo : 1 ≤ i) (hgt : J - 2 < i)
    (hhi : i ≤ 3 * m) :
    putnam_2005_a2_stripRightAt m J p i =
      putnam_2005_a2_down (p (i + 3)) := by
  have h0 : i ≠ 0 := by omega
  have hle : ¬ i ≤ J - 2 := by omega
  simp [putnam_2005_a2_stripRightAt, h0, hle, hhi]

private lemma putnam_2005_a2_stripRightAt_after
    {m J i : ℕ} (p : ℕ → ℤ × ℤ) (hJ : J + 1 ≤ 3 * (m + 1))
    (hhi : 3 * m < i) :
    putnam_2005_a2_stripRightAt m J p i = 0 := by
  have h0 : i ≠ 0 := by omega
  have hend : ¬ i ≤ 3 * m := by omega
  by_cases hle : i ≤ J - 2
  · omega
  · simp [putnam_2005_a2_stripRightAt, h0, hle, hend]

private lemma putnam_2005_a2_stripRightAt_source_mem
    {m J i : ℕ} (hJbounds : 2 ≤ J ∧ J + 1 ≤ 3 * (m + 1))
    (hi : i ∈ Set.Icc 1 (3 * m)) :
    (if i ≤ J - 2 then i + 1 else i + 3) ∈ Set.Icc 1 (3 * (m + 1)) := by
  rcases hi with ⟨hilo, hihi⟩
  by_cases hle : i ≤ J - 2
  · rw [if_pos hle]
    have hiJ : i + 2 ≤ J := Nat.add_le_of_le_sub hJbounds.1 hle
    constructor
    · omega
    · have hJhi : J + 1 ≤ 3 * (m + 1) := hJbounds.2
      omega
  · rw [if_neg hle]
    have hcalc : 3 * (m + 1) = 3 * m + 3 := by omega
    constructor
    · omega
    · rw [hcalc]
      omega

private lemma putnam_2005_a2_stripRightAt_value
    {m J i : ℕ} (p : ℕ → ℤ × ℤ)
    (hi : i ∈ Set.Icc 1 (3 * m)) :
    putnam_2005_a2_stripRightAt m J p i =
      putnam_2005_a2_down (p (if i ≤ J - 2 then i + 1 else i + 3)) := by
  rcases hi with ⟨hilo, hihi⟩
  by_cases hle : i ≤ J - 2
  · simp [hle, putnam_2005_a2_stripRightAt_early p hilo hle]
  · have hgt : J - 2 < i := Nat.lt_of_not_ge hle
    simp [hle, putnam_2005_a2_stripRightAt_late p hilo hgt hihi]

private lemma putnam_2005_a2_stripRightAt_source_eq_imp
    {m J i k : ℕ}
    (hi : i ∈ Set.Icc 1 (3 * m)) (hk : k ∈ Set.Icc 1 (3 * m))
    (hsrc :
      (if i ≤ J - 2 then i + 1 else i + 3) =
        (if k ≤ J - 2 then k + 1 else k + 3)) :
    i = k := by
  by_cases hi_le : i ≤ J - 2 <;> by_cases hk_le : k ≤ J - 2
  · simp [hi_le, hk_le] at hsrc
    omega
  · simp [hi_le, hk_le] at hsrc
    have hsrc_i_le : i + 1 ≤ J - 1 := by omega
    have hsrc_k_ge : J + 2 ≤ k + 3 := by omega
    omega
  · simp [hi_le, hk_le] at hsrc
    have hsrc_i_ge : J + 2 ≤ i + 3 := by omega
    have hsrc_k_le : k + 1 ≤ J - 1 := by omega
    omega
  · simp [hi_le, hk_le] at hsrc
    omega

private noncomputable def putnam_2005_a2_leftBlockStart
    (n : ℕ) (p : ℕ → ℤ × ℤ)
    (hrook : putnam_2005_a2_rook n p) : ℕ :=
  min (putnam_2005_a2_idx n p hrook.1 ((1 : ℤ), (2 : ℤ)))
    (putnam_2005_a2_idx n p hrook.1 ((1 : ℤ), (3 : ℤ)))

private lemma putnam_2005_a2_leftBlockStart_spec
    {n : ℕ} (npos : 0 < n) {r : ℤ} (hr : r = 1 ∨ r = 3)
    {p : ℕ → ℤ × ℤ} (hrook : putnam_2005_a2_rook n p)
    (hp1 : p 1 = ((1 : ℤ), (1 : ℤ)))
    (hend : p (3 * n) = ((n : ℤ), r)) :
    let J := putnam_2005_a2_leftBlockStart n p hrook
    (2 ≤ J ∧ J + 1 ≤ 3 * n) ∧
      ((p J = ((1 : ℤ), (2 : ℤ)) ∧ p (J + 1) = ((1 : ℤ), (3 : ℤ))) ∨
        (p J = ((1 : ℤ), (3 : ℤ)) ∧ p (J + 1) = ((1 : ℤ), (2 : ℤ)))) := by
  simpa [putnam_2005_a2_leftBlockStart] using
    putnam_2005_a2_left_top_block (n := n) npos (r := r) hr hrook hp1 hend

private lemma putnam_2005_a2_leftBlock_other_two_le
    {n J k : ℕ} {p : ℕ → ℤ × ℤ}
    (hrook : putnam_2005_a2_rook n p)
    (hp1 : p 1 = ((1 : ℤ), (1 : ℤ)))
    (hJbounds : 2 ≤ J ∧ J + 1 ≤ 3 * n)
    (hblock :
      (p J = ((1 : ℤ), (2 : ℤ)) ∧ p (J + 1) = ((1 : ℤ), (3 : ℤ))) ∨
        (p J = ((1 : ℤ), (3 : ℤ)) ∧ p (J + 1) = ((1 : ℤ), (2 : ℤ))))
    (hk : k ∈ Set.Icc 1 (3 * n))
    (hk1 : k ≠ 1) (hkJ : k ≠ J) (hkJ1 : k ≠ J + 1) :
    (2 : ℤ) ≤ (p k).1 := by
  classical
  have hrect := putnam_2005_a2_value_mem_rect n p hrook.1 k hk
  rcases hrect with ⟨hx, hy⟩
  simp at hx hy
  by_contra hnot
  have hxone : (p k).1 = (1 : ℤ) := by omega
  let b : ℤ := (p k).2
  have hb_cases : b = (1 : ℤ) ∨ b = (2 : ℤ) ∨ b = (3 : ℤ) := by
    have hblo : (1 : ℤ) ≤ b := hy.1
    have hbhi : b ≤ (3 : ℤ) := hy.2
    omega
  have h1mem : (1 : ℕ) ∈ Set.Icc 1 (3 * n) := by
    constructor <;> omega
  have hJmem : J ∈ Set.Icc 1 (3 * n) := by
    constructor <;> omega
  have hJ1mem : J + 1 ∈ Set.Icc 1 (3 * n) := by
    constructor <;> omega
  rcases hb_cases with hb | hb | hb
  · have hsame : p k = p 1 := by
      apply Prod.ext
      · rw [hp1]
        exact hxone
      · dsimp [b] at hb
        rw [hp1]
        exact hb
    have hidx := putnam_2005_a2_index_injective n p hrook.1 hk h1mem hsame
    exact hk1 hidx
  · rcases hblock with hblock | hblock
    · have hsame : p k = p J := by
        apply Prod.ext
        · rw [hblock.1]
          exact hxone
        · dsimp [b] at hb
          rw [hblock.1]
          exact hb
      have hidx := putnam_2005_a2_index_injective n p hrook.1 hk hJmem hsame
      exact hkJ hidx
    · have hsame : p k = p (J + 1) := by
        apply Prod.ext
        · rw [hblock.2]
          exact hxone
        · dsimp [b] at hb
          rw [hblock.2]
          exact hb
      have hidx := putnam_2005_a2_index_injective n p hrook.1 hk hJ1mem hsame
      exact hkJ1 hidx
  · rcases hblock with hblock | hblock
    · have hsame : p k = p (J + 1) := by
        apply Prod.ext
        · rw [hblock.2]
          exact hxone
        · dsimp [b] at hb
          rw [hblock.2]
          exact hb
      have hidx := putnam_2005_a2_index_injective n p hrook.1 hk hJ1mem hsame
      exact hkJ1 hidx
    · have hsame : p k = p J := by
        apply Prod.ext
        · rw [hblock.1]
          exact hxone
        · dsimp [b] at hb
          rw [hblock.1]
          exact hb
      have hidx := putnam_2005_a2_index_injective n p hrook.1 hk hJmem hsame
      exact hkJ hidx

private lemma putnam_2005_a2_leftBlock_bridge
    {n J : ℕ} {p : ℕ → ℤ × ℤ}
    (hrook : putnam_2005_a2_rook n p)
    (hp1 : p 1 = ((1 : ℤ), (1 : ℤ)))
    (hJbounds : 2 ≤ J ∧ J + 1 ≤ 3 * n)
    (hJge3 : 3 ≤ J)
    (hJ1lt : J + 1 < 3 * n)
    (hblock :
      (p J = ((1 : ℤ), (2 : ℤ)) ∧ p (J + 1) = ((1 : ℤ), (3 : ℤ))) ∨
        (p J = ((1 : ℤ), (3 : ℤ)) ∧ p (J + 1) = ((1 : ℤ), (2 : ℤ)))) :
    putnam_2005_a2_unit (putnam_2005_a2_down (p (J - 1)))
      (putnam_2005_a2_down (p (J + 2))) := by
  classical
  have hpmem := putnam_2005_a2_value_mem_rect n p hrook.1
  have hprev_mem_idx : J - 1 ∈ Set.Icc 1 (3 * n) := by
    constructor <;> omega
  have hnext_mem_idx : J + 2 ∈ Set.Icc 1 (3 * n) := by
    constructor <;> omega
  have hprev_rect := hpmem (J - 1) hprev_mem_idx
  have hnext_rect := hpmem (J + 2) hnext_mem_idx
  have hprev_col : (2 : ℤ) ≤ (p (J - 1)).1 := by
    exact putnam_2005_a2_leftBlock_other_two_le hrook hp1 hJbounds hblock
      hprev_mem_idx (by omega) (by omega) (by omega)
  have hnext_col : (2 : ℤ) ≤ (p (J + 2)).1 := by
    exact putnam_2005_a2_leftBlock_other_two_le hrook hp1 hJbounds hblock
      hnext_mem_idx (by omega) (by omega) (by omega)
  have hprev_adj := hrook.2.1 (J - 1) (by constructor <;> omega)
  have hnext_adj := hrook.2.1 (J + 1) (by constructor <;> omega)
  have hprev_arg : J - 1 + 1 = J := by omega
  rcases hblock with hblock | hblock
  · have hprev_unit : putnam_2005_a2_unit (p (J - 1)) ((1 : ℤ), (2 : ℤ)) := by
      simpa [hprev_arg, hblock.1] using hprev_adj
    have hnext_unit : putnam_2005_a2_unit ((1 : ℤ), (3 : ℤ)) (p (J + 2)) := by
      simpa [hblock.2] using hnext_adj
    have hprev_eq := putnam_2005_a2_neighbor_to_left_two_right hprev_rect hprev_col hprev_unit
    have hnext_eq := putnam_2005_a2_neighbor_from_left_three_right hnext_rect hnext_col hnext_unit
    rw [hprev_eq, hnext_eq]
    simp [putnam_2005_a2_unit, putnam_2005_a2_down]
  · have hprev_unit : putnam_2005_a2_unit (p (J - 1)) ((1 : ℤ), (3 : ℤ)) := by
      simpa [hprev_arg, hblock.1] using hprev_adj
    have hnext_unit : putnam_2005_a2_unit ((1 : ℤ), (2 : ℤ)) (p (J + 2)) := by
      simpa [hblock.2] using hnext_adj
    have hprev_eq := putnam_2005_a2_neighbor_to_left_three_right hprev_rect hprev_col hprev_unit
    have hnext_eq := putnam_2005_a2_neighbor_from_left_two_right hnext_rect hnext_col hnext_unit
    rw [hprev_eq, hnext_eq]
    simp [putnam_2005_a2_unit, putnam_2005_a2_down, abs_sub_comm]

private def putnam_2005_a2_toursFirstUp (n : ℕ) (r : ℤ) : Set (ℕ → ℤ × ℤ) :=
  {p | p ∈ putnam_2005_a2_tours n r ∧ p 2 = ((1 : ℤ), (2 : ℤ))}

private def putnam_2005_a2_toursFirstRight (n : ℕ) (r : ℤ) : Set (ℕ → ℤ × ℤ) :=
  {p | p ∈ putnam_2005_a2_tours n r ∧ p 2 = ((2 : ℤ), (1 : ℤ))}

private noncomputable def putnam_2005_a2_firstUpEquiv
    (m : ℕ) (hmpos : 0 < m) (r : ℤ) (hr : r = 1 ∨ r = 3) :
    (putnam_2005_a2_tours m (4 - r)) ≃
      (putnam_2005_a2_toursFirstUp (m + 1) r) where
  toFun q :=
    ⟨putnam_2005_a2_prependVertical m q.1,
      by
        have h := putnam_2005_a2_prependVertical_tour (m := m) hmpos (r := r) q.2
        exact ⟨h.1, h.2⟩⟩
  invFun p :=
    ⟨putnam_2005_a2_stripVertical m p.1,
      putnam_2005_a2_stripVertical_tour (m := m) hmpos (r := r) hr p.2.1 p.2.2⟩
  left_inv q := by
    apply Subtype.ext
    exact putnam_2005_a2_strip_prependVertical (m := m) (r := 4 - r) q.2
  right_inv p := by
    apply Subtype.ext
    exact putnam_2005_a2_prepend_stripVertical (m := m) hmpos (r := r) hr p.2.1 p.2.2

private lemma putnam_2005_a2_firstUp_encard
    (m : ℕ) (hmpos : 0 < m) (r : ℤ) (hr : r = 1 ∨ r = 3) :
    (putnam_2005_a2_toursFirstUp (m + 1) r).encard =
      (putnam_2005_a2_tours m (4 - r)).encard := by
  exact (Set.encard_congr (putnam_2005_a2_firstUpEquiv m hmpos r hr).symm)

private lemma putnam_2005_a2_expandRightAt_tour
    {m : ℕ} (hmpos : 0 < m) {r : ℤ} (hr : r = 1 ∨ r = 3)
    {q : ℕ → ℤ × ℤ} (hq : q ∈ putnam_2005_a2_tours m r) :
    let j := putnam_2005_a2_leftBlockStart m q hq.1
    putnam_2005_a2_expandRightAt m j q ∈ putnam_2005_a2_tours (m + 1) r ∧
      putnam_2005_a2_expandRightAt m j q 2 = ((2 : ℤ), (1 : ℤ)) := by
  classical
  rcases hq with ⟨hrookq, hq1, hqend⟩
  let j := putnam_2005_a2_leftBlockStart m q hrookq
  let p := putnam_2005_a2_expandRightAt m j q
  have hspec := putnam_2005_a2_leftBlockStart_spec (n := m) hmpos (r := r) hr
    hrookq hq1 hqend
  have hjbounds : 2 ≤ j ∧ j + 1 ≤ 3 * m := by
    simpa [j] using hspec.1
  have hblock :
      (q j = ((1 : ℤ), (2 : ℤ)) ∧ q (j + 1) = ((1 : ℤ), (3 : ℤ))) ∨
        (q j = ((1 : ℤ), (3 : ℤ)) ∧ q (j + 1) = ((1 : ℤ), (2 : ℤ))) := by
    simpa [j] using hspec.2
  have hqmem := putnam_2005_a2_value_mem_rect m q hrookq.1
  have hqinj := putnam_2005_a2_index_injective m q hrookq.1
  have hjmem : j ∈ Set.Icc 1 (3 * m) := by
    constructor <;> omega
  have hj1mem : j + 1 ∈ Set.Icc 1 (3 * m) := by
    constructor <;> omega
  have hp2 : p 2 = ((2 : ℤ), (1 : ℤ)) := by
    have hshift : p 2 = putnam_2005_a2_up (q 1) := by
      have harg : 2 - 1 = 1 := by omega
      calc
        p 2 = putnam_2005_a2_up (q (2 - 1)) :=
          putnam_2005_a2_expandRightAt_early q (m := m) (j := j) (i := 2)
            (by omega) (by omega)
        _ = putnam_2005_a2_up (q 1) := by rw [harg]
    rw [hshift, hq1]
    simp [putnam_2005_a2_up]
  have hp_mem :
      ∀ i ∈ Set.Icc 1 (3 * (m + 1)),
        p i ∈ Set.prod (Set.Icc (1 : ℤ) ((m + 1 : ℕ) : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)) := by
    intro i hi
    rcases hi with ⟨hilo, hihi⟩
    by_cases hi1 : i = 1
    · subst i
      simp [p]
      constructor
      · constructor
        · norm_num
        · change (1 : ℤ) ≤ ((m + 1 : ℕ) : ℤ)
          exact_mod_cast (show 1 ≤ m + 1 by omega)
      · norm_num
    by_cases hle : i ≤ j + 1
    · have hshift : p i = putnam_2005_a2_up (q (i - 1)) :=
        putnam_2005_a2_expandRightAt_early q (by omega) hle
      rw [hshift]
      exact putnam_2005_a2_up_mem_rect
        (hqmem (i - 1) (by constructor <;> omega))
    by_cases hfirst : i = j + 2
    · subst i
      simpa [p, putnam_2005_a2_expandRightAt_block_first] using
        putnam_2005_a2_mem_rect_succ (hqmem j hjmem)
    by_cases hsecond : i = j + 3
    · subst i
      simpa [p, putnam_2005_a2_expandRightAt_block_second] using
        putnam_2005_a2_mem_rect_succ (hqmem (j + 1) hj1mem)
    · have hlo : j + 4 ≤ i := by omega
      have hshift : p i = putnam_2005_a2_up (q (i - 3)) :=
        putnam_2005_a2_expandRightAt_late q hlo hihi
      rw [hshift]
      exact putnam_2005_a2_up_mem_rect
        (hqmem (i - 3) (by constructor <;> omega))
  have hp_inj :
      ∀ ⦃i k : ℕ⦄, i ∈ Set.Icc 1 (3 * (m + 1)) →
        k ∈ Set.Icc 1 (3 * (m + 1)) → p i = p k → i = k := by
    intro i k hi hk hik
    have shifted_col :
        ∀ {t : ℕ}, t ∈ Set.Icc 1 (3 * (m + 1)) →
          t ≠ 1 → t ≠ j + 2 → t ≠ j + 3 → (2 : ℤ) ≤ (p t).1 := by
      intro t ht ht1 htb1 htb2
      have hshift := putnam_2005_a2_expandRightAt_shift_of_not_block
        (m := m) (j := j) q ht ht1 htb1 htb2
      have hsrcmem := putnam_2005_a2_expandRightAt_source_mem
        (m := m) (j := j) hjbounds ht ht1
      have hrect := hqmem (if t ≤ j + 1 then t - 1 else t - 3) hsrcmem
      rcases hrect with ⟨hx, hy⟩
      change (2 : ℤ) ≤ (putnam_2005_a2_expandRightAt m j q t).1
      rw [hshift]
      simp [putnam_2005_a2_up] at hx ⊢
      omega
    have hleft_inj :
        ∀ {a b : ℕ}, (a = 1 ∨ a = j + 2 ∨ a = j + 3) →
          (b = 1 ∨ b = j + 2 ∨ b = j + 3) → p a = p b → a = b := by
      intro a b ha hb hv
      rcases hblock with hblock | hblock
      · rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
        · rfl
        · have hrow := congr_arg Prod.snd hv
          simp [p, putnam_2005_a2_expandRightAt_block_first, hblock] at hrow
        · have hrow := congr_arg Prod.snd hv
          simp [p, putnam_2005_a2_expandRightAt_block_second, hblock] at hrow
        · have hrow := congr_arg Prod.snd hv
          simp [p, putnam_2005_a2_expandRightAt_block_first, hblock] at hrow
        · rfl
        · have hrow := congr_arg Prod.snd hv
          simp [p, putnam_2005_a2_expandRightAt_block_first,
            putnam_2005_a2_expandRightAt_block_second, hblock] at hrow
        · have hrow := congr_arg Prod.snd hv
          simp [p, putnam_2005_a2_expandRightAt_block_second, hblock] at hrow
        · have hrow := congr_arg Prod.snd hv
          simp [p, putnam_2005_a2_expandRightAt_block_first,
            putnam_2005_a2_expandRightAt_block_second, hblock] at hrow
        · rfl
      · rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
        · rfl
        · have hrow := congr_arg Prod.snd hv
          simp [p, putnam_2005_a2_expandRightAt_block_first, hblock] at hrow
        · have hrow := congr_arg Prod.snd hv
          simp [p, putnam_2005_a2_expandRightAt_block_second, hblock] at hrow
        · have hrow := congr_arg Prod.snd hv
          simp [p, putnam_2005_a2_expandRightAt_block_first, hblock] at hrow
        · rfl
        · have hrow := congr_arg Prod.snd hv
          simp [p, putnam_2005_a2_expandRightAt_block_first,
            putnam_2005_a2_expandRightAt_block_second, hblock] at hrow
        · have hrow := congr_arg Prod.snd hv
          simp [p, putnam_2005_a2_expandRightAt_block_second, hblock] at hrow
        · have hrow := congr_arg Prod.snd hv
          simp [p, putnam_2005_a2_expandRightAt_block_first,
            putnam_2005_a2_expandRightAt_block_second, hblock] at hrow
        · rfl
    by_cases hi_left : i = 1 ∨ i = j + 2 ∨ i = j + 3
    · by_cases hk_left : k = 1 ∨ k = j + 2 ∨ k = j + 3
      · exact hleft_inj hi_left hk_left hik
      · have hk1 : k ≠ 1 := by intro h; exact hk_left (Or.inl h)
        have hkb1 : k ≠ j + 2 := by intro h; exact hk_left (Or.inr (Or.inl h))
        have hkb2 : k ≠ j + 3 := by intro h; exact hk_left (Or.inr (Or.inr h))
        have hkcol := shifted_col hk hk1 hkb1 hkb2
        rcases hi_left with rfl | rfl | rfl
        · have : (2 : ℤ) ≤ (p 1).1 := by simpa [hik.symm] using hkcol
          simp [p] at this
        · rcases hblock with hblock | hblock
          · have : (2 : ℤ) ≤ (p (j + 2)).1 := by simpa [hik.symm] using hkcol
            simp [p, putnam_2005_a2_expandRightAt_block_first, hblock] at this
          · have : (2 : ℤ) ≤ (p (j + 2)).1 := by simpa [hik.symm] using hkcol
            simp [p, putnam_2005_a2_expandRightAt_block_first, hblock] at this
        · rcases hblock with hblock | hblock
          · have : (2 : ℤ) ≤ (p (j + 3)).1 := by simpa [hik.symm] using hkcol
            simp [p, putnam_2005_a2_expandRightAt_block_second, hblock] at this
          · have : (2 : ℤ) ≤ (p (j + 3)).1 := by simpa [hik.symm] using hkcol
            simp [p, putnam_2005_a2_expandRightAt_block_second, hblock] at this
    · by_cases hk_left : k = 1 ∨ k = j + 2 ∨ k = j + 3
      · have hi1 : i ≠ 1 := by intro h; exact hi_left (Or.inl h)
        have hib1 : i ≠ j + 2 := by intro h; exact hi_left (Or.inr (Or.inl h))
        have hib2 : i ≠ j + 3 := by intro h; exact hi_left (Or.inr (Or.inr h))
        have hicol := shifted_col hi hi1 hib1 hib2
        rcases hk_left with rfl | rfl | rfl
        · have : (2 : ℤ) ≤ (p 1).1 := by simpa [← hik] using hicol
          simp [p] at this
        · rcases hblock with hblock | hblock
          · have : (2 : ℤ) ≤ (p (j + 2)).1 := by simpa [← hik] using hicol
            simp [p, putnam_2005_a2_expandRightAt_block_first, hblock] at this
          · have : (2 : ℤ) ≤ (p (j + 2)).1 := by simpa [← hik] using hicol
            simp [p, putnam_2005_a2_expandRightAt_block_first, hblock] at this
        · rcases hblock with hblock | hblock
          · have : (2 : ℤ) ≤ (p (j + 3)).1 := by simpa [← hik] using hicol
            simp [p, putnam_2005_a2_expandRightAt_block_second, hblock] at this
          · have : (2 : ℤ) ≤ (p (j + 3)).1 := by simpa [← hik] using hicol
            simp [p, putnam_2005_a2_expandRightAt_block_second, hblock] at this
      · have hi1 : i ≠ 1 := by intro h; exact hi_left (Or.inl h)
        have hib1 : i ≠ j + 2 := by intro h; exact hi_left (Or.inr (Or.inl h))
        have hib2 : i ≠ j + 3 := by intro h; exact hi_left (Or.inr (Or.inr h))
        have hk1 : k ≠ 1 := by intro h; exact hk_left (Or.inl h)
        have hkb1 : k ≠ j + 2 := by intro h; exact hk_left (Or.inr (Or.inl h))
        have hkb2 : k ≠ j + 3 := by intro h; exact hk_left (Or.inr (Or.inr h))
        have hshifti := putnam_2005_a2_expandRightAt_shift_of_not_block
          (m := m) (j := j) q hi hi1 hib1 hib2
        have hshiftk := putnam_2005_a2_expandRightAt_shift_of_not_block
          (m := m) (j := j) q hk hk1 hkb1 hkb2
        have hsrcimem := putnam_2005_a2_expandRightAt_source_mem
          (m := m) (j := j) hjbounds hi hi1
        have hsrckmem := putnam_2005_a2_expandRightAt_source_mem
          (m := m) (j := j) hjbounds hk hk1
        have hqeq :
            q (if i ≤ j + 1 then i - 1 else i - 3) =
              q (if k ≤ j + 1 then k - 1 else k - 3) := by
          have hdown := congr_arg putnam_2005_a2_down hik
          change putnam_2005_a2_down (putnam_2005_a2_expandRightAt m j q i) =
              putnam_2005_a2_down (putnam_2005_a2_expandRightAt m j q k) at hdown
          rw [hshifti, hshiftk] at hdown
          simpa [putnam_2005_a2_down_up] using hdown
        have hsrc :=
          hqinj hsrcimem hsrckmem hqeq
        exact putnam_2005_a2_expandRightAt_source_eq_imp
          (m := m) (j := j) hjbounds hi hk hi1 hib1 hib2 hk1 hkb1 hkb2 hsrc
  have hpuniq :
      ∀ P ∈ Set.prod (Set.Icc (1 : ℤ) ((m + 1 : ℕ) : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)),
        ∃! i, i ∈ Set.Icc 1 (3 * (m + 1)) ∧ p i = P := by
    exact putnam_2005_a2_unique_hits_of_mem_inj
      (A := (Set.Icc 1 (3 * (m + 1)) : Set ℕ))
      (B := Set.prod (Set.Icc (1 : ℤ) ((m + 1 : ℕ) : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)))
      (f := p)
      (Set.finite_Icc 1 (3 * (m + 1)))
      ((Set.finite_Icc (1 : ℤ) ((m + 1 : ℕ) : ℤ)).prod
        (Set.finite_Icc (1 : ℤ) (3 : ℤ)))
      (by rw [putnam_2005_a2_index_ncard, putnam_2005_a2_rect_ncard])
      hp_mem
      (by intro a b ha hb hab; exact hp_inj ha hb hab)
  have hpadj :
      ∀ i ∈ Set.Icc 1 (3 * (m + 1) - 1), putnam_2005_a2_unit (p i) (p (i + 1)) := by
    intro i hi
    rcases hi with ⟨hilo, hihi⟩
    by_cases hi1 : i = 1
    · subst i
      have hp2' : p 2 = ((2 : ℤ), (1 : ℤ)) := hp2
      simp [p, hp2', putnam_2005_a2_unit]
    by_cases hlej : i ≤ j
    · have hpi : p i = putnam_2005_a2_up (q (i - 1)) :=
        putnam_2005_a2_expandRightAt_early q (by omega) (by omega)
      have hpip1 : p (i + 1) = putnam_2005_a2_up (q ((i - 1) + 1)) := by
        have harg : i + 1 - 1 = (i - 1) + 1 := by omega
        calc
          p (i + 1) = putnam_2005_a2_up (q (i + 1 - 1)) :=
            putnam_2005_a2_expandRightAt_early q (by omega) (by omega)
          _ = putnam_2005_a2_up (q ((i - 1) + 1)) := by rw [harg]
      have hqadj := hrookq.2.1 (i - 1) (by constructor <;> omega)
      rw [hpi, hpip1]
      exact (putnam_2005_a2_unit_up_iff _ _).2 hqadj
    by_cases hij1 : i = j + 1
    · subst i
      have hleft : p (j + 1) = putnam_2005_a2_up (q j) := by
        have harg : j + 1 - 1 = j := by omega
        calc
          p (j + 1) = putnam_2005_a2_up (q (j + 1 - 1)) :=
            putnam_2005_a2_expandRightAt_early q (by omega) (by omega)
          _ = putnam_2005_a2_up (q j) := by rw [harg]
      have hright : p (j + 2) = q j := putnam_2005_a2_expandRightAt_block_first q
      rcases hblock with hblock | hblock
      · rw [hleft, hright, hblock.1]
        simp [putnam_2005_a2_unit, putnam_2005_a2_up]
      · rw [hleft, hright, hblock.1]
        simp [putnam_2005_a2_unit, putnam_2005_a2_up]
    by_cases hij2 : i = j + 2
    · subst i
      have hleft : p (j + 2) = q j := putnam_2005_a2_expandRightAt_block_first q
      have hright : p (j + 3) = q (j + 1) := putnam_2005_a2_expandRightAt_block_second q
      rcases hblock with hblock | hblock
      · rw [hleft, hright, hblock.1, hblock.2]
        simp [putnam_2005_a2_unit]
      · rw [hleft, hright, hblock.1, hblock.2]
        simp [putnam_2005_a2_unit, abs_sub_comm]
    by_cases hij3 : i = j + 3
    · subst i
      have hleft : p (j + 3) = q (j + 1) := putnam_2005_a2_expandRightAt_block_second q
      have hright : p (j + 4) = putnam_2005_a2_up (q (j + 1)) := by
        have harg : j + 4 - 3 = j + 1 := by omega
        calc
          p (j + 4) = putnam_2005_a2_up (q (j + 4 - 3)) :=
            putnam_2005_a2_expandRightAt_late q (by omega) (by omega)
          _ = putnam_2005_a2_up (q (j + 1)) := by rw [harg]
      rcases hblock with hblock | hblock
      · rw [hleft, hright, hblock.2]
        simp [putnam_2005_a2_unit, putnam_2005_a2_up]
      · rw [hleft, hright, hblock.2]
        simp [putnam_2005_a2_unit, putnam_2005_a2_up]
    · have hlo : j + 4 ≤ i := by omega
      have hpi : p i = putnam_2005_a2_up (q (i - 3)) :=
        putnam_2005_a2_expandRightAt_late q hlo (by omega)
      have hpip1 : p (i + 1) = putnam_2005_a2_up (q ((i - 3) + 1)) := by
        have harg : i + 1 - 3 = (i - 3) + 1 := by omega
        calc
          p (i + 1) = putnam_2005_a2_up (q (i + 1 - 3)) :=
            putnam_2005_a2_expandRightAt_late q (by omega) (by omega)
          _ = putnam_2005_a2_up (q ((i - 3) + 1)) := by rw [harg]
      have hqadj := hrookq.2.1 (i - 3) (by constructor <;> omega)
      rw [hpi, hpip1]
      exact (putnam_2005_a2_unit_up_iff _ _).2 hqadj
  have hp0 : p 0 = 0 := by simp [p]
  have hpafter : ∀ i > 3 * (m + 1), p i = 0 := by
    intro i hi
    exact putnam_2005_a2_expandRightAt_after q (by omega) hi
  have hp1 : p 1 = ((1 : ℤ), (1 : ℤ)) := by simp [p]
  have hpend : p (3 * (m + 1)) = (((m + 1 : ℕ) : ℤ), r) := by
    have hshift : p (3 * (m + 1)) = putnam_2005_a2_up (q (3 * m)) := by
      have harg : 3 * (m + 1) - 3 = 3 * m := by omega
      calc
        p (3 * (m + 1)) =
            putnam_2005_a2_up (q (3 * (m + 1) - 3)) :=
          putnam_2005_a2_expandRightAt_late q (by omega) (by omega)
        _ = putnam_2005_a2_up (q (3 * m)) := by rw [harg]
    rw [hshift, hqend]
    simp [putnam_2005_a2_up]
  refine ⟨?_, hp2⟩
  exact ⟨⟨hpuniq, hpadj, hp0, hpafter⟩, hp1, hpend⟩

private lemma putnam_2005_a2_stripRightAt_tour
    {m : ℕ} (hmpos : 0 < m) {r : ℤ} (hr : r = 1 ∨ r = 3)
    {p : ℕ → ℤ × ℤ}
    (hp : p ∈ putnam_2005_a2_toursFirstRight (m + 1) r) :
    let J := putnam_2005_a2_leftBlockStart (m + 1) p hp.1.1
    putnam_2005_a2_stripRightAt m J p ∈ putnam_2005_a2_tours m r := by
  classical
  rcases hp with ⟨hptour, hp2⟩
  rcases hptour with ⟨hrookp, hp1, hpend⟩
  let J := putnam_2005_a2_leftBlockStart (m + 1) p hrookp
  let q := putnam_2005_a2_stripRightAt m J p
  have hspec := putnam_2005_a2_leftBlockStart_spec (n := m + 1) (by omega)
    (r := r) hr hrookp hp1 hpend
  have hJbounds : 2 ≤ J ∧ J + 1 ≤ 3 * (m + 1) := by
    simpa [J] using hspec.1
  have hblock :
      (p J = ((1 : ℤ), (2 : ℤ)) ∧ p (J + 1) = ((1 : ℤ), (3 : ℤ))) ∨
        (p J = ((1 : ℤ), (3 : ℤ)) ∧ p (J + 1) = ((1 : ℤ), (2 : ℤ))) := by
    simpa [J] using hspec.2
  have hJge3 : 3 ≤ J := by
    have hJne2 : J ≠ 2 := by
      intro hJ2
      rcases hblock with hblock | hblock
      · have hbad : p 2 = ((1 : ℤ), (2 : ℤ)) := by simpa [hJ2] using hblock.1
        rw [hp2] at hbad
        norm_num at hbad
      · have hbad : p 2 = ((1 : ℤ), (3 : ℤ)) := by simpa [hJ2] using hblock.1
        rw [hp2] at hbad
        norm_num at hbad
    omega
  have hJ1lt : J + 1 < 3 * (m + 1) := by
    have hne : J + 1 ≠ 3 * (m + 1) := by
      intro hendidx
      rcases hblock with hblock | hblock
      · have heq : ((1 : ℤ), (3 : ℤ)) = (((m + 1 : ℕ) : ℤ), r) := by
          rw [← hblock.2, hendidx, hpend]
        have hfst : (1 : ℤ) = ((m + 1 : ℕ) : ℤ) := congr_arg Prod.fst heq
        have hm2 : (2 : ℤ) ≤ ((m + 1 : ℕ) : ℤ) := by
          exact_mod_cast (show 2 ≤ m + 1 by omega)
        omega
      · have heq : ((1 : ℤ), (2 : ℤ)) = (((m + 1 : ℕ) : ℤ), r) := by
          rw [← hblock.2, hendidx, hpend]
        have hfst : (1 : ℤ) = ((m + 1 : ℕ) : ℤ) := congr_arg Prod.fst heq
        have hm2 : (2 : ℤ) ≤ ((m + 1 : ℕ) : ℤ) := by
          exact_mod_cast (show 2 ≤ m + 1 by omega)
        omega
    omega
  have hpmem := putnam_2005_a2_value_mem_rect (m + 1) p hrookp.1
  have hpinj := putnam_2005_a2_index_injective (m + 1) p hrookp.1
  have hsource_not_left :
      ∀ {i : ℕ}, i ∈ Set.Icc 1 (3 * m) →
        (if i ≤ J - 2 then i + 1 else i + 3) ≠ 1 ∧
          (if i ≤ J - 2 then i + 1 else i + 3) ≠ J ∧
          (if i ≤ J - 2 then i + 1 else i + 3) ≠ J + 1 := by
    intro i hi
    rcases hi with ⟨hilo, hihi⟩
    by_cases hle : i ≤ J - 2
    · rw [if_pos hle]
      have hiJ : i + 2 ≤ J := Nat.add_le_of_le_sub hJbounds.1 hle
      constructor
      · omega
      · constructor <;> omega
    · rw [if_neg hle]
      have hgt : J - 2 < i := Nat.lt_of_not_ge hle
      constructor
      · omega
      · constructor <;> omega
  have hq_mem :
      ∀ i ∈ Set.Icc 1 (3 * m),
        q i ∈ Set.prod (Set.Icc (1 : ℤ) (m : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)) := by
    intro i hi
    have hqval := putnam_2005_a2_stripRightAt_value (m := m) (J := J) p hi
    have hsrcmem := putnam_2005_a2_stripRightAt_source_mem (m := m) (J := J)
      hJbounds hi
    have hnot := hsource_not_left hi
    have hcol : (2 : ℤ) ≤ (p (if i ≤ J - 2 then i + 1 else i + 3)).1 :=
      putnam_2005_a2_leftBlock_other_two_le hrookp hp1 hJbounds hblock hsrcmem
        hnot.1 hnot.2.1 hnot.2.2
    change putnam_2005_a2_stripRightAt m J p i ∈
      Set.prod (Set.Icc (1 : ℤ) (m : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ))
    rw [hqval]
    exact putnam_2005_a2_down_mem_rect (hpmem _ hsrcmem) hcol
  have hq_inj :
      ∀ ⦃i k : ℕ⦄, i ∈ Set.Icc 1 (3 * m) → k ∈ Set.Icc 1 (3 * m) →
        q i = q k → i = k := by
    intro i k hi hk hik
    have hqvali := putnam_2005_a2_stripRightAt_value (m := m) (J := J) p hi
    have hqvalk := putnam_2005_a2_stripRightAt_value (m := m) (J := J) p hk
    have hsrcimem := putnam_2005_a2_stripRightAt_source_mem (m := m) (J := J)
      hJbounds hi
    have hsrckmem := putnam_2005_a2_stripRightAt_source_mem (m := m) (J := J)
      hJbounds hk
    have hnoti := hsource_not_left hi
    have hnotk := hsource_not_left hk
    have hcoli : (2 : ℤ) ≤ (p (if i ≤ J - 2 then i + 1 else i + 3)).1 :=
      putnam_2005_a2_leftBlock_other_two_le hrookp hp1 hJbounds hblock hsrcimem
        hnoti.1 hnoti.2.1 hnoti.2.2
    have hcolk : (2 : ℤ) ≤ (p (if k ≤ J - 2 then k + 1 else k + 3)).1 :=
      putnam_2005_a2_leftBlock_other_two_le hrookp hp1 hJbounds hblock hsrckmem
        hnotk.1 hnotk.2.1 hnotk.2.2
    have hp_eq :
        p (if i ≤ J - 2 then i + 1 else i + 3) =
          p (if k ≤ J - 2 then k + 1 else k + 3) := by
      have hup := congr_arg putnam_2005_a2_up hik
      change putnam_2005_a2_up (putnam_2005_a2_stripRightAt m J p i) =
          putnam_2005_a2_up (putnam_2005_a2_stripRightAt m J p k) at hup
      rw [hqvali, hqvalk] at hup
      simpa [putnam_2005_a2_up_down_of_two_le hcoli,
        putnam_2005_a2_up_down_of_two_le hcolk] using hup
    have hsrc_eq := hpinj hsrcimem hsrckmem hp_eq
    exact putnam_2005_a2_stripRightAt_source_eq_imp hi hk hsrc_eq
  have hquniq :
      ∀ Q ∈ Set.prod (Set.Icc (1 : ℤ) (m : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)),
        ∃! i, i ∈ Set.Icc 1 (3 * m) ∧ q i = Q := by
    exact putnam_2005_a2_unique_hits_of_mem_inj
      (A := (Set.Icc 1 (3 * m) : Set ℕ))
      (B := Set.prod (Set.Icc (1 : ℤ) (m : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)))
      (f := q)
      (Set.finite_Icc 1 (3 * m))
      ((Set.finite_Icc (1 : ℤ) (m : ℤ)).prod (Set.finite_Icc (1 : ℤ) (3 : ℤ)))
      (by rw [putnam_2005_a2_index_ncard, putnam_2005_a2_rect_ncard])
      hq_mem
      (by intro a b ha hb hab; exact hq_inj ha hb hab)
  have hqadj :
      ∀ i ∈ Set.Icc 1 (3 * m - 1), putnam_2005_a2_unit (q i) (q (i + 1)) := by
    intro i hi
    rcases hi with ⟨hilo, hihi⟩
    by_cases hearly_next : i + 1 ≤ J - 2
    · have hqi : q i = putnam_2005_a2_down (p (i + 1)) := by
        exact putnam_2005_a2_stripRightAt_early p hilo (by omega)
      have hqip1 : q (i + 1) = putnam_2005_a2_down (p ((i + 1) + 1)) := by
        exact putnam_2005_a2_stripRightAt_early p (by omega) hearly_next
      have hpadj := hrookp.2.1 (i + 1) (by constructor <;> omega)
      rw [hqi, hqip1]
      exact (putnam_2005_a2_unit_down_iff _ _).2 hpadj
    by_cases hbridge : i = J - 2
    · subst i
      have hqi : q (J - 2) = putnam_2005_a2_down (p (J - 1)) := by
        have harg : J - 2 + 1 = J - 1 := by omega
        calc
          q (J - 2) = putnam_2005_a2_down (p (J - 2 + 1)) :=
            putnam_2005_a2_stripRightAt_early p (by omega) (by omega)
          _ = putnam_2005_a2_down (p (J - 1)) := by rw [harg]
      have hqnext : q (J - 2 + 1) = putnam_2005_a2_down (p (J + 2)) := by
        have harg : J - 2 + 1 + 3 = J + 2 := by omega
        calc
          q (J - 2 + 1) = putnam_2005_a2_down (p (J - 2 + 1 + 3)) :=
            putnam_2005_a2_stripRightAt_late p (by omega) (by omega) (by omega)
          _ = putnam_2005_a2_down (p (J + 2)) := by rw [harg]
      rw [hqi, hqnext]
      exact putnam_2005_a2_leftBlock_bridge hrookp hp1 hJbounds hJge3 hJ1lt hblock
    · have hlate : J - 2 < i := by
        have hgt_or : J - 2 < i ∨ i = J - 2 := by omega
        rcases hgt_or with hgt | heq
        · exact hgt
        · exact False.elim (hbridge heq)
      have hqi : q i = putnam_2005_a2_down (p (i + 3)) :=
        putnam_2005_a2_stripRightAt_late p hilo hlate (by omega)
      have hqip1 : q (i + 1) = putnam_2005_a2_down (p ((i + 3) + 1)) := by
        have harg : i + 1 + 3 = (i + 3) + 1 := by omega
        calc
          q (i + 1) = putnam_2005_a2_down (p (i + 1 + 3)) :=
            putnam_2005_a2_stripRightAt_late p (by omega) (by omega) (by omega)
          _ = putnam_2005_a2_down (p ((i + 3) + 1)) := by rw [harg]
      have hpadj := hrookp.2.1 (i + 3) (by constructor <;> omega)
      rw [hqi, hqip1]
      exact (putnam_2005_a2_unit_down_iff _ _).2 hpadj
  have hq0 : q 0 = 0 := by simp [q]
  have hqafter : ∀ i > 3 * m, q i = 0 := by
    intro i hi
    exact putnam_2005_a2_stripRightAt_after p hJbounds.2 hi
  have hq1 : q 1 = ((1 : ℤ), (1 : ℤ)) := by
    have hstrip : q 1 = putnam_2005_a2_down (p 2) :=
      putnam_2005_a2_stripRightAt_early p (by omega) (by omega)
    rw [hstrip, hp2]
    simp [putnam_2005_a2_down]
  have hqend : q (3 * m) = ((m : ℤ), r) := by
    have hlate : J - 2 < 3 * m := by omega
    have hstrip : q (3 * m) = putnam_2005_a2_down (p (3 * (m + 1))) := by
      have harg : 3 * m + 3 = 3 * (m + 1) := by omega
      calc
        q (3 * m) = putnam_2005_a2_down (p (3 * m + 3)) :=
          putnam_2005_a2_stripRightAt_late p (by omega) hlate (by omega)
        _ = putnam_2005_a2_down (p (3 * (m + 1))) := by rw [harg]
    rw [hstrip, hpend]
    simp [putnam_2005_a2_down]
  exact ⟨⟨hquniq, hqadj, hq0, hqafter⟩, hq1, hqend⟩

private lemma putnam_2005_a2_expandRightAt_leftBlockStart
    {m j : ℕ} {q : ℕ → ℤ × ℤ}
    (hjbounds : 2 ≤ j ∧ j + 1 ≤ 3 * m)
    (hblock :
      (q j = ((1 : ℤ), (2 : ℤ)) ∧ q (j + 1) = ((1 : ℤ), (3 : ℤ))) ∨
        (q j = ((1 : ℤ), (3 : ℤ)) ∧ q (j + 1) = ((1 : ℤ), (2 : ℤ))))
    (hrookp : putnam_2005_a2_rook (m + 1) (putnam_2005_a2_expandRightAt m j q)) :
    putnam_2005_a2_leftBlockStart (m + 1) (putnam_2005_a2_expandRightAt m j q)
      hrookp = j + 2 := by
  classical
  let p := putnam_2005_a2_expandRightAt m j q
  have h12mem : ((1 : ℤ), (2 : ℤ)) ∈
      Set.prod (Set.Icc (1 : ℤ) ((m + 1 : ℕ) : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)) :=
    putnam_2005_a2_mem_left_two (n := m + 1) (by omega)
  have h13mem : ((1 : ℤ), (3 : ℤ)) ∈
      Set.prod (Set.Icc (1 : ℤ) ((m + 1 : ℕ) : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)) :=
    putnam_2005_a2_mem_left_three (n := m + 1) (by omega)
  have hj2mem : j + 2 ∈ Set.Icc 1 (3 * (m + 1)) := by
    constructor <;> omega
  have hj3mem : j + 3 ∈ Set.Icc 1 (3 * (m + 1)) := by
    constructor <;> omega
  rcases hblock with hblock | hblock
  · have hidx12 : j + 2 =
        putnam_2005_a2_idx (m + 1) p hrookp.1 ((1 : ℤ), (2 : ℤ)) := by
      exact putnam_2005_a2_idx_eq_of_value (m + 1) p hrookp.1
        ((1 : ℤ), (2 : ℤ)) h12mem hj2mem (by
          simpa [p, putnam_2005_a2_expandRightAt_block_first, hblock.1])
    have hidx13 : j + 3 =
        putnam_2005_a2_idx (m + 1) p hrookp.1 ((1 : ℤ), (3 : ℤ)) := by
      exact putnam_2005_a2_idx_eq_of_value (m + 1) p hrookp.1
        ((1 : ℤ), (3 : ℤ)) h13mem hj3mem (by
          simpa [p, putnam_2005_a2_expandRightAt_block_second, hblock.2])
    change min
        (putnam_2005_a2_idx (m + 1) p hrookp.1 ((1 : ℤ), (2 : ℤ)))
        (putnam_2005_a2_idx (m + 1) p hrookp.1 ((1 : ℤ), (3 : ℤ))) = j + 2
    rw [← hidx12, ← hidx13]
    exact Nat.min_eq_left (by omega)
  · have hidx12 : j + 3 =
        putnam_2005_a2_idx (m + 1) p hrookp.1 ((1 : ℤ), (2 : ℤ)) := by
      exact putnam_2005_a2_idx_eq_of_value (m + 1) p hrookp.1
        ((1 : ℤ), (2 : ℤ)) h12mem hj3mem (by
          simpa [p, putnam_2005_a2_expandRightAt_block_second, hblock.2])
    have hidx13 : j + 2 =
        putnam_2005_a2_idx (m + 1) p hrookp.1 ((1 : ℤ), (3 : ℤ)) := by
      exact putnam_2005_a2_idx_eq_of_value (m + 1) p hrookp.1
        ((1 : ℤ), (3 : ℤ)) h13mem hj2mem (by
          simpa [p, putnam_2005_a2_expandRightAt_block_first, hblock.1])
    change min
        (putnam_2005_a2_idx (m + 1) p hrookp.1 ((1 : ℤ), (2 : ℤ)))
        (putnam_2005_a2_idx (m + 1) p hrookp.1 ((1 : ℤ), (3 : ℤ))) = j + 2
    rw [← hidx12, ← hidx13]
    exact Nat.min_eq_right (by omega)

private lemma putnam_2005_a2_strip_expandRightAt
    {m j : ℕ} {r : ℤ} {q : ℕ → ℤ × ℤ}
    (hq : q ∈ putnam_2005_a2_tours m r)
    (hjbounds : 2 ≤ j ∧ j + 1 ≤ 3 * m) :
    putnam_2005_a2_stripRightAt m (j + 2) (putnam_2005_a2_expandRightAt m j q) = q := by
  classical
  rcases hq with ⟨hrookq, hq1, hqend⟩
  funext i
  by_cases hi0 : i = 0
  · subst i
    simp [putnam_2005_a2_stripRightAt]
    exact hrookq.2.2.1.symm
  by_cases hi : i ≤ 3 * m
  · have hilo : 1 ≤ i := by omega
    by_cases hle : i ≤ j
    · have hstrip :
          putnam_2005_a2_stripRightAt m (j + 2)
              (putnam_2005_a2_expandRightAt m j q) i =
            putnam_2005_a2_down
              (putnam_2005_a2_expandRightAt m j q (i + 1)) := by
        have hJ : i ≤ j + 2 - 2 := by omega
        exact putnam_2005_a2_stripRightAt_early _ hilo hJ
      have hexpand :
          putnam_2005_a2_expandRightAt m j q (i + 1) =
            putnam_2005_a2_up (q i) := by
        have harg : i + 1 - 1 = i := by omega
        calc
          putnam_2005_a2_expandRightAt m j q (i + 1) =
              putnam_2005_a2_up (q (i + 1 - 1)) :=
            putnam_2005_a2_expandRightAt_early q (by omega) (by omega)
          _ = putnam_2005_a2_up (q i) := by rw [harg]
      rw [hstrip, hexpand, putnam_2005_a2_down_up]
    · have hstrip :
          putnam_2005_a2_stripRightAt m (j + 2)
              (putnam_2005_a2_expandRightAt m j q) i =
            putnam_2005_a2_down
              (putnam_2005_a2_expandRightAt m j q (i + 3)) := by
        have hJ : j + 2 - 2 < i := by
          have : j < i := Nat.lt_of_not_ge hle
          omega
        exact putnam_2005_a2_stripRightAt_late _ hilo hJ hi
      have hexpand :
          putnam_2005_a2_expandRightAt m j q (i + 3) =
            putnam_2005_a2_up (q i) := by
        have harg : i + 3 - 3 = i := by omega
        calc
          putnam_2005_a2_expandRightAt m j q (i + 3) =
              putnam_2005_a2_up (q (i + 3 - 3)) :=
            putnam_2005_a2_expandRightAt_late q (by omega) (by omega)
          _ = putnam_2005_a2_up (q i) := by rw [harg]
      rw [hstrip, hexpand, putnam_2005_a2_down_up]
  · have hgt : 3 * m < i := by omega
    rw [putnam_2005_a2_stripRightAt_after _ (by omega) hgt]
    exact (hrookq.2.2.2 i hgt).symm

private lemma putnam_2005_a2_stripRightAt_leftBlockStart
    {m J : ℕ} (hmpos : 0 < m) {p : ℕ → ℤ × ℤ}
    (hrookp : putnam_2005_a2_rook (m + 1) p)
    (hp1 : p 1 = ((1 : ℤ), (1 : ℤ)))
    (hJbounds : 2 ≤ J ∧ J + 1 ≤ 3 * (m + 1))
    (hJge3 : 3 ≤ J)
    (hJ1lt : J + 1 < 3 * (m + 1))
    (hblock :
      (p J = ((1 : ℤ), (2 : ℤ)) ∧ p (J + 1) = ((1 : ℤ), (3 : ℤ))) ∨
        (p J = ((1 : ℤ), (3 : ℤ)) ∧ p (J + 1) = ((1 : ℤ), (2 : ℤ))))
    (hrookq : putnam_2005_a2_rook m (putnam_2005_a2_stripRightAt m J p)) :
    putnam_2005_a2_leftBlockStart m (putnam_2005_a2_stripRightAt m J p)
      hrookq = J - 2 := by
  classical
  let q := putnam_2005_a2_stripRightAt m J p
  have h12mem : ((1 : ℤ), (2 : ℤ)) ∈
      Set.prod (Set.Icc (1 : ℤ) (m : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)) :=
    putnam_2005_a2_mem_left_two (n := m) hmpos
  have h13mem : ((1 : ℤ), (3 : ℤ)) ∈
      Set.prod (Set.Icc (1 : ℤ) (m : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)) :=
    putnam_2005_a2_mem_left_three (n := m) hmpos
  have hJm2mem : J - 2 ∈ Set.Icc 1 (3 * m) := by
    constructor
    · omega
    · have hne : J + 1 ≠ 3 * (m + 1) := by omega
      omega
  have hJm1mem : J - 1 ∈ Set.Icc 1 (3 * m) := by
    constructor
    · omega
    · omega
  have hpmem := putnam_2005_a2_value_mem_rect (m + 1) p hrookp.1
  have hprev_mem_idx : J - 1 ∈ Set.Icc 1 (3 * (m + 1)) := by
    constructor <;> omega
  have hnext_mem_idx : J + 2 ∈ Set.Icc 1 (3 * (m + 1)) := by
    constructor <;> omega
  have hprev_rect := hpmem (J - 1) hprev_mem_idx
  have hnext_rect := hpmem (J + 2) hnext_mem_idx
  have hprev_col : (2 : ℤ) ≤ (p (J - 1)).1 := by
    exact putnam_2005_a2_leftBlock_other_two_le hrookp hp1 hJbounds hblock
      hprev_mem_idx (by omega) (by omega) (by omega)
  have hnext_col : (2 : ℤ) ≤ (p (J + 2)).1 := by
    exact putnam_2005_a2_leftBlock_other_two_le hrookp hp1 hJbounds hblock
      hnext_mem_idx (by omega) (by omega) (by omega)
  have hprev_adj := hrookp.2.1 (J - 1) (by constructor <;> omega)
  have hnext_adj := hrookp.2.1 (J + 1) (by constructor <;> omega)
  have hprev_arg : J - 1 + 1 = J := by omega
  rcases hblock with hblock | hblock
  · have hprev_unit : putnam_2005_a2_unit (p (J - 1)) ((1 : ℤ), (2 : ℤ)) := by
      simpa [hprev_arg, hblock.1] using hprev_adj
    have hnext_unit : putnam_2005_a2_unit ((1 : ℤ), (3 : ℤ)) (p (J + 2)) := by
      simpa [hblock.2] using hnext_adj
    have hprev_eq := putnam_2005_a2_neighbor_to_left_two_right hprev_rect hprev_col hprev_unit
    have hnext_eq := putnam_2005_a2_neighbor_from_left_three_right hnext_rect hnext_col hnext_unit
    have hqJm2 : q (J - 2) = ((1 : ℤ), (2 : ℤ)) := by
      have hstrip : q (J - 2) = putnam_2005_a2_down (p (J - 1)) := by
        have harg : J - 2 + 1 = J - 1 := by omega
        calc
          q (J - 2) = putnam_2005_a2_down (p (J - 2 + 1)) :=
            putnam_2005_a2_stripRightAt_early p (by omega) (by omega)
          _ = putnam_2005_a2_down (p (J - 1)) := by rw [harg]
      rw [hstrip, hprev_eq]
      simp [putnam_2005_a2_down]
    have hqJm1 : q (J - 1) = ((1 : ℤ), (3 : ℤ)) := by
      have hstrip : q (J - 1) = putnam_2005_a2_down (p (J + 2)) := by
        have harg : J - 1 + 3 = J + 2 := by omega
        calc
          q (J - 1) = putnam_2005_a2_down (p (J - 1 + 3)) :=
            putnam_2005_a2_stripRightAt_late p (by omega) (by omega) (by omega)
          _ = putnam_2005_a2_down (p (J + 2)) := by rw [harg]
      rw [hstrip, hnext_eq]
      simp [putnam_2005_a2_down]
    have hidx12 : J - 2 = putnam_2005_a2_idx m q hrookq.1 ((1 : ℤ), (2 : ℤ)) :=
      putnam_2005_a2_idx_eq_of_value m q hrookq.1 ((1 : ℤ), (2 : ℤ))
        h12mem hJm2mem hqJm2
    have hidx13 : J - 1 = putnam_2005_a2_idx m q hrookq.1 ((1 : ℤ), (3 : ℤ)) :=
      putnam_2005_a2_idx_eq_of_value m q hrookq.1 ((1 : ℤ), (3 : ℤ))
        h13mem hJm1mem hqJm1
    change min
        (putnam_2005_a2_idx m q hrookq.1 ((1 : ℤ), (2 : ℤ)))
        (putnam_2005_a2_idx m q hrookq.1 ((1 : ℤ), (3 : ℤ))) = J - 2
    rw [← hidx12, ← hidx13]
    exact Nat.min_eq_left (by omega)
  · have hprev_unit : putnam_2005_a2_unit (p (J - 1)) ((1 : ℤ), (3 : ℤ)) := by
      simpa [hprev_arg, hblock.1] using hprev_adj
    have hnext_unit : putnam_2005_a2_unit ((1 : ℤ), (2 : ℤ)) (p (J + 2)) := by
      simpa [hblock.2] using hnext_adj
    have hprev_eq := putnam_2005_a2_neighbor_to_left_three_right hprev_rect hprev_col hprev_unit
    have hnext_eq := putnam_2005_a2_neighbor_from_left_two_right hnext_rect hnext_col hnext_unit
    have hqJm2 : q (J - 2) = ((1 : ℤ), (3 : ℤ)) := by
      have hstrip : q (J - 2) = putnam_2005_a2_down (p (J - 1)) := by
        have harg : J - 2 + 1 = J - 1 := by omega
        calc
          q (J - 2) = putnam_2005_a2_down (p (J - 2 + 1)) :=
            putnam_2005_a2_stripRightAt_early p (by omega) (by omega)
          _ = putnam_2005_a2_down (p (J - 1)) := by rw [harg]
      rw [hstrip, hprev_eq]
      simp [putnam_2005_a2_down]
    have hqJm1 : q (J - 1) = ((1 : ℤ), (2 : ℤ)) := by
      have hstrip : q (J - 1) = putnam_2005_a2_down (p (J + 2)) := by
        have harg : J - 1 + 3 = J + 2 := by omega
        calc
          q (J - 1) = putnam_2005_a2_down (p (J - 1 + 3)) :=
            putnam_2005_a2_stripRightAt_late p (by omega) (by omega) (by omega)
          _ = putnam_2005_a2_down (p (J + 2)) := by rw [harg]
      rw [hstrip, hnext_eq]
      simp [putnam_2005_a2_down]
    have hidx12 : J - 1 = putnam_2005_a2_idx m q hrookq.1 ((1 : ℤ), (2 : ℤ)) :=
      putnam_2005_a2_idx_eq_of_value m q hrookq.1 ((1 : ℤ), (2 : ℤ))
        h12mem hJm1mem hqJm1
    have hidx13 : J - 2 = putnam_2005_a2_idx m q hrookq.1 ((1 : ℤ), (3 : ℤ)) :=
      putnam_2005_a2_idx_eq_of_value m q hrookq.1 ((1 : ℤ), (3 : ℤ))
        h13mem hJm2mem hqJm2
    change min
        (putnam_2005_a2_idx m q hrookq.1 ((1 : ℤ), (2 : ℤ)))
        (putnam_2005_a2_idx m q hrookq.1 ((1 : ℤ), (3 : ℤ))) = J - 2
    rw [← hidx12, ← hidx13]
    exact Nat.min_eq_right (by omega)

private lemma putnam_2005_a2_expand_stripRightAt
    {m J : ℕ} {p : ℕ → ℤ × ℤ}
    (hrookp : putnam_2005_a2_rook (m + 1) p)
    (hp1 : p 1 = ((1 : ℤ), (1 : ℤ)))
    (hJbounds : 2 ≤ J ∧ J + 1 ≤ 3 * (m + 1))
    (hJge3 : 3 ≤ J)
    (hJ1lt : J + 1 < 3 * (m + 1))
    (hblock :
      (p J = ((1 : ℤ), (2 : ℤ)) ∧ p (J + 1) = ((1 : ℤ), (3 : ℤ))) ∨
        (p J = ((1 : ℤ), (3 : ℤ)) ∧ p (J + 1) = ((1 : ℤ), (2 : ℤ)))) :
    putnam_2005_a2_expandRightAt m (J - 2) (putnam_2005_a2_stripRightAt m J p) = p := by
  classical
  let q := putnam_2005_a2_stripRightAt m J p
  have hpmem := putnam_2005_a2_value_mem_rect (m + 1) p hrookp.1
  have hcol_other :
      ∀ {t : ℕ}, t ∈ Set.Icc 1 (3 * (m + 1)) →
        t ≠ 1 → t ≠ J → t ≠ J + 1 → (2 : ℤ) ≤ (p t).1 := by
    intro t ht ht1 htJ htJ1
    exact putnam_2005_a2_leftBlock_other_two_le hrookp hp1 hJbounds hblock ht ht1 htJ htJ1
  have hprev_mem_idx : J - 1 ∈ Set.Icc 1 (3 * (m + 1)) := by
    constructor <;> omega
  have hnext_mem_idx : J + 2 ∈ Set.Icc 1 (3 * (m + 1)) := by
    constructor <;> omega
  have hprev_rect := hpmem (J - 1) hprev_mem_idx
  have hnext_rect := hpmem (J + 2) hnext_mem_idx
  have hprev_col : (2 : ℤ) ≤ (p (J - 1)).1 :=
    hcol_other hprev_mem_idx (by omega) (by omega) (by omega)
  have hnext_col : (2 : ℤ) ≤ (p (J + 2)).1 :=
    hcol_other hnext_mem_idx (by omega) (by omega) (by omega)
  have hprev_adj := hrookp.2.1 (J - 1) (by constructor <;> omega)
  have hnext_adj := hrookp.2.1 (J + 1) (by constructor <;> omega)
  have hprev_arg : J - 1 + 1 = J := by omega
  have hq_block :
      (q (J - 2) = p J ∧ q (J - 1) = p (J + 1)) := by
    rcases hblock with hblock | hblock
    · have hprev_unit : putnam_2005_a2_unit (p (J - 1)) ((1 : ℤ), (2 : ℤ)) := by
        simpa [hprev_arg, hblock.1] using hprev_adj
      have hnext_unit : putnam_2005_a2_unit ((1 : ℤ), (3 : ℤ)) (p (J + 2)) := by
        simpa [hblock.2] using hnext_adj
      have hprev_eq := putnam_2005_a2_neighbor_to_left_two_right hprev_rect hprev_col hprev_unit
      have hnext_eq := putnam_2005_a2_neighbor_from_left_three_right hnext_rect hnext_col hnext_unit
      constructor
      · have hstrip : q (J - 2) = putnam_2005_a2_down (p (J - 1)) := by
          have harg : J - 2 + 1 = J - 1 := by omega
          calc
            q (J - 2) = putnam_2005_a2_down (p (J - 2 + 1)) :=
              putnam_2005_a2_stripRightAt_early p (by omega) (by omega)
            _ = putnam_2005_a2_down (p (J - 1)) := by rw [harg]
        rw [hstrip, hprev_eq, hblock.1]
        simp [putnam_2005_a2_down]
      · have hstrip : q (J - 1) = putnam_2005_a2_down (p (J + 2)) := by
          have harg : J - 1 + 3 = J + 2 := by omega
          calc
            q (J - 1) = putnam_2005_a2_down (p (J - 1 + 3)) :=
              putnam_2005_a2_stripRightAt_late p (by omega) (by omega) (by omega)
            _ = putnam_2005_a2_down (p (J + 2)) := by rw [harg]
        rw [hstrip, hnext_eq, hblock.2]
        simp [putnam_2005_a2_down]
    · have hprev_unit : putnam_2005_a2_unit (p (J - 1)) ((1 : ℤ), (3 : ℤ)) := by
        simpa [hprev_arg, hblock.1] using hprev_adj
      have hnext_unit : putnam_2005_a2_unit ((1 : ℤ), (2 : ℤ)) (p (J + 2)) := by
        simpa [hblock.2] using hnext_adj
      have hprev_eq := putnam_2005_a2_neighbor_to_left_three_right hprev_rect hprev_col hprev_unit
      have hnext_eq := putnam_2005_a2_neighbor_from_left_two_right hnext_rect hnext_col hnext_unit
      constructor
      · have hstrip : q (J - 2) = putnam_2005_a2_down (p (J - 1)) := by
          have harg : J - 2 + 1 = J - 1 := by omega
          calc
            q (J - 2) = putnam_2005_a2_down (p (J - 2 + 1)) :=
              putnam_2005_a2_stripRightAt_early p (by omega) (by omega)
            _ = putnam_2005_a2_down (p (J - 1)) := by rw [harg]
        rw [hstrip, hprev_eq, hblock.1]
        simp [putnam_2005_a2_down]
      · have hstrip : q (J - 1) = putnam_2005_a2_down (p (J + 2)) := by
          have harg : J - 1 + 3 = J + 2 := by omega
          calc
            q (J - 1) = putnam_2005_a2_down (p (J - 1 + 3)) :=
              putnam_2005_a2_stripRightAt_late p (by omega) (by omega) (by omega)
            _ = putnam_2005_a2_down (p (J + 2)) := by rw [harg]
        rw [hstrip, hnext_eq, hblock.2]
        simp [putnam_2005_a2_down]
  funext i
  by_cases hi0 : i = 0
  · subst i
    simp [putnam_2005_a2_expandRightAt]
    exact hrookp.2.2.1.symm
  by_cases hi1 : i = 1
  · subst i
    simp [putnam_2005_a2_expandRightAt, hp1]
  by_cases hiend : i ≤ 3 * (m + 1)
  · by_cases hle : i ≤ (J - 2) + 1
    · have hi2 : 2 ≤ i := by omega
      have hshift :
          putnam_2005_a2_expandRightAt m (J - 2) q i =
            putnam_2005_a2_up (q (i - 1)) :=
        putnam_2005_a2_expandRightAt_early q hi2 hle
      have hstrip : q (i - 1) = putnam_2005_a2_down (p i) := by
        have harg : i - 1 + 1 = i := by omega
        calc
          q (i - 1) = putnam_2005_a2_down (p (i - 1 + 1)) :=
            putnam_2005_a2_stripRightAt_early p (by omega) (by
              have hiJ : i ≤ J - 1 := by omega
              have : i - 1 + 2 ≤ J := by omega
              exact (Nat.le_sub_iff_add_le hJbounds.1).2 this)
          _ = putnam_2005_a2_down (p i) := by rw [harg]
      have himem : i ∈ Set.Icc 1 (3 * (m + 1)) := by constructor <;> omega
      have hcol : (2 : ℤ) ≤ (p i).1 :=
        hcol_other himem (by omega) (by omega) (by omega)
      rw [hshift, hstrip, putnam_2005_a2_up_down_of_two_le hcol]
    · by_cases hfirst : i = (J - 2) + 2
      · subst i
        rw [putnam_2005_a2_expandRightAt_block_first]
        change q (J - 2) = p (J - 2 + 2)
        rw [hq_block.1]
        have hright : J - 2 + 2 = J := by omega
        rw [hright]
      by_cases hsecond : i = (J - 2) + 3
      · subst i
        rw [putnam_2005_a2_expandRightAt_block_second]
        change q (J - 2 + 1) = p (J - 2 + 3)
        have hleft : J - 2 + 1 = J - 1 := by omega
        rw [hleft, hq_block.2]
        have hright : J - 2 + 3 = J + 1 := by omega
        rw [hright]
      · have hlo : (J - 2) + 4 ≤ i := by omega
        have hshift :
            putnam_2005_a2_expandRightAt m (J - 2) q i =
              putnam_2005_a2_up (q (i - 3)) :=
          putnam_2005_a2_expandRightAt_late q hlo hiend
        have hstrip : q (i - 3) = putnam_2005_a2_down (p i) := by
          have harg : i - 3 + 3 = i := by omega
          calc
            q (i - 3) = putnam_2005_a2_down (p (i - 3 + 3)) :=
              putnam_2005_a2_stripRightAt_late p (by omega) (by omega) (by
                have h := Nat.sub_le_sub_right hiend 3
                have hcalc : 3 * (m + 1) - 3 = 3 * m := by omega
                simpa [hcalc] using h)
            _ = putnam_2005_a2_down (p i) := by rw [harg]
        have himem : i ∈ Set.Icc 1 (3 * (m + 1)) := by constructor <;> omega
        have hcol : (2 : ℤ) ≤ (p i).1 :=
          hcol_other himem (by omega) (by omega) (by omega)
        rw [hshift, hstrip, putnam_2005_a2_up_down_of_two_le hcol]
  · have hgt : 3 * (m + 1) < i := by omega
    rw [putnam_2005_a2_expandRightAt_after q (by omega) hgt]
    exact (hrookp.2.2.2 i hgt).symm

private noncomputable def putnam_2005_a2_firstRightEquiv
    (m : ℕ) (hmpos : 0 < m) (r : ℤ) (hr : r = 1 ∨ r = 3) :
    (putnam_2005_a2_tours m r) ≃
      (putnam_2005_a2_toursFirstRight (m + 1) r) where
  toFun q :=
    let j := putnam_2005_a2_leftBlockStart m q.1 q.2.1
    ⟨putnam_2005_a2_expandRightAt m j q.1,
      by
        have h := putnam_2005_a2_expandRightAt_tour (m := m) hmpos (r := r) hr q.2
        exact ⟨h.1, h.2⟩⟩
  invFun p :=
    let J := putnam_2005_a2_leftBlockStart (m + 1) p.1 p.2.1.1
    ⟨putnam_2005_a2_stripRightAt m J p.1,
      putnam_2005_a2_stripRightAt_tour (m := m) hmpos (r := r) hr p.2⟩
  left_inv q := by
    apply Subtype.ext
    dsimp
    let j := putnam_2005_a2_leftBlockStart m q.1 q.2.1
    have hspec := putnam_2005_a2_leftBlockStart_spec (n := m) hmpos (r := r) hr
      q.2.1 q.2.2.1 q.2.2.2
    have hjbounds : 2 ≤ j ∧ j + 1 ≤ 3 * m := by
      simpa [j] using hspec.1
    have hblock :
        (q.1 j = ((1 : ℤ), (2 : ℤ)) ∧ q.1 (j + 1) = ((1 : ℤ), (3 : ℤ))) ∨
          (q.1 j = ((1 : ℤ), (3 : ℤ)) ∧ q.1 (j + 1) = ((1 : ℤ), (2 : ℤ))) := by
      simpa [j] using hspec.2
    have hstart :
        putnam_2005_a2_leftBlockStart (m + 1)
          (putnam_2005_a2_expandRightAt m j q.1)
          (putnam_2005_a2_expandRightAt_tour (m := m) hmpos (r := r) hr q.2).1.1 =
            j + 2 :=
      putnam_2005_a2_expandRightAt_leftBlockStart (m := m) (j := j) (q := q.1)
        hjbounds hblock
        (putnam_2005_a2_expandRightAt_tour (m := m) hmpos (r := r) hr q.2).1.1
    rw [hstart]
    exact putnam_2005_a2_strip_expandRightAt (m := m) (j := j) (r := r) q.2 hjbounds
  right_inv p := by
    apply Subtype.ext
    dsimp
    let J := putnam_2005_a2_leftBlockStart (m + 1) p.1 p.2.1.1
    rcases p.2 with ⟨hptour, hp2⟩
    rcases hptour with ⟨hrookp, hp1, hpend⟩
    have hspec := putnam_2005_a2_leftBlockStart_spec (n := m + 1) (by omega)
      (r := r) hr hrookp hp1 hpend
    have hJbounds : 2 ≤ J ∧ J + 1 ≤ 3 * (m + 1) := by
      simpa [J] using hspec.1
    have hblock :
        (p.1 J = ((1 : ℤ), (2 : ℤ)) ∧ p.1 (J + 1) = ((1 : ℤ), (3 : ℤ))) ∨
          (p.1 J = ((1 : ℤ), (3 : ℤ)) ∧ p.1 (J + 1) = ((1 : ℤ), (2 : ℤ))) := by
      simpa [J] using hspec.2
    have hJge3 : 3 ≤ J := by
      have hJne2 : J ≠ 2 := by
        intro hJ2
        rcases hblock with hblock | hblock
        · have hbad : p.1 2 = ((1 : ℤ), (2 : ℤ)) := by simpa [hJ2] using hblock.1
          rw [hp2] at hbad
          norm_num at hbad
        · have hbad : p.1 2 = ((1 : ℤ), (3 : ℤ)) := by simpa [hJ2] using hblock.1
          rw [hp2] at hbad
          norm_num at hbad
      omega
    have hJ1lt : J + 1 < 3 * (m + 1) := by
      have hne : J + 1 ≠ 3 * (m + 1) := by
        intro hendidx
        rcases hblock with hblock | hblock
        · have heq : ((1 : ℤ), (3 : ℤ)) = (((m + 1 : ℕ) : ℤ), r) := by
            rw [← hblock.2, hendidx, hpend]
          have hfst : (1 : ℤ) = ((m + 1 : ℕ) : ℤ) := congr_arg Prod.fst heq
          have hm2 : (2 : ℤ) ≤ ((m + 1 : ℕ) : ℤ) := by
            exact_mod_cast (show 2 ≤ m + 1 by omega)
          omega
        · have heq : ((1 : ℤ), (2 : ℤ)) = (((m + 1 : ℕ) : ℤ), r) := by
            rw [← hblock.2, hendidx, hpend]
          have hfst : (1 : ℤ) = ((m + 1 : ℕ) : ℤ) := congr_arg Prod.fst heq
          have hm2 : (2 : ℤ) ≤ ((m + 1 : ℕ) : ℤ) := by
            exact_mod_cast (show 2 ≤ m + 1 by omega)
          omega
      omega
    have hstripTour := putnam_2005_a2_stripRightAt_tour (m := m) hmpos (r := r) hr p.2
    have hstart :
        putnam_2005_a2_leftBlockStart m
          (putnam_2005_a2_stripRightAt m J p.1)
          hstripTour.1 =
            J - 2 :=
      putnam_2005_a2_stripRightAt_leftBlockStart (m := m) (J := J) hmpos
        hrookp hp1 hJbounds hJge3 hJ1lt hblock hstripTour.1
    rw [hstart]
    exact putnam_2005_a2_expand_stripRightAt (m := m) (J := J)
      hrookp hp1 hJbounds hJge3 hJ1lt hblock

private lemma putnam_2005_a2_firstRight_encard
    (m : ℕ) (hmpos : 0 < m) (r : ℤ) (hr : r = 1 ∨ r = 3) :
    (putnam_2005_a2_toursFirstRight (m + 1) r).encard =
      (putnam_2005_a2_tours m r).encard := by
  exact (Set.encard_congr (putnam_2005_a2_firstRightEquiv m hmpos r hr).symm)

private lemma putnam_2005_a2_tours_succ_encard
    (m : ℕ) (hmpos : 0 < m) (r : ℤ) (hr : r = 1 ∨ r = 3) :
    (putnam_2005_a2_tours (m + 1) r).encard =
      (putnam_2005_a2_tours m (4 - r)).encard + (putnam_2005_a2_tours m r).encard := by
  classical
  have hunion :
      putnam_2005_a2_tours (m + 1) r =
        putnam_2005_a2_toursFirstUp (m + 1) r ∪
          putnam_2005_a2_toursFirstRight (m + 1) r := by
    ext p
    constructor
    · intro hp
      have hfirst := putnam_2005_a2_first_move (n := m + 1) (by omega)
        hp.1 hp.2.1
      rcases hfirst with hfirst | hfirst
      · exact Or.inl ⟨hp, hfirst⟩
      · exact Or.inr ⟨hp, hfirst⟩
    · intro hp
      rcases hp with hp | hp
      · exact hp.1
      · exact hp.1
  have hdisj :
      Disjoint (putnam_2005_a2_toursFirstUp (m + 1) r)
        (putnam_2005_a2_toursFirstRight (m + 1) r) := by
    rw [Set.disjoint_left]
    intro p hpup hpright
    have hbad : ((1 : ℤ), (2 : ℤ)) = ((2 : ℤ), (1 : ℤ)) := by
      rw [← hpup.2, hpright.2]
    norm_num at hbad
  rw [hunion, Set.encard_union_eq hdisj,
    putnam_2005_a2_firstUp_encard m hmpos r hr,
    putnam_2005_a2_firstRight_encard m hmpos r hr]

private def putnam_2005_a2_one_three_path : ℕ → ℤ × ℤ :=
  fun i =>
    if i = 0 then 0
    else if i = 1 then ((1 : ℤ), (1 : ℤ))
    else if i = 2 then ((1 : ℤ), (2 : ℤ))
    else if i = 3 then ((1 : ℤ), (3 : ℤ))
    else 0

private lemma putnam_2005_a2_tours_one_one_encard :
    (putnam_2005_a2_tours 1 1).encard = 0 := by
  classical
  rw [Set.encard_eq_zero]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  rcases hp with ⟨hrook, hp1, hp3⟩
  have hmem : ((1 : ℤ), (1 : ℤ)) ∈
      Set.prod (Set.Icc (1 : ℤ) (1 : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)) := by
    constructor <;> norm_num
  have huniq := hrook.1 ((1 : ℤ), (1 : ℤ)) hmem
  have h1 : (1 : ℕ) ∈ Set.Icc 1 (3 * (1 : ℕ)) ∧
      p 1 = ((1 : ℤ), (1 : ℤ)) := by
    constructor
    · norm_num
    · exact hp1
  have h3 : (3 : ℕ) ∈ Set.Icc 1 (3 * (1 : ℕ)) ∧
      p 3 = ((1 : ℤ), (1 : ℤ)) := by
    constructor
    · norm_num
    · exact hp3
  have h13 : (1 : ℕ) = 3 := ExistsUnique.unique huniq h1 h3
  norm_num at h13

private lemma putnam_2005_a2_tours_one_three_encard :
    (putnam_2005_a2_tours 1 3).encard = 1 := by
  classical
  let v := putnam_2005_a2_one_three_path
  have hv0 : v 0 = 0 := by simp [v, putnam_2005_a2_one_three_path]
  have hv1 : v 1 = ((1 : ℤ), (1 : ℤ)) := by simp [v, putnam_2005_a2_one_three_path]
  have hv2 : v 2 = ((1 : ℤ), (2 : ℤ)) := by simp [v, putnam_2005_a2_one_three_path]
  have hv3 : v 3 = ((1 : ℤ), (3 : ℤ)) := by simp [v, putnam_2005_a2_one_three_path]
  have hvafter : ∀ i > 3, v i = 0 := by
    intro i hi
    have h0 : i ≠ 0 := by omega
    have h1 : i ≠ 1 := by omega
    have h2 : i ≠ 2 := by omega
    have h3 : i ≠ 3 := by omega
    simp [v, putnam_2005_a2_one_three_path, h0, h1, h2, h3]
  have hvrook : putnam_2005_a2_rook 1 v := by
    refine ⟨?_, ?_, hv0, ?_⟩
    · intro P hP
      rcases P with ⟨a, b⟩
      rcases hP with ⟨ha, hb⟩
      simp at ha hb
      have ha1 : a = (1 : ℤ) := by omega
      subst a
      have hb_cases : b = (1 : ℤ) ∨ b = (2 : ℤ) ∨ b = (3 : ℤ) := by omega
      rcases hb_cases with rfl | rfl | rfl
      · refine ⟨1, ?_, ?_⟩
        · constructor
          · norm_num
          · exact hv1
        · intro j hj
          rcases hj with ⟨hjmem, hjval⟩
          rcases hjmem with ⟨hjlo, hjhi⟩
          interval_cases j <;> simp [v, putnam_2005_a2_one_three_path] at hjval ⊢
      · refine ⟨2, ?_, ?_⟩
        · constructor
          · norm_num
          · exact hv2
        · intro j hj
          rcases hj with ⟨hjmem, hjval⟩
          rcases hjmem with ⟨hjlo, hjhi⟩
          interval_cases j <;> simp [v, putnam_2005_a2_one_three_path] at hjval ⊢
      · refine ⟨3, ?_, ?_⟩
        · constructor
          · norm_num
          · exact hv3
        · intro j hj
          rcases hj with ⟨hjmem, hjval⟩
          rcases hjmem with ⟨hjlo, hjhi⟩
          interval_cases j <;> simp [v, putnam_2005_a2_one_three_path] at hjval ⊢
    · intro i hi
      rcases hi with ⟨hilo, hihi⟩
      interval_cases i <;> simp [v, putnam_2005_a2_one_three_path, putnam_2005_a2_unit]
    · intro i hi
      exact hvafter i (by simpa using hi)
  have hset : putnam_2005_a2_tours 1 3 = {v} := by
    ext p
    constructor
    · intro hp
      rcases hp with ⟨hrook, hp1, hp3⟩
      have hp2 : p 2 = ((1 : ℤ), (2 : ℤ)) := by
        have hp2mem := putnam_2005_a2_value_mem_rect 1 p hrook.1 2 (by norm_num)
        have hadj := hrook.2.1 1 (by norm_num)
        have hadj' : putnam_2005_a2_unit ((1 : ℤ), (1 : ℤ)) (p 2) := by
          simpa [hp1] using hadj
        rcases hp2mem with ⟨ha, hb⟩
        simp at ha hb
        rcases hadj' with h | h
        · apply Prod.ext
          · simpa using h.1.symm
          · have habs := (abs_eq (show (0 : ℤ) ≤ 1 by norm_num)).mp h.2
            rcases habs with hb' | hb' <;> omega
        · have habs := (abs_eq (show (0 : ℤ) ≤ 1 by norm_num)).mp h.2
          rcases habs with ha' | ha' <;> omega
      apply Set.mem_singleton_iff.mpr
      funext i
      by_cases hi0 : i = 0
      · subst i
        rw [hrook.2.2.1, hv0]
      by_cases hi1 : i = 1
      · subst i
        rw [hp1, hv1]
      by_cases hi2 : i = 2
      · subst i
        rw [hp2, hv2]
      by_cases hi3 : i = 3
      · subst i
        rw [hp3, hv3]
        norm_num
      have hgt : 3 < i := by omega
      rw [hrook.2.2.2 i (by omega), hvafter i hgt]
    · intro hp
      rw [Set.mem_singleton_iff] at hp
      subst p
      exact ⟨hvrook, hv1, hv3⟩
  rw [hset]
  exact Set.encard_singleton v

private lemma putnam_2005_a2_tours_encard_formula
    (n : ℕ) (npos : 0 < n) :
    (putnam_2005_a2_tours n 1).encard =
        ((if n = 1 then 0 else 2 ^ (n - 2)) : ℕ) ∧
      (putnam_2005_a2_tours n 3).encard =
        ((if n = 1 then 1 else 2 ^ (n - 2)) : ℕ) := by
  induction n with
  | zero =>
      omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        constructor
        · simpa using putnam_2005_a2_tours_one_one_encard
        · simpa using putnam_2005_a2_tours_one_three_encard
      · have hnpos : 0 < n := by omega
        have ihpair := ih hnpos
        have hrec1 := putnam_2005_a2_tours_succ_encard n hnpos (1 : ℤ) (Or.inl rfl)
        have hrec3 := putnam_2005_a2_tours_succ_encard n hnpos (3 : ℤ) (Or.inr rfl)
        have hn1_or : n = 1 ∨ 2 ≤ n := by omega
        constructor
        · rw [hrec1]
          have h41 : (4 : ℤ) - 1 = 3 := by norm_num
          rw [h41]
          rw [ihpair.2, ihpair.1]
          rcases hn1_or with hn1 | hn2
          · subst n
            norm_num
          · have hpow : 2 ^ (n - 1) = 2 ^ (n - 2) + 2 ^ (n - 2) := by
              have hsub : n - 1 = (n - 2) + 1 := by omega
              rw [hsub, pow_succ]
              omega
            have hn_ne_one : n ≠ 1 := by omega
            have hsucc_ne_one : n + 1 ≠ 1 := by omega
            simp [hn0, hn_ne_one, hpow, add_comm]
        · rw [hrec3]
          have h43 : (4 : ℤ) - 3 = 1 := by norm_num
          rw [h43]
          rw [ihpair.1, ihpair.2]
          rcases hn1_or with hn1 | hn2
          · subst n
            norm_num
          · have hpow : 2 ^ (n - 1) = 2 ^ (n - 2) + 2 ^ (n - 2) := by
              have hsub : n - 1 = (n - 2) + 1 := by omega
              rw [hsub, pow_succ]
              omega
            have hn_ne_one : n ≠ 1 := by omega
            have hsucc_ne_one : n + 1 ≠ 1 := by omega
            simp [hn0, hn_ne_one, hpow, add_comm]

-- uses (ℕ → ℤ × ℤ) instead of (Icc 1 (3 * n) → ℤ × ℤ)
-- fun n ↦ if n = 1 then 0 else 2 ^ (n - 2)
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
: ({p : ℕ → ℤ × ℤ | rooktour p ∧ p 1 = (1, 1) ∧ p (3 * n) = ((n : ℤ), 1)}.encard = ((fun n ↦ if n = 1 then 0 else 2 ^ (n - 2)) : ℕ → ℕ ) n) := by
  classical
  by_cases hn : n = 1
  · subst n
    subst S
    subst unit
    subst rooktour
    conv_rhs => norm_num
    rw [Set.encard_eq_zero]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    rcases hp with ⟨hrook, hp1, hp3⟩
    have hmem : ((1 : ℤ), (1 : ℤ)) ∈
        Set.prod (Set.Icc (1 : ℤ) (1 : ℤ)) (Set.Icc (1 : ℤ) (3 : ℤ)) := by
      constructor <;> norm_num
    have huniq := hrook.1 ((1 : ℤ), (1 : ℤ)) hmem
    have h1 : (1 : ℕ) ∈ Set.Icc 1 (3 * (1 : ℕ)) ∧
        p 1 = ((1 : ℤ), (1 : ℤ)) := by
      constructor
      · norm_num
      · simpa using hp1
    have h3 : (3 : ℕ) ∈ Set.Icc 1 (3 * (1 : ℕ)) ∧
        p 3 = ((1 : ℤ), (1 : ℤ)) := by
      constructor
      · norm_num
      · simpa using hp3
    have h13 : (1 : ℕ) = 3 := ExistsUnique.unique huniq h1 h3
    norm_num at h13
  · subst S
    subst unit
    subst rooktour
    simp [hn]
    have hformula := (putnam_2005_a2_tours_encard_formula n npos).1
    simpa [putnam_2005_a2_tours, putnam_2005_a2_rook, putnam_2005_a2_unit, hn] using hformula
