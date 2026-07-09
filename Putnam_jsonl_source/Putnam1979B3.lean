import Mathlib

open Set Topology Filter Polynomial

-- fun n ↦ (n - 1) / 2
/--
Let $F$ be a finite field with $n$ elements, and assume $n$ is odd. Suppose $x^2 + bx + c$ is an irreducible polynomial over $F$. For how many elements $d \in F$ is $x^2 + bx + c + d$ irreducible?
-/
theorem putnam_1979_b3
(F : Type*) [Field F] [Fintype F]
(n : ℕ)
(hn : n = Fintype.card F)
(nodd : Odd n)
(b c : F)
(p : Polynomial F)
(hp : p = X ^ 2 + (C b) * X + (C c) ∧ Irreducible p)
: ({d : F | Irreducible (p + (C d))}.ncard = ((fun n ↦ (n - 1) / 2) : ℕ → ℤ ) n) := by
  classical
  subst n
  have hchar : ringChar F ≠ 2 := by
    intro h
    have h0 : Fintype.card F % 2 = 0 := FiniteField.even_card_of_char_two h
    have h1 : Fintype.card F % 2 = 1 := Nat.odd_iff.mp nodd
    omega
  have htwo : (2 : F) ≠ 0 := Ring.two_ne_zero hchar
  let A : F := (b / 2) ^ 2 - c
  have hroot_iff (e : F) :
      (∃ x, Polynomial.IsRoot (X ^ 2 + C b * X + C e : F[X]) x) ↔
        IsSquare ((b / 2) ^ 2 - e) := by
    constructor
    · rintro ⟨x, hx⟩
      rw [isSquare_iff_exists_sq]
      refine ⟨x + b / 2, ?_⟩
      have hx' : x ^ 2 + b * x + e = 0 := by
        simpa [Polynomial.IsRoot] using hx
      have hsq : (b / 2) ^ 2 - e = (x + b / 2) * (x + b / 2) := by
        field_simp [htwo]
        ring_nf at hx' ⊢
        linear_combination -4 * hx'
      simpa [pow_two] using hsq
    · intro hs
      rw [isSquare_iff_exists_sq] at hs
      rcases hs with ⟨y, hy⟩
      refine ⟨y - b / 2, ?_⟩
      have hy' : (b / 2) ^ 2 - e = y * y := by
        simpa [pow_two] using hy
      have hval : (y - b / 2) ^ 2 + b * (y - b / 2) + e = 0 := by
        field_simp [htwo] at hy' ⊢
        ring_nf at hy' ⊢
        rw [← hy']
        ring
      simpa [Polynomial.IsRoot] using hval
  have hirr_iff (d : F) : Irreducible (p + C d) ↔ ¬ IsSquare (A - d) := by
    have hpoly : p + C d = X ^ 2 + C b * X + C (c + d) := by
      rw [hp.1]
      simp only [map_add]
      ring_nf
    rw [hpoly]
    have hmd : (X ^ 2 + C b * X + C (c + d) : F[X]).IsMonicOfDegree 2 :=
      Polynomial.isMonicOfDegree_add_add_two b (c + d)
    calc
      Irreducible (X ^ 2 + C b * X + C (c + d) : F[X])
          ↔ ¬ ∃ x, Polynomial.IsRoot (X ^ 2 + C b * X + C (c + d) : F[X]) x := by
            rw [hmd.monic.irreducible_iff_roots_eq_zero_of_degree_le_three]
            · constructor
              · rintro h ⟨x, hx⟩
                have hxmem : x ∈ (X ^ 2 + C b * X + C (c + d) : F[X]).roots :=
                  (Polynomial.mem_roots hmd.ne_zero).mpr hx
                rw [h] at hxmem
                simp at hxmem
              · intro h
                apply Multiset.eq_zero_of_forall_notMem
                intro x hx
                exact h ⟨x, (Polynomial.mem_roots hmd.ne_zero).mp hx⟩
            · rw [hmd.natDegree_eq]
            · rw [hmd.natDegree_eq]
              norm_num
      _ ↔ ¬ IsSquare ((b / 2) ^ 2 - (c + d)) := not_congr (hroot_iff (c + d))
      _ ↔ ¬ IsSquare (A - d) := by
        have hexpr : (b / 2) ^ 2 - (c + d) = A - d := by
          subst A
          ring
        rw [hexpr]
  have hncard_irred :
      {d : F | Irreducible (p + C d)}.ncard = {a : F | ¬ IsSquare a}.ncard := by
    refine Set.ncard_congr (fun d _ => A - d) ?_ ?_ ?_
    · intro d hd
      exact (hirr_iff d).mp hd
    · intro d₁ d₂ _ _ h
      exact sub_right_inj.mp h
    · intro y hy
      refine ⟨A - y, ?_, ?_⟩
      · apply (hirr_iff (A - y)).mpr
        have hAy : A - (A - y) = y := by ring
        simpa [hAy] using hy
      · ring
  let sq : Finset F := Finset.univ.filter fun a : F => a ≠ 0 ∧ IsSquare a
  let nonsq : Finset F := Finset.univ.filter fun a : F => ¬ IsSquare a
  have hsum_count :
      (∑ a : F, quadraticChar F a) = (sq.card : ℤ) - (nonsq.card : ℤ) := by
    have hpoint : ∀ a : F,
        quadraticChar F a =
          (if a ≠ 0 ∧ IsSquare a then (1 : ℤ) else 0) -
            (if ¬ IsSquare a then (1 : ℤ) else 0) := by
      intro a
      by_cases ha : a = 0
      · simp [quadraticChar, quadraticCharFun, ha]
      · by_cases hs : IsSquare a
        · simp [quadraticChar, quadraticCharFun, ha, hs]
        · simp [quadraticChar, quadraticCharFun, ha, hs]
    calc
      (∑ a : F, quadraticChar F a)
          = ∑ a : F, ((if a ≠ 0 ∧ IsSquare a then (1 : ℤ) else 0) -
              (if ¬ IsSquare a then (1 : ℤ) else 0)) := by
            simp [hpoint]
      _ = (∑ a : F, (if a ≠ 0 ∧ IsSquare a then (1 : ℤ) else 0)) -
            (∑ a : F, (if ¬ IsSquare a then (1 : ℤ) else 0)) := by
            rw [Finset.sum_sub_distrib]
      _ = (sq.card : ℤ) - (nonsq.card : ℤ) := by
            rw [Finset.sum_boole, Finset.sum_boole]
  have hsq_eq_nonsq : sq.card = nonsq.card := by
    have hsum0 : (∑ a : F, quadraticChar F a) = 0 := quadraticChar_sum_zero hchar
    have hdiff : (sq.card : ℤ) - (nonsq.card : ℤ) = 0 := by
      rw [← hsum_count, hsum0]
    omega
  have hnonzero_card : (Finset.univ.filter (fun a : F => a ≠ 0)).card = Fintype.card F - 1 := by
    have h :=
      Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset F)) (p := fun a : F => a = 0)
    have hzero : (Finset.univ.filter (fun a : F => a = 0)).card = 1 := by
      rw [Finset.card_eq_one]
      exact ⟨0, by ext a; simp⟩
    rw [hzero] at h
    simp only [Finset.card_univ] at h
    have h' : 1 + (Finset.univ.filter (fun a : F => a ≠ 0)).card = Fintype.card F := by
      simpa [ne_eq] using h
    omega
  have hpartition : sq.card + nonsq.card = Fintype.card F - 1 := by
    have h :=
      Finset.card_filter_add_card_filter_not
        (s := (Finset.univ.filter (fun a : F => a ≠ 0))) (p := fun a : F => IsSquare a)
    have hnot :
        (Finset.univ.filter (fun a : F => ¬ IsSquare a ∧ a ≠ 0)) =
          (Finset.univ.filter (fun a : F => ¬ IsSquare a)) := by
      ext a
      constructor
      · intro ha
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, (Finset.mem_filter.mp ha).2.1⟩
      · intro ha
        have hns : ¬ IsSquare a := (Finset.mem_filter.mp ha).2
        have hne : a ≠ 0 := by
          intro hz
          apply hns
          rw [hz]
          exact IsSquare.zero
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, hns, hne⟩
    have hpart :
        sq.card + nonsq.card = (Finset.univ.filter (fun a : F => a ≠ 0)).card := by
      simpa [sq, nonsq, Finset.filter_filter, and_left_comm, and_assoc, and_comm, hnot] using h
    rw [hpart, hnonzero_card]
  have hnonsq : nonsq.card = (Fintype.card F - 1) / 2 := by
    omega
  have hncard_nonsq : {a : F | ¬ IsSquare a}.ncard = nonsq.card := by
    rw [Set.ncard_eq_toFinset_card]
    simp [nonsq]
  rw [hncard_irred, hncard_nonsq, hnonsq]
  rcases nodd with ⟨k, hk⟩
  rw [hk]
  norm_num
