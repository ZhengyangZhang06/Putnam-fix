import Mathlib

open Set Topology Filter Polynomial

abbrev putnam_1979_b3_solution : ℕ → ℤ := fun n ↦ Int.floor (((n : ℚ) - 1) / 2)

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
: ({d : F | Irreducible (p + (C d))}.ncard = putnam_1979_b3_solution n) :=
by
  classical
  have hcardodd : Odd (Fintype.card F) := by
    simpa [hn] using nodd
  have hchar_ne_two : ringChar F ≠ 2 := by
    intro hchar
    have h0 : Fintype.card F % 2 = 0 :=
      FiniteField.even_card_of_char_two (F := F) hchar
    have h1 : Fintype.card F % 2 = 1 := Nat.odd_iff.mp hcardodd
    omega
  haveI : NeZero (2 : F) := ⟨Ring.two_ne_zero hchar_ne_two⟩

  have hirr_iff (d : F) :
      Irreducible (p + C d) ↔ ¬ IsSquare (discrim (1 : F) b (c + d)) := by
    have hpoly : p + C d = X ^ 2 + C b * X + C (c + d) := by
      rw [hp.1]
      simp only [map_add]
      ring_nf
    have hnat : (p + C d).natDegree = 2 := by
      rw [hpoly]
      exact (Polynomial.isMonicOfDegree_add_add_two b (c + d)).natDegree_eq
    have hne : p + C d ≠ 0 := by
      intro hz
      have hzdeg := congrArg Polynomial.natDegree hz
      rw [hnat, Polynomial.natDegree_zero] at hzdeg
      norm_num at hzdeg
    have hroots : (p + C d).roots = 0 ↔ ∀ x : F, (p + C d).eval x ≠ 0 := by
      rw [Multiset.eq_zero_iff_forall_notMem]
      simp [Polynomial.mem_roots hne]
    have hnoRoot :
        (∀ x : F, (p + C d).eval x ≠ 0) ↔
          ¬ IsSquare (discrim (1 : F) b (c + d)) := by
      constructor
      · intro h hs
        rcases hs with ⟨s, hs⟩
        rcases exists_quadratic_eq_zero (a := (1 : F)) (b := b) (c := c + d)
            one_ne_zero ⟨s, hs⟩ with ⟨x, hx⟩
        apply h x
        rw [hpoly]
        simpa [pow_two] using hx
      · intro h x hx
        apply h
        have hxq : (1 : F) * (x * x) + b * x + (c + d) = 0 := by
          rw [hpoly] at hx
          simpa [pow_two] using hx
        refine ⟨2 * (1 : F) * x + b, ?_⟩
        simpa [pow_two] using
          (discrim_eq_sq_of_quadratic_eq_zero (a := (1 : F)) (b := b)
            (c := c + d) hxq)
    rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three]
    · exact hroots.trans hnoRoot
    · rw [hnat]
    · rw [hnat]
      norm_num

  have hdisc_inj : Function.Injective fun d : F ↦ discrim (1 : F) b (c + d) := by
    intro d1 d2 h
    have h4 : (4 : F) ≠ 0 := by
      rw [show (4 : F) = (2 : F) * (2 : F) by norm_num]
      exact mul_ne_zero two_ne_zero two_ne_zero
    simp [discrim] at h
    ring_nf at h
    exact h.resolve_right h4
  have hdisc_surj : Function.Surjective fun d : F ↦ discrim (1 : F) b (c + d) := by
    intro a
    refine ⟨(b ^ 2 - 4 * c - a) / 4, ?_⟩
    have h4 : (4 : F) ≠ 0 := by
      rw [show (4 : F) = (2 : F) * (2 : F) by norm_num]
      exact mul_ne_zero two_ne_zero two_ne_zero
    simp [discrim]
    field_simp [h4]
    ring
  have hdisc_card :
      ({d : F | Irreducible (p + C d)}.ncard =
        {a : F | ¬ IsSquare a}.ncard) := by
    refine Set.ncard_congr (fun d _ ↦ discrim (1 : F) b (c + d)) ?_ ?_ ?_
    · intro d hd
      exact (hirr_iff d).mp hd
    · intro d1 d2 _ _ h
      exact hdisc_inj h
    · intro a ha
      rcases hdisc_surj a with ⟨d, rfl⟩
      exact ⟨d, (hirr_iff d).mpr ha, rfl⟩

  have hnonsquares :
      ({a : F | ¬ IsSquare a}.ncard = (Fintype.card F - 1) / 2) := by
    let H : Subgroup Fˣ := (powMonoidHom 2 : Fˣ →* Fˣ).range
    have hunit : ∀ u : Fˣ, IsSquare (u : F) ↔ u ∈ H := by
      intro u
      constructor
      · rintro ⟨y, hy⟩
        have hy0 : y ≠ 0 := by
          intro hyz
          have hu0 : (u : F) = 0 := by
            rw [hyz, mul_zero] at hy
            exact hy
          exact u.ne_zero hu0
        refine (MonoidHom.mem_range).2 ⟨Units.mk0 y hy0, ?_⟩
        ext
        simpa [H, pow_two] using hy.symm
      · intro hu
        rcases (MonoidHom.mem_range).1 hu with ⟨v, hv⟩
        refine ⟨(v : F), ?_⟩
        have hv' := congrArg Units.val hv
        simpa [H, pow_two] using hv'.symm
    let e : {a : F // ¬ IsSquare a} ≃ {u : Fˣ // u ∉ H} :=
      { toFun := fun a ↦
          have ha0 : (a : F) ≠ 0 := by
            intro ha0
            exact a.2 ⟨0, by simp [ha0]⟩
          ⟨Units.mk0 (a : F) ha0, by
            intro hmem
            exact a.2 ((hunit (Units.mk0 (a : F) ha0)).mpr hmem)⟩
        invFun := fun u ↦
          ⟨(u.1 : F), by
            intro hs
            exact u.2 ((hunit u.1).mp hs)⟩
        left_inv := by
          intro a
          ext
          rfl
        right_inv := by
          intro u
          ext
          rfl }
    have hncard :
        ({a : F | ¬ IsSquare a}.ncard = Fintype.card {a : F // ¬ IsSquare a}) := by
      rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
      rfl
    have hHcard : Fintype.card H = Fintype.card Fˣ / 2 := by
      have heven_units : 2 ∣ Nat.card Fˣ := by
        rw [Nat.card_eq_fintype_card, Fintype.card_units]
        rw [Nat.dvd_iff_mod_eq_zero]
        have hmod : Fintype.card F % 2 = 1 := Nat.odd_iff.mp hcardodd
        omega
      have hgcd : (Nat.card Fˣ).gcd 2 = 2 := Nat.gcd_eq_right heven_units
      have hgcd' : (Fintype.card Fˣ).gcd 2 = 2 := by
        simpa [Nat.card_eq_fintype_card] using hgcd
      simpa [H, hgcd', Nat.card_eq_fintype_card] using
        (IsCyclic.card_powMonoidHom_range (Fˣ) 2)
    calc
      ({a : F | ¬ IsSquare a}.ncard) = Fintype.card {a : F // ¬ IsSquare a} := hncard
      _ = Fintype.card {u : Fˣ // u ∉ H} := Fintype.card_congr e
      _ = Fintype.card Fˣ - Fintype.card H := by
        simpa [H] using (Fintype.card_subtype_compl (fun u : Fˣ ↦ u ∈ H))
      _ = (Fintype.card F - 1) / 2 := by
        rw [hHcard, Fintype.card_units]
        have hmod : Fintype.card F % 2 = 1 := Nat.odd_iff.mp hcardodd
        omega

  rw [putnam_1979_b3_solution]
  rw [hdisc_card, hnonsquares, hn]
  have hmod : Fintype.card F % 2 = 1 := Nat.odd_iff.mp hcardodd
  have hpos : 1 ≤ Fintype.card F := by omega
  have hdiv : 2 ∣ Fintype.card F - 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  have hrat : (((Fintype.card F : ℚ) - 1) / 2) =
      (((Fintype.card F - 1) / 2 : ℕ) : ℚ) := by
    rw [Nat.cast_div hdiv (by norm_num : (2 : ℚ) ≠ 0)]
    rw [Nat.cast_sub hpos]
    ring
  rw [hrat, Int.floor_natCast]
