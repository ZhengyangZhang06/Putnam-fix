import Mathlib

open MvPolynomial Real Nat Filter Topology

/--
Let $F$ be the field of $p^2$ elements, where $p$ is an odd prime. Suppose $S$ is a set of $(p^2-1)/2$ distinct nonzero elements of $F$ with the property that for each $a\neq 0$ in $F$, exactly one of $a$ and $-a$ is in $S$. Let $N$ be the number of elements in the intersection $S \cap \{2a: a \in S\}$. Prove that $N$ is even.
-/
theorem putnam_1987_b6
    (p : ℕ)
    (F : Type*) [Field F] [Fintype F]
    (S : Set F)
    (hp : Odd p ∧ Nat.Prime p)
    (Fcard : Fintype.card F = p ^ 2)
    (Snz : ∀ x ∈ S, x ≠ 0)
    (Scard : S.ncard = ((p : ℤ) ^ 2 - 1) / 2)
    (hS : ∀ a : F, a ≠ 0 → Xor' (a ∈ S) (-a ∈ S)) :
    (Even ((S ∩ {x | ∃ a ∈ S, x = 2 * a}).ncard)) :=
by
  classical
  let T : Set F := S ∩ {x | ∃ a ∈ S, x = (2 : F) * a}
  change Even T.ncard
  let s : Finset F := S.toFinset
  let P : F → Prop := fun x ↦ (2 : F) * x ∈ S
  let fVal : F → F := fun x ↦ if P x then (2 : F) * x else -((2 : F) * x)

  have htwo : (2 : F) ≠ 0 := by
    intro htwo
    have hsum : (1 : F) + 1 = 0 := by
      simpa [one_add_one_eq_two] using htwo
    have hneg : (-(1 : F)) = 1 := by
      rw [neg_eq_iff_add_eq_zero]
      simpa [add_comm] using hsum
    have hx := hS 1 one_ne_zero
    rw [hneg, xor_self] at hx
    exact hx

  have hneg_one_ne : (-1 : F) ≠ 1 := by
    intro hneg
    apply htwo
    have hsum : (1 : F) + 1 = 0 := by
      nth_rw 1 [← hneg]
      simp
    simpa [one_add_one_eq_two] using hsum

  have hchar_ne_two : ringChar F ≠ 2 := by
    intro hchar
    haveI : CharP F 2 := ringChar.of_eq hchar
    exact htwo (by simpa using (CharP.cast_eq_zero F 2))

  have hnot_pair : ∀ {z : F}, z ≠ 0 → z ∈ S → -z ∈ S → False := by
    intro z hz0 hz hzneg
    have hzxor := hS z hz0
    rcases hzxor with h | h
    · exact h.2 hzneg
    · exact h.2 hz

  have hf_memS : ∀ {x : F}, x ∈ S → fVal x ∈ S := by
    intro x hxS
    by_cases hx : P x
    · have hx' : (2 : F) * x ∈ S := by
        simpa [P] using hx
      simpa [fVal, hx] using hx'
    · have hx0 : (2 : F) * x ≠ 0 := mul_ne_zero htwo (Snz x hxS)
      have hxSxor := hS ((2 : F) * x) hx0
      rcases hxSxor with hpos | hneg
      · exact False.elim (hx hpos.1)
      · simpa [fVal, hx] using hneg.1

  let phi : S → S :=
    fun x ↦ ⟨fVal x.1, hf_memS (x := x.1) x.2⟩

  have hphi_inj : Function.Injective phi := by
    intro x y hxy
    apply Subtype.ext
    have hval : fVal x.1 = fVal y.1 := congrArg Subtype.val hxy
    by_cases hx : P x.1 <;> by_cases hy : P y.1
    · have h2xy : (2 : F) * x.1 = (2 : F) * y.1 := by
        simpa [fVal, hx, hy] using hval
      exact mul_left_cancel₀ htwo h2xy
    · have h2xy : (2 : F) * x.1 = (2 : F) * (-y.1) := by
        have h' : (2 : F) * x.1 = -((2 : F) * y.1) := by
          simpa [fVal, hx, hy] using hval
        simpa [mul_neg] using h'
      have hx_neg_y : x.1 = -y.1 := mul_left_cancel₀ htwo h2xy
      exfalso
      exact hnot_pair (Snz y.1 y.2) y.2 (by simpa [hx_neg_y] using x.2)
    · have h2yx : (2 : F) * y.1 = (2 : F) * (-x.1) := by
        have h' : (2 : F) * y.1 = -((2 : F) * x.1) := by
          simpa [fVal, hx, hy] using hval.symm
        simpa [mul_neg] using h'
      have hy_neg_x : y.1 = -x.1 := mul_left_cancel₀ htwo h2yx
      exfalso
      exact hnot_pair (Snz x.1 x.2) x.2 (by simpa [hy_neg_x] using y.2)
    · have h2xy : (2 : F) * x.1 = (2 : F) * y.1 := by
        have h' : -((2 : F) * x.1) = -((2 : F) * y.1) := by
          simpa [fVal, hx, hy] using hval
        exact neg_injective h'
      exact mul_left_cancel₀ htwo h2xy

  have hphi_surj : Function.Surjective phi :=
    Finite.surjective_of_injective hphi_inj

  have hf_mem_fin : ∀ x ∈ s, fVal x ∈ s := by
    intro x hx
    exact Set.mem_toFinset.mpr (hf_memS (Set.mem_toFinset.mp hx))

  have hf_inj_fin :
      ∀ x ∈ s, ∀ y ∈ s, fVal x = fVal y → x = y := by
    intro x hx y hy hxy
    have hsub : phi ⟨x, Set.mem_toFinset.mp hx⟩ = phi ⟨y, Set.mem_toFinset.mp hy⟩ := by
      apply Subtype.ext
      exact hxy
    exact congrArg Subtype.val (hphi_inj hsub)

  have hf_surj_fin : ∀ y ∈ s, ∃ x, ∃ _ : x ∈ s, fVal x = y := by
    intro y hy
    obtain ⟨x, hx⟩ := hphi_surj ⟨y, Set.mem_toFinset.mp hy⟩
    exact ⟨x.1, Set.mem_toFinset.mpr x.2, congrArg Subtype.val hx⟩

  have hprod_perm : (∏ x ∈ s, fVal x) = ∏ x ∈ s, x := by
    refine Finset.prod_bij (s := s) (t := s) (f := fun x ↦ fVal x) (g := fun x ↦ x)
      (fun x _ ↦ fVal x) hf_mem_fin hf_inj_fin hf_surj_fin ?_
    intro x hx
    rfl

  let negCount : ℕ := (s.filter (fun x ↦ ¬ P x)).card

  have hsign :
      (∏ x ∈ s, (if P x then (1 : F) else -1)) = (-1 : F) ^ negCount := by
    dsimp [negCount]
    rw [Finset.prod_ite]
    simp [Finset.prod_const]

  have hprod_two :
      (∏ x ∈ s, (2 : F) * x) = (2 : F) ^ s.card * ∏ x ∈ s, x := by
    simpa using
      (Finset.pow_card_mul_prod (s := s) (f := fun x : F ↦ x) (b := (2 : F))).symm

  have hprod_decomp :
      (∏ x ∈ s, fVal x) =
        (-1 : F) ^ negCount * ((2 : F) ^ s.card * ∏ x ∈ s, x) := by
    calc
      (∏ x ∈ s, fVal x)
          = ∏ x ∈ s, (if P x then (1 : F) else -1) * ((2 : F) * x) := by
              refine Finset.prod_congr rfl ?_
              intro x hx
              by_cases hpx : P x <;> simp [fVal, hpx]
      _ = (∏ x ∈ s, (if P x then (1 : F) else -1)) *
            (∏ x ∈ s, (2 : F) * x) := by
              rw [Finset.prod_mul_distrib]
      _ = (-1 : F) ^ negCount * ((2 : F) ^ s.card * ∏ x ∈ s, x) := by
              rw [hsign, hprod_two]

  have hS_half : S.ncard = Fintype.card F / 2 := by
    rw [Fcard]
    rcases hp.1 with ⟨k, rfl⟩
    have hn : (S.ncard : ℤ) = 2 * (k : ℤ) * (k + 1) := by
      rw [Scard]
      have hnum : (((2 * k + 1 : ℕ) : ℤ) ^ 2 - 1) =
          2 * (2 * (k : ℤ) * (k + 1)) := by
        norm_num [Nat.cast_add, Nat.cast_mul]
        ring
      rw [hnum]
      rw [Int.mul_ediv_cancel_left]
      norm_num
    have hn_nat : S.ncard = 2 * k * (k + 1) := by
      exact_mod_cast hn
    have hdiv : (2 * k + 1) ^ 2 / 2 = 2 * k * (k + 1) := by
      have hp2 : (2 * k + 1) ^ 2 = 2 * (2 * k * (k + 1)) + 1 := by
        ring
      rw [hp2]
      omega
    rw [hn_nat, hdiv]

  have hs_card : s.card = S.ncard := by
    simp [s, Set.ncard_eq_toFinset_card']

  have hs_half : s.card = Fintype.card F / 2 := by
    rw [hs_card, hS_half]

  have hchi : ZMod.χ₈ (Fintype.card F) = (1 : ℤ) := by
    have hmod8 : Fintype.card F % 8 = 1 := by
      rw [Fcard]
      have h8 : 8 ∣ p ^ 2 - 1 := Nat.eight_dvd_sq_sub_one_of_odd hp.1
      have hp0 : 0 < p := hp.1.pos
      have hp2pos : 0 < p ^ 2 := pow_pos hp0 2
      omega
    have hmod2 : Fintype.card F % 2 = 1 := by
      omega
    rw [ZMod.χ₈_nat_eq_if_mod_eight]
    simp [hmod2, hmod8]

  have htwo_pow_card : (2 : F) ^ (Fintype.card F / 2) = 1 := by
    simpa [hchi] using (FiniteField.two_pow_card (F := F) hchar_ne_two)

  have htwo_pow_s : (2 : F) ^ s.card = 1 := by
    simpa [hs_half] using htwo_pow_card

  have hprod_nonzero : (∏ x ∈ s, x) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr
      (by
        intro x hx
        exact Snz x (Set.mem_toFinset.mp hx))

  have hneg_pow : (-1 : F) ^ negCount = 1 := by
    have hmain :
        (-1 : F) ^ negCount * ((2 : F) ^ s.card * ∏ x ∈ s, x) = ∏ x ∈ s, x := by
      rw [← hprod_decomp]
      exact hprod_perm
    have hmain' : (-1 : F) ^ negCount * (∏ x ∈ s, x) = 1 * (∏ x ∈ s, x) := by
      simpa [htwo_pow_s, mul_assoc] using hmain
    exact mul_right_cancel₀ hprod_nonzero hmain'

  have hneg_even : Even negCount :=
    (neg_one_pow_eq_one_iff_even hneg_one_ne).mp hneg_pow

  have hS_even : Even S.ncard := by
    rcases hp.1 with ⟨k, rfl⟩
    have hn : (S.ncard : ℤ) = 2 * (k : ℤ) * (k + 1) := by
      rw [Scard]
      have hnum : (((2 * k + 1 : ℕ) : ℤ) ^ 2 - 1) =
          2 * (2 * (k : ℤ) * (k + 1)) := by
        norm_num [Nat.cast_add, Nat.cast_mul]
        ring
      rw [hnum]
      rw [Int.mul_ediv_cancel_left]
      norm_num
    refine ⟨k * (k + 1), ?_⟩
    have hn_nat : S.ncard = 2 * k * (k + 1) := by
      exact_mod_cast hn
    rw [hn_nat]
    ring

  have hs_even : Even s.card := by
    rwa [hs_card]

  have hpos_even : Even (s.filter P).card := by
    have hsplit := Finset.card_filter_add_card_filter_not (s := s) P
    dsimp [negCount] at hneg_even
    rcases hs_even with ⟨u, hu⟩
    rcases hneg_even with ⟨v, hv⟩
    refine ⟨u - v, ?_⟩
    omega

  let emb2 : F ↪ F :=
    ⟨fun x ↦ (2 : F) * x, by
      intro x y hxy
      exact mul_left_cancel₀ htwo hxy⟩

  have hT_finset : T.toFinset = (s.filter P).map emb2 := by
    ext x
    constructor
    · intro hx
      have hxT : x ∈ T := Set.mem_toFinset.mp hx
      rcases hxT with ⟨hxS, a, haS, hxa⟩
      refine Finset.mem_map.mpr ?_
      refine ⟨a, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Set.mem_toFinset.mpr haS, by simpa [P, hxa.symm] using hxS⟩
      · simp [emb2, hxa]
    · intro hx
      rcases Finset.mem_map.mp hx with ⟨a, ha, hax⟩
      have ha' := Finset.mem_filter.mp ha
      have haS : a ∈ S := Set.mem_toFinset.mp ha'.1
      have h2aS : (2 : F) * a ∈ S := ha'.2
      apply Set.mem_toFinset.mpr
      refine ⟨?_, a, haS, ?_⟩
      · simpa [emb2] using hax ▸ h2aS
      · simpa [emb2] using hax.symm

  have hT_card : T.ncard = (s.filter P).card := by
    rw [Set.ncard_eq_toFinset_card' T, hT_finset, Finset.card_map]

  rwa [hT_card]
