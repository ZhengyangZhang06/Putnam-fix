import Mathlib

open Nat Set

private lemma putnam_2005_b2_bound (n : ℕ) (k : ℕ → ℤ)
    (hn : n > 0) (hpos : ∀ i ∈ Finset.range n, k i > 0)
    (hsum : ∑ i ∈ Finset.range n, k i = 5 * n - 4)
    (hrec : (∑ i : Finset.range n, (1 : ℝ) / (k i)) = 1) :
    n ≤ 4 := by
  have hrec' : (∑ i ∈ Finset.range n, (1 : ℝ) / (k i)) = 1 := by
    rw [← Finset.sum_attach]
    simpa using hrec
  have hrecInv : (∑ i ∈ Finset.range n, ((k i : ℝ)⁻¹)) = 1 := by
    simpa [one_div] using hrec'
  have hposR : ∀ i ∈ Finset.range n, (0 : ℝ) < (k i : ℝ) := by
    intro i hi
    exact_mod_cast hpos i hi
  have hsumR : (∑ i ∈ Finset.range n, (k i : ℝ)) = (5 * n - 4 : ℝ) := by
    exact_mod_cast hsum
  have hsed := Finset.sq_sum_div_le_sum_sq_div (Finset.range n)
    (fun _ : ℕ => (1 : ℝ)) (g := fun i => (k i : ℝ)) hposR
  have hleR : ((n : ℝ) ^ 2) / (5 * n - 4 : ℝ) ≤ 1 := by
    simpa [hsumR, hrecInv] using hsed
  have hdenpos : (0 : ℝ) < (5 * n - 4 : ℝ) := by
    rw [← hsumR]
    exact Finset.sum_pos hposR (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hn))
  have hquadR : ((n : ℝ) ^ 2) ≤ (5 * n - 4 : ℝ) := by
    rwa [div_le_iff₀ hdenpos, one_mul] at hleR
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnleR : (n : ℝ) ≤ 4 := by nlinarith
  exact_mod_cast hnleR

private lemma putnam_2005_b2_two_impossible (k : ℕ → ℤ)
    (hpos : ∀ i ∈ Finset.range 2, k i > 0)
    (hsum : ∑ i ∈ Finset.range 2, k i = 6)
    (hrec : (∑ i : Finset.range 2, (1 : ℝ) / (k i)) = 1) : False := by
  set a : ℤ := k 0 with ha
  set b : ℤ := k 1 with hb
  have hapos : 0 < a := by rw [ha]; exact hpos 0 (by norm_num)
  have hbpos : 0 < b := by rw [hb]; exact hpos 1 (by norm_num)
  have hsumab : a + b = 6 := by
    norm_num [Finset.sum_range_succ] at hsum
    simpa [ha, hb] using hsum
  have hrecFin : (∑ i ∈ Finset.range 2, (1 : ℝ) / (k i)) = 1 := by
    rw [← Finset.sum_attach]
    simpa using hrec
  have hrecab : (1 : ℝ) / a + 1 / b = 1 := by
    norm_num [Finset.sum_range_succ] at hrecFin
    simpa [ha, hb] using hrecFin
  have hale : a ≤ 5 := by omega
  have hble : b ≤ 5 := by omega
  interval_cases a <;> interval_cases b <;>
    (norm_num at hsumab
     try omega
     try norm_num at hrecab)

private lemma putnam_2005_b2_three_forward (k : ℕ → ℤ)
    (hpos : ∀ i ∈ Finset.range 3, k i > 0)
    (hsum : ∑ i ∈ Finset.range 3, k i = 11)
    (hrec : (∑ i : Finset.range 3, (1 : ℝ) / (k i)) = 1) :
    k '' ({0, 1, 2} : Set ℕ) = ({2, 3, 6} : Set ℤ) := by
  set a : ℤ := k 0 with ha
  set b : ℤ := k 1 with hb
  have hapos : 0 < a := by rw [ha]; exact hpos 0 (by norm_num)
  have hbpos : 0 < b := by rw [hb]; exact hpos 1 (by norm_num)
  have hk2pos : 0 < k 2 := hpos 2 (by norm_num)
  norm_num [Finset.sum_range_succ] at hsum
  have hrecFin : (∑ i ∈ Finset.range 3, (1 : ℝ) / (k i)) = 1 := by
    rw [← Finset.sum_attach]
    simpa using hrec
  norm_num [Finset.sum_range_succ] at hrecFin
  have hale : a ≤ 9 := by omega
  have hble : b ≤ 9 := by omega
  interval_cases a <;> interval_cases b <;>
    (have hk2val : k 2 = (11 : ℤ) - k 0 - k 1 := by omega
     simp [← ha, ← hb, hk2val] at hrecFin
     try norm_num at hrecFin
     try
       ext z
       simp [Set.mem_image, ← ha, ← hb, hk2val]
       tauto)

private lemma putnam_2005_b2_three_reverse (k : ℕ → ℤ)
    (himg : k '' ({0, 1, 2} : Set ℕ) = ({2, 3, 6} : Set ℤ)) :
    (∀ i ∈ Finset.range 3, k i > 0) ∧
      (∑ i ∈ Finset.range 3, k i = 11) ∧
      ((∑ i : Finset.range 3, (1 : ℝ) / (k i)) = 1) := by
  have himgFin : (Finset.range 3).image k = ({2, 3, 6} : Finset ℤ) := by
    ext z
    rw [Finset.mem_image]
    change (∃ x, x ∈ Finset.range 3 ∧ k x = z) ↔
      z ∈ (({2, 3, 6} : Finset ℤ) : Set ℤ)
    have hz : z ∈ k '' ({0, 1, 2} : Set ℕ) ↔
        z ∈ (({2, 3, 6} : Finset ℤ) : Set ℤ) := by
      rw [himg]
      simp
    rw [← hz]
    simp [Set.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨x, hx, hkx⟩
      interval_cases x <;> simp_all
    · rintro (h | h | h)
      · exact ⟨0, by norm_num, h⟩
      · exact ⟨1, by norm_num, h⟩
      · exact ⟨2, by norm_num, h⟩
  have hinj : Set.InjOn k (Finset.range 3) := by
    apply Finset.injOn_of_card_image_eq
    norm_num [himgFin]
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have hki : k i ∈ ({2, 3, 6} : Finset ℤ) := by
      rw [← himgFin]
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
    norm_num at hki
    omega
  · have hsum := Finset.sum_image (s := Finset.range 3) (g := k)
      (f := fun x : ℤ => x) hinj
    rw [himgFin] at hsum
    norm_num at hsum
    exact hsum.symm
  · have hsum := Finset.sum_image (s := Finset.range 3) (g := k)
      (f := fun x : ℤ => (1 : ℝ) / x) hinj
    rw [himgFin] at hsum
    norm_num at hsum
    have hrecFin : (∑ i ∈ Finset.range 3, (1 : ℝ) / (k i)) = 1 := by
      simpa [one_div] using hsum.symm
    rw [← Finset.sum_subtype (s := Finset.range 3) (p := fun i => i ∈ Finset.range 3)
      (by intro x; rfl) (f := fun i => (1 : ℝ) / (k i))]
    exact hrecFin

private lemma putnam_2005_b2_four_forward (k : ℕ → ℤ)
    (hpos : ∀ i ∈ Finset.range 4, k i > 0)
    (hsum : ∑ i ∈ Finset.range 4, k i = 16)
    (hrec : (∑ i : Finset.range 4, (1 : ℝ) / (k i)) = 1) :
    ∀ i : Fin 4, k i = 4 := by
  have hrecFin : (∑ i ∈ Finset.range 4, (1 : ℝ) / (k i)) = 1 := by
    rw [← Finset.sum_attach]
    simpa using hrec
  have hrecInv : (∑ i ∈ Finset.range 4, ((k i : ℝ)⁻¹)) = 1 := by
    simpa [one_div] using hrecFin
  have hsumR : (∑ i ∈ Finset.range 4, (k i : ℝ)) = 16 := by
    exact_mod_cast hsum
  have hposR : ∀ i ∈ Finset.range 4, (0 : ℝ) < (k i : ℝ) := by
    intro i hi
    exact_mod_cast hpos i hi
  have hsqsum : (∑ i ∈ Finset.range 4, (((k i : ℝ) - 4) ^ 2 / (k i : ℝ))) = 0 := by
    calc
      (∑ i ∈ Finset.range 4, (((k i : ℝ) - 4) ^ 2 / (k i : ℝ)))
          = ∑ i ∈ Finset.range 4, ((k i : ℝ) - 8 + 16 / (k i : ℝ)) := by
              apply Finset.sum_congr rfl
              intro i hi
              have hne : (k i : ℝ) ≠ 0 := (hposR i hi).ne'
              field_simp [hne]
              ring_nf
      _ = (∑ i ∈ Finset.range 4, (k i : ℝ)) - 8 * (4 : ℝ) +
            16 * (∑ i ∈ Finset.range 4, ((k i : ℝ)⁻¹)) := by
              simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum,
                div_eq_mul_inv]
              ring_nf
      _ = 0 := by norm_num [hsumR, hrecInv]
  intro j
  have hj : (j : ℕ) ∈ Finset.range 4 := Finset.mem_range.mpr j.2
  have hnonneg : ∀ i ∈ Finset.range 4,
      (0 : ℝ) ≤ (((k i : ℝ) - 4) ^ 2 / (k i : ℝ)) := by
    intro i hi
    exact div_nonneg (sq_nonneg _) (le_of_lt (hposR i hi))
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsqsum (j : ℕ) hj
  have hne : (k (j : ℕ) : ℝ) ≠ 0 := (hposR (j : ℕ) hj).ne'
  have hsquare : ((k (j : ℕ) : ℝ) - 4) ^ 2 = 0 := by
    rcases (div_eq_zero_iff.mp hzero) with hs | hden
    · exact hs
    · exact False.elim (hne hden)
  have hreal : (k (j : ℕ) : ℝ) = 4 := by
    have hlin : (k (j : ℕ) : ℝ) - 4 = 0 := sq_eq_zero_iff.mp hsquare
    linarith
  exact_mod_cast hreal

-- Note: uses ℕ → ℕ instead of Fin n → ℕ
-- {(n, k) : ℕ × (ℕ → ℤ) | (n = 1 ∧ k 0 = 1) ∨ (n = 3 ∧ (k '' {0, 1, 2} = {2, 3, 6})) ∨ (n = 4 ∧ (∀ i : Fin 4, k i = 4))}
/--
Find all positive integers $n,k_1,\dots,k_n$ such that $k_1+\cdots+k_n=5n-4$ and $\frac{1}{k_1}+\cdots+\frac{1}{k_n}=1$.
-/
theorem putnam_2005_b2
: {((n : ℕ), (k : ℕ → ℤ)) | (n > 0) ∧ (∀ i ∈ Finset.range n, k i > 0) ∧ (∑ i ∈ Finset.range n, k i = 5 * n - 4) ∧ (∑ i : Finset.range n, (1 : ℝ) / (k i) = 1)} = (({(n, k) : ℕ × (ℕ → ℤ) | (n = 1 ∧ k 0 = 1) ∨ (n = 3 ∧ (k '' {0, 1, 2} = {2, 3, 6})) ∨ (n = 4 ∧ (∀ i : Fin 4, k i = 4))}) : Set (ℕ × (ℕ → ℤ)) ) := by
  classical
  ext x
  rcases x with ⟨n, k⟩
  constructor
  · intro hx
    rcases hx with ⟨hn, hpos, hsum, hrec⟩
    have hnle : n ≤ 4 := putnam_2005_b2_bound n k hn hpos hsum hrec
    interval_cases n
    · exact Or.inl ⟨rfl, by
        norm_num [Finset.sum_range_succ] at hsum
        exact hsum⟩
    · exact False.elim (putnam_2005_b2_two_impossible k (by simpa using hpos)
        (by simpa using hsum) (by simpa using hrec))
    · exact Or.inr (Or.inl ⟨rfl,
        putnam_2005_b2_three_forward k (by simpa using hpos)
          (by simpa using hsum) (by simpa using hrec)⟩)
    · exact Or.inr (Or.inr ⟨rfl,
        putnam_2005_b2_four_forward k (by simpa using hpos)
          (by simpa using hsum) (by simpa using hrec)⟩)
  · intro hx
    rcases hx with h1 | h3 | h4
    · rcases h1 with ⟨rfl, hk0⟩
      refine ⟨by norm_num, ?_, ?_, ?_⟩
      · intro i hi
        simp at hi
        subst i
        norm_num [hk0]
      · norm_num [Finset.sum_range_succ, hk0]
      · simp [hk0]
    · rcases h3 with ⟨rfl, himg⟩
      rcases putnam_2005_b2_three_reverse k himg with ⟨hpos3, hsum3, hrec3⟩
      refine ⟨by norm_num, hpos3, ?_, hrec3⟩
      simpa using hsum3
    · rcases h4 with ⟨rfl, hk⟩
      refine ⟨by norm_num, ?_, ?_, ?_⟩
      · intro i hi
        have hi4 : i < 4 := Finset.mem_range.mp hi
        have hki := hk ⟨i, hi4⟩
        norm_num [hki]
      · norm_num [Finset.sum_range_succ, hk ⟨0, by norm_num⟩, hk ⟨1, by norm_num⟩,
          hk ⟨2, by norm_num⟩, hk ⟨3, by norm_num⟩]
      · rw [← Finset.sum_subtype (s := Finset.range 4) (p := fun i => i ∈ Finset.range 4)
          (by intro x; rfl) (f := fun i => (1 : ℝ) / (k i))]
        norm_num [Finset.sum_range_succ, hk ⟨0, by norm_num⟩, hk ⟨1, by norm_num⟩,
          hk ⟨2, by norm_num⟩, hk ⟨3, by norm_num⟩]
