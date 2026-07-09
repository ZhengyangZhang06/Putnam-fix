import Mathlib

open Polynomial Real Complex Matrix Filter Topology Multiset

noncomputable abbrev putnam_1975_b3_solution : ℕ → ℝ := fun k => ∏ i : Fin k, ((i + 1 : ℝ)⁻¹)

private lemma putnam_1975_b3_esymm_cons_succ (x : ℝ) (s : Multiset ℝ) (k : ℕ) :
    (x ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + x * s.esymm k := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_add, Multiset.map_map,
    Multiset.sum_map_mul_left, Multiset.prod_cons]

private lemma putnam_1975_b3_esymm_one_eq_sum (s : Multiset ℝ) :
    s.esymm 1 = s.sum := by
  simp [Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map]

private lemma putnam_1975_b3_multiset_sum_pos {s : Multiset ℝ}
    (h : ∀ x ∈ s, 0 < x) (hne : s ≠ 0) : 0 < s.sum := by
  induction s using Multiset.induction with
  | empty => contradiction
  | cons a s ih =>
      rw [Multiset.sum_cons]
      have ha : 0 < a := h a (by simp)
      have hs_nonneg : 0 ≤ s.sum :=
        Multiset.sum_nonneg (fun x hx => le_of_lt (h x (by simp [hx])))
      exact add_pos_of_pos_of_nonneg ha hs_nonneg

private lemma putnam_1975_b3_factorial_mul_esymm_le_sum_pow
    (s : Multiset ℝ) (h : ∀ x ∈ s, 0 ≤ x) :
    ∀ k : ℕ, (Nat.factorial k : ℝ) * s.esymm k ≤ s.sum ^ k := by
  induction s using Multiset.induction with
  | empty =>
      intro k
      cases k <;> simp [Multiset.esymm]
  | cons x s ih =>
      intro k
      have hx : 0 ≤ x := h x (by simp)
      have hs : ∀ y ∈ s, 0 ≤ y := fun y hy => h y (by simp [hy])
      have hsum : 0 ≤ s.sum := Multiset.sum_nonneg hs
      cases k with
      | zero => simp [Multiset.esymm]
      | succ k =>
          calc
            (Nat.factorial (k + 1) : ℝ) * (x ::ₘ s).esymm (k + 1)
                = (Nat.factorial (k + 1) : ℝ) * s.esymm (k + 1) +
                    ((k + 1 : ℕ) : ℝ) * x *
                      ((Nat.factorial k : ℝ) * s.esymm k) := by
                  rw [putnam_1975_b3_esymm_cons_succ]
                  rw [Nat.factorial_succ, Nat.cast_mul]
                  ring
            _ ≤ s.sum ^ (k + 1) + ((k + 1 : ℕ) : ℝ) * x * s.sum ^ k := by
                  gcongr
                  · exact ih hs (k + 1)
                  · exact ih hs k
            _ = s.sum ^ (k + 1) + ((k + 1 : ℕ) : ℝ) * s.sum ^ k * x := by
                  ring
            _ ≤ (s.sum + x) ^ (k + 1) := by
                  simpa [Nat.succ_eq_add_one] using
                    (pow_add_mul_le_add_pow (a := s.sum) (b := x) hsum
                      (by nlinarith) (k + 1))
            _ = (x ::ₘ s).sum ^ (k + 1) := by
                  simp [Multiset.sum_cons, add_comm]

private lemma putnam_1975_b3_esymm_replicate_one (n k : ℕ) :
    (Multiset.replicate n (1 : ℝ)).esymm k = (Nat.choose n k : ℝ) := by
  have hmap0 :
      (Multiset.powersetCard k (Multiset.replicate n (1 : ℝ))).map Multiset.prod =
        Multiset.replicate
          (((Multiset.powersetCard k (Multiset.replicate n (1 : ℝ))).map
            Multiset.prod).card) (1 : ℝ) := by
    apply Multiset.eq_replicate_card.2
    intro b hb
    rcases Multiset.mem_map.mp hb with ⟨t, ht, rfl⟩
    exact Multiset.prod_eq_one fun y hy =>
      Multiset.eq_of_mem_replicate
        (Multiset.mem_of_le (Multiset.mem_powersetCard.mp ht).1 hy)
  have hmap :
      (Multiset.powersetCard k (Multiset.replicate n (1 : ℝ))).map Multiset.prod =
        Multiset.replicate
          ((Multiset.powersetCard k (Multiset.replicate n (1 : ℝ))).card) (1 : ℝ) := by
    simpa [Multiset.card_map] using hmap0
  rw [Multiset.esymm, hmap, Multiset.sum_replicate, Multiset.card_powersetCard]
  simp

private lemma putnam_1975_b3_choose_div_pow_tendsto (k : ℕ) :
    Tendsto (fun n : ℕ => (Nat.choose n k : ℝ) / (n : ℝ)^k) atTop
      (𝓝 (1 / (Nat.factorial k : ℝ))) := by
  let F : ℝ := Nat.factorial k
  have heq : Asymptotics.IsEquivalent atTop
      (fun n : ℕ => (Nat.choose n k : ℝ) / (n : ℝ)^k)
      (fun n : ℕ => (((n : ℝ)^k / F) / (n : ℝ)^k)) := by
    simpa [F] using
      (isEquivalent_choose k).div
        (Asymptotics.IsEquivalent.refl (u := fun n : ℕ => (n : ℝ)^k))
  have hconst : (fun n : ℕ => (((n : ℝ)^k / F) / (n : ℝ)^k)) =ᶠ[atTop]
      (fun _ : ℕ => 1 / F) := by
    refine Filter.eventually_atTop.mpr ⟨1, ?_⟩
    intro n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
    have hpow : (n : ℝ)^k ≠ 0 := pow_ne_zero k hn0
    have hF : F ≠ 0 := by
      dsimp [F]
      exact_mod_cast Nat.factorial_ne_zero k
    field_simp [hpow, hF]
  have htend_rhs : Tendsto (fun n : ℕ => (((n : ℝ)^k / F) / (n : ℝ)^k)) atTop
      (𝓝 (1 / F)) := by
    exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm hconst) tendsto_const_nhds
  simpa [F] using heq.symm.tendsto_nhds htend_rhs

/--
Let $s_k (a_1, a_2, \dots, a_n)$ denote the $k$-th elementary symmetric function; that is, the sum of all $k$-fold products of the $a_i$. For example, $s_1 (a_1, \dots, a_n) = \sum_{i=1}^{n} a_i$, and $s_2 (a_1, a_2, a_3) = a_1a_2 + a_2a_3 + a_1a_3$. Find the supremum $M_k$ (which is never attained) of $$\frac{s_k (a_1, a_2, \dots, a_n)}{(s_1 (a_1, a_2, \dots, a_n))^k}$$ across all $n$-tuples $(a_1, a_2, \dots, a_n)$ of positive real numbers with $n \ge k$.
-/
theorem putnam_1975_b3
: ∀ k : ℕ, k > 0 → (∀ a : Multiset ℝ, (∀ i ∈ a, i > 0) ∧ card a ≥ k →
(esymm a k)/(esymm a 1)^k ≤ putnam_1975_b3_solution k) ∧
∀ M : ℝ, M < putnam_1975_b3_solution k → (∃ a : Multiset ℝ, (∀ i ∈ a, i > 0) ∧ card a ≥ k ∧
(esymm a k)/(esymm a 1)^k > M) :=
by
  intro k hk
  constructor
  · intro a ha
    have hcardpos : 0 < a.card := lt_of_lt_of_le hk ha.2
    have hsumpos : 0 < a.sum :=
      putnam_1975_b3_multiset_sum_pos ha.1 (Multiset.card_pos.mp hcardpos)
    have hpowpos : 0 < a.sum ^ k := pow_pos hsumpos k
    have hfacpos : 0 < (Nat.factorial k : ℝ) := by positivity
    have hle : (Nat.factorial k : ℝ) * a.esymm k ≤ a.sum ^ k :=
      putnam_1975_b3_factorial_mul_esymm_le_sum_pow a
        (fun x hx => le_of_lt (ha.1 x hx)) k
    have hmain : a.esymm k / a.sum ^ k ≤ 1 / (Nat.factorial k : ℝ) := by
      rw [div_le_iff₀ hpowpos]
      simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using
        (le_div_iff₀' hfacpos).2 (by simpa [mul_comm] using hle)
    rw [putnam_1975_b3_esymm_one_eq_sum]
    dsimp [putnam_1975_b3_solution]
    have hprod : (∏ i : Fin k, ((i + 1 : ℝ)⁻¹)) =
        1 / (Nat.factorial k : ℝ) := by
      rw [Fin.prod_univ_eq_prod_range (fun i : ℕ => ((i + 1 : ℝ)⁻¹)) k]
      have hbase : (∏ i ∈ Finset.range k, (i + 1 : ℝ)) =
          (Nat.factorial k : ℝ) := by
        clear hmain hle hfacpos hpowpos hsumpos hcardpos ha hk a
        induction k with
        | zero => simp
        | succ k ih =>
            rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
            norm_num [Nat.cast_add, Nat.cast_mul]
            ring
      rw [Finset.prod_inv_distrib, hbase]
      simp [one_div]
    rwa [hprod]
  · intro M hM
    have hlim := putnam_1975_b3_choose_div_pow_tendsto k
    have hevent : ∀ᶠ n : ℕ in atTop,
        M < (Nat.choose n k : ℝ) / (n : ℝ)^k := by
      exact hlim.eventually
        (eventually_gt_nhds (by
          dsimp [putnam_1975_b3_solution] at hM ⊢
          have hprod : (∏ i : Fin k, ((i + 1 : ℝ)⁻¹)) =
              1 / (Nat.factorial k : ℝ) := by
            rw [Fin.prod_univ_eq_prod_range (fun i : ℕ => ((i + 1 : ℝ)⁻¹)) k]
            have hbase : (∏ i ∈ Finset.range k, (i + 1 : ℝ)) =
                (Nat.factorial k : ℝ) := by
              clear hlim hM hk M
              induction k with
              | zero => simp
              | succ k ih =>
                  rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
                  norm_num [Nat.cast_add, Nat.cast_mul]
                  ring
            rw [Finset.prod_inv_distrib, hbase]
            simp [one_div]
          rwa [hprod] at hM))
    have htail : ∀ᶠ n : ℕ in atTop, k ≤ n :=
      Filter.eventually_atTop.mpr ⟨k, fun n hn => hn⟩
    rcases Filter.Eventually.exists (hevent.and htail) with ⟨n, hnratio, hnk⟩
    refine ⟨Multiset.replicate n (1 : ℝ), ?_, ?_, ?_⟩
    · intro i hi
      have hi1 : i = 1 := Multiset.eq_of_mem_replicate hi
      linarith
    · simpa using hnk
    · simpa [putnam_1975_b3_esymm_replicate_one, Nat.choose_one_right] using hnratio
