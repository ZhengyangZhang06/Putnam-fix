import Mathlib

open Polynomial Real Complex Matrix Filter Topology Multiset
open Asymptotics

private lemma putnam_1975_b3_esymm_zero (a : Multiset ℝ) : a.esymm 0 = 1 := by
  simp [Multiset.esymm]

private lemma putnam_1975_b3_esymm_one (a : Multiset ℝ) : a.esymm 1 = a.sum := by
  simp [Multiset.esymm, Multiset.powersetCard_one]

private lemma putnam_1975_b3_esymm_cons_succ (x : ℝ) (a : Multiset ℝ) (k : ℕ) :
    (x ::ₘ a).esymm (k + 1) = a.esymm (k + 1) + x * a.esymm k := by
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Function.comp_apply, Multiset.prod_cons]
  rw [Multiset.sum_map_mul_left]

private lemma putnam_1975_b3_esymm_nonneg (a : Multiset ℝ) (k : ℕ)
    (h : ∀ x ∈ a, 0 ≤ x) : 0 ≤ a.esymm k := by
  rw [Multiset.esymm]
  apply Multiset.sum_nonneg
  intro y hy
  rcases Multiset.mem_map.mp hy with ⟨b, hb, rfl⟩
  apply Multiset.prod_nonneg
  intro x hx
  exact h x (Multiset.mem_of_le (Multiset.mem_powersetCard.mp hb).1 hx)

private lemma putnam_1975_b3_sum_pos (a : Multiset ℝ) (h : ∀ x ∈ a, 0 < x)
    (hne : a ≠ 0) : 0 < a.sum := by
  obtain ⟨l, rfl⟩ := Quotient.mk_surjective a
  simpa using List.sum_pos l (by simpa using h) (by simpa using hne)

private lemma putnam_1975_b3_factorial_mul_esymm_le_pow (a : Multiset ℝ)
    (h : ∀ x ∈ a, 0 ≤ x) (k : ℕ) :
    (Nat.factorial k : ℝ) * a.esymm k ≤ (a.esymm 1) ^ k := by
  induction a using Multiset.induction_on generalizing k with
  | empty =>
      cases k <;> simp [Multiset.esymm]
  | cons x a ih =>
      have hx : 0 ≤ x := h x (by simp)
      have ha : ∀ y ∈ a, 0 ≤ y := by
        intro y hy
        exact h y (by simp [hy])
      cases k with
      | zero =>
          simp [putnam_1975_b3_esymm_zero]
      | succ k =>
          let S : ℝ := a.esymm 1
          have hS : 0 ≤ S := by
            dsimp [S]
            exact putnam_1975_b3_esymm_nonneg a 1 ha
          have hmain :=
            pow_add_mul_le_add_pow (a := S) (b := x) hS (by nlinarith [hS, hx]) (k + 1)
          have hih1 :
              (Nat.factorial (k + 1) : ℝ) * a.esymm (k + 1) ≤ S ^ (k + 1) := by
            simpa [S] using ih ha (k + 1)
          have hih0 : (Nat.factorial k : ℝ) * a.esymm k ≤ S ^ k := by
            simpa [S] using ih ha k
          have hfac :
              (Nat.factorial (k + 1) : ℝ) = (k + 1 : ℝ) * (Nat.factorial k : ℝ) := by
            norm_num [Nat.factorial_succ]
          have hsecond :
              (Nat.factorial (k + 1) : ℝ) * (x * a.esymm k) ≤
                (k + 1 : ℝ) * x * S ^ k := by
            calc
              (Nat.factorial (k + 1) : ℝ) * (x * a.esymm k)
                  = ((k + 1 : ℝ) * x) * ((Nat.factorial k : ℝ) * a.esymm k) := by
                      rw [hfac]
                      ring
              _ ≤ ((k + 1 : ℝ) * x) * S ^ k := by
                      exact mul_le_mul_of_nonneg_left hih0 (by positivity)
              _ = (k + 1 : ℝ) * x * S ^ k := by ring
          calc
            (Nat.factorial (k + 1) : ℝ) * (x ::ₘ a).esymm (k + 1)
                = (Nat.factorial (k + 1) : ℝ) * a.esymm (k + 1) +
                    (Nat.factorial (k + 1) : ℝ) * (x * a.esymm k) := by
                    rw [putnam_1975_b3_esymm_cons_succ]
                    ring
            _ ≤ S ^ (k + 1) + (k + 1 : ℝ) * x * S ^ k := by
                    exact add_le_add hih1 hsecond
            _ ≤ (S + x) ^ (k + 1) := by
                    simpa [S, mul_comm, mul_left_comm, mul_assoc] using hmain
            _ = (x ::ₘ a).esymm 1 ^ (k + 1) := by
                    have h1 : (x ::ₘ a).esymm 1 = S + x := by
                      simpa [S, putnam_1975_b3_esymm_zero, add_comm] using
                        putnam_1975_b3_esymm_cons_succ x a 0
                    rw [h1]

-- fun k : ℕ => 1/(Nat.factorial k)
/--
Let $s_k (a_1, a_2, \dots, a_n)$ denote the $k$-th elementary symmetric function; that is, the sum of all $k$-fold products of the $a_i$. For example, $s_1 (a_1, \dots, a_n) = \sum_{i=1}^{n} a_i$, and $s_2 (a_1, a_2, a_3) = a_1a_2 + a_2a_3 + a_1a_3$. Find the supremum $M_k$ (which is never attained) of $$\frac{s_k (a_1, a_2, \dots, a_n)}{(s_1 (a_1, a_2, \dots, a_n))^k}$$ across all $n$-tuples $(a_1, a_2, \dots, a_n)$ of positive real numbers with $n \ge k$.
-/
theorem putnam_1975_b3
: ∀ k : ℕ, k > 0 → (∀ a : Multiset ℝ, (∀ i ∈ a, i > 0) ∧ card a ≥ k →
(esymm a k)/(esymm a 1)^k ≤ ((fun k : ℕ => 1/(Nat.factorial k)) : ℕ → ℝ ) k) ∧
∀ M : ℝ, M < ((fun k : ℕ => 1/(Nat.factorial k)) : ℕ → ℝ ) k → (∃ a : Multiset ℝ, (∀ i ∈ a, i > 0) ∧ card a ≥ k ∧
(esymm a k)/(esymm a 1)^k > M) := by
  intro k hk
  constructor
  · intro a ha
    have hanonneg : ∀ i ∈ a, 0 ≤ i := by
      intro i hi
      exact le_of_lt (ha.1 i hi)
    have hineq := putnam_1975_b3_factorial_mul_esymm_le_pow a hanonneg k
    have hcardpos : 0 < card a := lt_of_lt_of_le hk ha.2
    have hane : a ≠ 0 := Multiset.card_pos.mp hcardpos
    have hsumpos : 0 < a.esymm 1 := by
      rw [putnam_1975_b3_esymm_one]
      exact putnam_1975_b3_sum_pos a ha.1 hane
    have hdenpos : 0 < (a.esymm 1) ^ k := pow_pos hsumpos k
    have hfacpos : 0 < (Nat.factorial k : ℝ) := by positivity
    have hE_le : a.esymm k ≤ (a.esymm 1) ^ k / (Nat.factorial k : ℝ) := by
      rw [le_div_iff₀ hfacpos]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hineq
    calc
      a.esymm k / (a.esymm 1) ^ k
          ≤ ((a.esymm 1) ^ k / (Nat.factorial k : ℝ)) / (a.esymm 1) ^ k := by
              exact div_le_div_of_nonneg_right hE_le hdenpos.le
      _ = 1 / (Nat.factorial k : ℝ) := by
              field_simp [ne_of_gt hdenpos, ne_of_gt hfacpos]
  · intro M hM
    have hlim :
        Tendsto (fun n : ℕ => (n.choose k : ℝ) / (n : ℝ) ^ k) atTop
          (𝓝 (1 / (Nat.factorial k : ℝ))) := by
      have hdiv :
          (fun n : ℕ => (n.choose k : ℝ) / (n : ℝ) ^ k) ~[atTop]
            (fun n : ℕ => ((n : ℝ) ^ k / (Nat.factorial k : ℝ)) / (n : ℝ) ^ k) := by
        exact (isEquivalent_choose k).div Asymptotics.IsEquivalent.refl
      have hright :
          Tendsto
            (fun n : ℕ => ((n : ℝ) ^ k / (Nat.factorial k : ℝ)) / (n : ℝ) ^ k)
            atTop (𝓝 (1 / (Nat.factorial k : ℝ))) := by
        apply tendsto_nhds_of_eventually_eq
        filter_upwards [eventually_ne_atTop 0] with n hn
        have hnz : (n : ℝ) ≠ 0 := by exact_mod_cast hn
        have hfnz : (Nat.factorial k : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
        field_simp [pow_ne_zero k hnz, hfnz]
      exact hdiv.symm.tendsto_nhds hright
    have hevent :
        ∀ᶠ n : ℕ in atTop, M < (n.choose k : ℝ) / (n : ℝ) ^ k :=
      hlim.eventually (Ioi_mem_nhds hM)
    rcases ((hevent.and (eventually_ge_atTop k)).exists) with ⟨n, hnM, hnk⟩
    let a : Multiset ℝ := (Finset.range n).val.map (fun _ : ℕ => (1 : ℝ))
    refine ⟨a, ?_, ?_, ?_⟩
    · intro i hi
      rcases Multiset.mem_map.mp hi with ⟨j, hj, rfl⟩
      norm_num
    · simpa [a] using hnk
    · have hkval : a.esymm k = (n.choose k : ℝ) := by
        rw [show a.esymm k = ((Finset.range n).val.map (fun _ : ℕ => (1 : ℝ))).esymm k by rfl]
        rw [Finset.esymm_map_val]
        simp [Finset.card_powersetCard]
      have h1val : a.esymm 1 = (n : ℝ) := by
        rw [show a.esymm 1 = ((Finset.range n).val.map (fun _ : ℕ => (1 : ℝ))).esymm 1 by rfl]
        rw [Finset.esymm_map_val]
        simp [Finset.card_powersetCard]
      simpa [hkval, h1val] using hnM
