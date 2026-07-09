import Mathlib

open Topology Filter Set

private lemma putnam_2019_b2_trig_term (A B h : ℝ) (hh : h = B - A)
    (hcosA : Real.cos A ≠ 0) (hcosB : Real.cos B ≠ 0) (hsin : Real.sin h ≠ 0) :
    Real.sin (A + B) / (Real.cos A ^ 2 * Real.cos B ^ 2) =
      (Real.tan B ^ 2 - Real.tan A ^ 2) / Real.sin h := by
  subst h
  rw [Real.sin_sub] at hsin
  rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, Real.sin_sub, Real.sin_add]
  field_simp [hcosA, hcosB]
  ring_nf
  field_simp [show -(Real.sin A * Real.cos B) + Real.cos A * Real.sin B ≠ 0 by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
      mul_assoc] using hsin]
  ring_nf

private lemma putnam_2019_b2_angle_pos (n : ℕ) (hn : 0 < n) :
    0 < Real.pi / (2 * (n : ℝ)) := by
  positivity

private lemma putnam_2019_b2_sin_angle_pos (n : ℕ) (hn : 0 < n) :
    0 < Real.sin (Real.pi / (2 * (n : ℝ))) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact putnam_2019_b2_angle_pos n hn
  · have hnRge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [div_lt_iff₀]
    · nlinarith [Real.pi_pos, hnRge1]
    · positivity

private lemma putnam_2019_b2_cos_pos_index (n j : ℕ) (hn : 0 < n) (hj : j < n) :
    0 < Real.cos (((j : ℝ) * Real.pi) / (2 * (n : ℝ))) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have hnonneg : 0 ≤ ((j : ℝ) * Real.pi) / (2 * (n : ℝ)) := by positivity
    have hneg : -(Real.pi / 2) < (0 : ℝ) := by nlinarith [Real.pi_pos]
    exact lt_of_lt_of_le hneg hnonneg
  · have hjR : (j : ℝ) < (n : ℝ) := by exact_mod_cast hj
    rw [div_lt_iff₀]
    · nlinarith [Real.pi_pos, hjR]
    · positivity

private lemma putnam_2019_b2_final_tan (n : ℕ) (hn : 1 ≤ n) :
    (Real.tan (((n - 1 : ℕ) : ℝ) * Real.pi / (2 * (n : ℝ))) ^ 2 - Real.tan 0 ^ 2) /
        Real.sin (Real.pi / (2 * (n : ℝ))) =
      Real.cos (Real.pi / (2 * (n : ℝ))) ^ 2 /
        Real.sin (Real.pi / (2 * (n : ℝ))) ^ 3 := by
  have hs : Real.sin (Real.pi / (2 * (n : ℝ))) ≠ 0 :=
    (putnam_2019_b2_sin_angle_pos n (lt_of_lt_of_le Nat.zero_lt_one hn)).ne'
  have hangle : ((n - 1 : ℕ) : ℝ) * Real.pi / (2 * (n : ℝ)) =
      Real.pi / 2 - Real.pi / (2 * (n : ℝ)) := by
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    rw [Nat.cast_sub hn]
    field_simp [hn0]
    ring_nf
  rw [hangle, Real.tan_pi_div_two_sub, Real.tan_zero,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero]
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hs]

private lemma putnam_2019_b2_sum_eq (n : ℕ) (hn : 2 ≤ n) :
    (∑ k : Icc (1 : ℤ) ((n : ℤ) - 1),
      Real.sin ((2 * k - 1) * Real.pi / (2 * n)) /
        ((Real.cos ((k - 1) * Real.pi / (2 * n)) ^ 2) *
          (Real.cos (k * Real.pi / (2 * n)) ^ 2))) =
      Real.cos (Real.pi / (2 * (n : ℝ))) ^ 2 /
        Real.sin (Real.pi / (2 * (n : ℝ))) ^ 3 := by
  let F : ℕ → ℝ := fun i => Real.tan (((i : ℝ) * Real.pi) / (2 * (n : ℝ))) ^ 2
  let G : ℤ → ℝ := fun k =>
    Real.sin ((2 * k - 1 : ℤ) * Real.pi / (2 * (n : ℝ))) /
      ((Real.cos ((k - 1 : ℤ) * Real.pi / (2 * (n : ℝ))) ^ 2) *
        (Real.cos (k * Real.pi / (2 * (n : ℝ))) ^ 2))
  let h : ℝ := Real.pi / (2 * (n : ℝ))
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hsin : Real.sin h ≠ 0 := (putnam_2019_b2_sin_angle_pos n hnpos).ne'
  have hcard : ((((n : ℤ) - 1) + 1 - (1 : ℤ)).toNat) = n - 1 := by omega
  calc
    (∑ k : Icc (1 : ℤ) ((n : ℤ) - 1),
      Real.sin ((2 * k - 1) * Real.pi / (2 * n)) /
        ((Real.cos ((k - 1) * Real.pi / (2 * n)) ^ 2) *
          (Real.cos (k * Real.pi / (2 * n)) ^ 2)))
        = ∑ k : Icc (1 : ℤ) ((n : ℤ) - 1), G k := by
          apply Finset.sum_congr rfl
          intro k hk
          dsimp [G]
          simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_one]
    _ = ∑ i ∈ Finset.range (n - 1), G ((i : ℤ) + 1) := by
          rw [← Finset.sum_subtype
            (s := Finset.Icc (1 : ℤ) ((n : ℤ) - 1))
            (p := fun x : ℤ => x ∈ Icc (1 : ℤ) ((n : ℤ) - 1))]
          · rw [Int.Icc_eq_finset_map, Finset.sum_map, hcard]
            apply Finset.sum_congr rfl
            intro i hi
            simp [Function.Embedding.trans_apply, add_comm]
          · intro x
            simp [Finset.mem_Icc, Set.mem_Icc]
    _ = ∑ i ∈ Finset.range (n - 1), (F (i + 1) - F i) / Real.sin h := by
          apply Finset.sum_congr rfl
          intro i hi
          have hi_lt : i < n - 1 := Finset.mem_range.mp hi
          have hi_n : i < n := by omega
          have hi1_n : i + 1 < n := by omega
          have hcos_i : Real.cos (((i : ℝ) * Real.pi) / (2 * (n : ℝ))) ≠ 0 :=
            (putnam_2019_b2_cos_pos_index n i hnpos hi_n).ne'
          have hcos_i1 : Real.cos ((((i + 1 : ℕ) : ℝ) * Real.pi) / (2 * (n : ℝ))) ≠ 0 :=
            (putnam_2019_b2_cos_pos_index n (i + 1) hnpos hi1_n).ne'
          have hterm := putnam_2019_b2_trig_term
            (((i : ℝ) * Real.pi) / (2 * (n : ℝ)))
            ((((i + 1 : ℕ) : ℝ) * Real.pi) / (2 * (n : ℝ))) h
            (by
              dsimp [h]
              have hn0 : (n : ℝ) ≠ 0 := by positivity
              field_simp [hn0]
              norm_num [Nat.cast_add, add_comm])
            hcos_i hcos_i1 hsin
          dsimp [F, G, h] at hterm ⊢
          have hsinarg :
              (((2 * ((i : ℤ) + 1) - 1 : ℤ) : ℝ) * Real.pi / (2 * (n : ℝ))) =
                (i : ℝ) * Real.pi / (2 * (n : ℝ)) +
                  ((i + 1 : ℕ) : ℝ) * Real.pi / (2 * (n : ℝ)) := by
            norm_num [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_one,
              Nat.cast_add]
            ring_nf
          rw [hsinarg]
          simpa [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_one,
            Nat.cast_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
            mul_assoc] using hterm
    _ = (∑ i ∈ Finset.range (n - 1), (F (i + 1) - F i)) / Real.sin h := by
          rw [Finset.sum_div]
    _ = (F (n - 1) - F 0) / Real.sin h := by
          rw [Finset.sum_range_sub]
    _ = Real.cos (Real.pi / (2 * (n : ℝ))) ^ 2 /
        Real.sin (Real.pi / (2 * (n : ℝ))) ^ 3 := by
          dsimp [F, h]
          simpa using putnam_2019_b2_final_tan n (le_trans (by norm_num) hn)

private lemma putnam_2019_b2_sin_mul_tendsto :
    Tendsto (fun n : ℕ => Real.sin (Real.pi / (2 * (n : ℝ))) * (n : ℝ)) atTop
      (𝓝 (Real.pi / 2)) := by
  have hangle_tendsto : Tendsto (fun n : ℕ => Real.pi / (2 * (n : ℝ))) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_nhds_zero_nat
    have hmul : Tendsto (fun n : ℕ => (Real.pi / 2) * (n : ℝ)⁻¹) atTop
        (𝓝 ((Real.pi / 2) * 0)) := tendsto_const_nhds.mul hinv
    convert hmul using 1
    · ext n
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring_nf
    · ring_nf
  have hangle_ne : ∀ᶠ n : ℕ in atTop,
      Real.pi / (2 * (n : ℝ)) ∈ ({0}ᶜ : Set ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
    have hp : 0 < Real.pi / (2 * (n : ℝ)) := putnam_2019_b2_angle_pos n hnpos
    simp [hp.ne']
  have hangle_within : Tendsto (fun n : ℕ => Real.pi / (2 * (n : ℝ))) atTop
      (𝓝[≠] (0 : ℝ)) := tendsto_nhdsWithin_iff.mpr ⟨hangle_tendsto, hangle_ne⟩
  have hslope : Tendsto (slope Real.sin 0) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    simpa [Real.cos_zero] using (Real.hasDerivAt_sin 0).tendsto_slope
  have hratio : Tendsto
      (fun n : ℕ => Real.sin (Real.pi / (2 * (n : ℝ))) /
        (Real.pi / (2 * (n : ℝ)))) atTop (𝓝 1) := by
    convert hslope.comp hangle_within using 1
    ext n
    simp [slope, Real.sin_zero, div_eq_mul_inv, mul_comm]
  have hscale : Tendsto (fun n : ℕ => Real.pi / (2 * (n : ℝ)) * (n : ℝ)) atTop
      (𝓝 (Real.pi / 2)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))
    field_simp [hn0]
  have hprod : Tendsto
      (fun n : ℕ =>
        (Real.sin (Real.pi / (2 * (n : ℝ))) /
          (Real.pi / (2 * (n : ℝ)))) *
          (Real.pi / (2 * (n : ℝ)) * (n : ℝ))) atTop
        (𝓝 (Real.pi / 2)) := by
    simpa using hratio.mul hscale
  refine Tendsto.congr' ?_ hprod
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))
  field_simp [hn0]

private lemma putnam_2019_b2_limit :
    Tendsto (fun n : ℕ =>
      (Real.cos (Real.pi / (2 * (n : ℝ))) ^ 2 /
        Real.sin (Real.pi / (2 * (n : ℝ))) ^ 3) / (n : ℝ) ^ 3) atTop
      (𝓝 (8 / Real.pi ^ 3)) := by
  have hangle_tendsto : Tendsto (fun n : ℕ => Real.pi / (2 * (n : ℝ))) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_nhds_zero_nat
    have hmul : Tendsto (fun n : ℕ => (Real.pi / 2) * (n : ℝ)⁻¹) atTop
        (𝓝 ((Real.pi / 2) * 0)) := tendsto_const_nhds.mul hinv
    convert hmul using 1
    · ext n
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring_nf
    · ring_nf
  have hcos : Tendsto (fun n : ℕ => Real.cos (Real.pi / (2 * (n : ℝ))) ^ 2) atTop
      (𝓝 1) := by
    simpa [Real.cos_zero] using (Real.continuous_cos.tendsto 0).comp hangle_tendsto |>.pow 2
  have hden : Tendsto (fun n : ℕ =>
      (Real.sin (Real.pi / (2 * (n : ℝ))) * (n : ℝ)) ^ 3) atTop
      (𝓝 ((Real.pi / 2) ^ 3)) :=
    putnam_2019_b2_sin_mul_tendsto.pow 3
  have hden_ne : (Real.pi / 2) ^ 3 ≠ 0 := by positivity
  have hdiv : Tendsto (fun n : ℕ =>
      Real.cos (Real.pi / (2 * (n : ℝ))) ^ 2 /
        (Real.sin (Real.pi / (2 * (n : ℝ))) * (n : ℝ)) ^ 3) atTop
      (𝓝 (1 / (Real.pi / 2) ^ 3)) :=
    hcos.div hden hden_ne
  have hdiv' : Tendsto (fun n : ℕ =>
      Real.cos (Real.pi / (2 * (n : ℝ))) ^ 2 /
        (Real.sin (Real.pi / (2 * (n : ℝ))) * (n : ℝ)) ^ 3) atTop
      (𝓝 (8 / Real.pi ^ 3)) := by
    convert hdiv using 1
    field_simp [Real.pi_ne_zero]
    ring_nf
  refine Tendsto.congr' ?_ hdiv'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))
  field_simp [hn0]

-- 8/Real.pi^3
/--
For all $n \geq 1$, let
\[
a_n = \sum_{k=1}^{n-1} \frac{\sin \left( \frac{(2k-1)\pi}{2n} \right)}{\cos^2 \left( \frac{(k-1)\pi}{2n} \right) \cos^2 \left( \frac{k\pi}{2n} \right)}.
\]
Determine
\[
\lim_{n \to \infty} \frac{a_n}{n^3}.
\]
-/
theorem putnam_2019_b2
(a : ℕ → ℝ)
(ha : a = fun n : ℕ => ∑ k : Icc (1 : ℤ) (n - 1),
Real.sin ((2*k - 1)*Real.pi/(2*n))/((Real.cos ((k - 1)*Real.pi/(2*n))^2)*(Real.cos (k*Real.pi/(2*n))^2)))
: Tendsto (fun n : ℕ => (a n)/n^3) atTop (𝓝 ((8/Real.pi^3) : ℝ )) := by
  subst a
  refine Tendsto.congr' ?_ putnam_2019_b2_limit
  filter_upwards [eventually_ge_atTop 2] with n hn
  rw [putnam_2019_b2_sum_eq n hn]
