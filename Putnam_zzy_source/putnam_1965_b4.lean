import Mathlib

open EuclideanGeometry Topology Filter Complex

private lemma putnam_1965_b4_sum_Icc_zero_eq_range {α : Type*} [AddCommMonoid α]
    (m : ℕ) (F : ℕ → α) :
    (∑ i ∈ Finset.Icc 0 m, F i) = ∑ i ∈ Finset.range (m + 1), F i := by
  apply Finset.sum_congr
  · ext i
    simp
  · intro i hi
    rfl

private noncomputable abbrev putnam_1965_b4_U (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc 0 (n / 2), (n.choose (2 * i) : ℝ) * x ^ i

private noncomputable abbrev putnam_1965_b4_V (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc 0 ((n - 1) / 2), (n.choose (2 * i + 1) : ℝ) * x ^ i

private lemma putnam_1965_b4_U_even_rec (m : ℕ) (hm : 0 < m) (x : ℝ) :
    putnam_1965_b4_U (2 * m + 1) x =
      putnam_1965_b4_U (2 * m) x + x * putnam_1965_b4_V (2 * m) x := by
  dsimp [putnam_1965_b4_U, putnam_1965_b4_V]
  have h1 : (2 * m + 1) / 2 = m := by omega
  have h2 : (2 * m) / 2 = m := by omega
  have h3 : (2 * m - 1) / 2 = m - 1 := by omega
  rw [h1, h2, h3]
  rw [putnam_1965_b4_sum_Icc_zero_eq_range m,
    putnam_1965_b4_sum_Icc_zero_eq_range m,
    putnam_1965_b4_sum_Icc_zero_eq_range (m - 1)]
  rw [Nat.sub_add_cancel hm]
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [Nat.mul_zero, Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one]
  rw [Finset.mul_sum]
  have hsum :
      (∑ k ∈ Finset.range m, ↑((2 * m + 1).choose (2 * (k + 1))) * x ^ (k + 1)) =
        (∑ k ∈ Finset.range m, ↑((2 * m).choose (2 * (k + 1))) * x ^ (k + 1)) +
          (∑ i ∈ Finset.range m, x * (↑((2 * m).choose (2 * i + 1)) * x ^ i)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hchoose :
        (2 * m + 1).choose (2 * (i + 1)) =
          (2 * m).choose (2 * i + 1) + (2 * m).choose (2 * (i + 1)) := by
      simpa [Nat.succ_eq_add_one, add_comm, add_left_comm, add_assoc, two_mul]
        using Nat.choose_succ_succ (2 * m) (2 * i + 1)
    rw [hchoose]
    norm_num
    ring
  linear_combination hsum

private lemma putnam_1965_b4_U_odd_rec (m : ℕ) (x : ℝ) :
    putnam_1965_b4_U (2 * m + 2) x =
      putnam_1965_b4_U (2 * m + 1) x + x * putnam_1965_b4_V (2 * m + 1) x := by
  dsimp [putnam_1965_b4_U, putnam_1965_b4_V]
  have h1 : (2 * m + 2) / 2 = m + 1 := by omega
  have h2 : (2 * m + 1) / 2 = m := by omega
  have h3 : (2 * m) / 2 = m := by omega
  rw [h1, h2, h3]
  rw [putnam_1965_b4_sum_Icc_zero_eq_range (m + 1),
    putnam_1965_b4_sum_Icc_zero_eq_range m,
    putnam_1965_b4_sum_Icc_zero_eq_range m]
  rw [Finset.sum_range_succ']
  simp only [Nat.mul_zero, Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one]
  rw [Finset.mul_sum]
  have htail :
      (∑ k ∈ Finset.range (m + 1),
          ↑((2 * m + 1).choose (2 * (k + 1))) * x ^ (k + 1)) =
        ∑ k ∈ Finset.range m,
          ↑((2 * m + 1).choose (2 * (k + 1))) * x ^ (k + 1) := by
    rw [Finset.sum_range_succ]
    have hz : (2 * m + 1).choose (2 * (m + 1)) = 0 := by
      apply Nat.choose_eq_zero_of_lt
      omega
    rw [hz]
    simp
  rw [Finset.sum_range_succ' (fun k => ↑((2 * m + 1).choose (2 * k)) * x ^ k) m]
  simp only [Nat.mul_zero, Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one]
  rw [← htail]
  have hsum :
      (∑ k ∈ Finset.range (m + 1),
          ↑((2 * m + 2).choose (2 * (k + 1))) * x ^ (k + 1)) =
        (∑ k ∈ Finset.range (m + 1),
          ↑((2 * m + 1).choose (2 * (k + 1))) * x ^ (k + 1)) +
          (∑ i ∈ Finset.range (m + 1),
            x * (↑((2 * m + 1).choose (2 * i + 1)) * x ^ i)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hchoose :
        (2 * m + 2).choose (2 * (i + 1)) =
          (2 * m + 1).choose (2 * i + 1) + (2 * m + 1).choose (2 * (i + 1)) := by
      simpa [Nat.succ_eq_add_one, add_comm, add_left_comm, add_assoc, two_mul]
        using Nat.choose_succ_succ (2 * m + 1) (2 * i + 1)
    rw [hchoose]
    norm_num
    ring
  linear_combination hsum

private lemma putnam_1965_b4_V_even_rec (m : ℕ) (hm : 0 < m) (x : ℝ) :
    putnam_1965_b4_V (2 * m + 1) x =
      putnam_1965_b4_U (2 * m) x + putnam_1965_b4_V (2 * m) x := by
  dsimp [putnam_1965_b4_U, putnam_1965_b4_V]
  have h1 : (2 * m) / 2 = m := by omega
  have h2 : (2 * m - 1) / 2 = m - 1 := by omega
  rw [h1, h2]
  rw [putnam_1965_b4_sum_Icc_zero_eq_range m,
    putnam_1965_b4_sum_Icc_zero_eq_range m,
    putnam_1965_b4_sum_Icc_zero_eq_range (m - 1)]
  rw [Nat.sub_add_cancel hm]
  have htail :
      (∑ k ∈ Finset.range (m + 1), ↑((2 * m).choose (2 * k + 1)) * x ^ k) =
        ∑ k ∈ Finset.range m, ↑((2 * m).choose (2 * k + 1)) * x ^ k := by
    rw [Finset.sum_range_succ]
    have hz : (2 * m).choose (2 * m + 1) = 0 := by
      apply Nat.choose_eq_zero_of_lt
      omega
    rw [hz]
    simp
  rw [← htail]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hchoose :
      (2 * m + 1).choose (2 * i + 1) =
        (2 * m).choose (2 * i) + (2 * m).choose (2 * i + 1) := by
    simpa [Nat.succ_eq_add_one, add_comm, add_left_comm, add_assoc, two_mul]
      using Nat.choose_succ_succ (2 * m) (2 * i)
  rw [hchoose]
  norm_num
  ring

private lemma putnam_1965_b4_V_odd_rec (m : ℕ) (x : ℝ) :
    putnam_1965_b4_V (2 * m + 2) x =
      putnam_1965_b4_U (2 * m + 1) x + putnam_1965_b4_V (2 * m + 1) x := by
  dsimp [putnam_1965_b4_U, putnam_1965_b4_V]
  have h2 : (2 * m + 1) / 2 = m := by omega
  have h3 : (2 * m) / 2 = m := by omega
  rw [h2, h3]
  rw [putnam_1965_b4_sum_Icc_zero_eq_range m,
    putnam_1965_b4_sum_Icc_zero_eq_range m,
    putnam_1965_b4_sum_Icc_zero_eq_range m]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hchoose :
      (2 * m + 2).choose (2 * i + 1) =
        (2 * m + 1).choose (2 * i) + (2 * m + 1).choose (2 * i + 1) := by
    simpa [Nat.succ_eq_add_one, add_comm, add_left_comm, add_assoc, two_mul]
      using Nat.choose_succ_succ (2 * m + 1) (2 * i)
  rw [hchoose]
  norm_num
  ring

private lemma putnam_1965_b4_U_succ (n : ℕ) (x : ℝ) :
    putnam_1965_b4_U (n + 1) x =
      putnam_1965_b4_U n x + x * putnam_1965_b4_V n x := by
  by_cases hn : n = 0
  · subst n
    norm_num [putnam_1965_b4_U, putnam_1965_b4_V]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · subst n
      have hmpos : 0 < m := by omega
      simpa [two_mul, add_comm, add_left_comm, add_assoc]
        using putnam_1965_b4_U_even_rec m hmpos x
    · subst n
      simpa [two_mul, add_comm, add_left_comm, add_assoc]
        using putnam_1965_b4_U_odd_rec m x

private lemma putnam_1965_b4_V_succ (n : ℕ) (x : ℝ) :
    putnam_1965_b4_V (n + 1) x =
      putnam_1965_b4_U n x + putnam_1965_b4_V n x := by
  by_cases hn : n = 0
  · subst n
    norm_num [putnam_1965_b4_U, putnam_1965_b4_V]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · subst n
      have hmpos : 0 < m := by omega
      simpa [two_mul, add_comm, add_left_comm, add_assoc]
        using putnam_1965_b4_V_even_rec m hmpos x
    · subst n
      simpa [two_mul, add_comm, add_left_comm, add_assoc]
        using putnam_1965_b4_V_odd_rec m x

private lemma putnam_1965_b4_V_pos (n : ℕ) (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    0 < putnam_1965_b4_V n x := by
  dsimp [putnam_1965_b4_V]
  refine Finset.sum_pos' ?nonneg ?pos
  · intro i hi
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx _)
  · refine ⟨0, ?_, ?_⟩
    · simp
    · simp [Nat.choose_one_right, hn]

private lemma putnam_1965_b4_U_zero (n : ℕ) :
    putnam_1965_b4_U n 0 = 1 := by
  dsimp [putnam_1965_b4_U]
  rw [Finset.sum_eq_single (a := 0)]
  · simp
  · intro b hb hb0
    simp [zero_pow hb0]
  · intro hnot
    simp at hnot

private lemma putnam_1965_b4_V_zero (n : ℕ) :
    putnam_1965_b4_V n 0 = n := by
  dsimp [putnam_1965_b4_V]
  rw [Finset.sum_eq_single (a := 0)]
  · simp [Nat.choose_one_right]
  · intro b hb hb0
    simp [zero_pow hb0]
  · intro hnot
    simp at hnot

private lemma putnam_1965_b4_ratio_formula {a U V A B : ℝ} (ha : a ≠ 0) (hV : V ≠ 0)
    (hp : U + a * V = A) (hm : U - a * V = B) :
    U / V = a * ((A + B) / (A - B)) := by
  have hU : 2 * U = A + B := by linear_combination hp + hm
  have hW : 2 * a * V = A - B := by linear_combination hp - hm
  have hAB : A - B ≠ 0 := by
    rw [← hW]
    exact mul_ne_zero (mul_ne_zero two_ne_zero ha) hV
  field_simp [hV, hAB]
  rw [← hU, ← hW]
  ring

private lemma putnam_1965_b4_U_add_mul_V (n : ℕ) (a x : ℝ) (hx : x = a ^ 2) :
    putnam_1965_b4_U n x + a * putnam_1965_b4_V n x = (1 + a) ^ n := by
  subst x
  induction n with
  | zero =>
      norm_num [putnam_1965_b4_U, putnam_1965_b4_V]
  | succ n ih =>
      rw [putnam_1965_b4_U_succ, putnam_1965_b4_V_succ]
      calc
        putnam_1965_b4_U n (a ^ 2) + a ^ 2 * putnam_1965_b4_V n (a ^ 2) +
            a * (putnam_1965_b4_U n (a ^ 2) + putnam_1965_b4_V n (a ^ 2)) =
            (1 + a) * (putnam_1965_b4_U n (a ^ 2) + a * putnam_1965_b4_V n (a ^ 2)) := by
          ring
        _ = (1 + a) ^ (n + 1) := by
          rw [ih, pow_succ]
          ring

private lemma putnam_1965_b4_U_sub_mul_V (n : ℕ) (a x : ℝ) (hx : x = a ^ 2) :
    putnam_1965_b4_U n x - a * putnam_1965_b4_V n x = (1 - a) ^ n := by
  subst x
  induction n with
  | zero =>
      norm_num [putnam_1965_b4_U, putnam_1965_b4_V]
  | succ n ih =>
      rw [putnam_1965_b4_U_succ, putnam_1965_b4_V_succ]
      calc
        putnam_1965_b4_U n (a ^ 2) + a ^ 2 * putnam_1965_b4_V n (a ^ 2) -
            a * (putnam_1965_b4_U n (a ^ 2) + putnam_1965_b4_V n (a ^ 2)) =
            (1 - a) * (putnam_1965_b4_U n (a ^ 2) - a * putnam_1965_b4_V n (a ^ 2)) := by
          ring
        _ = (1 - a) ^ (n + 1) := by
          rw [ih, pow_succ]
          ring

private lemma putnam_1965_b4_sq_sub (n : ℕ) (x : ℝ) :
    putnam_1965_b4_U n x ^ 2 - x * putnam_1965_b4_V n x ^ 2 = (1 - x) ^ n := by
  induction n with
  | zero =>
      norm_num [putnam_1965_b4_U, putnam_1965_b4_V]
  | succ n ih =>
      rw [putnam_1965_b4_U_succ, putnam_1965_b4_V_succ]
      calc
        (putnam_1965_b4_U n x + x * putnam_1965_b4_V n x) ^ 2 -
            x * (putnam_1965_b4_U n x + putnam_1965_b4_V n x) ^ 2 =
            (1 - x) * (putnam_1965_b4_U n x ^ 2 - x * putnam_1965_b4_V n x ^ 2) := by
          ring
        _ = (1 - x) ^ (n + 1) := by
          rw [ih, pow_succ]
          ring

private lemma putnam_1965_b4_hu_succ
    (u v : ℕ → ℝ → ℝ)
    (hu : ∀ n > 0, ∀ x, u n x = putnam_1965_b4_U n x)
    (hv : ∀ n > 0, ∀ x, v n x = putnam_1965_b4_V n x)
    (n : ℕ) (hn : 0 < n) (x : ℝ) :
    u (n + 1) x = u n x + x * v n x := by
  rw [hu (n + 1) (Nat.succ_pos n) x, hu n hn x, hv n hn x,
    putnam_1965_b4_U_succ]

private lemma putnam_1965_b4_hv_succ
    (u v : ℕ → ℝ → ℝ)
    (hu : ∀ n > 0, ∀ x, u n x = putnam_1965_b4_U n x)
    (hv : ∀ n > 0, ∀ x, v n x = putnam_1965_b4_V n x)
    (n : ℕ) (hn : 0 < n) (x : ℝ) :
    v (n + 1) x = u n x + v n x := by
  rw [hv (n + 1) (Nat.succ_pos n) x, hu n hn x, hv n hn x,
    putnam_1965_b4_V_succ]

private lemma putnam_1965_b4_f_rec
    (f u v : ℕ → ℝ → ℝ)
    (hu : ∀ n > 0, ∀ x, u n x = putnam_1965_b4_U n x)
    (hv : ∀ n > 0, ∀ x, v n x = putnam_1965_b4_V n x)
    (hf : ∀ n > 0, ∀ x, f n x = u n x / v n x)
    (n : ℕ) (hn : 0 < n) (x : ℝ)
    (hvn : v n x ≠ 0) (hvs : v (n + 1) x ≠ 0) :
    f (n + 1) x = (f n x + x) / (f n x + 1) := by
  have hu_s := putnam_1965_b4_hu_succ u v hu hv n hn x
  have hv_s := putnam_1965_b4_hv_succ u v hu hv n hn x
  have hsum : u n x + v n x ≠ 0 := by
    intro hzero
    apply hvs
    rwa [hv_s]
  rw [hf (n + 1) (Nat.succ_pos n) x, hf n hn x, hu_s, hv_s]
  field_simp [hvn, hsum]

private lemma putnam_1965_b4_f_mul_rec
    (f u v : ℕ → ℝ → ℝ)
    (hu : ∀ n > 0, ∀ x, u n x = putnam_1965_b4_U n x)
    (hv : ∀ n > 0, ∀ x, v n x = putnam_1965_b4_V n x)
    (hf : ∀ n > 0, ∀ x, f n x = u n x / v n x)
    (n : ℕ) (hn : 0 < n) (x : ℝ)
    (hvn : v n x ≠ 0) (hvs : v (n + 1) x ≠ 0) :
    f (n + 1) x * (f n x + 1) = f n x + x := by
  have hrec := putnam_1965_b4_f_rec f u v hu hv hf n hn x hvn hvs
  have hu_s := putnam_1965_b4_hu_succ u v hu hv n hn x
  have hv_s := putnam_1965_b4_hv_succ u v hu hv n hn x
  have hsum : u n x + v n x ≠ 0 := by
    intro hzero
    apply hvs
    rwa [hv_s]
  have hq : f n x + 1 ≠ 0 := by
    rw [hf n hn x]
    have hquot : u n x / v n x + 1 = (u n x + v n x) / v n x := by
      field_simp [hvn]
    rw [hquot]
    exact div_ne_zero hsum hvn
  rw [hrec]
  field_simp [hq]

private lemma putnam_1965_b4_tendsto_nonneg
    (f u v : ℕ → ℝ → ℝ)
    (hu : ∀ n > 0, ∀ x, u n x = putnam_1965_b4_U n x)
    (hv : ∀ n > 0, ∀ x, v n x = putnam_1965_b4_V n x)
    (hf : ∀ n > 0, ∀ x, f n x = u n x / v n x)
    {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n ↦ f n x) atTop (𝓝 (Real.sqrt x)) := by
  rcases lt_or_eq_of_le hx with hxpos | rfl
  · let a := Real.sqrt x
    let r := (1 - a) / (1 + a)
    have ha_pos : 0 < a := Real.sqrt_pos_of_pos hxpos
    have ha_ne : a ≠ 0 := ne_of_gt ha_pos
    have hx_sq : x = a ^ 2 := by
      dsimp [a]
      rw [Real.sq_sqrt hx]
    have hrabs : |r| < 1 := by
      dsimp [r]
      rw [abs_div, abs_of_pos (by linarith : 0 < 1 + a)]
      rw [div_lt_one (by linarith : 0 < 1 + a)]
      exact abs_lt.2 ⟨by linarith, by linarith⟩
    have heq :
        (fun n : ℕ ↦ f n x) =ᶠ[atTop]
          (fun n : ℕ ↦ a * ((1 + r ^ n) / (1 - r ^ n))) := by
      filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
      have hn : 0 < n := by omega
      have hVpos : 0 < putnam_1965_b4_V n x := putnam_1965_b4_V_pos n hn hx
      have hratio :
          putnam_1965_b4_U n x / putnam_1965_b4_V n x =
            a * (((1 + a) ^ n + (1 - a) ^ n) / ((1 + a) ^ n - (1 - a) ^ n)) := by
        exact putnam_1965_b4_ratio_formula ha_ne (ne_of_gt hVpos)
          (putnam_1965_b4_U_add_mul_V n a x hx_sq)
          (putnam_1965_b4_U_sub_mul_V n a x hx_sq)
      have hconv :
          (((1 + a) ^ n + (1 - a) ^ n) / ((1 + a) ^ n - (1 - a) ^ n)) =
            (1 + r ^ n) / (1 - r ^ n) := by
        dsimp [r]
        have hA0 : (1 + a) ^ n ≠ 0 := by positivity
        rw [div_pow]
        field_simp [hA0]
      rw [hf n hn x, hu n hn x, hv n hn x, hratio, hconv]
    have hpow : Tendsto (fun n : ℕ ↦ r ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_abs_lt_one hrabs
    have hfrac :
        Tendsto (fun n : ℕ ↦ (1 + r ^ n) / (1 - r ^ n)) atTop
          (𝓝 ((1 + 0) / (1 - 0 : ℝ))) := by
      exact (tendsto_const_nhds.add hpow).div (tendsto_const_nhds.sub hpow) (by norm_num)
    have hgeom :
        Tendsto (fun n : ℕ ↦ a * ((1 + r ^ n) / (1 - r ^ n))) atTop (𝓝 a) := by
      have hmul :
          Tendsto (fun n : ℕ ↦ a * ((1 + r ^ n) / (1 - r ^ n))) atTop
            (𝓝 (a * ((1 + 0) / (1 - 0 : ℝ)))) := by
        exact tendsto_const_nhds.mul hfrac
      simpa using hmul
    exact Filter.Tendsto.congr' heq.symm hgeom
  · have heq :
        (fun n : ℕ ↦ f n 0) =ᶠ[atTop] (fun n : ℕ ↦ 1 / (n : ℝ)) := by
      filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
      have hn : 0 < n := by omega
      rw [hf n hn 0, hu n hn 0, hv n hn 0,
        putnam_1965_b4_U_zero, putnam_1965_b4_V_zero]
    have hlim : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    simpa [Real.sqrt_zero] using Filter.Tendsto.congr' heq.symm hlim

private lemma putnam_1965_b4_not_tendsto_neg
    (f u v : ℕ → ℝ → ℝ)
    (hu : ∀ n > 0, ∀ x, u n x = putnam_1965_b4_U n x)
    (hv : ∀ n > 0, ∀ x, v n x = putnam_1965_b4_V n x)
    (hf : ∀ n > 0, ∀ x, f n x = u n x / v n x)
    {x l : ℝ} (hx : x < 0) :
    ¬ Tendsto (fun n ↦ f n x) atTop (𝓝 l) := by
  intro hlim
  by_cases hfreq : ∃ᶠ n in atTop, v n x = 0
  · have hfreq_pos : ∃ᶠ n in atTop, v n x = 0 ∧ 1 ≤ n :=
      hfreq.and_eventually (Filter.eventually_ge_atTop (1 : ℕ))
    have hfreq0 : ∃ᶠ n in atTop, f n x = (fun _ : ℕ ↦ (0 : ℝ)) n := by
      refine hfreq_pos.mono ?_
      intro n hn
      have hnpos : 0 < n := by omega
      rw [hf n hnpos x, hn.1, div_zero]
    have hfreq1 :
        ∃ᶠ n in atTop, (fun n : ℕ ↦ f (n + 1) x) n = (fun _ : ℕ ↦ (1 : ℝ)) n := by
      refine hfreq_pos.mono ?_
      intro n hn
      have hnpos : 0 < n := by omega
      have hvzero : v n x = 0 := hn.1
      have hu_s := putnam_1965_b4_hu_succ u v hu hv n hnpos x
      have hv_s := putnam_1965_b4_hv_succ u v hu hv n hnpos x
      have hune : u n x ≠ 0 := by
        intro huzero
        have hUzero : putnam_1965_b4_U n x = 0 := by
          rw [← hu n hnpos x, huzero]
        have hVzero : putnam_1965_b4_V n x = 0 := by
          rw [← hv n hnpos x, hvzero]
        have hpowpos : 0 < (1 - x) ^ n := pow_pos (by linarith : 0 < 1 - x) n
        have hinv := putnam_1965_b4_sq_sub n x
        have hpowzero : (1 - x) ^ n = 0 := by
          rw [← hinv, hUzero, hVzero]
          ring
        exact (ne_of_gt hpowpos) hpowzero
      change f (n + 1) x = 1
      rw [hf (n + 1) (Nat.succ_pos n) x, hu_s, hv_s, hvzero]
      field_simp [hune]
      ring
    have hl0 : l = 0 :=
      tendsto_nhds_unique_of_frequently_eq hlim tendsto_const_nhds hfreq0
    have hlim_shift : Tendsto (fun n : ℕ ↦ f (n + 1) x) atTop (𝓝 l) :=
      hlim.comp (Filter.tendsto_add_atTop_nat 1)
    have hl1 : l = 1 :=
      tendsto_nhds_unique_of_frequently_eq hlim_shift tendsto_const_nhds hfreq1
    nlinarith
  · have hv_event : ∀ᶠ n in atTop, v n x ≠ 0 := (not_frequently.mp hfreq)
    have hv_s_event : ∀ᶠ n in atTop, v (n + 1) x ≠ 0 :=
      (Filter.tendsto_add_atTop_nat 1).eventually hv_event
    have hrec_event :
        (fun n : ℕ ↦ f (n + 1) x * (f n x + 1)) =ᶠ[atTop]
          (fun n : ℕ ↦ f n x + x) := by
      filter_upwards [Filter.eventually_ge_atTop (1 : ℕ), hv_event, hv_s_event] with n hn hvn hvs
      have hnpos : 0 < n := by omega
      exact putnam_1965_b4_f_mul_rec f u v hu hv hf n hnpos x hvn hvs
    have hlim_shift : Tendsto (fun n : ℕ ↦ f (n + 1) x) atTop (𝓝 l) :=
      hlim.comp (Filter.tendsto_add_atTop_nat 1)
    have hleft :
        Tendsto (fun n : ℕ ↦ f (n + 1) x * (f n x + 1)) atTop
          (𝓝 (l * (l + 1))) := by
      exact hlim_shift.mul (hlim.add tendsto_const_nhds)
    have hright : Tendsto (fun n : ℕ ↦ f n x + x) atTop (𝓝 (l + x)) :=
      hlim.add tendsto_const_nhds
    have hlim_eq : l * (l + 1) = l + x :=
      tendsto_nhds_unique (Filter.Tendsto.congr' hrec_event hleft) hright
    have hx_nonneg : 0 ≤ x := by
      have hsquare : l ^ 2 = x := by nlinarith
      rw [← hsquare]
      exact sq_nonneg l
    linarith

noncomputable abbrev putnam_1965_b4_solution : ((((ℝ → ℝ) → (ℝ → ℝ)) × ((ℝ → ℝ) → (ℝ → ℝ))) × ((Set ℝ) × (ℝ → ℝ))) :=
  (((fun F x => (F x + x) / (F x + 1)), (fun _ _ => 1)), ({0} ∪ Set.Ioi 0, Real.sqrt))

/--
Let $$f(x, n) = \frac{{n \choose 0} + {n \choose 2}x + {n \choose 4}x^2 + \cdots}{{n \choose 1} + {n \choose 3}x + {n \choose 5}x^2 + \cdots}$$ for all real numbers $x$ and positive integers $n$. Express $f(x, n+1)$ as a rational function involving $f(x, n)$ and $x$, and find $\lim_{n \to \infty} f(x, n)$ for all $x$ for which this limit converges.
-/
theorem putnam_1965_b4
    (f u v : ℕ → ℝ → ℝ)
    (hu : ∀ n > 0, ∀ x, u n x = ∑ i ∈ Finset.Icc 0 (n / 2), (n.choose (2 * i)) * x ^ i)
    (hv : ∀ n > 0, ∀ x, v n x = ∑ i ∈ Finset.Icc 0 ((n - 1) / 2), (n.choose (2 * i + 1)) * x ^ i)
    (hf : ∀ n > 0, ∀ x, f n x = u n x / v n x)
    (n : ℕ)
    (hn : 0 < n) :
    let ⟨⟨p, q⟩, ⟨s, g⟩⟩ := putnam_1965_b4_solution
    (∀ x, v n x ≠ 0 → v (n + 1) x ≠ 0 → q (f n) x ≠ 0 → f (n + 1) x = p (f n) x / q (f n) x) ∧
    s = {x | ∃ l, Tendsto (fun n ↦ f n x) atTop (𝓝 l)} ∧
    ∀ x ∈ s, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)) :=
  by
  dsimp [putnam_1965_b4_solution]
  constructor
  · intro x hvn hvs _hq
    simpa [add_comm, add_left_comm, add_assoc] using
      putnam_1965_b4_f_rec f u v hu hv hf n hn x hvn hvs
  · constructor
    · apply Set.ext
      intro x
      constructor
      · intro hx
        have hx0 : 0 ≤ x := by
          rcases hx with hxzero | hxpos
          · have hxeq : x = 0 := by simpa using hxzero
            simp [hxeq]
          · exact le_of_lt hxpos
        exact ⟨Real.sqrt x, putnam_1965_b4_tendsto_nonneg f u v hu hv hf hx0⟩
      · intro hx
        have hx0 : 0 ≤ x := by
          by_contra hxnon
          rcases hx with ⟨l, hlim⟩
          exact (putnam_1965_b4_not_tendsto_neg f u v hu hv hf (lt_of_not_ge hxnon)) hlim
        rcases lt_or_eq_of_le hx0 with hxpos | hzero
        · exact Or.inr hxpos
        · exact Or.inl (by simp [hzero])
    · intro x hx
      have hx0 : 0 ≤ x := by
        rcases hx with hxzero | hxpos
        · have hxeq : x = 0 := by simpa using hxzero
          simp [hxeq]
        · exact le_of_lt hxpos
      exact putnam_1965_b4_tendsto_nonneg f u v hu hv hf hx0
