import Mathlib

open Topology Filter Real

noncomputable abbrev putnam_2017_b4_solution : ℝ := (Real.log 4 / 2) * Real.log 2

namespace Putnam2017B4

noncomputable def zterm (s : ℝ) (n : ℕ) : ℝ := 1 / (n : ℝ) ^ s

noncomputable def T (k : ℕ) (s : ℝ) : ℝ :=
  3 * zterm s (4 * k + 2) - zterm s (4 * k + 3) -
    zterm s (4 * k + 4) - zterm s (4 * k + 5)

noncomputable def logTerm (k : ℕ) (s : ℝ) : ℝ :=
  3 * log ((4 * k + 2 : ℕ) : ℝ) * zterm s (4 * k + 2) -
    log ((4 * k + 3 : ℕ) : ℝ) * zterm s (4 * k + 3) -
    log ((4 * k + 4 : ℕ) : ℝ) * zterm s (4 * k + 4) -
    log ((4 * k + 5 : ℕ) : ℝ) * zterm s (4 * k + 5)

noncomputable def phi (u x : ℝ) : ℝ := log x * x ^ (-u)

noncomputable def rho (u x : ℝ) : ℝ := x ^ (-u)

noncomputable def A (s : ℝ) : ℝ := 2 * (2 : ℝ) ^ (-s) - 1

noncomputable def Q (s : ℝ) (k : ℕ) : ℝ := (T k 1 - T k s) / (s - 1)

lemma zterm_zero {s : ℝ} (hs : 0 < s) : zterm s 0 = 0 := by
  simp [zterm, hs.ne']

lemma zterm_one (s : ℝ) : zterm s 1 = 1 := by
  simp [zterm]

lemma zterm_eq_rpow_neg {s : ℝ} {n : ℕ} (_hn : n ≠ 0) :
    zterm s n = ((n : ℝ) ^ (-s)) := by
  unfold zterm
  rw [Real.rpow_neg (Nat.cast_nonneg n)]
  rw [one_div]

lemma hasDerivAt_zterm {n : ℕ} (hn : n ≠ 0) (s : ℝ) :
    HasDerivAt (fun u : ℝ => zterm u n) (-(log (n : ℝ)) * zterm s n) s := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hneg : HasDerivAt (fun u : ℝ => -u) (-1) s := (hasDerivAt_id s).neg
  have h := hneg.const_rpow hnpos
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Eventually.of_forall fun u => zterm_eq_rpow_neg (s := u) hn
  · rw [zterm_eq_rpow_neg (s := s) hn]
    ring

lemma hasDerivAt_T (k : ℕ) (s : ℝ) :
    HasDerivAt (fun u : ℝ => T k u) (-(logTerm k s)) s := by
  have h2 : (4 * k + 2 : ℕ) ≠ 0 := by omega
  have h3 : (4 * k + 3 : ℕ) ≠ 0 := by omega
  have h4 : (4 * k + 4 : ℕ) ≠ 0 := by omega
  have h5 : (4 * k + 5 : ℕ) ≠ 0 := by omega
  unfold T logTerm
  convert
    ((((hasDerivAt_zterm h2 s).const_mul 3).sub (hasDerivAt_zterm h3 s)).sub
      (hasDerivAt_zterm h4 s)).sub (hasDerivAt_zterm h5 s) using 1
  ring

lemma zterm_two_mul {s : ℝ} (hs : 0 < s) (n : ℕ) :
    zterm s (2 * n) = (2 : ℝ) ^ (-s) * zterm s n := by
  unfold zterm
  by_cases hn : n = 0
  · subst n
    simp [hs.ne']
  · rw [Nat.cast_mul]
    norm_num only [Nat.cast_ofNat]
    rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2) (Nat.cast_nonneg n)]
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2)]
    field_simp [show (n : ℝ) ^ s ≠ 0 by positivity]

lemma tsum_zterm_even {s : ℝ} (hs : 0 < s) :
    (∑' n : ℕ, zterm s (2 * n)) = (2 : ℝ) ^ (-s) * ∑' n : ℕ, zterm s n := by
  simp_rw [zterm_two_mul hs]
  rw [tsum_mul_left]

lemma zterm_summable {s : ℝ} (hs : 1 < s) : Summable fun n : ℕ => zterm s n := by
  simpa [zterm] using (Real.summable_one_div_nat_rpow.mpr hs : Summable fun n : ℕ => 1 / (n : ℝ) ^ s)

lemma zterm_comp_summable {s : ℝ} (hs : 1 < s) {a b : ℕ} (hb : b ≠ 0) :
    Summable fun n : ℕ => zterm s (a + b * n) := by
  exact (zterm_summable hs).comp_injective (by
    intro m n h
    have hbpos : 0 < b := Nat.pos_of_ne_zero hb
    exact Nat.mul_left_cancel hbpos (Nat.add_left_cancel h))

lemma tsum_zterm_four_two {s : ℝ} (hs : 1 < s) :
    (∑' n : ℕ, zterm s (4 * n + 2)) =
      (2 : ℝ) ^ (-s) * ((∑' n : ℕ, zterm s n) - (2 : ℝ) ^ (-s) * ∑' n : ℕ, zterm s n) := by
  have hs0 : 0 < s := zero_lt_one.trans hs
  have hsum := zterm_summable hs
  have heven : Summable fun n : ℕ => zterm s (2 * n) :=
    hsum.comp_injective (mul_right_injective₀ (two_ne_zero' ℕ))
  have hodd : Summable fun n : ℕ => zterm s (2 * n + 1) :=
    hsum.comp_injective ((add_left_injective 1).comp (mul_right_injective₀ (two_ne_zero' ℕ)))
  have hsplit :
      (∑' n : ℕ, zterm s (2 * n + 1)) =
        (∑' n : ℕ, zterm s n) - (∑' n : ℕ, zterm s (2 * n)) := by
    have h := tsum_even_add_odd (f := fun n : ℕ => zterm s n) heven hodd
    linarith
  calc
    (∑' n : ℕ, zterm s (4 * n + 2))
        = (∑' n : ℕ, zterm s (2 * (2 * n + 1))) := by
          congr 1 with n
          rw [show 2 * (2 * n + 1) = 4 * n + 2 by omega]
    _ = (∑' n : ℕ, (2 : ℝ) ^ (-s) * zterm s (2 * n + 1)) := by
          congr 1 with n
          rw [zterm_two_mul hs0 (2 * n + 1)]
    _ = (2 : ℝ) ^ (-s) * (∑' n : ℕ, zterm s (2 * n + 1)) := by
          rw [tsum_mul_left]
    _ = (2 : ℝ) ^ (-s) * ((∑' n : ℕ, zterm s n) - (2 : ℝ) ^ (-s) * ∑' n : ℕ, zterm s n) := by
          rw [hsplit, tsum_zterm_even hs0]

lemma tsum_zterm_residue_four (f : ℕ → ℝ) (hf : Summable f) :
    (∑' n : ℕ, f n) = (∑' m : ℕ, f (0 + 4 * m)) + (∑' m : ℕ, f (1 + 4 * m)) +
      (∑' m : ℕ, f (2 + 4 * m)) + (∑' m : ℕ, f (3 + 4 * m)) := by
  rw [Nat.sumByResidueClasses hf 4]
  rw [← Equiv.sum_comp (ZMod.finEquiv 4).toEquiv
    (fun j : ZMod 4 => ∑' m : ℕ, f (j.val + 4 * m))]
  rw [Fin.sum_univ_four]
  change (∑' m : ℕ, f (0 + 4 * m)) + (∑' m : ℕ, f (1 + 4 * m)) +
      (∑' m : ℕ, f (2 + 4 * m)) + (∑' m : ℕ, f (3 + 4 * m)) = _
  rfl

lemma tsum_zterm_tail_two {s : ℝ} (hs : 1 < s) :
    (∑' n : ℕ, zterm s (n + 2)) = (∑' n : ℕ, zterm s n) - 1 := by
  have hsum := zterm_summable hs
  have h := hsum.sum_add_tsum_nat_add 2
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at h
  simp [zterm_zero (zero_lt_one.trans hs), zterm_one s] at h
  linarith

lemma tsum_T_eq {s : ℝ} (hs : 1 < s) :
    (∑' k : ℕ, T k s) =
      1 - (2 * (2 : ℝ) ^ (-s) - 1) ^ 2 * (∑' n : ℕ, zterm s n) := by
  have hsum_tail : Summable fun n : ℕ => zterm s (n + 2) := by
    simpa [Nat.add_comm] using (summable_nat_add_iff (G := ℝ) (f := fun n : ℕ => zterm s n) 2).2 (zterm_summable hs)
  have hblock := tsum_zterm_residue_four (fun n : ℕ => zterm s (n + 2)) hsum_tail
  have hblock' :
      (∑' k : ℕ, (zterm s (4 * k + 2) + zterm s (4 * k + 3) +
        zterm s (4 * k + 4) + zterm s (4 * k + 5))) =
        (∑' n : ℕ, zterm s (n + 2)) := by
    have h2 : Summable fun k : ℕ => zterm s (4 * k + 2) := by
      simpa [Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm] using
        zterm_comp_summable hs (a := 2) (b := 4) (by norm_num)
    have h3 : Summable fun k : ℕ => zterm s (4 * k + 3) := by
      simpa [Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm] using
        zterm_comp_summable hs (a := 3) (b := 4) (by norm_num)
    have h4 : Summable fun k : ℕ => zterm s (4 * k + 4) := by
      simpa [Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm] using
        zterm_comp_summable hs (a := 4) (b := 4) (by norm_num)
    have h5 : Summable fun k : ℕ => zterm s (4 * k + 5) := by
      simpa [Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm] using
        zterm_comp_summable hs (a := 5) (b := 4) (by norm_num)
    rw [hblock]
    rw [((h2.add h3).add h4).tsum_add h5, (h2.add h3).tsum_add h4, h2.tsum_add h3]
    have hA :
        (∑' b : ℕ, zterm s (4 * b + 2)) =
          (∑' m : ℕ, (fun n => zterm s (n + 2)) (0 + 4 * m)) := by
      apply tsum_congr
      intro m
      simp only
      congr 1
      omega
    have hB :
        (∑' b : ℕ, zterm s (4 * b + 3)) =
          (∑' m : ℕ, (fun n => zterm s (n + 2)) (1 + 4 * m)) := by
      apply tsum_congr
      intro m
      simp only
      congr 1
      omega
    have hC :
        (∑' b : ℕ, zterm s (4 * b + 4)) =
          (∑' m : ℕ, (fun n => zterm s (n + 2)) (2 + 4 * m)) := by
      apply tsum_congr
      intro m
      simp only
      congr 1
      omega
    have hD :
        (∑' b : ℕ, zterm s (4 * b + 5)) =
          (∑' m : ℕ, (fun n => zterm s (n + 2)) (3 + 4 * m)) := by
      apply tsum_congr
      intro m
      simp only
      congr 1
      omega
    rw [← hA, ← hB, ← hC, ← hD]
  have hT :
      (∑' k : ℕ, T k s) =
        4 * (∑' k : ℕ, zterm s (4 * k + 2)) -
          (∑' k : ℕ, (zterm s (4 * k + 2) + zterm s (4 * k + 3) +
            zterm s (4 * k + 4) + zterm s (4 * k + 5))) := by
    have h2 : Summable fun k : ℕ => zterm s (4 * k + 2) := by
      simpa [Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm] using
        zterm_comp_summable hs (a := 2) (b := 4) (by norm_num)
    have h3 : Summable fun k : ℕ => zterm s (4 * k + 3) := by
      simpa [Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm] using
        zterm_comp_summable hs (a := 3) (b := 4) (by norm_num)
    have h4 : Summable fun k : ℕ => zterm s (4 * k + 4) := by
      simpa [Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm] using
        zterm_comp_summable hs (a := 4) (b := 4) (by norm_num)
    have h5 : Summable fun k : ℕ => zterm s (4 * k + 5) := by
      simpa [Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm] using
        zterm_comp_summable hs (a := 5) (b := 4) (by norm_num)
    have hblocksum : Summable fun k : ℕ =>
        zterm s (4 * k + 2) + zterm s (4 * k + 3) +
          zterm s (4 * k + 4) + zterm s (4 * k + 5) :=
      ((h2.add h3).add h4).add h5
    have hcongr : (fun k : ℕ => T k s) =
        fun k : ℕ => 4 * zterm s (4 * k + 2) -
          (zterm s (4 * k + 2) + zterm s (4 * k + 3) +
            zterm s (4 * k + 4) + zterm s (4 * k + 5)) := by
      funext k
      unfold T
      ring
    rw [tsum_congr (congr_fun hcongr), (Summable.mul_left 4 h2).tsum_sub hblocksum,
      tsum_mul_left]
  rw [hT, hblock', tsum_zterm_tail_two hs, tsum_zterm_four_two hs]
  ring

lemma hasDerivAt_phi (u x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => phi u y) ((1 - u * log x) * x ^ (-u - 1)) x := by
  have hxne : x ≠ 0 := ne_of_gt hx
  unfold phi
  have hlog : HasDerivAt log x⁻¹ x := Real.hasDerivAt_log hxne
  have hr : HasDerivAt (fun y : ℝ => y ^ (-u)) ((-u) * x ^ ((-u) - 1)) x :=
    Real.hasDerivAt_rpow_const (x := x) (p := -u) (Or.inl hxne)
  convert hlog.mul hr using 1
  have hrpow : x⁻¹ * x ^ (-u) = x ^ (-u - 1) := by
    rw [← Real.rpow_neg_one x, ← Real.rpow_add hx]
    ring_nf
  rw [hrpow]
  ring

lemma deriv_phi (u x : ℝ) (hx : 0 < x) :
    deriv (fun y : ℝ => phi u y) x = (1 - u * log x) * x ^ (-u - 1) := by
  exact (hasDerivAt_phi u x hx).deriv

lemma hasDerivAt_rho (u x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => rho u y) ((-u) * x ^ (-u - 1)) x := by
  have hxne : x ≠ 0 := ne_of_gt hx
  simpa [rho] using Real.hasDerivAt_rpow_const (x := x) (p := -u) (Or.inl hxne)

lemma phi_deriv_norm_bound {u x : ℝ} (hu1 : 1 ≤ u) (hu2 : u ≤ 2) (hx1 : 1 ≤ x) :
    ‖(1 - u * log x) * x ^ (-u - 1)‖ ≤ 5 * x ^ (-(3 / 2 : ℝ)) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hu0 : 0 ≤ u := zero_le_one.trans hu1
  have hlog0 : 0 ≤ log x := log_nonneg hx1
  have hcoef :
      ‖1 - u * log x‖ ≤ 5 * x ^ ((1 / 2 : ℝ)) := by
    calc
      ‖1 - u * log x‖ ≤ ‖(1 : ℝ)‖ + ‖u * log x‖ := norm_sub_le _ _
      _ = 1 + ‖u‖ * ‖log x‖ := by rw [norm_one, norm_mul]
      _ ≤ 1 + 2 * log x := by
        have hu_norm : ‖u‖ ≤ 2 := by
          rwa [Real.norm_of_nonneg hu0]
        rw [Real.norm_of_nonneg hlog0]
        nlinarith [mul_le_mul_of_nonneg_right hu_norm hlog0]
      _ ≤ 1 + 2 * (2 * x ^ ((1 / 2 : ℝ))) := by
        gcongr
        have h := Real.log_le_rpow_div (x := x) (ε := (1 / 2 : ℝ)) hx0.le (by norm_num)
        norm_num at h
        nlinarith
      _ ≤ 5 * x ^ ((1 / 2 : ℝ)) := by
        have hsqrt : 1 ≤ x ^ ((1 / 2 : ℝ)) := by
          simpa using Real.rpow_le_rpow zero_le_one hx1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
        nlinarith
  have hrpow_nonneg : 0 ≤ x ^ (-u - 1) := Real.rpow_nonneg hx0.le _
  have hrpow_le : x ^ (-u - 1) ≤ x ^ (-(2 : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le hx1 ?_
    linarith
  calc
    ‖(1 - u * log x) * x ^ (-u - 1)‖
        = ‖1 - u * log x‖ * x ^ (-u - 1) := by
          rw [norm_mul, Real.norm_of_nonneg hrpow_nonneg]
    _ ≤ (5 * x ^ ((1 / 2 : ℝ))) * x ^ (-(2 : ℝ)) := by
          exact mul_le_mul hcoef hrpow_le hrpow_nonneg (by positivity)
    _ = 5 * x ^ (-(3 / 2 : ℝ)) := by
          rw [mul_assoc, ← Real.rpow_add hx0]
          ring_nf

lemma rho_deriv_norm_bound {u x : ℝ} (hu1 : 1 ≤ u) (hu2 : u ≤ 2) (hx1 : 1 ≤ x) :
    ‖(-u) * x ^ (-u - 1)‖ ≤ 2 * x ^ (-(2 : ℝ)) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hu0 : 0 ≤ u := zero_le_one.trans hu1
  have hrpow_nonneg : 0 ≤ x ^ (-u - 1) := Real.rpow_nonneg hx0.le _
  have hrpow_le : x ^ (-u - 1) ≤ x ^ (-(2 : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le hx1 ?_
    linarith
  calc
    ‖(-u) * x ^ (-u - 1)‖ = ‖u‖ * x ^ (-u - 1) := by
      rw [norm_mul, norm_neg, Real.norm_of_nonneg hrpow_nonneg]
    _ ≤ 2 * x ^ (-(2 : ℝ)) := by
      gcongr
      rwa [Real.norm_of_nonneg hu0]

lemma phi_block (k : ℕ) (u : ℝ) :
    logTerm k u =
      3 * phi u ((4 * k + 2 : ℕ) : ℝ) -
        phi u ((4 * k + 3 : ℕ) : ℝ) -
        phi u ((4 * k + 4 : ℕ) : ℝ) -
        phi u ((4 * k + 5 : ℕ) : ℝ) := by
  have h2 : (4 * k + 2 : ℕ) ≠ 0 := by omega
  have h3 : (4 * k + 3 : ℕ) ≠ 0 := by omega
  have h4 : (4 * k + 4 : ℕ) ≠ 0 := by omega
  have h5 : (4 * k + 5 : ℕ) ≠ 0 := by omega
  unfold logTerm phi
  rw [zterm_eq_rpow_neg (s := u) h2, zterm_eq_rpow_neg (s := u) h3,
    zterm_eq_rpow_neg (s := u) h4, zterm_eq_rpow_neg (s := u) h5]
  ring

lemma rho_block (k : ℕ) (u : ℝ) :
    T k u =
      3 * rho u ((4 * k + 2 : ℕ) : ℝ) -
        rho u ((4 * k + 3 : ℕ) : ℝ) -
        rho u ((4 * k + 4 : ℕ) : ℝ) -
        rho u ((4 * k + 5 : ℕ) : ℝ) := by
  have h2 : (4 * k + 2 : ℕ) ≠ 0 := by omega
  have h3 : (4 * k + 3 : ℕ) ≠ 0 := by omega
  have h4 : (4 * k + 4 : ℕ) ≠ 0 := by omega
  have h5 : (4 * k + 5 : ℕ) ≠ 0 := by omega
  unfold T rho
  rw [zterm_eq_rpow_neg (s := u) h2, zterm_eq_rpow_neg (s := u) h3,
    zterm_eq_rpow_neg (s := u) h4, zterm_eq_rpow_neg (s := u) h5]

lemma phi_sub_bound {u a b : ℝ} (hu1 : 1 ≤ u) (hu2 : u ≤ 2)
    (ha1 : 1 ≤ a) (hab : a ≤ b) :
    ‖phi u b - phi u a‖ ≤ (5 * a ^ (-(3 / 2 : ℝ))) * (b - a) := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha1
  have hderiv : ∀ x ∈ Set.Icc a b,
      HasDerivWithinAt (fun y : ℝ => phi u y)
        ((1 - u * log x) * x ^ (-u - 1)) (Set.Icc a b) x := by
    intro x hx
    exact (hasDerivAt_phi u x (ha0.trans_le hx.1)).hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ico a b,
      ‖(1 - u * log x) * x ^ (-u - 1)‖ ≤ 5 * a ^ (-(3 / 2 : ℝ)) := by
    intro x hx
    have hx1 : 1 ≤ x := ha1.trans hx.1
    have hx0 : 0 < x := zero_lt_one.trans_le hx1
    have hxa : a ≤ x := hx.1
    have hpow : x ^ (-(3 / 2 : ℝ)) ≤ a ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos ha0 hxa (by norm_num)
    exact (phi_deriv_norm_bound hu1 hu2 hx1).trans (by gcongr)
  exact norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound b ⟨hab, le_rfl⟩

lemma rho_sub_bound {u a b : ℝ} (hu1 : 1 ≤ u) (hu2 : u ≤ 2)
    (ha1 : 1 ≤ a) (hab : a ≤ b) :
    ‖rho u b - rho u a‖ ≤ (2 * a ^ (-(2 : ℝ))) * (b - a) := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha1
  have hderiv : ∀ x ∈ Set.Icc a b,
      HasDerivWithinAt (fun y : ℝ => rho u y)
        ((-u) * x ^ (-u - 1)) (Set.Icc a b) x := by
    intro x hx
    exact (hasDerivAt_rho u x (ha0.trans_le hx.1)).hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ico a b,
      ‖(-u) * x ^ (-u - 1)‖ ≤ 2 * a ^ (-(2 : ℝ)) := by
    intro x hx
    have hx1 : 1 ≤ x := ha1.trans hx.1
    have hxa : a ≤ x := hx.1
    have hpow : x ^ (-(2 : ℝ)) ≤ a ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos ha0 hxa (by norm_num)
    exact (rho_deriv_norm_bound hu1 hu2 hx1).trans (by gcongr)
  exact norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound b ⟨hab, le_rfl⟩

lemma logTerm_bound {u : ℝ} (hu1 : 1 ≤ u) (hu2 : u ≤ 2) (k : ℕ) :
    ‖logTerm k u‖ ≤ 30 * zterm (3 / 2 : ℝ) (4 * k + 2) := by
  have h2 : (4 * k + 2 : ℕ) ≠ 0 := by omega
  rw [zterm_eq_rpow_neg (s := (3 / 2 : ℝ)) h2]
  let a : ℝ := ((4 * k + 2 : ℕ) : ℝ)
  let b : ℝ := ((4 * k + 3 : ℕ) : ℝ)
  let c : ℝ := ((4 * k + 4 : ℕ) : ℝ)
  let d : ℝ := ((4 * k + 5 : ℕ) : ℝ)
  let A : ℝ := phi u a
  let B : ℝ := phi u b
  let C : ℝ := phi u c
  let D : ℝ := phi u d
  have ha1 : 1 ≤ a := by
    dsimp [a]
    exact_mod_cast (by omega : (1 : ℕ) ≤ 4 * k + 2)
  have hab : a ≤ b := by
    dsimp [a, b]
    exact_mod_cast (by omega : 4 * k + 2 ≤ 4 * k + 3)
  have hac : a ≤ c := by
    dsimp [a, c]
    exact_mod_cast (by omega : 4 * k + 2 ≤ 4 * k + 4)
  have had : a ≤ d := by
    dsimp [a, d]
    exact_mod_cast (by omega : 4 * k + 2 ≤ 4 * k + 5)
  have hbdiff : b - a = 1 := by
    dsimp [a, b]
    norm_num
  have hcdiff : c - a = 2 := by
    dsimp [a, c]
    norm_num
  have hddiff : d - a = 3 := by
    dsimp [a, d]
    norm_num
  have hB : ‖A - B‖ ≤ (5 * a ^ (-(3 / 2 : ℝ))) * 1 := by
    simpa [A, B, norm_sub_rev, hbdiff] using phi_sub_bound hu1 hu2 ha1 hab
  have hC : ‖A - C‖ ≤ (5 * a ^ (-(3 / 2 : ℝ))) * 2 := by
    simpa [A, C, norm_sub_rev, hcdiff] using phi_sub_bound hu1 hu2 ha1 hac
  have hD : ‖A - D‖ ≤ (5 * a ^ (-(3 / 2 : ℝ))) * 3 := by
    simpa [A, D, norm_sub_rev, hddiff] using phi_sub_bound hu1 hu2 ha1 had
  have hrewrite : logTerm k u = (A - B) + (A - C) + (A - D) := by
    rw [phi_block]
    dsimp [A, B, C, D, a, b, c, d]
    ring
  calc
    ‖logTerm k u‖ = ‖(A - B) + (A - C) + (A - D)‖ := by rw [hrewrite]
    _ ≤ ‖A - B‖ + ‖A - C‖ + ‖A - D‖ := by
      calc
        ‖(A - B) + (A - C) + (A - D)‖ ≤ ‖(A - B) + (A - C)‖ + ‖A - D‖ :=
          norm_add_le _ _
        _ ≤ (‖A - B‖ + ‖A - C‖) + ‖A - D‖ :=
          add_le_add (norm_add_le _ _) le_rfl
        _ = ‖A - B‖ + ‖A - C‖ + ‖A - D‖ := by ring
    _ ≤ 30 * a ^ (-(3 / 2 : ℝ)) := by nlinarith

lemma T_bound {u : ℝ} (hu1 : 1 ≤ u) (hu2 : u ≤ 2) (k : ℕ) :
    ‖T k u‖ ≤ 12 * zterm (2 : ℝ) (4 * k + 2) := by
  have h2 : (4 * k + 2 : ℕ) ≠ 0 := by omega
  rw [zterm_eq_rpow_neg (s := (2 : ℝ)) h2]
  let a : ℝ := ((4 * k + 2 : ℕ) : ℝ)
  let b : ℝ := ((4 * k + 3 : ℕ) : ℝ)
  let c : ℝ := ((4 * k + 4 : ℕ) : ℝ)
  let d : ℝ := ((4 * k + 5 : ℕ) : ℝ)
  let A : ℝ := rho u a
  let B : ℝ := rho u b
  let C : ℝ := rho u c
  let D : ℝ := rho u d
  have ha1 : 1 ≤ a := by
    dsimp [a]
    exact_mod_cast (by omega : (1 : ℕ) ≤ 4 * k + 2)
  have hab : a ≤ b := by
    dsimp [a, b]
    exact_mod_cast (by omega : 4 * k + 2 ≤ 4 * k + 3)
  have hac : a ≤ c := by
    dsimp [a, c]
    exact_mod_cast (by omega : 4 * k + 2 ≤ 4 * k + 4)
  have had : a ≤ d := by
    dsimp [a, d]
    exact_mod_cast (by omega : 4 * k + 2 ≤ 4 * k + 5)
  have hbdiff : b - a = 1 := by
    dsimp [a, b]
    norm_num
  have hcdiff : c - a = 2 := by
    dsimp [a, c]
    norm_num
  have hddiff : d - a = 3 := by
    dsimp [a, d]
    norm_num
  have hB : ‖A - B‖ ≤ (2 * a ^ (-(2 : ℝ))) * 1 := by
    simpa [A, B, norm_sub_rev, hbdiff] using rho_sub_bound hu1 hu2 ha1 hab
  have hC : ‖A - C‖ ≤ (2 * a ^ (-(2 : ℝ))) * 2 := by
    simpa [A, C, norm_sub_rev, hcdiff] using rho_sub_bound hu1 hu2 ha1 hac
  have hD : ‖A - D‖ ≤ (2 * a ^ (-(2 : ℝ))) * 3 := by
    simpa [A, D, norm_sub_rev, hddiff] using rho_sub_bound hu1 hu2 ha1 had
  have hrewrite : T k u = (A - B) + (A - C) + (A - D) := by
    rw [rho_block]
    dsimp [A, B, C, D, a, b, c, d]
    ring
  calc
    ‖T k u‖ = ‖(A - B) + (A - C) + (A - D)‖ := by rw [hrewrite]
    _ ≤ ‖A - B‖ + ‖A - C‖ + ‖A - D‖ := by
      calc
        ‖(A - B) + (A - C) + (A - D)‖ ≤ ‖(A - B) + (A - C)‖ + ‖A - D‖ :=
          norm_add_le _ _
        _ ≤ (‖A - B‖ + ‖A - C‖) + ‖A - D‖ :=
          add_le_add (norm_add_le _ _) le_rfl
        _ = ‖A - B‖ + ‖A - C‖ + ‖A - D‖ := by ring
    _ ≤ 12 * a ^ (-(2 : ℝ)) := by nlinarith

lemma summable_log_bound : Summable fun k : ℕ => 30 * zterm (3 / 2 : ℝ) (4 * k + 2) := by
  exact Summable.mul_left 30 (by
    simpa [Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm] using
      zterm_comp_summable (s := (3 / 2 : ℝ)) (by norm_num) (a := 2) (b := 4) (by norm_num))

lemma summable_T_bound : Summable fun k : ℕ => 12 * zterm (2 : ℝ) (4 * k + 2) := by
  exact Summable.mul_left 12 (by
    simpa [Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm] using
      zterm_comp_summable (s := (2 : ℝ)) (by norm_num) (a := 2) (b := 4) (by norm_num))

lemma tendsto_tsum_T_at_one :
    Tendsto (fun s : ℝ => ∑' k : ℕ, T k s) (𝓝[>] (1 : ℝ)) (𝓝 (∑' k : ℕ, T k 1)) := by
  refine tendsto_tsum_of_dominated_convergence summable_T_bound ?_ ?_
  · intro k
    exact (hasDerivAt_T k 1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · have hlt2 : ∀ᶠ s in 𝓝[>] (1 : ℝ), s < 2 :=
      nhdsWithin_le_nhds (isOpen_Iio.mem_nhds (by norm_num : (1 : ℝ) < 2))
    filter_upwards [eventually_mem_nhdsWithin, hlt2] with s hs1 hs2 k
    exact T_bound hs1.le hs2.le k

lemma tendsto_zterm_residue :
    Tendsto (fun s : ℝ => (s - 1) * (∑' n : ℕ, zterm s n)) (𝓝[>] (1 : ℝ)) (𝓝 1) := by
  simpa [zterm] using tendsto_sub_mul_tsum_nat_rpow

lemma hasDerivAt_A : HasDerivAt A (-(log 2)) (1 : ℝ) := by
  have hneg : HasDerivAt (fun s : ℝ => -s) (-1) (1 : ℝ) := (hasDerivAt_id 1).neg
  have hpow := hneg.const_rpow (by norm_num : (0 : ℝ) < 2)
  unfold A
  convert ((hpow.const_mul 2).sub (hasDerivAt_const (1 : ℝ) (1 : ℝ))) using 1
  ring

lemma tendsto_A_at_one :
    Tendsto A (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  have hA1 : A (1 : ℝ) = 0 := by
    norm_num [A, Real.rpow_neg_one]
  simpa [hA1] using hasDerivAt_A.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

lemma tendsto_A_div :
    Tendsto (fun s : ℝ => A s / (s - 1)) (𝓝[>] (1 : ℝ)) (𝓝 (-(log 2))) := by
  have hslope := Filter.Tendsto.mono_left hasDerivAt_A.tendsto_slope (nhdsGT_le_nhdsNE (1 : ℝ))
  refine hslope.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with s hs
  rw [slope_def_field]
  have hA1 : A (1 : ℝ) = 0 := by
    norm_num [A, Real.rpow_neg_one]
  simp [hA1]

lemma tendsto_A_sq_zeta_zero :
    Tendsto (fun s : ℝ => (A s) ^ 2 * (∑' n : ℕ, zterm s n)) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  have hlim :
      Tendsto (fun s : ℝ => (A s * (A s / (s - 1))) *
          ((s - 1) * (∑' n : ℕ, zterm s n))) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    simpa using (tendsto_A_at_one.mul tendsto_A_div).mul tendsto_zterm_residue
  refine hlim.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with s hs
  have hne : s - 1 ≠ 0 := sub_ne_zero.mpr hs.ne'
  field_simp [hne]

lemma tendsto_T_rhs_at_one :
    Tendsto (fun s : ℝ => 1 - (A s) ^ 2 * (∑' n : ℕ, zterm s n)) (𝓝[>] (1 : ℝ)) (𝓝 1) := by
  simpa using tendsto_const_nhds.sub tendsto_A_sq_zeta_zero

lemma tsum_T_one_eq : (∑' k : ℕ, T k 1) = 1 := by
  have h_rhs :
      Tendsto (fun s : ℝ => ∑' k : ℕ, T k s) (𝓝[>] (1 : ℝ)) (𝓝 1) := by
    refine tendsto_T_rhs_at_one.congr' ?_
    filter_upwards [eventually_mem_nhdsWithin] with s hs
    simpa [A] using (tsum_T_eq hs).symm
  exact tendsto_nhds_unique tendsto_tsum_T_at_one h_rhs

lemma quotient_bound {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2) (k : ℕ) :
    ‖Q s k‖ ≤ 30 * zterm (3 / 2 : ℝ) (4 * k + 2) := by
  have hderiv : ∀ u ∈ Set.Icc (1 : ℝ) s,
      HasDerivWithinAt (fun y : ℝ => T k y) (-(logTerm k u)) (Set.Icc (1 : ℝ) s) u := by
    intro u hu
    exact (hasDerivAt_T k u).hasDerivWithinAt
  have hbound : ∀ u ∈ Set.Ico (1 : ℝ) s,
      ‖-(logTerm k u)‖ ≤ 30 * zterm (3 / 2 : ℝ) (4 * k + 2) := by
    intro u hu
    have hu2 : u ≤ 2 := (lt_trans hu.2 hs2).le
    simpa using logTerm_bound hu.1 hu2 k
  have hseg :=
    norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound s ⟨hs1.le, le_rfl⟩
  have hnum : ‖T k 1 - T k s‖ ≤ (30 * zterm (3 / 2 : ℝ) (4 * k + 2)) * (s - 1) := by
    simpa [norm_sub_rev] using hseg
  have hpos : 0 < s - 1 := sub_pos.mpr hs1
  calc
    ‖Q s k‖ = ‖T k 1 - T k s‖ / (s - 1) := by
      rw [Q, norm_div, Real.norm_of_nonneg hpos.le]
    _ ≤ ((30 * zterm (3 / 2 : ℝ) (4 * k + 2)) * (s - 1)) / (s - 1) := by
      exact div_le_div_of_nonneg_right hnum hpos.le
    _ = 30 * zterm (3 / 2 : ℝ) (4 * k + 2) := by
      field_simp [hpos.ne']

lemma tendsto_Q_at_one (k : ℕ) :
    Tendsto (fun s : ℝ => Q s k) (𝓝[>] (1 : ℝ)) (𝓝 (logTerm k 1)) := by
  have hslope :=
    Filter.Tendsto.mono_left (hasDerivAt_T k 1).tendsto_slope (nhdsGT_le_nhdsNE (1 : ℝ))
  have hneg : Tendsto (fun s : ℝ => -(slope (fun u : ℝ => T k u) 1 s))
      (𝓝[>] (1 : ℝ)) (𝓝 (logTerm k 1)) := by
    simpa using hslope.neg
  refine hneg.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with s hs
  change 1 < s at hs
  rw [slope_def_field, Q]
  field_simp [sub_ne_zero.mpr hs.ne']
  ring

lemma tendsto_tsum_Q_at_one :
    Tendsto (fun s : ℝ => ∑' k : ℕ, Q s k) (𝓝[>] (1 : ℝ))
      (𝓝 (∑' k : ℕ, logTerm k 1)) := by
  refine tendsto_tsum_of_dominated_convergence summable_log_bound (fun k => tendsto_Q_at_one k) ?_
  have hlt2 : ∀ᶠ s in 𝓝[>] (1 : ℝ), s < 2 :=
    nhdsWithin_le_nhds (isOpen_Iio.mem_nhds (by norm_num : (1 : ℝ) < 2))
  filter_upwards [eventually_mem_nhdsWithin, hlt2] with s hs1 hs2 k
  exact quotient_bound hs1 hs2 k

lemma tsum_Q_eq {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2) :
    (∑' k : ℕ, Q s k) = (1 - (∑' k : ℕ, T k s)) / (s - 1) := by
  have hT1 : Summable fun k : ℕ => T k 1 := by
    exact summable_T_bound.of_norm_bounded fun k => by
      simpa using T_bound (by norm_num : (1 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 2) k
  have hTs : Summable fun k : ℕ => T k s := by
    exact summable_T_bound.of_norm_bounded fun k => T_bound hs1.le hs2.le k
  calc
    (∑' k : ℕ, Q s k) = (∑' k : ℕ, (T k 1 - T k s) / (s - 1)) := by rfl
    _ = (∑' k : ℕ, (T k 1 - T k s)) / (s - 1) := by
      rw [tsum_div_const]
    _ = ((∑' k : ℕ, T k 1) - (∑' k : ℕ, T k s)) / (s - 1) := by
      rw [hT1.tsum_sub hTs]
    _ = (1 - (∑' k : ℕ, T k s)) / (s - 1) := by
      rw [tsum_T_one_eq]

lemma tendsto_quotient_rhs :
    Tendsto (fun s : ℝ => (1 - (∑' k : ℕ, T k s)) / (s - 1)) (𝓝[>] (1 : ℝ))
      (𝓝 ((Real.log 4 / 2) * Real.log 2)) := by
  have hprod :
      Tendsto (fun s : ℝ => (A s / (s - 1)) * (A s / (s - 1)) *
          ((s - 1) * (∑' n : ℕ, zterm s n))) (𝓝[>] (1 : ℝ))
        (𝓝 (Real.log 2 * Real.log 2)) := by
    have h := (tendsto_A_div.mul tendsto_A_div).mul tendsto_zterm_residue
    simpa using h
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    ring
  have htarget : Real.log 2 * Real.log 2 = (Real.log 4 / 2) * Real.log 2 := by
    rw [hlog4]
    ring
  rw [← htarget]
  refine hprod.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with s hs
  change 1 < s at hs
  have hne : s - 1 ≠ 0 := sub_ne_zero.mpr hs.ne'
  rw [tsum_T_eq hs]
  simp [A]
  field_simp [hne]

lemma tsum_logTerm_one_eq : (∑' k : ℕ, logTerm k 1) = (Real.log 4 / 2) * Real.log 2 := by
  have hsumQ :
      Tendsto (fun s : ℝ => ∑' k : ℕ, Q s k) (𝓝[>] (1 : ℝ))
        (𝓝 ((Real.log 4 / 2) * Real.log 2)) := by
    refine tendsto_quotient_rhs.congr' ?_
    have hlt2 : ∀ᶠ s in 𝓝[>] (1 : ℝ), s < 2 :=
      nhdsWithin_le_nhds (isOpen_Iio.mem_nhds (by norm_num : (1 : ℝ) < 2))
    filter_upwards [eventually_mem_nhdsWithin, hlt2] with s hs1 hs2
    change 1 < s at hs1
    exact (tsum_Q_eq hs1 hs2).symm
  exact tendsto_nhds_unique tendsto_tsum_Q_at_one hsumQ

end Putnam2017B4

/--
Evaluate the sum \begin{gather*} \sum_{k=0}^\infty \left( 3 \cdot \frac{\ln(4k+2)}{4k+2} - \frac{\ln(4k+3)}{4k+3} - \frac{\ln(4k+4)}{4k+4} - \frac{\ln(4k+5)}{4k+5} \right) \ = 3 \cdot \frac{\ln 2}{2} - \frac{\ln 3}{3} - \frac{\ln 4}{4} - \frac{\ln 5}{5} + 3 \cdot \frac{\ln 6}{6} - \frac{\ln 7}{7} \ - \frac{\ln 8}{8} - \frac{\ln 9}{9} + 3 \cdot \frac{\ln 10}{10} - \cdots . \end{gather*} (As usual, $\ln x$ denotes the natural logarithm of $x$.)
-/
theorem putnam_2017_b4 :
  (∑' k : ℕ, (3 * log (4 * k + 2) / (4 * k + 2) - log (4 * k + 3) / (4 * k + 3) - log (4 * k + 4) / (4 * k + 4) - log (4 * k + 5) / (4 * k + 5)) = putnam_2017_b4_solution) :=
by
  rw [putnam_2017_b4_solution, ← Putnam2017B4.tsum_logTerm_one_eq]
  apply tsum_congr
  intro k
  simp [Putnam2017B4.logTerm, Putnam2017B4.zterm, Real.rpow_one]
  ring
