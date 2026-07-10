import Mathlib

open Polynomial

private lemma putnam_1975_a3_weighted_amgm {u θ : ℝ} (hu : 0 ≤ u) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) : u ^ θ ≤ θ * u + (1 - θ) := by
  have hθ0' : 0 ≤ θ := hθ0.le
  have hθ1' : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1.le
  have hsum : θ + (1 - θ) = 1 := by ring
  simpa [Real.one_rpow] using
    (Real.geom_mean_le_arith_mean2_weighted hθ0' hθ1' hu zero_le_one hsum)

private lemma putnam_1975_a3_max_core {u θ m : ℝ} (hu : 0 ≤ u) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hm0 : 0 < m) (hm : m ^ (1 - θ) = θ) :
    u ^ θ - u ≤ m ^ θ - m := by
  have hdiv : 0 ≤ u / m := div_nonneg hu hm0.le
  have hmain := putnam_1975_a3_weighted_amgm hdiv hθ0 hθ1
  have hmθ_nonneg : 0 ≤ m ^ θ := Real.rpow_nonneg hm0.le θ
  have hmθ_pos : 0 < m ^ θ := Real.rpow_pos_of_pos hm0 θ
  have hmul := mul_le_mul_of_nonneg_left hmain hmθ_nonneg
  have hleft : m ^ θ * (u / m) ^ θ = u ^ θ := by
    rw [Real.div_rpow hu hm0.le]
    rw [div_eq_mul_inv]
    field_simp [hmθ_pos.ne']
  have hm_split : m ^ (1 - θ) * m ^ θ = m := by
    rw [← Real.rpow_add hm0 (1 - θ) θ]
    rw [show 1 - θ + θ = 1 by ring, Real.rpow_one]
  have hm_mul : θ * m ^ θ = m := by
    simpa [hm] using hm_split
  have hterm1 : m ^ θ * (θ * (u / m)) = u := by
    calc
      m ^ θ * (θ * (u / m)) = (θ * m ^ θ) * (u / m) := by ring
      _ = m * (u / m) := by rw [hm_mul]
      _ = u := by field_simp [hm0.ne']
  have hterm2 : m ^ θ * (1 - θ) = m ^ θ - m := by
    calc
      m ^ θ * (1 - θ) = m ^ θ - θ * m ^ θ := by ring
      _ = m ^ θ - m := by rw [hm_mul]
  have hright : m ^ θ * (θ * (u / m) + (1 - θ)) = u + (m ^ θ - m) := by
    rw [mul_add, hterm1, hterm2]
  have hle : u ^ θ ≤ u + (m ^ θ - m) := by
    simpa [hleft, hright] using hmul
  linarith

private lemma putnam_1975_a3_min_core {u θ n : ℝ} (hu : 0 ≤ u) (hθ1 : 1 < θ)
    (hn0 : 0 < n) (hn : n ^ (θ - 1) = 1 / θ) :
    n ^ θ - n ≤ u ^ θ - u := by
  have hθ0 : 0 < θ := lt_trans zero_lt_one hθ1
  have hα0 : 0 < 1 / θ := one_div_pos.mpr hθ0
  have hα1 : 1 / θ < 1 := by
    rw [div_lt_iff₀ hθ0]
    linarith
  have huθ : 0 ≤ u ^ θ := Real.rpow_nonneg hu θ
  have hnθ0 : 0 < n ^ θ := Real.rpow_pos_of_pos hn0 θ
  have hcond : (n ^ θ) ^ (1 - 1 / θ) = 1 / θ := by
    rw [← Real.rpow_mul hn0.le θ (1 - 1 / θ)]
    have hmul : θ * (1 - 1 / θ) = θ - 1 := by
      field_simp [hθ0.ne']
    rw [hmul, hn]
  have hmax := putnam_1975_a3_max_core huθ hα0 hα1 hnθ0 hcond
  have hu_id : (u ^ θ) ^ (1 / θ) = u := by
    rw [← Real.rpow_mul hu θ (1 / θ)]
    rw [show θ * (1 / θ) = 1 by field_simp [hθ0.ne'], Real.rpow_one]
  have hn_id : (n ^ θ) ^ (1 / θ) = n := by
    rw [← Real.rpow_mul hn0.le θ (1 / θ)]
    rw [show θ * (1 / θ) = 1 by field_simp [hθ0.ne'], Real.rpow_one]
  linarith

private lemma putnam_1975_a3_le_one_of_rpow_eq {m e r : ℝ} (hm0 : 0 ≤ m) (he : 0 < e)
    (hr : r ≤ 1) (hm : m ^ e = r) : m ≤ 1 := by
  have hpow : m ^ e ≤ (1 : ℝ) ^ e := by
    simpa [hm] using hr
  exact (Real.rpow_le_rpow_iff hm0 zero_le_one he).mp hpow

private lemma putnam_1975_a3_x_identity {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (((a / b) ^ (1 / (b - a))) ^ b) ^ (1 - a / b) = a / b := by
  have hb : 0 < b := lt_trans ha hab
  have hbase : 0 < a / b := div_pos ha hb
  have hba : 0 < b - a := sub_pos.mpr hab
  have hxm : 0 ≤ (a / b) ^ (1 / (b - a)) := Real.rpow_nonneg hbase.le _
  have hpow : ((a / b) ^ (1 / (b - a))) ^ (b - a) = a / b := by
    rw [one_div, Real.rpow_inv_rpow hbase.le hba.ne']
  rw [← Real.rpow_mul hxm b (1 - a / b)]
  have hmul : b * (1 - a / b) = b - a := by
    field_simp [hb.ne']
  rw [hmul, hpow]

private lemma putnam_1975_a3_z_identity {b c : ℝ} (hb : 0 < b) (hbc : b < c) :
    (((b / c) ^ (1 / (c - b))) ^ b) ^ (c / b - 1) = b / c := by
  have hc : 0 < c := lt_trans hb hbc
  have hbase : 0 < b / c := div_pos hb hc
  have hcb : 0 < c - b := sub_pos.mpr hbc
  have hzm : 0 ≤ (b / c) ^ (1 / (c - b)) := Real.rpow_nonneg hbase.le _
  have hpow : ((b / c) ^ (1 / (c - b))) ^ (c - b) = b / c := by
    rw [one_div, Real.rpow_inv_rpow hbase.le hcb.ne']
  rw [← Real.rpow_mul hzm b (c / b - 1)]
  have hmul : b * (c / b - 1) = c - b := by
    field_simp [hb.ne']
  rw [hmul, hpow]

-- (fun (a, b, c) => ((a/b)^(1/(b - a)), (1 - ((a/b)^(1/(b - a)))^b)^(1/b), 0), fun (a, b, c) => (0, (1 - ((b/c)^(1/(c - b)))^b)^(1/b), (b/c)^(1/(c - b))))
/--
If $a$, $b$, and $c$ are real numbers satisfying $0 < a < b < c$, at what points in the set $$\{(x, y, z) \in \mathbb{R}^3 : x^b + y^b + z^b = 1, x \ge 0, y \ge 0, z \ge 0\}$$ does $f(x, y, z) = x^a + y^b + z^c$ attain its maximum and minimum?
-/
theorem putnam_1975_a3
(a b c : ℝ)
(hi : 0 < a ∧ a < b ∧ b < c)
(P : (ℝ × ℝ × ℝ) → Prop)
(f : (ℝ × ℝ × ℝ) → ℝ)
(hP : P = fun (x, y, z) => x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ x^b + y^b + z^b = 1)
(hf : f = fun (x, y, z) => x^a + y^b + z^c)
: (P (((fun (a, b, c) => ((a/b)^(1/(b - a)), (1 - ((a/b)^(1/(b - a)))^b)^(1/b), 0), fun (a, b, c) => (0, (1 - ((b/c)^(1/(c - b)))^b)^(1/b), (b/c)^(1/(c - b)))) : ((ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ)) × ((ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ)) ).1 (a, b, c)) ∧ ∀ x y z : ℝ, P (x, y, z) →
f (x, y, z) ≤ f (((fun (a, b, c) => ((a/b)^(1/(b - a)), (1 - ((a/b)^(1/(b - a)))^b)^(1/b), 0), fun (a, b, c) => (0, (1 - ((b/c)^(1/(c - b)))^b)^(1/b), (b/c)^(1/(c - b)))) : ((ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ)) × ((ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ)) ).1 (a, b, c))) ∧
(P (((fun (a, b, c) => ((a/b)^(1/(b - a)), (1 - ((a/b)^(1/(b - a)))^b)^(1/b), 0), fun (a, b, c) => (0, (1 - ((b/c)^(1/(c - b)))^b)^(1/b), (b/c)^(1/(c - b)))) : ((ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ)) × ((ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ)) ).2 (a, b, c)) ∧ ∀ x y z : ℝ, P (x, y, z) →
f (x, y, z) ≥ f (((fun (a, b, c) => ((a/b)^(1/(b - a)), (1 - ((a/b)^(1/(b - a)))^b)^(1/b), 0), fun (a, b, c) => (0, (1 - ((b/c)^(1/(c - b)))^b)^(1/b), (b/c)^(1/(c - b)))) : ((ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ)) × ((ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ)) ).2 (a, b, c))) := by
  rcases hi with ⟨ha, hab, hbc⟩
  subst P
  subst f
  dsimp
  set xm : ℝ := (a / b) ^ (1 / (b - a)) with hxm
  set ym : ℝ := (1 - xm ^ b) ^ (1 / b) with hym
  set zm : ℝ := (b / c) ^ (1 / (c - b)) with hzm
  set yn : ℝ := (1 - zm ^ b) ^ (1 / b) with hyn
  have hb : 0 < b := lt_trans ha hab
  have hc : 0 < c := lt_trans hb hbc
  have hα0 : 0 < a / b := div_pos ha hb
  have hα1 : a / b < 1 := by
    rw [div_lt_one hb]
    exact hab
  have hβ1 : 1 < c / b := by
    rw [one_lt_div hb]
    exact hbc
  have hγ1 : b / c < 1 := by
    rw [div_lt_one hc]
    exact hbc
  have h0a : (0 : ℝ) ^ a = 0 := Real.zero_rpow ha.ne'
  have h0b : (0 : ℝ) ^ b = 0 := Real.zero_rpow hb.ne'
  have h0c : (0 : ℝ) ^ c = 0 := Real.zero_rpow hc.ne'
  have hxm_pos : 0 < xm := by
    rw [hxm]
    exact Real.rpow_pos_of_pos hα0 _
  have hxm_nonneg : 0 ≤ xm := hxm_pos.le
  have hxm_b_pos : 0 < xm ^ b := Real.rpow_pos_of_pos hxm_pos b
  have hxm_b_nonneg : 0 ≤ xm ^ b := hxm_b_pos.le
  have hxm_id : (xm ^ b) ^ (1 - a / b) = a / b := by
    simpa [hxm] using putnam_1975_a3_x_identity ha hab
  have hxm_b_le_one : xm ^ b ≤ 1 := by
    exact putnam_1975_a3_le_one_of_rpow_eq hxm_b_nonneg (sub_pos.mpr hα1) hα1.le hxm_id
  have hym_arg_nonneg : 0 ≤ 1 - xm ^ b := sub_nonneg.mpr hxm_b_le_one
  have hym_nonneg : 0 ≤ ym := by
    rw [hym]
    exact Real.rpow_nonneg hym_arg_nonneg _
  have hym_b : ym ^ b = 1 - xm ^ b := by
    rw [hym, one_div, Real.rpow_inv_rpow hym_arg_nonneg hb.ne']
  have hxm_a : xm ^ a = (xm ^ b) ^ (a / b) := by
    calc
      xm ^ a = xm ^ (b * (a / b)) := by
        rw [show b * (a / b) = a by field_simp [hb.ne']]
      _ = (xm ^ b) ^ (a / b) := Real.rpow_mul hxm_nonneg b (a / b)
  have hzm_pos : 0 < zm := by
    rw [hzm]
    exact Real.rpow_pos_of_pos (div_pos hb hc) _
  have hzm_nonneg : 0 ≤ zm := hzm_pos.le
  have hzm_b_pos : 0 < zm ^ b := Real.rpow_pos_of_pos hzm_pos b
  have hzm_b_nonneg : 0 ≤ zm ^ b := hzm_b_pos.le
  have hzm_id0 : (zm ^ b) ^ (c / b - 1) = b / c := by
    simpa [hzm] using putnam_1975_a3_z_identity hb hbc
  have hbc_inv : b / c = 1 / (c / b) := by
    field_simp [hb.ne', hc.ne']
  have hzm_id : (zm ^ b) ^ (c / b - 1) = 1 / (c / b) := by
    exact hzm_id0.trans hbc_inv
  have hzm_b_le_one : zm ^ b ≤ 1 := by
    exact putnam_1975_a3_le_one_of_rpow_eq hzm_b_nonneg (sub_pos.mpr hβ1) hγ1.le hzm_id0
  have hyn_arg_nonneg : 0 ≤ 1 - zm ^ b := sub_nonneg.mpr hzm_b_le_one
  have hyn_nonneg : 0 ≤ yn := by
    rw [hyn]
    exact Real.rpow_nonneg hyn_arg_nonneg _
  have hyn_b : yn ^ b = 1 - zm ^ b := by
    rw [hyn, one_div, Real.rpow_inv_rpow hyn_arg_nonneg hb.ne']
  have hzm_c : zm ^ c = (zm ^ b) ^ (c / b) := by
    calc
      zm ^ c = zm ^ (b * (c / b)) := by
        rw [show b * (c / b) = c by field_simp [hb.ne']]
      _ = (zm ^ b) ^ (c / b) := Real.rpow_mul hzm_nonneg b (c / b)
  constructor
  · constructor
    · refine ⟨hxm_nonneg, hym_nonneg, le_rfl, ?_⟩
      rw [hym_b, h0b]
      ring
    · intro x y z hxyz
      rcases hxyz with ⟨hx, hy, hz, hsum⟩
      have hxb_nonneg : 0 ≤ x ^ b := Real.rpow_nonneg hx b
      have hyb_nonneg : 0 ≤ y ^ b := Real.rpow_nonneg hy b
      have hzb_nonneg : 0 ≤ z ^ b := Real.rpow_nonneg hz b
      have hxb_le_one : x ^ b ≤ 1 := by nlinarith only [hyb_nonneg, hzb_nonneg, hsum]
      have hzb_le_one : z ^ b ≤ 1 := by nlinarith only [hxb_nonneg, hyb_nonneg, hsum]
      have hxa : x ^ a = (x ^ b) ^ (a / b) := by
        calc
          x ^ a = x ^ (b * (a / b)) := by
            rw [show b * (a / b) = a by field_simp [hb.ne']]
          _ = (x ^ b) ^ (a / b) := Real.rpow_mul hx b (a / b)
      have hzc : z ^ c = (z ^ b) ^ (c / b) := by
        calc
          z ^ c = z ^ (b * (c / b)) := by
            rw [show b * (c / b) = c by field_simp [hb.ne']]
          _ = (z ^ b) ^ (c / b) := Real.rpow_mul hz b (c / b)
      have hxpart0 :
          (x ^ b) ^ (a / b) - x ^ b ≤ (xm ^ b) ^ (a / b) - xm ^ b :=
        putnam_1975_a3_max_core hxb_nonneg hα0 hα1 hxm_b_pos hxm_id
      have hxpart : x ^ a - x ^ b ≤ xm ^ a - xm ^ b := by
        simpa [hxa, hxm_a] using hxpart0
      have hzpow_le : (z ^ b) ^ (c / b) ≤ z ^ b :=
        Real.rpow_le_self_of_le_one hzb_nonneg hzb_le_one hβ1.le
      have hzpart : z ^ c - z ^ b ≤ 0 := by
        rw [hzc]
        exact sub_nonpos.mpr hzpow_le
      have hlhs : x ^ a + y ^ b + z ^ c = 1 + (x ^ a - x ^ b) + (z ^ c - z ^ b) := by
        have hy_eq : y ^ b = 1 - x ^ b - z ^ b := by linarith only [hsum]
        rw [hy_eq]
        abel
      have hrhs : xm ^ a + ym ^ b + 0 ^ c = 1 + (xm ^ a - xm ^ b) := by
        rw [hym_b, h0c]
        abel
      calc
        x ^ a + y ^ b + z ^ c = 1 + (x ^ a - x ^ b) + (z ^ c - z ^ b) := hlhs
        _ ≤ 1 + (xm ^ a - xm ^ b) := by linarith only [hxpart, hzpart]
        _ = xm ^ a + ym ^ b + 0 ^ c := hrhs.symm
  · constructor
    · refine ⟨le_rfl, hyn_nonneg, hzm_nonneg, ?_⟩
      rw [hyn_b, h0b]
      ring
    · intro x y z hxyz
      rcases hxyz with ⟨hx, hy, hz, hsum⟩
      have hxb_nonneg : 0 ≤ x ^ b := Real.rpow_nonneg hx b
      have hyb_nonneg : 0 ≤ y ^ b := Real.rpow_nonneg hy b
      have hzb_nonneg : 0 ≤ z ^ b := Real.rpow_nonneg hz b
      have hxb_le_one : x ^ b ≤ 1 := by nlinarith only [hyb_nonneg, hzb_nonneg, hsum]
      have hxa : x ^ a = (x ^ b) ^ (a / b) := by
        calc
          x ^ a = x ^ (b * (a / b)) := by
            rw [show b * (a / b) = a by field_simp [hb.ne']]
          _ = (x ^ b) ^ (a / b) := Real.rpow_mul hx b (a / b)
      have hzc : z ^ c = (z ^ b) ^ (c / b) := by
        calc
          z ^ c = z ^ (b * (c / b)) := by
            rw [show b * (c / b) = c by field_simp [hb.ne']]
          _ = (z ^ b) ^ (c / b) := Real.rpow_mul hz b (c / b)
      have hxpow_ge : x ^ b ≤ (x ^ b) ^ (a / b) :=
        Real.self_le_rpow_of_le_one hxb_nonneg hxb_le_one hα1.le
      have hxpart : 0 ≤ x ^ a - x ^ b := by
        rw [hxa]
        linarith only [hxpow_ge]
      have hzpart0 :
          (zm ^ b) ^ (c / b) - zm ^ b ≤ (z ^ b) ^ (c / b) - z ^ b :=
        putnam_1975_a3_min_core hzb_nonneg hβ1 hzm_b_pos hzm_id
      have hzpart : zm ^ c - zm ^ b ≤ z ^ c - z ^ b := by
        simpa [hzc, hzm_c] using hzpart0
      have hlhs : x ^ a + y ^ b + z ^ c = 1 + (x ^ a - x ^ b) + (z ^ c - z ^ b) := by
        have hy_eq : y ^ b = 1 - x ^ b - z ^ b := by linarith only [hsum]
        rw [hy_eq]
        abel
      have hrhs : 0 ^ a + yn ^ b + zm ^ c = 1 + (zm ^ c - zm ^ b) := by
        rw [h0a, hyn_b]
        abel
      calc
        0 ^ a + yn ^ b + zm ^ c = 1 + (zm ^ c - zm ^ b) := hrhs
        _ ≤ 1 + (x ^ a - x ^ b) + (z ^ c - z ^ b) := by
          linarith only [hxpart, hzpart]
        _ = x ^ a + y ^ b + z ^ c := hlhs.symm
