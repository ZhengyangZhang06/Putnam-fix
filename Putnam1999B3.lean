import Mathlib

open Filter Topology Metric

private def putnam_1999_b3_param (t : Fin 3 × ℕ × ℕ) : ℕ × ℕ :=
  (t.2.1 + 2 * t.2.2 + t.1, 2 * t.2.1 + t.2.2 + t.1)

private lemma putnam_1999_b3_param_injective :
    Function.Injective putnam_1999_b3_param := by
  intro a b h
  rcases a with ⟨r, k, l⟩
  rcases b with ⟨r', k', l'⟩
  simp [putnam_1999_b3_param] at h ⊢
  constructor
  · apply Fin.ext
    omega
  constructor <;> omega

private lemma putnam_1999_b3_exists_param_of_cone {m n : ℕ}
    (hmn : m ≤ 2 * n) (hnm : n ≤ 2 * m) :
    ∃ r : Fin 3, ∃ k l : ℕ, m = k + 2 * l + r ∧ n = 2 * k + l + r := by
  let u := 2 * n - m
  let v := 2 * m - n
  let rNat := u % 3
  have hrlt : rNat < 3 := by
    dsimp [rNat]
    exact Nat.mod_lt _ (by norm_num)
  refine ⟨⟨rNat, hrlt⟩, u / 3, v / 3, ?_, ?_⟩
  have hmod : u % 3 = v % 3 := by
    dsimp [u, v]
    omega
  have hu0 : 3 * (u / 3) + u % 3 = u := Nat.div_add_mod u 3
  have hv0 : 3 * (v / 3) + v % 3 = v := Nat.div_add_mod v 3
  have hu : u = 3 * (u / 3) + rNat := by omega
  have hv : v = 3 * (v / 3) + rNat := by omega
  have huv : u + 2 * v = 3 * m := by
    dsimp [u, v]
    omega
  have hvu : 2 * u + v = 3 * n := by
    dsimp [u, v]
    omega
  · simp
    omega
  · simp
    omega

private lemma putnam_1999_b3_ratio_iff_cone {m n : ℕ} :
    (m > 0 ∧ n > 0 ∧ (1 : ℝ) / 2 ≤ (m : ℝ) / n ∧ (m : ℝ) / n ≤ 2) ↔
      (m > 0 ∧ n > 0 ∧ m ≤ 2 * n ∧ n ≤ 2 * m) := by
  constructor
  · rintro ⟨hmpos, hnpos, hlow, hhigh⟩
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hnpos
    refine ⟨hmpos, hnpos, ?_, ?_⟩
    · have hleR : (m : ℝ) ≤ 2 * (n : ℝ) := by
        calc
          (m : ℝ) = ((m : ℝ) / n) * n := by field_simp [hnR.ne']
          _ ≤ 2 * (n : ℝ) := mul_le_mul_of_nonneg_right hhigh hnR.le
      exact_mod_cast hleR
    · have hleR : (n : ℝ) ≤ 2 * (m : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_right hlow (show 0 ≤ (2 : ℝ) * n by positivity)
        field_simp [hnR.ne'] at hmul
        linarith
      exact_mod_cast hleR
  · rintro ⟨hmpos, hnpos, hmle, hnle⟩
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hnpos
    refine ⟨hmpos, hnpos, ?_, ?_⟩
    · have hleR : (n : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hnle
      field_simp [hnR.ne']
      nlinarith
    · have hleR : (m : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hmle
      field_simp [hnR.ne']
      nlinarith

private lemma putnam_1999_b3_cone_tsum_eq_param (x y : ℝ) :
    (∑' p : ℕ × ℕ, if p.1 ≤ 2 * p.2 ∧ p.2 ≤ 2 * p.1 then x ^ p.1 * y ^ p.2 else 0)
      = ∑' q : Fin 3 × ℕ × ℕ,
          x ^ (putnam_1999_b3_param q).1 * y ^ (putnam_1999_b3_param q).2 := by
  let f : ℕ × ℕ → ℝ := fun p =>
    if p.1 ≤ 2 * p.2 ∧ p.2 ≤ 2 * p.1 then x ^ p.1 * y ^ p.2 else 0
  let g : Fin 3 × ℕ × ℕ → ℝ := fun q =>
    x ^ (putnam_1999_b3_param q).1 * y ^ (putnam_1999_b3_param q).2
  change (∑' p : ℕ × ℕ, f p) = ∑' q : Fin 3 × ℕ × ℕ, g q
  refine tsum_eq_tsum_of_ne_zero_bij (fun q : Function.support g => putnam_1999_b3_param q.1)
    ?hi ?hf ?hfg
  · intro a b h
    apply Subtype.ext
    exact putnam_1999_b3_param_injective h
  · intro p hp
    dsimp [f] at hp
    by_cases hcone : p.1 ≤ 2 * p.2 ∧ p.2 ≤ 2 * p.1
    · have hpne : x ^ p.1 * y ^ p.2 ≠ 0 := by
        simpa [hcone] using hp
      obtain ⟨r, k, l, hm, hn⟩ := putnam_1999_b3_exists_param_of_cone hcone.1 hcone.2
      have hparam : putnam_1999_b3_param (r, k, l) = p := by
        ext <;> simp [putnam_1999_b3_param, hm, hn]
      refine ⟨⟨(r, k, l), ?_⟩, hparam⟩
      change g (r, k, l) ≠ 0
      dsimp [g]
      rw [hparam]
      exact hpne
    · simp [hcone] at hp
  · intro q
    rcases q with ⟨q, hq⟩
    dsimp [f, g]
    have hcone :
        (putnam_1999_b3_param q).1 ≤ 2 * (putnam_1999_b3_param q).2 ∧
          (putnam_1999_b3_param q).2 ≤ 2 * (putnam_1999_b3_param q).1 := by
      rcases q with ⟨r, k, l⟩
      simp [putnam_1999_b3_param]
      constructor <;> omega
    simp [hcone]

private lemma putnam_1999_b3_param_monomial (x y : ℝ) (q : Fin 3 × ℕ × ℕ) :
    x ^ (putnam_1999_b3_param q).1 * y ^ (putnam_1999_b3_param q).2 =
      (x * y) ^ q.1.val * ((x * y ^ 2) ^ q.2.1 * ((x ^ 2 * y) ^ q.2.2)) := by
  rcases q with ⟨r, k, l⟩
  simp [putnam_1999_b3_param, pow_add, pow_mul]
  ring

private lemma putnam_1999_b3_param_tsum_eq (x y : ℝ)
    (ha : ‖x * y ^ 2‖ < 1) (hb : ‖x ^ 2 * y‖ < 1) :
    (∑' q : Fin 3 × ℕ × ℕ,
        x ^ (putnam_1999_b3_param q).1 * y ^ (putnam_1999_b3_param q).2)
      = (1 + x * y + (x * y) ^ 2) * (1 - x * y ^ 2)⁻¹ * (1 - x ^ 2 * y)⁻¹ := by
  let a : ℝ := x * y ^ 2
  let b : ℝ := x ^ 2 * y
  let c : ℝ := x * y
  have hfnorm : Summable fun r : Fin 3 => ‖c ^ r.val‖ := Summable.of_finite
  have hanorm : Summable fun n : ℕ => ‖a ^ n‖ :=
    summable_norm_geometric_of_norm_lt_one (by simpa [a] using ha)
  have hbnorm : Summable fun n : ℕ => ‖b ^ n‖ :=
    summable_norm_geometric_of_norm_lt_one (by simpa [b] using hb)
  have hg : Summable fun p : ℕ × ℕ => a ^ p.1 * b ^ p.2 :=
    summable_mul_of_summable_norm hanorm hbnorm
  have hgnorm : Summable fun p : ℕ × ℕ => ‖a ^ p.1 * b ^ p.2‖ := hg.norm
  have hprod_tsum :
      (∑' p : ℕ × ℕ, a ^ p.1 * b ^ p.2) = (1 - a)⁻¹ * (1 - b)⁻¹ := by
    rw [← tsum_mul_tsum_of_summable_norm hanorm hbnorm]
    rw [tsum_geometric_of_norm_lt_one (by simpa [a] using ha),
      tsum_geometric_of_norm_lt_one (by simpa [b] using hb)]
  have htriple :
      (∑' q : Fin 3 × ℕ × ℕ, c ^ q.1.val * (a ^ q.2.1 * b ^ q.2.2)) =
        (∑' r : Fin 3, c ^ r.val) * (∑' p : ℕ × ℕ, a ^ p.1 * b ^ p.2) := by
    rw [tsum_mul_tsum_of_summable_norm hfnorm hgnorm]
  calc
    (∑' q : Fin 3 × ℕ × ℕ,
        x ^ (putnam_1999_b3_param q).1 * y ^ (putnam_1999_b3_param q).2)
        = ∑' q : Fin 3 × ℕ × ℕ, c ^ q.1.val * (a ^ q.2.1 * b ^ q.2.2) := by
            apply tsum_congr
            intro q
            simpa [a, b, c] using putnam_1999_b3_param_monomial x y q
    _ = (∑' r : Fin 3, c ^ r.val) * (∑' p : ℕ × ℕ, a ^ p.1 * b ^ p.2) := htriple
    _ = (1 + c + c ^ 2) * ((1 - a)⁻¹ * (1 - b)⁻¹) := by
          rw [hprod_tsum]
          congr 1
          rw [tsum_fintype, Fin.sum_univ_three]
          norm_num
    _ = (1 + x * y + (x * y) ^ 2) * (1 - x * y ^ 2)⁻¹ * (1 - x ^ 2 * y)⁻¹ := by
          simp [a, b, c]
          ring

private lemma putnam_1999_b3_original_tsum_eq_cone_sub_one (x y : ℝ)
    (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    (∑' m : ℕ, ∑' n : ℕ,
        if (m > 0 ∧ n > 0 ∧ (1 : ℝ) / 2 ≤ (m : ℝ) / n ∧ (m : ℝ) / n ≤ 2)
        then x ^ m * y ^ n else 0)
      = (∑' p : ℕ × ℕ,
          if p.1 ≤ 2 * p.2 ∧ p.2 ≤ 2 * p.1 then x ^ p.1 * y ^ p.2 else 0) - 1 := by
  classical
  let fpos : ℕ × ℕ → ℝ := fun p =>
    if p.1 > 0 ∧ p.2 > 0 ∧ p.1 ≤ 2 * p.2 ∧ p.2 ≤ 2 * p.1 then
      x ^ p.1 * y ^ p.2
    else 0
  let fall : ℕ × ℕ → ℝ := fun p =>
    if p.1 ≤ 2 * p.2 ∧ p.2 ≤ 2 * p.1 then x ^ p.1 * y ^ p.2 else 0
  let sing : ℕ × ℕ → ℝ := fun p => if p = (0, 0) then 1 else 0
  have hmono : Summable fun p : ℕ × ℕ => x ^ p.1 * y ^ p.2 :=
    summable_mul_of_summable_norm (summable_norm_geometric_of_norm_lt_one hx)
      (summable_norm_geometric_of_norm_lt_one hy)
  have hpos : Summable fpos := by
    let s : Set (ℕ × ℕ) :=
      {p | p.1 > 0 ∧ p.2 > 0 ∧ p.1 ≤ 2 * p.2 ∧ p.2 ≤ 2 * p.1}
    refine (hmono.indicator s).congr ?_
    intro p
    by_cases hp : p.1 > 0 ∧ p.2 > 0 ∧ p.1 ≤ 2 * p.2 ∧ p.2 ≤ 2 * p.1
    · simp [s, fpos, Set.indicator, hp]
    · simp [s, fpos, Set.indicator, hp]
  have hfall : Summable fall := by
    let s : Set (ℕ × ℕ) := {p | p.1 ≤ 2 * p.2 ∧ p.2 ≤ 2 * p.1}
    refine (hmono.indicator s).congr ?_
    intro p
    by_cases hp : p.1 ≤ 2 * p.2 ∧ p.2 ≤ 2 * p.1
    · simp [s, fall, Set.indicator, hp]
    · simp [s, fall, Set.indicator, hp]
  have hsing : Summable sing := by
    refine summable_of_finite_support ((Set.finite_singleton ((0, 0) : ℕ × ℕ)).subset ?_)
    intro p hp
    by_cases h : p = (0, 0)
    · simp [h]
    · exfalso
      apply hp
      simp [sing, h]
  have hpoint : ∀ p : ℕ × ℕ, fpos p = fall p - sing p := by
    intro p
    rcases p with ⟨m, n⟩
    dsimp [fpos, fall, sing]
    by_cases h0 : (m, n) = ((0, 0) : ℕ × ℕ)
    · injection h0 with hm hn
      subst m
      subst n
      simp
    · have h0' : ¬(m = 0 ∧ n = 0) := by simpa using h0
      by_cases hcone : m ≤ 2 * n ∧ n ≤ 2 * m
      · have hm : m > 0 := by omega
        have hn : n > 0 := by omega
        rw [if_pos ⟨hm, hn, hcone.1, hcone.2⟩, if_pos hcone, if_neg h0]
        ring
      · have hnot : ¬(m > 0 ∧ n > 0 ∧ m ≤ 2 * n ∧ n ≤ 2 * m) := by tauto
        rw [if_neg hnot, if_neg hcone, if_neg h0]
        ring
  have hiter :
      (∑' m : ℕ, ∑' n : ℕ,
        if (m > 0 ∧ n > 0 ∧ (1 : ℝ) / 2 ≤ (m : ℝ) / n ∧ (m : ℝ) / n ≤ 2)
        then x ^ m * y ^ n else 0)
        = ∑' m : ℕ, ∑' n : ℕ, fpos (m, n) := by
    apply tsum_congr
    intro m
    apply tsum_congr
    intro n
    dsimp [fpos]
    by_cases h : m > 0 ∧ n > 0 ∧ m ≤ 2 * n ∧ n ≤ 2 * m
    · have hr :
          m > 0 ∧ n > 0 ∧ (1 : ℝ) / 2 ≤ (m : ℝ) / n ∧ (m : ℝ) / n ≤ 2 :=
        putnam_1999_b3_ratio_iff_cone.mpr h
      rw [if_pos hr, if_pos h]
    · have hr :
          ¬(m > 0 ∧ n > 0 ∧ (1 : ℝ) / 2 ≤ (m : ℝ) / n ∧ (m : ℝ) / n ≤ 2) := by
        intro hr
        exact h (putnam_1999_b3_ratio_iff_cone.mp hr)
      rw [if_neg hr, if_neg h]
  calc
    (∑' m : ℕ, ∑' n : ℕ,
        if (m > 0 ∧ n > 0 ∧ (1 : ℝ) / 2 ≤ (m : ℝ) / n ∧ (m : ℝ) / n ≤ 2)
        then x ^ m * y ^ n else 0)
        = ∑' m : ℕ, ∑' n : ℕ, fpos (m, n) := hiter
    _ = ∑' p : ℕ × ℕ, fpos p := hpos.tsum_prod.symm
    _ = ∑' p : ℕ × ℕ, (fall p - sing p) := by
          apply tsum_congr
          intro p
          rw [hpoint]
    _ = (∑' p : ℕ × ℕ, fall p) - (∑' p : ℕ × ℕ, sing p) := hfall.tsum_sub hsing
    _ = (∑' p : ℕ × ℕ, fall p) - 1 := by
          congr 1
          simp [sing, tsum_ite_eq ((0, 0) : ℕ × ℕ) (fun _ : ℕ × ℕ => (1 : ℝ))]
    _ = (∑' p : ℕ × ℕ,
          if p.1 ≤ 2 * p.2 ∧ p.2 ≤ 2 * p.1 then x ^ p.1 * y ^ p.2 else 0) - 1 := rfl

private lemma putnam_1999_b3_norm_factors_lt_one {x y : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    ‖x * y ^ 2‖ < 1 ∧ ‖x ^ 2 * y‖ < 1 := by
  have hy2lt : y ^ 2 < 1 := by
    simpa [sq] using (mul_lt_mul'' hy1 hy1 hy0 hy0)
  have hx2lt : x ^ 2 < 1 := by
    simpa [sq] using (mul_lt_mul'' hx1 hx1 hx0 hx0)
  have hxy2_nonneg : 0 ≤ x * y ^ 2 := by positivity
  have hx2y_nonneg : 0 ≤ x ^ 2 * y := by positivity
  have hxy2lt : x * y ^ 2 < 1 := by
    simpa using (mul_lt_mul'' hx1 hy2lt hx0 (sq_nonneg y))
  have hx2ylt : x ^ 2 * y < 1 := by
    simpa [mul_comm] using (mul_lt_mul'' hx2lt hy1 (sq_nonneg x) hy0)
  constructor
  · rw [Real.norm_of_nonneg hxy2_nonneg]
    exact hxy2lt
  · rw [Real.norm_of_nonneg hx2y_nonneg]
    exact hx2ylt

private lemma putnam_1999_b3_one_sub_ne_zero_of_norm_lt_one {a : ℝ} (ha : ‖a‖ < 1) :
    1 - a ≠ 0 := by
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, norm_one] at ha
    norm_num at ha
  exact sub_ne_zero.mpr (Ne.symm ha1)

abbrev putnam_1999_b3_solution : ℝ := 3

/--
Let $A=\{(x,y):0\leq x,y<1\}$.  For $(x,y)\in A$, let \[S(x,y) = \sum_{\frac{1}{2}\leq \frac{m}{n}\leq 2} x^m y^n,\] where the sum ranges over all pairs $(m,n)$ of positive integers satisfying the indicated inequalities.  Evaluate \[\lim_{(x,y)\rightarrow (1,1), (x,y)\in A} (1-xy^2)(1-x^2y)S(x,y).\]
-/
theorem putnam_1999_b3
(A : Set (ℝ × ℝ))
(hA : A = {xy | 0 ≤ xy.1 ∧ xy.1 < 1 ∧ 0 ≤ xy.2 ∧ xy.2 < 1})
(S : ℝ → ℝ → ℝ)
(hS : S = fun x y => ∑' m : ℕ, ∑' n : ℕ, if (m > 0 ∧ n > 0 ∧ (1 : ℝ)/2 ≤ (m : ℝ)/n ∧ (m : ℝ)/n ≤ 2) then x^m * y^n else 0)
: Tendsto (fun xy : (ℝ × ℝ) => (1 - xy.1 * xy.2^2) * (1 - xy.1^2 * xy.2) * (S xy.1 xy.2)) (𝓝[A] ⟨1,1⟩) (𝓝 putnam_1999_b3_solution) :=
by
  let F : ℝ × ℝ → ℝ := fun xy =>
    (1 - xy.1 * xy.2 ^ 2) * (1 - xy.1 ^ 2 * xy.2) * (S xy.1 xy.2)
  let G : ℝ × ℝ → ℝ := fun xy =>
    1 + xy.1 * xy.2 + (xy.1 * xy.2) ^ 2 -
      (1 - xy.1 * xy.2 ^ 2) * (1 - xy.1 ^ 2 * xy.2)
  have hG_tendsto : Tendsto G (𝓝[A] (⟨1, 1⟩ : ℝ × ℝ)) (𝓝 (3 : ℝ)) := by
    have hcont : ContinuousAt G (⟨1, 1⟩ : ℝ × ℝ) := by
      dsimp [G]
      fun_prop
    have hlim : Tendsto G (𝓝[A] (⟨1, 1⟩ : ℝ × ℝ)) (𝓝 (G (⟨1, 1⟩ : ℝ × ℝ))) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hGval : G (⟨1, 1⟩ : ℝ × ℝ) = 3 := by norm_num [G]
    simpa [hGval, G] using hlim
  have hFG : F =ᶠ[𝓝[A] (⟨1, 1⟩ : ℝ × ℝ)] G := by
    filter_upwards [eventually_mem_nhdsWithin] with xy hxyA
    let x : ℝ := xy.1
    let y : ℝ := xy.2
    have hmem : 0 ≤ x ∧ x < 1 ∧ 0 ≤ y ∧ y < 1 := by
      simpa [hA, x, y] using hxyA
    rcases hmem with ⟨hx0, hx1, hy0, hy1⟩
    have hxnorm : ‖x‖ < 1 := by
      rw [Real.norm_of_nonneg hx0]
      exact hx1
    have hynorm : ‖y‖ < 1 := by
      rw [Real.norm_of_nonneg hy0]
      exact hy1
    have hfac := putnam_1999_b3_norm_factors_lt_one hx0 hx1 hy0 hy1
    have hsum :
      S x y =
          (1 + x * y + (x * y) ^ 2) * (1 - x * y ^ 2)⁻¹ * (1 - x ^ 2 * y)⁻¹ - 1 := by
      rw [hS]
      change
        (∑' m : ℕ, ∑' n : ℕ,
          if (m > 0 ∧ n > 0 ∧ (1 : ℝ) / 2 ≤ (m : ℝ) / n ∧ (m : ℝ) / n ≤ 2)
          then x ^ m * y ^ n else 0)
          = (1 + x * y + (x * y) ^ 2) * (1 - x * y ^ 2)⁻¹ *
              (1 - x ^ 2 * y)⁻¹ - 1
      rw [putnam_1999_b3_original_tsum_eq_cone_sub_one x y hxnorm hynorm]
      rw [putnam_1999_b3_cone_tsum_eq_param x y]
      rw [putnam_1999_b3_param_tsum_eq x y hfac.1 hfac.2]
    have hane : 1 - x * y ^ 2 ≠ 0 :=
      putnam_1999_b3_one_sub_ne_zero_of_norm_lt_one hfac.1
    have hbne : 1 - x ^ 2 * y ≠ 0 :=
      putnam_1999_b3_one_sub_ne_zero_of_norm_lt_one hfac.2
    change
      (1 - x * y ^ 2) * (1 - x ^ 2 * y) * S x y =
        1 + x * y + (x * y) ^ 2 - (1 - x * y ^ 2) * (1 - x ^ 2 * y)
    rw [hsum]
    field_simp [hane, hbne]
  simpa [putnam_1999_b3_solution, F] using Filter.Tendsto.congr' hFG.symm hG_tendsto
