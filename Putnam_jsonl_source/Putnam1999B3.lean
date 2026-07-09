import Mathlib

open Filter Topology Metric

-- 3
/--
Let $A=\{(x,y):0\leq x,y<1\}$.  For $(x,y)\in A$, let \[S(x,y) = \sum_{\frac{1}{2}\leq \frac{m}{n}\leq 2} x^m y^n,\] where the sum ranges over all pairs $(m,n)$ of positive integers satisfying the indicated inequalities.  Evaluate \[\lim_{(x,y)\rightarrow (1,1), (x,y)\in A} (1-xy^2)(1-x^2y)S(x,y).\]
-/
theorem putnam_1999_b3
(A : Set (ℝ × ℝ))
(hA : A = {xy | 0 ≤ xy.1 ∧ xy.1 < 1 ∧ 0 ≤ xy.2 ∧ xy.2 < 1})
(S : ℝ → ℝ → ℝ)
(hS : S = fun x y => ∑' m : ℕ, ∑' n : ℕ, if (m > 0 ∧ n > 0 ∧ (1 : ℝ)/2 ≤ (m : ℝ)/n ∧ (m : ℝ)/n ≤ 2) then x^m * y^n else 0)
: Tendsto (fun xy : (ℝ × ℝ) => (1 - xy.1 * xy.2^2) * (1 - xy.1^2 * xy.2) * (S xy.1 xy.2)) (𝓝[A] ⟨1,1⟩) (𝓝 ((3) : ℝ )) := by
  classical
  have tsum_pos :
      ∀ r : ℝ, 0 ≤ r → r < 1 →
        (∑' n : ℕ, if n > 0 then r^n else 0) = r * (1 - r)⁻¹ := by
    intro r hr0 hr1
    have hnorm : ‖r‖ < 1 := by
      rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
    have hgeom : Summable fun n : ℕ => r^n := summable_geometric_of_norm_lt_one hnorm
    have hf : Summable fun n : ℕ => if n > 0 then r^n else 0 := by
      convert hgeom.indicator {n : ℕ | n > 0} using 1
      funext n
      rw [Set.indicator_apply]
      rfl
    calc
      (∑' n : ℕ, if n > 0 then r^n else 0)
          = (if (0 : ℕ) > 0 then r^0 else 0) +
              ∑' n : ℕ, (if n + 1 > 0 then r^(n + 1) else 0) := by
                exact hf.tsum_eq_zero_add
      _ = ∑' n : ℕ, r^(n + 1) := by simp
      _ = ∑' n : ℕ, r * r^n := by
        apply tsum_congr
        intro n
        rw [pow_succ']
      _ = r * (∑' n : ℕ, r^n) := by rw [tsum_mul_left]
      _ = r * (1 - r)⁻¹ := by rw [tsum_geometric_of_norm_lt_one hnorm]
  have tsum_tail :
      ∀ r : ℝ, 0 ≤ r → r < 1 → ∀ K : ℕ,
        (∑' n : ℕ, if n > K then r^n else 0) = r^(K + 1) * (1 - r)⁻¹ := by
    intro r hr0 hr1 K
    have hnorm : ‖r‖ < 1 := by
      rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
    have hshift :
        (∑' n : ℕ, if n > K then r^n else 0) = ∑' k : ℕ, r^(k + (K + 1)) := by
      let f : ℕ → ℝ := fun n => if n > K then r^n else 0
      let g : ℕ → ℝ := fun k => r^(k + (K + 1))
      change (∑' n : ℕ, f n) = ∑' k : ℕ, g k
      refine tsum_eq_tsum_of_ne_zero_bij
        (fun k : ↑(Function.support g) => k.1 + (K + 1)) ?inj ?surj ?eq
      · intro a b h
        apply Subtype.ext
        exact Nat.add_right_cancel h
      · intro n hn
        simp only [Function.support] at hn ⊢
        have hgt : n > K := by
          by_contra h
          have : f n = 0 := by simp [f, h]
          exact hn this
        have hle : K + 1 ≤ n := Nat.succ_le_iff.mpr hgt
        rcases Nat.exists_eq_add_of_le' hle with ⟨k, hk⟩
        refine ⟨⟨k, ?_⟩, ?_⟩
        · have hfne : r^n ≠ 0 := by
            simpa [f, hgt] using hn
          simpa [g, hk] using hfne
        · exact hk.symm
      · intro k
        have hgt : k.1 + (K + 1) > K := by omega
        simp [f, g, hgt]
    calc
      (∑' n : ℕ, if n > K then r^n else 0) = ∑' k : ℕ, r^(k + (K + 1)) := hshift
      _ = ∑' k : ℕ, r^k * r^(K + 1) := by
        apply tsum_congr
        intro k
        rw [pow_add]
      _ = (∑' k : ℕ, r^k) * r^(K + 1) := by rw [tsum_mul_right]
      _ = (1 - r)⁻¹ * r^(K + 1) := by rw [tsum_geometric_of_norm_lt_one hnorm]
      _ = r^(K + 1) * (1 - r)⁻¹ := by ring
  have summable_if :
      ∀ (x y : ℝ), 0 ≤ x → x < 1 → 0 ≤ y → y < 1 →
        ∀ (P : ℕ × ℕ → Prop), [DecidablePred P] →
          Summable fun p : ℕ × ℕ => if P p then x^p.1 * y^p.2 else 0 := by
    intro x y hx0 hx1 hy0 hy1 P hP
    have hxnorm : ‖x‖ < 1 := by
      rwa [Real.norm_eq_abs, abs_of_nonneg hx0]
    have hynorm : ‖y‖ < 1 := by
      rwa [Real.norm_eq_abs, abs_of_nonneg hy0]
    have hxsum : Summable fun n : ℕ => x^n := summable_geometric_of_norm_lt_one hxnorm
    have hysum : Summable fun n : ℕ => y^n := summable_geometric_of_norm_lt_one hynorm
    have hprod : Summable fun p : ℕ × ℕ => x^p.1 * y^p.2 :=
      hxsum.mul_of_nonneg hysum (fun n => pow_nonneg hx0 n) (fun n => pow_nonneg hy0 n)
    convert hprod.indicator {p : ℕ × ℕ | P p} using 1
    funext p
    rw [Set.indicator_apply]
    rfl
  have closed_form :
      ∀ xy ∈ A,
        (1 - xy.1 * xy.2^2) * (1 - xy.1^2 * xy.2) * (S xy.1 xy.2) =
          xy.1 * xy.2 * ((1 + xy.1) * (1 + xy.2) - xy.1^2 * xy.2^2) := by
    intro xy hxyA
    have hmem : 0 ≤ xy.1 ∧ xy.1 < 1 ∧ 0 ≤ xy.2 ∧ xy.2 < 1 := by
      simpa [hA] using hxyA
    set x : ℝ := xy.1
    set y : ℝ := xy.2
    have hx0 : 0 ≤ x := by simpa [x] using hmem.1
    have hx1 : x < 1 := by simpa [x] using hmem.2.1
    have hy0 : 0 ≤ y := by simpa [y] using hmem.2.2.1
    have hy1 : y < 1 := by simpa [y] using hmem.2.2.2
    have hxy20 : 0 ≤ x * y^2 := by positivity
    have hxy21 : x * y^2 < 1 := by
      have hy2lt : y^2 < 1 := by nlinarith [sq_nonneg y, sq_nonneg (y - 1)]
      have hle : x * y^2 ≤ 1 * y^2 := mul_le_mul_of_nonneg_right hx1.le (sq_nonneg y)
      nlinarith
    have hx2y0 : 0 ≤ x^2 * y := by positivity
    have hx2y1 : x^2 * y < 1 := by
      have hx2lt : x^2 < 1 := by nlinarith [sq_nonneg x, sq_nonneg (x - 1)]
      have hle : x^2 * y ≤ x^2 * 1 := mul_le_mul_of_nonneg_left hy1.le (sq_nonneg x)
      nlinarith
    let fP : ℕ × ℕ → ℝ := fun p =>
      if p.1 > 0 ∧ p.2 > 0 ∧ (2 : ℝ)⁻¹ ≤ (p.1 : ℝ) / p.2 ∧ (p.1 : ℝ) / p.2 ≤ 2
      then x^p.1 * y^p.2 else 0
    let fAll : ℕ × ℕ → ℝ := fun p =>
      if p.1 > 0 ∧ p.2 > 0 then x^p.1 * y^p.2 else 0
    let fHi : ℕ × ℕ → ℝ := fun p =>
      if p.1 > 0 ∧ p.2 > 0 ∧ (2 : ℝ) < (p.1 : ℝ) / p.2
      then x^p.1 * y^p.2 else 0
    let fLo : ℕ × ℕ → ℝ := fun p =>
      if p.1 > 0 ∧ p.2 > 0 ∧ (p.1 : ℝ) / p.2 < (2 : ℝ)⁻¹
      then x^p.1 * y^p.2 else 0
    have hP : Summable fP := by
      dsimp [fP]
      exact summable_if x y hx0 hx1 hy0 hy1
        (fun p : ℕ × ℕ =>
          p.1 > 0 ∧ p.2 > 0 ∧ (2 : ℝ)⁻¹ ≤ (p.1 : ℝ) / p.2 ∧
            (p.1 : ℝ) / p.2 ≤ 2)
    have hAll : Summable fAll := by
      dsimp [fAll]
      exact summable_if x y hx0 hx1 hy0 hy1
        (fun p : ℕ × ℕ => p.1 > 0 ∧ p.2 > 0)
    have hHi : Summable fHi := by
      dsimp [fHi]
      exact summable_if x y hx0 hx1 hy0 hy1
        (fun p : ℕ × ℕ => p.1 > 0 ∧ p.2 > 0 ∧ (2 : ℝ) < (p.1 : ℝ) / p.2)
    have hLo : Summable fLo := by
      dsimp [fLo]
      exact summable_if x y hx0 hx1 hy0 hy1
        (fun p : ℕ × ℕ => p.1 > 0 ∧ p.2 > 0 ∧ (p.1 : ℝ) / p.2 < (2 : ℝ)⁻¹)
    have hsplit : ∀ p : ℕ × ℕ, fP p = fAll p - fHi p - fLo p := by
      intro p
      dsimp [fP, fAll, fHi, fLo]
      by_cases hpos : p.1 > 0 ∧ p.2 > 0
      · by_cases hlow : (2 : ℝ)⁻¹ ≤ (p.1 : ℝ) / p.2
        · by_cases hhigh : (p.1 : ℝ) / p.2 ≤ 2
          · have hnhi : ¬ (2 : ℝ) < (p.1 : ℝ) / p.2 := not_lt.mpr hhigh
            have hnlo : ¬ (p.1 : ℝ) / p.2 < (2 : ℝ)⁻¹ := not_lt.mpr hlow
            simp [hpos, hlow, hhigh, hnhi, hnlo]
          · have hhi : (2 : ℝ) < (p.1 : ℝ) / p.2 := lt_of_not_ge hhigh
            have hnlo : ¬ (p.1 : ℝ) / p.2 < (2 : ℝ)⁻¹ := not_lt.mpr hlow
            simp [hpos, hlow, hhigh, hhi, hnlo]
        · have hlo : (p.1 : ℝ) / p.2 < (2 : ℝ)⁻¹ := lt_of_not_ge hlow
          have hnhi : ¬ (2 : ℝ) < (p.1 : ℝ) / p.2 := by
            intro hhi
            have : (2 : ℝ)⁻¹ < (2 : ℝ) := by norm_num
            linarith
          simp [hpos, hlow, hlo, hnhi]
      · have hnP :
            ¬ (p.1 > 0 ∧ p.2 > 0 ∧ (2 : ℝ)⁻¹ ≤ (p.1 : ℝ) / p.2 ∧
              (p.1 : ℝ) / p.2 ≤ 2) := by
          intro h
          exact hpos ⟨h.1, h.2.1⟩
        have hnHi : ¬ (p.1 > 0 ∧ p.2 > 0 ∧ (2 : ℝ) < (p.1 : ℝ) / p.2) := by
          intro h
          exact hpos ⟨h.1, h.2.1⟩
        have hnLo : ¬ (p.1 > 0 ∧ p.2 > 0 ∧ (p.1 : ℝ) / p.2 < (2 : ℝ)⁻¹) := by
          intro h
          exact hpos ⟨h.1, h.2.1⟩
        simp [hpos, hnP, hnHi, hnLo]
    have hAll_eval :
        (∑' p : ℕ × ℕ, fAll p) = (x * (1 - x)⁻¹) * (y * (1 - y)⁻¹) := by
      rw [hAll.tsum_prod]
      dsimp [fAll]
      calc
        (∑' m : ℕ, ∑' n : ℕ, if m > 0 ∧ n > 0 then x^m * y^n else 0)
            = ∑' m : ℕ, if m > 0 then x^m * (∑' n : ℕ, if n > 0 then y^n else 0) else 0 := by
              apply tsum_congr
              intro m
              by_cases hm : m > 0
              · simp only [hm, true_and, if_true]
                calc
                  (∑' n : ℕ, if n > 0 then x^m * y^n else 0)
                      = ∑' n : ℕ, x^m * (if n > 0 then y^n else 0) := by
                        apply tsum_congr
                        intro n
                        by_cases hn : n > 0 <;> simp [hn]
                  _ = x^m * (∑' n : ℕ, if n > 0 then y^n else 0) := by rw [tsum_mul_left]
              · simp [hm]
        _ = ∑' m : ℕ, (if m > 0 then x^m else 0) * (y * (1 - y)⁻¹) := by
          rw [tsum_pos y hy0 hy1]
          apply tsum_congr
          intro m
          by_cases hm : m > 0 <;> simp [hm]
        _ = (∑' m : ℕ, if m > 0 then x^m else 0) * (y * (1 - y)⁻¹) := by rw [tsum_mul_right]
        _ = (x * (1 - x)⁻¹) * (y * (1 - y)⁻¹) := by rw [tsum_pos x hx0 hx1]
    have hLo_eval :
        (∑' p : ℕ × ℕ, fLo p) =
          (y * (1 - y)⁻¹) * ((x * y^2) * (1 - x * y^2)⁻¹) := by
      rw [hLo.tsum_prod]
      dsimp [fLo]
      calc
        (∑' m : ℕ, ∑' n : ℕ,
            if m > 0 ∧ n > 0 ∧ (m : ℝ) / n < (2 : ℝ)⁻¹ then x^m * y^n else 0)
            = ∑' m : ℕ, if m > 0 then x^m * (∑' n : ℕ, if n > 2 * m then y^n else 0) else 0 := by
              apply tsum_congr
              intro m
              by_cases hm : m > 0
              · simp only [hm, true_and, if_true]
                calc
                  (∑' n : ℕ, if n > 0 ∧ (m : ℝ) / n < (2 : ℝ)⁻¹ then x^m * y^n else 0)
                      = ∑' n : ℕ, x^m * (if n > 2 * m then y^n else 0) := by
                        apply tsum_congr
                        intro n
                        have hiff : (n > 0 ∧ (m : ℝ) / n < (2 : ℝ)⁻¹) ↔ n > 2 * m := by
                          constructor
                          · intro h
                            have hnpos_nat : 0 < n := h.1
                            have hnpos : (0 : ℝ) < n := by exact_mod_cast hnpos_nat
                            have hlt : (m : ℝ) < ((2 : ℝ)⁻¹) * n := (div_lt_iff₀ hnpos).1 h.2
                            have h2 : (2 : ℝ) * m < n := by nlinarith
                            exact_mod_cast h2
                          · intro h
                            have hnpos_nat : 0 < n := by omega
                            have hnpos : (0 : ℝ) < n := by exact_mod_cast hnpos_nat
                            constructor
                            · exact hnpos_nat
                            · rw [div_lt_iff₀ hnpos]
                              have h2 : (2 : ℝ) * m < n := by exact_mod_cast h
                              nlinarith
                        by_cases hcond : n > 0 ∧ (m : ℝ) / n < (2 : ℝ)⁻¹
                        · have hn : n > 2 * m := hiff.mp hcond
                          simp [hcond, hn]
                        · have hn : ¬ n > 2 * m := fun hn => hcond (hiff.mpr hn)
                          simp [hcond, hn]
                  _ = x^m * (∑' n : ℕ, if n > 2 * m then y^n else 0) := by rw [tsum_mul_left]
              · simp [hm]
        _ = ∑' m : ℕ, if m > 0 then x^m * (y^(2 * m + 1) * (1 - y)⁻¹) else 0 := by
          apply tsum_congr
          intro m
          by_cases hm : m > 0 <;> simp [hm, tsum_tail y hy0 hy1 (2 * m)]
        _ = ∑' m : ℕ, (y * (1 - y)⁻¹) * (if m > 0 then (x * y^2)^m else 0) := by
          apply tsum_congr
          intro m
          by_cases hm : m > 0
          · simp [hm]
            calc
              x^m * (y^(2 * m + 1) * (1 - y)⁻¹) = (x^m * y^(2 * m + 1)) * (1 - y)⁻¹ := by ring
              _ = (y * (x * y^2)^m) * (1 - y)⁻¹ := by
                rw [show x^m * y^(2 * m + 1) = y * (x * y^2)^m by
                  rw [pow_add]
                  simp only [pow_one]
                  rw [mul_pow, pow_mul]
                  ring]
              _ = (y * (1 - y)⁻¹) * (x * y^2)^m := by ring
          · simp [hm]
        _ = (y * (1 - y)⁻¹) * (∑' m : ℕ, if m > 0 then (x * y^2)^m else 0) := by rw [tsum_mul_left]
        _ = (y * (1 - y)⁻¹) * ((x * y^2) * (1 - x * y^2)⁻¹) := by
          rw [tsum_pos (x * y^2) hxy20 hxy21]
    have hHi_uncurry :
        Summable (Function.uncurry
          (fun m n : ℕ =>
            if m > 0 ∧ n > 0 ∧ (2 : ℝ) < (m : ℝ) / n then x^m * y^n else 0)) := by
      simpa [Function.uncurry, fHi] using hHi
    have hHi_eval :
        (∑' p : ℕ × ℕ, fHi p) =
          (x * (1 - x)⁻¹) * ((x^2 * y) * (1 - x^2 * y)⁻¹) := by
      rw [hHi.tsum_prod]
      dsimp [fHi]
      rw [← (Summable.tsum_comm
        (f := fun m n : ℕ =>
          if m > 0 ∧ n > 0 ∧ (2 : ℝ) < (m : ℝ) / n then x^m * y^n else 0) hHi_uncurry)]
      calc
        (∑' n : ℕ, ∑' m : ℕ,
            if m > 0 ∧ n > 0 ∧ (2 : ℝ) < (m : ℝ) / n then x^m * y^n else 0)
            = ∑' n : ℕ, if n > 0 then y^n * (∑' m : ℕ, if m > 2 * n then x^m else 0) else 0 := by
              apply tsum_congr
              intro n
              by_cases hn : n > 0
              · calc
                  (∑' m : ℕ, if m > 0 ∧ n > 0 ∧ (2 : ℝ) < (m : ℝ) / n then x^m * y^n else 0)
                      = ∑' m : ℕ, (if m > 2 * n then x^m else 0) * y^n := by
                        apply tsum_congr
                        intro m
                        have hiff : (m > 0 ∧ (2 : ℝ) < (m : ℝ) / n) ↔ m > 2 * n := by
                          constructor
                          · intro h
                            have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
                            have hlt : (2 : ℝ) * n < m := by
                              have := (lt_div_iff₀ hnpos).1 h.2
                              simpa [mul_comm] using this
                            exact_mod_cast hlt
                          · intro h
                            have hmpos : 0 < m := by omega
                            constructor
                            · exact hmpos
                            · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
                              rw [lt_div_iff₀ hnpos]
                              have h2 : (2 : ℝ) * n < m := by exact_mod_cast h
                              simpa [mul_comm] using h2
                        by_cases hcond : m > 0 ∧ (2 : ℝ) < (m : ℝ) / n
                        · have hmgt : m > 2 * n := hiff.mp hcond
                          have hfull : m > 0 ∧ n > 0 ∧ (2 : ℝ) < (m : ℝ) / n := ⟨hcond.1, hn, hcond.2⟩
                          simp [hfull, hmgt]
                        · have hmgt : ¬ m > 2 * n := fun hmgt => hcond (hiff.mpr hmgt)
                          have hfull : ¬ (m > 0 ∧ n > 0 ∧ (2 : ℝ) < (m : ℝ) / n) := by
                            intro h
                            exact hcond ⟨h.1, h.2.2⟩
                          simp [hfull, hmgt]
                  _ = (∑' m : ℕ, if m > 2 * n then x^m else 0) * y^n := by rw [tsum_mul_right]
                  _ = y^n * (∑' m : ℕ, if m > 2 * n then x^m else 0) := by ring
                  _ = (if n > 0 then y^n * (∑' m : ℕ, if m > 2 * n then x^m else 0) else 0) := by simp [hn]
              · simp [hn]
        _ = ∑' n : ℕ, if n > 0 then y^n * (x^(2 * n + 1) * (1 - x)⁻¹) else 0 := by
          apply tsum_congr
          intro n
          by_cases hn : n > 0 <;> simp [hn, tsum_tail x hx0 hx1 (2 * n)]
        _ = ∑' n : ℕ, (x * (1 - x)⁻¹) * (if n > 0 then (x^2 * y)^n else 0) := by
          apply tsum_congr
          intro n
          by_cases hn : n > 0
          · simp [hn]
            calc
              y^n * (x^(2 * n + 1) * (1 - x)⁻¹) = (y^n * x^(2 * n + 1)) * (1 - x)⁻¹ := by ring
              _ = (x * (x^2 * y)^n) * (1 - x)⁻¹ := by
                rw [show y^n * x^(2 * n + 1) = x * (x^2 * y)^n by
                  rw [pow_add]
                  simp only [pow_one]
                  rw [mul_pow, pow_mul]
                  ring]
              _ = (x * (1 - x)⁻¹) * (x^2 * y)^n := by ring
          · simp [hn]
        _ = (x * (1 - x)⁻¹) * (∑' n : ℕ, if n > 0 then (x^2 * y)^n else 0) := by rw [tsum_mul_left]
        _ = (x * (1 - x)⁻¹) * ((x^2 * y) * (1 - x^2 * y)⁻¹) := by
          rw [tsum_pos (x^2 * y) hx2y0 hx2y1]
    have hSsum :
        S x y = (∑' p : ℕ × ℕ, fAll p) - (∑' p : ℕ × ℕ, fHi p) - (∑' p : ℕ × ℕ, fLo p) := by
      calc
        S x y =
            (∑' m : ℕ, ∑' n : ℕ,
              if (m > 0 ∧ n > 0 ∧ (1 : ℝ) / 2 ≤ (m : ℝ) / n ∧ (m : ℝ) / n ≤ 2)
              then x^m * y^n else 0) := by rw [hS]
        _ = ∑' p : ℕ × ℕ, fP p := by
          calc
            (∑' m : ℕ, ∑' n : ℕ,
              if (m > 0 ∧ n > 0 ∧ (1 : ℝ) / 2 ≤ (m : ℝ) / n ∧ (m : ℝ) / n ≤ 2)
              then x^m * y^n else 0)
                = ∑' m : ℕ, ∑' n : ℕ, fP (m, n) := by
                  apply tsum_congr
                  intro m
                  apply tsum_congr
                  intro n
                  dsimp [fP]
                  simp [one_div]
            _ = ∑' p : ℕ × ℕ, fP p := (hP.tsum_prod).symm
        _ = ∑' p : ℕ × ℕ, (fAll p - fHi p - fLo p) := by
          apply tsum_congr
          exact hsplit
        _ = (∑' p : ℕ × ℕ, fAll p) - (∑' p : ℕ × ℕ, fHi p) - (∑' p : ℕ × ℕ, fLo p) := by
          rw [Summable.tsum_sub (hAll.sub hHi) hLo]
          rw [Summable.tsum_sub hAll hHi]
    have hS_eval :
        S x y =
          (x * (1 - x)⁻¹) * (y * (1 - y)⁻¹) -
          (x * (1 - x)⁻¹) * ((x^2 * y) * (1 - x^2 * y)⁻¹) -
          (y * (1 - y)⁻¹) * ((x * y^2) * (1 - x * y^2)⁻¹) := by
      rw [hSsum, hAll_eval, hHi_eval, hLo_eval]
    have hxne : 1 - x ≠ 0 := by nlinarith
    have hyne : 1 - y ≠ 0 := by nlinarith
    have hxy2ne : 1 - x * y^2 ≠ 0 := by nlinarith
    have hx2yne : 1 - x^2 * y ≠ 0 := by nlinarith
    change (1 - x * y^2) * (1 - x^2 * y) * S x y =
      x * y * ((1 + x) * (1 + y) - x^2 * y^2)
    rw [hS_eval]
    field_simp [hxne, hyne, hxy2ne, hx2yne]
    ring
  have hpoly :
      Tendsto
        (fun xy : ℝ × ℝ =>
          xy.1 * xy.2 * ((1 + xy.1) * (1 + xy.2) - xy.1^2 * xy.2^2))
        (𝓝[A] ⟨1, 1⟩) (𝓝 (3 : ℝ)) := by
    have hcont :
        ContinuousAt
          (fun xy : ℝ × ℝ =>
            xy.1 * xy.2 * ((1 + xy.1) * (1 + xy.2) - xy.1^2 * xy.2^2))
          ⟨1, 1⟩ := by
      fun_prop
    have hval :
        (fun xy : ℝ × ℝ =>
          xy.1 * xy.2 * ((1 + xy.1) * (1 + xy.2) - xy.1^2 * xy.2^2))
          ⟨1, 1⟩ = (3 : ℝ) := by norm_num
    rw [← hval]
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  exact hpoly.congr'
    (eventually_nhdsWithin_of_forall fun xy hxy => (closed_form xy hxy).symm)
