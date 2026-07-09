import Mathlib

open Topology Filter

private lemma multiset_amgm (m : Multiset ℝ) (hm : ∀ x ∈ m, 0 ≤ x) (hpos : 0 < m.card) :
    m.prod ^ (m.card : ℝ)⁻¹ ≤ m.sum / (m.card : ℝ) := by
  let l := m.toList
  have hlenpos : 0 < l.length := by simpa [l, Multiset.length_toList] using hpos
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin l.length)), 0 ≤ (1 : ℝ) := by
    simp
  have hwpos : 0 < ∑ i ∈ (Finset.univ : Finset (Fin l.length)), (1 : ℝ) := by
    simp [hlenpos]
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin l.length)), 0 ≤ l[i.1] := by
    intro i _hi
    have hmeml : l[i.1] ∈ l := List.getElem_mem i.2
    have hmemtl : l[i.1] ∈ m.toList := by simp [l] at hmeml ⊢
    exact hm l[i.1] ((Multiset.mem_toList).mp hmemtl)
  have h := Real.geom_mean_le_arith_mean (Finset.univ : Finset (Fin l.length))
    (fun _ => (1 : ℝ)) (fun i : Fin l.length => l[i.1]) hw hwpos hz
  simpa [l, Fin.prod_univ_getElem, Fin.sum_univ_getElem, Multiset.prod_toList,
    Multiset.sum_toList, Multiset.length_toList, Real.rpow_one] using h

private lemma complex_norm_eq_re_of_im_zero_of_nonneg {z : ℂ} (him : z.im = 0)
    (hre : 0 ≤ z.re) : ‖z‖ = z.re := by
  let r : ℝ := z.re
  have hr : 0 ≤ r := by simpa [r] using hre
  have hz : z = (r : ℂ) := by
    apply Complex.ext
    · simp [r]
    · simp [r, him]
  change ‖z‖ = r
  rw [hz]
  exact Complex.norm_of_nonneg hr

private lemma roots_norm_prod_eq_coeff (p : Polynomial ℂ) (hnat : p.natDegree = 2019) :
    ‖p.coeff 0‖ = ‖p.coeff 2019‖ * (p.roots.map fun z => ‖z‖).prod := by
  have hsplit : p.Splits := IsAlgClosed.splits p
  have heval := Polynomial.Splits.eval_eq_prod_roots (f := p) hsplit (0 : ℂ)
  have hlead : p.leadingCoeff = p.coeff 2019 := by
    rw [← Polynomial.coeff_natDegree, hnat]
  calc
    ‖p.coeff 0‖ = ‖Polynomial.eval 0 p‖ := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
    _ = ‖p.leadingCoeff * (p.roots.map fun x => (0 : ℂ) - x).prod‖ := by
      rw [heval]
    _ = ‖p.leadingCoeff‖ * ‖(p.roots.map fun x => (0 : ℂ) - x).prod‖ := by
      rw [norm_mul]
    _ = ‖p.coeff 2019‖ * (p.roots.map fun z => ‖z‖).prod := by
      rw [hlead]
      congr 1
      calc
        ‖(p.roots.map fun x => (0 : ℂ) - x).prod‖ =
            (Multiset.map (fun z : ℂ => ‖z‖) (p.roots.map fun x => (0 : ℂ) - x)).prod := by
          exact map_multiset_prod Complex.isAbsoluteValueNorm.abvHom
            (p.roots.map fun x => (0 : ℂ) - x)
        _ = (p.roots.map fun z => ‖z‖).prod := by
          congr 1
          ext z
          simp [norm_neg]

private lemma geom_coeff (q : ℝ) (n : ℕ) :
    ((∑ k ∈ Finset.range 2020, Polynomial.C ((q ^ k : ℝ) : ℂ) * Polynomial.X ^ k :
        Polynomial ℂ).coeff n) =
      if n < 2020 then ((q ^ n : ℝ) : ℂ) else 0 := by
  by_cases hn : n < 2020
  · rw [if_pos hn]
    simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single n]
    · simp
    · intro b _hb hbn
      rw [if_neg hbn.symm]
    · intro hnmem
      exact False.elim (hnmem (Finset.mem_range.mpr hn))
  · rw [if_neg hn]
    simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_zero]
    intro k hk
    have hkn : n ≠ k := by
      intro h
      apply hn
      simpa [← h] using hk
    rw [if_neg hkn]

-- 2019^(-(1:ℝ)/2019)
/--
Given real numbers $b_0, b_1, \dots, b_{2019}$ with $b_{2019} \neq 0$, let $z_1,z_2,\dots,z_{2019}$ be
the roots in the complex plane of the polynomial
\[
P(z) = \sum_{k=0}^{2019} b_k z^k.
\]
Let $\mu = (|z_1| + \cdots + |z_{2019}|)/2019$ be the average of the distances from $z_1,z_2,\dots,z_{2019}$ to the origin. Determine the largest constant $M$ such that $\mu \geq M$ for all choices of $b_0,b_1,\dots, b_{2019}$ that satisfy
\[
1 \leq b_0 < b_1 < b_2 < \cdots < b_{2019} \leq 2019.
\]
-/
theorem putnam_2019_a3
  (v : Polynomial ℂ → Prop)
  (hv : v = fun b => b.degree = 2019 ∧ 1 ≤ (b.coeff 0).re ∧ (b.coeff 2019).re ≤ 2019 ∧
    (∀ i : Fin 2020, (b.coeff i).im = 0) ∧ (∀ i : Fin 2019, (b.coeff i).re < (b.coeff (i + 1)).re))
  (μ : Polynomial ℂ → ℝ)
  (hμ : μ = fun b => (Multiset.map (fun ω : ℂ => ‖ω‖) (Polynomial.roots b)).sum/2019) :
  IsGreatest {M : ℝ | ∀ b, v b → μ b ≥ M} ((2019^(-(1:ℝ)/2019)) : ℝ ) := by
  let r : ℝ := (2019 : ℝ) ^ (-(1 : ℝ) / 2019)
  change IsGreatest {M : ℝ | ∀ b, v b → μ b ≥ M} r
  constructor
  · intro b hb
    rw [hv] at hb
    rcases hb with ⟨hdeg, hb0, hb2019, hbim, hbinc⟩
    rw [hμ]
    let m : Multiset ℝ := b.roots.map fun ω : ℂ => ‖ω‖
    change r ≤ m.sum / 2019
    have hnat : b.natDegree = 2019 := Polynomial.natDegree_eq_of_degree_eq_some hdeg
    have hcard : m.card = 2019 := by
      simp [m, Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits b), hnat]
    have hmnonneg : ∀ x ∈ m, 0 ≤ x := by
      intro x hx
      simp [m] at hx
      rcases hx with ⟨z, _hz, rfl⟩
      exact norm_nonneg z
    have hamgm := multiset_amgm m hmnonneg (by rw [hcard]; norm_num)
    have hmono_nat : ∀ n ≤ 2019, (b.coeff 0).re ≤ (b.coeff n).re := by
      intro n hn
      induction n with
      | zero =>
          simp
      | succ n ih =>
          have hnle : n ≤ 2019 := Nat.le_of_succ_le hn
          have hnlt : n < 2019 := Nat.lt_of_succ_le hn
          have hstep : (b.coeff n).re < (b.coeff (n + 1)).re := by
            simpa using hbinc ⟨n, hnlt⟩
          exact (ih hnle).trans (le_of_lt hstep)
    have hlead_nonneg : 0 ≤ (b.coeff 2019).re := by
      exact (by norm_num : (0 : ℝ) ≤ 1).trans (hb0.trans (hmono_nat 2019 (by norm_num)))
    have hcoeff0_norm : ‖b.coeff 0‖ = (b.coeff 0).re :=
      complex_norm_eq_re_of_im_zero_of_nonneg (hbim ⟨0, by norm_num⟩)
        ((by norm_num : (0 : ℝ) ≤ 1).trans hb0)
    have hcoeff2019_norm : ‖b.coeff 2019‖ = (b.coeff 2019).re :=
      complex_norm_eq_re_of_im_zero_of_nonneg (hbim ⟨2019, by norm_num⟩) hlead_nonneg
    have hprod_eq : (b.coeff 0).re = (b.coeff 2019).re * m.prod := by
      have h := roots_norm_prod_eq_coeff b hnat
      simpa [hcoeff0_norm, hcoeff2019_norm] using h
    have hprod_nonneg : 0 ≤ m.prod := Multiset.prod_nonneg hmnonneg
    have h1_le_2019prod : 1 ≤ (2019 : ℝ) * m.prod := by
      have h1_le_leadprod : 1 ≤ (b.coeff 2019).re * m.prod := by
        rw [← hprod_eq]
        exact hb0
      exact h1_le_leadprod.trans (mul_le_mul_of_nonneg_right hb2019 hprod_nonneg)
    have hprod_ge : (2019 : ℝ)⁻¹ ≤ m.prod := by
      rw [inv_le_iff_one_le_mul₀ (by norm_num : (0 : ℝ) < 2019)]
      rwa [mul_comm]
    have hconst :
        ((2019 : ℝ)⁻¹) ^ ((2019 : ℝ)⁻¹) = r := by
      dsimp [r]
      rw [Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2019)]
      rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2019)]
      congr 1
      norm_num [div_eq_mul_inv]
    have hprod_rpow : r ≤ m.prod ^ ((2019 : ℝ)⁻¹) := by
      rw [← hconst]
      exact Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ (2019 : ℝ)⁻¹) hprod_ge
        (by norm_num : (0 : ℝ) ≤ (2019 : ℝ)⁻¹)
    have hamgm2019 : m.prod ^ ((2019 : ℝ)⁻¹) ≤ m.sum / 2019 := by
      simpa [hcard] using hamgm
    exact hprod_rpow.trans hamgm2019
  · intro M hM
    let q : ℝ := (2019 : ℝ) ^ ((2019 : ℝ)⁻¹)
    let p : Polynomial ℂ :=
      ∑ k ∈ Finset.range 2020, Polynomial.C ((q ^ k : ℝ) : ℂ) * Polynomial.X ^ k
    have hqpos : 0 < q := by
      dsimp [q]
      exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2019) ((2019 : ℝ)⁻¹)
    have hqnonneg : 0 ≤ q := le_of_lt hqpos
    have hqgt1 : 1 < q := by
      dsimp [q]
      exact Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2019)
        (by norm_num : (0 : ℝ) < (2019 : ℝ)⁻¹)
    have hqpow : q ^ 2019 = (2019 : ℝ) := by
      dsimp [q]
      simpa using Real.rpow_inv_natCast_pow (x := (2019 : ℝ)) (n := 2019)
        (by norm_num : (0 : ℝ) ≤ 2019) (by norm_num : (2019 : ℕ) ≠ 0)
    have hcoeff : ∀ n : ℕ, p.coeff n = if n < 2020 then ((q ^ n : ℝ) : ℂ) else 0 := by
      intro n
      simpa [p] using geom_coeff q n
    have hpcoeff2019 : p.coeff 2019 = ((2019 : ℝ) : ℂ) := by
      rw [hcoeff 2019, if_pos (by norm_num : 2019 < 2020), hqpow]
    have hpcoeff2019_ne : p.coeff 2019 ≠ 0 := by
      rw [hpcoeff2019]
      norm_num
    have hnatle : p.natDegree ≤ 2019 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [hcoeff N, if_neg]
      omega
    have hnatdegp : p.natDegree = 2019 :=
      Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hnatle hpcoeff2019_ne
    have hp_ne : p ≠ 0 := by
      intro hp
      have hbad : p.coeff 2019 = 0 := by
        simpa using congrArg (fun f : Polynomial ℂ => f.coeff 2019) hp
      rw [hpcoeff2019] at hbad
      norm_num at hbad
    have hdegp : p.degree = 2019 := (Polynomial.degree_eq_iff_natDegree_eq hp_ne).2 hnatdegp
    have hpv : v p := by
      rw [hv]
      refine ⟨hdegp, ?_, ?_, ?_, ?_⟩
      · have hp0 : p.coeff 0 = (1 : ℂ) := by
          rw [hcoeff 0, if_pos (by norm_num : 0 < 2020)]
          simp
        rw [hp0]
        norm_num
      · rw [hpcoeff2019]
        norm_num
      · intro i
        rw [hcoeff i, if_pos i.2]
        simpa [Complex.ofReal_pow] using (Complex.ofReal_im (q ^ (i : ℕ)))
      · intro i
        have hi : (i : ℕ) < 2020 := by omega
        have hi1 : (i : ℕ) + 1 < 2020 := by omega
        rw [hcoeff i, if_pos hi, hcoeff (i + 1), if_pos hi1]
        simp only [Complex.ofReal_re]
        exact pow_lt_pow_right₀ hqgt1 (Nat.lt_succ_self (i : ℕ))
    have hcardp : p.roots.card = 2019 := by
      rw [Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits p), hnatdegp]
    have hqinv : q⁻¹ = r := by
      change ((2019 : ℝ) ^ ((2019 : ℝ)⁻¹))⁻¹ = (2019 : ℝ) ^ (-(1 : ℝ) / 2019)
      rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2019)]
      norm_num [div_eq_mul_inv]
    have hrootnorm : ∀ z ∈ p.roots, ‖z‖ = r := by
      intro z hz
      have hroot : p.IsRoot z := (Polynomial.mem_roots hp_ne).mp hz
      have heval_zero : Polynomial.eval z p = 0 := Polynomial.IsRoot.def.mp hroot
      have heval_geom : Polynomial.eval z p =
          ∑ k ∈ Finset.range 2020, (((q : ℂ) * z) ^ k) := by
        simp [p, Polynomial.eval_finset_sum, mul_pow]
      have hsum0 : (∑ k ∈ Finset.range 2020, (((q : ℂ) * z) ^ k)) = 0 := by
        rw [← heval_geom]
        exact heval_zero
      have hgeom := geom_sum_mul ((q : ℂ) * z) 2020
      have hpow_sub : ((q : ℂ) * z) ^ 2020 - 1 = 0 := by
        rw [← hgeom, hsum0, zero_mul]
      have hpow : ((q : ℂ) * z) ^ 2020 = 1 := sub_eq_zero.mp hpow_sub
      have hnormpow : (q * ‖z‖) ^ 2020 = (1 : ℝ) ^ 2020 := by
        have hnorm : ‖(((q : ℂ) * z) ^ 2020)‖ = ‖(1 : ℂ)‖ :=
          congrArg (fun w : ℂ => ‖w‖) hpow
        rw [Complex.norm_pow] at hnorm
        rw [norm_mul, Complex.norm_of_nonneg hqnonneg] at hnorm
        simpa using hnorm
      have hqnorm : q * ‖z‖ = 1 := by
        exact (pow_left_inj₀ (mul_nonneg hqnonneg (norm_nonneg z)) zero_le_one
          (by norm_num : (2020 : ℕ) ≠ 0)).mp hnormpow
      exact (eq_inv_of_mul_eq_one_right hqnorm).trans hqinv
    have hsumroots : (p.roots.map fun z : ℂ => ‖z‖).sum = 2019 * r := by
      have hmap : p.roots.map (fun z : ℂ => ‖z‖) =
          Multiset.replicate p.roots.card r := by
        rw [← Multiset.map_const p.roots r]
        exact Multiset.map_congr rfl hrootnorm
      rw [hmap, hcardp, Multiset.sum_replicate]
      norm_num [nsmul_eq_mul]
    have hmup : μ p = r := by
      rw [hμ]
      change (p.roots.map (fun z : ℂ => ‖z‖)).sum / 2019 = r
      rw [hsumroots]
      norm_num
    have hMp := hM p hpv
    rw [hmup] at hMp
    exact hMp
