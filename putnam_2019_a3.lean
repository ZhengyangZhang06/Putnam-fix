import Mathlib

open Topology Filter

noncomputable abbrev putnam_2019_a3_solution : ℝ :=
  Real.exp (-(Real.log (2019 : ℝ) / 2019))

private noncomputable def putnam_2019_a3_qR : ℝ :=
  (2019 : ℝ) ^ ((1 : ℝ) / 2019)

private noncomputable def putnam_2019_a3_q : ℂ :=
  (putnam_2019_a3_qR : ℂ)

private noncomputable def putnam_2019_a3_poly : Polynomial ℂ :=
  Polynomial.ofFn 2020 (fun i : Fin 2020 => putnam_2019_a3_q ^ (i : ℕ))

private lemma putnam_2019_a3_lower_bound (b : Polynomial ℂ)
    (hb : b.degree = 2019 ∧ 1 ≤ (b.coeff 0).re ∧ (b.coeff 2019).re ≤ 2019 ∧
      (∀ i : Fin 2020, (b.coeff i).im = 0) ∧
      (∀ i : Fin 2019, (b.coeff i).re < (b.coeff (i + 1)).re)) :
    (Multiset.map (fun ω : ℂ => ‖ω‖) b.roots).sum / 2019 ≥
      putnam_2019_a3_solution := by
  classical
  rcases hb with ⟨hdeg, hb0, htop, him, hinc⟩
  have hnat : b.natDegree = 2019 := Polynomial.natDegree_eq_of_degree_eq_some hdeg
  have hcard : b.roots.card = 2019 := by
    have h := (IsAlgClosed.splits b).natDegree_eq_card_roots
    rw [hnat] at h
    exact h.symm
  have hre_ge_one : ∀ n : ℕ, n ≤ 2019 → 1 ≤ (b.coeff n).re := by
    intro n hn
    induction n with
    | zero => simpa using hb0
    | succ n ih =>
        have hnlt : n < 2019 := Nat.lt_of_succ_le hn
        have hprev : 1 ≤ (b.coeff n).re := ih (Nat.le_of_lt hnlt)
        have hstep : (b.coeff n).re < (b.coeff (n + 1)).re := by
          simpa using hinc ⟨n, hnlt⟩
        exact hprev.trans hstep.le
  have htop_ge1 : 1 ≤ (b.coeff 2019).re := hre_ge_one 2019 le_rfl
  have htop_pos : 0 < (b.coeff 2019).re := lt_of_lt_of_le zero_lt_one htop_ge1
  have hcoeff0_real : b.coeff 0 = ((b.coeff 0).re : ℂ) := by
    rw [← Complex.re_add_im (b.coeff 0)]
    simp [him ⟨0, by norm_num⟩]
  have hcoeff2019_real : b.coeff 2019 = ((b.coeff 2019).re : ℂ) := by
    rw [← Complex.re_add_im (b.coeff 2019)]
    simp [him ⟨2019, by norm_num⟩]
  have hlead_eq : b.leadingCoeff = b.coeff 2019 := by
    rw [Polynomial.leadingCoeff, hnat]
  have hlead_real : b.leadingCoeff = ((b.coeff 2019).re : ℂ) :=
    hlead_eq.trans hcoeff2019_real
  have hnorm0 : ‖b.coeff 0‖ = (b.coeff 0).re := by
    rw [hcoeff0_real]
    exact Complex.norm_of_nonneg (zero_le_one.trans hb0)
  have hnormlead : ‖b.leadingCoeff‖ = (b.coeff 2019).re := by
    rw [hlead_real]
    exact Complex.norm_of_nonneg htop_pos.le
  have hlead_norm_ne : ‖b.leadingCoeff‖ ≠ 0 := by
    rw [hnormlead]
    exact ne_of_gt htop_pos
  have hvieta := (IsAlgClosed.splits b).coeff_zero_eq_leadingCoeff_mul_prod_roots
  have hnorm_coeff : ‖b.coeff 0‖ = ‖b.leadingCoeff‖ * ‖b.roots.prod‖ := by
    rw [hvieta, norm_mul, norm_mul]
    simp
  have hprod_roots_eq : ‖b.roots.prod‖ = ‖b.coeff 0‖ / ‖b.leadingCoeff‖ := by
    rw [eq_div_iff hlead_norm_ne]
    rw [mul_comm]
    exact hnorm_coeff.symm
  have hprod_norms_eq :
      (Multiset.map (fun z : ℂ => ‖z‖) b.roots).prod = ‖b.roots.prod‖ := by
    simpa using (map_multiset_prod (normHom : ℂ →*₀ ℝ) b.roots).symm
  have hratio : (1 : ℝ) / 2019 ≤ (b.coeff 0).re / (b.coeff 2019).re := by
    have h1 : (1 : ℝ) / 2019 ≤ 1 / (b.coeff 2019).re := by
      exact one_div_le_one_div_of_le htop_pos htop
    have h2 : 1 / (b.coeff 2019).re ≤
        (b.coeff 0).re / (b.coeff 2019).re := by
      exact div_le_div_of_nonneg_right hb0 htop_pos.le
    exact h1.trans h2
  let s : Multiset ℝ := Multiset.map (fun z : ℂ => ‖z‖) b.roots
  have hprod_ge : (1 : ℝ) / 2019 ≤ s.prod := by
    dsimp [s]
    rw [hprod_norms_eq, hprod_roots_eq, hnorm0, hnormlead]
    exact hratio
  let l : List ℝ := s.toList
  have hlen : l.length = 2019 := by
    dsimp [l, s]
    rw [Multiset.length_toList, Multiset.card_map, hcard]
  have h_nonneg : ∀ i : Fin l.length, 0 ≤ l[i] := by
    intro i
    have hmem : l[i] ∈ l := List.getElem_mem i.2
    have hmems : l[i] ∈ s := by
      simpa [l] using (Multiset.mem_toList.mp hmem)
    rcases Multiset.mem_map.mp hmems with ⟨z, _hz, hval⟩
    rw [← hval]
    exact norm_nonneg z
  have hamgm := Real.geom_mean_le_arith_mean (Finset.univ : Finset (Fin l.length))
    (fun _ => (1 : ℝ)) (fun i => l[i])
    (by intro i hi; norm_num)
    (by simp [hlen])
    (by intro i hi; exact h_nonneg i)
  have hamgm' : l.prod ^ ((l.length : ℝ)⁻¹) ≤ l.sum / (l.length : ℝ) := by
    simpa [Fin.prod_univ_getElem, Fin.sum_univ_getElem, Finset.card_univ,
      Fintype.card_fin] using hamgm
  have hprod_ge_l : (1 : ℝ) / 2019 ≤ l.prod := by
    dsimp [l]
    rw [Multiset.prod_toList]
    exact hprod_ge
  have hpow_ge : ((1 : ℝ) / 2019) ^ ((1 : ℝ) / 2019) ≤
      l.prod ^ ((1 : ℝ) / 2019) := by
    exact Real.rpow_le_rpow (by norm_num) hprod_ge_l (by norm_num)
  have hmean_ge0 : ((1 : ℝ) / 2019) ^ ((1 : ℝ) / 2019) ≤
      l.sum / 2019 := by
    have hamgm2019 : l.prod ^ ((1 : ℝ) / 2019) ≤ l.sum / 2019 := by
      simpa [hlen, one_div] using hamgm'
    exact hpow_ge.trans hamgm2019
  have hsum_eq : l.sum = s.sum := by
    dsimp [l]
    exact Multiset.sum_toList s
  have hmean_ge : ((1 : ℝ) / 2019) ^ ((1 : ℝ) / 2019) ≤ s.sum / 2019 := by
    simpa [hsum_eq] using hmean_ge0
  have hsol_eq : putnam_2019_a3_solution =
      ((1 : ℝ) / 2019) ^ ((1 : ℝ) / 2019) := by
    rw [putnam_2019_a3_solution]
    rw [one_div]
    rw [Real.rpow_def_of_pos (by positivity : 0 < (2019 : ℝ)⁻¹)]
    rw [Real.log_inv]
    congr
    ring_nf
  dsimp [s] at hmean_ge
  rw [hsol_eq]
  exact hmean_ge

private lemma putnam_2019_a3_witness_valid :
    putnam_2019_a3_poly.degree = 2019 ∧
      1 ≤ (putnam_2019_a3_poly.coeff 0).re ∧
      (putnam_2019_a3_poly.coeff 2019).re ≤ 2019 ∧
      (∀ i : Fin 2020, (putnam_2019_a3_poly.coeff i).im = 0) ∧
      (∀ i : Fin 2019,
        (putnam_2019_a3_poly.coeff i).re <
          (putnam_2019_a3_poly.coeff (i + 1)).re) := by
  classical
  have hqpos : 0 < putnam_2019_a3_qR := by
    dsimp [putnam_2019_a3_qR]
    positivity
  have hqnonneg : 0 ≤ putnam_2019_a3_qR := hqpos.le
  have hqpowR : putnam_2019_a3_qR ^ 2019 = (2019 : ℝ) := by
    dsimp [putnam_2019_a3_qR]
    simpa using
      (Real.rpow_inv_natCast_pow (x := (2019 : ℝ)) (n := 2019)
        (by norm_num) (by norm_num))
  have hqpowC : putnam_2019_a3_q ^ 2019 = (2019 : ℂ) := by
    dsimp [putnam_2019_a3_q]
    rw [← Complex.ofReal_pow, hqpowR]
    norm_num
  have hqgt : 1 < putnam_2019_a3_qR := by
    by_contra hnot
    have hle : putnam_2019_a3_qR ≤ 1 := le_of_not_gt hnot
    have hpowle : putnam_2019_a3_qR ^ 2019 ≤ (1 : ℝ) ^ 2019 :=
      pow_le_pow_left₀ hqnonneg hle 2019
    rw [hqpowR] at hpowle
    norm_num at hpowle
  have hcoeff_real (n : ℕ) (hn : n < 2020) :
      putnam_2019_a3_poly.coeff n = (putnam_2019_a3_qR ^ n : ℂ) := by
    have hcoeff : putnam_2019_a3_poly.coeff n = putnam_2019_a3_q ^ n := by
      simpa [putnam_2019_a3_poly] using
        Polynomial.ofFn_coeff_eq_val_of_lt (R := ℂ)
          (v := fun j : Fin 2020 => putnam_2019_a3_q ^ (j : ℕ)) hn
    exact hcoeff
  have hnat : putnam_2019_a3_poly.natDegree = 2019 := by
    refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      have h2020 : 2020 ≤ N := by omega
      simpa [putnam_2019_a3_poly] using
        Polynomial.ofFn_coeff_eq_zero_of_ge (R := ℂ)
          (v := fun i : Fin 2020 => putnam_2019_a3_q ^ (i : ℕ)) h2020
    · have : putnam_2019_a3_poly.coeff 2019 = (2019 : ℂ) := by
        rw [hcoeff_real 2019 (by norm_num)]
        rw [← Complex.ofReal_pow, hqpowR]
        norm_num
      rw [this]
      norm_num
  have hdeg : putnam_2019_a3_poly.degree = 2019 :=
    (Polynomial.degree_eq_iff_natDegree_eq_of_pos (p := putnam_2019_a3_poly)
      (n := 2019) (by norm_num)).2 hnat
  refine ⟨hdeg, ?_, ?_, ?_, ?_⟩
  · rw [hcoeff_real 0 (by norm_num)]
    norm_num
  · rw [hcoeff_real 2019 (by norm_num)]
    rw [← Complex.ofReal_pow, hqpowR]
    norm_num
  · intro i
    rw [hcoeff_real i i.2]
    simp [← Complex.ofReal_pow]
  · intro i
    have hi0 : (i : ℕ) < 2020 := by omega
    have hi1 : (i : ℕ) + 1 < 2020 := by omega
    rw [hcoeff_real i hi0, hcoeff_real ((i : ℕ) + 1) hi1]
    simpa [← Complex.ofReal_pow] using
      pow_lt_pow_right₀ hqgt (Nat.lt_succ_self (i : ℕ))

private lemma putnam_2019_a3_witness_root_norm (z : ℂ)
    (hz : putnam_2019_a3_poly.IsRoot z) :
    ‖z‖ = putnam_2019_a3_solution := by
  classical
  have hqpos : 0 < putnam_2019_a3_qR := by
    dsimp [putnam_2019_a3_qR]
    positivity
  have hqnonneg : 0 ≤ putnam_2019_a3_qR := hqpos.le
  have hqne : putnam_2019_a3_qR ≠ 0 := ne_of_gt hqpos
  have hnat : putnam_2019_a3_poly.natDegree = 2019 :=
    Polynomial.natDegree_eq_of_degree_eq_some putnam_2019_a3_witness_valid.1
  have hgeom0 :
      ∑ i ∈ Finset.range 2020, (putnam_2019_a3_q * z) ^ i = 0 := by
    rw [Polynomial.IsRoot.def] at hz
    have heval := hz
    rw [Polynomial.eval_eq_sum_range] at heval
    rw [hnat] at heval
    have hsum :
        ∑ i ∈ Finset.range (2019 + 1),
            putnam_2019_a3_poly.coeff i * z ^ i =
          ∑ i ∈ Finset.range 2020, (putnam_2019_a3_q * z) ^ i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi2020 : i < 2020 := by simpa using Finset.mem_range.mp hi
      have hcoeff : putnam_2019_a3_poly.coeff i = putnam_2019_a3_q ^ i := by
        simpa [putnam_2019_a3_poly] using
          Polynomial.ofFn_coeff_eq_val_of_lt (R := ℂ)
            (v := fun j : Fin 2020 => putnam_2019_a3_q ^ (j : ℕ)) hi2020
      rw [hcoeff, mul_pow]
    norm_num at heval ⊢
    simpa [hsum] using heval
  have hwpow : (putnam_2019_a3_q * z) ^ 2020 = 1 := by
    have h := geom_sum_mul (putnam_2019_a3_q * z) 2020
    rw [hgeom0, zero_mul] at h
    exact sub_eq_zero.mp h.symm
  have hnormw : ‖putnam_2019_a3_q * z‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hwpow (by norm_num)
  have hnormq : ‖putnam_2019_a3_q‖ = putnam_2019_a3_qR := by
    dsimp [putnam_2019_a3_q]
    exact Complex.norm_of_nonneg hqnonneg
  have hmulnorm : putnam_2019_a3_qR * ‖z‖ = 1 := by
    simpa [norm_mul, hnormq] using hnormw
  have hz_norm : ‖z‖ = putnam_2019_a3_qR⁻¹ := by
    calc
      ‖z‖ = putnam_2019_a3_qR⁻¹ * (putnam_2019_a3_qR * ‖z‖) := by
        rw [← mul_assoc, inv_mul_cancel₀ hqne, one_mul]
      _ = putnam_2019_a3_qR⁻¹ := by rw [hmulnorm, mul_one]
  rw [hz_norm]
  rw [putnam_2019_a3_solution]
  dsimp [putnam_2019_a3_qR]
  rw [Real.rpow_def_of_pos (by norm_num : 0 < (2019 : ℝ))]
  rw [← Real.exp_neg]
  apply Real.exp_injective
  ring_nf

private lemma putnam_2019_a3_witness_mu :
    (Multiset.map (fun ω : ℂ => ‖ω‖) putnam_2019_a3_poly.roots).sum / 2019 =
      putnam_2019_a3_solution := by
  classical
  have hnat : putnam_2019_a3_poly.natDegree = 2019 :=
    Polynomial.natDegree_eq_of_degree_eq_some putnam_2019_a3_witness_valid.1
  have hBne : putnam_2019_a3_poly ≠ 0 := by
    intro hzero
    have hdeg0 : putnam_2019_a3_poly.natDegree = 0 := by simp [hzero]
    omega
  have hcard : putnam_2019_a3_poly.roots.card = 2019 := by
    have h := (IsAlgClosed.splits putnam_2019_a3_poly).natDegree_eq_card_roots
    rw [hnat] at h
    exact h.symm
  have hmap : Multiset.map (fun ω : ℂ => ‖ω‖) putnam_2019_a3_poly.roots =
      Multiset.replicate
        (Multiset.card (Multiset.map (fun ω : ℂ => ‖ω‖) putnam_2019_a3_poly.roots))
        putnam_2019_a3_solution := by
    rw [Multiset.eq_replicate_card]
    intro r hr
    rcases Multiset.mem_map.mp hr with ⟨z, hz, rfl⟩
    exact putnam_2019_a3_witness_root_norm z ((Polynomial.mem_roots hBne).mp hz)
  rw [hmap, Multiset.sum_replicate, Multiset.card_map, hcard]
  norm_num

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
  IsGreatest {M : ℝ | ∀ b, v b → μ b ≥ M} putnam_2019_a3_solution :=
by
  subst v
  subst μ
  refine ⟨?_, ?_⟩
  · intro b hb
    exact putnam_2019_a3_lower_bound b hb
  · intro M hM
    have hMle := hM putnam_2019_a3_poly putnam_2019_a3_witness_valid
    simpa [putnam_2019_a3_witness_mu] using hMle
