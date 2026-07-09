import Mathlib

open Nat Set MeasureTheory Topology Filter

private def putnam_1973_a2_coeff (a : Fin 8 → ℝ) (n : ℕ) : ℝ :=
  a ⟨n % 8, Nat.mod_lt n (by norm_num)⟩

private lemma putnam_1973_a2_sum_pm_one {α : Type*} [Fintype α] (f : α → ℝ)
    (hf : ∀ i, f i = 1 ∨ f i = -1) :
    (∑ i, f i) =
      2 * ((Finset.univ.filter fun i => f i = 1).card : ℝ) - (Fintype.card α : ℝ) := by
  classical
  calc
    (∑ i, f i) = ∑ i, (if f i = 1 then (1 : ℝ) else -1) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rcases hf i with h | h <;> simp [h]
    _ = ∑ i, (2 * (if f i = 1 then (1 : ℝ) else 0) - 1) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      by_cases h : f i = 1 <;> norm_num [h]
    _ = 2 * (∑ i, (if f i = 1 then (1 : ℝ) else 0)) - ∑ _i : α, (1 : ℝ) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = 2 * ((Finset.univ.filter fun i => f i = 1).card : ℝ) -
        (Fintype.card α : ℝ) := by
      rw [← Finset.natCast_card_filter]
      simp

private lemma putnam_1973_a2_coeff_period (a : Fin 8 → ℝ) (q x : ℕ) :
    putnam_1973_a2_coeff a (8 * q + x) = putnam_1973_a2_coeff a x := by
  simp [putnam_1973_a2_coeff, Nat.add_mod, Nat.mul_mod_right]

private lemma putnam_1973_a2_coeff_block_sum (a : Fin 8 → ℝ) :
    (∑ i ∈ Finset.range 8, putnam_1973_a2_coeff a i) = ∑ j : Fin 8, a j := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => putnam_1973_a2_coeff a i) 8]
  simp [putnam_1973_a2_coeff, Fin.sum_univ_eight]

private lemma putnam_1973_a2_coeff_shift_block_sum (a : Fin 8 → ℝ) :
    (∑ i ∈ Finset.range 8, putnam_1973_a2_coeff a (i + 1)) = ∑ j : Fin 8, a j := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => putnam_1973_a2_coeff a (i + 1)) 8]
  simp [putnam_1973_a2_coeff, Fin.sum_univ_eight]
  ring_nf

private lemma putnam_1973_a2_full_blocks_zero (a : Fin 8 → ℝ)
    (hzero : ∑ j : Fin 8, a j = 0) :
    ∀ q : ℕ, (∑ i ∈ Finset.range (8 * q), putnam_1973_a2_coeff a i) = 0 := by
  intro q
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih, zero_add]
      calc
        (∑ x ∈ Finset.range 8, putnam_1973_a2_coeff a (8 * q + x)) =
            ∑ x ∈ Finset.range 8, putnam_1973_a2_coeff a x := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          exact putnam_1973_a2_coeff_period a q x
        _ = 0 := by
          rw [putnam_1973_a2_coeff_block_sum, hzero]

private lemma putnam_1973_a2_partial_sums_bounded (a : Fin 8 → ℝ)
    (hzero : ∑ j : Fin 8, a j = 0) :
    ∀ n : ℕ,
      ‖∑ i ∈ Finset.range n, putnam_1973_a2_coeff a i‖ ≤
        ∑ i ∈ Finset.range 8, ‖putnam_1973_a2_coeff a i‖ := by
  intro n
  let q := n / 8
  let r := n % 8
  have hrle : r ≤ 8 := by
    exact (Nat.mod_lt n (by norm_num : 0 < 8)).le
  have hn : n = 8 * q + r := by
    dsimp [q, r]
    rw [Nat.div_add_mod]
  rw [hn, Finset.sum_range_add, putnam_1973_a2_full_blocks_zero a hzero q, zero_add]
  calc
    ‖∑ x ∈ Finset.range r, putnam_1973_a2_coeff a (8 * q + x)‖ ≤
        ∑ x ∈ Finset.range r, ‖putnam_1973_a2_coeff a (8 * q + x)‖ :=
      norm_sum_le _ _
    _ = ∑ x ∈ Finset.range r, ‖putnam_1973_a2_coeff a x‖ := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      rw [putnam_1973_a2_coeff_period a q x]
    _ ≤ ∑ x ∈ Finset.range 8, ‖putnam_1973_a2_coeff a x‖ := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        ((Finset.range_subset_range).2 hrle)
        (by intro x hx8 hxr; exact norm_nonneg _)

private lemma putnam_1973_a2_zero_mean_converges (a : Fin 8 → ℝ)
    (hzero : ∑ j : Fin 8, a j = 0) :
    ∃ l : ℝ,
      Tendsto (fun n : ℕ =>
        ∑ i ∈ Finset.Icc 1 n, putnam_1973_a2_coeff a i / (i : ℝ)) atTop (𝓝 l) := by
  let f : ℕ → ℝ := fun n => (1 : ℝ) / (n + 1 : ℕ)
  let z : ℕ → ℝ := fun n => putnam_1973_a2_coeff a (n + 1)
  have hanti : Antitone f := by
    intro m n hmn
    dsimp [f]
    gcongr
  have hf0 : Tendsto f atTop (𝓝 0) := by
    simpa [f] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hzb : ∀ n : ℕ, ‖∑ i ∈ Finset.range n, z i‖ ≤ ∑ i ∈ Finset.range 8, ‖z i‖ := by
    intro n
    let b : Fin 8 → ℝ := fun j => putnam_1973_a2_coeff a (j.val + 1)
    have hbzero : ∑ j : Fin 8, b j = 0 := by
      have hshift : (∑ j : Fin 8, b j) = ∑ j : Fin 8, a j := by
        dsimp [b]
        rw [Fin.sum_univ_eq_sum_range (fun i => putnam_1973_a2_coeff a (i + 1)) 8]
        exact putnam_1973_a2_coeff_shift_block_sum a
      exact hshift.trans hzero
    have hb := putnam_1973_a2_partial_sums_bounded b hbzero n
    have hsum_eq : (∑ i ∈ Finset.range n, z i) =
        ∑ i ∈ Finset.range n, putnam_1973_a2_coeff b i := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp [z, b, putnam_1973_a2_coeff]
    have hbound_eq : (∑ i ∈ Finset.range 8, ‖z i‖) =
        ∑ i ∈ Finset.range 8, ‖putnam_1973_a2_coeff b i‖ := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp [z, b, putnam_1973_a2_coeff]
    rwa [hsum_eq, hbound_eq]
  have hcau := hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0 hzb
  rcases cauchySeq_tendsto_of_complete hcau with ⟨l, hl⟩
  refine ⟨l, ?_⟩
  refine hl.congr' (Eventually.of_forall ?_)
  intro n
  symm
  change (∑ i ∈ Finset.Icc 1 n, putnam_1973_a2_coeff a i / (i : ℝ)) =
    ∑ i ∈ Finset.range n, f i • z i
  rw [← Finset.Ico_add_one_right_eq_Icc]
  rw [Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro k hk
  simp [f, z, Nat.add_comm, Nat.cast_add, div_eq_mul_inv, mul_comm]

private lemma putnam_1973_a2_harmonic_Icc_atTop :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.Icc 1 n, (1 : ℝ) / (i : ℝ)) atTop atTop := by
  have h := Real.tendsto_sum_range_one_div_nat_succ_atTop
  refine h.congr' (Eventually.of_forall ?_)
  intro n
  symm
  change (∑ i ∈ Finset.Icc 1 n, (1 : ℝ) / (i : ℝ)) =
    ∑ i ∈ Finset.range n, (1 : ℝ) / ((i : ℝ) + 1)
  rw [← Finset.Ico_add_one_right_eq_Icc]
  rw [Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro k hk
  simp [Nat.add_comm, Nat.cast_add]

private lemma putnam_1973_a2_harmonic_scaled_not_convergent (c : ℝ) (hc : c ≠ 0) :
    ¬ ∃ l : ℝ,
      Tendsto (fun n : ℕ => c * ∑ i ∈ Finset.Icc 1 n, (1 : ℝ) / (i : ℝ)) atTop (𝓝 l) := by
  rintro ⟨l, hl⟩
  rcases lt_or_gt_of_ne hc.symm with hcpos | hcneg
  · exact not_tendsto_nhds_of_tendsto_atTop
      (Tendsto.const_mul_atTop hcpos putnam_1973_a2_harmonic_Icc_atTop) l hl
  · exact not_tendsto_nhds_of_tendsto_atBot
      ((Filter.tendsto_const_mul_atBot_of_neg hcneg).2 putnam_1973_a2_harmonic_Icc_atTop) l hl

private lemma putnam_1973_a2_total_zero_of_converges (a : Fin 8 → ℝ)
    (hconv : ∃ l : ℝ,
      Tendsto (fun n : ℕ =>
        ∑ i ∈ Finset.Icc 1 n, putnam_1973_a2_coeff a i / (i : ℝ)) atTop (𝓝 l)) :
    ∑ j : Fin 8, a j = 0 := by
  classical
  let total : ℝ := ∑ j : Fin 8, a j
  by_contra htotal
  let c : ℝ := total / 8
  have hc : c ≠ 0 := by
    dsimp [c]
    exact div_ne_zero htotal (by norm_num)
  let d : Fin 8 → ℝ := fun j => a j - c
  have hdzero : ∑ j : Fin 8, d j = 0 := by
    dsimp [d, c, total]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num
    ring
  rcases hconv with ⟨lA, hA⟩
  rcases putnam_1973_a2_zero_mean_converges d hdzero with ⟨lD, hD⟩
  let A : ℕ → ℝ := fun n => ∑ i ∈ Finset.Icc 1 n, putnam_1973_a2_coeff a i / (i : ℝ)
  let D : ℕ → ℝ := fun n => ∑ i ∈ Finset.Icc 1 n, putnam_1973_a2_coeff d i / (i : ℝ)
  let Hc : ℕ → ℝ := fun n => c * ∑ i ∈ Finset.Icc 1 n, (1 : ℝ) / (i : ℝ)
  have hdiff : ∀ n : ℕ, A n - D n = Hc n := by
    intro n
    dsimp [A, D, Hc]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp [d, putnam_1973_a2_coeff, div_eq_mul_inv]
    ring
  have hHconv : ∃ l : ℝ, Tendsto Hc atTop (𝓝 l) := by
    refine ⟨lA - lD, ?_⟩
    have hAD : Tendsto (fun n => A n - D n) atTop (𝓝 (lA - lD)) := by
      exact hA.sub hD
    exact hAD.congr' (Eventually.of_forall hdiff)
  exact putnam_1973_a2_harmonic_scaled_not_convergent c hc hHconv

-- True
/--
Consider an infinite series whose $n$th term is given by $\pm \frac{1}{n}$, where the actual values of the $\pm$ signs repeat in blocks of $8$ (so the $\frac{1}{9}$ term has the same sign as the $\frac{1}{1}$ term, and so on). Call such a sequence balanced if each block contains four $+$ and four $-$ signs. Prove that being balanced is a sufficient condition for the sequence to converge. Is being balanced also necessary for the sequence to converge?
-/
theorem putnam_1973_a2
(L : List ℝ)
(hL : L.length = 8 ∧ ∀ i : Fin L.length, L[i] = 1 ∨ L[i] = -1)
(pluses : ℕ)
(hpluses : pluses = {i : Fin L.length | L[i] = 1}.ncard)
(S : ℕ → ℝ)
(hS : S = fun n : ℕ ↦ ∑ i ∈ Finset.Icc 1 n, L[i % 8]/i)
: (pluses = 4 → ∃ l : ℝ, Tendsto S atTop (𝓝 l)) ∧ (((True) : Prop ) ↔ ((∃ l : ℝ, Tendsto S atTop (𝓝 l)) → pluses = 4)) := by
  classical
  rcases hL with ⟨hlen, hpm⟩
  let e : Fin 8 ≃ Fin L.length := finCongr (by rw [hlen])
  let a : Fin 8 → ℝ := fun j => L[e j]
  have hcoeff : ∀ i : ℕ, L[i % 8] = putnam_1973_a2_coeff a i := by
    intro i
    have hidx : e ⟨i % 8, Nat.mod_lt i (by norm_num : 0 < 8)⟩ =
        (⟨i % 8, by rw [hlen]; exact Nat.mod_lt i (by norm_num : 0 < 8)⟩ : Fin L.length) := by
      ext
      simp [e, finCongr_apply]
    simp [putnam_1973_a2_coeff, a, hidx]
  have hSeq : S = fun n : ℕ =>
      ∑ i ∈ Finset.Icc 1 n, putnam_1973_a2_coeff a i / (i : ℝ) := by
    rw [hS]
    funext n
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [hcoeff i]
  have ha_pm : ∀ j : Fin 8, a j = 1 ∨ a j = -1 := by
    intro j
    exact hpm (e j)
  have hplus_card : (Finset.univ.filter (fun j : Fin 8 => a j = 1)).card = pluses := by
    have hcard : (Finset.univ.filter (fun j : Fin 8 => a j = 1)).card =
        (Finset.univ.filter (fun i : Fin L.length => L[i] = 1)).card := by
      rw [← Fintype.card_subtype (fun j : Fin 8 => a j = 1)]
      rw [← Fintype.card_subtype (fun i : Fin L.length => L[i] = 1)]
      exact Fintype.card_congr (e.subtypeEquiv (by intro j; simp [a]))
    rw [hcard, hpluses]
    simp [Set.ncard_eq_toFinset_card', Set.toFinset_setOf]
  have hsum_formula : (∑ j : Fin 8, a j) = 2 * (pluses : ℝ) - 8 := by
    rw [putnam_1973_a2_sum_pm_one a ha_pm, hplus_card]
    norm_num
  constructor
  · intro hbal
    have hzero : ∑ j : Fin 8, a j = 0 := by
      rw [hsum_formula]
      norm_num [hbal]
    rcases putnam_1973_a2_zero_mean_converges a hzero with ⟨l, hl⟩
    exact ⟨l, by simpa [hSeq] using hl⟩
  · constructor
    · intro _ hconvS
      have hconvA : ∃ l : ℝ,
          Tendsto (fun n : ℕ =>
            ∑ i ∈ Finset.Icc 1 n, putnam_1973_a2_coeff a i / (i : ℝ)) atTop (𝓝 l) := by
        rcases hconvS with ⟨l, hl⟩
        exact ⟨l, by simpa [hSeq] using hl⟩
      have hzero := putnam_1973_a2_total_zero_of_converges a hconvA
      have hreal : (pluses : ℝ) = 4 := by
        rw [hsum_formula] at hzero
        nlinarith
      exact_mod_cast hreal
    · intro _
      trivial
