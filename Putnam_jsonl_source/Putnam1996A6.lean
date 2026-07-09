import Mathlib

set_option maxHeartbeats 1000000

open Function

private lemma putnam_1996_a6_eqOn_Icc_of_step_right
    {f φ : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
    (hstep : ∀ x ∈ Set.Icc a b, x < b →
      φ x ∈ Set.Icc a b ∧ x < φ x ∧ f x = f (φ x)) :
    ∀ x ∈ Set.Icc a b, f x = f b := by
  classical
  have hbmem : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  obtain ⟨xM, hxMI, hxMmax⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc a b)).exists_isMaxOn ⟨b, hbmem⟩ hf
  let Smax : Set ℝ := {x | x ∈ Set.Icc a b ∧ f x = f xM}
  have hxM_S : xM ∈ Smax := ⟨hxMI, rfl⟩
  have hSmax_closed : IsClosed Smax := by
    change IsClosed (Set.Icc a b ∩ f ⁻¹' ({f xM} : Set ℝ))
    exact hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hSmax_comp : IsCompact Smax :=
    (isCompact_Icc : IsCompact (Set.Icc a b)).of_isClosed_subset hSmax_closed (by
      intro x hx
      exact hx.1)
  obtain ⟨yM, hyM_S, hyM_great⟩ :=
    hSmax_comp.exists_isMaxOn ⟨xM, hxM_S⟩ (continuousOn_id : ContinuousOn id Smax)
  have hyM_eq_b : yM = b := by
    have hyI : yM ∈ Set.Icc a b := hyM_S.1
    by_contra hne
    have hylt : yM < b := lt_of_le_of_ne hyI.2 hne
    rcases hstep yM hyI hylt with ⟨hφI, hyltφ, hfy⟩
    have hφS : φ yM ∈ Smax := ⟨hφI, by rw [← hfy, hyM_S.2]⟩
    have : φ yM ≤ yM := hyM_great hφS
    linarith
  have hmax_b : f xM = f b := by
    rw [← hyM_eq_b]
    exact hyM_S.2.symm
  obtain ⟨xm, hxmi, hxmin⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc a b)).exists_isMinOn ⟨b, hbmem⟩ hf
  let Smin : Set ℝ := {x | x ∈ Set.Icc a b ∧ f x = f xm}
  have hxm_S : xm ∈ Smin := ⟨hxmi, rfl⟩
  have hSmin_closed : IsClosed Smin := by
    change IsClosed (Set.Icc a b ∩ f ⁻¹' ({f xm} : Set ℝ))
    exact hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hSmin_comp : IsCompact Smin :=
    (isCompact_Icc : IsCompact (Set.Icc a b)).of_isClosed_subset hSmin_closed (by
      intro x hx
      exact hx.1)
  obtain ⟨ym, hym_S, hym_great⟩ :=
    hSmin_comp.exists_isMaxOn ⟨xm, hxm_S⟩ (continuousOn_id : ContinuousOn id Smin)
  have hym_eq_b : ym = b := by
    have hyI : ym ∈ Set.Icc a b := hym_S.1
    by_contra hne
    have hylt : ym < b := lt_of_le_of_ne hyI.2 hne
    rcases hstep ym hyI hylt with ⟨hφI, hyltφ, hfy⟩
    have hφS : φ ym ∈ Smin := ⟨hφI, by rw [← hfy, hym_S.2]⟩
    have : φ ym ≤ ym := hym_great hφS
    linarith
  have hmin_b : f xm = f b := by
    rw [← hym_eq_b]
    exact hym_S.2.symm
  intro x hx
  have hle : f x ≤ f b := by simpa [hmax_b] using hxMmax hx
  have hge : f b ≤ f x := by simpa [hmin_b] using hxmin hx
  exact le_antisymm hle hge

private lemma putnam_1996_a6_eqOn_Icc_of_step_left
    {f φ : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
    (hstep : ∀ x ∈ Set.Icc a b, a < x →
      φ x ∈ Set.Icc a b ∧ φ x < x ∧ f x = f (φ x)) :
    ∀ x ∈ Set.Icc a b, f x = f a := by
  classical
  have hamem : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  obtain ⟨xM, hxMI, hxMmax⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc a b)).exists_isMaxOn ⟨a, hamem⟩ hf
  let Smax : Set ℝ := {x | x ∈ Set.Icc a b ∧ f x = f xM}
  have hxM_S : xM ∈ Smax := ⟨hxMI, rfl⟩
  have hSmax_closed : IsClosed Smax := by
    change IsClosed (Set.Icc a b ∩ f ⁻¹' ({f xM} : Set ℝ))
    exact hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hSmax_comp : IsCompact Smax :=
    (isCompact_Icc : IsCompact (Set.Icc a b)).of_isClosed_subset hSmax_closed (by
      intro x hx
      exact hx.1)
  obtain ⟨yM, hyM_S, hyM_least⟩ :=
    hSmax_comp.exists_isMinOn ⟨xM, hxM_S⟩ (continuousOn_id : ContinuousOn id Smax)
  have hyM_eq_a : yM = a := by
    have hyI : yM ∈ Set.Icc a b := hyM_S.1
    by_contra hne
    have hygt : a < yM := lt_of_le_of_ne hyI.1 (Ne.symm hne)
    rcases hstep yM hyI hygt with ⟨hφI, hφlt, hfy⟩
    have hφS : φ yM ∈ Smax := ⟨hφI, by rw [← hfy, hyM_S.2]⟩
    have : yM ≤ φ yM := hyM_least hφS
    linarith
  have hmax_a : f xM = f a := by
    rw [← hyM_eq_a]
    exact hyM_S.2.symm
  obtain ⟨xm, hxmi, hxmin⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc a b)).exists_isMinOn ⟨a, hamem⟩ hf
  let Smin : Set ℝ := {x | x ∈ Set.Icc a b ∧ f x = f xm}
  have hxm_S : xm ∈ Smin := ⟨hxmi, rfl⟩
  have hSmin_closed : IsClosed Smin := by
    change IsClosed (Set.Icc a b ∩ f ⁻¹' ({f xm} : Set ℝ))
    exact hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hSmin_comp : IsCompact Smin :=
    (isCompact_Icc : IsCompact (Set.Icc a b)).of_isClosed_subset hSmin_closed (by
      intro x hx
      exact hx.1)
  obtain ⟨ym, hym_S, hym_least⟩ :=
    hSmin_comp.exists_isMinOn ⟨xm, hxm_S⟩ (continuousOn_id : ContinuousOn id Smin)
  have hym_eq_a : ym = a := by
    have hyI : ym ∈ Set.Icc a b := hym_S.1
    by_contra hne
    have hygt : a < ym := lt_of_le_of_ne hyI.1 (Ne.symm hne)
    rcases hstep ym hyI hygt with ⟨hφI, hφlt, hfy⟩
    have hφS : φ ym ∈ Smin := ⟨hφI, by rw [← hfy, hym_S.2]⟩
    have : ym ≤ φ ym := hym_least hφS
    linarith
  have hmin_a : f xm = f a := by
    rw [← hym_eq_a]
    exact hym_S.2.symm
  intro x hx
  have hle : f x ≤ f a := by simpa [hmax_a] using hxMmax hx
  have hge : f a ≤ f x := by simpa [hmin_a] using hxmin hx
  exact le_antisymm hle hge

private lemma putnam_1996_a6_supercritical_continuousOn_nonneg
    {c : ℝ} {f : ℝ → ℝ}
    (hc : (1 / 4 : ℝ) < c)
    (hfbase : ContinuousOn f (Set.Icc 0 c))
    (hfc : f 0 = f c)
    (hpos : ∀ x > 0, f x = f (x ^ 2 + c)) :
    ContinuousOn f (Set.Ici 0) := by
  let T : ℝ → ℝ := fun x => x ^ 2 + c
  have hcpos : 0 < c := by nlinarith
  have hδpos : 0 < c - 1 / 4 := by linarith
  have hT_ge_add : ∀ x : ℝ, x + (c - 1 / 4) ≤ T x := by
    intro x
    dsimp [T]
    nlinarith [sq_nonneg (x - 1 / 2)]
  have hT_nonneg : ∀ x : ℝ, 0 ≤ T x := by
    intro x
    dsimp [T]
    nlinarith [sq_nonneg x, le_of_lt hcpos]
  have hiter_c_nonneg : ∀ n : ℕ, 0 ≤ Nat.iterate T n c := by
    intro n
    induction n with
    | zero => simpa using le_of_lt hcpos
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact hT_nonneg _
  have hbound_c : ∀ n : ℕ, (n : ℝ) * (c - 1 / 4) ≤ Nat.iterate T n c := by
    intro n
    induction n with
    | zero =>
        simpa using le_of_lt hcpos
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        calc
          ((Nat.succ n : ℕ) : ℝ) * (c - 1 / 4)
              = (n : ℝ) * (c - 1 / 4) + (c - 1 / 4) := by
                norm_num [Nat.cast_succ, add_mul]
          _ ≤ Nat.iterate T n c + (c - 1 / 4) := by linarith
          _ ≤ T (Nat.iterate T n c) := hT_ge_add _
  have hstep_cont : ∀ a : ℝ, 0 ≤ a → ContinuousOn f (Set.Icc 0 a) →
      ContinuousOn f (Set.Icc 0 (T a)) := by
    intro a ha hfprev
    have hTa_ge_c : c ≤ T a := by
      dsimp [T]
      nlinarith [sq_nonneg a]
    have hright : ContinuousOn f (Set.Icc c (T a)) := by
      have hsqrt_cont : ContinuousOn (fun x : ℝ => f (√(x - c))) (Set.Icc c (T a)) := by
        refine hfprev.comp' ?_ ?_
        · fun_prop
        · intro x hx
          have hxsub_nonneg : 0 ≤ x - c := by linarith [hx.1]
          have hxsub_le : x - c ≤ a ^ 2 := by
            dsimp [T] at hx
            linarith [hx.2]
          constructor
          · exact Real.sqrt_nonneg _
          · rw [Real.sqrt_le_left ha]
            simpa using hxsub_le
      refine hsqrt_cont.congr ?_
      intro x hx
      have hxsub_nonneg : 0 ≤ x - c := by linarith [hx.1]
      have hsqsqrt : (√(x - c)) ^ 2 + c = x := by
        rw [Real.sq_sqrt hxsub_nonneg]
        ring
      by_cases hroot : √(x - c) = 0
      · have hx_eq_c : x = c := by
          have : x - c = 0 := by
            rw [← Real.sq_sqrt hxsub_nonneg, hroot]
            norm_num
          linarith
        simpa [hx_eq_c] using hfc.symm
      · have hroot_pos : 0 < √(x - c) :=
          lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hroot)
        have hpos_eq : f (√(x - c)) = f x := by
          simpa [hsqsqrt] using hpos (√(x - c)) hroot_pos
        exact hpos_eq.symm
    have hleft : ContinuousOn f (Set.Icc 0 c) := hfbase
    have hunion : ContinuousOn f (Set.Icc 0 c ∪ Set.Icc c (T a)) :=
      hleft.union_of_isClosed hright isClosed_Icc isClosed_Icc
    rwa [Set.Icc_union_Icc_eq_Icc (le_of_lt hcpos) hTa_ge_c] at hunion
  have hcont_iter : ∀ n : ℕ, ContinuousOn f (Set.Icc 0 (Nat.iterate T n c)) := by
    intro n
    induction n with
    | zero =>
        simpa using hfbase
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact hstep_cont (Nat.iterate T n c) (hiter_c_nonneg n) ih
  intro x hx0
  have hx0le : 0 ≤ x := hx0
  obtain ⟨n, hn⟩ := exists_nat_gt (x / (c - 1 / 4))
  have hxlt_mul : x < (n : ℝ) * (c - 1 / 4) := by
    exact (div_lt_iff₀ hδpos).mp hn
  have hxlt_iter : x < Nat.iterate T n c := lt_of_lt_of_le hxlt_mul (hbound_c n)
  have hwithin := (hcont_iter n) x ⟨hx0le, le_of_lt hxlt_iter⟩
  refine hwithin.mono_of_mem_nhdsWithin ?_
  rcases lt_or_eq_of_le hx0le with hxpos | rfl
  · exact mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds hxpos hxlt_iter)
  · simpa [Set.Ici] using Icc_mem_nhdsGE hxlt_iter

private lemma putnam_1996_a6_continuous_of_supercritical_data
    {f : ℝ → ℝ}
    (hnonneg : ContinuousOn f (Set.Ici (0 : ℝ)))
    (heven_neg : ∀ x < 0, f x = f (-x)) :
    Continuous f := by
  have hneg : ContinuousOn f (Set.Iic (0 : ℝ)) := by
    have hcomp : ContinuousOn (fun x : ℝ => f (-x)) (Set.Iic (0 : ℝ)) := by
      refine hnonneg.comp' ?_ ?_
      · fun_prop
      · intro x hx
        exact neg_nonneg.mpr (show x ≤ 0 from hx)
    refine hcomp.congr ?_
    intro x hx
    by_cases hxlt : x < 0
    · exact heven_neg x hxlt
    · have hx0 : x = 0 := le_antisymm (show x ≤ 0 from hx) (not_lt.mp hxlt)
      simp [hx0]
  have huniv : ContinuousOn f (Set.Iic (0 : ℝ) ∪ Set.Ici (0 : ℝ)) :=
    hneg.union_of_isClosed hnonneg isClosed_Iic isClosed_Ici
  rw [Set.Iic_union_Ici] at huniv
  exact continuousOn_univ.mp huniv

private lemma putnam_1996_a6_subcritical_constant
    {c : ℝ} {f : ℝ → ℝ}
    (cgt0 : c > 0) (hc : c ≤ (1 / 4 : ℝ))
    (hfcont : Continuous f)
    (hinv : ∀ x : ℝ, f x = f (x ^ 2 + c)) :
    ∃ d : ℝ, ∀ x : ℝ, f x = d := by
  classical
  let D : ℝ := √(1 - 4 * c)
  let r : ℝ := (1 - D) / 2
  let s : ℝ := (1 + D) / 2
  have hDnon : 0 ≤ 1 - 4 * c := by nlinarith
  have hDsq : D ^ 2 = 1 - 4 * c := by
    dsimp [D]
    exact Real.sq_sqrt hDnon
  have hDnonneg : 0 ≤ D := by
    dsimp [D]
    exact Real.sqrt_nonneg _
  have hsum : r + s = 1 := by
    dsimp [r, s]
    ring
  have hmul : r * s = c := by
    dsimp [r, s, D] at *
    nlinarith
  have hTr : r ^ 2 + c = r := by
    dsimp [r, D] at *
    nlinarith
  have hTs : s ^ 2 + c = s := by
    dsimp [s, D] at *
    nlinarith
  have h0r : 0 ≤ r := by
    dsimp [r, D] at *
    nlinarith [sq_nonneg (√(1 - 4 * c) - 1)]
  have hrs : r ≤ s := by
    dsimp [r, s]
    nlinarith [hDnonneg]
  have h0s : 0 ≤ s := le_trans h0r hrs
  have hspos : 0 < s := lt_of_lt_of_le cgt0 (by nlinarith [sq_nonneg s, hTs])
  have hcle_s : c ≤ s := by nlinarith [sq_nonneg s, hTs]
  have heven : ∀ x : ℝ, f x = f (-x) := by
    intro x
    calc
      f x = f (x ^ 2 + c) := hinv x
      _ = f ((-x) ^ 2 + c) := by ring_nf
      _ = f (-x) := (hinv (-x)).symm
  have hconst0r : ∀ x ∈ Set.Icc 0 r, f x = f r := by
    refine putnam_1996_a6_eqOn_Icc_of_step_right
      (f := f) (φ := fun x : ℝ => x ^ 2 + c) h0r hfcont.continuousOn ?_
    intro x hx hxlt
    have hx0 : 0 ≤ x := hx.1
    have hxr : x ≤ r := hx.2
    have hTx_nonneg : 0 ≤ x ^ 2 + c := by nlinarith [sq_nonneg x, le_of_lt cgt0]
    have hTx_le_r : x ^ 2 + c ≤ r := by
      have hx2 : x ^ 2 ≤ r ^ 2 := sq_le_sq' (by linarith) hxr
      nlinarith
    have hx_lt_Tx : x < x ^ 2 + c := by
      have hxmr : x - r < 0 := by linarith
      have hxms : x - s < 0 := by linarith
      have hprod : 0 < (x - r) * (x - s) := mul_pos_of_neg_of_neg hxmr hxms
      have hfactor : x ^ 2 + c - x = (x - r) * (x - s) := by nlinarith
      nlinarith
    exact ⟨⟨hTx_nonneg, hTx_le_r⟩, hx_lt_Tx, hinv x⟩
  have hconst_lt_s : ∀ x : ℝ, r ≤ x → x < s → f x = f r := by
    intro x hrx hxs
    by_cases hxr : x = r
    · simp [hxr]
    have hrltx : r < x := lt_of_le_of_ne hrx (Ne.symm hxr)
    have hconst_rx : ∀ y ∈ Set.Icc r x, f y = f r := by
      refine putnam_1996_a6_eqOn_Icc_of_step_left
        (f := f) (φ := fun y : ℝ => y ^ 2 + c)
        (le_of_lt hrltx) hfcont.continuousOn ?_
      intro y hy hry
      have hyr : r ≤ y := hy.1
      have hyx : y ≤ x := hy.2
      have hys : y < s := lt_of_le_of_lt hyx hxs
      have hTlt_y : y ^ 2 + c < y := by
        have hyrpos : 0 < y - r := by linarith
        have hysneg : y - s < 0 := by linarith
        have hprod : (y - r) * (y - s) < 0 := mul_neg_of_pos_of_neg hyrpos hysneg
        have hfactor : y ^ 2 + c - y = (y - r) * (y - s) := by nlinarith
        nlinarith
      have hT_ge_r : r ≤ y ^ 2 + c := by
        have hr2 : r ^ 2 ≤ y ^ 2 := sq_le_sq' (by linarith) hyr
        nlinarith
      have hT_le_x : y ^ 2 + c ≤ x := le_trans (le_of_lt hTlt_y) hyx
      exact ⟨⟨hT_ge_r, hT_le_x⟩, hTlt_y, hinv y⟩
    exact hconst_rx x ⟨le_of_lt hrltx, le_rfl⟩
  have hs_eq_fr : f s = f r := by
    by_cases hreqs : r = s
    · rw [← hreqs]
    let A : Set ℝ := {x | f x = f r}
    have hAclosed : IsClosed A := by
      dsimp [A]
      exact isClosed_eq hfcont continuous_const
    have hIoo_subset : Set.Ioo r s ⊆ A := by
      intro x hx
      exact hconst_lt_s x (le_of_lt hx.1) hx.2
    have hs_closure : s ∈ closure A := by
      apply closure_mono hIoo_subset
      rw [closure_Ioo hreqs]
      exact ⟨hrs, le_rfl⟩
    have hsA : s ∈ A := by
      rwa [hAclosed.closure_eq] at hs_closure
    exact hsA
  have htail : ∀ x : ℝ, s ≤ x → f x = f s := by
    intro x hsx
    by_cases hxs : x = s
    · simp [hxs]
    have hsltx : s < x := lt_of_le_of_ne hsx (Ne.symm hxs)
    have hconst_sx : ∀ y ∈ Set.Icc s x, f y = f s := by
      refine putnam_1996_a6_eqOn_Icc_of_step_left
        (f := f) (φ := fun y : ℝ => √(y - c))
        (le_of_lt hsltx) hfcont.continuousOn ?_
      intro y hy hsy
      have hylex : y ≤ x := hy.2
      have hsley : s ≤ y := hy.1
      have hyc_nonneg : 0 ≤ y - c := by linarith
      have hsqrt_sq : (√(y - c)) ^ 2 + c = y := by
        rw [Real.sq_sqrt hyc_nonneg]
        ring
      have hy0 : 0 ≤ y := le_trans h0s hsley
      have hpolypos : 0 < y ^ 2 + c - y := by
        have hyrpos : 0 < y - r := by linarith
        have hyspos : 0 < y - s := by linarith
        have hprod : 0 < (y - r) * (y - s) := mul_pos hyrpos hyspos
        have hfactor : y ^ 2 + c - y = (y - r) * (y - s) := by nlinarith
        nlinarith
      have hsqrt_lt_y : √(y - c) < y := by
        rw [Real.sqrt_lt hyc_nonneg hy0]
        nlinarith
      have hs_le_sqrt : s ≤ √(y - c) := by
        rw [Real.le_sqrt h0s hyc_nonneg]
        nlinarith
      have hsqrt_le_x : √(y - c) ≤ x := le_trans (le_of_lt hsqrt_lt_y) hylex
      have hfeq : f y = f (√(y - c)) := by
        have htmp : f (√(y - c)) = f y := by
          simpa [hsqrt_sq] using hinv (√(y - c))
        exact htmp.symm
      exact ⟨⟨hs_le_sqrt, hsqrt_le_x⟩, hsqrt_lt_y, hfeq⟩
    exact hconst_sx x ⟨le_of_lt hsltx, le_rfl⟩
  have hnonneg_const : ∀ x : ℝ, 0 ≤ x → f x = f r := by
    intro x hx0
    by_cases hxs : x < s
    · by_cases hxr : x ≤ r
      · exact hconst0r x ⟨hx0, hxr⟩
      · exact hconst_lt_s x (le_of_lt (not_le.mp hxr)) hxs
    · have hsx : s ≤ x := not_lt.mp hxs
      calc
        f x = f s := htail x hsx
        _ = f r := hs_eq_fr
  refine ⟨f r, ?_⟩
  intro x
  by_cases hx0 : 0 ≤ x
  · exact hnonneg_const x hx0
  · have hneg_nonneg : 0 ≤ -x := by linarith
    calc
      f x = f (-x) := heven x
      _ = f r := hnonneg_const (-x) hneg_nonneg

-- (fun c : ℝ => if c ≤ 1 / 4 then {f : ℝ → ℝ | ∃ d : ℝ, ∀ x : ℝ, f x = d} else {f : ℝ → ℝ | ContinuousOn f (Set.Icc 0 c) ∧ f 0 = f c ∧ (∀ x > 0, f x = f (x ^ 2 + c)) ∧ (∀ x < 0, f x = f (-x))})
/--
Let $c>0$ be a constant. Give a complete description, with proof, of the set of all continuous functions $f:\mathbb{R} \to \mathbb{R}$ such that $f(x)=f(x^2+c)$ for all $x \in \mathbb{R}$.
-/
theorem putnam_1996_a6
(c : ℝ)
(f : ℝ → ℝ)
(cgt0 : c > 0)
: (Continuous f ∧ ∀ x : ℝ, f x = f (x ^ 2 + c)) ↔ f ∈ ((fun c : ℝ => if c ≤ 1 / 4 then {f : ℝ → ℝ | ∃ d : ℝ, ∀ x : ℝ, f x = d} else {f : ℝ → ℝ | ContinuousOn f (Set.Icc 0 c) ∧ f 0 = f c ∧ (∀ x > 0, f x = f (x ^ 2 + c)) ∧ (∀ x < 0, f x = f (-x))}) : ℝ → Set (ℝ → ℝ) ) c := by
  classical
  by_cases hc : c ≤ (4 : ℝ)⁻¹
  · simp [hc]
    constructor
    · intro h
      have hc' : c ≤ (1 / 4 : ℝ) := by simpa [one_div] using hc
      exact putnam_1996_a6_subcritical_constant cgt0 hc' h.1 h.2
    · rintro ⟨d, hd⟩
      have hf_eq : f = fun _ : ℝ => d := funext hd
      constructor
      · simpa [hf_eq] using (continuous_const : Continuous fun _ : ℝ => d)
      · intro x
        rw [hd x, hd (x ^ 2 + c)]
  · have hcgt : (1 / 4 : ℝ) < c := by
      have : (4 : ℝ)⁻¹ < c := lt_of_not_ge hc
      simpa [one_div] using this
    simp [hc]
    constructor
    · intro h
      rcases h with ⟨hfcont, hinv⟩
      constructor
      · exact hfcont.continuousOn
      constructor
      · simpa using hinv 0
      constructor
      · intro x hx
        exact hinv x
      · intro x hx
        calc
          f x = f (x ^ 2 + c) := hinv x
          _ = f ((-x) ^ 2 + c) := by ring_nf
          _ = f (-x) := (hinv (-x)).symm
    · intro h
      rcases h with ⟨hfIcc, hfc, hpos, hneg⟩
      constructor
      · exact putnam_1996_a6_continuous_of_supercritical_data
          (putnam_1996_a6_supercritical_continuousOn_nonneg hcgt hfIcc hfc hpos) hneg
      · intro x
        by_cases hxpos : 0 < x
        · exact hpos x hxpos
        · by_cases hxneg : x < 0
          · have hnegpos : 0 < -x := by linarith
            calc
              f x = f (-x) := hneg x hxneg
              _ = f ((-x) ^ 2 + c) := hpos (-x) hnegpos
              _ = f (x ^ 2 + c) := by ring_nf
          · have hx0 : x = 0 := le_antisymm (not_lt.mp hxpos) (not_lt.mp hxneg)
            subst x
            simpa using hfc
