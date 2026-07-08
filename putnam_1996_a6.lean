import Mathlib

noncomputable section

open Function
open Filter
open Set
open scoped Topology

private def putnamA6_g (c x : ℝ) : ℝ :=
  x ^ 2 + c

private def putnamA6_h (c x : ℝ) : ℝ :=
  Real.sqrt (x - c)

private def putnamA6_p (c : ℝ) : ℝ :=
  (1 - Real.sqrt (1 - 4 * c)) / 2

private def putnamA6_q (c : ℝ) : ℝ :=
  (1 + Real.sqrt (1 - 4 * c)) / 2

abbrev putnam_1996_a6_solution : ℝ → Set (ℝ → ℝ) :=
  fun c =>
    if c ≤ 1 / 4 then
      Set.range (fun k : ℝ => fun _ : ℝ => k)
    else
      {f : ℝ → ℝ | Continuous f ∧
        (∀ x : ℝ, f x = f (-x)) ∧
        ∀ x : ℝ, 0 ≤ x → f x = f (x ^ 2 + c)}

private lemma putnamA6_disc_nonneg {c : ℝ} (hc : c ≤ 1 / 4) :
    0 ≤ 1 - 4 * c := by
  nlinarith

private lemma putnamA6_p_add_q (c : ℝ) :
    putnamA6_p c + putnamA6_q c = 1 := by
  unfold putnamA6_p putnamA6_q
  ring

private lemma putnamA6_p_mul_q {c : ℝ} (hc : c ≤ 1 / 4) :
    putnamA6_p c * putnamA6_q c = c := by
  have hs := Real.sq_sqrt (putnamA6_disc_nonneg hc)
  unfold putnamA6_p putnamA6_q at *
  nlinarith

private lemma putnamA6_p_le_q (c : ℝ) :
    putnamA6_p c ≤ putnamA6_q c := by
  have hs : 0 ≤ Real.sqrt (1 - 4 * c) := Real.sqrt_nonneg _
  unfold putnamA6_p putnamA6_q
  nlinarith

private lemma putnamA6_p_nonneg {c : ℝ} (hc0 : 0 < c) :
    0 ≤ putnamA6_p c := by
  have hsle : Real.sqrt (1 - 4 * c) ≤ 1 := by
    rw [Real.sqrt_le_one]
    nlinarith [hc0]
  unfold putnamA6_p
  nlinarith

private lemma putnamA6_q_nonneg {c : ℝ} :
    0 ≤ putnamA6_q c := by
  have hs : 0 ≤ Real.sqrt (1 - 4 * c) := Real.sqrt_nonneg _
  unfold putnamA6_q
  nlinarith

private lemma putnamA6_fixed_p {c : ℝ} (hc : c ≤ 1 / 4) :
    putnamA6_g c (putnamA6_p c) = putnamA6_p c := by
  have hs := Real.sq_sqrt (putnamA6_disc_nonneg hc)
  unfold putnamA6_g putnamA6_p at *
  nlinarith

private lemma putnamA6_fixed_q {c : ℝ} (hc : c ≤ 1 / 4) :
    putnamA6_g c (putnamA6_q c) = putnamA6_q c := by
  have hs := Real.sq_sqrt (putnamA6_disc_nonneg hc)
  unfold putnamA6_g putnamA6_q at *
  nlinarith

private lemma putnamA6_c_le_q {c : ℝ} (hc : c ≤ 1 / 4) :
    c ≤ putnamA6_q c := by
  have hfix := putnamA6_fixed_q (c := c) hc
  have hsq : 0 ≤ putnamA6_q c ^ 2 := sq_nonneg _
  unfold putnamA6_g at hfix
  nlinarith

private lemma putnamA6_fixed_eq_p_or_q {c x : ℝ} (hc : c ≤ 1 / 4)
    (hx : putnamA6_g c x = x) :
    x = putnamA6_p c ∨ x = putnamA6_q c := by
  have hs := Real.sq_sqrt (putnamA6_disc_nonneg hc)
  have hsq : (2 * x - 1) ^ 2 = (Real.sqrt (1 - 4 * c)) ^ 2 := by
    unfold putnamA6_g at hx
    nlinarith
  rcases eq_or_eq_neg_of_sq_eq_sq (2 * x - 1) (Real.sqrt (1 - 4 * c)) hsq with h | h
  · right
    unfold putnamA6_q
    nlinarith
  · left
    unfold putnamA6_p
    nlinarith

private lemma putnamA6_g_factor {c x : ℝ} (hc : c ≤ 1 / 4) :
    putnamA6_g c x - x = (putnamA6_p c - x) * (putnamA6_q c - x) := by
  have hsum := putnamA6_p_add_q c
  have hprod := putnamA6_p_mul_q (c := c) hc
  calc
    putnamA6_g c x - x = x ^ 2 + c - x := by rfl
    _ = x ^ 2 + putnamA6_p c * putnamA6_q c - (putnamA6_p c + putnamA6_q c) * x := by
      rw [hprod, hsum]
      ring
    _ = (putnamA6_p c - x) * (putnamA6_q c - x) := by ring

private lemma putnamA6_g_factor' {c x : ℝ} (hc : c ≤ 1 / 4) :
    x - putnamA6_g c x = (x - putnamA6_p c) * (putnamA6_q c - x) := by
  have hsum := putnamA6_p_add_q c
  have hprod := putnamA6_p_mul_q (c := c) hc
  calc
    x - putnamA6_g c x = x - (x ^ 2 + c) := by rfl
    _ = x - (x ^ 2 + putnamA6_p c * putnamA6_q c) := by rw [hprod]
    _ = (x - putnamA6_p c) * (putnamA6_q c - x) := by
      have hq : putnamA6_q c = 1 - putnamA6_p c := by nlinarith
      rw [hq]
      ring

private lemma putnamA6_g_le_p {c x : ℝ} (hc0 : 0 < c) (hc : c ≤ 1 / 4)
    (hx0 : 0 ≤ x) (hxp : x ≤ putnamA6_p c) :
    putnamA6_g c x ≤ putnamA6_p c := by
  have hp0 := putnamA6_p_nonneg (c := c) hc0
  have hfix := putnamA6_fixed_p (c := c) hc
  have hprod : 0 ≤ (putnamA6_p c - x) * (putnamA6_p c + x) :=
    mul_nonneg (sub_nonneg.mpr hxp) (add_nonneg hp0 hx0)
  unfold putnamA6_g at hfix ⊢
  nlinarith

private lemma putnamA6_p_le_g {c x : ℝ} (hc0 : 0 < c) (hc : c ≤ 1 / 4)
    (hpx : putnamA6_p c ≤ x) :
    putnamA6_p c ≤ putnamA6_g c x := by
  have hp0 := putnamA6_p_nonneg (c := c) hc0
  have hfix := putnamA6_fixed_p (c := c) hc
  have hx0 : 0 ≤ x := hp0.trans hpx
  have hprod : 0 ≤ (x - putnamA6_p c) * (x + putnamA6_p c) :=
    mul_nonneg (sub_nonneg.mpr hpx) (add_nonneg hx0 hp0)
  unfold putnamA6_g at hfix ⊢
  nlinarith

private lemma putnamA6_g_lt_q {c x : ℝ} (hc0 : 0 < c) (hc : c ≤ 1 / 4)
    (hpx : putnamA6_p c ≤ x) (hxq : x < putnamA6_q c) :
    putnamA6_g c x < putnamA6_q c := by
  have hfix := putnamA6_fixed_q (c := c) hc
  have hp0 := putnamA6_p_nonneg (c := c) hc0
  have hx0 : 0 ≤ x := hp0.trans hpx
  have hqpos : 0 < putnamA6_q c := lt_of_le_of_lt hx0 hxq
  have hpos : 0 < (putnamA6_q c - x) * (putnamA6_q c + x) :=
    mul_pos (sub_pos.mpr hxq) (add_pos_of_pos_of_nonneg hqpos hx0)
  unfold putnamA6_g at hfix ⊢
  nlinarith

private lemma putnamA6_tendsto_iterate_to_p_of_le_p {c x : ℝ}
    (hc0 : 0 < c) (hc : c ≤ 1 / 4) (hx0 : 0 ≤ x) (hxp : x ≤ putnamA6_p c) :
    Tendsto (fun n : ℕ => (putnamA6_g c)^[n] x) atTop (𝓝 (putnamA6_p c)) := by
  let u : ℕ → ℝ := fun n => (putnamA6_g c)^[n] x
  have hbounds : ∀ n, 0 ≤ u n ∧ u n ≤ putnamA6_p c := by
    intro n
    induction n with
    | zero =>
        simpa [u] using And.intro hx0 hxp
    | succ n ih =>
        have h0 : 0 ≤ putnamA6_g c (u n) := by
          unfold putnamA6_g
          nlinarith [sq_nonneg (u n), le_of_lt hc0]
        have hp : putnamA6_g c (u n) ≤ putnamA6_p c :=
          putnamA6_g_le_p (c := c) hc0 hc ih.1 ih.2
        simpa [u, Function.iterate_succ_apply'] using And.intro h0 hp
  have hmono : Monotone u := by
    refine monotone_nat_of_le_succ ?_
    intro n
    have hfac := putnamA6_g_factor (c := c) (x := u n) hc
    have hprod : 0 ≤ (putnamA6_p c - u n) * (putnamA6_q c - u n) :=
      mul_nonneg (sub_nonneg.mpr (hbounds n).2)
        (sub_nonneg.mpr ((hbounds n).2.trans (putnamA6_p_le_q c)))
    have : u n ≤ putnamA6_g c (u n) := by nlinarith
    simpa [u, Function.iterate_succ_apply'] using this
  have hbdd : BddAbove (range u) :=
    ⟨putnamA6_p c, by
      rintro y ⟨n, rfl⟩
      exact (hbounds n).2⟩
  have hlim : Tendsto u atTop (𝓝 (⨆ n, u n)) := tendsto_atTop_ciSup hmono hbdd
  have hcontg : Continuous (putnamA6_g c) := by
    unfold putnamA6_g
    fun_prop
  have hfix : IsFixedPt (putnamA6_g c) (⨆ n, u n) :=
    isFixedPt_of_tendsto_iterate (f := putnamA6_g c) (x := x) (y := ⨆ n, u n) (by simpa [u] using hlim)
      hcontg.continuousAt
  have hroot : putnamA6_g c (⨆ n, u n) = (⨆ n, u n) := hfix
  have hsle : (⨆ n, u n) ≤ putnamA6_p c := ciSup_le fun n => (hbounds n).2
  have hs : (⨆ n, u n) = putnamA6_p c := by
    rcases putnamA6_fixed_eq_p_or_q (c := c) hc hroot with h | h
    · exact h
    · have hqp : putnamA6_q c ≤ putnamA6_p c := by simpa [h] using hsle
      have hpq := putnamA6_p_le_q c
      have hEq : putnamA6_q c = putnamA6_p c := le_antisymm hqp hpq
      simp [h, hEq]
  simpa [u, hs] using hlim

private lemma putnamA6_tendsto_iterate_to_p_of_lt_q {c x : ℝ}
    (hc0 : 0 < c) (hc : c ≤ 1 / 4)
    (hpx : putnamA6_p c ≤ x) (hxq : x < putnamA6_q c) :
    Tendsto (fun n : ℕ => (putnamA6_g c)^[n] x) atTop (𝓝 (putnamA6_p c)) := by
  let u : ℕ → ℝ := fun n => (putnamA6_g c)^[n] x
  have hbounds : ∀ n, putnamA6_p c ≤ u n ∧ u n < putnamA6_q c := by
    intro n
    induction n with
    | zero =>
        simpa [u] using And.intro hpx hxq
    | succ n ih =>
        have hp : putnamA6_p c ≤ putnamA6_g c (u n) :=
          putnamA6_p_le_g (c := c) hc0 hc ih.1
        have hq : putnamA6_g c (u n) < putnamA6_q c :=
          putnamA6_g_lt_q (c := c) hc0 hc ih.1 ih.2
        simpa [u, Function.iterate_succ_apply'] using And.intro hp hq
  have hanti : Antitone u := by
    refine antitone_nat_of_succ_le ?_
    intro n
    have hfac := putnamA6_g_factor' (c := c) (x := u n) hc
    have hprod : 0 ≤ (u n - putnamA6_p c) * (putnamA6_q c - u n) :=
      mul_nonneg (sub_nonneg.mpr (hbounds n).1) (sub_nonneg.mpr (le_of_lt (hbounds n).2))
    have : putnamA6_g c (u n) ≤ u n := by nlinarith
    simpa [u, Function.iterate_succ_apply'] using this
  have hbdd : BddBelow (range u) :=
    ⟨putnamA6_p c, by
      rintro y ⟨n, rfl⟩
      exact (hbounds n).1⟩
  have hlim : Tendsto u atTop (𝓝 (⨅ n, u n)) := tendsto_atTop_ciInf hanti hbdd
  have hcontg : Continuous (putnamA6_g c) := by
    unfold putnamA6_g
    fun_prop
  have hfix : IsFixedPt (putnamA6_g c) (⨅ n, u n) :=
    isFixedPt_of_tendsto_iterate (f := putnamA6_g c) (x := x) (y := ⨅ n, u n) (by simpa [u] using hlim)
      hcontg.continuousAt
  have hroot : putnamA6_g c (⨅ n, u n) = (⨅ n, u n) := hfix
  have hsle : (⨅ n, u n) ≤ x := by
    simpa [u] using (ciInf_le hbdd 0 : (⨅ n, u n) ≤ u 0)
  have hs : (⨅ n, u n) = putnamA6_p c := by
    rcases putnamA6_fixed_eq_p_or_q (c := c) hc hroot with h | h
    · exact h
    · have hqx : putnamA6_q c ≤ x := by simpa [h] using hsle
      exact False.elim ((not_lt_of_ge hqx) hxq)
  simpa [u, hs] using hlim

private lemma putnamA6_h_le_self {c x : ℝ} (hc : c ≤ 1 / 4)
    (hqx : putnamA6_q c ≤ x) :
    putnamA6_h c x ≤ x := by
  have hq0 := putnamA6_q_nonneg (c := c)
  have hx0 : 0 ≤ x := hq0.trans hqx
  have hpq := putnamA6_p_le_q c
  have hfac := putnamA6_g_factor (c := c) (x := x) hc
  have hprod : 0 ≤ (x - putnamA6_p c) * (x - putnamA6_q c) :=
    mul_nonneg (sub_nonneg.mpr (hpq.trans hqx)) (sub_nonneg.mpr hqx)
  have hsquare : x - c ≤ x ^ 2 := by
    unfold putnamA6_g at hfac
    nlinarith
  unfold putnamA6_h
  exact (Real.sqrt_le_left hx0).mpr hsquare

private lemma putnamA6_q_le_h {c x : ℝ} (hc : c ≤ 1 / 4)
    (hqx : putnamA6_q c ≤ x) :
    putnamA6_q c ≤ putnamA6_h c x := by
  have hq0 := putnamA6_q_nonneg (c := c)
  have hcq := putnamA6_c_le_q (c := c) hc
  have hcx : c ≤ x := hcq.trans hqx
  have hfix := putnamA6_fixed_q (c := c) hc
  have hsquare : putnamA6_q c ^ 2 ≤ x - c := by
    unfold putnamA6_g at hfix
    nlinarith
  unfold putnamA6_h
  exact (Real.le_sqrt hq0 (sub_nonneg.mpr hcx)).mpr hsquare

private lemma putnamA6_tendsto_h_to_q {c x : ℝ}
    (hc : c ≤ 1 / 4) (hqx : putnamA6_q c ≤ x) :
    Tendsto (fun n : ℕ => (putnamA6_h c)^[n] x) atTop (𝓝 (putnamA6_q c)) := by
  let u : ℕ → ℝ := fun n => (putnamA6_h c)^[n] x
  have hbounds : ∀ n, putnamA6_q c ≤ u n := by
    intro n
    induction n with
    | zero =>
        simpa [u] using hqx
    | succ n ih =>
        have hq := putnamA6_q_le_h (c := c) hc ih
        simpa [u, Function.iterate_succ_apply'] using hq
  have hanti : Antitone u := by
    refine antitone_nat_of_succ_le ?_
    intro n
    have hh := putnamA6_h_le_self (c := c) hc (hbounds n)
    simpa [u, Function.iterate_succ_apply'] using hh
  have hbdd : BddBelow (range u) :=
    ⟨putnamA6_q c, by
      rintro y ⟨n, rfl⟩
      exact hbounds n⟩
  have hlim : Tendsto u atTop (𝓝 (⨅ n, u n)) := tendsto_atTop_ciInf hanti hbdd
  have hconth : Continuous (putnamA6_h c) := by
    unfold putnamA6_h
    fun_prop
  have hfix : IsFixedPt (putnamA6_h c) (⨅ n, u n) :=
    isFixedPt_of_tendsto_iterate (f := putnamA6_h c) (x := x) (y := ⨅ n, u n) (by simpa [u] using hlim)
      hconth.continuousAt
  have hge : putnamA6_q c ≤ (⨅ n, u n) := le_ciInf fun n => hbounds n
  have hcq := putnamA6_c_le_q (c := c) hc
  have hcx : c ≤ (⨅ n, u n) := hcq.trans hge
  have hroot : putnamA6_g c (⨅ n, u n) = (⨅ n, u n) := by
    have hsqrt : Real.sqrt ((⨅ n, u n) - c) = (⨅ n, u n) := by
      simpa [putnamA6_h] using hfix
    have hsquare : (⨅ n, u n) ^ 2 = (⨅ n, u n) - c := by
      calc
        (⨅ n, u n) ^ 2 = (Real.sqrt ((⨅ n, u n) - c)) ^ 2 := by rw [hsqrt]
        _ = (⨅ n, u n) - c := Real.sq_sqrt (sub_nonneg.mpr hcx)
    unfold putnamA6_g
    nlinarith
  have hs : (⨅ n, u n) = putnamA6_q c := by
    rcases putnamA6_fixed_eq_p_or_q (c := c) hc hroot with h | h
    · have hqp : putnamA6_q c ≤ putnamA6_p c := by simpa [h] using hge
      have hpq := putnamA6_p_le_q c
      have hEq : putnamA6_p c = putnamA6_q c := le_antisymm hpq hqp
      simpa [hEq] using h
    · exact h
  simpa [u, hs] using hlim

private lemma putnamA6_eq_of_tendsto_forward {c : ℝ} {f : ℝ → ℝ} {x y : ℝ}
    (hcont : Continuous f) (hfeq : ∀ x : ℝ, f x = f (putnamA6_g c x))
    (hlim : Tendsto (fun n : ℕ => (putnamA6_g c)^[n] x) atTop (𝓝 y)) :
    f x = f y := by
  have hconst : ∀ n : ℕ, f ((putnamA6_g c)^[n] x) = f x := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        calc
          f ((putnamA6_g c)^[n.succ] x)
              = f (putnamA6_g c ((putnamA6_g c)^[n] x)) := by rw [Function.iterate_succ_apply']
          _ = f ((putnamA6_g c)^[n] x) := (hfeq ((putnamA6_g c)^[n] x)).symm
          _ = f x := ih
  have hlimf : Tendsto (fun n : ℕ => f ((putnamA6_g c)^[n] x)) atTop (𝓝 (f y)) :=
    hcont.tendsto y |>.comp hlim
  have hlimf' : Tendsto (fun _ : ℕ => f x) atTop (𝓝 (f y)) := by
    convert hlimf using 1
    ext n
    exact (hconst n).symm
  exact tendsto_nhds_unique tendsto_const_nhds hlimf'

private lemma putnamA6_inverse_step {c : ℝ} {f : ℝ → ℝ}
    (hfeq : ∀ x : ℝ, f x = f (putnamA6_g c x)) :
    ∀ x : ℝ, c ≤ x → f x = f (putnamA6_h c x) := by
  intro x hx
  have hsquare : putnamA6_g c (putnamA6_h c x) = x := by
    unfold putnamA6_g putnamA6_h
    rw [Real.sq_sqrt (sub_nonneg.mpr hx)]
    ring
  calc
    f x = f (putnamA6_g c (putnamA6_h c x)) := by rw [hsquare]
    _ = f (putnamA6_h c x) := (hfeq (putnamA6_h c x)).symm

private lemma putnamA6_eq_of_tendsto_inverse {c : ℝ} {f : ℝ → ℝ} {x y : ℝ}
    (hcont : Continuous f) (hfeq : ∀ x : ℝ, f x = f (putnamA6_g c x))
    (hbound : ∀ n : ℕ, c ≤ (putnamA6_h c)^[n] x)
    (hlim : Tendsto (fun n : ℕ => (putnamA6_h c)^[n] x) atTop (𝓝 y)) :
    f x = f y := by
  have hstep := putnamA6_inverse_step (c := c) (f := f) hfeq
  have hconst : ∀ n : ℕ, f ((putnamA6_h c)^[n] x) = f x := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        calc
          f ((putnamA6_h c)^[n.succ] x)
              = f (putnamA6_h c ((putnamA6_h c)^[n] x)) := by rw [Function.iterate_succ_apply']
          _ = f ((putnamA6_h c)^[n] x) := (hstep ((putnamA6_h c)^[n] x) (hbound n)).symm
          _ = f x := ih
  have hlimf : Tendsto (fun n : ℕ => f ((putnamA6_h c)^[n] x)) atTop (𝓝 (f y)) :=
    hcont.tendsto y |>.comp hlim
  have hlimf' : Tendsto (fun _ : ℕ => f x) atTop (𝓝 (f y)) := by
    convert hlimf using 1
    ext n
    exact (hconst n).symm
  exact tendsto_nhds_unique tendsto_const_nhds hlimf'

private lemma putnamA6_even_of_feq {c : ℝ} {f : ℝ → ℝ}
    (hfeq : ∀ x : ℝ, f x = f (putnamA6_g c x)) :
    ∀ x : ℝ, f (-x) = f x := by
  intro x
  calc
    f (-x) = f (putnamA6_g c (-x)) := hfeq (-x)
    _ = f (putnamA6_g c x) := by
      congr 1
      unfold putnamA6_g
      ring
    _ = f x := (hfeq x).symm

private lemma putnamA6_abs_value {c : ℝ} {f : ℝ → ℝ}
    (hfeq : ∀ x : ℝ, f x = f (putnamA6_g c x)) (x : ℝ) :
    f x = f |x| := by
  have heven := putnamA6_even_of_feq (c := c) (f := f) hfeq
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
  · have hxle : x ≤ 0 := le_of_not_ge hx
    calc
      f x = f (-x) := (heven x).symm
      _ = f |x| := by rw [abs_of_nonpos hxle]

private lemma putnamA6_fq_eq_fp {c : ℝ} {f : ℝ → ℝ}
    (hc0 : 0 < c) (hc : c ≤ 1 / 4)
    (hcont : Continuous f) (hfeq : ∀ x : ℝ, f x = f (putnamA6_g c x)) :
    f (putnamA6_q c) = f (putnamA6_p c) := by
  by_cases hpq : putnamA6_p c = putnamA6_q c
  · simp [hpq]
  · have hlt : putnamA6_p c < putnamA6_q c :=
      lt_of_le_of_ne (putnamA6_p_le_q c) hpq
    let t : ℕ → ℝ := fun n => putnamA6_q c - (putnamA6_q c - putnamA6_p c) / ((n : ℝ) + 1)
    have htend : Tendsto t atTop (𝓝 (putnamA6_q c)) := by
      have hdiv : Tendsto
          (fun n : ℕ => (putnamA6_q c - putnamA6_p c) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
        simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using
          (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (putnamA6_q c - putnamA6_p c)).comp
            (tendsto_add_atTop_nat 1)
      simpa [t, sub_zero] using (tendsto_const_nhds.sub hdiv)
    have ht_bounds : ∀ n, putnamA6_p c ≤ t n ∧ t n < putnamA6_q c := by
      intro n
      have hdenpos : 0 < ((n : ℝ) + 1) := by positivity
      have hdiffpos : 0 < putnamA6_q c - putnamA6_p c := sub_pos.mpr hlt
      have hdivpos : 0 < (putnamA6_q c - putnamA6_p c) / ((n : ℝ) + 1) :=
        div_pos hdiffpos hdenpos
      have hdivle : (putnamA6_q c - putnamA6_p c) / ((n : ℝ) + 1) ≤
          putnamA6_q c - putnamA6_p c := by
        rw [div_le_iff₀ hdenpos]
        have hn0 : 0 ≤ (n : ℝ) := by positivity
        nlinarith
      constructor
      · dsimp [t]
        nlinarith
      · dsimp [t]
        nlinarith
    have hval : ∀ n, f (t n) = f (putnamA6_p c) := by
      intro n
      exact putnamA6_eq_of_tendsto_forward (c := c) (f := f) hcont hfeq
        (putnamA6_tendsto_iterate_to_p_of_lt_q (c := c) (x := t n) hc0 hc
          (ht_bounds n).1 (ht_bounds n).2)
    have hlimf : Tendsto (fun n : ℕ => f (t n)) atTop (𝓝 (f (putnamA6_q c))) :=
      hcont.tendsto (putnamA6_q c) |>.comp htend
    have hlimconst : Tendsto (fun _ : ℕ => f (putnamA6_p c)) atTop (𝓝 (f (putnamA6_q c))) := by
      convert hlimf using 1
      ext n
      exact (hval n).symm
    exact (tendsto_nhds_unique tendsto_const_nhds hlimconst).symm

private lemma putnamA6_constant_of_le_quarter {c : ℝ} {f : ℝ → ℝ}
    (hc0 : 0 < c) (hc : c ≤ 1 / 4)
    (hcont : Continuous f) (hfeq : ∀ x : ℝ, f x = f (putnamA6_g c x)) :
    ∃ k : ℝ, ∀ x : ℝ, f x = k := by
  refine ⟨f (putnamA6_p c), ?_⟩
  intro x
  have hfpq := putnamA6_fq_eq_fp (c := c) (f := f) hc0 hc hcont hfeq
  have hcxq := putnamA6_c_le_q (c := c) hc
  have habs_nonneg : 0 ≤ |x| := abs_nonneg x
  have hxabs : f x = f |x| := putnamA6_abs_value (c := c) (f := f) hfeq x
  suffices f |x| = f (putnamA6_p c) by exact hxabs.trans this
  by_cases hle : |x| ≤ putnamA6_p c
  · exact putnamA6_eq_of_tendsto_forward (c := c) (f := f) hcont hfeq
      (putnamA6_tendsto_iterate_to_p_of_le_p (c := c) (x := |x|) hc0 hc habs_nonneg hle)
  · have hpx : putnamA6_p c ≤ |x| := le_of_not_ge hle
    by_cases hltq : |x| < putnamA6_q c
    · exact putnamA6_eq_of_tendsto_forward (c := c) (f := f) hcont hfeq
        (putnamA6_tendsto_iterate_to_p_of_lt_q (c := c) (x := |x|) hc0 hc hpx hltq)
    · have hqx : putnamA6_q c ≤ |x| := le_of_not_gt hltq
      have hlim := putnamA6_tendsto_h_to_q (c := c) (x := |x|) hc hqx
      have hbound : ∀ n : ℕ, c ≤ (putnamA6_h c)^[n] |x| := by
        intro n
        exact hcxq.trans (by
          have hbounds_q : ∀ n : ℕ, putnamA6_q c ≤ (putnamA6_h c)^[n] |x| := by
            intro m
            induction m with
            | zero => simpa using hqx
            | succ m ih =>
                simpa [Function.iterate_succ_apply'] using putnamA6_q_le_h (c := c) hc ih
          exact hbounds_q n)
      have hyq : f |x| = f (putnamA6_q c) :=
        putnamA6_eq_of_tendsto_inverse (c := c) (f := f) hcont hfeq hbound hlim
      exact hyq.trans hfpq

/--
Let $c>0$ be a constant. Give a complete description, with proof, of the set of all continuous functions $f:\mathbb{R} \to \mathbb{R}$ such that $f(x)=f(x^2+c)$ for all $x \in \mathbb{R}$.
-/
theorem putnam_1996_a6
(c : ℝ)
(f : ℝ → ℝ)
(cgt0 : c > 0)
: (Continuous f ∧ ∀ x : ℝ, f x = f (x ^ 2 + c)) ↔ f ∈ putnam_1996_a6_solution c :=
by
  constructor
  · rintro ⟨hcont, hfeq_raw⟩
    have hfeq : ∀ x : ℝ, f x = f (putnamA6_g c x) := by
      intro x
      simpa [putnamA6_g] using hfeq_raw x
    by_cases hc : c ≤ (4 : ℝ)⁻¹
    ·
      have hc_quarter : c ≤ 1 / 4 := by simpa [one_div] using hc
      rcases putnamA6_constant_of_le_quarter (c := c) (f := f) cgt0 hc_quarter hcont hfeq with
        ⟨k, hk⟩
      have hconst : f ∈ Set.range (fun k : ℝ => fun _ : ℝ => k) := ⟨k, (funext hk).symm⟩
      simpa [putnam_1996_a6_solution, hc, one_div] using hconst
    ·
      have heven : ∀ x : ℝ, f x = f (-x) := by
        intro x
        exact (putnamA6_even_of_feq (c := c) (f := f) hfeq x).symm
      have hpos : ∀ x : ℝ, 0 ≤ x → f x = f (x ^ 2 + c) := by
        intro x hx
        simpa [putnamA6_g] using hfeq x
      simpa [putnam_1996_a6_solution, hc, one_div] using (And.intro hcont (And.intro heven hpos))
  · intro hsol
    by_cases hc : c ≤ (4 : ℝ)⁻¹
    · have hconst : f ∈ Set.range (fun k : ℝ => fun _ : ℝ => k) := by
        simpa [putnam_1996_a6_solution, hc, one_div] using hsol
      rcases hconst with ⟨k, hk⟩
      constructor
      · rw [← hk]
        exact continuous_const
      · intro x
        rw [← hk]
    · have hclass :
          Continuous f ∧
            (∀ x : ℝ, f x = f (-x)) ∧
            ∀ x : ℝ, 0 ≤ x → f x = f (x ^ 2 + c) := by
        simpa [putnam_1996_a6_solution, hc, one_div] using hsol
      rcases hclass with ⟨hcont, heven, hpos⟩
      constructor
      · exact hcont
      · intro x
        by_cases hx : 0 ≤ x
        · exact hpos x hx
        · calc
            f x = f (-x) := heven x
            _ = f ((-x) ^ 2 + c) := hpos (-x) (by linarith)
            _ = f (x ^ 2 + c) := by
              congr 1
              ring
