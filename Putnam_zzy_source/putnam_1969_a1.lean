import Mathlib

open Matrix Filter Topology Set Nat

abbrev putnam_1969_a1_solution : Set (Set ℝ) :=
  {s | s = univ ∨
    (∃ a : ℝ, s = Iic a) ∨
    (∃ a : ℝ, s = Iio a) ∨
    (∃ a : ℝ, s = Ici a) ∨
    (∃ a : ℝ, s = Ioi a) ∨
    (∃ a : ℝ, s = {a})}

noncomputable section

private def putnamRange (f : MvPolynomial (Fin 2) ℝ) : Set ℝ :=
  {z : ℝ | ∃ x : Fin 2 → ℝ, MvPolynomial.eval x f = z}

private def lineX (f : MvPolynomial (Fin 2) ℝ) (y : ℝ) : Polynomial ℝ :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i : Fin 2 => if i = 0 then Polynomial.X else Polynomial.C y) f

private lemma lineX_eval (f : MvPolynomial (Fin 2) ℝ) (x y : ℝ) :
    Polynomial.eval x (lineX f y) =
      MvPolynomial.eval (fun i : Fin 2 => if i = 0 then x else y) f := by
  change (Polynomial.evalRingHom x)
      (MvPolynomial.eval₂Hom Polynomial.C
        (fun i : Fin 2 => if i = 0 then Polynomial.X else Polynomial.C y) f) = _
  rw [MvPolynomial.map_eval₂Hom]
  apply MvPolynomial.eval₂Hom_congr <;> try rfl
  · ext a
    simp
  · funext i
    by_cases hi : i = 0 <;> simp [hi]

private def lineY0 (f : MvPolynomial (Fin 2) ℝ) : Polynomial ℝ :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i : Fin 2 => if i = 0 then Polynomial.C 0 else Polynomial.X) f

private lemma lineY0_eval (f : MvPolynomial (Fin 2) ℝ) (y : ℝ) :
    Polynomial.eval y (lineY0 f) =
      MvPolynomial.eval (fun i : Fin 2 => if i = 0 then 0 else y) f := by
  change (Polynomial.evalRingHom y)
      (MvPolynomial.eval₂Hom Polynomial.C
        (fun i : Fin 2 => if i = 0 then Polynomial.C 0 else Polynomial.X) f) = _
  rw [MvPolynomial.map_eval₂Hom]
  apply MvPolynomial.eval₂Hom_congr <;> try rfl
  · ext a
    simp
  · funext i
    by_cases hi : i = 0 <;> simp [hi]

private lemma polynomial_eval_eq_eval_zero_of_bdd (p : Polynomial ℝ)
    (hbddBelow : BddBelow (Set.range fun x : ℝ => Polynomial.eval x p))
    (hbddAbove : BddAbove (Set.range fun x : ℝ => Polynomial.eval x p)) :
    ∀ x : ℝ, Polynomial.eval x p = Polynomial.eval 0 p := by
  rcases hbddBelow with ⟨l, hl⟩
  rcases hbddAbove with ⟨u, hu⟩
  have hbounded : IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun x : ℝ => |Polynomial.eval x p|) := by
    refine Filter.isBoundedUnder_of ⟨max |l| |u|, ?_⟩
    intro x
    have hle : Polynomial.eval x p ≤ u := hu ⟨x, rfl⟩
    have hge : l ≤ Polynomial.eval x p := hl ⟨x, rfl⟩
    rw [abs_le]
    constructor <;>
      nlinarith [le_abs_self u, (abs_le.mp (le_refl |l|)).1,
        le_max_left (|l|) (|u|), le_max_right (|l|) (|u|)]
  have hdeg : p.degree ≤ 0 := (Polynomial.abs_isBoundedUnder_iff p).1 hbounded
  intro x
  rw [Polynomial.eq_C_of_degree_le_zero hdeg]
  simp

private lemma lineX_bddBelow (f : MvPolynomial (Fin 2) ℝ) (y : ℝ)
    (hbdd : BddBelow (putnamRange f)) :
    BddBelow (Set.range fun x : ℝ => Polynomial.eval x (lineX f y)) := by
  rcases hbdd with ⟨l, hl⟩
  refine ⟨l, ?_⟩
  rintro z ⟨x, rfl⟩
  exact hl ⟨fun i : Fin 2 => if i = 0 then x else y, (lineX_eval f x y).symm⟩

private lemma lineX_bddAbove (f : MvPolynomial (Fin 2) ℝ) (y : ℝ)
    (hbdd : BddAbove (putnamRange f)) :
    BddAbove (Set.range fun x : ℝ => Polynomial.eval x (lineX f y)) := by
  rcases hbdd with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  rintro z ⟨x, rfl⟩
  exact hu ⟨fun i : Fin 2 => if i = 0 then x else y, (lineX_eval f x y).symm⟩

private lemma lineY0_bddBelow (f : MvPolynomial (Fin 2) ℝ)
    (hbdd : BddBelow (putnamRange f)) :
    BddBelow (Set.range fun y : ℝ => Polynomial.eval y (lineY0 f)) := by
  rcases hbdd with ⟨l, hl⟩
  refine ⟨l, ?_⟩
  rintro z ⟨y, rfl⟩
  exact hl ⟨fun i : Fin 2 => if i = 0 then 0 else y, (lineY0_eval f y).symm⟩

private lemma lineY0_bddAbove (f : MvPolynomial (Fin 2) ℝ)
    (hbdd : BddAbove (putnamRange f)) :
    BddAbove (Set.range fun y : ℝ => Polynomial.eval y (lineY0 f)) := by
  rcases hbdd with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  rintro z ⟨y, rfl⟩
  exact hu ⟨fun i : Fin 2 => if i = 0 then 0 else y, (lineY0_eval f y).symm⟩

private lemma putnamRange_eq_singleton_of_bdd (f : MvPolynomial (Fin 2) ℝ)
    (hbddBelow : BddBelow (putnamRange f)) (hbddAbove : BddAbove (putnamRange f)) :
    putnamRange f = {MvPolynomial.eval (fun _ : Fin 2 => 0) f} := by
  have hxconst : ∀ y x : ℝ,
      MvPolynomial.eval (fun i : Fin 2 => if i = 0 then x else y) f =
        MvPolynomial.eval (fun i : Fin 2 => if i = 0 then 0 else y) f := by
    intro y x
    have h := polynomial_eval_eq_eval_zero_of_bdd (lineX f y)
      (lineX_bddBelow f y hbddBelow) (lineX_bddAbove f y hbddAbove) x
    simpa [lineX_eval] using h
  have hyconst : ∀ y : ℝ,
      MvPolynomial.eval (fun i : Fin 2 => if i = 0 then 0 else y) f =
        MvPolynomial.eval (fun _ : Fin 2 => 0) f := by
    intro y
    have h := polynomial_eval_eq_eval_zero_of_bdd (lineY0 f)
      (lineY0_bddBelow f hbddBelow) (lineY0_bddAbove f hbddAbove) y
    simpa [lineY0_eval] using h
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    have hxvec : (fun i : Fin 2 => if i = 0 then x 0 else x 1) = x := by
      funext i
      fin_cases i <;> simp
    rw [← hxvec, hxconst (x 1) (x 0), hyconst (x 1)]
    simp
  · intro hz
    rw [Set.mem_singleton_iff] at hz
    exact ⟨fun _ : Fin 2 => 0, hz.symm⟩

private lemma putnamRange_isPreconnected (f : MvPolynomial (Fin 2) ℝ) :
    IsPreconnected (putnamRange f) := by
  have h := (isPreconnected_univ : IsPreconnected (Set.univ : Set (Fin 2 → ℝ))).image
    (fun x => MvPolynomial.eval x f) (MvPolynomial.continuous_eval f).continuousOn
  convert h using 1
  ext z
  simp [putnamRange]

private lemma putnamRange_mem_solution (f : MvPolynomial (Fin 2) ℝ) :
    putnamRange f ∈ putnam_1969_a1_solution := by
  by_cases hb : BddBelow (putnamRange f)
  · by_cases ha : BddAbove (putnamRange f)
    · have h := putnamRange_eq_singleton_of_bdd f hb ha
      rw [h]
      rw [putnam_1969_a1_solution]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨MvPolynomial.eval (fun _ : Fin 2 => 0) f, rfl⟩))))
    ·
      have hs := putnamRange_isPreconnected f
      have hIoi : Ioi (sInf (putnamRange f)) ⊆ putnamRange f :=
        hs.Ioi_csInf_subset hb ha
      by_cases hmem : sInf (putnamRange f) ∈ putnamRange f
      · have h : putnamRange f = Ici (sInf (putnamRange f)) := by
          ext z
          constructor
          · intro hz
            exact csInf_le hb hz
          · intro hz
            change sInf (putnamRange f) ≤ z at hz
            rcases eq_or_lt_of_le hz with rfl | hlt
            · exact hmem
            · exact hIoi hlt
        rw [h]
        rw [putnam_1969_a1_solution]
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨sInf (putnamRange f), rfl⟩)))
      · have h : putnamRange f = Ioi (sInf (putnamRange f)) := by
          ext z
          constructor
          · intro hz
            exact lt_of_le_of_ne (csInf_le hb hz) (fun h => hmem (h ▸ hz))
          · intro hz
            exact hIoi hz
        rw [h]
        rw [putnam_1969_a1_solution]
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨sInf (putnamRange f), rfl⟩))))
  · by_cases ha : BddAbove (putnamRange f)
    ·
      have hs := putnamRange_isPreconnected f
      have hIio : Iio (sSup (putnamRange f)) ⊆ putnamRange f :=
        hs.Iio_csSup_subset hb ha
      by_cases hmem : sSup (putnamRange f) ∈ putnamRange f
      · have h : putnamRange f = Iic (sSup (putnamRange f)) := by
          ext z
          constructor
          · intro hz
            exact le_csSup ha hz
          · intro hz
            change z ≤ sSup (putnamRange f) at hz
            rcases eq_or_lt_of_le hz with rfl | hlt
            · exact hmem
            · exact hIio hlt
        rw [h]
        rw [putnam_1969_a1_solution]
        exact Or.inr (Or.inl ⟨sSup (putnamRange f), rfl⟩)
      · have h : putnamRange f = Iio (sSup (putnamRange f)) := by
          ext z
          constructor
          · intro hz
            exact lt_of_le_of_ne (le_csSup ha hz) (fun h => hmem (h ▸ hz))
          · intro hz
            exact hIio hz
        rw [h]
        rw [putnam_1969_a1_solution]
        exact Or.inr (Or.inr (Or.inl ⟨sSup (putnamRange f), rfl⟩))
    · have h : putnamRange f = univ :=
        (putnamRange_isPreconnected f).eq_univ_of_unbounded hb ha
      rw [h]
      rw [putnam_1969_a1_solution]
      simp

private def openCorePoly : MvPolynomial (Fin 2) ℝ :=
  (MvPolynomial.X (0 : Fin 2)) ^ 2 +
    (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) - MvPolynomial.C (1 : ℝ)) ^ 2

private lemma openCore_eval_pos (x : Fin 2 → ℝ) :
    0 < x 0 ^ 2 + (x 0 * x 1 - 1) ^ 2 := by
  have hnonneg1 : 0 ≤ x 0 ^ 2 := sq_nonneg _
  have hnonneg2 : 0 ≤ (x 0 * x 1 - 1) ^ 2 := sq_nonneg _
  refine lt_of_le_of_ne (add_nonneg hnonneg1 hnonneg2) ?_
  intro hzero
  have hparts := (add_eq_zero_iff_of_nonneg hnonneg1 hnonneg2).mp hzero.symm
  have hx0 : x 0 = 0 := sq_eq_zero_iff.mp hparts.1
  have hbad : x 0 * x 1 - 1 = 0 := sq_eq_zero_iff.mp hparts.2
  rw [hx0] at hbad
  norm_num at hbad

private lemma putnamRange_X :
    putnamRange (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ) = univ := by
  ext z
  constructor
  · intro hz
    exact trivial
  · intro hz
    exact ⟨fun i : Fin 2 => if i = 0 then z else 0, by simp [MvPolynomial.eval_X]⟩

private lemma putnamRange_C (a : ℝ) :
    putnamRange (MvPolynomial.C a : MvPolynomial (Fin 2) ℝ) = {a} := by
  ext z
  constructor
  · rintro ⟨x, hx⟩
    simp [hx.symm]
  · intro hz
    rw [Set.mem_singleton_iff] at hz
    exact ⟨fun _ : Fin 2 => 0, by simp [hz]⟩

private lemma putnamRange_Ici (a : ℝ) :
    putnamRange ((MvPolynomial.X (0 : Fin 2)) ^ 2 + MvPolynomial.C a :
      MvPolynomial (Fin 2) ℝ) = Ici a := by
  ext z
  constructor
  · rintro ⟨x, hx⟩
    change a ≤ z
    rw [← hx]
    simp only [map_add, map_pow, MvPolynomial.eval_X, MvPolynomial.eval_C]
    nlinarith [sq_nonneg (x 0)]
  · intro hz
    change a ≤ z at hz
    refine ⟨fun i : Fin 2 => if i = 0 then Real.sqrt (z - a) else 0, ?_⟩
    simp only [map_add, map_pow, MvPolynomial.eval_X, MvPolynomial.eval_C]
    have hnonneg : 0 ≤ z - a := sub_nonneg.mpr hz
    simp [Real.sq_sqrt hnonneg]

private lemma putnamRange_Iic (a : ℝ) :
    putnamRange (MvPolynomial.C a - (MvPolynomial.X (0 : Fin 2)) ^ 2 :
      MvPolynomial (Fin 2) ℝ) = Iic a := by
  ext z
  constructor
  · rintro ⟨x, hx⟩
    change z ≤ a
    rw [← hx]
    simp only [map_sub, map_pow, MvPolynomial.eval_X, MvPolynomial.eval_C]
    nlinarith [sq_nonneg (x 0)]
  · intro hz
    change z ≤ a at hz
    refine ⟨fun i : Fin 2 => if i = 0 then Real.sqrt (a - z) else 0, ?_⟩
    simp only [map_sub, map_pow, MvPolynomial.eval_X, MvPolynomial.eval_C]
    have hnonneg : 0 ≤ a - z := sub_nonneg.mpr hz
    simp [Real.sq_sqrt hnonneg]

private lemma putnamRange_Ioi (a : ℝ) :
    putnamRange (openCorePoly + MvPolynomial.C a : MvPolynomial (Fin 2) ℝ) = Ioi a := by
  ext z
  constructor
  · rintro ⟨x, hx⟩
    change a < z
    rw [← hx]
    simp only [openCorePoly, map_add, map_sub, map_mul, map_pow, MvPolynomial.eval_X,
      MvPolynomial.eval_C]
    linarith [openCore_eval_pos x]
  · intro hz
    change a < z at hz
    let t : ℝ := Real.sqrt (z - a)
    have htpos : 0 < t := by
      dsimp [t]
      exact Real.sqrt_pos.2 (sub_pos.mpr hz)
    have htne : t ≠ 0 := ne_of_gt htpos
    refine ⟨fun i : Fin 2 => if i = 0 then t else t⁻¹, ?_⟩
    simp only [openCorePoly, map_add, map_sub, map_mul, map_pow, MvPolynomial.eval_X,
      MvPolynomial.eval_C]
    have hsq : t ^ 2 = z - a := by
      dsimp [t]
      exact Real.sq_sqrt (le_of_lt (sub_pos.mpr hz))
    have hmul : t * t⁻¹ = 1 := mul_inv_cancel₀ htne
    simp [hmul, hsq]

private lemma putnamRange_Iio (a : ℝ) :
    putnamRange (MvPolynomial.C a - openCorePoly : MvPolynomial (Fin 2) ℝ) = Iio a := by
  ext z
  constructor
  · rintro ⟨x, hx⟩
    change z < a
    rw [← hx]
    simp only [openCorePoly, map_sub, map_add, map_mul, map_pow, MvPolynomial.eval_X,
      MvPolynomial.eval_C]
    linarith [openCore_eval_pos x]
  · intro hz
    change z < a at hz
    let t : ℝ := Real.sqrt (a - z)
    have htpos : 0 < t := by
      dsimp [t]
      exact Real.sqrt_pos.2 (sub_pos.mpr hz)
    have htne : t ≠ 0 := ne_of_gt htpos
    refine ⟨fun i : Fin 2 => if i = 0 then t else t⁻¹, ?_⟩
    simp only [openCorePoly, map_sub, map_add, map_mul, map_pow, MvPolynomial.eval_X,
      MvPolynomial.eval_C]
    have hsq : t ^ 2 = a - z := by
      dsimp [t]
      exact Real.sq_sqrt (le_of_lt (sub_pos.mpr hz))
    have hmul : t * t⁻¹ = 1 := mul_inv_cancel₀ htne
    simp [hmul, hsq]

/--
What are the possible ranges (across all real inputs $x$ and $y$) of a polynomial $f(x, y)$ with real coefficients?
-/
theorem putnam_1969_a1
: {{z : ℝ | ∃ x : Fin 2 → ℝ, MvPolynomial.eval x f = z} | f : MvPolynomial (Fin 2) ℝ} = putnam_1969_a1_solution :=
by
  change {putnamRange f | f : MvPolynomial (Fin 2) ℝ} = putnam_1969_a1_solution
  ext s
  constructor
  · rintro ⟨f, rfl⟩
    exact putnamRange_mem_solution f
  · intro hs
    rw [putnam_1969_a1_solution] at hs
    simp only [Set.mem_setOf_eq] at hs
    rcases hs with h_univ | ⟨a, h_Iic⟩ | ⟨a, h_Iio⟩ | ⟨a, h_Ici⟩ |
      ⟨a, h_Ioi⟩ | ⟨a, h_singleton⟩
    · exact ⟨MvPolynomial.X (0 : Fin 2), by rw [h_univ]; exact putnamRange_X⟩
    · exact ⟨MvPolynomial.C a - (MvPolynomial.X (0 : Fin 2)) ^ 2,
        by rw [h_Iic]; exact putnamRange_Iic a⟩
    · exact ⟨MvPolynomial.C a - openCorePoly,
        by rw [h_Iio]; exact putnamRange_Iio a⟩
    · exact ⟨(MvPolynomial.X (0 : Fin 2)) ^ 2 + MvPolynomial.C a,
        by rw [h_Ici]; exact putnamRange_Ici a⟩
    · exact ⟨openCorePoly + MvPolynomial.C a,
        by rw [h_Ioi]; exact putnamRange_Ioi a⟩
    · exact ⟨MvPolynomial.C a, by
        rw [h_singleton]
        exact putnamRange_C a⟩

end
