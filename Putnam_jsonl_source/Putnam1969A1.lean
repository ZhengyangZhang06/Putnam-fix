import Mathlib

open Matrix Filter Topology Set Nat

-- {{x} | x : ℝ} ∪ {Set.Ici x | x : ℝ} ∪ {Set.Iic x | x : ℝ} ∪ {Set.Iio x | x : ℝ} ∪ {Set.Ioi x | x : ℝ} ∪ {Set.univ}
/--
What are the possible ranges (across all real inputs $x$ and $y$) of a polynomial $f(x, y)$ with real coefficients?
-/
theorem putnam_1969_a1
: {{z : ℝ | ∃ x : Fin 2 → ℝ, MvPolynomial.eval x f = z} | f : MvPolynomial (Fin 2) ℝ} = (({{x} | x : ℝ} ∪ {Set.Ici x | x : ℝ} ∪ {Set.Iic x | x : ℝ} ∪ {Set.Iio x | x : ℝ} ∪ {Set.Ioi x | x : ℝ} ∪ {Set.univ}) : Set (Set ℝ) ) := by
  have h_pos_sum (u v : ℝ) : 0 < (u * v - 1) ^ 2 + v ^ 2 := by
    have hnot : (u * v - 1) ^ 2 + v ^ 2 ≠ 0 := by
      intro h
      have hv2 : v ^ 2 = 0 := by nlinarith [sq_nonneg (u * v - 1), sq_nonneg v]
      have hv : v = 0 := sq_eq_zero_iff.mp hv2
      have hu2 : (u * v - 1) ^ 2 = 0 := by
        nlinarith [sq_nonneg (u * v - 1), sq_nonneg v]
      have hu : u * v - 1 = 0 := sq_eq_zero_iff.mp hu2
      rw [hv, mul_zero, zero_sub] at hu
      norm_num at hu
    exact lt_of_le_of_ne (add_nonneg (sq_nonneg _) (sq_nonneg _)) (Ne.symm hnot)
  have h_range_singleton (a : ℝ) :
      {z : ℝ | ∃ x : Fin 2 → ℝ, MvPolynomial.eval x (MvPolynomial.C a) = z} =
        ({a} : Set ℝ) := by
    ext z
    simp
  have h_range_Ici (a : ℝ) :
      {z : ℝ | ∃ x : Fin 2 → ℝ,
        MvPolynomial.eval x ((MvPolynomial.X (0 : Fin 2)) ^ 2 + MvPolynomial.C a) = z} =
        Set.Ici a := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      simp
      positivity
    · intro hz
      refine ⟨fun i : Fin 2 => if i = 0 then Real.sqrt (z - a) else 0, ?_⟩
      simp [Real.sq_sqrt (sub_nonneg.mpr hz)]
  have h_range_Iic (a : ℝ) :
      {z : ℝ | ∃ x : Fin 2 → ℝ,
        MvPolynomial.eval x (MvPolynomial.C a - (MvPolynomial.X (0 : Fin 2)) ^ 2) = z} =
        Set.Iic a := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      simp
      positivity
    · intro hz
      refine ⟨fun i : Fin 2 => if i = 0 then Real.sqrt (a - z) else 0, ?_⟩
      simp [Real.sq_sqrt (sub_nonneg.mpr hz)]
  have h_range_Ioi (a : ℝ) :
      {z : ℝ | ∃ x : Fin 2 → ℝ,
        MvPolynomial.eval x
          (MvPolynomial.C a +
            (((MvPolynomial.X (0 : Fin 2)) * (MvPolynomial.X (1 : Fin 2)) - 1) ^ 2 +
              (MvPolynomial.X (1 : Fin 2)) ^ 2)) = z} =
        Set.Ioi a := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      simp
      have hpos : 0 < (x 0 * x 1 - 1) ^ 2 + (x 1) ^ 2 := h_pos_sum (x 0) (x 1)
      linarith
    · intro hz
      have hzlt : a < z := by simpa using hz
      let r := Real.sqrt ((z - a) / 2)
      have hnonneg : 0 ≤ (z - a) / 2 := by nlinarith
      have hposarg : 0 < (z - a) / 2 := by nlinarith
      have hr2 : r ^ 2 = (z - a) / 2 := by simpa [r] using Real.sq_sqrt hnonneg
      have hrpos : 0 < r := Real.sqrt_pos.2 hposarg
      refine ⟨fun i : Fin 2 => if i = 0 then (1 + r) / r else r, ?_⟩
      simp
      have hmul : ((1 + r) / r) * r = 1 + r := div_mul_cancel₀ (1 + r) hrpos.ne'
      nlinarith [hr2, hmul]
  have h_range_Iio (a : ℝ) :
      {z : ℝ | ∃ x : Fin 2 → ℝ,
        MvPolynomial.eval x
          (MvPolynomial.C a -
            (((MvPolynomial.X (0 : Fin 2)) * (MvPolynomial.X (1 : Fin 2)) - 1) ^ 2 +
              (MvPolynomial.X (1 : Fin 2)) ^ 2)) = z} =
        Set.Iio a := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      simp
      have hpos : 0 < (x 0 * x 1 - 1) ^ 2 + (x 1) ^ 2 := h_pos_sum (x 0) (x 1)
      linarith
    · intro hz
      have hzlt : z < a := by simpa using hz
      let r := Real.sqrt ((a - z) / 2)
      have hnonneg : 0 ≤ (a - z) / 2 := by nlinarith
      have hposarg : 0 < (a - z) / 2 := by nlinarith
      have hr2 : r ^ 2 = (a - z) / 2 := by simpa [r] using Real.sq_sqrt hnonneg
      have hrpos : 0 < r := Real.sqrt_pos.2 hposarg
      refine ⟨fun i : Fin 2 => if i = 0 then (1 + r) / r else r, ?_⟩
      simp
      have hmul : ((1 + r) / r) * r = 1 + r := div_mul_cancel₀ (1 + r) hrpos.ne'
      nlinarith [hr2, hmul]
  have h_range_univ :
      {z : ℝ | ∃ x : Fin 2 → ℝ, MvPolynomial.eval x (MvPolynomial.X (0 : Fin 2)) = z} =
        Set.univ := by
    ext z
    constructor
    · intro hz
      trivial
    · intro hz
      exact ⟨fun i : Fin 2 => if i = 0 then z else 0, by simp⟩
  have h_range_bdd_eq_singleton (f : MvPolynomial (Fin 2) ℝ)
      (hb : BddBelow {z : ℝ | ∃ x : Fin 2 → ℝ, MvPolynomial.eval x f = z})
      (ha : BddAbove {z : ℝ | ∃ x : Fin 2 → ℝ, MvPolynomial.eval x f = z}) :
      ∃ c : ℝ, {z : ℝ | ∃ x : Fin 2 → ℝ, MvPolynomial.eval x f = z} = ({c} : Set ℝ) := by
    obtain ⟨lo, hlo⟩ := hb
    obtain ⟨hi, hhi⟩ := ha
    refine ⟨MvPolynomial.eval (fun _ : Fin 2 => 0) f, ?_⟩
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      let P : Polynomial ℝ :=
        MvPolynomial.eval₂ Polynomial.C (fun i => Polynomial.C (x i) * Polynomial.X) f
      have hline (t : ℝ) :
          Polynomial.eval t P = MvPolynomial.eval (fun i => x i * t) f := by
        dsimp [P]
        calc
          Polynomial.eval t
              (MvPolynomial.eval₂ Polynomial.C
                (fun i => Polynomial.C (x i) * Polynomial.X) f)
              = (Polynomial.evalRingHom t)
                (MvPolynomial.eval₂ Polynomial.C
                  (fun i => Polynomial.C (x i) * Polynomial.X) f) := rfl
          _ = MvPolynomial.eval₂ ((Polynomial.evalRingHom t).comp Polynomial.C)
                ((Polynomial.evalRingHom t) ∘
                  fun i => Polynomial.C (x i) * Polynomial.X) f := by
                rw [MvPolynomial.eval₂_comp_left]
          _ = MvPolynomial.eval₂ (RingHom.id ℝ) (fun i => x i * t) f := by
                change
                  (MvPolynomial.eval₂Hom ((Polynomial.evalRingHom t).comp Polynomial.C)
                    ((Polynomial.evalRingHom t) ∘
                      fun i => Polynomial.C (x i) * Polynomial.X)) f =
                    (MvPolynomial.eval₂Hom (RingHom.id ℝ) (fun i => x i * t)) f
                apply MvPolynomial.eval₂Hom_congr
                · ext r
                  change Polynomial.eval t (Polynomial.C r) = r
                  simp
                · funext i
                  change Polynomial.eval t (Polynomial.C (x i) * Polynomial.X) = x i * t
                  simp
                · rfl
          _ = MvPolynomial.eval (fun i => x i * t) f := by
                rw [MvPolynomial.eval₂_id]
      have hPbdd : IsBoundedUnder (· ≤ ·) atTop (fun t : ℝ => |Polynomial.eval t P|) := by
        refine ⟨max |lo| |hi|, eventually_map.mpr (Eventually.of_forall ?_)⟩
        intro t
        have hmem :
            Polynomial.eval t P ∈
              {z : ℝ | ∃ y : Fin 2 → ℝ, MvPolynomial.eval y f = z} := by
          refine ⟨fun i => x i * t, ?_⟩
          exact (hline t).symm
        have hlow : lo ≤ Polynomial.eval t P := hlo hmem
        have hhigh : Polynomial.eval t P ≤ hi := hhi hmem
        apply abs_le'.2
        constructor
        · exact hhigh.trans ((le_abs_self hi).trans (le_max_right _ _))
        · exact (neg_le_neg hlow).trans ((neg_le_abs lo).trans (le_max_left _ _))
      have hdeg : P.degree ≤ 0 := (Polynomial.abs_isBoundedUnder_iff P).1 hPbdd
      have hconst : P = Polynomial.C (P.coeff 0) := Polynomial.eq_C_of_degree_le_zero hdeg
      have heq : MvPolynomial.eval x f = MvPolynomial.eval (fun _ : Fin 2 => 0) f := by
        calc
          MvPolynomial.eval x f =
              MvPolynomial.eval (fun i => x i * (1 : ℝ)) f := by
              rw [show (fun i => x i * (1 : ℝ)) = x by funext i; simp]
          _ = Polynomial.eval 1 P := (hline 1).symm
          _ = Polynomial.eval 0 P := by rw [hconst]; simp
          _ = MvPolynomial.eval (fun i => x i * (0 : ℝ)) f := hline 0
          _ = MvPolynomial.eval (fun _ : Fin 2 => 0) f := by
              rw [show (fun i => x i * (0 : ℝ)) = (fun _ : Fin 2 => 0) by
                funext i
                simp]
      exact by simp [heq]
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact ⟨fun _ : Fin 2 => 0, rfl⟩
  ext S
  constructor
  · rintro ⟨f, rfl⟩
    let s : Set ℝ := {z : ℝ | ∃ x : Fin 2 → ℝ, MvPolynomial.eval x f = z}
    have hsdef : s = {z : ℝ | ∃ x : Fin 2 → ℝ, MvPolynomial.eval x f = z} := rfl
    change s ∈
      (({{x} | x : ℝ} ∪ {Set.Ici x | x : ℝ} ∪ {Set.Iic x | x : ℝ} ∪
        {Set.Iio x | x : ℝ} ∪ {Set.Ioi x | x : ℝ} ∪ {Set.univ}) : Set (Set ℝ))
    have hpre : IsPreconnected s := by
      have hcont : Continuous (fun x : Fin 2 → ℝ => MvPolynomial.eval x f) :=
        MvPolynomial.continuous_eval f
      have hsrange : s = Set.range (fun x : Fin 2 → ℝ => MvPolynomial.eval x f) := by
        ext z
        simp [s, Set.range]
      rw [hsrange]
      exact isPreconnected_range hcont
    have hclass := hpre.mem_intervals
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hclass
    have hnonempty : s.Nonempty :=
      ⟨MvPolynomial.eval (fun _ : Fin 2 => 0) f, ⟨fun _ : Fin 2 => 0, rfl⟩⟩
    rcases hclass with hIcc | hIco | hIoc | hIoo | hIci | hIoi | hIic | hIio | huniv | hempty
    · have hb : BddBelow s := by rw [hIcc]; simp
      have ha : BddAbove s := by rw [hIcc]; simp
      rcases h_range_bdd_eq_singleton f (by simpa [hsdef] using hb)
          (by simpa [hsdef] using ha) with ⟨c, hc⟩
      rw [← hsdef] at hc
      rw [hc]
      simp
    · have hb : BddBelow s := by rw [hIco]; simp
      have ha : BddAbove s := by rw [hIco]; simp
      rcases h_range_bdd_eq_singleton f (by simpa [hsdef] using hb)
          (by simpa [hsdef] using ha) with ⟨c, hc⟩
      rw [← hsdef] at hc
      rw [hc]
      simp
    · have hb : BddBelow s := by rw [hIoc]; simp
      have ha : BddAbove s := by rw [hIoc]; simp
      rcases h_range_bdd_eq_singleton f (by simpa [hsdef] using hb)
          (by simpa [hsdef] using ha) with ⟨c, hc⟩
      rw [← hsdef] at hc
      rw [hc]
      simp
    · have hb : BddBelow s := by rw [hIoo]; simp
      have ha : BddAbove s := by rw [hIoo]; simp
      rcases h_range_bdd_eq_singleton f (by simpa [hsdef] using hb)
          (by simpa [hsdef] using ha) with ⟨c, hc⟩
      rw [← hsdef] at hc
      rw [hc]
      simp
    · rw [hIci]
      simp
    · rw [hIoi]
      simp
    · rw [hIic]
      simp
    · rw [hIio]
      simp
    · rw [huniv]
      simp
    · rw [hempty] at hnonempty
      rcases hnonempty with ⟨x, hx⟩
      cases hx
  · intro hS
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff] at hS
    rcases hS with (((((h | h) | h) | h) | h) | h)
    · rcases h with ⟨a, rfl⟩
      refine ⟨MvPolynomial.C a, ?_⟩
      exact h_range_singleton a
    · rcases h with ⟨a, rfl⟩
      refine ⟨(MvPolynomial.X (0 : Fin 2)) ^ 2 + MvPolynomial.C a, ?_⟩
      exact h_range_Ici a
    · rcases h with ⟨a, rfl⟩
      refine ⟨MvPolynomial.C a - (MvPolynomial.X (0 : Fin 2)) ^ 2, ?_⟩
      exact h_range_Iic a
    · rcases h with ⟨a, rfl⟩
      refine ⟨MvPolynomial.C a -
        (((MvPolynomial.X (0 : Fin 2)) * (MvPolynomial.X (1 : Fin 2)) - 1) ^ 2 +
          (MvPolynomial.X (1 : Fin 2)) ^ 2), ?_⟩
      exact h_range_Iio a
    · rcases h with ⟨a, rfl⟩
      refine ⟨MvPolynomial.C a +
        (((MvPolynomial.X (0 : Fin 2)) * (MvPolynomial.X (1 : Fin 2)) - 1) ^ 2 +
          (MvPolynomial.X (1 : Fin 2)) ^ 2), ?_⟩
      exact h_range_Ioi a
    · subst S
      refine ⟨MvPolynomial.X (0 : Fin 2), ?_⟩
      exact h_range_univ
