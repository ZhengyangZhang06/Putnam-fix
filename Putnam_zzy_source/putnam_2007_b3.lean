import Mathlib

open Set Nat Function

noncomputable abbrev putnam_2007_b3_solution : ℝ :=
  (((2 : ℝ) ^ 2006) *
    (((1 + Real.sqrt 5) / 2) ^ 4017 -
      ((1 - Real.sqrt 5) / 2) ^ 4017)) / Real.sqrt 5

private lemma putnam_2007_b3_floor_step (m : ℤ) :
    ⌊((3 * (m : ℝ) + (⌊(m : ℝ) * Real.sqrt 5⌋ : ℝ)) * Real.sqrt 5)⌋ =
      5 * m + 3 * ⌊(m : ℝ) * Real.sqrt 5⌋ := by
  let t : ℝ := Real.sqrt 5
  let y : ℤ := ⌊(m : ℝ) * t⌋
  change ⌊((3 * (m : ℝ) + (y : ℝ)) * t)⌋ = 5 * m + 3 * y
  have ht_sq : t ^ 2 = 5 := by
    dsimp [t]
    exact Real.sq_sqrt (by norm_num)
  have htwo_lt_t : (2 : ℝ) < t := by
    dsimp [t]
    rw [← Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)]
    exact Real.sqrt_lt_sqrt (by positivity) (by norm_num)
  have ht_lt_three : t < (3 : ℝ) := by
    dsimp [t]
    rw [← Real.sqrt_sq (show (0 : ℝ) ≤ 3 by norm_num)]
    exact Real.sqrt_lt_sqrt (by positivity) (by norm_num)
  have hfactor_pos : 0 < 3 - t := by linarith
  have hfactor_lt_one : 3 - t < 1 := by linarith
  have hfloor_le : (y : ℝ) ≤ (m : ℝ) * t := by
    dsimp [y]
    exact Int.floor_le _
  have hfloor_lt : (m : ℝ) * t < (y : ℝ) + 1 := by
    dsimp [y]
    exact Int.lt_floor_add_one _
  let d : ℝ := (m : ℝ) * t - (y : ℝ)
  have hd_nonneg : 0 ≤ d := by
    dsimp [d]
    linarith
  have hd_lt_one : d < 1 := by
    dsimp [d]
    linarith
  have hdf_nonneg : 0 ≤ d * (3 - t) := mul_nonneg hd_nonneg hfactor_pos.le
  have hdf_lt_one : d * (3 - t) < 1 := by
    calc
      d * (3 - t) < 1 * (3 - t) := by
        exact mul_lt_mul_of_pos_right hd_lt_one hfactor_pos
      _ < 1 := by linarith
  have hdecomp :
      ((3 * (m : ℝ) + (y : ℝ)) * t) =
        ((5 * m + 3 * y : ℤ) : ℝ) + d * (3 - t) := by
    dsimp [d]
    norm_num [Int.cast_add, Int.cast_mul]
    ring_nf
    rw [ht_sq]
    ring
  exact Int.floor_eq_iff.mpr
    ⟨by rw [hdecomp]; linarith, by rw [hdecomp]; linarith⟩

/--
Let $x_0 = 1$ and for $n \geq 0$, let $x_{n+1} = 3x_n + \lfloor x_n \sqrt{5} \rfloor$. In particular, $x_1 = 5$, $x_2 = 26$, $x_3 = 136$, $x_4 = 712$. Find a closed-form expression for $x_{2007}$. ($\lfloor a \rfloor$ means the largest integer $\leq a$.)
-/
theorem putnam_2007_b3
(x : ℕ → ℝ)
(hx0 : x 0 = 1)
(hx : ∀ n : ℕ, x (n + 1) = 3 * (x n) + ⌊(x n) * Real.sqrt 5⌋)
: (x 2007 = putnam_2007_b3_solution) :=
by
  let t : ℝ := Real.sqrt 5
  let r : ℝ := 3 + t
  let s : ℝ := 3 - t
  let a : ℕ → ℝ := fun n => ((2 + t) * r ^ n + (t - 2) * s ^ n) / (2 * t)
  have hx_int : ∀ n : ℕ, ∃ m : ℤ, x n = m := by
    intro n
    induction n with
    | zero =>
        exact ⟨1, by simpa using hx0⟩
    | succ n ih =>
        rcases ih with ⟨m, hm⟩
        refine ⟨3 * m + ⌊(m : ℝ) * Real.sqrt 5⌋, ?_⟩
        rw [hx n, hm]
        norm_num [Int.cast_add, Int.cast_mul]
  have hx_rec : ∀ n : ℕ, x (n + 2) = 6 * x (n + 1) - 4 * x n := by
    intro n
    rcases hx_int n with ⟨m, hm⟩
    have hx_succ :
        x (n + 1) = 3 * (m : ℝ) + (⌊(m : ℝ) * Real.sqrt 5⌋ : ℝ) := by
      rw [hx n, hm]
    calc
      x (n + 2) =
          3 * x (n + 1) + (⌊(x (n + 1)) * Real.sqrt 5⌋ : ℝ) := by
        simpa [Nat.add_assoc] using hx (n + 1)
      _ = 3 * (3 * (m : ℝ) + (⌊(m : ℝ) * Real.sqrt 5⌋ : ℝ)) +
            (5 * m + 3 * ⌊(m : ℝ) * Real.sqrt 5⌋ : ℤ) := by
        rw [hx_succ, putnam_2007_b3_floor_step]
      _ = 6 * x (n + 1) - 4 * x n := by
        rw [hx_succ, hm]
        norm_num [Int.cast_add, Int.cast_mul]
        ring
  have ht_sq : t ^ 2 = 5 := by
    dsimp [t]
    exact Real.sq_sqrt (by norm_num)
  have ht_pos : 0 < t := by
    dsimp [t]
    positivity
  have ht_ne : t ≠ 0 := ne_of_gt ht_pos
  have hfloor_sqrt5 : ⌊Real.sqrt 5⌋ = (2 : ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor
    · exact (le_of_lt (by
        rw [← Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)]
        exact Real.sqrt_lt_sqrt (by positivity) (by norm_num)) :
          (2 : ℝ) ≤ Real.sqrt 5)
    · norm_num
      rw [← Real.sqrt_sq (show (0 : ℝ) ≤ 3 by norm_num)]
      exact Real.sqrt_lt_sqrt (by positivity) (by norm_num)
  have hr_char : r ^ 2 = 6 * r - 4 := by
    dsimp [r]
    nlinarith [ht_sq]
  have hs_char : s ^ 2 = 6 * s - 4 := by
    dsimp [s]
    nlinarith [ht_sq]
  have ha0 : a 0 = 1 := by
    dsimp [a]
    field_simp [ht_ne]
    ring
  have ha1 : a 1 = 5 := by
    dsimp [a, r, s]
    field_simp [ht_ne]
    ring
  have ha_rec : ∀ n : ℕ, a (n + 2) = 6 * a (n + 1) - 4 * a n := by
    intro n
    have hrpow : r ^ (n + 2) = 6 * r ^ (n + 1) - 4 * r ^ n := by
      calc
        r ^ (n + 2) = r ^ n * r ^ 2 := by rw [pow_add]
        _ = r ^ n * (6 * r - 4) := by rw [hr_char]
        _ = 6 * r ^ (n + 1) - 4 * r ^ n := by
          rw [pow_succ]
          ring
    have hspow : s ^ (n + 2) = 6 * s ^ (n + 1) - 4 * s ^ n := by
      calc
        s ^ (n + 2) = s ^ n * s ^ 2 := by rw [pow_add]
        _ = s ^ n * (6 * s - 4) := by rw [hs_char]
        _ = 6 * s ^ (n + 1) - 4 * s ^ n := by
          rw [pow_succ]
          ring
    dsimp [a]
    rw [hrpow, hspow]
    field_simp [ht_ne]
    ring
  have hxa_pair : ∀ n : ℕ, x n = a n ∧ x (n + 1) = a (n + 1) := by
    intro n
    induction n with
    | zero =>
        constructor
        · rw [hx0, ha0]
        · rw [ha1]
          rw [hx 0, hx0]
          norm_num [hfloor_sqrt5]
    | succ n ih =>
        constructor
        · exact ih.2
        · rw [hx_rec n, ha_rec n, ih.1, ih.2]
  have hfinal : x 2007 = a 2007 := (hxa_pair 2007).1
  have ha_closed : a 2007 = putnam_2007_b3_solution := by
    dsimp [a, r, s]
    let phi : ℝ := (1 + t) / 2
    let psi : ℝ := (1 - t) / 2
    have hcore (u v w : ℝ) :
        (u ^ 3 * (2 * u ^ 2) ^ 2007 + (-v ^ 3) * (2 * v ^ 2) ^ 2007) / (2 * w) =
          (((2 : ℝ) ^ 2006) * (u ^ 4017 - v ^ 4017)) / w := by
      have h2 : (2 : ℝ) ^ 2007 = (2 : ℝ) ^ 2006 * 2 := by
        rw [show (2007 : ℕ) = 2006 + 1 by norm_num]
        rw [pow_add]
        norm_num
      ring_nf
      rw [h2]
      ring
    have ht_cube : t ^ 3 = 5 * t := by
      calc
        t ^ 3 = t * t ^ 2 := by ring
        _ = t * 5 := by rw [ht_sq]
        _ = 5 * t := by ring
    have hphi3 : phi ^ 3 = 2 + t := by
      dsimp [phi]
      ring_nf
      nlinarith [ht_sq, ht_cube]
    have hpsi3 : psi ^ 3 = 2 - t := by
      dsimp [psi]
      ring_nf
      nlinarith [ht_sq, ht_cube]
    have hr_phi : 3 + t = 2 * phi ^ 2 := by
      dsimp [phi]
      ring_nf
      nlinarith [ht_sq]
    have hs_psi : 3 - t = 2 * psi ^ 2 := by
      dsimp [psi]
      ring_nf
      nlinarith [ht_sq]
    have hpsi_neg : t - 2 = -psi ^ 3 := by
      rw [hpsi3]
      ring
    change ((2 + t) * (3 + t) ^ 2007 + (t - 2) * (3 - t) ^ 2007) / (2 * t) =
      (((2 : ℝ) ^ 2006) * (phi ^ 4017 - psi ^ 4017)) / t
    rw [← hphi3, hpsi_neg, hr_phi, hs_psi]
    exact hcore phi psi t
  exact hfinal.trans ha_closed
