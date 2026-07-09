import Mathlib

private def putnam_2015_b3_coeff (t q : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | n + 2 => t * putnam_2015_b3_coeff t q (n + 1) + q * putnam_2015_b3_coeff t q n

private lemma putnam_2015_b3_coeff_nonneg_of_nonneg {t q : ℝ} (ht : 0 ≤ t) (hq : 0 ≤ q) :
    ∀ n : ℕ, 0 ≤ putnam_2015_b3_coeff t q n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simp [putnam_2015_b3_coeff]
  | one => simp [putnam_2015_b3_coeff]
  | more n ih1 ih2 =>
      simp [putnam_2015_b3_coeff]
      positivity

private lemma putnam_2015_b3_coeff_pos_of_pos {t q : ℝ} (ht : 0 < t) (hq : 0 < q) :
    ∀ n : ℕ, 0 < n → 0 < putnam_2015_b3_coeff t q n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      intro hn
      omega
  | one =>
      intro _hn
      simp [putnam_2015_b3_coeff]
  | more n _ih1 ih2 =>
      intro _hn
      simp [putnam_2015_b3_coeff]
      have hpos : 0 < putnam_2015_b3_coeff t q (n + 1) := ih2 (by omega)
      have hnonneg : 0 ≤ putnam_2015_b3_coeff t q n :=
        putnam_2015_b3_coeff_nonneg_of_nonneg (le_of_lt ht) (le_of_lt hq) n
      positivity

private lemma putnam_2015_b3_coeff_neg_left (t q : ℝ) :
    ∀ n : ℕ,
      putnam_2015_b3_coeff (-t) q n =
        (-1 : ℝ) ^ (n + 1) * putnam_2015_b3_coeff t q n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simp [putnam_2015_b3_coeff]
  | one => simp [putnam_2015_b3_coeff]
  | more n ih1 ih2 =>
      have hpow : (-1 : ℝ) ^ (n + 3) = (-1 : ℝ) ^ (n + 1) := by
        rw [show n + 3 = n + 1 + 2 by omega, pow_add]
        norm_num
      simp [putnam_2015_b3_coeff, ih1, ih2, hpow]
      ring

private lemma putnam_2015_b3_coeff_ne_zero_of_q_pos {t q : ℝ} (hq : 0 < q)
    {n : ℕ} (hn : 0 < n) (ht : t ≠ 0) :
    putnam_2015_b3_coeff t q n ≠ 0 := by
  rcases lt_or_gt_of_ne ht with htneg | htpos
  · have hpos : 0 < putnam_2015_b3_coeff (-t) q n :=
      putnam_2015_b3_coeff_pos_of_pos (by linarith) hq n hn
    have hrel := putnam_2015_b3_coeff_neg_left t q n
    intro hzero
    rw [hrel, hzero, mul_zero] at hpos
    exact (lt_irrefl (0 : ℝ) hpos)
  · exact ne_of_gt (putnam_2015_b3_coeff_pos_of_pos htpos hq n hn)

private def putnam_2015_b3_AP (M : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  (M 0 1 - M 0 0 = M 1 0 - M 0 1) ∧
    (M 1 0 - M 0 1 = M 1 1 - M 1 0)

private lemma putnam_2015_b3_smul_add_one_AP_iff
    (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : putnam_2015_b3_AP M) (α β : ℝ) :
    putnam_2015_b3_AP (α • M + β • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ↔ β = 0 := by
  constructor
  · intro h
    unfold putnam_2015_b3_AP at hM h
    have hfirst := h.1
    simp at hfirst
    have hscaled := congrArg (fun x : ℝ => α * x) hM.1
    ring_nf at hscaled hfirst
    nlinarith [hscaled, hfirst]
  · intro hβ
    subst β
    unfold putnam_2015_b3_AP at hM ⊢
    constructor
    · simp
      have hscaled := congrArg (fun x : ℝ => α * x) hM.1
      ring_nf at hscaled ⊢
      exact hscaled
    · simp
      have hscaled := congrArg (fun x : ℝ => α * x) hM.2
      ring_nf at hscaled ⊢
      exact hscaled

private lemma putnam_2015_b3_pow_succ
    (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : putnam_2015_b3_AP M) :
    ∀ n : ℕ,
      M ^ (n + 1) =
        (putnam_2015_b3_coeff (M 0 0 + M 1 1) (2 * (M 0 1 - M 0 0) ^ 2) (n + 1)) • M +
          ((2 * (M 0 1 - M 0 0) ^ 2) *
            putnam_2015_b3_coeff (M 0 0 + M 1 1) (2 * (M 0 1 - M 0 0) ^ 2) n) •
            (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro n
  induction n with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;> simp [putnam_2015_b3_coeff]
  | succ n ih =>
      unfold putnam_2015_b3_AP at hM
      have h10 : M 1 0 = 2 * M 0 1 - M 0 0 := by linarith [hM.1]
      have h11 : M 1 1 = 3 * M 0 1 - 2 * M 0 0 := by linarith [hM.1, hM.2]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [pow_succ, ih, Matrix.mul_apply, Fin.sum_univ_two, putnam_2015_b3_coeff, h10, h11] <;>
        ring

private lemma putnam_2015_b3_pow_succ_AP_iff
    (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : putnam_2015_b3_AP M) (n : ℕ) :
    putnam_2015_b3_AP (M ^ (n + 1)) ↔
      (2 * (M 0 1 - M 0 0) ^ 2) *
        putnam_2015_b3_coeff (M 0 0 + M 1 1) (2 * (M 0 1 - M 0 0) ^ 2) n = 0 := by
  rw [putnam_2015_b3_pow_succ M hM n]
  exact putnam_2015_b3_smul_add_one_AP_iff M hM
    (putnam_2015_b3_coeff (M 0 0 + M 1 1) (2 * (M 0 1 - M 0 0) ^ 2) (n + 1))
    ((2 * (M 0 1 - M 0 0) ^ 2) *
      putnam_2015_b3_coeff (M 0 0 + M 1 1) (2 * (M 0 1 - M 0 0) ^ 2) n)

abbrev putnam_2015_b3_solution : Set (Matrix (Fin 2) (Fin 2) ℝ) :=
  {M | ∃ a b : ℝ, M = !![a, a; a, a] ∨ M = !![3 * b, b; -b, -3 * b]}

/--
Let $S$ be the set of all $2 \times 2$ real matrices $M=\begin{pmatrix} a & b \\ c & d \end{pmatrix}$ whose entries $a,b,c,d$ (in that order) form an arithmetic progression. Find all matrices $M$ in $S$ for which there is some integer $k>1$ such that $M^k$ is also in $S$.
-/
theorem putnam_2015_b3
  (M : Matrix (Fin 2) (Fin 2) ℝ)
  (S : Set (Matrix (Fin 2) (Fin 2) ℝ))
  (hS : S = {M' | (M' 0 1 - M' 0 0 = M' 1 0 - M' 0 1) ∧ (M' 1 0 - M' 0 1 = M' 1 1 - M' 1 0)}) :
  (M ∈ S ∧ (∃ k > 1, M ^ k ∈ S)) ↔ M ∈ putnam_2015_b3_solution :=
by
  constructor
  · rintro ⟨hMS, k, hk, hkpow⟩
    have hMAP : putnam_2015_b3_AP M := by
      simpa [hS, putnam_2015_b3_AP] using hMS
    have hpowAP : putnam_2015_b3_AP (M ^ k) := by
      simpa [hS, putnam_2015_b3_AP] using hkpow
    have hM := hMAP
    unfold putnam_2015_b3_AP at hM
    by_cases hdiff : M 0 1 - M 0 0 = 0
    · refine ⟨M 0 0, 0, Or.inl ?_⟩
      have h01 : M 0 1 = M 0 0 := by linarith
      have h10 : M 1 0 = M 0 0 := by linarith [hM.1, h01]
      have h11 : M 1 1 = M 0 0 := by linarith [hM.2, h01, h10]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h01, h10, h11]
    · let q : ℝ := 2 * (M 0 1 - M 0 0) ^ 2
      have hk_eq : k - 1 + 1 = k := by omega
      have hpowAP' : putnam_2015_b3_AP (M ^ (k - 1 + 1)) := by
        simpa [hk_eq] using hpowAP
      have hbeta :
          q * putnam_2015_b3_coeff (M 0 0 + M 1 1) q (k - 1) = 0 := by
        have hiff := putnam_2015_b3_pow_succ_AP_iff M hMAP (k - 1)
        exact hiff.mp (by simpa [q] using hpowAP')
      have hqpos : 0 < q := by
        have hsquare : 0 < (M 0 1 - M 0 0) ^ 2 := sq_pos_of_ne_zero hdiff
        dsimp [q]
        nlinarith
      have hcoeff0 :
          putnam_2015_b3_coeff (M 0 0 + M 1 1) q (k - 1) = 0 :=
        (mul_eq_zero.mp hbeta).resolve_left (ne_of_gt hqpos)
      have htrace : M 0 0 + M 1 1 = 0 := by
        by_contra htrace
        exact (putnam_2015_b3_coeff_ne_zero_of_q_pos hqpos (by omega) htrace) hcoeff0
      refine ⟨0, M 0 1, Or.inr ?_⟩
      have h00 : M 0 0 = 3 * M 0 1 := by linarith [hM.1, hM.2, htrace]
      have h10 : M 1 0 = -M 0 1 := by linarith [hM.1, h00]
      have h11 : M 1 1 = -3 * M 0 1 := by linarith [htrace, h00]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]
  · intro hsol
    rcases hsol with ⟨a, b, hconst_or_trace⟩
    rcases hconst_or_trace with hmat | hmat
    · let N : Matrix (Fin 2) (Fin 2) ℝ := !![a, a; a, a]
      have hMN : M = N := by
        simpa [N] using hmat
      have hN : putnam_2015_b3_AP N := by
        unfold putnam_2015_b3_AP
        dsimp [N]
        constructor <;> ring
      rw [hMN]
      constructor
      · simpa [hS, putnam_2015_b3_AP] using hN
      · refine ⟨2, by norm_num, ?_⟩
        rw [hS]
        have hiff := putnam_2015_b3_pow_succ_AP_iff N hN 1
        have hbeta :
            (2 * (N 0 1 - N 0 0) ^ 2) *
              putnam_2015_b3_coeff (N 0 0 + N 1 1)
                (2 * (N 0 1 - N 0 0) ^ 2) 1 = 0 := by
          dsimp [N]
          simp [putnam_2015_b3_coeff]
        simpa [putnam_2015_b3_AP] using hiff.mpr hbeta
    · let N : Matrix (Fin 2) (Fin 2) ℝ := !![3 * b, b; -b, -3 * b]
      have hMN : M = N := by
        simpa [N] using hmat
      have hN : putnam_2015_b3_AP N := by
        unfold putnam_2015_b3_AP
        dsimp [N]
        constructor <;> ring
      rw [hMN]
      constructor
      · simpa [hS, putnam_2015_b3_AP] using hN
      · refine ⟨3, by norm_num, ?_⟩
        rw [hS]
        have hiff := putnam_2015_b3_pow_succ_AP_iff N hN 2
        have ht : N 0 0 + N 1 1 = 0 := by
          dsimp [N]
          ring
        have hbeta :
            (2 * (N 0 1 - N 0 0) ^ 2) *
              putnam_2015_b3_coeff (N 0 0 + N 1 1)
                (2 * (N 0 1 - N 0 0) ^ 2) 2 = 0 := by
          simp [putnam_2015_b3_coeff, ht]
        simpa [putnam_2015_b3_AP] using hiff.mpr hbeta
