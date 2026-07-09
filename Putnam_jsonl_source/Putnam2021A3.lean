import Mathlib

open Filter Topology

open scoped BigOperators

private lemma putnam_2021_a3_inner_eq_of_dist
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {P Q : E} {N s : ℝ}
    (hP : inner ℝ P P = N) (hQ : inner ℝ Q Q = N) (hd : dist P Q = s) :
    inner ℝ P Q = N - s ^ 2 / 2 := by
  have hdistnorm : ‖P - Q‖ ^ 2 = s ^ 2 := by
    rw [← dist_eq_norm, hd]
  rw [← real_inner_self_eq_norm_sq (P - Q)] at hdistnorm
  simp only [inner_sub_left, inner_sub_right] at hdistnorm
  have hcomm : inner ℝ Q P = inner ℝ P Q := by rw [real_inner_comm]
  nlinarith

private lemma putnam_2021_a3_edge_inner_half
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u v : E} {s : ℝ}
    (huu : inner ℝ u u = s ^ 2) (hvv : inner ℝ v v = s ^ 2)
    (huv_dist : dist u v = s) :
    inner ℝ u v = s ^ 2 / 2 := by
  have h := putnam_2021_a3_inner_eq_of_dist (N := s ^ 2) huu hvv huv_dist
  nlinarith

private lemma putnam_2021_a3_edges_linearIndependent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u v w : E} {s : ℝ} (hs : 0 < s)
    (huu : inner ℝ u u = s ^ 2) (hvv : inner ℝ v v = s ^ 2)
    (hww : inner ℝ w w = s ^ 2)
    (huv : inner ℝ u v = s ^ 2 / 2) (huw : inner ℝ u w = s ^ 2 / 2)
    (hvw : inner ℝ v w = s ^ 2 / 2) :
    LinearIndependent ℝ ![u, v, w] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h0 := congrArg (fun x => inner ℝ x u) hg
  have h1 := congrArg (fun x => inner ℝ x v) hg
  have h2 := congrArg (fun x => inner ℝ x w) hg
  have hnu : ‖u‖ ^ 2 = s ^ 2 := by rw [← real_inner_self_eq_norm_sq, huu]
  have hnv : ‖v‖ ^ 2 = s ^ 2 := by rw [← real_inner_self_eq_norm_sq, hvv]
  have hnw : ‖w‖ ^ 2 = s ^ 2 := by rw [← real_inner_self_eq_norm_sq, hww]
  have hsym_uv : inner ℝ v u = s ^ 2 / 2 := by simpa [real_inner_comm] using huv
  have hsym_uw : inner ℝ w u = s ^ 2 / 2 := by simpa [real_inner_comm] using huw
  have hsym_vw : inner ℝ w v = s ^ 2 / 2 := by simpa [real_inner_comm] using hvw
  simp [Fin.sum_univ_three, inner_add_left, real_inner_smul_left, hnu, hnv, hnw,
    huv, huw, hvw, hsym_uv, hsym_uw, hsym_vw] at h0 h1 h2
  field_simp [pow_ne_zero 2 hs.ne'] at h0 h1 h2
  norm_num at h0 h1 h2
  have h0' : g 0 * 2 + g 1 + g 2 = 0 := h0.resolve_left hs.ne'
  have h1' : g 0 + g 1 * 2 + g 2 = 0 := h1.resolve_left hs.ne'
  have h2' : g 0 + g 1 + 2 * g 2 = 0 := h2.resolve_left hs.ne'
  fin_cases i <;> simp <;> nlinarith

private lemma putnam_2021_a3_orthogonal_to_edges_eq_zero
    {u v w S : EuclideanSpace ℝ (Fin 3)}
    (hli : LinearIndependent ℝ ![u, v, w])
    (hSu : inner ℝ S u = 0) (hSv : inner ℝ S v = 0) (hSw : inner ℝ S w = 0) :
    S = 0 := by
  have hspan : Submodule.span ℝ (Set.range ![u, v, w]) =
      (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) := by
    exact hli.span_eq_top_of_card_eq_finrank (by simp)
  have hSorth : S ∈ (Submodule.span ℝ (Set.range ![u, v, w]))ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro x hx
    refine Submodule.span_induction ?mem ?zero ?add ?smul hx
    · intro y hy
      rcases hy with ⟨i, rfl⟩
      fin_cases i
      · simpa using hSu
      · simpa using hSv
      · simpa using hSw
    · simp
    · intro x y hx hy hx0 hy0
      simpa [inner_add_right, hx0, hy0]
    · intro a x hx hx0
      simpa [real_inner_smul_right, hx0]
  have hStop : S ∈ (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))ᗮ := by
    rw [← hspan]
    exact hSorth
  rw [Submodule.top_orthogonal_eq_bot] at hStop
  simpa using hStop

set_option maxHeartbeats 3000000 in
private lemma putnam_2021_a3_pair_inner_neg_third
    {A B C D : EuclideanSpace ℝ (Fin 3)} {N s : ℝ} (hs : 0 < s)
    (hAA : inner ℝ A A = N) (hBB : inner ℝ B B = N)
    (hCC : inner ℝ C C = N) (hDD : inner ℝ D D = N)
    (hdAB : dist A B = s) (hdAC : dist A C = s) (hdAD : dist A D = s)
    (hdBC : dist B C = s) (hdBD : dist B D = s) (hdCD : dist C D = s) :
    inner ℝ A B = -N / 3 ∧ inner ℝ A C = -N / 3 ∧ inner ℝ B C = -N / 3 := by
  set t : ℝ := N - s ^ 2 / 2 with ht
  have hAn : ‖A‖ ^ 2 = N := by rw [← real_inner_self_eq_norm_sq, hAA]
  have hBn : ‖B‖ ^ 2 = N := by rw [← real_inner_self_eq_norm_sq, hBB]
  have hCn : ‖C‖ ^ 2 = N := by rw [← real_inner_self_eq_norm_sq, hCC]
  have hDn : ‖D‖ ^ 2 = N := by rw [← real_inner_self_eq_norm_sq, hDD]
  have hAB : inner ℝ A B = t := by
    simpa [t] using putnam_2021_a3_inner_eq_of_dist hAA hBB hdAB
  have hAC : inner ℝ A C = t := by
    simpa [t] using putnam_2021_a3_inner_eq_of_dist hAA hCC hdAC
  have hAD : inner ℝ A D = t := by
    simpa [t] using putnam_2021_a3_inner_eq_of_dist hAA hDD hdAD
  have hBC : inner ℝ B C = t := by
    simpa [t] using putnam_2021_a3_inner_eq_of_dist hBB hCC hdBC
  have hBD : inner ℝ B D = t := by
    simpa [t] using putnam_2021_a3_inner_eq_of_dist hBB hDD hdBD
  have hCD : inner ℝ C D = t := by
    simpa [t] using putnam_2021_a3_inner_eq_of_dist hCC hDD hdCD
  have hBA : inner ℝ B A = t := by simpa [real_inner_comm] using hAB
  have hCA : inner ℝ C A = t := by simpa [real_inner_comm] using hAC
  have hDA : inner ℝ D A = t := by simpa [real_inner_comm] using hAD
  have hCB : inner ℝ C B = t := by simpa [real_inner_comm] using hBC
  have hDB : inner ℝ D B = t := by simpa [real_inner_comm] using hBD
  have hDC : inner ℝ D C = t := by simpa [real_inner_comm] using hCD
  let u : EuclideanSpace ℝ (Fin 3) := B - A
  let v : EuclideanSpace ℝ (Fin 3) := C - A
  let w : EuclideanSpace ℝ (Fin 3) := D - A
  have huu : inner ℝ u u = s ^ 2 := by
    change inner ℝ (B - A) (B - A) = s ^ 2
    rw [real_inner_self_eq_norm_sq]
    rw [← dist_eq_norm, dist_comm, hdAB]
  have hvv : inner ℝ v v = s ^ 2 := by
    change inner ℝ (C - A) (C - A) = s ^ 2
    rw [real_inner_self_eq_norm_sq]
    rw [← dist_eq_norm, dist_comm, hdAC]
  have hww : inner ℝ w w = s ^ 2 := by
    change inner ℝ (D - A) (D - A) = s ^ 2
    rw [real_inner_self_eq_norm_sq]
    rw [← dist_eq_norm, dist_comm, hdAD]
  have hdistuv : dist u v = s := by
    change dist (B - A) (C - A) = s
    rw [← hdBC]
    simp [dist_eq_norm]
  have hdistuw : dist u w = s := by
    change dist (B - A) (D - A) = s
    rw [← hdBD]
    simp [dist_eq_norm]
  have hdistvw : dist v w = s := by
    change dist (C - A) (D - A) = s
    rw [← hdCD]
    simp [dist_eq_norm]
  have huv : inner ℝ u v = s ^ 2 / 2 := putnam_2021_a3_edge_inner_half huu hvv hdistuv
  have huw : inner ℝ u w = s ^ 2 / 2 := putnam_2021_a3_edge_inner_half huu hww hdistuw
  have hvw : inner ℝ v w = s ^ 2 / 2 := putnam_2021_a3_edge_inner_half hvv hww hdistvw
  have hli : LinearIndependent ℝ ![u, v, w] :=
    putnam_2021_a3_edges_linearIndependent hs huu hvv hww huv huw hvw
  let S : EuclideanSpace ℝ (Fin 3) := A + B + C + D
  have hSu : inner ℝ S u = 0 := by
    change inner ℝ (A + B + C + D) (B - A) = 0
    simp [inner_add_left, inner_sub_right, hAB, hBn, hCB, hDB, hAn, hBA, hCA, hDA]
    ring
  have hSv : inner ℝ S v = 0 := by
    change inner ℝ (A + B + C + D) (C - A) = 0
    simp [inner_add_left, inner_sub_right, hAC, hBC, hCn, hDC, hAn, hBA, hCA, hDA]
    ring
  have hSw : inner ℝ S w = 0 := by
    change inner ℝ (A + B + C + D) (D - A) = 0
    simp [inner_add_left, inner_sub_right, hAD, hBD, hCD, hDn, hAn, hBA, hCA, hDA]
    ring
  have hSzero : S = 0 := putnam_2021_a3_orthogonal_to_edges_eq_zero hli hSu hSv hSw
  have hAeq : inner ℝ A S = 0 := by rw [hSzero, inner_zero_right]
  have htneg : t = -N / 3 := by
    change inner ℝ A (A + B + C + D) = 0 at hAeq
    simp [inner_add_right, hAn, hAB, hAC, hAD] at hAeq
    nlinarith
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

private lemma putnam_2021_a3_dot_eq_inner (P Q : EuclideanSpace ℝ (Fin 3)) :
    ((fun i : Fin 3 => P i) ⬝ᵥ (fun i : Fin 3 => Q i)) = inner ℝ P Q := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct_comm]

private lemma putnam_2021_a3_inner_self_of_mem_sphere
    {N : ℕ} {Nsphere : Set (EuclideanSpace ℝ (Fin 3))}
    (hNsphere : Nsphere = {p | (p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 = (N : ℝ)})
    {P : EuclideanSpace ℝ (Fin 3)} (hP : P ∈ Nsphere) :
    inner ℝ P P = (N : ℝ) := by
  have hPeq : (P 0) ^ 2 + (P 1) ^ 2 + (P 2) ^ 2 = (N : ℝ) := by
    simpa [hNsphere] using hP
  rw [real_inner_self_eq_norm_sq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simpa [Real.norm_eq_abs, sq_abs] using hPeq

private lemma putnam_2021_a3_det_sq_gram (a b c : Fin 3 → ℝ) :
    (Matrix.det ![a, b, c]) ^ 2 =
      (a ⬝ᵥ a) * (b ⬝ᵥ b) * (c ⬝ᵥ c)
        + 2 * (a ⬝ᵥ b) * (a ⬝ᵥ c) * (b ⬝ᵥ c)
        - (a ⬝ᵥ a) * (b ⬝ᵥ c) ^ 2
        - (b ⬝ᵥ b) * (a ⬝ᵥ c) ^ 2
        - (c ⬝ᵥ c) * (a ⬝ᵥ b) ^ 2 := by
  rw [Matrix.det_fin_three]
  simp [Matrix.vec3_dotProduct]
  ring

private lemma putnam_2021_a3_number_theory
    {N D : ℕ} (hN : 0 < N) (h : 27 * D ^ 2 = 16 * N ^ 3) :
    N ∈ (({3 * m ^ 2 | m > 0}) : Set ℕ) := by
  have h3rhs : 3 ∣ 16 * N ^ 3 := by
    rw [← h]
    exact dvd_mul_of_dvd_left (by norm_num : 3 ∣ 27) _
  have h3Npow : 3 ∣ N ^ 3 := by
    rcases (Nat.prime_three.dvd_mul.mp h3rhs) with hdiv | hdiv
    · norm_num at hdiv
    · exact hdiv
  have h3N : 3 ∣ N := Nat.prime_three.dvd_of_dvd_pow h3Npow
  rcases h3N with ⟨q, rfl⟩
  have hqpos : 0 < q := by nlinarith
  have hDsq : D ^ 2 = 16 * q ^ 3 := by
    norm_num [pow_succ, mul_assoc] at h ⊢
    nlinarith
  have hq2dvd : q ^ 2 ∣ D ^ 2 := by
    rw [hDsq]
    refine ⟨16 * q, by ring⟩
  have hqD : q ∣ D := (Nat.pow_dvd_pow_iff (by norm_num : 2 ≠ 0)).mp hq2dvd
  rcases hqD with ⟨r, rfl⟩
  have hr_sq : r ^ 2 = 16 * q := by
    have hcancel : q ^ 2 * r ^ 2 = q ^ 2 * (16 * q) := by
      nlinarith [hDsq]
    exact Nat.mul_left_cancel (Nat.pow_pos hqpos : 0 < q ^ 2) hcancel
  have h4dvd : 4 ^ 2 ∣ r ^ 2 := by
    rw [hr_sq]
    refine ⟨q, by norm_num [pow_two, mul_assoc]⟩
  have h4r : 4 ∣ r := (Nat.pow_dvd_pow_iff (by norm_num : 2 ≠ 0)).mp h4dvd
  rcases h4r with ⟨m, rfl⟩
  have hq : q = m ^ 2 := by
    have hcancel : 16 * m ^ 2 = 16 * q := by
      nlinarith [hr_sq]
    exact (Nat.mul_left_cancel (by norm_num : 0 < 16) hcancel).symm
  subst q
  refine ⟨m, ?_, rfl⟩
  nlinarith

private lemma putnam_2021_a3_constructed_dist (m : ℕ)
    (P Q : EuclideanSpace ℝ (Fin 3)) :
    P = WithLp.toLp 2 ![(m : ℝ), (m : ℝ), (m : ℝ)] ∧
      Q = WithLp.toLp 2 ![(m : ℝ), -(m : ℝ), -(m : ℝ)] →
    dist P Q = Real.sqrt 8 * (m : ℝ) := by
  rintro ⟨rfl, rfl⟩
  apply (sq_eq_sq₀ dist_nonneg
    (mul_nonneg (Real.sqrt_nonneg 8) (Nat.cast_nonneg _))).1
  rw [EuclideanSpace.dist_sq_eq]
  simp [Fin.sum_univ_three, Real.dist_eq]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]

-- {3 * m ^ 2 | m > 0}
/--
Determine all positive integers $N$ for which the sphere $x^2+y^2+z^2=N$ has an inscribed regular tetrahedron whose vertices have integer coordinates.
-/
theorem putnam_2021_a3
  (N : ℕ)
  (Nsphere : Set (EuclideanSpace ℝ (Fin 3)))
  (hNsphere : Nsphere = {p | (p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 = (N : ℝ)})
  (intcoords : (EuclideanSpace ℝ (Fin 3)) → Prop)
  (intcoords_def : ∀ p, intcoords p ↔ ∀ i : Fin 3, p i = round (p i)) :
  (0 < N ∧ ∃ A B C D : EuclideanSpace ℝ (Fin 3),
    A ∈ Nsphere ∧ B ∈ Nsphere ∧ C ∈ Nsphere ∧ D ∈ Nsphere ∧
    intcoords A ∧ intcoords B ∧ intcoords C ∧ intcoords D ∧
    (∃ s > 0, dist A B = s ∧ dist A C = s ∧ dist A D = s ∧ dist B C = s ∧ dist B D = s ∧ dist C D = s))
  ↔ N ∈ (({3 * m ^ 2 | m > 0}) : Set ℕ ) := by
  constructor
  · intro h
    rcases h with
      ⟨hNpos, A, B, C, D, hA, hB, hC, hD, hAi, hBi, hCi, hDi, s, hspos,
        hdAB, hdAC, hdAD, hdBC, hdBD, hdCD⟩
    have hAA := putnam_2021_a3_inner_self_of_mem_sphere hNsphere hA
    have hBB := putnam_2021_a3_inner_self_of_mem_sphere hNsphere hB
    have hCC := putnam_2021_a3_inner_self_of_mem_sphere hNsphere hC
    have hDD := putnam_2021_a3_inner_self_of_mem_sphere hNsphere hD
    obtain ⟨hABi, hACi, hBCi⟩ :=
      putnam_2021_a3_pair_inner_neg_third hspos hAA hBB hCC hDD
        hdAB hdAC hdAD hdBC hdBD hdCD
    let aR : Fin 3 → ℝ := fun i => A i
    let bR : Fin 3 → ℝ := fun i => B i
    let cR : Fin 3 → ℝ := fun i => C i
    have hdotAA : aR ⬝ᵥ aR = (N : ℝ) := by
      simpa [aR] using (putnam_2021_a3_dot_eq_inner A A).trans hAA
    have hdotBB : bR ⬝ᵥ bR = (N : ℝ) := by
      simpa [bR] using (putnam_2021_a3_dot_eq_inner B B).trans hBB
    have hdotCC : cR ⬝ᵥ cR = (N : ℝ) := by
      simpa [cR] using (putnam_2021_a3_dot_eq_inner C C).trans hCC
    have hdotAB : aR ⬝ᵥ bR = -(N : ℝ) / 3 := by
      simpa [aR, bR] using (putnam_2021_a3_dot_eq_inner A B).trans hABi
    have hdotAC : aR ⬝ᵥ cR = -(N : ℝ) / 3 := by
      simpa [aR, cR] using (putnam_2021_a3_dot_eq_inner A C).trans hACi
    have hdotBC : bR ⬝ᵥ cR = -(N : ℝ) / 3 := by
      simpa [bR, cR] using (putnam_2021_a3_dot_eq_inner B C).trans hBCi
    have hdet_real :
        (Matrix.det ![aR, bR, cR]) ^ 2 = 16 * (N : ℝ) ^ 3 / 27 := by
      rw [putnam_2021_a3_det_sq_gram, hdotAA, hdotBB, hdotCC, hdotAB, hdotAC, hdotBC]
      ring
    let aZ : Fin 3 → ℤ := fun i => round (A i)
    let bZ : Fin 3 → ℤ := fun i => round (B i)
    let cZ : Fin 3 → ℤ := fun i => round (C i)
    have hAcoord : ∀ i : Fin 3, A i = (aZ i : ℝ) := (intcoords_def A).mp hAi
    have hBcoord : ∀ i : Fin 3, B i = (bZ i : ℝ) := (intcoords_def B).mp hBi
    have hCcoord : ∀ i : Fin 3, C i = (cZ i : ℝ) := (intcoords_def C).mp hCi
    let z : ℤ := Matrix.det (![aZ, bZ, cZ] : Matrix (Fin 3) (Fin 3) ℤ)
    have hdet_cast : Matrix.det (![aR, bR, cR] : Matrix (Fin 3) (Fin 3) ℝ) = (z : ℝ) := by
      change
        Matrix.det (![fun i : Fin 3 => A i, fun i : Fin 3 => B i, fun i : Fin 3 => C i] :
          Matrix (Fin 3) (Fin 3) ℝ) =
        ((Matrix.det (![aZ, bZ, cZ] : Matrix (Fin 3) (Fin 3) ℤ) : ℤ) : ℝ)
      rw [Matrix.det_fin_three, Matrix.det_fin_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons]
      rw [hAcoord 0, hAcoord 1, hAcoord 2, hBcoord 0, hBcoord 1, hBcoord 2,
        hCcoord 0, hCcoord 1, hCcoord 2]
      norm_num
    have hzreal : ((z.natAbs : ℕ) : ℝ) ^ 2 = 16 * (N : ℝ) ^ 3 / 27 := by
      calc
        ((z.natAbs : ℕ) : ℝ) ^ 2 = (z : ℝ) ^ 2 := by
          calc
            ((z.natAbs : ℕ) : ℝ) ^ 2 = ((z.natAbs : ℤ) : ℝ) ^ 2 := by norm_num
            _ = (z : ℝ) ^ 2 := by exact_mod_cast (Int.natAbs_sq z)
        _ = 16 * (N : ℝ) ^ 3 / 27 := by
          rw [← hdet_cast]
          exact hdet_real
    have hnat : 27 * z.natAbs ^ 2 = 16 * N ^ 3 := by
      have h' : (27 * ((z.natAbs : ℕ) : ℝ) ^ 2) = 16 * (N : ℝ) ^ 3 := by
        nlinarith
      exact_mod_cast h'
    exact putnam_2021_a3_number_theory hNpos hnat
  · intro h
    rcases h with ⟨m, hmpos, hN⟩
    let A : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![(m : ℝ), (m : ℝ), (m : ℝ)]
    let B : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![(m : ℝ), -(m : ℝ), -(m : ℝ)]
    let C : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![-(m : ℝ), (m : ℝ), -(m : ℝ)]
    let D : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![-(m : ℝ), -(m : ℝ), (m : ℝ)]
    have hround_pos : (m : ℝ) = round (m : ℝ) := by norm_num
    have hround_neg : -(m : ℝ) = round (-(m : ℝ)) := by
      rw [← Int.cast_natCast (R := ℝ) m, ← Int.cast_neg, round_intCast]
    have hmem (P : EuclideanSpace ℝ (Fin 3))
        (hP : P = A ∨ P = B ∨ P = C ∨ P = D) : P ∈ Nsphere := by
      rcases hP with rfl | rfl | rfl | rfl
      all_goals
        simp [A, B, C, D, hNsphere]
        rw [← hN]
        norm_num
        ring
    have hint (P : EuclideanSpace ℝ (Fin 3))
        (hP : P = A ∨ P = B ∨ P = C ∨ P = D) : intcoords P := by
      apply (intcoords_def P).2
      rcases hP with rfl | rfl | rfl | rfl
      · intro i
        fin_cases i <;> simpa [A] using hround_pos
      · intro i
        fin_cases i
        · simpa [B] using hround_pos
        · simpa [B] using hround_neg
        · simpa [B] using hround_neg
      · intro i
        fin_cases i
        · simpa [C] using hround_neg
        · simpa [C] using hround_pos
        · simpa [C] using hround_neg
      · intro i
        fin_cases i
        · simpa [D] using hround_neg
        · simpa [D] using hround_neg
        · simpa [D] using hround_pos
    have hdistAB : dist A B = Real.sqrt 8 * (m : ℝ) :=
      putnam_2021_a3_constructed_dist m A B ⟨rfl, rfl⟩
    have hdistAC : dist A C = Real.sqrt 8 * (m : ℝ) := by
      apply (sq_eq_sq₀ dist_nonneg
        (mul_nonneg (Real.sqrt_nonneg 8) (Nat.cast_nonneg _))).1
      rw [EuclideanSpace.dist_sq_eq]
      simp [A, C, Fin.sum_univ_three, Real.dist_eq]
      ring_nf
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
    have hdistAD : dist A D = Real.sqrt 8 * (m : ℝ) := by
      apply (sq_eq_sq₀ dist_nonneg
        (mul_nonneg (Real.sqrt_nonneg 8) (Nat.cast_nonneg _))).1
      rw [EuclideanSpace.dist_sq_eq]
      simp [A, D, Fin.sum_univ_three, Real.dist_eq]
      ring_nf
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
    have hdistBC : dist B C = Real.sqrt 8 * (m : ℝ) := by
      apply (sq_eq_sq₀ dist_nonneg
        (mul_nonneg (Real.sqrt_nonneg 8) (Nat.cast_nonneg _))).1
      rw [EuclideanSpace.dist_sq_eq]
      simp [B, C, Fin.sum_univ_three, Real.dist_eq]
      ring_nf
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
    have hdistBD : dist B D = Real.sqrt 8 * (m : ℝ) := by
      apply (sq_eq_sq₀ dist_nonneg
        (mul_nonneg (Real.sqrt_nonneg 8) (Nat.cast_nonneg _))).1
      rw [EuclideanSpace.dist_sq_eq]
      simp [B, D, Fin.sum_univ_three, Real.dist_eq]
      ring_nf
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
    have hdistCD : dist C D = Real.sqrt 8 * (m : ℝ) := by
      apply (sq_eq_sq₀ dist_nonneg
        (mul_nonneg (Real.sqrt_nonneg 8) (Nat.cast_nonneg _))).1
      rw [EuclideanSpace.dist_sq_eq]
      simp [C, D, Fin.sum_univ_three, Real.dist_eq]
      ring_nf
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
    constructor
    · rw [← hN]
      positivity
    · refine ⟨A, B, C, D, hmem A (Or.inl rfl), hmem B (Or.inr (Or.inl rfl)),
        hmem C (Or.inr (Or.inr (Or.inl rfl))), hmem D (Or.inr (Or.inr (Or.inr rfl))),
        hint A (Or.inl rfl), hint B (Or.inr (Or.inl rfl)),
        hint C (Or.inr (Or.inr (Or.inl rfl))), hint D (Or.inr (Or.inr (Or.inr rfl))), ?_⟩
      refine ⟨Real.sqrt 8 * (m : ℝ), ?_, hdistAB, hdistAC, hdistAD, hdistBC, hdistBD, hdistCD⟩
      positivity
