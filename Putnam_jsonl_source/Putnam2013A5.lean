import Mathlib

open Function Set MeasureTheory

-- Note: uses (Fin m → Fin m → Fin m → ℝ) instead of ensuring inputs are strictly increasing
/--
For $m \geq 3$, a list of $\binom{m}{3}$ real numbers $a_{ijk}$ ($1 \leq i< j< k \leq m$) is said to be \emph{area definite} for $\mathbb{R}^n$ if the inequality $\sum_{1 \leq i< j< k \leq m} a_{ijk} \cdot \text{Area}(\Delta A_iA_jA_k) \geq 0$ holds for every choice of $m$ points $A_1,\dots,A_m$ in $\mathbb{R}^n$. For example, the list of four numbers $a_{123}=a_{124}=a_{134}=1$, $a_{234}=-1$ is area definite for $\mathbb{R}^2$. Prove that if a list of $\binom{m}{3}$ numbers is area definite for $\mathbb{R}^2$, then it is area definite for $\mathbb{R}^3$.
-/
theorem putnam_2013_a5
(m : ℕ)
(area2 : (Fin 2 → ℝ) → (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℝ)
(area3 : (Fin 3 → ℝ) → (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ)
(areadef2 : (Fin m → Fin m → Fin m → ℝ) → Prop)
(areadef3 : (Fin m → Fin m → Fin m → ℝ) → Prop)
(mge3 : m ≥ 3)
(harea2 : ∀ a b c, area2 a b c = (volume (convexHull ℝ {a, b, c})).toReal)
(harea3 : ∀ a b c, area3 a b c = (μH[2] (convexHull ℝ {a, b, c})).toReal)
(hareadef2 : ∀ a, areadef2 a ↔ ∀ A : Fin m → (Fin 2 → ℝ), (∑ i : Fin m, ∑ j : Fin m, ∑ k : Fin m, if (i < j ∧ j < k) then (a i j k * area2 (A i) (A j) (A k)) else 0) ≥ 0)
(hareadef3 : ∀ a, areadef3 a ↔ ∀ A : Fin m → (Fin 3 → ℝ), (∑ i : Fin m, ∑ j : Fin m, ∑ k : Fin m, if (i < j ∧ j < k) then (a i j k * area3 (A i) (A j) (A k)) else 0) ≥ 0)
: ∀ a, areadef2 a → areadef3 a := by
  classical
  intro a ha
  refine (hareadef3 a).2 ?_
  intro A
  have h2 : ∀ B : Fin m → (Fin 2 → ℝ),
      0 ≤ (∑ i : Fin m, ∑ j : Fin m, ∑ k : Fin m,
        if (i < j ∧ j < k) then
          (a i j k * area2 (B i) (B j) (B k))
        else 0) := by
    intro B
    exact (hareadef2 a).1 ha B
  -- Geometric bridge still missing: for this finite configuration, each spatial triangle-area
  -- vector on increasing triples should be a nonnegative finite combination of planar
  -- triangle-area vectors.
  have hgeom : ∃ (ι : Type) (_ : Fintype ι), ∃ (w : ι → ℝ),
      (∀ t, 0 ≤ w t) ∧ ∃ (B : ι → Fin m → (Fin 2 → ℝ)),
      ∀ i j k, i < j ∧ j < k →
        area3 (A i) (A j) (A k) =
        ∑ t : ι, w t * area2 (B t i) (B t j) (B t k) := by
    sorry
  rcases hgeom with ⟨ι, hι, w, hw, B, hB⟩
  letI : Fintype ι := hι
  let F : Fin m → Fin m → Fin m → ι → ℝ := fun i j k t =>
    if (i < j ∧ j < k) then
      a i j k * (w t * area2 (B t i) (B t j) (B t k))
    else 0
  have hleft :
      (∑ i : Fin m, ∑ j : Fin m, ∑ k : Fin m,
          if (i < j ∧ j < k) then
            (a i j k * area3 (A i) (A j) (A k))
          else 0)
        = ∑ i : Fin m, ∑ j : Fin m, ∑ k : Fin m, ∑ t : ι, F i j k t := by
    apply Finset.sum_congr rfl; intro i _hi
    apply Finset.sum_congr rfl; intro j _hj
    apply Finset.sum_congr rfl; intro k _hk
    by_cases hijk : i < j ∧ j < k
    · rw [hB i j k hijk]
      simp [F, hijk, Finset.mul_sum]
    · simp [F, hijk]
  have hreorder :
      (∑ i : Fin m, ∑ j : Fin m, ∑ k : Fin m, ∑ t : ι, F i j k t)
        = ∑ t : ι, ∑ i : Fin m, ∑ j : Fin m, ∑ k : Fin m, F i j k t := by
    rw [← Fintype.sum_prod_type' (f := fun (i : Fin m) (j : Fin m) =>
      ∑ k : Fin m, ∑ t : ι, F i j k t)]
    rw [← Fintype.sum_prod_type' (f := fun (ij : Fin m × Fin m) (k : Fin m) =>
      ∑ t : ι, F ij.1 ij.2 k t)]
    rw [← Fintype.sum_prod_type' (f := fun (ijk : (Fin m × Fin m) × Fin m) (t : ι) =>
      F ijk.1.1 ijk.1.2 ijk.2 t)]
    rw [← Fintype.sum_prod_type' (f := fun (t : ι) (i : Fin m) =>
      ∑ j : Fin m, ∑ k : Fin m, F i j k t)]
    rw [← Fintype.sum_prod_type' (f := fun (ti : ι × Fin m) (j : Fin m) =>
      ∑ k : Fin m, F ti.2 j k ti.1)]
    rw [← Fintype.sum_prod_type' (f := fun (tij : (ι × Fin m) × Fin m) (k : Fin m) =>
      F tij.1.2 tij.2 k tij.1.1)]
    let e : (((Fin m × Fin m) × Fin m) × ι) ≃ (((ι × Fin m) × Fin m) × Fin m) :=
      { toFun := fun x => (((x.2, x.1.1.1), x.1.1.2), x.1.2)
        invFun := fun y => (((y.1.1.2, y.1.2), y.2), y.1.1.1)
        left_inv := by rintro ⟨⟨⟨i, j⟩, k⟩, t⟩; rfl
        right_inv := by rintro ⟨⟨⟨t, i⟩, j⟩, k⟩; rfl }
    refine Fintype.sum_equiv e _ _ ?_
    intro x
    rfl
  have hright :
      (∑ t : ι, ∑ i : Fin m, ∑ j : Fin m, ∑ k : Fin m, F i j k t)
        = ∑ t : ι, w t * (∑ i : Fin m, ∑ j : Fin m, ∑ k : Fin m,
            if (i < j ∧ j < k) then
              (a i j k * area2 (B t i) (B t j) (B t k))
            else 0) := by
    apply Finset.sum_congr rfl; intro t _ht
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _hj
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _hk
    by_cases hijk : i < j ∧ j < k
    · simp [F, hijk]
      ring
    · simp [F, hijk]
  rw [hleft, hreorder, hright]
  exact Finset.sum_nonneg fun t _ht => mul_nonneg (hw t) (h2 (B t))
