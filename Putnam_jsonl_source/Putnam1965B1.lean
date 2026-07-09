import Mathlib

open EuclideanGeometry Topology Filter Complex
open MeasureTheory

private lemma putnam_1965_b1_reflect_Icc :
    MeasurePreserving (fun x : ℝ => 1 - x)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  have hpre : (fun x : ℝ => 1 - x) ⁻¹' Set.Icc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 1 := by
    ext x
    constructor <;> intro hx <;> constructor <;> linarith [hx.1, hx.2]
  simpa [hpre] using
    ((volume : Measure ℝ).measurePreserving_sub_left (1 : ℝ)).restrict_preimage
      (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) 1))

private lemma putnam_1965_b1_reflect_pi (m : ℕ) :
    MeasurePreserving (fun x : Fin m → ℝ => fun k => 1 - x k)
      (Measure.pi fun _ : Fin m => volume.restrict (Set.Icc (0 : ℝ) 1))
      (Measure.pi fun _ : Fin m => volume.restrict (Set.Icc (0 : ℝ) 1)) :=
  MeasureTheory.measurePreserving_pi
    (fun _ : Fin m => volume.restrict (Set.Icc (0 : ℝ) 1))
    (fun _ : Fin m => volume.restrict (Set.Icc (0 : ℝ) 1))
    (fun _ => putnam_1965_b1_reflect_Icc)

private lemma putnam_1965_b1_cube_eq (m : ℕ) :
    {x : Fin m → ℝ | ∀ k : Fin m, x k ∈ Set.Icc (0 : ℝ) 1} =
      Set.pi Set.univ (fun _ : Fin m => Set.Icc (0 : ℝ) 1) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_const]

private lemma putnam_1965_b1_cube_restrict (m : ℕ) :
    (volume.restrict {x : Fin m → ℝ | ∀ k : Fin m, x k ∈ Set.Icc (0 : ℝ) 1}) =
      Measure.pi (fun _ : Fin m => volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  rw [putnam_1965_b1_cube_eq, volume_pi, Measure.restrict_pi_pi]

-- 1 / 2
/--
Find $$\lim_{n \to \infty} \int_{0}^{1} \int_{0}^{1} \cdots \int_{0}^{1} \cos^2\left(\frac{\pi}{2n}(x_1 + x_2 + \cdots + x_n)\right) dx_1 dx_2 \cdots dx_n.$$
-/
theorem putnam_1965_b1
: Tendsto (fun n : ℕ ↦ ∫ x in {x : Fin (n+1) → ℝ | ∀ k : Fin (n+1), x k ∈ Set.Icc 0 1}, (Real.cos (Real.pi/(2 * (n+1)) * ∑ k : Fin (n+1), x k))^2) atTop (𝓝 ((1 / 2) : ℝ )) := by
  classical
  have hconst :
      (fun n : ℕ ↦
        ∫ x in {x : Fin (n+1) → ℝ | ∀ k : Fin (n+1), x k ∈ Set.Icc 0 1},
          (Real.cos (Real.pi/(2 * (n+1)) * ∑ k : Fin (n+1), x k))^2) =
        fun _ : ℕ => (1 / 2 : ℝ) := by
    funext n
    let μ : Measure (Fin (n + 1) → ℝ) :=
      Measure.pi fun _ : Fin (n + 1) => volume.restrict (Set.Icc (0 : ℝ) 1)
    let u : (Fin (n + 1) → ℝ) → ℝ :=
      fun x => Real.pi / (2 * ((n : ℝ) + 1)) * ∑ k : Fin (n + 1), x k
    have hmpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hmne : (n : ℝ) + 1 ≠ 0 := ne_of_gt hmpos
    change
      (∫ x, (Real.cos (u x)) ^ 2
        ∂(volume.restrict {x : Fin (n + 1) → ℝ |
          ∀ k : Fin (n + 1), x k ∈ Set.Icc (0 : ℝ) 1})) =
        (1 / 2 : ℝ)
    rw [putnam_1965_b1_cube_restrict (n + 1)]
    change (∫ x, (Real.cos (u x)) ^ 2 ∂μ) = (1 / 2 : ℝ)
    have hmp :
        MeasurePreserving (fun x : Fin (n + 1) → ℝ => fun k => 1 - x k) μ μ := by
      simpa [μ] using putnam_1965_b1_reflect_pi (n + 1)
    have hreflect :
        (∫ x, (Real.cos (u x)) ^ 2 ∂μ) =
          ∫ x, (Real.cos (u (fun k => 1 - x k))) ^ 2 ∂μ := by
      calc
        (∫ x, (Real.cos (u x)) ^ 2 ∂μ)
            = ∫ x, (Real.cos (u x)) ^ 2
                ∂Measure.map (fun x : Fin (n + 1) → ℝ => fun k => 1 - x k) μ := by
                rw [hmp.map_eq]
        _ = ∫ x, (Real.cos (u (fun k => 1 - x k))) ^ 2 ∂μ := by
                exact integral_map
                  (f := fun x : Fin (n + 1) → ℝ => (Real.cos (u x)) ^ 2)
                  hmp.aemeasurable (by
                    rw [hmp.map_eq]
                    fun_prop)
    have hureflect :
        ∀ x : Fin (n + 1) → ℝ, u (fun k => 1 - x k) = Real.pi / 2 - u x := by
      intro x
      simp [u, Finset.sum_sub_distrib]
      field_simp [hmne]
    have hcos_sin :
        (∫ x, (Real.cos (u (fun k => 1 - x k))) ^ 2 ∂μ) =
          ∫ x, (Real.sin (u x)) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      simp [hureflect x, Real.cos_pi_div_two_sub]
    have hsame :
        (∫ x, (Real.cos (u x)) ^ 2 ∂μ) =
          ∫ x, (Real.sin (u x)) ^ 2 ∂μ :=
      hreflect.trans hcos_sin
    haveI : IsFiniteMeasure μ := by
      dsimp [μ]
      infer_instance
    have hcos_int : Integrable (fun x => (Real.cos (u x)) ^ 2) μ := by
      refine Integrable.of_bound (by fun_prop) 1 ?_
      filter_upwards with x
      simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.cos (u x)))] using
        Real.cos_sq_le_one (u x)
    have hsin_int : Integrable (fun x => (Real.sin (u x)) ^ 2) μ := by
      refine Integrable.of_bound (by fun_prop) 1 ?_
      filter_upwards with x
      simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.sin (u x)))] using
        Real.sin_sq_le_one (u x)
    have hsum :
        (∫ x, (Real.cos (u x)) ^ 2 ∂μ) +
            (∫ x, (Real.sin (u x)) ^ 2 ∂μ) =
          1 := by
      calc
        (∫ x, (Real.cos (u x)) ^ 2 ∂μ) +
            (∫ x, (Real.sin (u x)) ^ 2 ∂μ)
            = ∫ x, (Real.cos (u x)) ^ 2 + (Real.sin (u x)) ^ 2 ∂μ := by
                exact (integral_add hcos_int hsin_int).symm
        _ = ∫ _ : Fin (n + 1) → ℝ, (1 : ℝ) ∂μ := by
                apply integral_congr_ae
                filter_upwards with x
                rw [Real.cos_sq_add_sin_sq]
        _ = 1 := by
                simp [integral_const, μ, measureReal_def, Measure.pi_univ, Real.volume_Icc]
    nlinarith
  rw [hconst]
  exact tendsto_const_nhds
