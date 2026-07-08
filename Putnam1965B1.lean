import Mathlib

open EuclideanGeometry Topology Filter Complex
open MeasureTheory

private lemma putnam_1965_b1_integral_eq (n : ℕ) :
    (∫ x in {x : Fin (n+1) → ℝ | ∀ k : Fin (n+1), x k ∈ Set.Icc 0 1},
      (Real.cos (Real.pi/(2 * (n+1)) * ∑ k : Fin (n+1), x k))^2) = (1 / 2 : ℝ) := by
  let m : ℕ := n + 1
  let C : Set (Fin m → ℝ) := {x : Fin m → ℝ | ∀ k : Fin m, x k ∈ Set.Icc 0 1}
  let θ : (Fin m → ℝ) → ℝ := fun x => Real.pi / (2 * (m : ℝ)) * ∑ k : Fin m, x k
  let I : ℝ := ∫ x in C, (Real.cos (θ x)) ^ 2
  let J : ℝ := ∫ x in C, (Real.sin (θ x)) ^ 2
  have hm : m ≠ 0 := by omega
  have hC_eq : C = Set.Icc 0 1 := by
    ext x
    simp [C, Set.mem_Icc, Pi.le_def, forall_and]
  have hC_meas : MeasurableSet C := by
    rw [hC_eq]
    exact measurableSet_Icc
  have hC_compact : IsCompact C := by
    rw [hC_eq]
    exact isCompact_Icc
  have hvol : (volume : Measure (Fin m → ℝ)).real C = 1 := by
    rw [hC_eq]
    rw [Measure.real, Real.volume_Icc_pi]
    simp
  have hcos_int : IntegrableOn (fun x : Fin m → ℝ => (Real.cos (θ x)) ^ 2) C volume := by
    exact ContinuousOn.integrableOn_compact hC_compact (by fun_prop)
  have hsin_int : IntegrableOn (fun x : Fin m → ℝ => (Real.sin (θ x)) ^ 2) C volume := by
    exact ContinuousOn.integrableOn_compact hC_compact (by fun_prop)
  have hpre :
      (fun x : Fin m → ℝ => (1 : Fin m → ℝ) - x) ⁻¹' C = C := by
    ext x
    simp only [C, Set.mem_preimage, Set.mem_setOf_eq, Pi.sub_apply, Pi.one_apply, Set.mem_Icc]
    constructor
    · intro h k
      have hk := h k
      constructor <;> linarith
    · intro h k
      have hk := h k
      constructor <;> linarith
  have hreflect_point : ∀ x : Fin m → ℝ,
      (Real.cos (θ ((1 : Fin m → ℝ) - x))) ^ 2 = (Real.sin (θ x)) ^ 2 := by
    intro x
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have hangle : θ ((1 : Fin m → ℝ) - x) = Real.pi / 2 - θ x := by
      have hsum :
          ∑ k : Fin m, (((1 : Fin m → ℝ) - x) k) = (m : ℝ) - ∑ k : Fin m, x k := by
        simp [Finset.sum_sub_distrib]
      simp only [θ]
      rw [hsum]
      field_simp [hmR]
    rw [hangle, Real.cos_pi_div_two_sub]
  have hchange :
      ∫ x in C, (Real.cos (θ ((1 : Fin m → ℝ) - x))) ^ 2 = I := by
    have hmp : MeasurePreserving (fun x : Fin m → ℝ => (1 : Fin m → ℝ) - x) volume volume :=
      Measure.measurePreserving_sub_left (volume : Measure (Fin m → ℝ)) (1 : Fin m → ℝ)
    have h :=
      hmp.setIntegral_preimage_emb
        (MeasurableEquiv.subLeft (1 : Fin m → ℝ)).measurableEmbedding
        (fun y : Fin m → ℝ => (Real.cos (θ y)) ^ 2) C
    simpa [I, hpre] using h
  have hJI : J = I := by
    calc
      J = ∫ x in C, (Real.cos (θ ((1 : Fin m → ℝ) - x))) ^ 2 := by
        simpa [J] using (setIntegral_congr_fun hC_meas fun x _ => (hreflect_point x).symm)
      _ = I := hchange
  have hsum_int : J + I = 1 := by
    calc
      J + I = ∫ x in C, ((Real.sin (θ x)) ^ 2 + (Real.cos (θ x)) ^ 2) := by
        rw [integral_add hsin_int.integrable hcos_int.integrable]
      _ = ∫ x in C, (1 : ℝ) := by
        exact setIntegral_congr_fun hC_meas fun x _ => by
          rw [Real.sin_sq_add_cos_sq]
      _ = 1 := by
        simp [hvol]
  have htwo : 2 * I = 1 := by
    calc
      2 * I = I + I := by ring
      _ = J + I := by rw [hJI]
      _ = 1 := hsum_int
  have hI : I = 1 / 2 := by linarith
  simpa [I, C, θ, m] using hI

noncomputable abbrev putnam_1965_b1_solution : ℝ := 1 / 2

/--
Find $$\lim_{n \to \infty} \int_{0}^{1} \int_{0}^{1} \cdots \int_{0}^{1} \cos^2\left(\frac{\pi}{2n}(x_1 + x_2 + \cdots + x_n)\right) dx_1 dx_2 \cdots dx_n.$$
-/
theorem putnam_1965_b1
: Tendsto (fun n : ℕ ↦ ∫ x in {x : Fin (n+1) → ℝ | ∀ k : Fin (n+1), x k ∈ Set.Icc 0 1}, (Real.cos (Real.pi/(2 * (n+1)) * ∑ k : Fin (n+1), x k))^2) atTop (𝓝 putnam_1965_b1_solution) :=
by
  have hfun :
      (fun n : ℕ ↦ ∫ x in {x : Fin (n+1) → ℝ | ∀ k : Fin (n+1), x k ∈ Set.Icc 0 1},
        (Real.cos (Real.pi/(2 * (n+1)) * ∑ k : Fin (n+1), x k))^2) =
        (fun _ : ℕ => (1 / 2 : ℝ)) := by
    funext n
    exact putnam_1965_b1_integral_eq n
  rw [putnam_1965_b1_solution, hfun]
  exact tendsto_const_nhds
