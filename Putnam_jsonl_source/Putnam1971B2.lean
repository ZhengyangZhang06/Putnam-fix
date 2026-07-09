import Mathlib

open Set MvPolynomial

-- {fun x : ℝ => (x^3 - x^2 - 1)/(2 * x * (x - 1))}
/--
Find all functions $F : \mathbb{R} \setminus \{0, 1\} \to \mathbb{R}$ that satisfy $F(x) + F\left(\frac{x - 1}{x}\right) = 1 + x$ for all $x \in \mathbb{R} \setminus \{0, 1\}$.
-/
theorem putnam_1971_b2
(S : Set ℝ)
(hS : S = univ \ {0, 1})
(P : (ℝ → ℝ) → Prop)
(hP : P = fun (F : ℝ → ℝ) => ∀ x ∈ S, F x + F ((x - 1)/x) = 1 + x)
: (∀ F ∈ (({fun x : ℝ => (x^3 - x^2 - 1)/(2 * x * (x - 1))}) : Set (ℝ → ℝ) ), P F) ∧ ∀ f : ℝ → ℝ, P f → ∃ F ∈ (({fun x : ℝ => (x^3 - x^2 - 1)/(2 * x * (x - 1))}) : Set (ℝ → ℝ) ), (∀ x ∈ S, f x = F x) := by
  subst S
  subst P
  constructor
  · intro F hF
    rw [Set.mem_singleton_iff] at hF
    subst F
    intro x hx
    have hx0 : x ≠ 0 := by
      intro h
      exact hx.2 (by simp [h])
    have hx1 : x ≠ 1 := by
      intro h
      exact hx.2 (by simp [h])
    have hxsub : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
    field_simp [hx0, hx1, hxsub]
    ring_nf
  · intro f hf
    let g : ℝ → ℝ := fun x : ℝ => (x^3 - x^2 - 1)/(2 * x * (x - 1))
    refine ⟨g, ?_, ?_⟩
    · simp [g]
    · intro x hx
      have hT_mem : ∀ {u : ℝ}, u ∈ (univ \ {0, 1} : Set ℝ) → (u - 1) / u ∈ (univ \ {0, 1} : Set ℝ) := by
        intro u hu
        have hu0 : u ≠ 0 := by
          intro h
          exact hu.2 (by simp [h])
        have hu1 : u ≠ 1 := by
          intro h
          exact hu.2 (by simp [h])
        have husub : u - 1 ≠ 0 := sub_ne_zero.mpr hu1
        have ht0 : (u - 1) / u ≠ 0 := by
          intro h
          have : u - 1 = 0 := by
            exact (div_eq_zero_iff.mp h).resolve_right hu0
          exact husub this
        have ht1 : (u - 1) / u ≠ 1 := by
          intro h
          have : u - 1 = u := by
            exact (div_eq_one_iff_eq hu0).mp h
          linarith
        simp [ht0, ht1]
      let y : ℝ := (x - 1) / x
      let z : ℝ := (y - 1) / y
      have hx0 : x ≠ 0 := by
        intro h
        exact hx.2 (by simp [h])
      have hx1 : x ≠ 1 := by
        intro h
        exact hx.2 (by simp [h])
      have hxsub : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
      have hy : y ∈ (univ \ {0, 1} : Set ℝ) := by
        simpa [y] using hT_mem hx
      have hz : z ∈ (univ \ {0, 1} : Set ℝ) := by
        simpa [z] using hT_mem hy
      have h1 : f x + f y = 1 + x := by
        simpa [y] using hf x hx
      have h2 : f y + f z = 1 + y := by
        simpa [z] using hf y hy
      have hcycle : (z - 1) / z = x := by
        subst z
        subst y
        field_simp [hx0, hx1, hxsub]
        ring_nf
      have h3 : f z + f x = 1 + z := by
        simpa [hcycle] using hf z hz
      have hfx : f x = ((1 + x) - (1 + y) + (1 + z)) / 2 := by
        linarith
      have hformula : ((1 + x) - (1 + y) + (1 + z)) / 2 = g x := by
        subst z
        subst y
        dsimp [g]
        field_simp [hx0, hx1, hxsub]
        ring_nf
      exact hfx.trans hformula
