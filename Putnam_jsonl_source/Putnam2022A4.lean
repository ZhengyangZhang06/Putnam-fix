import Mathlib

open MeasureTheory ProbabilityTheory Classical

-- 2*Real.exp ((1 : ℝ) / 2) - 3

noncomputable section

def putnam2022A4Cube (n : ℕ) : Set (Fin n → ℝ) := Set.univ.pi fun _ => Set.Ioo (0 : ℝ) 1

def putnam2022A4Cell (n : ℕ) (σ : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
  {x | x ∈ putnam2022A4Cube n ∧ StrictMono (fun a : Fin n => x (σ a))}

def putnam2022A4TieSet (n : ℕ) : Set (Fin n → ℝ) :=
  ⋃ p : Fin n × Fin n, {x | p.1 ≠ p.2 ∧ x p.1 = x p.2}

lemma putnam2022A4_measurableSet_cube (n : ℕ) : MeasurableSet (putnam2022A4Cube n) := by
  unfold putnam2022A4Cube
  exact MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)

lemma putnam2022A4_measurableSet_strict_order (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    MeasurableSet {x : Fin n → ℝ | StrictMono (fun a : Fin n => x (σ a))} := by
  classical
  rw [show {x : Fin n → ℝ | StrictMono (fun a : Fin n => x (σ a))} =
      ⋂ a : Fin n, ⋂ b : Fin n, {x : Fin n → ℝ | a < b → x (σ a) < x (σ b)} by
    ext x
    simp [StrictMono]]
  refine MeasurableSet.iInter fun a => ?_
  refine MeasurableSet.iInter fun b => ?_
  by_cases hab : a < b
  · simpa [hab] using measurableSet_lt (measurable_pi_apply (X := fun _ : Fin n => ℝ) (σ a))
      (measurable_pi_apply (X := fun _ : Fin n => ℝ) (σ b))
  · simp [hab]

lemma putnam2022A4_measurableSet_cell (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    MeasurableSet (putnam2022A4Cell n σ) := by
  unfold putnam2022A4Cell
  exact (putnam2022A4_measurableSet_cube n).inter
    (putnam2022A4_measurableSet_strict_order n σ)

lemma putnam2022A4_cell_sort_eq {n : ℕ} {σ : Equiv.Perm (Fin n)} {x : Fin n → ℝ}
    (hx : x ∈ putnam2022A4Cell n σ) :
    σ = Tuple.sort x := by
  unfold putnam2022A4Cell at hx
  rcases hx with ⟨_, hσ⟩
  rw [Tuple.eq_sort_iff]
  refine ⟨hσ.monotone, ?_⟩
  intro i j hij heq
  exact (ne_of_lt (hσ hij)) (by simpa using heq) |>.elim

lemma putnam2022A4_pairwise_disjoint_cells (n : ℕ) :
    Set.PairwiseDisjoint (Set.univ : Set (Equiv.Perm (Fin n))) (putnam2022A4Cell n) := by
  intro σ _ τ _ hστ
  refine Set.disjoint_left.2 ?_
  intro x hxσ hxτ
  have hs := putnam2022A4_cell_sort_eq hxσ
  have ht := putnam2022A4_cell_sort_eq hxτ
  exact hστ (hs.trans ht.symm)

lemma putnam2022A4_piCongrLeft_preimage_cell (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ) ⁻¹' putnam2022A4Cell n σ =
      putnam2022A4Cell n 1 := by
  ext x
  unfold putnam2022A4Cell putnam2022A4Cube
  constructor
  · intro hx
    rcases hx with ⟨hcube, hmono⟩
    constructor
    · intro j hj
      have h := hcube (σ j) trivial
      simpa [MeasurableEquiv.piCongrLeft_apply_apply] using h
    · intro a b hab
      have h := hmono hab
      simpa [MeasurableEquiv.piCongrLeft_apply_apply] using h
  · intro hx
    rcases hx with ⟨hcube, hmono⟩
    constructor
    · intro j hj
      have h := hcube (σ.symm j) trivial
      have happly := MeasurableEquiv.piCongrLeft_apply_apply
        (β := fun _ : Fin n => ℝ) σ x (σ.symm j)
      simp at happly
      simpa [happly]
    · intro a b hab
      have h := hmono hab
      simpa [MeasurableEquiv.piCongrLeft_apply_apply] using h

lemma putnam2022A4_volume_cell_eq (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (volume : Measure (Fin n → ℝ)) (putnam2022A4Cell n σ) =
      (volume : Measure (Fin n → ℝ)) (putnam2022A4Cell n 1) := by
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) σ
  have h := hmp.measure_preimage (putnam2022A4_measurableSet_cell n σ).nullMeasurableSet
  rw [putnam2022A4_piCongrLeft_preimage_cell n σ] at h
  exact h.symm

lemma putnam2022A4_tie_null {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    (volume : Measure (Fin n → ℝ)) {x | x i = x j} = 0 := by
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) -
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j)
  have hproper : L.ker.toAffineSubspace ≠ (⊤ : AffineSubspace ℝ (Fin n → ℝ)) := by
    intro htop
    have hmem : (Pi.single i (1 : ℝ)) ∈ L.ker := by
      have : (Pi.single i (1 : ℝ)) ∈ (L.ker.toAffineSubspace : Set (Fin n → ℝ)) := by
        rw [htop]
        simp
      simpa [Submodule.mem_toAffineSubspace] using this
    have hval := LinearMap.mem_ker.mp hmem
    have : (1 : ℝ) = 0 := by
      simp [L, hij] at hval
    norm_num at this
  have hzero :=
    Measure.addHaar_affineSubspace (volume : Measure (Fin n → ℝ)) L.ker.toAffineSubspace hproper
  have hset : {x : Fin n → ℝ | x i = x j} = (L.ker.toAffineSubspace : Set (Fin n → ℝ)) := by
    ext x
    simp [L, sub_eq_zero]
  rw [hset]
  exact hzero

lemma putnam2022A4_tieSet_null (n : ℕ) :
    (volume : Measure (Fin n → ℝ)) (putnam2022A4TieSet n) = 0 := by
  unfold putnam2022A4TieSet
  apply measure_iUnion_null
  intro p
  by_cases hp : p.1 = p.2
  · have hempty : {x : Fin n → ℝ | p.1 ≠ p.2 ∧ x p.1 = x p.2} = ∅ := by
      ext x
      simp [hp]
    rw [hempty, measure_empty]
  · exact measure_mono_null (fun _ hx => hx.2) (putnam2022A4_tie_null hp)

lemma putnam2022A4_cube_diff_cells_subset_tieSet (n : ℕ) :
    putnam2022A4Cube n \ (⋃ σ : Equiv.Perm (Fin n), putnam2022A4Cell n σ) ⊆
      putnam2022A4TieSet n := by
  intro x hx
  rcases hx with ⟨hxcube, hxnot⟩
  by_contra hxnotTie
  have hneq : ∀ a b : Fin n, a ≠ b → x a ≠ x b := by
    intro a b hab hxab
    apply hxnotTie
    unfold putnam2022A4TieSet
    exact Set.mem_iUnion.mpr ⟨(a, b), ⟨hab, hxab⟩⟩
  have hstrict : StrictMono (fun a : Fin n => x (Tuple.sort x a)) := by
    intro a b hab
    have hle := Tuple.monotone_sort x hab.le
    have hne : x (Tuple.sort x a) ≠ x (Tuple.sort x b) := by
      apply hneq
      exact (Tuple.sort x).injective.ne hab.ne
    exact lt_of_le_of_ne hle hne
  have hxcell : x ∈ putnam2022A4Cell n (Tuple.sort x) := ⟨hxcube, hstrict⟩
  exact hxnot (Set.mem_iUnion.mpr ⟨Tuple.sort x, hxcell⟩)

lemma putnam2022A4_cells_subset_cube (n : ℕ) :
    (⋃ σ : Equiv.Perm (Fin n), putnam2022A4Cell n σ) ⊆ putnam2022A4Cube n := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨σ, hxσ⟩
  exact hxσ.1

lemma putnam2022A4_volume_cells_union_eq_cube (n : ℕ) :
    (volume : Measure (Fin n → ℝ)) (⋃ σ : Equiv.Perm (Fin n), putnam2022A4Cell n σ) =
      (volume : Measure (Fin n → ℝ)) (putnam2022A4Cube n) := by
  refine measure_eq_measure_of_null_diff (putnam2022A4_cells_subset_cube n) ?_
  exact measure_mono_null (putnam2022A4_cube_diff_cells_subset_tieSet n)
    (putnam2022A4_tieSet_null n)

lemma putnam2022A4_volume_cube_real (n : ℕ) :
    (volume : Measure (Fin n → ℝ)).real (putnam2022A4Cube n) = 1 := by
  unfold putnam2022A4Cube
  simp [Measure.real, Real.volume_pi_Ioo_toReal
    (show (fun _ : Fin n => (0 : ℝ)) ≤ (fun _ => (1 : ℝ)) by intro _; norm_num)]

lemma putnam2022A4_volume_cube_ne_top (n : ℕ) :
    (volume : Measure (Fin n → ℝ)) (putnam2022A4Cube n) ≠ ⊤ := by
  unfold putnam2022A4Cube
  rw [Real.volume_pi_Ioo]
  simp

lemma putnam2022A4_volume_cell_one_real (n : ℕ) :
    (volume : Measure (Fin n → ℝ)).real (putnam2022A4Cell n 1) =
      1 / (Nat.factorial n : ℝ) := by
  let μ : Measure (Fin n → ℝ) := volume
  have hfinite : ∀ b ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))),
      μ (putnam2022A4Cell n b) ≠ ⊤ := by
    intro b _
    exact measure_ne_top_of_subset (fun _ hx => hx.1)
      (by simpa [μ] using putnam2022A4_volume_cube_ne_top n)
  have hsum := measureReal_biUnion_finset (μ := μ)
    (s := (Finset.univ : Finset (Equiv.Perm (Fin n))))
    (by simpa using putnam2022A4_pairwise_disjoint_cells n)
    (by intro σ _; exact putnam2022A4_measurableSet_cell n σ)
    (h := hfinite)
  have hUnion : μ.real (⋃ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))),
      putnam2022A4Cell n σ) = μ.real (putnam2022A4Cube n) := by
    have hset : (⋃ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))), putnam2022A4Cell n σ) =
        ⋃ σ : Equiv.Perm (Fin n), putnam2022A4Cell n σ := by
      ext x
      simp
    rw [hset]
    exact congrArg ENNReal.toReal (putnam2022A4_volume_cells_union_eq_cube n)
  rw [hUnion, putnam2022A4_volume_cube_real n] at hsum
  have hcellreal : ∀ σ : Equiv.Perm (Fin n),
      μ.real (putnam2022A4Cell n σ) = μ.real (putnam2022A4Cell n 1) := by
    intro σ
    simp [Measure.real, μ, putnam2022A4_volume_cell_eq n σ]
  simp_rw [hcellreal] at hsum
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm] at hsum
  rw [Fintype.card_fin] at hsum
  simp only [nsmul_eq_mul] at hsum
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hmul : (Nat.factorial n : ℝ) * μ.real (putnam2022A4Cell n 1) = 1 := hsum.symm
  rw [eq_div_iff hfac]
  simpa [mul_comm, μ] using hmul

def putnam2022A4Rswap (n : ℕ) : Set (ℝ × (Fin (n + 1) → ℝ)) :=
  {p | p.2 ∈ putnam2022A4Cell (n + 1) 1 ∧ p.1 ∈ Set.Ioo 0 (p.2 0)}

lemma putnam2022A4_measurableSet_Rswap (n : ℕ) : MeasurableSet (putnam2022A4Rswap n) := by
  unfold putnam2022A4Rswap
  refine (measurable_snd (putnam2022A4_measurableSet_cell (n + 1) 1)).inter ?_
  exact (measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_lt measurable_fst
      ((measurable_pi_apply (X := fun _ : Fin (n + 1) => ℝ) (0 : Fin (n + 1))).comp
        measurable_snd))

lemma putnam2022A4_swap_preimage_Rswap (n : ℕ) :
    Prod.swap ⁻¹' putnam2022A4Rswap n =
      regionBetween (fun _ : Fin (n + 1) → ℝ => 0) (fun x => x 0)
        (putnam2022A4Cell (n + 1) 1) := by
  ext p
  simp [putnam2022A4Rswap, regionBetween]

lemma putnam2022A4_split_preimage_Rswap (n : ℕ) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => ℝ) 0) ⁻¹'
      putnam2022A4Rswap n = putnam2022A4Cell (n + 2) 1 := by
  ext y
  constructor
  · intro hy
    change (Fin.tail y ∈ putnam2022A4Cell (n + 1) 1 ∧
      y 0 ∈ Set.Ioo 0 ((Fin.tail y) 0)) at hy
    rcases hy with ⟨htail, h0⟩
    rcases htail with ⟨htailcube, htailmono⟩
    constructor
    · intro j hj
      cases j using Fin.cases with
      | zero => exact ⟨h0.1, lt_trans h0.2 (htailcube 0 trivial).2⟩
      | succ k => exact htailcube k trivial
    · intro a b hab
      cases a using Fin.cases with
      | zero =>
          cases b using Fin.cases with
          | zero => exact (lt_irrefl _ hab).elim
          | succ k =>
              have hle : y (Fin.succ 0) ≤ y (Fin.succ k) :=
                htailmono.monotone (by simp)
              exact lt_of_lt_of_le h0.2 hle
      | succ a' =>
          cases b using Fin.cases with
          | zero => exact (not_lt_of_ge (by simp) hab).elim
          | succ b' => exact htailmono (by simpa using hab)
  · intro hy
    rcases hy with ⟨hycube, hymono⟩
    change Fin.tail y ∈ putnam2022A4Cell (n + 1) 1 ∧ y 0 ∈ Set.Ioo 0 ((Fin.tail y) 0)
    constructor
    · constructor
      · intro j hj
        exact hycube j.succ trivial
      · intro a b hab
        exact hymono (by simpa using hab)
    · exact ⟨(hycube 0 trivial).1,
        hymono (show (0 : Fin (n + 2)) < Fin.succ 0 by simp)⟩

lemma putnam2022A4_region_measure_eq_cell_succ (n : ℕ) :
    ((volume : Measure (Fin (n + 1) → ℝ)).prod volume)
      (regionBetween (fun _ : Fin (n + 1) → ℝ => 0) (fun x => x 0)
        (putnam2022A4Cell (n + 1) 1)) =
    (volume : Measure (Fin (n + 2) → ℝ)) (putnam2022A4Cell (n + 2) 1) := by
  have hswap :
      ((volume : Measure (Fin (n + 1) → ℝ)).prod volume)
        (regionBetween (fun _ : Fin (n + 1) → ℝ => 0) (fun x => x 0)
          (putnam2022A4Cell (n + 1) 1)) =
      ((volume : Measure ℝ).prod (volume : Measure (Fin (n + 1) → ℝ)))
        (putnam2022A4Rswap n) := by
    symm
    rw [← Measure.prod_swap (μ := (volume : Measure (Fin (n + 1) → ℝ)))
      (ν := (volume : Measure ℝ))]
    rw [Measure.map_apply measurable_swap (putnam2022A4_measurableSet_Rswap n)]
    rw [putnam2022A4_swap_preimage_Rswap n]
  have hsplit :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 2) => ℝ) (0 : Fin (n + 2))).measure_preimage
      (putnam2022A4_measurableSet_Rswap n).nullMeasurableSet
  rw [putnam2022A4_split_preimage_Rswap n] at hsplit
  exact hswap.trans hsplit.symm

lemma putnam2022A4_integral_cell_zero_eq_volume_succ (n : ℕ) :
    ∫ x in putnam2022A4Cell (n + 1) (1 : Equiv.Perm (Fin (n + 1))),
        x (0 : Fin (n + 1)) ∂(volume : Measure (Fin (n + 1) → ℝ)) =
    (volume : Measure (Fin (n + 2) → ℝ)).real (putnam2022A4Cell (n + 2) 1) := by
  let s := putnam2022A4Cell (n + 1) (1 : Equiv.Perm (Fin (n + 1)))
  let f : (Fin (n + 1) → ℝ) → ℝ := fun x => x 0
  have hs : MeasurableSet s := putnam2022A4_measurableSet_cell (n + 1) 1
  have hfin : (volume : Measure (Fin (n + 1) → ℝ)) s ≠ ⊤ := by
    exact measure_ne_top_of_subset (fun _ hx => hx.1)
      (by simpa [s] using putnam2022A4_volume_cube_ne_top (n + 1))
  have hintOn : IntegrableOn f s (volume : Measure (Fin (n + 1) → ℝ)) := by
    refine Measure.integrableOn_of_bounded hfin
      (measurable_pi_apply (X := fun _ : Fin (n + 1) => ℝ) (0 : Fin (n + 1))).aestronglyMeasurable
      (M := 1) ?_
    filter_upwards [self_mem_ae_restrict hs] with x hx
    have hx0 := hx.1 (0 : Fin (n + 1)) trivial
    change |x 0| ≤ (1 : ℝ)
    exact abs_le.mpr ⟨by linarith [hx0.1], le_of_lt hx0.2⟩
  have hnonneg : 0 ≤ᵐ[(volume : Measure (Fin (n + 1) → ℝ)).restrict s] f := by
    filter_upwards [self_mem_ae_restrict hs] with x hx
    exact le_of_lt (hx.1 (0 : Fin (n + 1)) trivial).1
  have hOfReal := ofReal_integral_eq_lintegral_ofReal hintOn.integrable hnonneg
  have hregion := volume_regionBetween_eq_lintegral'
    (μ := (volume : Measure (Fin (n + 1) → ℝ)))
    (f := fun _ : Fin (n + 1) → ℝ => 0) (g := fun x => x 0) (s := s)
    measurable_const (measurable_pi_apply (X := fun _ : Fin (n + 1) => ℝ) (0 : Fin (n + 1))) hs
  have hregion' :
      ((volume : Measure (Fin (n + 1) → ℝ)).prod volume)
        (regionBetween (fun _ : Fin (n + 1) → ℝ => 0) (fun x => x 0) s) =
      ∫⁻ y in s, ENNReal.ofReal (y 0) ∂(volume : Measure (Fin (n + 1) → ℝ)) := by
    simpa [Pi.sub_apply] using hregion
  simp only [s, f] at hOfReal hregion'
  have hvol : ENNReal.ofReal
        (∫ x in s, f x ∂(volume : Measure (Fin (n + 1) → ℝ))) =
      (volume : Measure (Fin (n + 2) → ℝ)) (putnam2022A4Cell (n + 2) 1) := by
    rw [hOfReal]
    rw [← hregion']
    simpa [s] using putnam2022A4_region_measure_eq_cell_succ n
  have hIntNonneg :
      0 ≤ ∫ x in s, f x ∂(volume : Measure (Fin (n + 1) → ℝ)) :=
    integral_nonneg_of_ae hnonneg
  calc
    ∫ x in putnam2022A4Cell (n + 1) (1 : Equiv.Perm (Fin (n + 1))),
        x (0 : Fin (n + 1)) ∂(volume : Measure (Fin (n + 1) → ℝ))
        = ∫ x in s, f x ∂(volume : Measure (Fin (n + 1) → ℝ)) := rfl
    _ = (ENNReal.ofReal
          (∫ x in s, f x ∂(volume : Measure (Fin (n + 1) → ℝ)))).toReal := by
      rw [ENNReal.toReal_ofReal hIntNonneg]
    _ = (volume : Measure (Fin (n + 2) → ℝ)).real (putnam2022A4Cell (n + 2) 1) := by
      rw [hvol]
      rfl

lemma putnam2022A4_integral_cell_one_zero (n : ℕ) :
    ∫ x in putnam2022A4Cell (n + 1) (1 : Equiv.Perm (Fin (n + 1))),
        x (0 : Fin (n + 1)) ∂(volume : Measure (Fin (n + 1) → ℝ)) =
      1 / (Nat.factorial (n + 2) : ℝ) := by
  rw [putnam2022A4_integral_cell_zero_eq_volume_succ n]
  rw [putnam2022A4_volume_cell_one_real (n + 2)]

lemma putnam2022A4_integral_cell_rev_last (n : ℕ) :
    ∫ x in putnam2022A4Cell (n + 1) (Fin.revPerm : Equiv.Perm (Fin (n + 1))),
        x (Fin.last n) ∂(volume : Measure (Fin (n + 1) → ℝ)) =
      1 / (Nat.factorial (n + 2) : ℝ) := by
  let σ : Equiv.Perm (Fin (n + 1)) := Fin.revPerm
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin (n + 1) => ℝ) σ
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin (n + 1) => ℝ) σ
  have hchange := hmp.setIntegral_preimage_emb e.measurableEmbedding
    (fun y : Fin (n + 1) → ℝ => y (σ 0)) (putnam2022A4Cell (n + 1) σ)
  have hpre := putnam2022A4_piCongrLeft_preimage_cell (n + 1) σ
  rw [hpre] at hchange
  have hcoord : (fun x : Fin (n + 1) → ℝ => e x (σ 0)) =
      fun x => x (0 : Fin (n + 1)) := by
    funext x
    simpa [e] using MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Fin (n + 1) => ℝ) σ x (0 : Fin (n + 1))
  rw [hcoord] at hchange
  have hσ0 : σ 0 = Fin.last n := by
    simp [σ, Fin.revPerm_apply, Fin.rev_zero]
  rw [← hσ0]
  exact hchange.symm.trans (putnam2022A4_integral_cell_one_zero n)

lemma putnam2022A4_descFin_iff_strictMono_rev (n : ℕ) (x : Fin (n + 1) → ℝ) :
    (∀ j : Fin n, x j.castSucc > x j.succ) ↔
      StrictMono (fun a : Fin (n + 1) => x (Fin.revPerm a)) := by
  constructor
  · intro h
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    have hi := h (Fin.rev i)
    simpa [Fin.revPerm_apply, Fin.rev_castSucc, Fin.rev_succ, gt_iff_lt] using hi
  · intro hs j
    have hstep := (Fin.strictMono_iff_lt_succ.mp hs) (Fin.rev j)
    simpa [Fin.revPerm_apply, Fin.rev_castSucc, Fin.rev_succ, gt_iff_lt] using hstep

lemma putnam2022A4_measurableSet_descFin (n : ℕ) :
    MeasurableSet {x : Fin (n + 1) → ℝ | ∀ j : Fin n, x j.castSucc > x j.succ} := by
  rw [show {x : Fin (n + 1) → ℝ | ∀ j : Fin n, x j.castSucc > x j.succ} =
      ⋂ j : Fin n, {x : Fin (n + 1) → ℝ | x j.succ < x j.castSucc} by
    ext x
    simp [gt_iff_lt]]
  exact MeasurableSet.iInter fun j =>
    measurableSet_lt
      (measurable_pi_apply (X := fun _ : Fin (n + 1) => ℝ) j.succ)
      (measurable_pi_apply (X := fun _ : Fin (n + 1) => ℝ) j.castSucc)

lemma putnam2022A4_closed_desc_ae_open_desc (n : ℕ) :
    ((({x : Fin (n + 1) → ℝ | ∀ j : Fin n, x j.castSucc > x j.succ} :
        Set (Fin (n + 1) → ℝ)) ∩
      (Set.univ.pi fun _ : Fin (n + 1) => Set.Icc (0 : ℝ) 1)) :
        Set (Fin (n + 1) → ℝ))
      =ᵐ[(volume : Measure (Fin (n + 1) → ℝ))]
    putnam2022A4Cell (n + 1) (Fin.revPerm : Equiv.Perm (Fin (n + 1))) := by
  have hcube :
      (Set.univ.pi fun _ : Fin (n + 1) => Set.Icc (0 : ℝ) 1)
        =ᵐ[(volume : Measure (Fin (n + 1) → ℝ))]
      (putnam2022A4Cube (n + 1)) := by
    simpa [putnam2022A4Cube, volume_pi] using
      (Measure.univ_pi_Ioo_ae_eq_Icc (μ := fun _ : Fin (n + 1) => (volume : Measure ℝ))
        (f := fun _ : Fin (n + 1) => (0 : ℝ)) (g := fun _ => (1 : ℝ))).symm
  have hstrict :
      ({x : Fin (n + 1) → ℝ | ∀ j : Fin n, x j.castSucc > x j.succ} :
        Set (Fin (n + 1) → ℝ)) =
      {x : Fin (n + 1) → ℝ |
        StrictMono (fun a : Fin (n + 1) =>
          x ((Fin.revPerm : Equiv.Perm (Fin (n + 1))) a))} := by
    ext x
    exact putnam2022A4_descFin_iff_strictMono_rev n x
  rw [hstrict]
  have h := (MeasureTheory.ae_eq_refl
      ({x : Fin (n + 1) → ℝ |
        StrictMono (fun a : Fin (n + 1) =>
          x ((Fin.revPerm : Equiv.Perm (Fin (n + 1))) a))})).inter hcube
  simpa [putnam2022A4Cell, and_comm, Fin.revPerm_apply] using h

lemma putnam2022A4_pi_uniform_measure (n : ℕ) :
    Measure.pi (fun _ : Fin (n + 1) => (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)) =
      (volume : Measure (Fin (n + 1) → ℝ)).restrict
        (Set.univ.pi fun _ : Fin (n + 1) => Set.Icc (0 : ℝ) 1) := by
  rw [← Measure.restrict_pi_pi (μ := fun _ : Fin (n + 1) => (volume : Measure ℝ))
    (s := fun _ : Fin (n + 1) => Set.Icc (0 : ℝ) 1)]
  rw [volume_pi]

lemma putnam2022A4_integral_desc_product (n : ℕ) :
    ∫ x, (if (∀ j : Fin n, x j.castSucc > x j.succ) then
        x (Fin.last n) / ((2 : ℝ) ^ (n + 1)) else 0)
      ∂(Measure.pi (fun _ : Fin (n + 1) =>
        (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1))) =
      1 / (((2 : ℝ) ^ (n + 1)) * (Nat.factorial (n + 2) : ℝ)) := by
  rw [putnam2022A4_pi_uniform_measure n]
  rw [show (fun x : Fin (n + 1) → ℝ =>
      if (∀ j : Fin n, x j.castSucc > x j.succ) then
        x (Fin.last n) / ((2 : ℝ) ^ (n + 1)) else 0) =
      Set.indicator {x : Fin (n + 1) → ℝ | ∀ j : Fin n, x j.castSucc > x j.succ}
        (fun x => x (Fin.last n) / ((2 : ℝ) ^ (n + 1))) by
    funext x
    by_cases hx : ∀ j : Fin n, x j.castSucc > x j.succ <;> simp [Set.indicator, hx]]
  rw [integral_indicator (putnam2022A4_measurableSet_descFin n)]
  change ∫ x, x (Fin.last n) / ((2 : ℝ) ^ (n + 1))
      ∂(((volume : Measure (Fin (n + 1) → ℝ)).restrict
        (Set.univ.pi fun _ : Fin (n + 1) => Set.Icc (0 : ℝ) 1)).restrict
        {x : Fin (n + 1) → ℝ | ∀ j : Fin n, x j.castSucc > x j.succ}) =
      1 / (((2 : ℝ) ^ (n + 1)) * (Nat.factorial (n + 2) : ℝ))
  rw [Measure.restrict_restrict (putnam2022A4_measurableSet_descFin n)]
  change ∫ x in ((({x : Fin (n + 1) → ℝ | ∀ j : Fin n, x j.castSucc > x j.succ} :
      Set (Fin (n + 1) → ℝ)) ∩
      (Set.univ.pi fun _ : Fin (n + 1) => Set.Icc (0 : ℝ) 1)) :
      Set (Fin (n + 1) → ℝ)), x (Fin.last n) / ((2 : ℝ) ^ (n + 1))
      ∂(volume : Measure (Fin (n + 1) → ℝ)) =
      1 / (((2 : ℝ) ^ (n + 1)) * (Nat.factorial (n + 2) : ℝ))
  rw [setIntegral_congr_set (putnam2022A4_closed_desc_ae_open_desc n)]
  rw [integral_div]
  rw [putnam2022A4_integral_cell_rev_last n]
  have hpow : ((2 : ℝ) ^ (n + 1)) ≠ 0 := by positivity
  have hfac : (Nat.factorial (n + 2) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n + 2)
  field_simp [hpow, hfac]

lemma putnam2022A4_mem_k_iff
    {Ω : Type*} (X : ℕ → Ω → ℝ) (k : Ω → Set ℕ)
    (hk : ∀ ω, k ω = sSup { s : Set ℕ |
      ∃ m, s = Set.Iic m ∧ ∀ l, l < m → X l ω > X (l + 1) ω }) :
    ∀ ω i, i ∈ k ω ↔ ∀ l, l < i → X l ω > X (l + 1) ω := by
  intro ω i
  rw [hk ω]
  constructor
  · intro hi l hli
    simp only [Set.sSup_eq_sUnion, Set.mem_sUnion, Set.mem_setOf_eq] at hi
    rcases hi with ⟨s, ⟨m, rfl, hm⟩, his⟩
    exact hm l (lt_of_lt_of_le hli his)
  · intro h
    simp only [Set.sSup_eq_sUnion, Set.mem_sUnion, Set.mem_setOf_eq]
    refine ⟨Set.Iic i, ⟨i, rfl, h⟩, ?_⟩
    simp

lemma putnam2022A4_finite_block_law
    {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i))
    (hX' : ∀ i, MeasureTheory.pdf.IsUniform (X i) (Set.Icc 0 1) ℙ)
    (hX'' : iIndepFun X)
    (n : ℕ) :
    Measure.map (fun ω (j : Fin n) => X j ω) (ℙ : Measure Ω)
      = Measure.pi (fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Icc 0 1)) := by
  have hm : ∀ j : Fin n, AEMeasurable (fun ω => X j ω) (ℙ : Measure Ω) :=
    fun j => (hX j).aemeasurable
  have hfinite : iIndepFun (fun j : Fin n => fun ω => X j ω) (ℙ : Measure Ω) := by
    exact hX''.precomp (fun _ _ h => Fin.ext h)
  have hmap := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map hm).1 hfinite
  rw [hmap]
  congr with j s hs
  have hu := hX' j
  rw [hu]
  rw [ProbabilityTheory.cond_apply (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) 1))]
  rw [Measure.restrict_apply hs]
  simp [Real.volume_Icc, Set.inter_comm]

lemma putnam2022A4_measurableSet_descΩ
    {Ω : Type*} [MeasureSpace Ω]
    (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (n : ℕ) :
    MeasurableSet {ω : Ω | ∀ j : Fin n, X j.val ω > X (j.val + 1) ω} := by
  rw [show {ω : Ω | ∀ j : Fin n, X j.val ω > X (j.val + 1) ω} =
      ⋂ j : Fin n, {ω : Ω | X (j.val + 1) ω < X j.val ω} by
    ext ω
    simp [gt_iff_lt]]
  exact MeasurableSet.iInter fun j => measurableSet_lt (hX (j.val + 1)) (hX j.val)

lemma putnam2022A4_uniform_mem_Icc_ae
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : ℕ → Ω → ℝ)
    (hX' : ∀ i, MeasureTheory.pdf.IsUniform (X i) (Set.Icc 0 1) ℙ)
    (i : ℕ) :
    ∀ᵐ ω ∂(ℙ : Measure Ω), X i ω ∈ Set.Icc (0 : ℝ) 1 := by
  have hpre : (ℙ : Measure Ω) ((X i) ⁻¹' (Set.Icc (0 : ℝ) 1)ᶜ) = 0 := by
    have h := (hX' i).measure_preimage
      (by simp [Real.volume_Icc])
      (by simp [Real.volume_Icc])
      ((measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) 1)).compl)
    rw [h]
    simp [Set.inter_compl_self]
  change (X i ⁻¹' Set.Icc (0 : ℝ) 1) ∈ ae (ℙ : Measure Ω)
  simpa [Set.preimage_compl] using (compl_mem_ae_iff.2 hpre)

lemma putnam2022A4_term_integral
    {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i))
    (hX' : ∀ i, MeasureTheory.pdf.IsUniform (X i) (Set.Icc 0 1) ℙ)
    (hX'' : iIndepFun X)
    (n : ℕ) :
    ∫ ω, (if (∀ j : Fin n, X j.val ω > X (j.val + 1) ω) then
        X n ω / ((2 : ℝ) ^ (n + 1)) else 0) ∂(ℙ : Measure Ω) =
      1 / (((2 : ℝ) ^ (n + 1)) * (Nat.factorial (n + 2) : ℝ)) := by
  let Y : Ω → (Fin (n + 1) → ℝ) := fun ω j => X j.val ω
  let g : (Fin (n + 1) → ℝ) → ℝ := fun x =>
    if (∀ j : Fin n, x j.castSucc > x j.succ) then
      x (Fin.last n) / ((2 : ℝ) ^ (n + 1)) else 0
  have hY : Measurable Y := by
    rw [measurable_pi_iff]
    intro j
    exact hX j.val
  have hg : Measurable g := by
    unfold g
    have hcoord : Measurable (fun x : Fin (n + 1) → ℝ =>
        x (Fin.last n) / ((2 : ℝ) ^ (n + 1))) :=
      (measurable_pi_apply (X := fun _ : Fin (n + 1) => ℝ) (Fin.last n)).div_const
        ((2 : ℝ) ^ (n + 1))
    exact Measurable.ite (putnam2022A4_measurableSet_descFin n) hcoord measurable_const
  have hmap := putnam2022A4_finite_block_law X hX hX' hX'' (n + 1)
  calc
    ∫ ω, (if (∀ j : Fin n, X j.val ω > X (j.val + 1) ω) then
        X n ω / ((2 : ℝ) ^ (n + 1)) else 0) ∂(ℙ : Measure Ω)
        = ∫ ω, g (Y ω) ∂(ℙ : Measure Ω) := by
          apply integral_congr_ae
          filter_upwards with ω
          unfold g Y
          simp
    _ = ∫ x, g x ∂Measure.map Y (ℙ : Measure Ω) := by
          rw [integral_map hY.aemeasurable hg.aestronglyMeasurable]
    _ = ∫ x, g x ∂(Measure.pi (fun _ : Fin (n + 1) =>
          (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1))) := by
          rw [hmap]
    _ = 1 / (((2 : ℝ) ^ (n + 1)) * (Nat.factorial (n + 2) : ℝ)) := by
          exact putnam2022A4_integral_desc_product n

/--
Suppose $X_1, X_2, ...$ real numbers between 0 and 1 that are chosen independently and uniformly at random. Let $S = \sum_{i=1}^k X_i / 2^i $ where $k$ is the least positive integer such that $X_k < X_{k+1}$ or $k = \infty$ if there is no such integer. Find the expected value of $S$
-/
theorem putnam_2022_a4
    {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i))
    (hX' : ∀ i, MeasureTheory.pdf.IsUniform (X i) (Set.Icc 0 1) ℙ)
    (hX'' : iIndepFun X)
    (k : Ω → Set ℕ)
    /-
    If there is an `l` such that `X_l < X_{l+1}` then this is `Set.Iic l` for the smallest such `l`
    Otherwise, this is `sSup { (Set.Iic m : Set ℕ) | (m : ℕ) } = Set.univ`
    -/
    (hk : ∀ ω, k ω = sSup { s : Set ℕ |
      ∃ m, s = Set.Iic m ∧ ∀ l, l < m → X l ω > X (l + 1) ω })
    (S : Ω → ℝ)
    (hS : ∀ ω, S ω = ∑' (i : k ω), (X i ω) / (2 ^ (i.val + 1))) :
    ∫ ω, S ω ∂(ℙ : Measure Ω) = ((2*Real.exp ((1 : ℝ) / 2) - 3) : ℝ ) := by
  let term : ℕ → Ω → ℝ := fun n ω =>
    if (∀ j : Fin n, X j.val ω > X (j.val + 1) ω) then
      X n ω / ((2 : ℝ) ^ (n + 1)) else 0
  have hterm_meas : ∀ n, AEStronglyMeasurable (term n) (ℙ : Measure Ω) := by
    intro n
    have hdesc := putnam2022A4_measurableSet_descΩ X hX n
    have hcoord : Measurable (fun ω => X n ω / ((2 : ℝ) ^ (n + 1))) :=
      (hX n).div_const ((2 : ℝ) ^ (n + 1))
    exact (Measurable.ite hdesc hcoord measurable_const).aestronglyMeasurable
  have hterm_bound : ∀ n,
      (∫⁻ ω, ‖term n ω‖ₑ ∂(ℙ : Measure Ω)) ≤
        ENNReal.ofReal ((1 : ℝ) / ((2 : ℝ) ^ (n + 1))) := by
    intro n
    calc
      (∫⁻ ω, ‖term n ω‖ₑ ∂(ℙ : Measure Ω))
          ≤ ∫⁻ _ω, ENNReal.ofReal ((1 : ℝ) / ((2 : ℝ) ^ (n + 1))) ∂(ℙ : Measure Ω) := by
            apply lintegral_mono_ae
            filter_upwards [putnam2022A4_uniform_mem_Icc_ae X hX' n] with ω hω
            unfold term
            by_cases hdesc : ∀ j : Fin n, X j.val ω > X (j.val + 1) ω
            · have hif :
                  (if (∀ j : Fin n, X j.val ω > X (j.val + 1) ω) then
                    X n ω / ((2 : ℝ) ^ (n + 1)) else 0) =
                  X n ω / ((2 : ℝ) ^ (n + 1)) := by
                simp [hdesc]
              rw [hif]
              have hden : 0 < (2 : ℝ) ^ (n + 1) := by positivity
              have h_abs : |X n ω| ≤ 1 := abs_le.mpr ⟨by linarith [hω.1], hω.2⟩
              rw [← ofReal_norm_eq_enorm]
              apply ENNReal.ofReal_le_ofReal
              rw [Real.norm_eq_abs, abs_div, abs_of_pos hden]
              exact div_le_div_of_nonneg_right h_abs hden.le
            · simp [hdesc]
      _ = ENNReal.ofReal ((1 : ℝ) / ((2 : ℝ) ^ (n + 1))) := by
            simp
  have hbound_sum_ne_top :
      (∑' n, ENNReal.ofReal ((1 : ℝ) / ((2 : ℝ) ^ (n + 1)))) ≠ ⊤ := by
    have hsummable : Summable (fun n : ℕ => (1 : ℝ) / ((2 : ℝ) ^ (n + 1))) := by
      simpa [pow_succ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (summable_geometric_two' (1 : ℝ))
    have hnonneg : ∀ n : ℕ, 0 ≤ (1 : ℝ) / ((2 : ℝ) ^ (n + 1)) := by
      intro n
      positivity
    rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hsummable]
    exact ENNReal.ofReal_ne_top
  have hterm_lintegral_sum_ne_top :
      (∑' n, ∫⁻ ω, ‖term n ω‖ₑ ∂(ℙ : Measure Ω)) ≠ ⊤ := by
    exact ne_top_of_le_ne_top hbound_sum_ne_top (ENNReal.tsum_le_tsum hterm_bound)
  have hSsum : ∀ ω, S ω = ∑' n, term n ω := by
    intro ω
    rw [hS ω]
    rw [tsum_subtype (k ω) (fun i : ℕ => X i ω / ((2 : ℝ) ^ (i + 1)))]
    apply tsum_congr
    intro i
    have hmem := putnam2022A4_mem_k_iff X k hk ω i
    by_cases hi : i ∈ k ω
    · have hdescNat := hmem.mp hi
      have hdescFin : ∀ j : Fin i, X j.val ω > X (j.val + 1) ω := fun j =>
        hdescNat j.val j.isLt
      simp [Set.indicator, hi, term, hdescFin]
    · have hnotdescNat : ¬∀ l, l < i → X l ω > X (l + 1) ω := fun h => hi (hmem.mpr h)
      have hnotdescFin : ¬∀ j : Fin i, X j.val ω > X (j.val + 1) ω := by
        intro hfin
        apply hnotdescNat
        intro l hl
        exact hfin ⟨l, hl⟩
      simp [Set.indicator, hi, term, hnotdescFin]
  have hswap :
      ∫ ω, (∑' n, term n ω) ∂(ℙ : Measure Ω) =
        ∑' n, ∫ ω, term n ω ∂(ℙ : Measure Ω) :=
    integral_tsum hterm_meas hterm_lintegral_sum_ne_top
  have hterm_int : ∀ n,
      ∫ ω, term n ω ∂(ℙ : Measure Ω) =
        1 / (((2 : ℝ) ^ (n + 1)) * (Nat.factorial (n + 2) : ℝ)) := by
    intro n
    unfold term
    exact putnam2022A4_term_integral X hX hX' hX'' n
  calc
    ∫ ω, S ω ∂(ℙ : Measure Ω)
        = ∫ ω, (∑' n, term n ω) ∂(ℙ : Measure Ω) := by
          apply integral_congr_ae
          filter_upwards with ω
          exact hSsum ω
    _ = ∑' n, ∫ ω, term n ω ∂(ℙ : Measure Ω) := hswap
    _ = ∑' n : ℕ, (1 : ℝ) / (((2 : ℝ) ^ (n + 1)) * (Nat.factorial (n + 2) : ℝ)) := by
          apply tsum_congr
          intro n
          exact hterm_int n
    _ = 2 * Real.exp ((1 : ℝ) / 2) - 3 := by
          let f : ℕ → ℝ := fun n => ((1 : ℝ) / 2) ^ n / (Nat.factorial n : ℝ)
          have hExp : HasSum f (Real.exp ((1 : ℝ) / 2)) := by
            rw [Real.exp_eq_exp_ℝ]
            simpa [f] using (NormedSpace.expSeries_div_hasSum_exp ((1 : ℝ) / 2))
          have hShift : HasSum (fun i : ℕ => f (i + 2))
              (Real.exp ((1 : ℝ) / 2) - (1 + ((1 : ℝ) / 2))) := by
            convert (hasSum_nat_add_iff' (f := f) 2).2 hExp using 1
            simp [f]
            ring
          have hMul : HasSum (fun i : ℕ => 2 * f (i + 2))
              (2 * (Real.exp ((1 : ℝ) / 2) - (1 + ((1 : ℝ) / 2)))) :=
            hShift.mul_left 2
          have hTerm : (fun i : ℕ => 2 * f (i + 2)) =
              fun i : ℕ => (1 : ℝ) / (((2 : ℝ) ^ (i + 1)) *
                (Nat.factorial (i + 2) : ℝ)) := by
            funext i
            simp [f, pow_succ]
            ring_nf
          rw [← hTerm]
          rw [hMul.tsum_eq]
          ring
