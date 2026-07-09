import Mathlib

open Function Equiv

abbrev putnam_1996_b3_solution : ℕ → ℕ :=
  fun n => (∑ k ∈ Finset.range n, (k + 1) ^ 2) - (2 * n - 3)

def putnam_1996_b3_zigzagNat (n i : ℕ) : ℕ :=
  if i = 0 then 1 else if 2 * i ≤ n then 2 * i else 2 * (n - i) + 1

def putnam_1996_b3_zigzag (n i : ℕ) : ℤ :=
  (putnam_1996_b3_zigzagNat n i : ℤ)

lemma putnam_1996_b3_image_range_eq_finset_Icc {n : ℕ} {x : ℕ → ℤ}
    (h : x '' (Finset.range n : Set ℕ) = Set.Icc (1 : ℤ) n) :
    (Finset.range n).image x = Finset.Icc (1 : ℤ) n := by
  ext z
  constructor
  · intro hz
    rw [Finset.mem_image] at hz
    rcases hz with ⟨a, ha, rfl⟩
    have : x a ∈ x '' (Finset.range n : Set ℕ) := ⟨a, by simpa using ha, rfl⟩
    rw [h] at this
    simpa using this
  · intro hz
    have : z ∈ x '' (Finset.range n : Set ℕ) := by
      rw [h]
      simpa using hz
    rcases this with ⟨a, ha, hxa⟩
    rw [Finset.mem_image]
    exact ⟨a, by simpa using ha, hxa⟩

lemma putnam_1996_b3_card_Icc_one_int (n : ℕ) :
    (Finset.Icc (1 : ℤ) (n : ℤ)).card = n := by
  have hcast : ((Finset.Icc (1 : ℤ) (n : ℤ)).card : ℤ) = (n : ℤ) := by
    have hle : (1 : ℤ) ≤ (n : ℤ) + 1 := by omega
    rw [Int.card_Icc_of_le (1 : ℤ) (n : ℤ) hle]
    ring
  exact_mod_cast hcast

lemma putnam_1996_b3_injOn_range_of_image_eq {n : ℕ} {x : ℕ → ℤ}
    (h : x '' (Finset.range n : Set ℕ) = Set.Icc (1 : ℤ) n) :
    Set.InjOn x (Finset.range n : Set ℕ) := by
  have hfin := putnam_1996_b3_image_range_eq_finset_Icc (n := n) (x := x) h
  have hcard : ((Finset.range n).image x).card = (Finset.range n).card := by
    rw [hfin, putnam_1996_b3_card_Icc_one_int, Finset.card_range]
  exact (Finset.card_image_iff).mp hcard

lemma putnam_1996_b3_sum_Icc_one_sq_eq_sum_range (n : ℕ) :
    (∑ z ∈ Finset.Icc (1 : ℤ) (n : ℤ), z ^ 2) =
      ∑ i ∈ Finset.range n, ((i : ℤ) + 1) ^ 2 := by
  refine Finset.sum_bij (fun z _ => (z - 1).toNat) ?_ ?_ ?_ ?_
  · intro z hz
    rw [Finset.mem_Icc] at hz
    rw [Finset.mem_range]
    have hnonneg : 0 ≤ z - 1 := by omega
    rw [Int.toNat_lt hnonneg]
    omega
  · intro a ha b hb hab
    rw [Finset.mem_Icc] at ha hb
    have hnonnega : 0 ≤ a - 1 := by omega
    have hnonnegb : 0 ≤ b - 1 := by omega
    have hcasta : ((a - 1).toNat : ℤ) = a - 1 := Int.toNat_of_nonneg hnonnega
    have hcastb : ((b - 1).toNat : ℤ) = b - 1 := Int.toNat_of_nonneg hnonnegb
    have hcast_eq : ((a - 1).toNat : ℤ) = ((b - 1).toNat : ℤ) := by
      exact_mod_cast hab
    omega
  · intro i hi
    rw [Finset.mem_range] at hi
    refine ⟨(i : ℤ) + 1, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      constructor <;> omega
    · dsimp
      apply Int.ofNat.inj
      change (((((i : ℤ) + 1) - 1).toNat : ℤ) = (i : ℤ))
      rw [Int.toNat_of_nonneg]
      · ring
      · omega
  · intro z hz
    rw [Finset.mem_Icc] at hz
    have hnonneg : 0 ≤ z - 1 := by omega
    have hcast : (((z - 1).toNat : ℤ)) = z - 1 := Int.toNat_of_nonneg hnonneg
    dsimp
    rw [hcast]
    ring

lemma putnam_1996_b3_six_mul_sum_range_sq_succ_int (n : ℕ) :
    6 * (∑ i ∈ Finset.range n, ((i : ℤ) + 1) ^ 2) =
      (n : ℤ) * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      push_cast
      ring

lemma putnam_1996_b3_sum_range_sq_succ_int (n : ℕ) :
    (∑ i ∈ Finset.range n, ((i : ℤ) + 1) ^ 2) =
      ((n * (n + 1) * (2 * n + 1) / 6 : ℕ) : ℤ) := by
  have h6 := putnam_1996_b3_six_mul_sum_range_sq_succ_int n
  rw [Int.natCast_ediv]
  norm_num
  rw [← h6, Int.mul_ediv_cancel_left]
  norm_num

lemma putnam_1996_b3_sum_range_nat_sq_succ_cast (n : ℕ) :
    ((∑ k ∈ Finset.range n, (k + 1) ^ 2 : ℕ) : ℤ) =
      ((n * (n + 1) * (2 * n + 1) / 6 : ℕ) : ℤ) := by
  calc
    ((∑ k ∈ Finset.range n, (k + 1) ^ 2 : ℕ) : ℤ)
        = ∑ k ∈ Finset.range n, ((k : ℤ) + 1) ^ 2 := by
            rw [Nat.cast_sum]
            apply Finset.sum_congr rfl
            intro k _
            norm_num
    _ = ((n * (n + 1) * (2 * n + 1) / 6 : ℕ) : ℤ) :=
            putnam_1996_b3_sum_range_sq_succ_int n

lemma putnam_1996_b3_sum_Icc_nat_sq_cast (n : ℕ) :
    ((∑ k ∈ Finset.Icc 1 n, k ^ 2 : ℕ) : ℤ) =
      ((n * (n + 1) * (2 * n + 1) / 6 : ℕ) : ℤ) := by
  have hsum :
      (∑ k ∈ Finset.Icc 1 n, (k : ℤ) ^ 2) =
        ∑ i ∈ Finset.range n, ((i : ℤ) + 1) ^ 2 := by
    refine Finset.sum_bij (fun k _ => k - 1) ?_ ?_ ?_ ?_
    · intro k hk
      rw [Finset.mem_Icc] at hk
      rw [Finset.mem_range]
      change k - 1 < n
      exact lt_of_lt_of_le (Nat.sub_lt (by omega : 0 < k) (by decide : 0 < 1)) hk.2
    · intro a ha b hb hab
      rw [Finset.mem_Icc] at ha hb
      change a - 1 = b - 1 at hab
      calc
        a = (a - 1) + 1 := (Nat.sub_add_cancel ha.1).symm
        _ = (b - 1) + 1 := by rw [hab]
        _ = b := Nat.sub_add_cancel hb.1
    · intro i hi
      rw [Finset.mem_range] at hi
      refine ⟨i + 1, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        omega
      · change i + 1 - 1 = i
        omega
    · intro k hk
      rw [Finset.mem_Icc] at hk
      have hsub : (((k - 1 : ℕ) : ℤ) + 1) = (k : ℤ) := by omega
      rw [hsub]
  calc
    ((∑ k ∈ Finset.Icc 1 n, k ^ 2 : ℕ) : ℤ)
        = ∑ k ∈ Finset.Icc 1 n, (k : ℤ) ^ 2 := by
            rw [Nat.cast_sum]
            apply Finset.sum_congr rfl
            intro k _
            norm_num
    _ = ∑ i ∈ Finset.range n, ((i : ℤ) + 1) ^ 2 := hsum
    _ = ((n * (n + 1) * (2 * n + 1) / 6 : ℕ) : ℤ) :=
            putnam_1996_b3_sum_range_sq_succ_int n

lemma putnam_1996_b3_sum_Icc_nat_sq_eq (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, k ^ 2) =
      n * (n + 1) * (2 * n + 1) / 6 := by
  exact_mod_cast putnam_1996_b3_sum_Icc_nat_sq_cast n

lemma putnam_1996_b3_square_sum_of_image_eq {n : ℕ} {x : ℕ → ℤ}
    (h : x '' (Finset.range n : Set ℕ) = Set.Icc (1 : ℤ) n) :
    (∑ i : Fin n, x i ^ 2) =
      ((n * (n + 1) * (2 * n + 1) / 6 : ℕ) : ℤ) := by
  have hfin := putnam_1996_b3_image_range_eq_finset_Icc (n := n) (x := x) h
  have hcard : ((Finset.range n).image x).card = (Finset.range n).card := by
    rw [hfin, putnam_1996_b3_card_Icc_one_int, Finset.card_range]
  have hinj : Set.InjOn x (Finset.range n : Set ℕ) := (Finset.card_image_iff).mp hcard
  calc
    (∑ i : Fin n, x i ^ 2)
        = ∑ i ∈ Finset.range n, x i ^ 2 := by
            rw [Finset.sum_fin_eq_sum_range]
            apply Finset.sum_congr rfl
            intro i hi
            simp [Finset.mem_range.mp hi]
    _ = ∑ z ∈ (Finset.range n).image x, z ^ 2 := by
            rw [Finset.sum_image hinj]
    _ = ∑ z ∈ Finset.Icc (1 : ℤ) (n : ℤ), z ^ 2 := by rw [hfin]
    _ = ∑ i ∈ Finset.range n, ((i : ℤ) + 1) ^ 2 :=
            putnam_1996_b3_sum_Icc_one_sq_eq_sum_range n
    _ = ((n * (n + 1) * (2 * n + 1) / 6 : ℕ) : ℤ) :=
            putnam_1996_b3_sum_range_sq_succ_int n

lemma putnam_1996_b3_finRotate_val_mod {n : ℕ} (hn : 0 < n) (i : Fin n) :
    ((finRotate n i : Fin n) : ℕ) = (i.1 + 1) % n := by
  cases n with
  | zero => cases hn
  | succ m =>
      rw [finRotate_succ_apply]
      simp [Fin.add_def]

lemma putnam_1996_b3_sum_next_sq_eq {n : ℕ} (hn : 0 < n) (x : ℕ → ℤ) :
    (∑ i : Fin n, x ((i.1 + 1) % n) ^ 2) = ∑ i : Fin n, x i ^ 2 := by
  calc
    (∑ i : Fin n, x ((i.1 + 1) % n) ^ 2)
        = ∑ i : Fin n, x ((finRotate n i : Fin n) : ℕ) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            rw [putnam_1996_b3_finRotate_val_mod hn]
    _ = ∑ i : Fin n, x i ^ 2 := by
            simpa using Equiv.sum_comp (finRotate n) (fun i : Fin n => x (i : ℕ) ^ 2)

lemma putnam_1996_b3_cyclic_product_identity {n : ℕ} (hn : 0 < n) (x : ℕ → ℤ) :
    2 * (∑ i : Fin n, x i * x ((i.1 + 1) % n)) =
      2 * (∑ i : Fin n, x i ^ 2) -
        ∑ i : Fin n, (x i - x ((i.1 + 1) % n)) ^ 2 := by
  have hnext := putnam_1996_b3_sum_next_sq_eq hn x
  calc
    2 * (∑ i : Fin n, x i * x ((i.1 + 1) % n))
        = ∑ i : Fin n, 2 * (x i * x ((i.1 + 1) % n)) := by
            rw [Finset.mul_sum]
    _ = (∑ i : Fin n, x i ^ 2) + (∑ i : Fin n, x ((i.1 + 1) % n) ^ 2) -
        ∑ i : Fin n, (x i - x ((i.1 + 1) % n)) ^ 2 := by
            rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = 2 * (∑ i : Fin n, x i ^ 2) -
        ∑ i : Fin n, (x i - x ((i.1 + 1) % n)) ^ 2 := by
            rw [hnext]
            ring

lemma putnam_1996_b3_int_dist_eq_natAbs_real (a b : ℤ) :
    dist a b = (Int.natAbs (a - b) : ℝ) := by
  rw [Int.dist_eq, ← Int.cast_sub, ← Int.cast_abs, ← Nat.cast_natAbs]

lemma putnam_1996_b3_int_dist_one_nat (n : ℕ) (hn : 1 ≤ n) :
    dist (1 : ℤ) (n : ℤ) = (n - 1 : ℝ) := by
  rw [Int.dist_eq]
  norm_num
  rw [abs_sub_comm]
  have h : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    exact sub_nonneg.mpr (by exact_mod_cast hn)
  rw [abs_of_nonneg h]

lemma putnam_1996_b3_variation_lower_from_zero {n q : ℕ} (hn : 1 ≤ n) (hq : q ≤ n)
    (y : ℕ → ℤ) (hy0 : y 0 = 1) (hyq : y q = (n : ℤ)) (hyn : y n = 1) :
    (2 * (n - 1 : ℕ) : ℝ) ≤ ∑ i ∈ Finset.range n, dist (y i) (y (i + 1)) := by
  have h1 := dist_le_range_sum_dist y q
  have h2 := dist_le_Ico_sum_dist (f := y) hq
  have hdist1 : dist (y 0) (y q) = (n - 1 : ℝ) := by
    rw [hy0, hyq, putnam_1996_b3_int_dist_one_nat n hn]
  have hdist2 : dist (y q) (y n) = (n - 1 : ℝ) := by
    rw [hyq, hyn, dist_comm, putnam_1996_b3_int_dist_one_nat n hn]
  have hadd := add_le_add h1 h2
  rw [hdist1, hdist2] at hadd
  have hsum := Finset.sum_range_add_sum_Ico (fun i => dist (y i) (y (i + 1))) hq
  rw [hsum] at hadd
  have hsub : ((n : ℝ) - 1) = (n - 1 : ℕ) := by
    rw [← Nat.cast_one, ← Nat.cast_sub hn]
  rw [← hsub]
  simpa [two_mul] using hadd

lemma putnam_1996_b3_finCycle_val_mod {n : ℕ} (p i : Fin n) :
    ((finCycle p i : Fin n) : ℕ) = (i.1 + p.1) % n := by
  rw [finCycle_apply]
  simp [Fin.add_def]

lemma putnam_1996_b3_rotated_edge_abs_sum_eq {n : ℕ} {p : ℕ} (hp : p < n)
    (x : ℕ → ℤ) :
    (∑ i ∈ Finset.range n,
        Int.natAbs (x ((p + i) % n) - x ((p + i + 1) % n))) =
      ∑ i : Fin n, Int.natAbs (x i - x ((i.1 + 1) % n)) := by
  let pF : Fin n := ⟨p, hp⟩
  have hleft :
      (∑ i : Fin n,
        Int.natAbs (x ((p + i.1) % n) - x ((p + i.1 + 1) % n))) =
      (∑ i ∈ Finset.range n,
        Int.natAbs (x ((p + i) % n) - x ((p + i + 1) % n))) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.mem_range.mp hi]
  rw [← hleft]
  calc
    (∑ i : Fin n,
        Int.natAbs (x ((p + i.1) % n) - x ((p + i.1 + 1) % n)))
        = ∑ i : Fin n,
            Int.natAbs (x ((finCycle pF i : Fin n) : ℕ) -
              x ((((finCycle pF i : Fin n) : ℕ) + 1) % n)) := by
            apply Finset.sum_congr rfl
            intro i _
            have hval : ((finCycle pF i : Fin n) : ℕ) = (i.1 + p) % n := by
              simpa [pF] using putnam_1996_b3_finCycle_val_mod pF i
            rw [hval]
            have hmod : (((i.1 + p) % n + 1) % n) = (p + i.1 + 1) % n := by
              rw [Nat.mod_add_mod]
              congr 1
              omega
            rw [hmod, Nat.add_comm p i.1]
    _ = ∑ i : Fin n, Int.natAbs (x i - x ((i.1 + 1) % n)) := by
            simpa using Equiv.sum_comp (finCycle pF)
              (fun j : Fin n => Int.natAbs (x (j : ℕ) - x (((j : ℕ) + 1) % n)))

lemma putnam_1996_b3_cycle_abs_sum_lower {n : ℕ} (hn : 2 ≤ n) {x : ℕ → ℤ}
    (h : x '' (Finset.range n : Set ℕ) = Set.Icc (1 : ℤ) n) :
    2 * (n - 1) ≤ ∑ i : Fin n, Int.natAbs (x i - x ((i.1 + 1) % n)) := by
  have hn1 : 1 ≤ n := by omega
  have hOneMem : (1 : ℤ) ∈ x '' (Finset.range n : Set ℕ) := by
    rw [h]
    exact ⟨le_rfl, by exact_mod_cast hn1⟩
  rcases hOneMem with ⟨p, hpSet, hpval⟩
  have hp : p < n := by simpa using hpSet
  have hnMem : (n : ℤ) ∈ x '' (Finset.range n : Set ℕ) := by
    rw [h]
    exact ⟨by exact_mod_cast hn1, le_rfl⟩
  rcases hnMem with ⟨q, hqSet, hqval⟩
  have hq : q < n := by simpa using hqSet
  let r := (q + n - p) % n
  let y : ℕ → ℤ := fun i => x ((p + i) % n)
  have hrle : r ≤ n := by
    have hrlt : r < n := Nat.mod_lt _ (by omega)
    omega
  have hy0 : y 0 = 1 := by
    dsimp [y]
    rw [Nat.mod_eq_of_lt hp]
    exact hpval
  have hyr : y r = (n : ℤ) := by
    dsimp [y, r]
    have hmod : (p + ((q + n - p) % n)) % n = q := by
      have hmod' : (p + ((q + n - p) % n)) % n = (p + (q + n - p)) % n := by
        rw [Nat.add_mod_mod]
      rw [hmod']
      have hsum : p + (q + n - p) = q + n := by omega
      rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hq]
    rw [hmod]
    exact hqval
  have hyn : y n = 1 := by
    dsimp [y]
    have hmod : (p + n) % n = p := by
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt hp]
    rw [hmod]
    exact hpval
  have hvarR := putnam_1996_b3_variation_lower_from_zero hn1 hrle y hy0 hyr hyn
  have hdist :
      (∑ i ∈ Finset.range n, dist (y i) (y (i + 1))) =
        ((∑ i ∈ Finset.range n,
          Int.natAbs (x ((p + i) % n) - x ((p + i + 1) % n))) : ℝ) := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [y]
    rw [show p + (i + 1) = p + i + 1 by omega]
    rw [putnam_1996_b3_int_dist_eq_natAbs_real]
  rw [hdist] at hvarR
  have hvarNat : 2 * (n - 1) ≤
      ∑ i ∈ Finset.range n,
        Int.natAbs (x ((p + i) % n) - x ((p + i + 1) % n)) := by
    exact_mod_cast hvarR
  rw [putnam_1996_b3_rotated_edge_abs_sum_eq hp x] at hvarNat
  exact hvarNat

lemma putnam_1996_b3_next_ne_self {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    (i.1 + 1) % n ≠ i.1 := by
  intro h
  by_cases hlt : i.1 + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at h
    omega
  · have hige : i.1 + 1 = n := by omega
    rw [hige, Nat.mod_self] at h
    omega

lemma putnam_1996_b3_int_sq_ge_three_abs_sub_two {d : ℤ} (hd : d ≠ 0) :
    3 * (Int.natAbs d : ℤ) - 2 ≤ d ^ 2 := by
  have h1 : (1 : ℤ) ≤ (Int.natAbs d : ℤ) := by
    have hpos : 0 < Int.natAbs d := Int.natAbs_pos.mpr hd
    exact_mod_cast hpos
  have hquad : 3 * (Int.natAbs d : ℤ) - 2 ≤ (Int.natAbs d : ℤ) ^ 2 := by
    nlinarith [sq_nonneg ((Int.natAbs d : ℤ) - 2)]
  simpa [Int.natCast_natAbs, sq_abs] using hquad

lemma putnam_1996_b3_cycle_sqdiff_lower {n : ℕ} (hn : 2 ≤ n) {x : ℕ → ℤ}
    (h : x '' (Finset.range n : Set ℕ) = Set.Icc (1 : ℤ) n) :
    (4 * (n : ℤ) - 6) ≤ ∑ i : Fin n, (x i - x ((i.1 + 1) % n)) ^ 2 := by
  have hinj := putnam_1996_b3_injOn_range_of_image_eq (n := n) (x := x) h
  have habs := putnam_1996_b3_cycle_abs_sum_lower hn h
  have hpoint : ∀ i : Fin n,
      3 * (Int.natAbs (x i - x ((i.1 + 1) % n)) : ℤ) - 2 ≤
        (x i - x ((i.1 + 1) % n)) ^ 2 := by
    intro i
    apply putnam_1996_b3_int_sq_ge_three_abs_sub_two
    apply sub_ne_zero.mpr
    intro hxeq
    have hi_mem : (i.1 : ℕ) ∈ (Finset.range n : Set ℕ) := by simp [i.2]
    have hnpos : 0 < n := by omega
    have hnextlt : (i.1 + 1) % n < n := Nat.mod_lt _ hnpos
    have hnext_mem : ((i.1 + 1) % n) ∈ (Finset.range n : Set ℕ) := by simp [hnextlt]
    have hidx := hinj hi_mem hnext_mem hxeq
    exact putnam_1996_b3_next_ne_self hn i hidx.symm
  have hsum :
      (∑ i : Fin n, (3 * (Int.natAbs (x i - x ((i.1 + 1) % n)) : ℤ) - 2)) ≤
      ∑ i : Fin n, (x i - x ((i.1 + 1) % n)) ^ 2 :=
    Finset.sum_le_sum (fun i _ => hpoint i)
  have habsZ0 : ((2 * (n - 1) : ℕ) : ℤ) ≤
      ∑ i : Fin n, (Int.natAbs (x i - x ((i.1 + 1) % n)) : ℤ) := by
    exact_mod_cast habs
  have hcalc : (4 * (n : ℤ) - 6) ≤
      ∑ i : Fin n, (3 * (Int.natAbs (x i - x ((i.1 + 1) % n)) : ℤ) - 2) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp
    have hsub : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    nlinarith
  exact le_trans hcalc hsum

lemma putnam_1996_b3_two_n_le_sumsq (n : ℕ) (hn : 2 ≤ n) :
    2 * n ≤ n * (n + 1) * (2 * n + 1) / 6 := by
  rw [Nat.le_div_iff_mul_le (by decide : 0 < 6)]
  calc
    (2 * n) * 6 = n * 3 * 4 := by ring
    _ ≤ n * (n + 1) * (2 * n + 1) := by gcongr <;> omega

lemma putnam_1996_b3_solution_cast (n : ℕ) (hn : 2 ≤ n) :
    (putnam_1996_b3_solution n : ℤ) =
      ((n * (n + 1) * (2 * n + 1) / 6 : ℕ) : ℤ) - (2 * (n : ℤ) - 3) := by
  unfold putnam_1996_b3_solution
  have hsub_le :
      2 * n - 3 ≤ ∑ k ∈ Finset.range n, (k + 1) ^ 2 := by
    have hcast := putnam_1996_b3_sum_range_nat_sq_succ_cast n
    have hnat :
        (∑ k ∈ Finset.range n, (k + 1) ^ 2) =
          n * (n + 1) * (2 * n + 1) / 6 := by
      exact_mod_cast hcast
    rw [hnat]
    have htwo := putnam_1996_b3_two_n_le_sumsq n hn
    omega
  rw [Nat.cast_sub hsub_le]
  rw [putnam_1996_b3_sum_range_nat_sq_succ_cast n]
  have hsub_cast : ((2 * n - 3 : ℕ) : ℤ) = 2 * (n : ℤ) - 3 := by omega
  rw [hsub_cast]

lemma putnam_1996_b3_product_le_solution {n : ℕ} (hn : 2 ≤ n) {x : ℕ → ℤ}
    (h : x '' (Finset.range n : Set ℕ) = Set.Icc (1 : ℤ) n) :
    (∑ i : Fin n, x i * x ((i.1 + 1) % n)) ≤
      (putnam_1996_b3_solution n : ℤ) := by
  have hnpos : 0 < n := by omega
  have hident := putnam_1996_b3_cyclic_product_identity hnpos x
  have hQ := putnam_1996_b3_square_sum_of_image_eq (n := n) (x := x) h
  have hD := putnam_1996_b3_cycle_sqdiff_lower hn h
  have h2 : 2 * (∑ i : Fin n, x i * x ((i.1 + 1) % n)) ≤
      2 * (putnam_1996_b3_solution n : ℤ) := by
    rw [hident, hQ, putnam_1996_b3_solution_cast n hn]
    nlinarith
  nlinarith

lemma putnam_1996_b3_zigzag_image_eq_Icc {n : ℕ} (hn : 2 ≤ n) :
    putnam_1996_b3_zigzag n '' (Finset.range n : Set ℕ) = Set.Icc (1 : ℤ) n := by
  ext z
  constructor
  · rintro ⟨i, hiSet, rfl⟩
    have hi : i < n := by simpa using hiSet
    dsimp [putnam_1996_b3_zigzag, putnam_1996_b3_zigzagNat]
    split_ifs with hi0 hle
    · constructor <;> omega
    · constructor <;> omega
    · constructor <;> omega
  · intro hz
    rw [Set.mem_Icc] at hz
    have hz0 : 0 ≤ z := by omega
    let m := z.toNat
    have hmz : (m : ℤ) = z := Int.toNat_of_nonneg hz0
    have hm1 : 1 ≤ m := by omega
    have hmn : m ≤ n := by omega
    by_cases hm_one : m = 1
    · refine ⟨0, by simp; omega, ?_⟩
      dsimp [putnam_1996_b3_zigzag, putnam_1996_b3_zigzagNat]
      omega
    · rcases Nat.even_or_odd m with heven | hodd
      · rcases heven with ⟨a, ha⟩
        have ha_lt : a < n := by omega
        refine ⟨a, by simpa using ha_lt, ?_⟩
        dsimp [putnam_1996_b3_zigzag, putnam_1996_b3_zigzagNat]
        have hnot0 : a ≠ 0 := by omega
        have hle : 2 * a ≤ n := by omega
        simp [hnot0, hle]
        omega
      · rcases hodd with ⟨a, ha⟩
        have hi_lt : n - a < n := by omega
        refine ⟨n - a, by simpa using hi_lt, ?_⟩
        dsimp [putnam_1996_b3_zigzag, putnam_1996_b3_zigzagNat]
        have hnot0 : n - a ≠ 0 := by omega
        have hnotle : ¬ 2 * (n - a) ≤ n := by omega
        simp [hnot0, hnotle]
        omega

lemma putnam_1996_b3_zigzag_edge_zero_sq {n : ℕ} (hn : 2 ≤ n) :
    (putnam_1996_b3_zigzag n 0 - putnam_1996_b3_zigzag n 1) ^ 2 = (1 : ℤ) := by
  dsimp [putnam_1996_b3_zigzag, putnam_1996_b3_zigzagNat]
  simp [show 2 * 1 ≤ n by omega]

lemma putnam_1996_b3_zigzag_edge_diff_bounds {n a : ℕ} (hn : 2 ≤ n) (ha : a < n) :
    (-2 : ℤ) ≤ putnam_1996_b3_zigzag n a -
        putnam_1996_b3_zigzag n ((a + 1) % n) ∧
      putnam_1996_b3_zigzag n a - putnam_1996_b3_zigzag n ((a + 1) % n) ≤ (2 : ℤ) := by
  dsimp [putnam_1996_b3_zigzag, putnam_1996_b3_zigzagNat]
  by_cases hnext : a + 1 < n
  · rw [Nat.mod_eq_of_lt hnext]
    split_ifs
    all_goals try contradiction
    all_goals try subst_vars
    all_goals try push_cast
    all_goals try simp_all
    all_goals try constructor
    all_goals omega
  · have hlast : a + 1 = n := by omega
    rw [hlast, Nat.mod_self]
    split_ifs
    all_goals try contradiction
    all_goals try subst_vars
    all_goals try push_cast
    all_goals try simp_all
    all_goals try constructor
    all_goals omega

lemma putnam_1996_b3_zigzag_edge_mid_sq {n : ℕ} (hn : 2 ≤ n) :
    (putnam_1996_b3_zigzag n (n / 2) -
        putnam_1996_b3_zigzag n (((n / 2) + 1) % n)) ^ 2 = (1 : ℤ) := by
  rcases Nat.even_or_odd n with ⟨q, hnq⟩ | ⟨q, hnq⟩
  · subst n
    have hq : 1 ≤ q := by omega
    have hhalf : (q + q) / 2 = q := by omega
    rw [hhalf]
    by_cases hq1 : q = 1
    · subst q
      norm_num [putnam_1996_b3_zigzag, putnam_1996_b3_zigzagNat]
    · have hnext : (q + 1) % (q + q) = q + 1 := by
        rw [Nat.mod_eq_of_lt]
        omega
      rw [hnext]
      norm_num [putnam_1996_b3_zigzag, putnam_1996_b3_zigzagNat]
      have hq0 : q ≠ 0 := by omega
      have hcur : 2 * q ≤ q + q := by omega
      have hnextbranch : ¬ 2 * (q + 1) ≤ q + q := by omega
      simp [hq0, hcur, hnextbranch]
      left
      omega
  · subst n
    have hq : 1 ≤ q := by omega
    have hhalf : (2 * q + 1) / 2 = q := by omega
    rw [hhalf]
    have hnext : (q + 1) % (2 * q + 1) = q + 1 := by
      rw [Nat.mod_eq_of_lt]
      omega
    rw [hnext]
    norm_num [putnam_1996_b3_zigzag, putnam_1996_b3_zigzagNat]
    have hq0 : q ≠ 0 := by omega
    have hnextbranch : ¬ 2 * (q + 1) ≤ 2 * q + 1 := by omega
    simp [hq0, hnextbranch]
    right
    omega

lemma putnam_1996_b3_zigzag_edge_sq_le_four {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    (putnam_1996_b3_zigzag n i -
        putnam_1996_b3_zigzag n ((i.1 + 1) % n)) ^ 2 ≤ (4 : ℤ) := by
  have hb := putnam_1996_b3_zigzag_edge_diff_bounds hn i.2
  nlinarith [sq_nonneg (putnam_1996_b3_zigzag n i -
      putnam_1996_b3_zigzag n ((i.1 + 1) % n) - 2),
    sq_nonneg (putnam_1996_b3_zigzag n i -
      putnam_1996_b3_zigzag n ((i.1 + 1) % n) + 2)]

lemma putnam_1996_b3_zigzag_sqdiff_sum_le {n : ℕ} (hn : 2 ≤ n) :
    (∑ i : Fin n, (putnam_1996_b3_zigzag n i -
      putnam_1996_b3_zigzag n ((i.1 + 1) % n)) ^ 2) ≤ 4 * (n : ℤ) - 6 := by
  let f : Fin n → ℤ := fun i => (putnam_1996_b3_zigzag n i -
    putnam_1996_b3_zigzag n ((i.1 + 1) % n)) ^ 2
  let i0 : Fin n := ⟨0, by omega⟩
  let im : Fin n := ⟨n / 2, by omega⟩
  have him_ne_i0 : im ≠ i0 := by
    intro h
    have : n / 2 = 0 := by simpa [im, i0] using congrArg Fin.val h
    omega
  have him_mem_erase : im ∈ (Finset.univ.erase i0) := by
    simp [him_ne_i0]
  have hcard : ((Finset.univ.erase i0).erase im).card = n - 2 := by
    rw [Finset.card_erase_of_mem him_mem_erase]
    rw [Finset.card_erase_of_mem (Finset.mem_univ i0)]
    rw [Finset.card_fin]
    omega
  have hrest : (∑ i ∈ (Finset.univ.erase i0).erase im, f i) ≤ (((n - 2) : ℕ) : ℤ) * 4 := by
    calc
      (∑ i ∈ (Finset.univ.erase i0).erase im, f i) ≤
          ∑ i ∈ (Finset.univ.erase i0).erase im, (4 : ℤ) := by
        apply Finset.sum_le_sum
        intro i _
        exact putnam_1996_b3_zigzag_edge_sq_le_four hn i
      _ = (((n - 2) : ℕ) : ℤ) * 4 := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
  have hi0val : f i0 = 1 := by
    dsimp [f, i0]
    rw [Nat.mod_eq_of_lt (by omega : 1 < n)]
    exact putnam_1996_b3_zigzag_edge_zero_sq hn
  have himval : f im = 1 := by
    dsimp [f, im]
    exact putnam_1996_b3_zigzag_edge_mid_sq hn
  have hdecomp :
      (∑ i : Fin n, f i) = (∑ i ∈ (Finset.univ.erase i0).erase im, f i) + f im + f i0 := by
    have h1 := (Finset.sum_erase_add (Finset.univ) f (Finset.mem_univ i0)).symm
    have h2 := (Finset.sum_erase_add (Finset.univ.erase i0) f him_mem_erase).symm
    rw [h1, h2]
  have hsub : (((n - 2 : ℕ) : ℤ)) = (n : ℤ) - 2 := by omega
  rw [show (∑ i : Fin n, (putnam_1996_b3_zigzag n i -
      putnam_1996_b3_zigzag n ((i.1 + 1) % n)) ^ 2) = ∑ i : Fin n, f i by rfl]
  rw [hdecomp, hi0val, himval]
  rw [hsub] at hrest
  nlinarith

lemma putnam_1996_b3_zigzag_product_eq_solution {n : ℕ} (hn : 2 ≤ n) :
    (∑ i : Fin n, putnam_1996_b3_zigzag n i *
      putnam_1996_b3_zigzag n ((i.1 + 1) % n)) =
      (putnam_1996_b3_solution n : ℤ) := by
  have hnpos : 0 < n := by omega
  have hzig := putnam_1996_b3_zigzag_image_eq_Icc hn
  have hident := putnam_1996_b3_cyclic_product_identity hnpos (putnam_1996_b3_zigzag n)
  have hQ := putnam_1996_b3_square_sum_of_image_eq (n := n)
    (x := putnam_1996_b3_zigzag n) hzig
  have hDlower := putnam_1996_b3_cycle_sqdiff_lower hn hzig
  have hDupper := putnam_1996_b3_zigzag_sqdiff_sum_le hn
  have hD : (∑ i : Fin n, (putnam_1996_b3_zigzag n i -
      putnam_1996_b3_zigzag n ((i.1 + 1) % n)) ^ 2) = 4 * (n : ℤ) - 6 :=
    le_antisymm hDupper hDlower
  have h2 : 2 * (∑ i : Fin n, putnam_1996_b3_zigzag n i *
      putnam_1996_b3_zigzag n ((i.1 + 1) % n)) =
      2 * (putnam_1996_b3_solution n : ℤ) := by
    rw [hident, hQ, hD, putnam_1996_b3_solution_cast n hn]
    ring
  nlinarith

/--
Given that $\{x_1,x_2,\ldots,x_n\}=\{1,2,\ldots,n\}$, find, with proof, the largest possible value, as a function of $n$ (with $n \geq 2$), of $x_1x_2+x_2x_3+\cdots+x_{n-1}x_n+x_nx_1$.
-/
theorem putnam_1996_b3
  (n : ℕ) (hn : n ≥ 2) :
  IsGreatest
  {k | ∃ x : ℕ → ℤ,
    (x '' (Finset.range n) = Set.Icc (1 : ℤ) n) ∧
    ∑ i : Fin n, x i * x ((i + 1) % n) = k}
  (putnam_1996_b3_solution n) := by
  constructor
  · refine ⟨putnam_1996_b3_zigzag n, putnam_1996_b3_zigzag_image_eq_Icc hn, ?_⟩
    exact putnam_1996_b3_zigzag_product_eq_solution hn
  · intro k hk
    rcases hk with ⟨x, hx, hsum⟩
    have hleInt : (k : ℤ) ≤ (putnam_1996_b3_solution n : ℤ) := by
      rw [← hsum]
      exact putnam_1996_b3_product_le_solution hn hx
    exact_mod_cast hleInt
