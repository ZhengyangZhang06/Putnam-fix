import Mathlib

open Function
open Finset

private def Pz (n : ℕ) : ℤ := 2*(n:ℤ)^3 + 3*(n:ℤ)^2 - 11*(n:ℤ) + 18
private def Pn (n : ℕ) : ℕ := 2*n^3 + 3*n^2 - 11*n + 18

private lemma Pz_dvd (n : ℕ) : (6:ℤ) ∣ Pz n := by
  induction n with
  | zero => norm_num [Pz]
  | succ n ih =>
      rcases ih with ⟨q, hq⟩
      refine ⟨q + ((n:ℤ)^2 + 2*(n:ℤ) - 1), ?_⟩
      calc
        Pz (n+1) = Pz n + 6 * ((n:ℤ)^2 + 2*(n:ℤ) - 1) := by
          unfold Pz
          norm_num
          ring
        _ = 6 * (q + ((n:ℤ)^2 + 2*(n:ℤ) - 1)) := by
          rw [hq]
          ring

private lemma Pn_cast (n : ℕ) (hn : 2 ≤ n) : ((Pn n : ℕ) : ℤ) = Pz n := by
  unfold Pn Pz
  have hle : 11*n ≤ 2*n^3 + 3*n^2 := by
    nlinarith [sq_nonneg ((n:ℤ) - 2), sq_nonneg ((n:ℤ))]
  rw [Nat.cast_add, Nat.cast_sub hle]
  push_cast
  ring

private lemma Pn_dvd (n : ℕ) (hn : 2 ≤ n) : 6 ∣ Pn n := by
  have hz : (6:ℤ) ∣ Pz n := Pz_dvd n
  rw [← Pn_cast n hn] at hz
  exact_mod_cast hz

private lemma formula_mul_six (n : ℕ) (hn : 2 ≤ n) :
    (6 : ℤ) * (((2 * n ^ 3 + 3 * n ^ 2 - 11 * n + 18) / 6 : ℕ) : ℤ) = Pz n := by
  have hdiv : 6 * (Pn n / 6) = Pn n := by
    rw [mul_comm]
    exact Nat.div_mul_cancel (Pn_dvd n hn)
  calc
    (6 : ℤ) * (((2 * n ^ 3 + 3 * n ^ 2 - 11 * n + 18) / 6 : ℕ) : ℤ)
        = ((6 * (Pn n / 6) : ℕ) : ℤ) := by
          unfold Pn
          norm_num
    _ = ((Pn n : ℕ) : ℤ) := by rw [hdiv]
    _ = Pz n := Pn_cast n hn

private lemma poly_relation (n : ℕ) :
    2 * ((n : ℤ) * ((n : ℤ) + 1) * (2 * (n : ℤ) + 1)) -
        6 * (4 * (n : ℤ) - 6) = 2 * Pz n := by
  unfold Pz
  ring

private lemma sum_squares_range (n : ℕ) :
    6 * (∑ i ∈ Finset.range n, ((i : ℤ) + 1)^2) =
      (n : ℤ) * ((n : ℤ) + 1) * (2 * (n : ℤ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      calc
        6 * ((∑ i ∈ Finset.range n, ((i : ℤ) + 1)^2) + ((n : ℤ) + 1)^2)
            = (n : ℤ) * ((n : ℤ) + 1) * (2 * (n : ℤ) + 1) + 6 * ((n : ℤ) + 1)^2 := by
              rw [mul_add, ih]
        _ = ((n + 1 : ℕ) : ℤ) * (((n + 1 : ℕ) : ℤ) + 1) * (2 * (((n + 1 : ℕ) : ℤ)) + 1) := by
              norm_num
              ring

private lemma sum_squares_fin (n : ℕ) :
    6 * (∑ i : Fin n, ((i : ℤ) + 1)^2) =
      (n : ℤ) * ((n : ℤ) + 1) * (2 * (n : ℤ) + 1) := by
  simpa using congrArg (fun z : ℤ => 6 * z)
    (Fin.sum_univ_eq_sum_range (fun i : ℕ => ((i : ℤ) + 1)^2) n) |>.trans
      (sum_squares_range n)

private lemma card_Icc_one_int (n : ℕ) : Fintype.card (Set.Icc (1 : ℤ) (n : ℤ)) = n := by
  have hcardz : (Fintype.card (Set.Icc (1 : ℤ) (n : ℤ)) : ℤ) = (n : ℤ) := by
    simpa using (Int.card_fintype_Icc_of_le (a := (1 : ℤ)) (b := (n : ℤ)) (by omega))
  exact_mod_cast hcardz

private lemma sum_sq_of_image_eq_Icc (n : ℕ) (x : ℕ → ℤ)
    (hx : x '' (Finset.range n) = Set.Icc (1 : ℤ) (n : ℤ)) :
    6 * (∑ i : Fin n, (x i)^2) =
      (n : ℤ) * ((n : ℤ) + 1) * (2 * (n : ℤ) + 1) := by
  classical
  have hmem (i : Fin n) : x i ∈ Set.Icc (1 : ℤ) (n : ℤ) := by
    rw [← hx]
    exact ⟨(i : ℕ), Finset.mem_range.mpr i.isLt, rfl⟩
  let f : Fin n → Set.Icc (1 : ℤ) (n : ℤ) := fun i => ⟨x i, hmem i⟩
  have hsurj : Function.Surjective f := by
    intro y
    have hy : (y : ℤ) ∈ x '' (Finset.range n) := by
      rw [hx]
      exact y.property
    rcases hy with ⟨m, hm, hxm⟩
    exact ⟨⟨m, Finset.mem_range.mp hm⟩, Subtype.ext hxm⟩
  have hcard : Fintype.card (Fin n) = Fintype.card (Set.Icc (1 : ℤ) (n : ℤ)) := by
    rw [Fintype.card_fin, card_Icc_one_int n]
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_surjective_and_card f).2 ⟨hsurj, hcard⟩
  have hsumx : (∑ i : Fin n, (x i)^2) = ∑ y : Set.Icc (1 : ℤ) (n : ℤ), (y : ℤ)^2 := by
    exact Fintype.sum_bijective f hbij (fun i : Fin n => (x i)^2)
      (fun y : Set.Icc (1 : ℤ) (n : ℤ) => (y : ℤ)^2) (by intro i; rfl)
  let g : Fin n → Set.Icc (1 : ℤ) (n : ℤ) := fun i =>
    ⟨((i : ℕ) : ℤ) + 1, by constructor <;> omega⟩
  have hginj : Function.Injective g := by
    intro i j hij
    apply Fin.ext
    have hv := congrArg Subtype.val hij
    change ((i : ℕ) : ℤ) + 1 = ((j : ℕ) : ℤ) + 1 at hv
    omega
  have hgbij : Function.Bijective g :=
    (Fintype.bijective_iff_injective_and_card g).2 ⟨hginj, hcard⟩
  have hsumIcc : (∑ y : Set.Icc (1 : ℤ) (n : ℤ), (y : ℤ)^2) =
      ∑ i : Fin n, (((i : ℕ) : ℤ) + 1)^2 := by
    exact (Fintype.sum_bijective g hgbij (fun i : Fin n => (((i : ℕ) : ℤ) + 1)^2)
      (fun y : Set.Icc (1 : ℤ) (n : ℤ) => (y : ℤ)^2) (by intro i; rfl)).symm
  rw [hsumx, hsumIcc]
  exact sum_squares_fin n

private lemma int_dist_eq_abs_cast (a b : ℤ) : dist a b = ((|a - b| : ℤ) : ℝ) := by
  rw [Int.dist_eq]
  rw [← Int.cast_sub]
  exact (Int.cast_abs (R := ℝ) (a := a - b)).symm

private lemma range_dist_eq_fin_sum {n : ℕ} [NeZero n] (a : Fin n → ℤ) :
    (∑ i ∈ Finset.range n,
        dist (a ⟨i % n, Nat.mod_lt i (NeZero.pos n)⟩)
          (a ⟨(i + 1) % n, Nat.mod_lt (i + 1) (NeZero.pos n)⟩))
      = ∑ i : Fin n, dist (a i) (a (i + 1)) := by
  calc
    (∑ i ∈ Finset.range n,
        dist (a ⟨i % n, Nat.mod_lt i (NeZero.pos n)⟩)
          (a ⟨(i + 1) % n, Nat.mod_lt (i + 1) (NeZero.pos n)⟩))
        = ∑ i ∈ Finset.range n, dist (a (Fin.ofNat n i)) (a (Fin.ofNat n (i + 1))) := by
          apply Finset.sum_congr rfl
          intro i hi
          rfl
    _ = ∑ i : Fin n, dist (a (Fin.ofNat n i)) (a (Fin.ofNat n (i + 1))) := by
          exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => dist (a (Fin.ofNat n i)) (a (Fin.ofNat n (i + 1)))) n).symm
    _ = ∑ i : Fin n, dist (a i) (a (i + 1)) := by
          apply Finset.sum_congr rfl
          intro i hi
          congr 2
          · apply Fin.ext
            simp
          · apply Fin.ext
            simp [Fin.val_add]

private lemma cyclic_abs_sum_ge_at_zero {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (a : Fin n → ℤ) (q : Fin n) (h0 : a 0 = (1 : ℤ)) (hq : a q = (n : ℤ)) :
    (2 * ((n : ℤ) - 1) : ℤ) ≤ ∑ i : Fin n, |a i - a (i + 1)| := by
  let f : ℕ → ℤ := fun t => a ⟨t % n, Nat.mod_lt t (NeZero.pos n)⟩
  have hf0 : f 0 = (1 : ℤ) := by simp [f, h0]
  have hfq : f q.val = (n : ℤ) := by
    simp [f, Nat.mod_eq_of_lt q.isLt, hq]
  have hfn : f n = (1 : ℤ) := by simp [f, h0]
  have hdist1 : dist (f 0) (f q.val) = (((n : ℤ) - 1 : ℤ) : ℝ) := by
    rw [hf0, hfq, int_dist_eq_abs_cast]
    have habs : |(1 : ℤ) - (n : ℤ)| = (n : ℤ) - 1 := by
      rw [abs_of_nonpos] <;> omega
    rw [habs]
  have hdist2 : dist (f q.val) (f n) = (((n : ℤ) - 1 : ℤ) : ℝ) := by
    rw [hfq, hfn, int_dist_eq_abs_cast]
    have habs : |(n : ℤ) - (1 : ℤ)| = (n : ℤ) - 1 := by
      rw [abs_of_nonneg] <;> omega
    rw [habs]
  have hpath1 := dist_le_range_sum_dist f q.val
  have hpath2 := dist_le_Ico_sum_dist f (show q.val ≤ n from q.isLt.le)
  have hreal_range : (2 * (((n : ℤ) : ℝ) - 1)) ≤
      ∑ i ∈ Finset.range n, dist (f i) (f (i + 1)) := by
    calc
      2 * (((n : ℤ) : ℝ) - 1) = dist (f 0) (f q.val) + dist (f q.val) (f n) := by
        rw [hdist1, hdist2]
        norm_num
        ring
      _ ≤ (∑ i ∈ Finset.range q.val, dist (f i) (f (i + 1))) +
          (∑ i ∈ Finset.Ico q.val n, dist (f i) (f (i + 1))) := by
        exact add_le_add hpath1 hpath2
      _ = ∑ i ∈ Finset.range n, dist (f i) (f (i + 1)) := by
        rw [Finset.sum_range_add_sum_Ico (fun i => dist (f i) (f (i + 1))) (show q.val ≤ n from q.isLt.le)]
  have hreal_fin_dist : (2 * (((n : ℤ) : ℝ) - 1)) ≤ ∑ i : Fin n, dist (a i) (a (i + 1)) := by
    simpa [f] using hreal_range.trans_eq (range_dist_eq_fin_sum a)
  have hreal_fin_abs : (2 * (((n : ℤ) : ℝ) - 1)) ≤
      ∑ i : Fin n, ((|a i - a (i + 1)| : ℤ) : ℝ) := by
    refine hreal_fin_dist.trans_eq ?_
    apply Finset.sum_congr rfl
    intro i hi
    exact int_dist_eq_abs_cast (a i) (a (i + 1))
  exact_mod_cast hreal_fin_abs

private lemma cyclic_abs_sum_ge {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (a : Fin n → ℤ) (p q : Fin n) (hp : a p = (1 : ℤ)) (hq : a q = (n : ℤ)) :
    (2 * ((n : ℤ) - 1) : ℤ) ≤ ∑ i : Fin n, |a i - a (i + 1)| := by
  let b : Fin n → ℤ := fun i => a (p + i)
  have hb0 : b 0 = (1 : ℤ) := by simpa [b] using hp
  have hbq : b (q - p) = (n : ℤ) := by
    have h : p + (q - p) = q := by abel_nf
    simpa [b, h] using hq
  have hb := cyclic_abs_sum_ge_at_zero hn b (q - p) hb0 hbq
  have hrot : (∑ i : Fin n, |b i - b (i + 1)|) = ∑ i : Fin n, |a i - a (i + 1)| := by
    calc
      (∑ i : Fin n, |b i - b (i + 1)|)
          = ∑ i : Fin n, |a (p + i) - a (p + (i + 1))| := by rfl
      _ = ∑ i : Fin n, |a (p + i) - a ((p + i) + 1)| := by
          apply Finset.sum_congr rfl
          intro i hi
          congr 2
          abel_nf
      _ = ∑ i : Fin n, |a i - a (i + 1)| := by
          simpa using (Equiv.sum_comp (Equiv.addLeft p) (fun i : Fin n => |a i - a (i + 1)|))
  rwa [hrot] at hb

private lemma three_mul_sub_two_le_sq_nat (m : ℕ) : (3 * (m : ℤ) - 2) ≤ (m : ℤ)^2 := by
  by_cases h0 : m = 0
  · subst m; norm_num
  · by_cases h1 : m = 1
    · subst m; norm_num
    · have hnonneg : 0 ≤ ((m : ℤ) - 1) * ((m : ℤ) - 2) := by
        exact mul_nonneg (by omega) (by omega)
      nlinarith

private lemma three_abs_sub_two_le_sq (z : ℤ) : 3 * |z| - 2 ≤ z ^ 2 := by
  calc
    3 * |z| - 2 = 3 * (z.natAbs : ℤ) - 2 := by rw [Int.natCast_natAbs]
    _ ≤ (z.natAbs : ℤ)^2 := three_mul_sub_two_le_sq_nat z.natAbs
    _ = |z|^2 := by rw [Int.natCast_natAbs]
    _ = z^2 := sq_abs z

private lemma diff_sq_lower {n : ℕ} [NeZero n] (a : Fin n → ℤ)
    (hvar : (2 * ((n : ℤ) - 1) : ℤ) ≤ ∑ i : Fin n, |a i - a (i + 1)|) :
    (4 * (n : ℤ) - 6 : ℤ) ≤ ∑ i : Fin n, (a i - a (i + 1))^2 := by
  have hedge : (∑ i : Fin n, (3 * |a i - a (i + 1)| - 2 : ℤ)) ≤
      ∑ i : Fin n, (a i - a (i + 1))^2 := by
    apply Finset.sum_le_sum
    intro i hi
    exact three_abs_sub_two_le_sq (a i - a (i + 1))
  have hleft : (∑ i : Fin n, (3 * |a i - a (i + 1)| - 2 : ℤ)) =
      3 * (∑ i : Fin n, |a i - a (i + 1)|) - 2 * (n : ℤ) := by
    simp [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_const, Fintype.card_fin]
    ring
  rw [hleft] at hedge
  nlinarith

private lemma product_identity {n : ℕ} [NeZero n] (x : ℕ → ℤ) :
    2 * (∑ i : Fin n, x i * x ((i + 1) % n)) =
      2 * (∑ i : Fin n, (x i)^2) - ∑ i : Fin n, (x i - x ((i + 1) % n))^2 := by
  let a : Fin n → ℤ := fun i => x i
  have h : 2 * (∑ i : Fin n, a i * a (i + 1)) =
      2 * (∑ i : Fin n, (a i)^2) - ∑ i : Fin n, (a i - a (i + 1))^2 := by
    have hnext : (∑ i : Fin n, (a (i + 1))^2) = ∑ i : Fin n, (a i)^2 := by
      simpa using (Equiv.sum_comp (Equiv.addRight (1 : Fin n)) (fun i : Fin n => (a i)^2))
    calc
      2 * (∑ i : Fin n, a i * a (i + 1))
          = ∑ i : Fin n, 2 * (a i * a (i + 1)) := by rw [Finset.mul_sum]
      _ = ∑ i : Fin n, ((a i)^2 + (a (i + 1))^2 - (a i - a (i + 1))^2) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = (∑ i : Fin n, (a i)^2) + (∑ i : Fin n, (a (i + 1))^2) - ∑ i : Fin n, (a i - a (i + 1))^2 := by
            simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = 2 * (∑ i : Fin n, (a i)^2) - ∑ i : Fin n, (a i - a (i + 1))^2 := by
            rw [hnext]
            ring
  simpa [a, Fin.val_add] using h

private def zig (n i : ℕ) : ℤ :=
  if i < (n + 1) / 2 then ((2 * i + 1 : ℕ) : ℤ) else ((2 * (n - i) : ℕ) : ℤ)

private lemma zig_mem_Icc {n i : ℕ} (hi : i < n) :
    zig n i ∈ Set.Icc (1 : ℤ) (n : ℤ) := by
  unfold zig
  by_cases h : i < (n + 1) / 2
  · rw [if_pos h]
    constructor <;> omega
  · rw [if_neg h]
    constructor <;> omega

private lemma zig_inj_on {n i j : ℕ} (hi : i < n) (hj : j < n)
    (hij : zig n i = zig n j) : i = j := by
  unfold zig at hij
  by_cases hiodd : i < (n + 1) / 2
  · by_cases hjodd : j < (n + 1) / 2
    · rw [if_pos hiodd, if_pos hjodd] at hij
      omega
    · rw [if_pos hiodd, if_neg hjodd] at hij
      omega
  · by_cases hjodd : j < (n + 1) / 2
    · rw [if_neg hiodd, if_pos hjodd] at hij
      omega
    · rw [if_neg hiodd, if_neg hjodd] at hij
      omega

private lemma zig_image_eq_Icc (n : ℕ) :
    zig n '' (Finset.range n : Set ℕ) = Set.Icc (1 : ℤ) (n : ℤ) := by
  classical
  have hsubset : (Finset.range n).image (zig n) ⊆ Finset.Icc (1 : ℤ) (n : ℤ) := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨i, hi, rfl⟩
    simpa using zig_mem_Icc (Finset.mem_range.mp hi)
  have hcard_image : ((Finset.range n).image (zig n)).card = n := by
    rw [Finset.card_image_of_injOn]
    · simp
    · intro i hi j hj hij
      exact zig_inj_on (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij
  have hcard_Icc : (Finset.Icc (1 : ℤ) (n : ℤ)).card = n := by
    have hz : ((Finset.Icc (1 : ℤ) (n : ℤ)).card : ℤ) = (n : ℤ) := by
      simpa using (Int.card_Icc_of_le (a := (1 : ℤ)) (b := (n : ℤ)) (by omega))
    exact_mod_cast hz
  have hfin : (Finset.range n).image (zig n) = Finset.Icc (1 : ℤ) (n : ℤ) := by
    exact Finset.eq_of_subset_of_card_le hsubset (by rw [hcard_image, hcard_Icc])
  ext y
  have hsetfin : (↑((Finset.range n).image (zig n)) : Set ℤ) = (↑(Finset.Icc (1 : ℤ) (n : ℤ)) : Set ℤ) := by
    exact congrArg (fun s : Finset ℤ => (s : Set ℤ)) hfin
  calc
    y ∈ Set.image (zig n) (↑(Finset.range n) : Set ℕ) ↔ y ∈ (↑((Finset.range n).image (zig n)) : Set ℤ) := by
      simp
    _ ↔ y ∈ (↑(Finset.Icc (1 : ℤ) (n : ℤ)) : Set ℤ) := by
      rw [hsetfin]
    _ ↔ y ∈ Set.Icc (1 : ℤ) (n : ℤ) := by
      simp

private lemma zig_join_sq (n : ℕ) (hn : 2 ≤ n) :
    (((2 * ((n + 1) / 2 - 1) + 1 : ℕ) : ℤ) - ((2 * (n - (n + 1) / 2) : ℕ) : ℤ)) ^ 2 = (1 : ℤ) := by
  have hcast1 : (((2 * ((n + 1) / 2 - 1) + 1 : ℕ) : ℤ)) = 2 * (((n + 1) / 2 : ℕ) : ℤ) - 1 := by omega
  have hcast2 : (((2 * (n - (n + 1) / 2) : ℕ) : ℤ)) = 2 * ((n : ℤ) - (((n + 1) / 2 : ℕ) : ℤ)) := by omega
  rw [hcast1, hcast2]
  by_cases heven : Even n
  · rcases heven with ⟨m, rfl⟩
    have hc : (m + m + 1) / 2 = m := by omega
    rw [hc]
    norm_num
  · have hodd : Odd n := Nat.not_even_iff_odd.mp heven
    rcases hodd with ⟨m, rfl⟩
    have hc : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    rw [hc]
    norm_num
    left
    ring

private lemma zig_edge_sq (n i : ℕ) (hn : 2 ≤ n) (hi : i < n) :
    (zig n i - zig n ((i + 1) % n))^2 =
      (if i = (n + 1) / 2 - 1 ∨ i = n - 1 then (1 : ℤ) else 4) := by
  unfold zig
  by_cases hwrap : i = n - 1
  · subst i
    have h0 : (n - 1 + 1) % n = 0 := by
      have : n - 1 + 1 = n := by omega
      rw [this, Nat.mod_self]
    rw [h0]
    have hleft : ¬ n - 1 < (n + 1) / 2 := by omega
    have hzero : 0 < (n + 1) / 2 := by omega
    rw [if_neg hleft, if_pos hzero]
    have hnsub : n - (n - 1) = 1 := by omega
    rw [hnsub]
    simp
  · have hnextlt : i + 1 < n := by omega
    have hmod : (i + 1) % n = i + 1 := Nat.mod_eq_of_lt hnextlt
    rw [hmod]
    by_cases hjoin : i = (n + 1) / 2 - 1
    · subst i
      have hi_left : (n + 1) / 2 - 1 < (n + 1) / 2 := by omega
      have hnext_eq : (n + 1) / 2 - 1 + 1 = (n + 1) / 2 := by omega
      rw [if_pos hi_left, hnext_eq]
      have hnxt' : ¬ (n + 1) / 2 < (n + 1) / 2 := by omega
      rw [if_neg hnxt']
      split_ifs with hbd
      · exact zig_join_sq n hn
      · exfalso; omega
    · by_cases hlow : i < (n + 1) / 2
      · have hnxtlow : i + 1 < (n + 1) / 2 := by omega
        rw [if_pos hlow, if_pos hnxtlow]
        split_ifs with hbd
        · exfalso; omega
        · push_cast
          ring
      · have hnxtlow : ¬ i + 1 < (n + 1) / 2 := by omega
        rw [if_neg hlow, if_neg hnxtlow]
        split_ifs with hbd
        · exfalso; omega
        · have hci : ((n - i : ℕ) : ℤ) = (n : ℤ) - (i : ℤ) := by
            rw [Nat.cast_sub]
            omega
          have hci1 : ((n - (i + 1) : ℕ) : ℤ) = (n : ℤ) - ((i + 1 : ℕ) : ℤ) := by
            rw [Nat.cast_sub]
            omega
          rw [Nat.cast_mul, Nat.cast_mul, hci, hci1]
          push_cast
          ring

private lemma sum_two_exceptions (n a b : ℕ) (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    (∑ i ∈ Finset.range n, (if i = a ∨ i = b then (1 : ℤ) else 4)) = 4 * (n : ℤ) - 6 := by
  classical
  let P : ℕ → Prop := fun i => i = a ∨ i = b
  have hfilter : (Finset.range n).filter P = ({a, b} : Finset ℕ) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton, P]
    constructor
    · intro h
      exact h.2
    · intro h
      constructor
      · rcases h with rfl | rfl
        · exact ha
        · exact hb
      · exact h
  have hboole : (∑ i ∈ Finset.range n, (if P i then (1 : ℤ) else 0)) = 2 := by
    rw [← Finset.sum_filter]
    rw [hfilter]
    simp [hab]
  calc
    (∑ i ∈ Finset.range n, (if i = a ∨ i = b then (1 : ℤ) else 4))
        = ∑ i ∈ Finset.range n, (4 - 3 * (if P i then (1 : ℤ) else 0)) := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hp : P i <;> simp [P, hp]
    _ = 4 * (n : ℤ) - 3 * (∑ i ∈ Finset.range n, (if P i then (1 : ℤ) else 0)) := by
          simp [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_const]
          ring
    _ = 4 * (n : ℤ) - 6 := by
          rw [hboole]
          ring

private lemma zig_diff_sq_sum (n : ℕ) (hn : 2 ≤ n) :
    (∑ i : Fin n, (zig n i - zig n ((i + 1) % n))^2) = 4 * (n : ℤ) - 6 := by
  let f : ℕ → ℤ := fun i => (zig n i - zig n ((i + 1) % n))^2
  change (∑ i : Fin n, f i) = 4 * (n : ℤ) - 6
  rw [Fin.sum_univ_eq_sum_range f n]
  calc
    (∑ i ∈ Finset.range n, f i) = ∑ i ∈ Finset.range n, (if i = (n + 1) / 2 - 1 ∨ i = n - 1 then (1 : ℤ) else 4) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact zig_edge_sq n i hn (Finset.mem_range.mp hi)
    _ = 4 * (n : ℤ) - 6 :=
      sum_two_exceptions n ((n + 1) / 2 - 1) (n - 1) (by omega) (by omega) (by omega)

private lemma product_sum_le_formula (n : ℕ) (hn : 2 ≤ n) (x : ℕ → ℤ)
    (hx : x '' (Finset.range n) = Set.Icc (1 : ℤ) (n : ℤ)) :
    (∑ i : Fin n, x i * x ((i + 1) % n)) ≤
      (((2 * n ^ 3 + 3 * n ^ 2 - 11 * n + 18) / 6 : ℕ) : ℤ) := by
  haveI : NeZero n := ⟨by omega⟩
  let a : Fin n → ℤ := fun i => x i
  have h1mem : (1 : ℤ) ∈ x '' (Finset.range n) := by
    rw [hx]
    exact ⟨by norm_num, by omega⟩
  rcases h1mem with ⟨p0, hp0, hpval⟩
  have hnmem : (n : ℤ) ∈ x '' (Finset.range n) := by
    rw [hx]
    exact ⟨by omega, le_rfl⟩
  rcases hnmem with ⟨q0, hq0, hqval⟩
  let p : Fin n := ⟨p0, Finset.mem_range.mp hp0⟩
  let q : Fin n := ⟨q0, Finset.mem_range.mp hq0⟩
  have hp : a p = (1 : ℤ) := by simpa [a, p] using hpval
  have hq : a q = (n : ℤ) := by simpa [a, q] using hqval
  have hvar := cyclic_abs_sum_ge hn a p q hp hq
  have hdiff_fin := diff_sq_lower a hvar
  have hdiff : (4 * (n : ℤ) - 6 : ℤ) ≤ ∑ i : Fin n, (x i - x ((i + 1) % n))^2 := by
    simpa [a, Fin.val_add] using hdiff_fin
  have hsq := sum_sq_of_image_eq_Icc n x hx
  have hid := product_identity (n := n) x
  have hpoly := poly_relation n
  have hM := formula_mul_six n hn
  nlinarith

-- Note: uses (ℕ → ℕ) instead of (Fin n → ℕ)
-- (fun n : ℕ => (2 * n ^ 3 + 3 * n ^ 2 - 11 * n + 18) / 6)
/--
Given that $\{x_1,x_2,\ldots,x_n\}=\{1,2,\ldots,n\}$, find, with proof, the largest possible value, as a function of $n$ (with $n \geq 2$), of $x_1x_2+x_2x_3+\cdots+x_{n-1}x_n+x_nx_1$.
-/
theorem putnam_1996_b3
  (n : ℕ) (hn : n ≥ 2) :
  IsGreatest
  {k | ∃ x : ℕ → ℤ,
    (x '' (Finset.range n) = Set.Icc (1 : ℤ) n) ∧
    ∑ i : Fin n, x i * x ((i + 1) % n) = k}
  (((fun n : ℕ => (2 * n ^ 3 + 3 * n ^ 2 - 11 * n + 18) / 6) : ℕ → ℕ ) n) := by
  constructor
  · refine ⟨zig n, zig_image_eq_Icc n, ?_⟩
    haveI : NeZero n := ⟨by omega⟩
    have hsq := sum_sq_of_image_eq_Icc n (zig n) (zig_image_eq_Icc n)
    have hdiff := zig_diff_sq_sum n hn
    have hid := product_identity (n := n) (zig n)
    have hpoly := poly_relation n
    have hM := formula_mul_six n hn
    nlinarith
  · intro k hk
    rcases hk with ⟨x, hximg, hxsum⟩
    rw [← hxsum]
    exact product_sum_le_formula n hn x hximg
