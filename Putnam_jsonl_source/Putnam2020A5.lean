import Mathlib

open Filter Topology Set

namespace Putnam2020A5

private def Rep (n : ℕ) : Set (Finset ℕ) :=
  {S | (∀ k ∈ S, 0 < k) ∧ (∑ k ∈ S, Nat.fib k) = n}

private noncomputable def cnt (n : ℕ) : ℕ :=
  (Rep n).ncard

private def fibLower (m : ℕ) : Finset ℕ :=
  (Finset.range m).erase 0

private lemma mem_fibLower {m k : ℕ} : k ∈ fibLower m ↔ k < m ∧ 0 < k := by
  rw [fibLower]
  simp only [Finset.mem_erase, Finset.mem_range]
  omega

private lemma sum_fibLower (m : ℕ) :
    (∑ k ∈ fibLower m, Nat.fib k) = Nat.fib (m + 1) - 1 := by
  rw [fibLower]
  rw [Finset.sum_erase]
  · have h := Nat.fib_succ_eq_succ_sum m
    omega
  · simp

private lemma fibLower_sdiff_sdiff {m : ℕ} {S : Finset ℕ} (hS : S ⊆ fibLower m) :
    fibLower m \ (fibLower m \ S) = S := by
  ext k
  constructor
  · intro hk
    by_contra hnot
    exact (Finset.mem_sdiff.mp hk).2
      (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hk).1, hnot⟩)
  · intro hk
    exact Finset.mem_sdiff.mpr ⟨hS hk, by simp [hk]⟩

private lemma rep_finite (n : ℕ) : (Rep n).Finite := by
  let B : Set (Finset ℕ) := {S | S ⊆ Finset.range (n + 2)}
  have hB : B.Finite :=
    Set.Finite.ofFinset ((Finset.range (n + 2)).powerset) (by
      intro S
      simp [B])
  refine hB.subset ?_
  intro S hS k hk
  have hkfib : Nat.fib k ≤ n := by
    have hle : Nat.fib k ≤ ∑ i ∈ S, Nat.fib i :=
      Finset.single_le_sum (fun i hi => Nat.zero_le _) hk
    exact hle.trans_eq hS.2
  have hk' : k ≤ n + 1 := (Nat.le_fib_add_one k).trans (Nat.add_le_add_right hkfib 1)
  exact Finset.mem_range.mpr (by omega)

private lemma cnt_zero : cnt 0 = 1 := by
  have hrep : Rep 0 = ({∅} : Set (Finset ℕ)) := by
    ext S
    constructor
    · intro hS
      have hzero : ∀ k ∈ S, Nat.fib k = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun k hk => Nat.zero_le _)).1 hS.2
      have hempty : S = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro k hk
        have hkpos : 0 < Nat.fib k := Nat.fib_pos.mpr (hS.1 k hk)
        exact hkpos.ne' (hzero k hk)
      simp [hempty]
    · intro hS
      rcases hS with rfl
      simp [Rep]
  simp [cnt, hrep]

private lemma rep_sum_le {S : Finset ℕ} {n k : ℕ} (hS : S ∈ Rep n) (hk : k ∈ S) :
    Nat.fib k ≤ n := by
  have hle : Nat.fib k ≤ ∑ i ∈ S, Nat.fib i :=
    Finset.single_le_sum (fun i hi => Nat.zero_le _) hk
  exact hle.trans_eq hS.2

private lemma rep_no_large {S : Finset ℕ} {n m k : ℕ}
    (hS : S ∈ Rep n) (hk : k ∈ S) (hhi : n < Nat.fib (m + 1)) :
    k ≤ m := by
  by_contra hkm
  have hmk : m + 1 ≤ k := by omega
  have hfib : Nat.fib (m + 1) ≤ Nat.fib k := Nat.fib_mono hmk
  exact (not_le_of_gt hhi) (hfib.trans (rep_sum_le hS hk))

private lemma rep_subset_lower_of_notMem {S : Finset ℕ} {n m : ℕ}
    (hS : S ∈ Rep n) (hhi : n < Nat.fib (m + 1)) (hmS : m ∉ S) :
    S ⊆ fibLower m := by
  intro k hk
  have hkm : k ≤ m := rep_no_large hS hk hhi
  have hkne : k ≠ m := by
    intro h
    exact hmS (h ▸ hk)
  exact mem_fibLower.mpr ⟨lt_of_le_of_ne hkm hkne, hS.1 k hk⟩

private lemma fib_sub_left_lt {m n : ℕ} (hm : 2 ≤ m)
    (hlo : Nat.fib m ≤ n) (hhi : n < Nat.fib (m + 1)) :
    n - Nat.fib m < Nat.fib m := by
  have hm0 : m ≠ 0 := by omega
  have hrec : Nat.fib (m + 1) = Nat.fib (m - 1) + Nat.fib m :=
    Nat.fib_add_one hm0
  have hmono : Nat.fib (m - 1) ≤ Nat.fib m := Nat.fib_mono (Nat.sub_le _ _)
  have hprevpos : 0 < Nat.fib (m - 1) := Nat.fib_pos.mpr (by omega)
  omega

private lemma fib_compl_lt {m n : ℕ} (hm : 2 ≤ m)
    (hlo : Nat.fib m ≤ n) :
    Nat.fib (m + 1) - 1 - n < Nat.fib m := by
  have hm0 : m ≠ 0 := by omega
  have hrec : Nat.fib (m + 1) = Nat.fib (m - 1) + Nat.fib m :=
    Nat.fib_add_one hm0
  have hmono : Nat.fib (m - 1) ≤ Nat.fib m := Nat.fib_mono (Nat.sub_le _ _)
  have hprevpos : 0 < Nat.fib (m - 1) := Nat.fib_pos.mpr (by omega)
  omega

private lemma rep_notMem_of_sum_lt {S : Finset ℕ} {n m : ℕ}
    (hS : S ∈ Rep n) (hlt : n < Nat.fib m) :
    m ∉ S := by
  intro hmS
  exact (not_le_of_gt hlt) (rep_sum_le hS hmS)

private lemma rep_subset_lower_of_sum_lt {S : Finset ℕ} {n m : ℕ}
    (hS : S ∈ Rep n) (hlt : n < Nat.fib m) :
    S ⊆ fibLower m := by
  intro k hk
  have hklt : k < m := by
    by_contra hkm
    have hmk : m ≤ k := by omega
    have hfib : Nat.fib m ≤ Nat.fib k := Nat.fib_mono hmk
    exact (not_le_of_gt hlt) (hfib.trans (rep_sum_le hS hk))
  exact mem_fibLower.mpr ⟨hklt, hS.1 k hk⟩

private lemma cnt_recur {m n : ℕ} (hm : 2 ≤ m)
    (hlo : Nat.fib m ≤ n) (hhi : n < Nat.fib (m + 1)) :
    cnt n = cnt (n - Nat.fib m) + cnt (Nat.fib (m + 1) - 1 - n) := by
  classical
  let L : Set (Finset ℕ) := {S | S ∈ Rep n ∧ m ∈ S}
  let R : Set (Finset ℕ) := {S | S ∈ Rep n ∧ m ∉ S}
  have hsplit : Rep n = L ∪ R := by
    ext S
    by_cases hmS : m ∈ S <;> simp [L, R, hmS]
  have hdisj : Disjoint L R := by
    rw [Set.disjoint_left]
    intro S hSL hSR
    exact hSR.2 hSL.2
  have hfinL : L.Finite := (rep_finite n).subset (by intro S hS; exact hS.1)
  have hfinR : R.Finite := (rep_finite n).subset (by intro S hS; exact hS.1)
  have hxlt : n - Nat.fib m < Nat.fib m := fib_sub_left_lt hm hlo hhi
  have hylt : Nat.fib (m + 1) - 1 - n < Nat.fib m := fib_compl_lt hm hlo
  have hLcard : L.ncard = cnt (n - Nat.fib m) := by
    refine Set.ncard_congr (fun S hS => S.erase m) ?_ ?_ ?_
    · intro S hS
      have hrep : S ∈ Rep n := hS.1
      have hmS : m ∈ S := hS.2
      refine ⟨?_, ?_⟩
      · intro k hk
        exact hrep.1 k (Finset.mem_of_mem_erase hk)
      · change (∑ k ∈ S.erase m, Nat.fib k) = n - Nat.fib m
        have hsum := Finset.sum_erase_add S (fun k => Nat.fib k) hmS
        apply Nat.eq_sub_of_add_eq
        calc
          (∑ k ∈ S.erase m, Nat.fib k) + Nat.fib m = ∑ k ∈ S, Nat.fib k := hsum
          _ = n := hrep.2
    · intro S T hS hT hST
      apply Finset.ext
      intro k
      by_cases hkm : k = m
      · subst k
        simp [hS.2, hT.2]
      · have hsimpS : k ∈ S.erase m ↔ k ∈ S := by simp [hkm]
        have hsimpT : k ∈ T.erase m ↔ k ∈ T := by simp [hkm]
        simpa [hsimpS, hsimpT] using Finset.ext_iff.mp hST k
    · intro T hT
      refine ⟨insert m T, ?_, ?_⟩
      · refine ⟨?_, Finset.mem_insert_self _ _⟩
        refine ⟨?_, ?_⟩
        · intro k hk
          rcases Finset.mem_insert.mp hk with rfl | hkT
          · omega
          · exact hT.1 k hkT
        · have hmT : m ∉ T := rep_notMem_of_sum_lt hT hxlt
          simp [Finset.sum_insert, hmT, hT.2]
          omega
      · have hmT : m ∉ T := rep_notMem_of_sum_lt hT hxlt
        simp [hmT]
  have hRcard : R.ncard = cnt (Nat.fib (m + 1) - 1 - n) := by
    refine Set.ncard_congr (fun S hS => fibLower m \ S) ?_ ?_ ?_
    · intro S hS
      have hsub : S ⊆ fibLower m := rep_subset_lower_of_notMem hS.1 hhi hS.2
      refine ⟨?_, ?_⟩
      · intro k hk
        exact (mem_fibLower.mp (Finset.mem_sdiff.mp hk).1).2
      · have hsdiff := Finset.sum_sdiff hsub (f := fun k => Nat.fib k)
        have hlow := sum_fibLower m
        have hrep : (∑ k ∈ S, Nat.fib k) = n := hS.1.2
        change (∑ k ∈ fibLower m \ S, Nat.fib k) = Nat.fib (m + 1) - 1 - n
        apply Nat.eq_sub_of_add_eq
        calc
          (∑ k ∈ fibLower m \ S, Nat.fib k) + n
              = (∑ k ∈ fibLower m \ S, Nat.fib k) + (∑ k ∈ S, Nat.fib k) := by rw [hrep]
          _ = ∑ k ∈ fibLower m, Nat.fib k := hsdiff
          _ = Nat.fib (m + 1) - 1 := hlow
    · intro S T hS hT hST
      have hsubS : S ⊆ fibLower m := rep_subset_lower_of_notMem hS.1 hhi hS.2
      have hsubT : T ⊆ fibLower m := rep_subset_lower_of_notMem hT.1 hhi hT.2
      have hST' : fibLower m \ S = fibLower m \ T := by simpa using hST
      have h1 : fibLower m \ (fibLower m \ S) = fibLower m \ (fibLower m \ T) := by
        rw [hST']
      simpa [fibLower_sdiff_sdiff hsubS, fibLower_sdiff_sdiff hsubT] using h1
    · intro T hT
      have hsubT : T ⊆ fibLower m := rep_subset_lower_of_sum_lt hT hylt
      refine ⟨fibLower m \ T, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · refine ⟨?_, ?_⟩
          · intro k hk
            exact (mem_fibLower.mp (Finset.mem_sdiff.mp hk).1).2
          · have hsdiff := Finset.sum_sdiff hsubT (f := fun k => Nat.fib k)
            have hlow := sum_fibLower m
            have hrep : (∑ k ∈ T, Nat.fib k) = Nat.fib (m + 1) - 1 - n := hT.2
            change (∑ k ∈ fibLower m \ T, Nat.fib k) = n
            have htotal : n ≤ Nat.fib (m + 1) - 1 := Nat.le_sub_one_of_lt hhi
            have hsum_eq :
                (∑ k ∈ fibLower m \ T, Nat.fib k) +
                    (Nat.fib (m + 1) - 1 - n) = Nat.fib (m + 1) - 1 := by
              calc
                (∑ k ∈ fibLower m \ T, Nat.fib k) + (Nat.fib (m + 1) - 1 - n)
                    = (∑ k ∈ fibLower m \ T, Nat.fib k) + (∑ k ∈ T, Nat.fib k) := by rw [hrep]
                _ = ∑ k ∈ fibLower m, Nat.fib k := hsdiff
                _ = Nat.fib (m + 1) - 1 := hlow
            omega
        · intro hmS
          have hmLower : m ∈ fibLower m := (Finset.mem_sdiff.mp hmS).1
          exact (not_lt_of_ge le_rfl) (mem_fibLower.mp hmLower).1
      · exact fibLower_sdiff_sdiff hsubT
  calc
    cnt n = (L ∪ R).ncard := by rw [cnt, hsplit]
    _ = L.ncard + R.ncard := by
      exact Set.ncard_union_eq hdisj hfinL hfinR
    _ = cnt (n - Nat.fib m) + cnt (Nat.fib (m + 1) - 1 - n) := by
      rw [hLcard, hRcard]

private lemma cnt_pos (n : ℕ) : 0 < cnt n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · simp [hn, cnt_zero]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hm2 : 2 ≤ Nat.greatestFib n := by
        rw [Nat.le_greatestFib]
        simpa [Nat.fib_two] using hnpos
      have hrec := cnt_recur hm2 (Nat.fib_greatestFib_le n) (Nat.lt_fib_greatestFib_add_one n)
      have hxlt : n - Nat.fib (Nat.greatestFib n) < n := by
        exact Nat.sub_lt hnpos (Nat.fib_pos.mpr (by omega : 0 < Nat.greatestFib n))
      have hylt : Nat.fib (Nat.greatestFib n + 1) - 1 - n < n := by
        have hm0 : Nat.greatestFib n ≠ 0 := by omega
        have hrecfib : Nat.fib (Nat.greatestFib n + 1) =
            Nat.fib (Nat.greatestFib n - 1) + Nat.fib (Nat.greatestFib n) :=
          Nat.fib_add_one hm0
        have hmono : Nat.fib (Nat.greatestFib n - 1) ≤ n := by
          exact (Nat.fib_mono (Nat.sub_le _ _)).trans (Nat.fib_greatestFib_le n)
        have hfm : Nat.fib (Nat.greatestFib n) ≤ n := Nat.fib_greatestFib_le n
        have hle2 : Nat.fib (Nat.greatestFib n + 1) ≤ n + n := by omega
        omega
      rw [hrec]
      exact Nat.add_pos_left (ih _ hxlt) _

private lemma fib_add_le_fib_add_pred {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    Nat.fib a + Nat.fib b ≤ Nat.fib (a + b - 1) := by
  have hidx : a + b - 1 = (a - 1) + (b - 1) + 1 := by omega
  rw [hidx, Nat.fib_add]
  rw [show a - 1 + 1 = a by omega, show b - 1 + 1 = b by omega]
  have ha1 : 1 ≤ Nat.fib a := Nat.succ_le_iff.mpr (Nat.fib_pos.mpr (by omega))
  have hb1 : 1 ≤ Nat.fib b := Nat.succ_le_iff.mpr (Nat.fib_pos.mpr (by omega))
  have hab : Nat.fib a + Nat.fib b ≤ Nat.fib a * Nat.fib b + 1 := by
    nlinarith [ha1, hb1, mul_nonneg (Nat.zero_le (Nat.fib a)) (Nat.zero_le (Nat.fib b))]
  have hprev : 1 ≤ Nat.fib (a - 1) * Nat.fib (b - 1) := by
    have hpa : 0 < Nat.fib (a - 1) := Nat.fib_pos.mpr (by omega)
    have hpb : 0 < Nat.fib (b - 1) := Nat.fib_pos.mpr (by omega)
    exact Nat.succ_le_iff.mpr (Nat.mul_pos hpa hpb)
  nlinarith

private lemma cnt_fib_sub_one : ∀ k : ℕ, 0 < k → cnt (Nat.fib (2 * k) - 1) = k
  | 0, hk => by omega
  | k + 1, _ => by
      induction k with
      | zero =>
          simp [Nat.fib_two, cnt_zero]
      | succ k ih =>
          have hm : 2 ≤ 2 * (k + 1) + 1 := by omega
          have hle : Nat.fib (2 * (k + 1) + 1) ≤ Nat.fib (2 * (k + 2)) - 1 := by
            have hlt : Nat.fib (2 * (k + 1) + 1) < Nat.fib (2 * (k + 2)) := by
              have hstrict := Nat.fib_lt_fib_succ (n := 2 * (k + 1) + 1) (by omega)
              simpa [show 2 * (k + 1) + 1 + 1 = 2 * (k + 2) by omega] using hstrict
            omega
          have hhi : Nat.fib (2 * (k + 2)) - 1 < Nat.fib (2 * (k + 1) + 1 + 1) := by
            simp [show 2 * (k + 1) + 1 + 1 = 2 * (k + 2) by omega]
          have hrec := cnt_recur hm hle hhi
          have harg1 : Nat.fib (2 * (k + 2)) - 1 - Nat.fib (2 * (k + 1) + 1) =
              Nat.fib (2 * (k + 1)) - 1 := by
            have hfib : Nat.fib (2 * (k + 1) + 1) =
                Nat.fib (2 * (k + 1) - 1) + Nat.fib (2 * (k + 1)) := by
              apply Nat.fib_add_one
              omega
            have hfib2 : Nat.fib (2 * (k + 2)) =
                Nat.fib (2 * (k + 1)) + Nat.fib (2 * (k + 1) + 1) := by
              simpa [show 2 * (k + 2) = 2 * (k + 1) + 2 by omega] using
                (Nat.fib_add_two (n := 2 * (k + 1)))
            omega
          have harg2 : Nat.fib (2 * (k + 1) + 1 + 1) - 1 -
                (Nat.fib (2 * (k + 2)) - 1) = 0 := by
            simp [show 2 * (k + 1) + 1 + 1 = 2 * (k + 2) by omega]
          rw [hrec, harg1, harg2, ih, cnt_zero]
          omega

private lemma cnt_upper (k n : ℕ) (h : cnt n = k) : n ≤ Nat.fib (2 * k) - 1 := by
  revert n
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro n hn
    by_cases hk0 : k = 0
    · subst k
      have hpos := cnt_pos n
      omega
    by_cases hn0 : n = 0
    · subst n
      exact Nat.zero_le _
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hm2 : 2 ≤ Nat.greatestFib n := by
      rw [Nat.le_greatestFib]
      simpa [Nat.fib_two] using hnpos
    let m := Nat.greatestFib n
    let x := n - Nat.fib m
    let y := Nat.fib (m + 1) - 1 - n
    have hrec : cnt n = cnt x + cnt y := by
      simpa [m, x, y] using
        cnt_recur hm2 (Nat.fib_greatestFib_le n) (Nat.lt_fib_greatestFib_add_one n)
    have hsum : cnt x + cnt y = k := by simpa [hrec] using hn
    have hxpos : 0 < cnt x := cnt_pos x
    have hypos : 0 < cnt y := cnt_pos y
    have hxltK : cnt x < k := by omega
    have hyltK : cnt y < k := by omega
    have hxle := ih (cnt x) hxltK x rfl
    have hyle := ih (cnt y) hyltK y rfl
    have hxy : x + y + 1 = Nat.fib (m - 1) := by
      have hm0 : m ≠ 0 := by omega
      have hrecfib : Nat.fib (m + 1) = Nat.fib (m - 1) + Nat.fib m :=
        Nat.fib_add_one hm0
      have hmle : Nat.fib m ≤ n := Nat.fib_greatestFib_le n
      have hnle : n ≤ Nat.fib (m + 1) - 1 := by
        exact Nat.le_sub_one_of_lt (Nat.lt_fib_greatestFib_add_one n)
      simp [x, y]
      omega
    have hfibsum : Nat.fib (2 * cnt x) + Nat.fib (2 * cnt y) ≤ Nat.fib (2 * k - 1) := by
      have hx2 : 2 ≤ 2 * cnt x := by omega
      have hy2 : 2 ≤ 2 * cnt y := by omega
      have hbase := fib_add_le_fib_add_pred hx2 hy2
      have hidx : 2 * cnt x + 2 * cnt y - 1 = 2 * k - 1 := by omega
      simpa [hidx] using hbase
    have hmFibLt : Nat.fib (m - 1) < Nat.fib (2 * k - 1) := by
      have hxFibPos : 0 < Nat.fib (2 * cnt x) := Nat.fib_pos.mpr (by omega)
      have hyFibPos : 0 < Nat.fib (2 * cnt y) := Nat.fib_pos.mpr (by omega)
      have hbound : x + y + 1 < Nat.fib (2 * cnt x) + Nat.fib (2 * cnt y) := by
        omega
      have hbound' : Nat.fib (m - 1) < Nat.fib (2 * cnt x) + Nat.fib (2 * cnt y) := by
        simpa [hxy] using hbound
      exact hbound'.trans_le hfibsum
    have hmIdx : m - 1 < 2 * k - 1 := by
      by_contra hnot
      have hleidx : 2 * k - 1 ≤ m - 1 := by omega
      have hlefib : Nat.fib (2 * k - 1) ≤ Nat.fib (m - 1) := Nat.fib_mono hleidx
      exact (not_le_of_gt hmFibLt) hlefib
    have hmLt : m < 2 * k := by omega
    have hnlt : n < Nat.fib (2 * k) := by
      have hm1le : m + 1 ≤ 2 * k := by omega
      exact (Nat.lt_fib_greatestFib_add_one n).trans_le (Nat.fib_mono hm1le)
    exact Nat.le_sub_one_of_lt hnlt

private lemma int_count_nat (n : ℕ) :
    ({S : Finset ℕ | (∀ k ∈ S, k > 0) ∧
      ((∑ k ∈ S.attach, Nat.fib (k : ℕ) : ℕ) : ℤ) = (n : ℤ)}.ncard) =
      cnt n := by
  congr 1
  ext S
  constructor
  · intro hS
    refine ⟨hS.1, ?_⟩
    have hmem : ((∑ k ∈ S, Nat.fib k : ℕ) : ℤ) = (n : ℤ) := by
      rw [← Finset.sum_attach S Nat.fib]
      exact hS.2
    exact_mod_cast hmem
  · intro hS
    refine ⟨hS.1, ?_⟩
    rw [Finset.sum_attach S Nat.fib]
    exact_mod_cast hS.2

end Putnam2020A5

-- (Nat.fib 4040) - 1
/--
Let $a_n$ be the number of sets $S$ of positive integers for which
\[
\sum_{k \in S} F_k = n,
\]
where the Fibonacci sequence $(F_k)_{k \geq 1}$ satisfies $F_{k+2} = F_{k+1} + F_k$ and begins $F_1 = 1, F_2 = 1, F_3 = 2, F_4 = 3$. Find the largest integer $n$ such that $a_n = 2020$.
-/
theorem putnam_2020_a5
  (a : ℤ → ℕ)
  (ha : a = fun n : ℤ => {S : Finset ℕ | (∀ k ∈ S, k > 0) ∧ ∑ k : S, Nat.fib k = n}.ncard) :
  IsGreatest {n | a n = 2020} (((Nat.fib 4040) - 1) : ℤ ) := by
  subst a
  have htarget :
      ((Nat.fib 4040 : ℤ) - 1) = (((Nat.fib 4040) - 1 : ℕ) : ℤ) := by
    rw [Int.ofNat_sub (by
      exact Nat.succ_le_iff.mpr (Nat.fib_pos.mpr (by norm_num : (0 : ℕ) < 4040)))]
    norm_num
  constructor
  · rw [htarget]
    dsimp
    rw [Putnam2020A5.int_count_nat]
    simpa using Putnam2020A5.cnt_fib_sub_one 2020 (by norm_num)
  · intro n hn
    dsimp at hn
    by_cases hneg : n < 0
    · have htarget_nonneg : (0 : ℤ) ≤ (((Nat.fib 4040) - 1 : ℕ) : ℤ) := by exact_mod_cast Nat.zero_le _
      rw [htarget]
      omega
    · have hnnonneg : 0 ≤ n := le_of_not_gt hneg
      have hncast : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hnnonneg
      have hcnt : Putnam2020A5.cnt n.toNat = 2020 := by
        have hraw := hn
        rw [← hncast, Putnam2020A5.int_count_nat] at hraw
        exact hraw
      have hleNat : n.toNat ≤ Nat.fib (2 * 2020) - 1 :=
        Putnam2020A5.cnt_upper 2020 n.toNat hcnt
      have hidx : 2 * 2020 = 4040 := by norm_num
      rw [hidx] at hleNat
      have hleInt : ((n.toNat : ℕ) : ℤ) ≤ (((Nat.fib 4040) - 1 : ℕ) : ℤ) := by
        exact_mod_cast hleNat
      rw [htarget]
      calc
        n = ((n.toNat : ℕ) : ℤ) := hncast.symm
        _ ≤ (((Nat.fib 4040) - 1 : ℕ) : ℤ) := hleInt
