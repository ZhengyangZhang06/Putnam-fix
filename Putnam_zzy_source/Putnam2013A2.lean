import Mathlib

open Function Set

/--
Let $S$ be the set of all positive integers that are \emph{not} perfect squares. For $n$ in $S$, consider choices of integers
$a_1, a_2, \dots, a_r$ such that $n < a_1<  a_2 < \cdots < a_r$
and $n \cdot a_1 \cdot a_2 \cdots a_r$ is a perfect square, and
let $f(n)$ be the minumum of $a_r$ over all such choices. For example,
$2 \cdot 3 \cdot 6$ is a perfect square, while $2 \cdot 3$, $2 \cdot 4$,
$2 \cdot 5$, $2 \cdot 3 \cdot 4$, $2 \cdot 3 \cdot 5$, $2 \cdot 4 \cdot 5$, and $2 \cdot 3 \cdot 4 \cdot 5$ are not, and so $f(2) = 6$.
Show that the function $f$ from $S$ to the integers is one-to-one.
-/
theorem putnam_2013_a2
  (S : Set ℤ)
  (hS : S = {n : ℤ | n > 0 ∧ ¬∃ m : ℤ, m ^ 2 = n})
  (P : ℤ → List ℤ → Prop)
  (hP : ∀ n a, P n a ↔
    a.length > 0 ∧ n < a[0]! ∧
    (∃ m : ℤ, m ^ 2 = n * a.prod) ∧
    (∀ i : Fin (a.length - 1), a[i] < a[i+(1:ℕ)]))
  (T : ℤ → Set ℤ)
  (hT : T = fun n : ℤ => {m : ℤ | ∃ a : List ℤ, P n a ∧ a[a.length - 1]! = m})
  (f : ℤ → ℤ)
  (hf : ∀ n ∈ S, ((∃ r ∈ T n, f n = r) ∧ ∀ r ∈ T n, f n ≤ r)) :
  InjOn f S :=
by
  classical
  have sortedLT_of_adjacent :
      ∀ {l : List ℤ},
        (∀ i : Fin (l.length - 1), l[i] < l[i+(1:ℕ)]) → l.SortedLT := by
    intro l h
    rw [List.sortedLT_iff_isChain]
    rw [List.isChain_iff_getElem]
    intro i hi
    have hi' : i < l.length - 1 := by omega
    simpa using h ⟨i, hi'⟩
  have mem_gt_of_sorted :
      ∀ {x z : ℤ} {l : List ℤ}, l.SortedLT → 0 < l.length →
        x < l[0]! → z ∈ l → x < z := by
    intro x z l hl hlen h0 hz
    rcases List.mem_iff_get.mp hz with ⟨i, rfl⟩
    let i0 : Fin l.length := ⟨0, hlen⟩
    have h00 : i0 ≤ i := by exact Nat.zero_le i
    have hle : l[i0] ≤ l[i] := hl.sortedLE.monotone_get h00
    have hget : l[i0] = l[0]! := by
      rw [getElem!_pos]
      rfl
    exact lt_of_lt_of_le (by simpa [hget] using h0) hle
  have mem_le_last_of_sorted :
      ∀ {z : ℤ} {l : List ℤ}, l.SortedLT → 0 < l.length → z ∈ l →
        z ≤ l[l.length - 1]! := by
    intro z l hl hlen hz
    rcases List.mem_iff_get.mp hz with ⟨i, rfl⟩
    let ilast : Fin l.length := ⟨l.length - 1, by omega⟩
    have hleidx : i ≤ ilast := by
      change (i : ℕ) ≤ l.length - 1
      omega
    have hle : l[i] ≤ l[ilast] := hl.sortedLE.monotone_get hleidx
    have hget : l[ilast] = l[l.length - 1]! := by
      rw [getElem!_pos]
      rfl
    simpa [hget] using hle
  have sort_prod : ∀ s : Finset ℤ, (s.sort).prod = ∏ z ∈ s, z := by
    intro s
    have h := List.prod_toFinset (f := fun z : ℤ => z)
      (s.sort_nodup (fun a b : ℤ => a ≤ b))
    simpa using h.symm
  have finset_prod_symmDiff_mul_inter_sq :
      ∀ s t : Finset ℤ,
        (∏ z ∈ symmDiff s t, (z : ℚ)) *
            (∏ z ∈ s ∩ t, (z : ℚ)) ^ 2 =
          (∏ z ∈ s, (z : ℚ)) * (∏ z ∈ t, (z : ℚ)) := by
    intro s t
    have hdisj : Disjoint (symmDiff s t) (s ∩ t) := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      ext z
      simp [Finset.mem_symmDiff]
      tauto
    have hunion : (symmDiff s t) ∪ (s ∩ t) = s ∪ t := by
      ext z
      simp [Finset.mem_symmDiff]
      tauto
    calc
      (∏ z ∈ symmDiff s t, (z : ℚ)) *
            (∏ z ∈ s ∩ t, (z : ℚ)) ^ 2
          = ((∏ z ∈ symmDiff s t, (z : ℚ)) *
                (∏ z ∈ s ∩ t, (z : ℚ))) *
              (∏ z ∈ s ∩ t, (z : ℚ)) := by ring
      _ = (∏ z ∈ (symmDiff s t) ∪ (s ∩ t), (z : ℚ)) *
              (∏ z ∈ s ∩ t, (z : ℚ)) := by rw [Finset.prod_union hdisj]
      _ = (∏ z ∈ s ∪ t, (z : ℚ)) * (∏ z ∈ s ∩ t, (z : ℚ)) := by rw [hunion]
      _ = (∏ z ∈ s, (z : ℚ)) * (∏ z ∈ t, (z : ℚ)) := by
        rw [Finset.prod_union_inter]
  have no_lt :
      ∀ {n k : ℤ}, n ∈ S → k ∈ S → f n = f k → ¬ n < k := by
    intro n k hnS hkS hfk hnk
    have hnS' : n > 0 ∧ ¬∃ m : ℤ, m ^ 2 = n := by
      simpa [hS] using hnS
    have hnpos : 0 < n := hnS'.1
    have hn_not_square : ¬∃ m : ℤ, m ^ 2 = n := hnS'.2
    rcases (hf n hnS).1 with ⟨rn, hrnT, hfrn⟩
    rcases (hf k hkS).1 with ⟨rk, hrkT, hfrk⟩
    have hrnT' : rn ∈ {m : ℤ | ∃ a : List ℤ, P n a ∧ a[a.length - 1]! = m} := by
      simpa [hT] using hrnT
    have hrkT' : rk ∈ {m : ℤ | ∃ a : List ℤ, P k a ∧ a[a.length - 1]! = m} := by
      simpa [hT] using hrkT
    rcases hrnT' with ⟨A, hPA, hAlast_rn⟩
    rcases hrkT' with ⟨B, hPB, hBlast_rk⟩
    have hAlast : A[A.length - 1]! = f n := by
      simpa [hfrn] using hAlast_rn
    have hBlast : B[B.length - 1]! = f n := by
      calc
        B[B.length - 1]! = rk := hBlast_rk
        _ = f k := hfrk.symm
        _ = f n := hfk.symm
    rcases (hP n A).mp hPA with
      ⟨hAlen, hn_lt_A0, ⟨u, hu⟩, hAadj⟩
    rcases (hP k B).mp hPB with
      ⟨hBlen, hk_lt_B0, ⟨v, hv⟩, hBadj⟩
    have hAsorted : A.SortedLT := sortedLT_of_adjacent hAadj
    have hBsorted : B.SortedLT := sortedLT_of_adjacent hBadj
    let Aset : Finset ℤ := A.toFinset
    let Bset : Finset ℤ := B.toFinset
    have hAprod : A.prod = ∏ z ∈ Aset, z := by
      have h := List.prod_toFinset (f := fun z : ℤ => z) hAsorted.nodup
      simpa [Aset] using h.symm
    have hBprod : B.prod = ∏ z ∈ Bset, z := by
      have h := List.prod_toFinset (f := fun z : ℤ => z) hBsorted.nodup
      simpa [Bset] using h.symm
    have hk_not_mem_B : k ∉ Bset := by
      intro hkB
      have hkB' : k ∈ B := by simpa [Bset] using hkB
      have : k < k :=
        mem_gt_of_sorted hBsorted hBlen hk_lt_B0 hkB'
      exact (lt_irrefl k) this
    let Cset : Finset ℤ := insert k Bset
    let Dset : Finset ℤ := symmDiff Aset Cset
    let L : List ℤ := Dset.sort
    have hM_mem_A : f n ∈ Aset := by
      have hlast_mem : A[A.length - 1]! ∈ A := by
        rw [getElem!_pos]
        exact List.getElem_mem (by omega)
      simpa [Aset, hAlast] using hlast_mem
    have hM_mem_B : f n ∈ Bset := by
      have hlast_mem : B[B.length - 1]! ∈ B := by
        rw [getElem!_pos]
        exact List.getElem_mem (by omega)
      simpa [Bset, hBlast] using hlast_mem
    have hM_mem_C : f n ∈ Cset := by
      exact Finset.mem_insert_of_mem hM_mem_B
    have hM_not_mem_D : f n ∉ Dset := by
      simp [Dset, Finset.mem_symmDiff, hM_mem_A, hM_mem_C]
    have hk_lt_M : k < f n := by
      have hfirst_mem : B[0]! ∈ B := by
        rw [getElem!_pos]
        exact List.getElem_mem hBlen
      have hfirst_le_last :=
        mem_le_last_of_sorted hBsorted hBlen hfirst_mem
      exact lt_of_lt_of_le hk_lt_B0 (by simpa [hBlast] using hfirst_le_last)
    have hD_gt : ∀ z ∈ Dset, n < z := by
      intro z hzD
      have hzU : z ∈ Aset ∪ Cset := Finset.symmDiff_subset_union hzD
      rcases (Finset.mem_union.mp hzU) with hzA | hzC
      · have hzA' : z ∈ A := by simpa [Aset] using hzA
        exact mem_gt_of_sorted hAsorted hAlen hn_lt_A0 hzA'
      · rw [Finset.mem_insert] at hzC
        rcases hzC with rfl | hzB
        · exact hnk
        · have hzB' : z ∈ B := by simpa [Bset] using hzB
          exact lt_trans hnk
            (mem_gt_of_sorted hBsorted hBlen hk_lt_B0 hzB')
    have hD_lt : ∀ z ∈ Dset, z < f n := by
      intro z hzD
      have hzU : z ∈ Aset ∪ Cset := Finset.symmDiff_subset_union hzD
      have hz_ne_M : z ≠ f n := by
        intro hz
        exact hM_not_mem_D (hz ▸ hzD)
      rcases (Finset.mem_union.mp hzU) with hzA | hzC
      · have hzA' : z ∈ A := by simpa [Aset] using hzA
        have hzle :=
          mem_le_last_of_sorted hAsorted hAlen hzA'
        exact lt_of_le_of_ne (by simpa [hAlast] using hzle) hz_ne_M
      · rw [Finset.mem_insert] at hzC
        rcases hzC with rfl | hzB
        · exact hk_lt_M
        · have hzB' : z ∈ B := by simpa [Bset] using hzB
          have hzle :=
            mem_le_last_of_sorted hBsorted hBlen hzB'
          exact lt_of_le_of_ne (by simpa [hBlast] using hzle) hz_ne_M
    have hCprodQ : (∏ z ∈ Cset, (z : ℚ)) =
        (k : ℚ) * ∏ z ∈ Bset, (z : ℚ) := by
      simp [Cset, Finset.prod_insert, hk_not_mem_B]
    have hsq_nA : IsSquare ((n : ℚ) * ∏ z ∈ Aset, (z : ℚ)) := by
      rw [isSquare_iff_exists_sq]
      use (u : ℚ)
      have hAprodQ : ((A.prod : ℤ) : ℚ) = ∏ z ∈ Aset, (z : ℚ) := by
        simp [hAprod]
      rw [← hAprodQ, ← Int.cast_mul, ← hu, Int.cast_pow]
    have hsq_C : IsSquare (∏ z ∈ Cset, (z : ℚ)) := by
      rw [isSquare_iff_exists_sq]
      use (v : ℚ)
      rw [hCprodQ]
      have hBprodQ : ((B.prod : ℤ) : ℚ) = ∏ z ∈ Bset, (z : ℚ) := by
        simp [hBprod]
      rw [← hBprodQ, ← Int.cast_mul, ← hv, Int.cast_pow]
    have hIne : (∏ z ∈ Aset ∩ Cset, (z : ℚ)) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr ?_
      intro z hz
      have hzA : z ∈ A := by
        have hzAset : z ∈ Aset := (Finset.mem_inter.mp hz).1
        simpa [Aset] using hzAset
      have hnz : 0 < z :=
        lt_trans hnpos
          (mem_gt_of_sorted hAsorted hAlen hn_lt_A0 hzA)
      exact_mod_cast (ne_of_gt hnz)
    have hsq_nD : IsSquare ((n : ℚ) * ∏ z ∈ Dset, (z : ℚ)) := by
      set I : ℚ := ∏ z ∈ Aset ∩ Cset, (z : ℚ)
      set Dp : ℚ := ∏ z ∈ Dset, (z : ℚ)
      set Ap : ℚ := ∏ z ∈ Aset, (z : ℚ)
      set Cp : ℚ := ∏ z ∈ Cset, (z : ℚ)
      have hprod : Dp * I ^ 2 = Ap * Cp := by
        simpa [I, Dp, Ap, Cp, Dset] using
          finset_prod_symmDiff_mul_inter_sq Aset Cset
      have hI : I ≠ 0 := by simpa [I] using hIne
      have hsq_right : IsSquare (((n : ℚ) * Ap) * Cp) := by
        have hsq_nA' : IsSquare ((n : ℚ) * Ap) := by
          simpa [Ap] using hsq_nA
        have hsq_C' : IsSquare Cp := by
          simpa [Cp] using hsq_C
        exact hsq_nA'.mul hsq_C'
      have heq : (n : ℚ) * Dp = (((n : ℚ) * Ap) * Cp) * (I ^ 2)⁻¹ := by
        field_simp [hI]
        ring_nf at hprod ⊢
        rw [hprod]
      have hsq_inv : IsSquare ((I ^ 2)⁻¹) := (IsSquare.sq I).inv
      have hsq_expr : IsSquare ((((n : ℚ) * Ap) * Cp) * (I ^ 2)⁻¹) :=
        hsq_right.mul hsq_inv
      simpa [Dp, heq] using hsq_expr
    have hLprod : L.prod = ∏ z ∈ Dset, z := by
      simpa [L] using sort_prod Dset
    have hsq_L_int : IsSquare (n * L.prod) := by
      apply Rat.isSquare_intCast_iff.mp
      have hcast : ((n * L.prod : ℤ) : ℚ) =
          (n : ℚ) * ∏ z ∈ Dset, (z : ℚ) := by
        have hLprodQ : ((L.prod : ℤ) : ℚ) = ∏ z ∈ Dset, (z : ℚ) := by
          simp [hLprod]
        rw [Int.cast_mul, hLprodQ]
      simpa [hcast] using hsq_nD
    have hDnonempty : Dset.Nonempty := by
      by_contra hDempty'
      have hDempty : Dset = ∅ := Finset.not_nonempty_iff_eq_empty.mp hDempty'
      have hLnil : L = [] := by simp [L, hDempty]
      have hsq_n : IsSquare n := by
        simpa [hLnil] using hsq_L_int
      rcases (isSquare_iff_exists_sq n).mp hsq_n with ⟨w, hw⟩
      exact hn_not_square ⟨w, hw.symm⟩
    have hLlen : L.length > 0 := by
      simpa [L] using hDnonempty.card_pos
    have hL0 : n < L[0]! := by
      have hfirst_mem : L[0]! ∈ L := by
        rw [getElem!_pos]
        exact List.getElem_mem hLlen
      have hfirst_mem_D : L[0]! ∈ Dset := by
        simpa [L] using hfirst_mem
      exact hD_gt _ hfirst_mem_D
    have hLsq : ∃ m : ℤ, m ^ 2 = n * L.prod := by
      rcases (isSquare_iff_exists_sq (n * L.prod)).mp hsq_L_int with ⟨w, hw⟩
      exact ⟨w, hw.symm⟩
    have hLadj : ∀ i : Fin (L.length - 1), L[i] < L[i+(1:ℕ)] := by
      have hsorted : L.SortedLT := by
        simpa [L] using Finset.sortedLT_sort Dset
      intro i
      have hchain : List.IsChain (· < ·) L :=
        List.sortedLT_iff_isChain.mp hsorted
      rw [List.isChain_iff_getElem] at hchain
      have hi : (i : ℕ) + 1 < L.length := by omega
      simpa using hchain (i : ℕ) hi
    have hPL : P n L := by
      exact (hP n L).mpr ⟨hLlen, hL0, hLsq, hLadj⟩
    let r : ℤ := L[L.length - 1]!
    have hrT : r ∈ T n := by
      rw [hT]
      exact ⟨L, hPL, rfl⟩
    have hr_lt : r < f n := by
      have hlast_mem : r ∈ L := by
        change L[L.length - 1]! ∈ L
        rw [getElem!_pos]
        exact List.getElem_mem (by omega)
      have hlast_mem_D : r ∈ Dset := by
        simpa [L, r] using hlast_mem
      exact hD_lt _ hlast_mem_D
    exact not_lt_of_ge ((hf n hnS).2 r hrT) hr_lt
  intro x hx y hy hxy
  have hxy_le : x ≤ y := le_of_not_gt (no_lt hy hx hxy.symm)
  have hyx_le : y ≤ x := le_of_not_gt (no_lt hx hy hxy)
  exact le_antisymm hxy_le hyx_le
