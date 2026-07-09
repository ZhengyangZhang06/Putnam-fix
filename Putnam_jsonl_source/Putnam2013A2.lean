import Mathlib

open Function Set
open scoped symmDiff

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
  InjOn f S := by
  classical
  have chain_of_adjacent :
      ∀ {a : List ℤ},
        (∀ i : Fin (a.length - 1), a[i] < a[i+(1:ℕ)]) →
        List.IsChain (fun x y : ℤ => x < y) a := by
    intro a h
    rw [List.isChain_iff_getElem]
    intro i hi
    have hi' : i < a.length - 1 := by omega
    simpa using h ⟨i, hi'⟩
  have getElem!_zero_eq_head! :
      ∀ {l : List ℤ}, l ≠ [] → l[0]! = l.head! := by
    intro l h
    cases l with
    | nil => contradiction
    | cons _ _ => rfl
  have getElem!_last_eq_getLast :
      ∀ {l : List ℤ} (h : l ≠ []), l[l.length - 1]! = l.getLast h := by
    intro l h
    have hidx : l.length - 1 < l.length := by
      cases l with
      | nil => contradiction
      | cons _ _ => simp
    rw [getElem!_pos l (l.length - 1) hidx]
    exact (List.getLast_eq_getElem h).symm
  have lt_of_mem_list :
      ∀ {n x : ℤ} {a : List ℤ},
        a.length > 0 → n < a[0]! →
        (∀ i : Fin (a.length - 1), a[i] < a[i+(1:ℕ)]) →
        x ∈ a → n < x := by
    intro n x a ha_len ha_first ha_adj hx
    have hane : a ≠ [] := List.length_pos_iff.mp ha_len
    have hchain := chain_of_adjacent (a := a) ha_adj
    have hsorted : a.SortedLT := List.sortedLT_iff_isChain.mpr hchain
    have hheadle : a.head! ≤ x := List.Pairwise.head!_le hsorted.sortedLE.pairwise hx
    have hnhead : n < a.head! := by
      simpa [getElem!_zero_eq_head! (l := a) hane] using ha_first
    exact lt_of_lt_of_le hnhead hheadle
  have mem_dropLast_lt_last :
      ∀ {x M : ℤ} {a : List ℤ},
        a.length > 0 →
        (∀ i : Fin (a.length - 1), a[i] < a[i+(1:ℕ)]) →
        a[a.length - 1]! = M → x ∈ a.dropLast → x < M := by
    intro x M a ha_len ha_adj ha_last hx
    have hane : a ≠ [] := List.length_pos_iff.mp ha_len
    have hchain := chain_of_adjacent (a := a) ha_adj
    have hsorted : a.SortedLT := List.sortedLT_iff_isChain.mpr hchain
    have hxlt : x < a.getLast hane := hsorted.pairwise.rel_dropLast_getLast hx
    have hlast : a.getLast hane = M := by
      simpa [getElem!_last_eq_getLast (l := a) hane] using ha_last
    simpa [hlast] using hxlt
  have prod_eq_dropLast_mul_getLast :
      ∀ {a : List ℤ} (h : a ≠ []), a.prod = a.dropLast.prod * a.getLast h := by
    intro a h
    conv_lhs => rw [← List.dropLast_append_getLast h]
    simp [List.prod_append]
  have sort_prod_eq_finset_prod :
      ∀ s : Finset ℤ, (s.sort (fun x y : ℤ => x ≤ y)).prod = ∏ x ∈ s, x := by
    intro s
    rw [← Finset.prod_toList s]
    exact (Finset.sort_perm_toList s (fun x y : ℤ => x ≤ y)).prod_eq
  have prod_mul_prod_eq_prod_symmDiff_mul_square :
      ∀ (s t : Finset ℤ) (g : ℤ → ℚ),
        (∏ x ∈ s, g x) * (∏ x ∈ t, g x) =
          (∏ x ∈ s ∆ t, g x) * (∏ x ∈ s ∩ t, g x) ^ 2 := by
    intro s t g
    have hdisj : Disjoint (s ∆ t) (s ∩ t) := by
      rw [Finset.disjoint_left]
      intro x hx hxi
      rw [Finset.mem_symmDiff] at hx
      simp only [Finset.mem_inter] at hxi
      rcases hx with ⟨_, hxt⟩ | ⟨_, hxs⟩
      · exact hxt hxi.2
      · exact hxs hxi.1
    have hunion : (s ∆ t) ∪ (s ∩ t) = s ∪ t := by
      ext x
      rw [Finset.mem_union, Finset.mem_union, Finset.mem_inter, Finset.mem_symmDiff]
      tauto
    calc
      (∏ x ∈ s, g x) * (∏ x ∈ t, g x)
          = (∏ x ∈ s ∪ t, g x) * (∏ x ∈ s ∩ t, g x) := by
              exact (Finset.prod_union_inter (s₁ := s) (s₂ := t) (f := g)).symm
      _ = ((∏ x ∈ s ∆ t, g x) * (∏ x ∈ s ∩ t, g x)) *
            (∏ x ∈ s ∩ t, g x) := by
              rw [← Finset.prod_union hdisj (f := g), hunion]
      _ = (∏ x ∈ s ∆ t, g x) * (∏ x ∈ s ∩ t, g x) ^ 2 := by
              rw [pow_two, mul_assoc]
  have isSquare_mul_prod_symmDiff_rat :
      ∀ (s t : Finset ℤ) (q : ℚ) (g : ℤ → ℚ),
        (∀ x ∈ s ∩ t, g x ≠ 0) →
        IsSquare (q * (∏ x ∈ s, g x) * (∏ x ∈ t, g x)) →
        IsSquare (q * (∏ x ∈ s ∆ t, g x)) := by
    intro s t q g hnz h
    let I : ℚ := ∏ x ∈ s ∩ t, g x
    have hI : I ≠ 0 := by
      dsimp [I]
      exact Finset.prod_ne_zero_iff.mpr hnz
    have hprod := prod_mul_prod_eq_prod_symmDiff_mul_square s t g
    have h' : IsSquare ((q * (∏ x ∈ s ∆ t, g x)) * I ^ 2) := by
      convert h using 1
      calc
        (q * (∏ x ∈ s ∆ t, g x)) * I ^ 2
            = q * ((∏ x ∈ s ∆ t, g x) * (∏ x ∈ s ∩ t, g x) ^ 2) := by
                dsimp [I]
                ring
        _ = q * ((∏ x ∈ s, g x) * (∏ x ∈ t, g x)) := by rw [← hprod]
        _ = q * (∏ x ∈ s, g x) * (∏ x ∈ t, g x) := by ring
    have hdiv := h'.div (IsSquare.sq I)
    convert hdiv using 1
    field_simp [hI]
  have isSquare_ratCast_of_exists_int_sq :
      ∀ {z : ℤ}, (∃ m : ℤ, m ^ 2 = z) → IsSquare (z : ℚ) := by
    intro z h
    rcases h with ⟨m, hm⟩
    refine ⟨(m : ℚ), ?_⟩
    rw [← hm]
    norm_num [pow_two]
  have exists_int_sq_of_isSquare_ratCast :
      ∀ {z : ℤ}, IsSquare (z : ℚ) → ∃ m : ℤ, m ^ 2 = z := by
    intro z h
    rcases (Rat.isSquare_intCast_iff.mp h) with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [hm, pow_two]
  have no_lt :
      ∀ {n m : ℤ}, n ∈ S → m ∈ S → n < m → f n = f m → False := by
    intro n m hn hm hnm hfm
    have hnS : n > 0 ∧ ¬∃ k : ℤ, k ^ 2 = n := by simpa [hS] using hn
    have hmS : m > 0 ∧ ¬∃ k : ℤ, k ^ 2 = m := by simpa [hS] using hm

    rcases (hf n hn).1 with ⟨ra, hraT, hfra⟩
    have hminn := (hf n hn).2
    have hraT' : ra ∈ {r : ℤ | ∃ a : List ℤ, P n a ∧ a[a.length - 1]! = r} := by
      simpa [hT] using hraT
    rcases hraT' with ⟨a, haP, haLast_ra⟩
    have haLast : a[a.length - 1]! = f n := haLast_ra.trans hfra.symm
    have haP' := (hP n a).mp haP
    rcases haP' with ⟨ha_len, ha_first, ha_sq, ha_adj⟩

    rcases (hf m hm).1 with ⟨rb, hrbT, hfrb⟩
    have hrbT' : rb ∈ {r : ℤ | ∃ b : List ℤ, P m b ∧ b[b.length - 1]! = r} := by
      simpa [hT] using hrbT
    rcases hrbT' with ⟨b, hbP, hbLast_rb⟩
    have hbLast_fm : b[b.length - 1]! = f m := hbLast_rb.trans hfrb.symm
    have hbLast : b[b.length - 1]! = f n := hbLast_fm.trans hfm.symm
    have hbP' := (hP m b).mp hbP
    rcases hbP' with ⟨hb_len, hb_first, hb_sq, hb_adj⟩

    have ha_ne : a ≠ [] := List.length_pos_iff.mp ha_len
    have hb_ne : b ≠ [] := List.length_pos_iff.mp hb_len
    have ha_getLast : a.getLast ha_ne = f n := by
      simpa [getElem!_last_eq_getLast (l := a) ha_ne] using haLast
    have hb_getLast : b.getLast hb_ne = f n := by
      simpa [getElem!_last_eq_getLast (l := b) hb_ne] using hbLast
    have hM_gt_m : m < f n := by
      have hmem : b.getLast hb_ne ∈ b := List.getLast_mem hb_ne
      have hlt := lt_of_mem_list hb_len hb_first hb_adj hmem
      simpa [hb_getLast] using hlt
    have hMpos : 0 < f n := lt_trans hmS.1 hM_gt_m
    have hMneQ : (f n : ℚ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hMpos)

    have ha_chain := chain_of_adjacent (a := a) ha_adj
    have hb_chain := chain_of_adjacent (a := b) hb_adj
    have ha_sorted : a.SortedLT := List.sortedLT_iff_isChain.mpr ha_chain
    have hb_sorted : b.SortedLT := List.sortedLT_iff_isChain.mpr hb_chain
    have ha_drop_nodup : a.dropLast.Nodup :=
      List.Nodup.sublist (List.dropLast_sublist a) ha_sorted.nodup
    have hb_drop_nodup : b.dropLast.Nodup :=
      List.Nodup.sublist (List.dropLast_sublist b) hb_sorted.nodup

    let A : Finset ℤ := a.dropLast.toFinset
    let B : Finset ℤ := b.dropLast.toFinset
    let D : Finset ℤ := ({m} : Finset ℤ) ∆ A
    let C : Finset ℤ := D ∆ B

    have hAprod : (∏ x ∈ A, x) = a.dropLast.prod := by
      dsimp [A]
      simpa using (List.prod_toFinset (f := id) ha_drop_nodup)
    have hBprod : (∏ x ∈ B, x) = b.dropLast.prod := by
      dsimp [B]
      simpa using (List.prod_toFinset (f := id) hb_drop_nodup)
    have hAprodQ : (∏ x ∈ A, (x : ℚ)) = (a.dropLast.prod : ℚ) := by
      rw [← hAprod]
      norm_num
    have hBprodQ : (∏ x ∈ B, (x : ℚ)) = (b.dropLast.prod : ℚ) := by
      rw [← hBprod]
      norm_num

    have hA_gt_n : ∀ x ∈ A, n < x := by
      intro x hx
      have hxdl : x ∈ a.dropLast := by simpa [A] using hx
      exact lt_of_mem_list ha_len ha_first ha_adj (List.mem_of_mem_dropLast hxdl)
    have hA_lt_M : ∀ x ∈ A, x < f n := by
      intro x hx
      have hxdl : x ∈ a.dropLast := by simpa [A] using hx
      exact mem_dropLast_lt_last ha_len ha_adj haLast hxdl
    have hB_gt_n : ∀ x ∈ B, n < x := by
      intro x hx
      have hxdl : x ∈ b.dropLast := by simpa [B] using hx
      have hmx := lt_of_mem_list hb_len hb_first hb_adj
        (List.mem_of_mem_dropLast hxdl)
      exact lt_trans hnm hmx
    have hB_gt_m : ∀ x ∈ B, m < x := by
      intro x hx
      have hxdl : x ∈ b.dropLast := by simpa [B] using hx
      exact lt_of_mem_list hb_len hb_first hb_adj (List.mem_of_mem_dropLast hxdl)
    have hB_lt_M : ∀ x ∈ B, x < f n := by
      intro x hx
      have hxdl : x ∈ b.dropLast := by simpa [B] using hx
      exact mem_dropLast_lt_last hb_len hb_adj hbLast hxdl
    have hD_gt_n : ∀ x ∈ D, n < x := by
      intro x hx
      change x ∈ ({m} : Finset ℤ) ∆ A at hx
      rw [Finset.mem_symmDiff] at hx
      rcases hx with ⟨hxm, _⟩ | ⟨hxA, _⟩
      · have hxeq : x = m := by simpa using hxm
        simpa [hxeq] using hnm
      · exact hA_gt_n x hxA
    have hD_lt_M : ∀ x ∈ D, x < f n := by
      intro x hx
      change x ∈ ({m} : Finset ℤ) ∆ A at hx
      rw [Finset.mem_symmDiff] at hx
      rcases hx with ⟨hxm, _⟩ | ⟨hxA, _⟩
      · have hxeq : x = m := by simpa using hxm
        simpa [hxeq] using hM_gt_m
      · exact hA_lt_M x hxA
    have hC_gt_n : ∀ x ∈ C, n < x := by
      intro x hx
      change x ∈ D ∆ B at hx
      rw [Finset.mem_symmDiff] at hx
      rcases hx with ⟨hxD, _⟩ | ⟨hxB, _⟩
      · exact hD_gt_n x hxD
      · exact hB_gt_n x hxB
    have hC_lt_M : ∀ x ∈ C, x < f n := by
      intro x hx
      change x ∈ D ∆ B at hx
      rw [Finset.mem_symmDiff] at hx
      rcases hx with ⟨hxD, _⟩ | ⟨hxB, _⟩
      · exact hD_lt_M x hxD
      · exact hB_lt_M x hxB

    have ha_prod : a.prod = a.dropLast.prod * f n := by
      rw [prod_eq_dropLast_mul_getLast ha_ne, ha_getLast]
    have hb_prod : b.prod = b.dropLast.prod * f n := by
      rw [prod_eq_dropLast_mul_getLast hb_ne, hb_getLast]
    have hsqa : IsSquare ((n * a.prod : ℤ) : ℚ) :=
      isSquare_ratCast_of_exists_int_sq ha_sq
    have hsqb : IsSquare ((m * b.prod : ℤ) : ℚ) :=
      isSquare_ratCast_of_exists_int_sq hb_sq
    have hrawDrop :
        IsSquare ((n : ℚ) * (m : ℚ) * (a.dropLast.prod : ℚ) * (b.dropLast.prod : ℚ)) := by
      have hdiv := (hsqa.mul hsqb).div (IsSquare.sq (f n : ℚ))
      convert hdiv using 1
      rw [ha_prod, hb_prod]
      norm_num [Int.cast_mul]
      field_simp [hMneQ]
    have hraw :
        IsSquare ((n : ℚ) * (m : ℚ) *
          (∏ x ∈ A, (x : ℚ)) * (∏ x ∈ B, (x : ℚ))) := by
      convert hrawDrop using 1
      rw [hAprodQ, hBprodQ]

    have hfirstInput :
        IsSquare (((n : ℚ) * (∏ x ∈ B, (x : ℚ))) *
          (∏ x ∈ ({m} : Finset ℤ), (x : ℚ)) * (∏ x ∈ A, (x : ℚ))) := by
      convert hraw using 1
      simp
      ring
    have hnz_first : ∀ x ∈ ({m} : Finset ℤ) ∩ A, (x : ℚ) ≠ 0 := by
      intro x hx
      have hxm : x = m := by
        have : x ∈ ({m} : Finset ℤ) := (Finset.mem_inter.mp hx).1
        simpa using this
      have hxpos : 0 < x := by simpa [hxm] using hmS.1
      exact_mod_cast (ne_of_gt hxpos)
    have hDsq :
        IsSquare (((n : ℚ) * (∏ x ∈ B, (x : ℚ))) *
          (∏ x ∈ D, (x : ℚ))) := by
      simpa [D] using
        isSquare_mul_prod_symmDiff_rat
          (({m} : Finset ℤ)) A ((n : ℚ) * (∏ x ∈ B, (x : ℚ)))
          (fun x : ℤ => (x : ℚ)) hnz_first hfirstInput
    have hsecondInput :
        IsSquare ((n : ℚ) * (∏ x ∈ D, (x : ℚ)) * (∏ x ∈ B, (x : ℚ))) := by
      convert hDsq using 1
      ring
    have hnz_second : ∀ x ∈ D ∩ B, (x : ℚ) ≠ 0 := by
      intro x hx
      have hxB : x ∈ B := (Finset.mem_inter.mp hx).2
      have hxpos : 0 < x := lt_trans hnS.1 (hB_gt_n x hxB)
      exact_mod_cast (ne_of_gt hxpos)
    have hCsqRat : IsSquare ((n : ℚ) * (∏ x ∈ C, (x : ℚ))) := by
      simpa [C] using
        isSquare_mul_prod_symmDiff_rat
          D B (n : ℚ) (fun x : ℤ => (x : ℚ)) hnz_second hsecondInput
    have hCsqRatInt : IsSquare ((n * (∏ x ∈ C, x) : ℤ) : ℚ) := by
      convert hCsqRat using 1
      norm_num [Int.cast_mul]
    have hCsq : ∃ u : ℤ, u ^ 2 = n * (∏ x ∈ C, x) :=
      exists_int_sq_of_isSquare_ratCast hCsqRatInt
    have hCnonempty : C.Nonempty := by
      by_contra hCempty
      have hCeq : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hCempty
      rcases hCsq with ⟨u, hu⟩
      have : u ^ 2 = n := by simpa [hCeq] using hu
      exact hnS.2 ⟨u, this⟩

    let w : List ℤ := C.sort (fun x y : ℤ => x ≤ y)
    have hw_len : w.length > 0 := by
      dsimp [w]
      rw [Finset.length_sort]
      exact Finset.card_pos.mpr hCnonempty
    have hw_first : n < w[0]! := by
      have hidx : 0 < w.length := hw_len
      have hmemC : w[0]! ∈ C := by
        rw [getElem!_pos w 0 hidx]
        exact (Finset.mem_sort (s := C) (fun x y : ℤ => x ≤ y)).1
          (List.getElem_mem hidx)
      exact hC_gt_n _ hmemC
    have hw_sq : ∃ u : ℤ, u ^ 2 = n * w.prod := by
      rcases hCsq with ⟨u, hu⟩
      refine ⟨u, ?_⟩
      simpa [w, sort_prod_eq_finset_prod C] using hu
    have hw_adj : ∀ i : Fin (w.length - 1), w[i] < w[i+(1:ℕ)] := by
      have hwChain : List.IsChain (fun x y : ℤ => x < y) w :=
        List.sortedLT_iff_isChain.mp (by
          dsimp [w]
          exact Finset.sortedLT_sort C)
      intro i
      have hi : (i : ℕ) + 1 < w.length := by omega
      simpa using hwChain.getElem (i : ℕ) hi
    have hwP : P n w := by
      rw [hP]
      exact ⟨hw_len, hw_first, hw_sq, hw_adj⟩
    have hw_last_lt : w[w.length - 1]! < f n := by
      have hidx : w.length - 1 < w.length := by omega
      have hmemC : w[w.length - 1]! ∈ C := by
        rw [getElem!_pos w (w.length - 1) hidx]
        exact (Finset.mem_sort (s := C) (fun x y : ℤ => x ≤ y)).1
          (List.getElem_mem hidx)
      exact hC_lt_M _ hmemC
    have hwT : w[w.length - 1]! ∈ T n := by
      rw [hT]
      exact ⟨w, hwP, rfl⟩
    have hle := hminn (w[w.length - 1]!) hwT
    exact not_lt_of_ge hle hw_last_lt

  intro n hn m hm hfm
  by_cases hnm : n = m
  · exact hnm
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · exact False.elim (no_lt hn hm hlt hfm)
  · exact False.elim (no_lt hm hn hgt hfm.symm)
