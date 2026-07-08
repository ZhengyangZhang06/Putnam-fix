import Mathlib

open Topology Filter Real Function Nat

open scoped BigOperators

namespace Putnam2017B6

noncomputable abbrev answer : ℕ :=
  Nat.descFactorial 2016 63 - 2016 * (63!)

def goodCount (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => p
  | n + 2 => p.descFactorial (n + 1) - (n + 1) * goodCount p (n + 1)

noncomputable def weightedCard (p n : ℕ) [Fintype (ZMod p)] (a : Fin n → ℕ) : ℕ :=
  Fintype.card
    {x : Fin n → ZMod p //
      Injective x ∧ (∑ i : Fin n, (a i : ZMod p) * x i) = 0}

def mergeCoeff {n : ℕ} (a : Fin (n + 1) → ℕ) (j : Fin n) : Fin n → ℕ :=
  fun i => a i.castSucc + if i = j then a (Fin.last n) else 0

lemma sum_mergeCoeff {n : ℕ} (a : Fin (n + 1) → ℕ) (j : Fin n) :
    (∑ i : Fin n, mergeCoeff a j i) =
      (∑ i : Fin n, a i.castSucc) + a (Fin.last n) := by
  classical
  simp [mergeCoeff, Finset.sum_add_distrib]

lemma mergeCoeff_pos {n : ℕ} {a : Fin (n + 1) → ℕ}
    (ha : ∀ i, 0 < a i) (j i : Fin n) : 0 < mergeCoeff a j i := by
  exact lt_of_lt_of_le (ha i.castSucc) (Nat.le_add_right _ _)

lemma mergeCoeff_sum {p n : ℕ} {a : Fin (n + 1) → ℕ}
    (ha_sum : (∑ i : Fin (n + 1), a i) = p) (j : Fin n) :
    (∑ i : Fin n, mergeCoeff a j i) = p := by
  rw [sum_mergeCoeff, ← Fin.sum_univ_castSucc, ha_sum]

lemma zmod_natCast_ne_zero_of_pos_lt {p k : ℕ} [Fact p.Prime]
    (hk0 : 0 < k) (hkp : k < p) : (k : ZMod p) ≠ 0 := by
  intro h
  exact Nat.not_dvd_of_pos_of_lt hk0 hkp
    ((CharP.cast_eq_zero_iff (ZMod p) p k).mp h)

lemma lastCoeff_ne_zero {p n : ℕ} [Fact p.Prime] {a : Fin (n + 2) → ℕ}
    (ha_pos : ∀ i, 0 < a i) (ha_sum : (∑ i : Fin (n + 2), a i) = p) :
    (a (Fin.last (n + 1)) : ZMod p) ≠ 0 := by
  apply zmod_natCast_ne_zero_of_pos_lt (ha_pos _)
  have hother : 0 < ∑ i : Fin (n + 1), a i.castSucc := by
    exact Finset.sum_pos (fun i _ => ha_pos i.castSucc) (Finset.univ_nonempty)
  have hsplit := ha_sum
  rw [Fin.sum_univ_castSucc] at hsplit
  omega

lemma weighted_sum_snoc {p n : ℕ} [Fact p.Prime] (a : Fin (n + 1) → ℕ)
    (y : Fin n → ZMod p) (z : ZMod p) :
    (∑ i : Fin (n + 1), (a i : ZMod p) *
      ((Fin.snoc y z : Fin (n + 1) → ZMod p) i)) =
      (∑ i : Fin n, (a i.castSucc : ZMod p) * y i) +
        (a (Fin.last n) : ZMod p) * z := by
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

lemma weighted_sum_merge {p n : ℕ} [Fact p.Prime] (a : Fin (n + 1) → ℕ)
    (j : Fin n) (y : Fin n → ZMod p) :
    (∑ i : Fin n, (mergeCoeff a j i : ZMod p) * y i) =
      (∑ i : Fin n, (a i.castSucc : ZMod p) * y i) +
        (a (Fin.last n) : ZMod p) * y j := by
  classical
  simp [mergeCoeff, Nat.cast_add, add_mul, Finset.sum_add_distrib, Finset.sum_ite_eq']

lemma weightedCard_one {p : ℕ} [Fact p.Prime] {a : Fin 1 → ℕ}
    (ha_sum : (∑ i : Fin 1, a i) = p) :
    weightedCard p 1 a = p := by
  classical
  have hcoeff : (a 0 : ZMod p) = 0 := by
    have h0 : a 0 = p := by simpa using ha_sum
    rw [h0]
    exact CharP.cast_eq_zero (ZMod p) p
  unfold weightedCard
  trans Fintype.card {x : Fin 1 → ZMod p // Injective x}
  · apply Fintype.card_congr
    refine Equiv.subtypeEquivRight ?_
    intro x
    simp [hcoeff]
  · rw [Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding (Fin 1) (ZMod p))]
    simp [ZMod.card]

lemma weightedCard_eq_goodCount {p n : ℕ} [Fact p.Prime] (a : Fin n → ℕ)
    (ha_pos : ∀ i, 0 < a i) (ha_sum : (∑ i : Fin n, a i) = p) :
    weightedCard p n a = goodCount p n := by
  classical
  induction n with
  | zero =>
      have hp0 : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
      simp at ha_sum
      exact (hp0 ha_sum.symm).elim
  | succ n ih =>
      cases n with
      | zero =>
          simpa [goodCount] using weightedCard_one (p := p) (a := a) ha_sum
      | succ n =>
          let last : ZMod p := (a (Fin.last (n + 1)) : ZMod p)
          let initSum : (Fin (n + 1) → ZMod p) → ZMod p :=
            fun y => ∑ i : Fin (n + 1), (a i.castSucc : ZMod p) * y i
          let sol : (Fin (n + 1) → ZMod p) → ZMod p :=
            fun y => - last⁻¹ * initSum y
          have hlast_ne : last ≠ 0 := by
            simpa [last] using lastCoeff_ne_zero (p := p) (n := n) (a := a) ha_pos ha_sum
          have hlinear (y : Fin (n + 1) → ZMod p) (z : ZMod p) :
              initSum y + last * z = 0 ↔ z = sol y := by
            constructor
            · intro h
              have h' : last * z = - initSum y :=
                eq_neg_of_add_eq_zero_right h
              calc
                z = last⁻¹ * (last * z) := by
                  rw [← mul_assoc, inv_mul_cancel₀ hlast_ne, one_mul]
                _ = last⁻¹ * (- initSum y) := by rw [h']
                _ = sol y := by
                  simp only [sol]
                  ring
            · intro hz
              rw [hz]
              change initSum y + last * (-last⁻¹ * initSum y) = 0
              calc
                initSum y + last * (-last⁻¹ * initSum y)
                    = initSum y + (-(last * last⁻¹)) * initSum y := by ring
                _ = initSum y + (-1) * initSum y := by
                  rw [mul_inv_cancel₀ hlast_ne]
                _ = 0 := by ring
          have hsolve (y : Fin (n + 1) → ZMod p) (z : ZMod p) :
              (∑ i : Fin (n + 2), (a i : ZMod p) *
                ((Fin.snoc y z : Fin (n + 2) → ZMod p) i)) = 0 ↔
                z = sol y := by
            rw [weighted_sum_snoc]
            change initSum y + last * z = 0 ↔ z = sol y
            exact hlinear y z
          have hfull :
              weightedCard p (n + 2) a =
                Fintype.card
                  {y : Fin (n + 1) → ZMod p //
                    Injective y ∧ sol y ∉ Set.range y} := by
            unfold weightedCard
            apply Fintype.card_congr
            refine
              { toFun := ?toFun
                invFun := ?invFun
                left_inv := ?left
                right_inv := ?right }
            · intro x
              refine ⟨Fin.init x.1, ?_⟩
              have hxinj := x.2.1
              have hsum := x.2.2
              have hsnoc : x.1 = Fin.snoc (Fin.init x.1) (x.1 (Fin.last (n + 1))) := by
                exact (Fin.snoc_init_self x.1).symm
              have hinj_init : Injective (Fin.init x.1) := by
                intro i j hij
                apply Fin.castSucc_injective (n + 1)
                apply hxinj
                simpa [Fin.init] using hij
              have hnot : sol (Fin.init x.1) ∉ Set.range (Fin.init x.1) := by
                intro hmem
                rcases hmem with ⟨j, hj⟩
                have hz : x.1 (Fin.last (n + 1)) = sol (Fin.init x.1) := by
                  have hzero :
                      (∑ i : Fin (n + 2), (a i : ZMod p) *
                        (Fin.snoc (Fin.init x.1) (x.1 (Fin.last (n + 1))) i)) = 0 := by
                    simpa [← hsnoc] using hsum
                  exact (hsolve (Fin.init x.1) (x.1 (Fin.last (n + 1)))).mp hzero
                have : x.1 (Fin.last (n + 1)) = x.1 j.castSucc := by
                  simpa [Fin.init] using hz.trans hj.symm
                have hidx := hxinj this
                exact Fin.castSucc_ne_last j hidx.symm
              exact ⟨hinj_init, hnot⟩
            · intro y
              refine ⟨Fin.snoc y.1 (sol y.1), ?_⟩
              have hyinj := y.2.1
              have hynot := y.2.2
              constructor
              · exact Fin.snoc_injective_of_injective hyinj hynot
              · exact (hsolve y.1 (sol y.1)).mpr rfl
            · intro x
              ext i
              induction i using Fin.lastCases with
              | last =>
                  simp
                  have hzero := x.2.2
                  have hxsnoc : x.1 =
                      Fin.snoc (Fin.init x.1) (x.1 (Fin.last (n + 1))) :=
                    (Fin.snoc_init_self x.1).symm
                  have hz : x.1 (Fin.last (n + 1)) = sol (Fin.init x.1) := by
                    have hzero' :
                        (∑ i : Fin (n + 2), (a i : ZMod p) *
                          (Fin.snoc (Fin.init x.1) (x.1 (Fin.last (n + 1))) i)) = 0 := by
                      simpa [← hxsnoc] using hzero
                    exact (hsolve (Fin.init x.1) (x.1 (Fin.last (n + 1)))).mp hzero'
                  exact hz.symm
              | cast i =>
                  simp [Fin.init]
            · intro y
              ext i
              simp [Fin.init]
          have hbad :
              Fintype.card
                {y : Fin (n + 1) → ZMod p //
                  Injective y ∧ sol y ∈ Set.range y} =
                (n + 1) * goodCount p (n + 1) := by
            calc
              Fintype.card
                {y : Fin (n + 1) → ZMod p //
                  Injective y ∧ sol y ∈ Set.range y}
                  = Fintype.card
                    (Σ j : Fin (n + 1),
                      {y : Fin (n + 1) → ZMod p //
                        Injective y ∧ sol y = y j}) := by
                    let f :
                        (Σ j : Fin (n + 1),
                          {y : Fin (n + 1) → ZMod p //
                            Injective y ∧ sol y = y j}) →
                        {y : Fin (n + 1) → ZMod p //
                          Injective y ∧ sol y ∈ Set.range y} :=
                      fun jy => ⟨jy.2.1, jy.2.2.1, ⟨jy.1, jy.2.2.2.symm⟩⟩
                    have hf_inj : Injective f := by
                      intro u v huv
                      cases u with
                      | mk j yu =>
                      cases v with
                      | mk k yv =>
                        cases yu with
                        | mk yu hyu =>
                        cases yv with
                        | mk yv hyv =>
                        have hfun : yu = yv := congr_arg (fun q => q.1) huv
                        subst yv
                        have hjk : j = k := by
                          apply hyu.1
                          rw [← hyu.2, ← hyv.2]
                        subst hjk
                        rfl
                    have hf_surj : Surjective f := by
                      intro y
                      rcases y.2.2 with ⟨j, hj⟩
                      refine ⟨⟨j, ⟨y.1, y.2.1, hj.symm⟩⟩, ?_⟩
                      rfl
                    exact (Fintype.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)).symm
              _ = ∑ j : Fin (n + 1),
                    Fintype.card
                      {y : Fin (n + 1) → ZMod p //
                        Injective y ∧ sol y = y j} := by
                    simp [Fintype.card_sigma]
              _ = ∑ _j : Fin (n + 1), goodCount p (n + 1) := by
                    apply Finset.sum_congr rfl
                    intro j _
                    have hmerge_pos : ∀ i, 0 < mergeCoeff a j i :=
                      mergeCoeff_pos ha_pos j
                    have hmerge_sum : (∑ i : Fin (n + 1), mergeCoeff a j i) = p :=
                      mergeCoeff_sum ha_sum j
                    have hjcard :
                        Fintype.card
                          {y : Fin (n + 1) → ZMod p //
                            Injective y ∧ sol y = y j} =
                        weightedCard p (n + 1) (mergeCoeff a j) := by
                      unfold weightedCard
                      apply Fintype.card_congr
                      refine Equiv.subtypeEquivRight ?_
                      intro y
                      constructor
                      · intro hy
                        refine ⟨hy.1, ?_⟩
                        rw [weighted_sum_merge]
                        change initSum y + last * y j = 0
                        exact (hlinear y (y j)).mpr hy.2.symm
                      · intro hy
                        refine ⟨hy.1, ?_⟩
                        have h0 := hy.2
                        rw [weighted_sum_merge] at h0
                        change initSum y + last * y j = 0 at h0
                        exact ((hlinear y (y j)).mp h0).symm
                    rw [hjcard, ih (mergeCoeff a j) hmerge_pos hmerge_sum]
              _ = (n + 1) * goodCount p (n + 1) := by
                    simp [Finset.card_univ, Fintype.card_fin]
          have htotal :
              Fintype.card {y : Fin (n + 1) → ZMod p // Injective y} =
                p.descFactorial (n + 1) := by
            rw [Fintype.card_congr
              (Equiv.subtypeInjectiveEquivEmbedding (Fin (n + 1)) (ZMod p))]
            simp [ZMod.card]
          have hpartition :
              Fintype.card
                {y : Fin (n + 1) → ZMod p //
                  Injective y ∧ sol y ∉ Set.range y} =
                p.descFactorial (n + 1) - (n + 1) * goodCount p (n + 1) := by
            let α := {y : Fin (n + 1) → ZMod p // Injective y}
            let bad : α → Prop := fun y => sol y.1 ∈ Set.range y.1
            have hbad' :
                Fintype.card {y : α // bad y} =
                  (n + 1) * goodCount p (n + 1) := by
              calc
                Fintype.card {y : α // bad y}
                    = Fintype.card
                        {y : Fin (n + 1) → ZMod p //
                          Injective y ∧ sol y ∈ Set.range y} := by
                        apply Fintype.card_congr
                        refine
                          { toFun := fun y => ⟨y.1.1, y.1.2, y.2⟩
                            invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
                            left_inv := by intro y; rfl
                            right_inv := by intro y; rfl }
                _ = (n + 1) * goodCount p (n + 1) := hbad
            have hgood' :
                Fintype.card {y : α // ¬ bad y} =
                  Fintype.card
                    {y : Fin (n + 1) → ZMod p //
                      Injective y ∧ sol y ∉ Set.range y} := by
              apply Fintype.card_congr
              refine
                { toFun := fun y => ⟨y.1.1, y.1.2, y.2⟩
                  invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
                  left_inv := by intro y; rfl
                  right_inv := by intro y; rfl }
            have hcomp := Fintype.card_subtype_compl (bad)
            rw [hgood'] at hcomp
            rw [hbad', htotal] at hcomp
            exact hcomp
          rw [hfull, hpartition]
          rfl

lemma goodCount_closed :
    goodCount 2017 64 = Nat.descFactorial 2016 63 - 2016 * (63!) := by
  decide

def coeff : Fin 64 → ℕ :=
  fun i => if (i : ℕ) ≤ 1 then 1 else i

lemma coeff_pos (i : Fin 64) : 0 < coeff i := by
  unfold coeff
  split_ifs with h
  · norm_num
  · exact Nat.pos_of_ne_zero (by omega)

lemma coeff_sum : (∑ i : Fin 64, coeff i) = 2017 := by
  decide

abbrev Index : Type := Finset.range 64

abbrev Value : Type := Finset.Icc 1 2017

def idxEquiv : Fin 64 ≃ Index where
  toFun i := ⟨i, Finset.mem_range.mpr i.2⟩
  invFun i := ⟨i, Finset.mem_range.mp i.2⟩
  left_inv i := by ext; rfl
  right_inv i := by ext; rfl

@[simp] lemma idxEquiv_apply_val (i : Fin 64) : (idxEquiv i : ℕ) = i := rfl

lemma natCast_zmod_2017_inj_on_Icc {a b : ℕ}
    (ha1 : 1 ≤ a) (ha2 : a ≤ 2017) (hb1 : 1 ≤ b) (hb2 : b ≤ 2017)
    (h : (a : ZMod 2017) = (b : ZMod 2017)) : a = b := by
  have hmod : a % 2017 = b % 2017 :=
    (ZMod.natCast_eq_natCast_iff' a b 2017).mp h
  by_cases ha : a = 2017
  · subst a
    by_cases hb : b = 2017
    · exact hb.symm
    · have hblt : b < 2017 := by omega
      rw [Nat.mod_self, Nat.mod_eq_of_lt hblt] at hmod
      omega
  · have halt : a < 2017 := by omega
    rw [Nat.mod_eq_of_lt halt] at hmod
    by_cases hb : b = 2017
    · subst b
      rw [Nat.mod_self] at hmod
      omega
    · have hblt : b < 2017 := by omega
      rw [Nat.mod_eq_of_lt hblt] at hmod
      exact hmod

lemma valueCast_injective : Injective (fun x : Value => ((x : ℕ) : ZMod 2017)) := by
  intro a b h
  apply Subtype.ext
  have ha : 1 ≤ (a : ℕ) ∧ (a : ℕ) ≤ 2017 := Finset.mem_Icc.mp a.2
  have hb : 1 ≤ (b : ℕ) ∧ (b : ℕ) ≤ 2017 := Finset.mem_Icc.mp b.2
  exact natCast_zmod_2017_inj_on_Icc ha.1 ha.2 hb.1 hb.2 h

lemma valueCast_bijective : Bijective (fun x : Value => ((x : ℕ) : ZMod 2017)) := by
  classical
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨valueCast_injective, ?_⟩
  simp [ZMod.card]

noncomputable def valueEquiv : Value ≃ ZMod 2017 :=
  Equiv.ofBijective (fun x : Value => ((x : ℕ) : ZMod 2017)) valueCast_bijective

@[simp] lemma valueEquiv_apply (x : Value) :
    valueEquiv x = ((x : ℕ) : ZMod 2017) := rfl

noncomputable def tupleEquiv : (Index → Value) ≃ (Fin 64 → ZMod 2017) :=
  Equiv.arrowCongr idxEquiv.symm valueEquiv

@[simp] lemma tupleEquiv_apply (x : Index → Value) (i : Fin 64) :
    tupleEquiv x i = ((x (idxEquiv i) : ℕ) : ZMod 2017) := rfl

lemma tupleEquiv_injective_iff (x : Index → Value) :
    Injective (tupleEquiv x) ↔ Injective x := by
  constructor
  · intro h a b hab
    have hmap : tupleEquiv x (idxEquiv.symm a) = tupleEquiv x (idxEquiv.symm b) := by
      simp [hab]
    have hidx := h hmap
    simpa using congrArg idxEquiv hidx
  · intro h i j hij
    apply idxEquiv.injective
    apply h
    exact valueEquiv.injective hij

def origTerm (x : Index → Value) (i : Index) : ℤ :=
  if i ≤ (⟨1, by norm_num⟩ : Index) then (x i : ℤ) else (i : ℤ) * (x i : ℤ)

lemma weighted_sum_eq_intCast_orig (x : Index → Value) :
    (∑ i : Fin 64, (coeff i : ZMod 2017) * tupleEquiv x i) =
      ((∑ i : Index, origTerm x i : ℤ) : ZMod 2017) := by
  rw [Int.cast_sum]
  refine Fintype.sum_equiv idxEquiv
    (fun i : Fin 64 => (coeff i : ZMod 2017) * tupleEquiv x i)
    (fun i : Index => ((origTerm x i : ℤ) : ZMod 2017)) ?_
  intro i
  unfold origTerm coeff
  by_cases hi : (i : ℕ) ≤ 1
  · have hle : idxEquiv i ≤ (⟨1, by norm_num⟩ : Index) := by
      simpa [idxEquiv] using hi
    simp [hi, hle]
  · have hle : ¬ idxEquiv i ≤ (⟨1, by norm_num⟩ : Index) := by
      simpa [idxEquiv] using hi
    simp [hi, hle, Int.cast_mul]

lemma orig_div_iff_weighted (x : Index → Value) :
    (2017 ∣ (∑ i : Index, origTerm x i : ℤ)) ↔
      (∑ i : Fin 64, (coeff i : ZMod 2017) * tupleEquiv x i) = 0 := by
  constructor
  · intro hd
    rw [weighted_sum_eq_intCast_orig]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd
      (∑ i : Index, origTerm x i : ℤ) 2017).mpr hd
  · intro hw
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd
      (∑ i : Index, origTerm x i : ℤ) 2017).mp
    rwa [weighted_sum_eq_intCast_orig x] at hw

end Putnam2017B6

noncomputable abbrev putnam_2017_b6_solution : ℕ := Putnam2017B6.answer

/--
Find the number of ordered $64$-tuples $(x_0,x_1,\dots,x_{63})$ such that $x_0,x_1,\dots,x_{63}$ are distinct elements of $\{1,2,\dots,2017\}$ and
\[
x_0 + x_1 + 2x_2 + 3x_3 + \cdots + 63 x_{63}
\]
is divisible by 2017.
-/
theorem putnam_2017_b6
  (S : Finset (Finset.range 64 → Finset.Icc 1 2017))
  (hs : ∀ x, x ∈ S ↔ (Injective x ∧ (2017 ∣ (∑ i : Finset.range 64, if i ≤ (⟨1, by norm_num⟩ : Finset.range 64) then (x i : ℤ) else i * (x i : ℤ))))) :
  S.card = putnam_2017_b6_solution :=
by
  classical
  haveI : Fact (Nat.Prime 2017) := ⟨by norm_num⟩
  have hS :
      S.card =
        Fintype.card
          {x : Putnam2017B6.Index → Putnam2017B6.Value //
            Injective x ∧
              (2017 ∣ (∑ i : Putnam2017B6.Index, Putnam2017B6.origTerm x i : ℤ))} := by
    exact (Fintype.card_of_subtype S (by
      intro x
      simpa [Putnam2017B6.origTerm] using hs x)).symm
  calc
    S.card =
        Fintype.card
          {x : Putnam2017B6.Index → Putnam2017B6.Value //
            Injective x ∧
              (2017 ∣ (∑ i : Putnam2017B6.Index, Putnam2017B6.origTerm x i : ℤ))} := hS
    _ = Putnam2017B6.weightedCard 2017 64 Putnam2017B6.coeff := by
      unfold Putnam2017B6.weightedCard
      apply Fintype.card_congr
      refine Putnam2017B6.tupleEquiv.subtypeEquiv ?_
      intro x
      constructor
      · intro hx
        exact ⟨(Putnam2017B6.tupleEquiv_injective_iff x).2 hx.1,
          (Putnam2017B6.orig_div_iff_weighted x).1 hx.2⟩
      · intro hx
        exact ⟨(Putnam2017B6.tupleEquiv_injective_iff x).1 hx.1,
          (Putnam2017B6.orig_div_iff_weighted x).2 hx.2⟩
    _ = putnam_2017_b6_solution := by
      rw [Putnam2017B6.weightedCard_eq_goodCount Putnam2017B6.coeff
        Putnam2017B6.coeff_pos Putnam2017B6.coeff_sum]
      rw [Putnam2017B6.goodCount_closed]
