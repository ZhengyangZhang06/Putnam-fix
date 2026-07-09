import Mathlib

set_option maxRecDepth 20000

noncomputable abbrev putnam_2022_a5_solution : ℕ := 290

namespace Putnam2022A5

def aliceValue (n : ℕ) : ℕ :=
  n / 7 +
    match n % 7 with
    | 0 => 0
    | 1 => 1
    | 2 => 0
    | 3 => 1
    | 4 => 2
    | 5 => 1
    | _ => 2

def bobValue (n : ℕ) : ℕ :=
  n / 7 +
    match n % 7 with
    | 1 => 1
    | 3 => 1
    | 5 => 1
    | _ => 0

def hotValue (n : ℕ) : ℕ :=
  if n % 7 = 4 ∨ n % 7 = 6 then 1 else 0

def runBase (rs : List ℕ) : ℕ :=
  (rs.map bobValue).sum

def runHot (rs : List ℕ) : ℕ :=
  (rs.map hotValue).sum

def runAlice (rs : List ℕ) : ℕ :=
  runBase rs + 2 * ((runHot rs + 1) / 2)

def runBob (rs : List ℕ) : ℕ :=
  runBase rs + 2 * (runHot rs / 2)

def splitRuns (l r : ℕ) : List ℕ :=
  (if l = 0 then [] else [l]) ++ (if r = 0 then [] else [r])

def RunMove (rs rs' : List ℕ) : Prop :=
  ∃ pre post m l r, rs = pre ++ m :: post ∧ 2 ≤ m ∧ l + 2 + r = m ∧
    rs' = pre ++ splitRuns l r ++ post

lemma runBase_append (a b : List ℕ) : runBase (a ++ b) = runBase a + runBase b := by
  simp [runBase, List.map_append, List.sum_append]

lemma runHot_append (a b : List ℕ) : runHot (a ++ b) = runHot a + runHot b := by
  simp [runHot, List.map_append, List.sum_append]

lemma runBase_cons (n : ℕ) (rs : List ℕ) : runBase (n :: rs) = bobValue n + runBase rs := by
  simp [runBase]

lemma runHot_cons (n : ℕ) (rs : List ℕ) : runHot (n :: rs) = hotValue n + runHot rs := by
  simp [runHot]

lemma bobValue_zero : bobValue 0 = 0 := by
  norm_num [bobValue]

lemma aliceValue_zero : aliceValue 0 = 0 := by
  norm_num [aliceValue]

lemma hotValue_zero : hotValue 0 = 0 := by
  norm_num [hotValue]

lemma bobValue_le_aliceValue (n : ℕ) : bobValue n ≤ aliceValue n := by
  unfold aliceValue bobValue
  have hmod : n % 7 < 7 := Nat.mod_lt n (by norm_num)
  interval_cases n % 7 <;> simp

lemma runBase_splitRuns (l r : ℕ) : runBase (splitRuns l r) = bobValue l + bobValue r := by
  unfold splitRuns
  by_cases hl : l = 0 <;> by_cases hr : r = 0 <;>
    simp [runBase, hl, hr, bobValue_zero, List.sum_cons]

lemma runHot_splitRuns (l r : ℕ) : runHot (splitRuns l r) = hotValue l + hotValue r := by
  unfold splitRuns
  by_cases hl : l = 0 <;> by_cases hr : r = 0 <;>
    simp [runHot, hl, hr, hotValue_zero, List.sum_cons]

lemma map_aliceValue_splitRuns (l r : ℕ) :
    ((splitRuns l r).map aliceValue).sum = aliceValue l + aliceValue r := by
  unfold splitRuns
  by_cases hl : l = 0 <;> by_cases hr : r = 0 <;>
    simp [hl, hr, aliceValue_zero, List.sum_cons]

lemma map_bobValue_splitRuns (l r : ℕ) :
    ((splitRuns l r).map bobValue).sum = bobValue l + bobValue r := by
  unfold splitRuns
  by_cases hl : l = 0 <;> by_cases hr : r = 0 <;>
    simp [hl, hr, bobValue_zero, List.sum_cons]

lemma map_bobValue_sum_le_aliceValue_sum (rs : List ℕ) :
    (rs.map bobValue).sum ≤ (rs.map aliceValue).sum := by
  induction rs with
  | nil =>
      simp
  | cons n rs ih =>
      simp [List.map_cons]
      have hn := bobValue_le_aliceValue n
      omega

lemma aliceValue_2022 : aliceValue 2022 = 290 := by
  norm_num [aliceValue]

lemma bobValue_le_self (n : ℕ) : bobValue n ≤ n := by
  unfold bobValue
  have hmod : n % 7 < 7 := Nat.mod_lt n (by norm_num)
  have hdiv : 7 * (n / 7) + n % 7 = n := Nat.div_add_mod n 7
  interval_cases n % 7 <;> simp at hdiv ⊢ <;> omega

lemma aliceValue_le_self (n : ℕ) : aliceValue n ≤ n := by
  unfold aliceValue
  have hmod : n % 7 < 7 := Nat.mod_lt n (by norm_num)
  have hdiv : 7 * (n / 7) + n % 7 = n := Nat.div_add_mod n 7
  interval_cases n % 7 <;> simp at hdiv ⊢ <;> omega

lemma mod_add_two_seven (l r : ℕ) :
    (l + 2 + r) % 7 = (l % 7 + 2 + r % 7) % 7 := by
  have hldiv : 7 * (l / 7) + l % 7 = l := Nat.div_add_mod l 7
  have hrdiv : 7 * (r / 7) + r % 7 = r := Nat.div_add_mod r 7
  have hcarrymod :
      7 * ((l % 7 + 2 + r % 7) / 7) + (l % 7 + 2 + r % 7) % 7 =
        l % 7 + 2 + r % 7 := Nat.div_add_mod (l % 7 + 2 + r % 7) 7
  have hmain :
      7 * ((l + 2 + r) / 7) + (l + 2 + r) % 7 = l + 2 + r :=
    Nat.div_add_mod (l + 2 + r) 7
  have h1 : (l + 2 + r) % 7 < 7 := Nat.mod_lt (l + 2 + r) (by norm_num)
  have h2 : (l % 7 + 2 + r % 7) % 7 < 7 :=
    Nat.mod_lt (l % 7 + 2 + r % 7) (by norm_num)
  omega

lemma div_add_two_seven (l r : ℕ) :
    (l + 2 + r) / 7 = l / 7 + r / 7 + ((l % 7 + 2 + r % 7) / 7) := by
  have hldiv : 7 * (l / 7) + l % 7 = l := Nat.div_add_mod l 7
  have hrdiv : 7 * (r / 7) + r % 7 = r := Nat.div_add_mod r 7
  have hcarrymod :
      7 * ((l % 7 + 2 + r % 7) / 7) + (l % 7 + 2 + r % 7) % 7 =
        l % 7 + 2 + r % 7 := Nat.div_add_mod (l % 7 + 2 + r % 7) 7
  have hmain :
      7 * ((l + 2 + r) / 7) + (l + 2 + r) % 7 = l + 2 + r :=
    Nat.div_add_mod (l + 2 + r) 7
  have hmodmain : (l + 2 + r) % 7 = (l % 7 + 2 + r % 7) % 7 :=
    mod_add_two_seven l r
  omega

lemma local_alice_upper (T l r m : ℕ) (hm : l + 2 + r = m) :
    bobValue l + bobValue r + 2 * ((T + hotValue l + hotValue r) / 2) ≤
      bobValue m + 2 * ((T + hotValue m + 1) / 2) := by
  subst m
  unfold bobValue hotValue
  rw [div_add_two_seven, mod_add_two_seven]
  have hldiv : 7 * (l / 7) + l % 7 = l := Nat.div_add_mod l 7
  have hrdiv : 7 * (r / 7) + r % 7 = r := Nat.div_add_mod r 7
  have htdiv : 2 * (T / 2) + T % 2 = T := Nat.div_add_mod T 2
  have hlmod : l % 7 < 7 := Nat.mod_lt l (by norm_num)
  have hrmod : r % 7 < 7 := Nat.mod_lt r (by norm_num)
  have htmod : T % 2 < 2 := Nat.mod_lt T (by norm_num)
  interval_cases l % 7 <;> interval_cases r % 7 <;> interval_cases T % 2 <;>
    simp at hldiv hrdiv htdiv ⊢ <;> omega

lemma local_bob_lower (T l r m : ℕ) (hm : l + 2 + r = m) :
    bobValue m + 2 * ((T + hotValue m) / 2) ≤
      bobValue l + bobValue r + 2 * ((T + hotValue l + hotValue r + 1) / 2) := by
  subst m
  unfold bobValue hotValue
  rw [div_add_two_seven, mod_add_two_seven]
  have hldiv : 7 * (l / 7) + l % 7 = l := Nat.div_add_mod l 7
  have hrdiv : 7 * (r / 7) + r % 7 = r := Nat.div_add_mod r 7
  have htdiv : 2 * (T / 2) + T % 2 = T := Nat.div_add_mod T 2
  have hlmod : l % 7 < 7 := Nat.mod_lt l (by norm_num)
  have hrmod : r % 7 < 7 := Nat.mod_lt r (by norm_num)
  have htmod : T % 2 < 2 := Nat.mod_lt T (by norm_num)
  interval_cases l % 7 <;> interval_cases r % 7 <;> interval_cases T % 2 <;>
    simp at hldiv hrdiv htdiv ⊢ <;> omega

lemma local_alice_exists (T m : ℕ) (hm : 2 ≤ m)
    (hsel : (T + hotValue m) % 2 = 0 ∨ hotValue m = 1) :
    ∃ l r, l + 2 + r = m ∧
      bobValue l + bobValue r + 2 * ((T + hotValue l + hotValue r) / 2) =
        bobValue m + 2 * ((T + hotValue m + 1) / 2) := by
  unfold hotValue at hsel
  unfold bobValue hotValue
  have hmdiv : 7 * (m / 7) + m % 7 = m := Nat.div_add_mod m 7
  have htdiv : 2 * (T / 2) + T % 2 = T := Nat.div_add_mod T 2
  have hmmod : m % 7 < 7 := Nat.mod_lt m (by norm_num)
  have htmod : T % 2 < 2 := Nat.mod_lt T (by norm_num)
  interval_cases m % 7
  · refine ⟨7 * (m / 7 - 1) + 5, 0, by omega, ?_⟩
    have h1 : (7 * (m / 7 - 1) + 5) % 7 = 5 := by omega
    have h2 : (7 * (m / 7 - 1) + 5) / 7 = m / 7 - 1 := by omega
    interval_cases T % 2 <;> simp [h1, h2] at hmdiv htdiv hsel ⊢ <;> omega
  · refine ⟨5, 7 * (m / 7 - 1) + 1, by omega, ?_⟩
    have h1 : (7 * (m / 7 - 1) + 1) % 7 = 1 := by omega
    have h2 : (7 * (m / 7 - 1) + 1) / 7 = m / 7 - 1 := by omega
    interval_cases T % 2 <;> simp [h1, h2] at hmdiv htdiv hsel ⊢ <;> omega
  · refine ⟨0, 7 * (m / 7), by omega, ?_⟩
    have h1 : (7 * (m / 7)) % 7 = 0 := by omega
    have h2 : (7 * (m / 7)) / 7 = m / 7 := by omega
    interval_cases T % 2 <;> simp [h1, h2] at hmdiv htdiv hsel ⊢ <;> omega
  · refine ⟨1, 7 * (m / 7), by omega, ?_⟩
    have h1 : (7 * (m / 7)) % 7 = 0 := by omega
    have h2 : (7 * (m / 7)) / 7 = m / 7 := by omega
    interval_cases T % 2 <;> simp [h1, h2] at hmdiv htdiv hsel ⊢ <;> omega
  · refine ⟨7 * (m / 7) + 1, 1, by omega, ?_⟩
    have h1 : (7 * (m / 7) + 1) % 7 = 1 := by omega
    have h2 : (7 * (m / 7) + 1) / 7 = m / 7 := by omega
    interval_cases T % 2 <;> simp [h1, h2] at hmdiv htdiv hsel ⊢ <;> omega
  · refine ⟨0, 7 * (m / 7) + 3, by omega, ?_⟩
    have h1 : (7 * (m / 7) + 3) % 7 = 3 := by omega
    have h2 : (7 * (m / 7) + 3) / 7 = m / 7 := by omega
    interval_cases T % 2 <;> simp [h1, h2] at hmdiv htdiv hsel ⊢ <;> omega
  · refine ⟨7 * (m / 7) + 3, 1, by omega, ?_⟩
    have h1 : (7 * (m / 7) + 3) % 7 = 3 := by omega
    have h2 : (7 * (m / 7) + 3) / 7 = m / 7 := by omega
    interval_cases T % 2 <;> simp [h1, h2] at hmdiv htdiv hsel ⊢ <;> omega

lemma local_bob_exists (T m : ℕ) (hm : 2 ≤ m)
    (hsel : (T + hotValue m) % 2 = 0 ∨ hotValue m = 1) :
    ∃ l r, l + 2 + r = m ∧
      bobValue l + bobValue r + 2 * ((T + hotValue l + hotValue r + 1) / 2) =
        bobValue m + 2 * ((T + hotValue m) / 2) := by
  unfold hotValue at hsel
  unfold bobValue hotValue
  have hmdiv : 7 * (m / 7) + m % 7 = m := Nat.div_add_mod m 7
  have htdiv : 2 * (T / 2) + T % 2 = T := Nat.div_add_mod T 2
  have hmmod : m % 7 < 7 := Nat.mod_lt m (by norm_num)
  have htmod : T % 2 < 2 := Nat.mod_lt T (by norm_num)
  interval_cases m % 7
  · refine ⟨7 * (m / 7 - 1) + 5, 0, by omega, ?_⟩
    have h1 : (7 * (m / 7 - 1) + 5) % 7 = 5 := by omega
    have h2 : (7 * (m / 7 - 1) + 5) / 7 = m / 7 - 1 := by omega
    interval_cases T % 2 <;> simp [h1, h2] at hmdiv htdiv hsel ⊢ <;> omega
  · refine ⟨5, 7 * (m / 7 - 1) + 1, by omega, ?_⟩
    have h1 : (7 * (m / 7 - 1) + 1) % 7 = 1 := by omega
    have h2 : (7 * (m / 7 - 1) + 1) / 7 = m / 7 - 1 := by omega
    interval_cases T % 2 <;> simp [h1, h2] at hmdiv htdiv hsel ⊢ <;> omega
  · refine ⟨0, 7 * (m / 7), by omega, ?_⟩
    have h1 : (7 * (m / 7)) % 7 = 0 := by omega
    have h2 : (7 * (m / 7)) / 7 = m / 7 := by omega
    interval_cases T % 2 <;> simp [h1, h2] at hmdiv htdiv hsel ⊢ <;> omega
  · refine ⟨1, 7 * (m / 7), by omega, ?_⟩
    have h1 : (7 * (m / 7)) % 7 = 0 := by omega
    have h2 : (7 * (m / 7)) / 7 = m / 7 := by omega
    interval_cases T % 2 <;> simp [h1, h2] at hmdiv htdiv hsel ⊢ <;> omega
  · refine ⟨0, 7 * (m / 7) + 2, by omega, ?_⟩
    have h1 : (7 * (m / 7) + 2) % 7 = 2 := by omega
    have h2 : (7 * (m / 7) + 2) / 7 = m / 7 := by omega
    interval_cases T % 2 <;> simp [h1, h2] at hmdiv htdiv hsel ⊢ <;> omega
  · refine ⟨0, 7 * (m / 7) + 3, by omega, ?_⟩
    have h1 : (7 * (m / 7) + 3) % 7 = 3 := by omega
    have h2 : (7 * (m / 7) + 3) / 7 = m / 7 := by omega
    interval_cases T % 2 <;> simp [h1, h2] at hmdiv htdiv hsel ⊢ <;> omega
  · refine ⟨2, 7 * (m / 7) + 2, by omega, ?_⟩
    have h1 : (7 * (m / 7) + 2) % 7 = 2 := by omega
    have h2 : (7 * (m / 7) + 2) / 7 = m / 7 := by omega
    interval_cases T % 2 <;> simp [h1, h2] at hmdiv htdiv hsel ⊢ <;> omega

lemma runMove_alice_upper {rs rs' : List ℕ} (h : RunMove rs rs') :
    runBob rs' ≤ runAlice rs := by
  rcases h with ⟨pre, post, m, l, r, hrs, hm2, hsplit, hrs'⟩
  subst rs
  subst rs'
  unfold runAlice runBob
  have hloc := local_alice_upper (runHot pre + runHot post) l r m hsplit
  simp [runBase_append, runHot_append, runBase_cons, runHot_cons,
    runBase_splitRuns, runHot_splitRuns, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at hloc ⊢
  omega

lemma runMove_bob_lower {rs rs' : List ℕ} (h : RunMove rs rs') :
    runBob rs ≤ runAlice rs' := by
  rcases h with ⟨pre, post, m, l, r, hrs, hm2, hsplit, hrs'⟩
  subst rs
  subst rs'
  unfold runAlice runBob
  have hloc := local_bob_lower (runHot pre + runHot post) l r m hsplit
  simp [runBase_append, runHot_append, runBase_cons, runHot_cons,
    runBase_splitRuns, runHot_splitRuns, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at hloc ⊢
  omega

lemma runBob_le_runAlice (rs : List ℕ) : runBob rs ≤ runAlice rs := by
  unfold runBob runAlice
  omega

lemma hotValue_eq_one_ge_two {m : ℕ} (hm : hotValue m = 1) : 2 ≤ m := by
  unfold hotValue at hm
  by_cases h : m % 7 = 4 ∨ m % 7 = 6
  · have hmod : m % 7 < 7 := Nat.mod_lt m (by norm_num)
    have hdiv : 7 * (m / 7) + m % 7 = m := Nat.div_add_mod m 7
    rcases h with h4 | h6 <;> omega
  · simp [h] at hm

lemma exists_hot_run_of_runHot_pos {rs : List ℕ} (hpos : 0 < runHot rs) :
    ∃ pre post m, rs = pre ++ m :: post ∧ hotValue m = 1 := by
  induction rs with
  | nil =>
      simp [runHot] at hpos
  | cons m rs ih =>
      by_cases hm : hotValue m = 1
      · exact ⟨[], rs, m, by simp, hm⟩
      · have hm0 : hotValue m = 0 := by
          unfold hotValue at hm ⊢
          split <;> simp_all
        have htail : 0 < runHot rs := by
          simp [runHot, hm0] at hpos
          exact hpos
        rcases ih htail with ⟨pre, post, n, hrs, hn⟩
        exact ⟨m :: pre, post, n, by simp [hrs], hn⟩

lemma runHot_decomp (pre post : List ℕ) (m : ℕ) :
    runHot (pre ++ m :: post) = runHot pre + hotValue m + runHot post := by
  simp [runHot_append, runHot_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma exists_select_run (rs : List ℕ)
    (hmove : ∃ pre post m, rs = pre ++ m :: post ∧ 2 ≤ m) :
    ∃ pre post m, rs = pre ++ m :: post ∧ 2 ≤ m ∧
      ((runHot pre + runHot post + hotValue m) % 2 = 0 ∨ hotValue m = 1) := by
  by_cases heven : runHot rs % 2 = 0
  · rcases hmove with ⟨pre, post, m, hrs, hm⟩
    refine ⟨pre, post, m, hrs, hm, Or.inl ?_⟩
    subst rs
    rw [runHot_decomp] at heven
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using heven
  · have hpos : 0 < runHot rs := by
      by_contra hzero
      have : runHot rs = 0 := by omega
      simp [this] at heven
    rcases exists_hot_run_of_runHot_pos hpos with ⟨pre, post, m, hrs, hmhot⟩
    exact ⟨pre, post, m, hrs, hotValue_eq_one_ge_two hmhot, Or.inr hmhot⟩

lemma runMove_alice_exists (rs : List ℕ)
    (hmove : ∃ pre post m, rs = pre ++ m :: post ∧ 2 ≤ m) :
    ∃ rs', RunMove rs rs' ∧ runAlice rs ≤ runBob rs' := by
  rcases exists_select_run rs hmove with ⟨pre, post, m, hrs, hm2, hsel⟩
  have hsel' : (runHot pre + runHot post + hotValue m) % 2 = 0 ∨ hotValue m = 1 := hsel
  rcases local_alice_exists (runHot pre + runHot post) m hm2 (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsel') with
    ⟨l, r, hsplit, heq⟩
  refine ⟨pre ++ splitRuns l r ++ post, ?_, ?_⟩
  · exact ⟨pre, post, m, l, r, hrs, hm2, hsplit, rfl⟩
  · subst rs
    unfold runAlice runBob
    simp [runBase_append, runHot_append, runBase_cons, runHot_cons,
      runBase_splitRuns, runHot_splitRuns, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at heq ⊢
    omega

lemma runMove_bob_exists (rs : List ℕ)
    (hmove : ∃ pre post m, rs = pre ++ m :: post ∧ 2 ≤ m) :
    ∃ rs', RunMove rs rs' ∧ runAlice rs' ≤ runBob rs := by
  rcases exists_select_run rs hmove with ⟨pre, post, m, hrs, hm2, hsel⟩
  have hsel' : (runHot pre + runHot post + hotValue m) % 2 = 0 ∨ hotValue m = 1 := hsel
  rcases local_bob_exists (runHot pre + runHot post) m hm2 (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsel') with
    ⟨l, r, hsplit, heq⟩
  refine ⟨pre ++ splitRuns l r ++ post, ?_, ?_⟩
  · exact ⟨pre, post, m, l, r, hrs, hm2, hsplit, rfl⟩
  · subst rs
    unfold runAlice runBob
    simp [runBase_append, runHot_append, runBase_cons, runHot_cons,
      runBase_splitRuns, runHot_splitRuns, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at heq ⊢
    omega

lemma aliceValue_split_to_bobValue (m : ℕ) (hm : 2 ≤ m) :
    ∃ l r, l + 2 + r = m ∧ aliceValue m ≤ bobValue l + bobValue r := by
  unfold aliceValue bobValue
  have hmod : m % 7 < 7 := Nat.mod_lt m (by norm_num)
  have hdiv : 7 * (m / 7) + m % 7 = m := Nat.div_add_mod m 7
  interval_cases m % 7
  · refine ⟨0, m - 2, by omega, ?_⟩
    simp at hdiv ⊢
    have h₁ : (m - 2) % 7 = 5 := by omega
    have h₂ : (m - 2) / 7 = m / 7 - 1 := by omega
    simp [h₁, h₂]
    omega
  · refine ⟨1, m - 3, by omega, ?_⟩
    simp at hdiv ⊢
    have h₁ : (m - 3) % 7 = 5 := by omega
    have h₂ : (m - 3) / 7 = m / 7 - 1 := by omega
    simp [h₁, h₂]
    omega
  · refine ⟨0, m - 2, by omega, ?_⟩
    simp at hdiv ⊢
    have h₁ : (m - 2) % 7 = 0 := by omega
    have h₂ : (m - 2) / 7 = m / 7 := by omega
    simp [h₁, h₂]
  · refine ⟨0, m - 2, by omega, ?_⟩
    simp at hdiv ⊢
    have h₁ : (m - 2) % 7 = 1 := by omega
    have h₂ : (m - 2) / 7 = m / 7 := by omega
    simp [h₁, h₂]
  · refine ⟨1, m - 3, by omega, ?_⟩
    simp at hdiv ⊢
    have h₁ : (m - 3) % 7 = 1 := by omega
    have h₂ : (m - 3) / 7 = m / 7 := by omega
    simp [h₁, h₂]
    omega
  · refine ⟨0, m - 2, by omega, ?_⟩
    simp at hdiv ⊢
    have h₁ : (m - 2) % 7 = 3 := by omega
    have h₂ : (m - 2) / 7 = m / 7 := by omega
    simp [h₁, h₂]
  · refine ⟨1, m - 3, by omega, ?_⟩
    simp at hdiv ⊢
    have h₁ : (m - 3) % 7 = 3 := by omega
    have h₂ : (m - 3) / 7 = m / 7 := by omega
    simp [h₁, h₂]
    omega

lemma bobValue_split_le_aliceValue (l r m : ℕ) (hm : l + 2 + r = m) :
    bobValue l + bobValue r ≤ aliceValue m := by
  subst m
  unfold aliceValue bobValue
  rw [div_add_two_seven, mod_add_two_seven]
  have hldiv : 7 * (l / 7) + l % 7 = l := Nat.div_add_mod l 7
  have hrdiv : 7 * (r / 7) + r % 7 = r := Nat.div_add_mod r 7
  have hlmod : l % 7 < 7 := Nat.mod_lt l (by norm_num)
  have hrmod : r % 7 < 7 := Nat.mod_lt r (by norm_num)
  interval_cases l % 7 <;> interval_cases r % 7 <;>
    simp at hldiv hrdiv ⊢ <;> omega

lemma bobValue_le_aliceValue_split (l r m : ℕ) (hm : l + 2 + r = m) :
    bobValue m ≤ aliceValue l + aliceValue r := by
  subst m
  unfold aliceValue bobValue
  rw [div_add_two_seven, mod_add_two_seven]
  have hldiv : 7 * (l / 7) + l % 7 = l := Nat.div_add_mod l 7
  have hrdiv : 7 * (r / 7) + r % 7 = r := Nat.div_add_mod r 7
  have hlmod : l % 7 < 7 := Nat.mod_lt l (by norm_num)
  have hrmod : r % 7 < 7 := Nat.mod_lt r (by norm_num)
  interval_cases l % 7 <;> interval_cases r % 7 <;>
    simp at hldiv hrdiv ⊢ <;> omega

lemma bobValue_split_to_aliceValue (m : ℕ) (hm : 2 ≤ m) :
    ∃ l r, l + 2 + r = m ∧ aliceValue l + aliceValue r ≤ bobValue m := by
  unfold aliceValue bobValue
  have hmod : m % 7 < 7 := Nat.mod_lt m (by norm_num)
  have hdiv : 7 * (m / 7) + m % 7 = m := Nat.div_add_mod m 7
  interval_cases m % 7
  · refine ⟨0, m - 2, by omega, ?_⟩
    simp at hdiv ⊢
    have h₁ : (m - 2) % 7 = 5 := by omega
    have h₂ : (m - 2) / 7 = m / 7 - 1 := by omega
    simp [h₁, h₂]
    omega
  · refine ⟨0, m - 2, by omega, ?_⟩
    simp at hdiv ⊢
    have h₁ : (m - 2) % 7 = 6 := by omega
    have h₂ : (m - 2) / 7 = m / 7 - 1 := by omega
    simp [h₁, h₂]
    omega
  · refine ⟨0, m - 2, by omega, ?_⟩
    simp at hdiv ⊢
    have h₁ : (m - 2) % 7 = 0 := by omega
    have h₂ : (m - 2) / 7 = m / 7 := by omega
    simp [h₁, h₂]
  · refine ⟨0, m - 2, by omega, ?_⟩
    simp at hdiv ⊢
    have h₁ : (m - 2) % 7 = 1 := by omega
    have h₂ : (m - 2) / 7 = m / 7 := by omega
    simp [h₁, h₂]
  · refine ⟨0, m - 2, by omega, ?_⟩
    simp at hdiv ⊢
    have h₁ : (m - 2) % 7 = 2 := by omega
    have h₂ : (m - 2) / 7 = m / 7 := by omega
    simp [h₁, h₂]
  · refine ⟨0, m - 2, by omega, ?_⟩
    simp at hdiv ⊢
    have h₁ : (m - 2) % 7 = 3 := by omega
    have h₂ : (m - 2) / 7 = m / 7 := by omega
    simp [h₁, h₂]
  · refine ⟨2, m - 4, by omega, ?_⟩
    simp at hdiv ⊢
    have h₁ : (m - 4) % 7 = 2 := by omega
    have h₂ : (m - 4) / 7 = m / 7 := by omega
    simp [h₁, h₂]

lemma runMove_simple_alice_upper {rs rs' : List ℕ} (h : RunMove rs rs') :
    (rs'.map bobValue).sum ≤ (rs.map aliceValue).sum := by
  rcases h with ⟨pre, post, m, l, r, hrs, hm2, hsplit, hrs'⟩
  subst rs
  subst rs'
  have hpre := map_bobValue_sum_le_aliceValue_sum pre
  have hpost := map_bobValue_sum_le_aliceValue_sum post
  have hloc := bobValue_split_le_aliceValue l r m hsplit
  simp [List.map_append, List.sum_append, map_bobValue_splitRuns, List.map_cons,
    List.sum_cons]
  omega

lemma runMove_simple_bob_lower {rs rs' : List ℕ} (h : RunMove rs rs') :
    (rs.map bobValue).sum ≤ (rs'.map aliceValue).sum := by
  rcases h with ⟨pre, post, m, l, r, hrs, hm2, hsplit, hrs'⟩
  subst rs
  subst rs'
  have hpre := map_bobValue_sum_le_aliceValue_sum pre
  have hpost := map_bobValue_sum_le_aliceValue_sum post
  have hloc := bobValue_le_aliceValue_split l r m hsplit
  simp [List.map_append, List.sum_append, map_aliceValue_splitRuns, List.map_cons,
    List.sum_cons]
  omega

def runWeight (v : ℕ → ℕ) : List Bool → ℕ → ℕ
  | [], r => if r = 0 then 0 else v r
  | b :: bs, r =>
      if b then
        runWeight v bs (r + 1)
      else
        (if r = 0 then 0 else v r) + runWeight v bs 0

def freeRunsAux : List Bool → ℕ → List ℕ
  | [], r => if r = 0 then [] else [r]
  | b :: bs, r =>
      if b then
        freeRunsAux bs (r + 1)
      else
        (if r = 0 then [] else [r]) ++ freeRunsAux bs 0

def freeRuns (bs : List Bool) : List ℕ :=
  freeRunsAux bs 0

lemma runWeight_eq_freeRunsAux (v : ℕ → ℕ) (bs : List Bool) (r : ℕ) :
    runWeight v bs r = ((freeRunsAux bs r).map v).sum := by
  induction bs generalizing r with
  | nil =>
      by_cases hr : r = 0 <;> simp [runWeight, freeRunsAux, hr]
  | cons b bs ih =>
      cases b
      · by_cases hr : r = 0 <;> simp [runWeight, freeRunsAux, ih, hr]
      · simp [runWeight, freeRunsAux, ih]

def leadTrue : List Bool → ℕ
  | [] => 0
  | true :: bs => leadTrue bs + 1
  | false :: _ => 0

def dropLeadTrue : List Bool → List Bool
  | [] => []
  | true :: bs => dropLeadTrue bs
  | false :: bs => false :: bs

def flipPair : List Bool → ℕ → List Bool
  | _ :: _ :: bs, 0 => false :: false :: bs
  | b :: bs, i + 1 => b :: flipPair bs i
  | bs, _ => bs

lemma flipPair_cons_succ (b : Bool) (bs : List Bool) (i : ℕ) :
    flipPair (b :: bs) (i + 1) = b :: flipPair bs i := by
  cases bs <;> simp [flipPair]

lemma freeRunsAux_pos_eq (bs : List Bool) {a : ℕ} (ha : 0 < a) :
    freeRunsAux bs a = (a + leadTrue bs) :: freeRunsAux (dropLeadTrue bs) 0 := by
  induction bs generalizing a with
  | nil =>
      simp [freeRunsAux, leadTrue, dropLeadTrue, Nat.ne_of_gt ha]
  | cons b bs ih =>
      cases b
      · simp [freeRunsAux, leadTrue, dropLeadTrue, Nat.ne_of_gt ha]
      · simpa [freeRunsAux, leadTrue, dropLeadTrue, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using ih (Nat.succ_pos a)

lemma freeRunsAux_zero_eq (bs : List Bool) :
    freeRunsAux bs 0 = splitRuns 0 (leadTrue bs) ++ freeRunsAux (dropLeadTrue bs) 0 := by
  cases bs with
  | nil =>
      simp [freeRunsAux, splitRuns, leadTrue, dropLeadTrue]
  | cons b bs =>
      cases b
      · simp [freeRunsAux, splitRuns, leadTrue, dropLeadTrue]
      · have h := freeRunsAux_pos_eq bs (a := 1) (by norm_num)
        rw [show freeRunsAux (true :: bs) 0 = freeRunsAux bs 1 by rfl, h]
        simp [splitRuns, leadTrue, dropLeadTrue, Nat.add_comm]

lemma freeRunsAux_false_false_eq (tail : List Bool) (r : ℕ) :
    freeRunsAux (false :: false :: tail) r =
      splitRuns r (leadTrue tail) ++ freeRunsAux (dropLeadTrue tail) 0 := by
  by_cases hr : r = 0
  · subst r
    rw [show freeRunsAux (false :: false :: tail) 0 = freeRunsAux tail 0 by
      simp [freeRunsAux]]
    rw [freeRunsAux_zero_eq tail]
  · rw [show freeRunsAux (false :: false :: tail) r = [r] ++ freeRunsAux tail 0 by
      simp [freeRunsAux, hr]]
    rw [freeRunsAux_zero_eq tail]
    unfold splitRuns
    simp [hr]

lemma RunMove.append_left (p : List ℕ) {a b : List ℕ} (h : RunMove a b) :
    RunMove (p ++ a) (p ++ b) := by
  rcases h with ⟨pre, post, m, l, r, ha, hm, hsplit, hb⟩
  refine ⟨p ++ pre, post, m, l, r, ?_, hm, hsplit, ?_⟩
  · rw [ha, List.append_assoc]
  · rw [hb]
    simp [List.append_assoc]

lemma freeRunsAux_flipPair_runMove (bs : List Bool) (i r : ℕ)
    (hlen : i + 1 < bs.length) (hi : bs[i] = true) (hi1 : bs[i + 1] = true) :
    RunMove (freeRunsAux bs r) (freeRunsAux (flipPair bs i) r) := by
  induction bs generalizing i r with
  | nil =>
      simp at hlen
  | cons b bs ih =>
      cases i with
      | zero =>
          cases bs with
          | nil =>
              simp at hlen
          | cons c tail =>
              simp at hi hi1
              subst b
              subst c
              have hold := freeRunsAux_pos_eq tail (a := r + 2) (by omega)
              have hnew := freeRunsAux_false_false_eq tail r
              rw [show freeRunsAux (true :: true :: tail) r = freeRunsAux tail (r + 2) by
                rfl]
              rw [show flipPair (true :: true :: tail) 0 = false :: false :: tail by
                simp [flipPair]]
              rw [hold, hnew]
              refine ⟨[], freeRunsAux (dropLeadTrue tail) 0, r + 2 + leadTrue tail,
                r, leadTrue tail, ?_, ?_, ?_, ?_⟩
              · simp
              · omega
              · omega
              · simp
      | succ j =>
          rw [flipPair_cons_succ]
          cases b
          · have htail : j + 1 < bs.length := by simpa using hlen
            have ht0 : bs[j] = true := by simpa using hi
            have ht1 : bs[j + 1] = true := by simpa using hi1
            have hmove := ih j 0 htail ht0 ht1
            by_cases hr : r = 0
            · subst r
              simpa [freeRunsAux] using hmove
            · have hpref :
                  RunMove ([r] ++ freeRunsAux bs 0) ([r] ++ freeRunsAux (flipPair bs j) 0) :=
                RunMove.append_left [r] hmove
              simpa [freeRunsAux, hr] using hpref
          · have htail : j + 1 < bs.length := by simpa using hlen
            have ht0 : bs[j] = true := by simpa using hi
            have ht1 : bs[j + 1] = true := by simpa using hi1
            simpa [freeRunsAux] using ih j (r + 1) htail ht0 ht1

lemma leadTrue_le_length (bs : List Bool) : leadTrue bs ≤ bs.length := by
  induction bs with
  | nil =>
      simp [leadTrue]
  | cons b bs ih =>
      cases b <;> simp [leadTrue, ih]

lemma dropLeadTrue_length_add (bs : List Bool) :
    (dropLeadTrue bs).length + leadTrue bs = bs.length := by
  induction bs with
  | nil =>
      simp [dropLeadTrue, leadTrue]
  | cons b bs ih =>
      cases b <;> simp [dropLeadTrue, leadTrue, ih, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc]

lemma leadTrue_dropLeadTrue_eq_zero (bs : List Bool) :
    leadTrue (dropLeadTrue bs) = 0 := by
  induction bs with
  | nil =>
      simp [dropLeadTrue, leadTrue]
  | cons b bs ih =>
      cases b <;> simp [dropLeadTrue, leadTrue, ih]

lemma freeRunsAux_eq_cons_of_leadTrue_zero (bs : List Bool) {a : ℕ}
    (ha : 0 < a) (hlead : leadTrue bs = 0) :
    freeRunsAux bs a = a :: freeRunsAux bs 0 := by
  cases bs with
  | nil =>
      simp [freeRunsAux, Nat.ne_of_gt ha]
  | cons b bs =>
      cases b
      · simp [freeRunsAux, Nat.ne_of_gt ha]
      · simp [leadTrue] at hlead

lemma leadTrue_flipPair_eq_zero_of_get_true (bs : List Bool) {j : ℕ}
    (hlead : leadTrue bs = 0) (hj : j < bs.length) (htrue : bs[j]'hj = true) :
    leadTrue (flipPair bs j) = 0 := by
  cases bs with
  | nil =>
      simp at hj
  | cons b tail =>
      cases b
      · cases j with
        | zero =>
            simp at htrue
        | succ j =>
            simp [flipPair_cons_succ, leadTrue]
      · simp [leadTrue] at hlead

lemma getElem_true_of_lt_leadTrue (bs : List Bool) (i : ℕ)
    (hi : i < leadTrue bs) (hib : i < bs.length) :
    bs[i]'hib = true := by
  induction bs generalizing i with
  | nil =>
      simp [leadTrue] at hi
  | cons b bs ih =>
      cases b
      · simp [leadTrue] at hi
      · cases i with
        | zero =>
            simp
        | succ i =>
            have hi' : i < leadTrue bs := by
              simp [leadTrue] at hi
              omega
            have hib' : i < bs.length := by
              simpa using hib
            simpa using ih i hi' hib'

lemma getElem_leadTrue_add (bs : List Bool) (j : ℕ)
    (hj : j < (dropLeadTrue bs).length)
    (hbs : leadTrue bs + j < bs.length) :
    bs[leadTrue bs + j]'hbs = (dropLeadTrue bs)[j]'hj := by
  induction bs generalizing j with
  | nil =>
      simp [dropLeadTrue] at hj
  | cons b bs ih =>
      cases b
      · simp [leadTrue, dropLeadTrue]
      · have hj' : j < (dropLeadTrue bs).length := by simpa [dropLeadTrue] using hj
        have hbs' : leadTrue bs + j < bs.length := by
          simp [leadTrue] at hbs
          omega
        have hidx : leadTrue (true :: bs) + j = (leadTrue bs + j) + 1 := by
          simp [leadTrue]
          omega
        calc
          (true :: bs)[leadTrue (true :: bs) + j]'hbs =
              (true :: bs)[(leadTrue bs + j) + 1]'(by simpa [hidx] using hbs) :=
            getElem_congr rfl hidx hbs
          _ = bs[leadTrue bs + j]'hbs' :=
            List.getElem_cons_succ true bs (leadTrue bs + j) _
          _ = (dropLeadTrue bs)[j]'hj' := ih j hj' hbs'

lemma freeRunsAux_flipPair_lead (bs : List Bool) (a l r : ℕ)
    (h : l + 2 + r = leadTrue bs) :
    freeRunsAux (flipPair bs l) a =
      splitRuns (a + l) r ++ freeRunsAux (dropLeadTrue bs) 0 := by
  induction l generalizing bs a with
  | zero =>
      cases bs with
      | nil =>
          simp [leadTrue] at h
      | cons b bs =>
          cases b
          · simp [leadTrue] at h
          · cases bs with
            | nil =>
                simp [leadTrue] at h
                omega
            | cons c tail =>
                cases c
                · simp [leadTrue] at h
                  omega
                · have hr : leadTrue tail = r := by
                    simp [leadTrue] at h
                    omega
                  rw [show flipPair (true :: true :: tail) 0 = false :: false :: tail by
                    simp [flipPair]]
                  rw [freeRunsAux_false_false_eq tail a]
                  simp [dropLeadTrue, hr, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  | succ l ih =>
      cases bs with
      | nil =>
          simp [leadTrue] at h
      | cons b tail =>
          cases b
          · simp [leadTrue] at h
          · have htail : l + 2 + r = leadTrue tail := by
              simp [leadTrue] at h
              omega
            rw [flipPair_cons_succ]
            change freeRunsAux (flipPair tail l) (a + 1) =
              splitRuns (a + (l + 1)) r ++ freeRunsAux (dropLeadTrue tail) 0
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih tail (a + 1) htail

lemma freeRunsAux_flipPair_after_lead (bs : List Bool) (a j : ℕ) :
    freeRunsAux (flipPair bs (leadTrue bs + j)) a =
      freeRunsAux (flipPair (dropLeadTrue bs) j) (a + leadTrue bs) := by
  induction bs generalizing a j with
  | nil =>
      simp [leadTrue, dropLeadTrue, flipPair]
  | cons b bs ih =>
      cases b
      · simp [leadTrue, dropLeadTrue]
      · rw [show leadTrue (true :: bs) + j = (leadTrue bs + j) + 1 by
          simp [leadTrue]
          omega]
        rw [flipPair_cons_succ]
        change freeRunsAux (flipPair bs (leadTrue bs + j)) (a + 1) =
          freeRunsAux (flipPair (dropLeadTrue bs) j) (a + (leadTrue bs + 1))
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (a + 1) j

lemma freeRuns_flipPair_after_lead (bs : List Bool) (j : ℕ)
    (hpos : 0 < leadTrue bs)
    (hj : j + 1 < (dropLeadTrue bs).length)
    (hjtrue : (dropLeadTrue bs)[j]'(Nat.lt_of_succ_lt hj) = true) :
    freeRuns (flipPair bs (leadTrue bs + j)) =
      leadTrue bs :: freeRuns (flipPair (dropLeadTrue bs) j) := by
  unfold freeRuns
  rw [freeRunsAux_flipPair_after_lead bs 0 j]
  have hrest0 : leadTrue (dropLeadTrue bs) = 0 := leadTrue_dropLeadTrue_eq_zero bs
  have hflip0 : leadTrue (flipPair (dropLeadTrue bs) j) = 0 :=
    leadTrue_flipPair_eq_zero_of_get_true (dropLeadTrue bs) hrest0 (Nat.lt_of_succ_lt hj)
      hjtrue
  simpa using
    freeRunsAux_eq_cons_of_leadTrue_zero (flipPair (dropLeadTrue bs) j) hpos hflip0

lemma freeRuns_eq_lead_cons (bs : List Bool) (hpos : 0 < leadTrue bs) :
    freeRuns bs = leadTrue bs :: freeRuns (dropLeadTrue bs) := by
  unfold freeRuns
  rw [freeRunsAux_zero_eq bs]
  have hsplit : splitRuns 0 (leadTrue bs) = [leadTrue bs] := by
    unfold splitRuns
    simp [Nat.ne_of_gt hpos]
  simp [hsplit]

lemma freeRuns_runMove_realize (bs : List Bool) {rs' : List ℕ}
    (hmove : RunMove (freeRuns bs) rs') :
    ∃ i, ∃ (hi : i + 1 < bs.length),
      bs[i]'(Nat.lt_of_succ_lt hi) = true ∧ bs[i + 1]'hi = true ∧
        freeRuns (flipPair bs i) = rs' := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (bs : List Bool), bs.length = n → ∀ {rs' : List ℕ},
      RunMove (freeRuns bs) rs' →
        ∃ i, ∃ (hi : i + 1 < bs.length),
          bs[i]'(Nat.lt_of_succ_lt hi) = true ∧ bs[i + 1]'hi = true ∧
            freeRuns (flipPair bs i) = rs'
  have hP : ∀ n, (∀ m < n, P m) → P n := by
    intro n ih bs hlen rs' hmove
    by_cases hlead0 : leadTrue bs = 0
    · cases bs with
      | nil =>
          rcases hmove with ⟨pre, post, m, l, r, hrs, hm2, hsplit, hrs'⟩
          simp [freeRuns, freeRunsAux] at hrs
      | cons b tail =>
          cases b
          · have htailMove : RunMove (freeRuns tail) rs' := by
              simpa [freeRuns, freeRunsAux] using hmove
            have htailLen : tail.length < n := by
              simp at hlen
              omega
            rcases ih tail.length htailLen tail rfl htailMove with
              ⟨j, hj, hjtrue, hj1true, hflip⟩
            refine ⟨j + 1, ?_, ?_, ?_, ?_⟩
            · simpa using Nat.succ_lt_succ hj
            · simpa using hjtrue
            · simpa using hj1true
            · simpa [freeRuns, freeRunsAux, flipPair_cons_succ] using hflip
          · simp [leadTrue] at hlead0
    · have hpos : 0 < leadTrue bs := Nat.pos_of_ne_zero hlead0
      have hfree := freeRuns_eq_lead_cons bs hpos
      rw [hfree] at hmove
      rcases hmove with ⟨pre, post, m, l, r, hrs, hm2, hsplit, hrs'⟩
      cases pre with
      | nil =>
          simp at hrs
          rcases hrs with ⟨hm_eq, hpost_eq⟩
          have hleadSplit : l + 2 + r = leadTrue bs := by omega
          subst m
          subst post
          simp at hrs'
          subst rs'
          have hleadLen := leadTrue_le_length bs
          have hi : l + 1 < bs.length := by omega
          have hlt0 : l < leadTrue bs := by omega
          have hlt1 : l + 1 < leadTrue bs := by omega
          refine ⟨l, hi, ?_, ?_, ?_⟩
          · exact getElem_true_of_lt_leadTrue bs l hlt0 (Nat.lt_of_succ_lt hi)
          · exact getElem_true_of_lt_leadTrue bs (l + 1) hlt1 hi
          · unfold freeRuns
            simpa using freeRunsAux_flipPair_lead bs 0 l r hleadSplit
      | cons a preTail =>
          simp at hrs
          rcases hrs with ⟨ha, htailEq⟩
          subst a
          let tailRs' : List ℕ := preTail ++ splitRuns l r ++ post
          have htailMove : RunMove (freeRuns (dropLeadTrue bs)) tailRs' :=
            ⟨preTail, post, m, l, r, htailEq, hm2, hsplit, rfl⟩
          have hrestLen : (dropLeadTrue bs).length < n := by
            have hlenDrop := dropLeadTrue_length_add bs
            omega
          rcases ih (dropLeadTrue bs).length hrestLen (dropLeadTrue bs) rfl htailMove with
            ⟨j, hj, hjtrue, hj1true, hflipTail⟩
          have hlenDrop := dropLeadTrue_length_add bs
          have hi : leadTrue bs + j + 1 < bs.length := by omega
          simp [tailRs'] at hrs'
          subst rs'
          refine ⟨leadTrue bs + j, hi, ?_, ?_, ?_⟩
          · exact (getElem_leadTrue_add bs j (Nat.lt_of_succ_lt hj) (by omega)).trans hjtrue
          · have hget := getElem_leadTrue_add bs (j + 1) hj (by omega)
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hget.trans hj1true
          · have hafter := freeRuns_flipPair_after_lead bs j hpos hj hjtrue
            simpa [tailRs', hflipTail] using hafter
  have hmain : P bs.length := Nat.strong_induction_on bs.length hP
  exact hmain bs rfl hmove

lemma freeRunsAux_sum (bs : List Bool) (r : ℕ) :
    (freeRunsAux bs r).sum = r + List.countP id bs := by
  induction bs generalizing r with
  | nil =>
      by_cases hr : r = 0 <;> simp [freeRunsAux, hr]
  | cons b bs ih =>
      cases b
      · by_cases hr : r = 0 <;> simp [freeRunsAux, ih, hr]
      · simp [freeRunsAux, ih, Nat.add_comm, Nat.add_left_comm]

lemma freeRuns_sum (bs : List Bool) : (freeRuns bs).sum = List.countP id bs := by
  simp [freeRuns, freeRunsAux_sum]

lemma bob_hot_le_self (n : ℕ) : bobValue n + 2 * hotValue n ≤ n := by
  unfold bobValue hotValue
  have hmod : n % 7 < 7 := Nat.mod_lt n (by norm_num)
  have hdiv : 7 * (n / 7) + n % 7 = n := Nat.div_add_mod n 7
  interval_cases n % 7 <;> simp at hdiv ⊢ <;> omega

lemma runBase_twoHot_le_sum (rs : List ℕ) : runBase rs + 2 * runHot rs ≤ rs.sum := by
  induction rs with
  | nil =>
      simp [runBase, runHot]
  | cons n rs ih =>
      unfold runBase runHot at ih ⊢
      simp [List.sum_cons, List.map_cons]
      have hn := bob_hot_le_self n
      omega

lemma two_half_succ_le_two_self (n : ℕ) : 2 * ((n + 1) / 2) ≤ 2 * n := by
  omega

lemma runAlice_le_sum (rs : List ℕ) : runAlice rs ≤ rs.sum := by
  unfold runAlice
  have h1 : 2 * ((runHot rs + 1) / 2) ≤ 2 * runHot rs := two_half_succ_le_two_self _
  have h2 := runBase_twoHot_le_sum rs
  omega

lemma runBob_le_sum (rs : List ℕ) : runBob rs ≤ rs.sum := by
  unfold runBob
  have h1 : 2 * (runHot rs / 2) ≤ 2 * runHot rs := by omega
  have h2 := runBase_twoHot_le_sum rs
  omega

lemma bobValue_eq_self_of_le_one {n : ℕ} (hn : n ≤ 1) : bobValue n = n := by
  interval_cases n <;> simp [bobValue]

lemma hotValue_eq_zero_of_le_one {n : ℕ} (hn : n ≤ 1) : hotValue n = 0 := by
  interval_cases n <;> simp [hotValue]

lemma runBase_eq_sum_of_le_one (rs : List ℕ) (h : ∀ n ∈ rs, n ≤ 1) :
    runBase rs = rs.sum := by
  induction rs with
  | nil =>
      simp [runBase]
  | cons n rs ih =>
      have hn : n ≤ 1 := h n (by simp)
      have hrs : ∀ m ∈ rs, m ≤ 1 := by
        intro m hm
        exact h m (by simp [hm])
      change bobValue n + runBase rs = n + rs.sum
      rw [bobValue_eq_self_of_le_one hn, ih hrs]

lemma runHot_eq_zero_of_le_one (rs : List ℕ) (h : ∀ n ∈ rs, n ≤ 1) :
    runHot rs = 0 := by
  induction rs with
  | nil =>
      simp [runHot]
  | cons n rs ih =>
      have hn : n ≤ 1 := h n (by simp)
      have hrs : ∀ m ∈ rs, m ≤ 1 := by
        intro m hm
        exact h m (by simp [hm])
      change hotValue n + runHot rs = 0
      rw [hotValue_eq_zero_of_le_one hn, ih hrs]

lemma runAlice_eq_sum_of_le_one (rs : List ℕ) (h : ∀ n ∈ rs, n ≤ 1) :
    runAlice rs = rs.sum := by
  unfold runAlice
  rw [runBase_eq_sum_of_le_one rs h, runHot_eq_zero_of_le_one rs h]
  norm_num

lemma runBob_eq_sum_of_le_one (rs : List ℕ) (h : ∀ n ∈ rs, n ≤ 1) :
    runBob rs = rs.sum := by
  unfold runBob
  rw [runBase_eq_sum_of_le_one rs h, runHot_eq_zero_of_le_one rs h]
  norm_num

lemma freeRuns_le_one_of_no_adjacent (bs : List Bool)
    (h : ∀ i (hi : i + 1 < bs.length),
      bs[i]'(Nat.lt_of_succ_lt hi) = true → bs[i + 1]'hi = false) :
    ∀ n ∈ freeRuns bs, n ≤ 1 := by
  induction bs with
  | nil =>
      simp [freeRuns, freeRunsAux]
  | cons b bs ih =>
      cases b
      · have htail : ∀ i (hi : i + 1 < bs.length),
            bs[i]'(Nat.lt_of_succ_lt hi) = true → bs[i + 1]'hi = false := by
          intro i hi htrue
          have h' := h (i + 1) (by simpa [Nat.add_assoc] using hi) (by simpa using htrue)
          simpa [Nat.add_assoc] using h'
        intro n hn
        simp [freeRuns, freeRunsAux] at hn
        exact ih htail n hn
      · cases bs with
        | nil =>
            simp [freeRuns, freeRunsAux]
        | cons c tail =>
            have hc : c = false := by
              have h' := h 0 (by simp) (by simp)
              simpa using h'
            subst c
            have htail : ∀ i (hi : i + 1 < (false :: tail).length),
                (false :: tail)[i]'(Nat.lt_of_succ_lt hi) = true →
                  (false :: tail)[i + 1]'hi = false := by
              intro i hi htrue
              cases i with
              | zero =>
                  simp at htrue
              | succ i =>
                  have hiNat : i + 2 < tail.length + 1 := by
                    simpa [Nat.add_assoc] using hi
                  have hbound : (i + 2) + 1 < (true :: false :: tail).length := by
                    simp
                    omega
                  have h' := h (i + 2) hbound (by simpa using htrue)
                  simpa [Nat.add_assoc] using h'
            intro n hn
            simp [freeRuns, freeRunsAux] at hn
            rcases hn with rfl | hn
            · omega
            · exact ih htail n (by simpa [freeRuns, freeRunsAux] using hn)

noncomputable def boardList (x : Set (Fin 2022)) : List Bool := by
  classical
  exact (List.finRange 2022).map fun i => decide (i ∉ x)

noncomputable def boardRuns (x : Set (Fin 2022)) : List ℕ :=
  freeRuns (boardList x)

noncomputable def boardAlice (x : Set (Fin 2022)) : ℕ :=
  runAlice (boardRuns x)

noncomputable def boardBob (x : Set (Fin 2022)) : ℕ :=
  runBob (boardRuns x)

lemma flipPair_length (bs : List Bool) (i : ℕ) :
    (flipPair bs i).length = bs.length := by
  induction bs generalizing i with
  | nil =>
      cases i <;> simp [flipPair]
  | cons b bs ih =>
      cases i with
      | zero =>
          cases bs <;> simp [flipPair]
      | succ i =>
          simp [flipPair_cons_succ, ih]

lemma flipPair_getElem (bs : List Bool) (i j : ℕ)
    (hi : i + 1 < bs.length) (hj : j < bs.length) :
    (flipPair bs i)[j]'(by simpa [flipPair_length] using hj) =
      if j = i ∨ j = i + 1 then false else bs[j] := by
  induction bs generalizing i j with
  | nil =>
      simp at hi
  | cons b bs ih =>
      cases i with
      | zero =>
          cases bs with
          | nil =>
              simp at hi
          | cons c tail =>
              cases j with
              | zero =>
                  simp [flipPair]
              | succ j =>
                  cases j with
                  | zero =>
                      simp [flipPair]
                  | succ j =>
                      simp [flipPair]
      | succ i =>
          cases j with
          | zero =>
              simp [flipPair_cons_succ]
          | succ j =>
              have hi' : i + 1 < bs.length := by simpa using hi
              have hj' : j < bs.length := by simpa using hj
              simpa [flipPair_cons_succ, Nat.succ_eq_add_one, Nat.add_assoc]
                using ih i j hi' hj'

lemma boardList_length (x : Set (Fin 2022)) : (boardList x).length = 2022 := by
  simp [boardList]

lemma boardList_getElem_true (x : Set (Fin 2022)) (j : ℕ)
    (hj : j < (boardList x).length) :
    (boardList x)[j] = true ↔
      (⟨j, by simpa [boardList] using hj⟩ : Fin 2022) ∉ x := by
  classical
  unfold boardList
  simp [List.getElem_map, List.getElem_finRange]

lemma boardList_union_pair_nat (x : Set (Fin 2022)) {j : ℕ} (hj : j + 1 < 2022) :
    boardList
        (x ∪ ({(⟨j, by omega⟩ : Fin 2022), (⟨j + 1, hj⟩ : Fin 2022)} : Set (Fin 2022))) =
      flipPair (boardList x) j := by
  classical
  apply List.ext_getElem
  · simp [boardList_length, flipPair_length]
  · intro k hk₁ hk₂
    have hk : k < (boardList x).length := by simpa [boardList_length] using hk₁
    have hflip := flipPair_getElem (boardList x) j k (by simpa [boardList_length] using hj) hk
    rw [hflip]
    rw [Bool.eq_iff_iff]
    rw [boardList_getElem_true]
    by_cases hkj : k = j
    · subst k
      simp
    · by_cases hkj1 : k = j + 1
      · subst k
        simp
      · have hne₀ :
          (⟨k, by simpa [boardList] using hk₁⟩ : Fin 2022) ≠ ⟨j, by omega⟩ := by
            intro h
            exact hkj (Fin.ext_iff.mp h)
        have hne₁ :
          (⟨k, by simpa [boardList] using hk₁⟩ : Fin 2022) ≠ ⟨j + 1, hj⟩ := by
            intro h
            exact hkj1 (Fin.ext_iff.mp h)
        simp [hkj, hkj1, hne₀, hne₁]
        exact (boardList_getElem_true x k hk).symm

lemma boardList_union_pair_fin (x : Set (Fin 2022)) (i : Fin 2022) (hi : i < 2021) :
    boardList (x ∪ ({i, i + 1} : Set (Fin 2022))) =
      flipPair (boardList x) i.val := by
  have hi' : i.val < 2021 := by
    rw [Fin.lt_def] at hi
    simpa using hi
  have hsucc : i.val + 1 < 2022 := by omega
  have h0 : (⟨i.val, by omega⟩ : Fin 2022) = i := Fin.ext rfl
  have h1 : (⟨i.val + 1, hsucc⟩ : Fin 2022) = i + 1 := by
    apply Fin.ext
    simpa using (Fin.val_add_one_of_lt (n := 2021) hi).symm
  simpa [h0, h1] using boardList_union_pair_nat x hsucc

lemma boardRuns_union_pair_nat_runMove (x : Set (Fin 2022)) {j : ℕ} (hj : j + 1 < 2022)
    (hjfree : (⟨j, by omega⟩ : Fin 2022) ∉ x)
    (hj1free : (⟨j + 1, hj⟩ : Fin 2022) ∉ x) :
    RunMove (boardRuns x)
      (boardRuns
        (x ∪ ({(⟨j, by omega⟩ : Fin 2022), (⟨j + 1, hj⟩ : Fin 2022)} : Set (Fin 2022)))) := by
  unfold boardRuns freeRuns
  rw [boardList_union_pair_nat x hj]
  refine freeRunsAux_flipPair_runMove (boardList x) j 0 ?_ ?_ ?_
  · simpa [boardList_length] using hj
  · exact (boardList_getElem_true x j (by simpa [boardList_length] using (lt_trans (Nat.lt_succ_self j) hj))).2 hjfree
  · exact (boardList_getElem_true x (j + 1) (by simpa [boardList_length] using hj)).2 hj1free

lemma boardRuns_union_pair_fin_runMove (x : Set (Fin 2022)) (i : Fin 2022) (hi : i < 2021)
    (hifree : i ∉ x) (hi1free : i + 1 ∉ x) :
    RunMove (boardRuns x) (boardRuns (x ∪ ({i, i + 1} : Set (Fin 2022)))) := by
  have hi' : i.val < 2021 := by
    rw [Fin.lt_def] at hi
    simpa using hi
  have hsucc : i.val + 1 < 2022 := by omega
  have h0 : (⟨i.val, by omega⟩ : Fin 2022) = i := Fin.ext rfl
  have h1 : (⟨i.val + 1, hsucc⟩ : Fin 2022) = i + 1 := by
    apply Fin.ext
    simpa using (Fin.val_add_one_of_lt (n := 2021) hi).symm
  simpa [h0, h1] using
    boardRuns_union_pair_nat_runMove x (j := i.val) hsucc (by simpa [h0] using hifree)
      (by simpa [h1] using hi1free)

lemma boardRuns_runMove_realize (x : Set (Fin 2022)) {rs' : List ℕ}
    (hmove : RunMove (boardRuns x) rs') :
    ∃ i : Fin 2022, ∃ hi : i < 2021, i ∉ x ∧ i + 1 ∉ x ∧
      boardRuns (x ∪ ({i, i + 1} : Set (Fin 2022))) = rs' := by
  rcases freeRuns_runMove_realize (boardList x) (by simpa [boardRuns] using hmove) with
    ⟨j, hj, hjtrue, hj1true, hflip⟩
  have hj2022 : j < 2022 := by
    have : j + 1 < 2022 := by simpa [boardList_length] using hj
    omega
  have hjsucc : j + 1 < 2022 := by simpa [boardList_length] using hj
  let i : Fin 2022 := ⟨j, hj2022⟩
  have hi : i < 2021 := by
    rw [Fin.lt_def]
    simpa [i] using (by omega : j < 2021)
  have hfree : i ∉ x := by
    simpa [i] using
      (boardList_getElem_true x j (by simpa [boardList_length] using hj2022)).1 hjtrue
  have hsucc_eq : (⟨j + 1, hjsucc⟩ : Fin 2022) = i + 1 := by
    apply Fin.ext
    simpa [i] using (Fin.val_add_one_of_lt (n := 2021) hi).symm
  have hfree1 : i + 1 ∉ x := by
    have hnat :
        (⟨j + 1, hjsucc⟩ : Fin 2022) ∉ x :=
      (boardList_getElem_true x (j + 1) (by simpa [boardList_length] using hjsucc)).1
        hj1true
    simpa [hsucc_eq] using hnat
  refine ⟨i, hi, hfree, hfree1, ?_⟩
  rw [boardRuns, boardList_union_pair_fin x i hi]
  simpa [i] using hflip

lemma boardRuns_has_move_of_exists_pair (x : Set (Fin 2022))
    (hplace : ∃ i : Fin 2022, i < 2021 ∧ i ∉ x ∧ i + 1 ∉ x) :
    ∃ pre post m, boardRuns x = pre ++ m :: post ∧ 2 ≤ m := by
  rcases hplace with ⟨i, hi, hifree, hi1free⟩
  rcases boardRuns_union_pair_fin_runMove x i hi hifree hi1free with
    ⟨pre, post, m, l, r, hrs, hm2, hsplit, hrs'⟩
  exact ⟨pre, post, m, hrs, hm2⟩

lemma boardList_countP (x : Set (Fin 2022)) :
    List.countP id (boardList x) = xᶜ.ncard := by
  classical
  unfold boardList
  rw [List.countP_map]
  change List.countP (fun i : Fin 2022 => decide (i ∉ x)) (List.finRange 2022) =
    xᶜ.ncard
  rw [List.countP_eq_length_filter]
  let l := List.filter (fun i : Fin 2022 => decide (i ∉ x)) (List.finRange 2022)
  have hnodup : l.Nodup := (List.nodup_finRange 2022).filter _
  have hcard : l.length = l.toFinset.card := by
    rw [List.toFinset_card_of_nodup hnodup]
  change l.length = xᶜ.ncard
  rw [hcard]
  let hxc : (xᶜ).Finite := Set.toFinite (xᶜ)
  have hfin : l.toFinset = hxc.toFinset := by
    ext i
    simp [l, List.toFinset_finRange]
  rw [hfin]
  exact (Set.ncard_eq_toFinset_card (xᶜ) hxc).symm

lemma boardRuns_sum (x : Set (Fin 2022)) : (boardRuns x).sum = xᶜ.ncard := by
  rw [boardRuns, freeRuns_sum, boardList_countP]

lemma boardList_no_adjacent_of_terminal (x : Set (Fin 2022))
    (hterm : ∀ i < 2021, i ∉ x → i + 1 ∈ x) :
    ∀ j (hj : j + 1 < (boardList x).length),
      (boardList x)[j]'(Nat.lt_of_succ_lt hj) = true →
        (boardList x)[j + 1]'hj = false := by
  intro j hj htrue
  have hj2021 : j < 2021 := by
    have : j + 1 < 2022 := by simpa [boardList_length] using hj
    omega
  have hj2022 : j < 2022 := by omega
  have hsucc : j + 1 < 2022 := by simpa [boardList_length] using hj
  let i : Fin 2022 := ⟨j, hj2022⟩
  have hi : i < 2021 := by
    rw [Fin.lt_def]
    simpa [i] using hj2021
  have hfree : i ∉ x := by
    simpa [i] using
      (boardList_getElem_true x j (by simpa [boardList_length] using hj2022)).1 htrue
  have hcovered_fin : i + 1 ∈ x := hterm i hi hfree
  have hsucc_eq : (⟨j + 1, hsucc⟩ : Fin 2022) = i + 1 := by
    apply Fin.ext
    simpa [i] using (Fin.val_add_one_of_lt (n := 2021) hi).symm
  rw [Bool.eq_false_iff]
  intro hnext
  have hfree_next : (⟨j + 1, hsucc⟩ : Fin 2022) ∉ x :=
    (boardList_getElem_true x (j + 1) (by simpa [boardList_length] using hsucc)).1 hnext
  exact hfree_next (by simpa [hsucc_eq] using hcovered_fin)

lemma boardRuns_le_one_of_terminal (x : Set (Fin 2022))
    (hterm : ∀ i < 2021, i ∉ x → i + 1 ∈ x) :
    ∀ n ∈ boardRuns x, n ≤ 1 := by
  unfold boardRuns
  exact freeRuns_le_one_of_no_adjacent (boardList x) (boardList_no_adjacent_of_terminal x hterm)

lemma boardAlice_eq_uncovered_of_terminal (x : Set (Fin 2022))
    (hterm : ∀ i < 2021, i ∉ x → i + 1 ∈ x) :
    boardAlice x = xᶜ.ncard := by
  rw [boardAlice, runAlice_eq_sum_of_le_one (boardRuns x) (boardRuns_le_one_of_terminal x hterm),
    boardRuns_sum]

lemma boardBob_eq_uncovered_of_terminal (x : Set (Fin 2022))
    (hterm : ∀ i < 2021, i ∉ x → i + 1 ∈ x) :
    boardBob x = xᶜ.ncard := by
  rw [boardBob, runBob_eq_sum_of_le_one (boardRuns x) (boardRuns_le_one_of_terminal x hterm),
    boardRuns_sum]

lemma exists_validMove_alice
    {IsValidMove : Set (Fin 2022) → Set (Fin 2022) → Prop}
    (IsValidMove_def : ∀ x y, IsValidMove x y ↔
      (x = y ∧ ∀ i < 2021, i ∉ x → i + 1 ∈ x) ∨
      ∃ i < 2021, i ∉ x ∧ i + 1 ∉ x ∧ y = x ∪ {i, i + 1})
    (x : Set (Fin 2022)) :
    ∃ y, IsValidMove x y ∧ boardAlice x ≤ boardBob y := by
  by_cases hplace : ∃ i : Fin 2022, i < 2021 ∧ i ∉ x ∧ i + 1 ∉ x
  · have hrun := boardRuns_has_move_of_exists_pair x hplace
    rcases runMove_alice_exists (boardRuns x) hrun with ⟨rs', hrunMove, hineq⟩
    rcases boardRuns_runMove_realize x hrunMove with ⟨i, hi, hifree, hi1free, hboard⟩
    refine ⟨x ∪ ({i, i + 1} : Set (Fin 2022)), ?_, ?_⟩
    · rw [IsValidMove_def]
      exact Or.inr ⟨i, hi, hifree, hi1free, rfl⟩
    · rw [boardAlice, boardBob, hboard]
      exact hineq
  · have hterm : ∀ i < 2021, i ∉ x → i + 1 ∈ x := by
      intro i hi hifree
      by_contra hi1free
      exact hplace ⟨i, hi, hifree, hi1free⟩
    refine ⟨x, ?_, ?_⟩
    · rw [IsValidMove_def]
      exact Or.inl ⟨rfl, hterm⟩
    · rw [boardAlice_eq_uncovered_of_terminal x hterm,
        boardBob_eq_uncovered_of_terminal x hterm]

lemma exists_validMove_bob
    {IsValidMove : Set (Fin 2022) → Set (Fin 2022) → Prop}
    (IsValidMove_def : ∀ x y, IsValidMove x y ↔
      (x = y ∧ ∀ i < 2021, i ∉ x → i + 1 ∈ x) ∨
      ∃ i < 2021, i ∉ x ∧ i + 1 ∉ x ∧ y = x ∪ {i, i + 1})
    (x : Set (Fin 2022)) :
    ∃ y, IsValidMove x y ∧ boardAlice y ≤ boardBob x := by
  by_cases hplace : ∃ i : Fin 2022, i < 2021 ∧ i ∉ x ∧ i + 1 ∉ x
  · have hrun := boardRuns_has_move_of_exists_pair x hplace
    rcases runMove_bob_exists (boardRuns x) hrun with ⟨rs', hrunMove, hineq⟩
    rcases boardRuns_runMove_realize x hrunMove with ⟨i, hi, hifree, hi1free, hboard⟩
    refine ⟨x ∪ ({i, i + 1} : Set (Fin 2022)), ?_, ?_⟩
    · rw [IsValidMove_def]
      exact Or.inr ⟨i, hi, hifree, hi1free, rfl⟩
    · rw [boardAlice, boardBob, hboard]
      exact hineq
  · have hterm : ∀ i < 2021, i ∉ x → i + 1 ∈ x := by
      intro i hi hifree
      by_contra hi1free
      exact hplace ⟨i, hi, hifree, hi1free⟩
    refine ⟨x, ?_, ?_⟩
    · rw [IsValidMove_def]
      exact Or.inl ⟨rfl, hterm⟩
    · rw [boardAlice_eq_uncovered_of_terminal x hterm,
        boardBob_eq_uncovered_of_terminal x hterm]

lemma boardAlice_le_uncovered (x : Set (Fin 2022)) : boardAlice x ≤ xᶜ.ncard := by
  rw [boardAlice, ← boardRuns_sum x]
  exact runAlice_le_sum (boardRuns x)

lemma boardBob_le_uncovered (x : Set (Fin 2022)) : boardBob x ≤ xᶜ.ncard := by
  rw [boardBob, ← boardRuns_sum x]
  exact runBob_le_sum (boardRuns x)

lemma validMove_alice_upper
    {IsValidMove : Set (Fin 2022) → Set (Fin 2022) → Prop}
    (IsValidMove_def : ∀ x y, IsValidMove x y ↔
      (x = y ∧ ∀ i < 2021, i ∉ x → i + 1 ∈ x) ∨
      ∃ i < 2021, i ∉ x ∧ i + 1 ∉ x ∧ y = x ∪ {i, i + 1})
    {x y : Set (Fin 2022)} (hxy : IsValidMove x y) :
    boardBob y ≤ boardAlice x := by
  rw [IsValidMove_def] at hxy
  rcases hxy with hpass | hplace
  · rcases hpass with ⟨rfl, _⟩
    exact runBob_le_runAlice (boardRuns x)
  · rcases hplace with ⟨i, hi, hifree, hi1free, rfl⟩
    simpa [boardBob, boardAlice] using
      runMove_alice_upper (boardRuns_union_pair_fin_runMove x i hi hifree hi1free)

lemma validMove_bob_lower
    {IsValidMove : Set (Fin 2022) → Set (Fin 2022) → Prop}
    (IsValidMove_def : ∀ x y, IsValidMove x y ↔
      (x = y ∧ ∀ i < 2021, i ∉ x → i + 1 ∈ x) ∨
      ∃ i < 2021, i ∉ x ∧ i + 1 ∉ x ∧ y = x ∪ {i, i + 1})
    {x y : Set (Fin 2022)} (hxy : IsValidMove x y) :
    boardBob x ≤ boardAlice y := by
  rw [IsValidMove_def] at hxy
  rcases hxy with hpass | hplace
  · rcases hpass with ⟨rfl, _⟩
    exact runBob_le_runAlice (boardRuns x)
  · rcases hplace with ⟨i, hi, hifree, hi1free, rfl⟩
    simpa [boardBob, boardAlice] using
      runMove_bob_lower (boardRuns_union_pair_fin_runMove x i hi hifree hi1free)

noncomputable def aliceWeight (x : Set (Fin 2022)) : ℕ :=
  runWeight aliceValue (boardList x) 0

noncomputable def bobWeight (x : Set (Fin 2022)) : ℕ :=
  runWeight bobValue (boardList x) 0

lemma aliceWeight_eq (x : Set (Fin 2022)) :
    aliceWeight x = ((boardRuns x).map aliceValue).sum := by
  rw [aliceWeight, boardRuns, freeRuns, runWeight_eq_freeRunsAux]

lemma bobWeight_eq (x : Set (Fin 2022)) :
    bobWeight x = ((boardRuns x).map bobValue).sum := by
  rw [bobWeight, boardRuns, freeRuns, runWeight_eq_freeRunsAux]

lemma aliceWeight_le_uncovered (x : Set (Fin 2022)) : aliceWeight x ≤ xᶜ.ncard := by
  rw [aliceWeight_eq, ← boardRuns_sum x]
  induction boardRuns x with
  | nil =>
      simp
  | cons n rs ih =>
      simp [List.sum_cons, List.map_cons]
      have hn := aliceValue_le_self n
      omega

lemma bobWeight_le_uncovered (x : Set (Fin 2022)) : bobWeight x ≤ xᶜ.ncard := by
  rw [bobWeight_eq, ← boardRuns_sum x]
  induction boardRuns x with
  | nil =>
      simp
  | cons n rs ih =>
      simp [List.sum_cons, List.map_cons]
      have hn := bobValue_le_self n
      omega

lemma validMove_simple_alice_upper
    {IsValidMove : Set (Fin 2022) → Set (Fin 2022) → Prop}
    (IsValidMove_def : ∀ x y, IsValidMove x y ↔
      (x = y ∧ ∀ i < 2021, i ∉ x → i + 1 ∈ x) ∨
      ∃ i < 2021, i ∉ x ∧ i + 1 ∉ x ∧ y = x ∪ {i, i + 1})
    {x y : Set (Fin 2022)} (hxy : IsValidMove x y) :
    bobWeight y ≤ aliceWeight x := by
  rw [IsValidMove_def] at hxy
  rcases hxy with hpass | hplace
  · rcases hpass with ⟨rfl, _⟩
    rw [aliceWeight_eq, bobWeight_eq]
    exact map_bobValue_sum_le_aliceValue_sum (boardRuns x)
  · rcases hplace with ⟨i, hi, hifree, hi1free, rfl⟩
    rw [aliceWeight_eq, bobWeight_eq]
    exact runMove_simple_alice_upper (boardRuns_union_pair_fin_runMove x i hi hifree hi1free)

lemma validMove_simple_bob_lower
    {IsValidMove : Set (Fin 2022) → Set (Fin 2022) → Prop}
    (IsValidMove_def : ∀ x y, IsValidMove x y ↔
      (x = y ∧ ∀ i < 2021, i ∉ x → i + 1 ∈ x) ∨
      ∃ i < 2021, i ∉ x ∧ i + 1 ∉ x ∧ y = x ∪ {i, i + 1})
    {x y : Set (Fin 2022)} (hxy : IsValidMove x y) :
    bobWeight x ≤ aliceWeight y := by
  rw [IsValidMove_def] at hxy
  rcases hxy with hpass | hplace
  · rcases hpass with ⟨rfl, _⟩
    rw [aliceWeight_eq, bobWeight_eq]
    exact map_bobValue_sum_le_aliceValue_sum (boardRuns x)
  · rcases hplace with ⟨i, hi, hifree, hi1free, rfl⟩
    rw [aliceWeight_eq, bobWeight_eq]
    exact runMove_simple_bob_lower (boardRuns_union_pair_fin_runMove x i hi hifree hi1free)

def Terminal (x : Set (Fin 2022)) : Prop :=
  ∀ i < 2021, i ∉ x → i + 1 ∈ x

def HasPlace (x : Set (Fin 2022)) : Prop :=
  ∃ i : Fin 2022, i < 2021 ∧ i ∉ x ∧ i + 1 ∉ x

lemma not_terminal_iff_hasPlace (x : Set (Fin 2022)) : ¬ Terminal x ↔ HasPlace x := by
  constructor
  · intro hterm
    by_contra hplace
    apply hterm
    intro i hi hifree
    by_contra hi1free
    exact hplace ⟨i, hi, hifree, hi1free⟩
  · rintro ⟨i, hi, hifree, hi1free⟩ hterm
    exact hi1free (hterm i hi hifree)

lemma validMove_eq_self_of_terminal
    {IsValidMove : Set (Fin 2022) → Set (Fin 2022) → Prop}
    (IsValidMove_def : ∀ x y, IsValidMove x y ↔
      (x = y ∧ ∀ i < 2021, i ∉ x → i + 1 ∈ x) ∨
      ∃ i < 2021, i ∉ x ∧ i + 1 ∉ x ∧ y = x ∪ {i, i + 1})
    {x y : Set (Fin 2022)} (hterm : Terminal x) (hxy : IsValidMove x y) :
    y = x := by
  rw [IsValidMove_def] at hxy
  rcases hxy with hpass | hplace
  · exact hpass.1.symm
  · rcases hplace with ⟨i, hi, hifree, hi1free, hy⟩
    exact (hi1free (hterm i hi hifree)).elim

lemma validMove_uncovered_lt_of_hasPlace
    {IsValidMove : Set (Fin 2022) → Set (Fin 2022) → Prop}
    (IsValidMove_def : ∀ x y, IsValidMove x y ↔
      (x = y ∧ ∀ i < 2021, i ∉ x → i + 1 ∈ x) ∨
      ∃ i < 2021, i ∉ x ∧ i + 1 ∉ x ∧ y = x ∪ {i, i + 1})
    {x y : Set (Fin 2022)} (hxy : IsValidMove x y) (hplacex : HasPlace x) :
    yᶜ.ncard < xᶜ.ncard := by
  rw [IsValidMove_def] at hxy
  rcases hxy with hpass | hplace
  · rcases hpass with ⟨rfl, hterm⟩
    rcases hplacex with ⟨i, hi, hifree, hi1free⟩
    exact (hi1free (hterm i hi hifree)).elim
  · rcases hplace with ⟨i, hi, hifree, hi1free, rfl⟩
    have hss : (x ∪ ({i, i + 1} : Set (Fin 2022)))ᶜ ⊂ xᶜ := by
      constructor
      · intro a ha hx
        exact ha (Or.inl hx)
      · intro hsub
        have hixc : i ∈ xᶜ := by simpa using hifree
        have hnot : i ∉ (x ∪ ({i, i + 1} : Set (Fin 2022)))ᶜ := by simp
        exact hnot (hsub hixc)
    exact Set.ncard_lt_ncard hss (Set.toFinite _)

noncomputable def playState (alice bob : Set (Fin 2022) → Set (Fin 2022)) :
    ℕ → Set (Fin 2022)
  | 0 => ∅
  | n + 1 => if Even n then alice (playState alice bob n) else bob (playState alice bob n)

lemma playState_transition
    {IsValidMove : Set (Fin 2022) → Set (Fin 2022) → Prop}
    {alice bob : Set (Fin 2022) → Set (Fin 2022)}
    (halice : ∀ x, IsValidMove x (alice x))
    (hbob : ∀ x, IsValidMove x (bob x)) (n : ℕ) :
    IsValidMove (playState alice bob n) (playState alice bob (n + 1)) := by
  simp [playState]
  by_cases hn : Even n
  · simp [hn, halice]
  · simp [hn, hbob]

lemma playState_terminal_persist
    {IsValidMove : Set (Fin 2022) → Set (Fin 2022) → Prop}
    (IsValidMove_def : ∀ x y, IsValidMove x y ↔
      (x = y ∧ ∀ i < 2021, i ∉ x → i + 1 ∈ x) ∨
      ∃ i < 2021, i ∉ x ∧ i + 1 ∉ x ∧ y = x ∪ {i, i + 1})
    {alice bob : Set (Fin 2022) → Set (Fin 2022)}
    (halice : ∀ x, IsValidMove x (alice x))
    (hbob : ∀ x, IsValidMove x (bob x)) :
    ∀ k m, Terminal (playState alice bob k) →
      Terminal (playState alice bob (k + m)) := by
  intro k m
  induction m with
  | zero =>
      simpa
  | succ m ih =>
      intro hterm
      have hterm_m : Terminal (playState alice bob (k + m)) := ih hterm
      have hmove : IsValidMove (playState alice bob (k + m))
          (playState alice bob (k + m + 1)) :=
        playState_transition halice hbob (k + m)
      have heq := validMove_eq_self_of_terminal IsValidMove_def hterm_m hmove
      have hnext : Terminal (playState alice bob (k + m + 1)) := by
        simpa [heq] using hterm_m
      simpa [Nat.add_assoc] using hnext

lemma chain_getElem {α : Type*} {R : α → α → Prop} {l : List α}
    (hchain : l.Chain' R) {i : ℕ} (hi : i + 1 < l.length) :
    R (l[i]'(Nat.lt_of_succ_lt hi)) (l[i + 1]'hi) := by
  induction l generalizing i with
  | nil =>
      simp at hi
  | cons a t ih =>
      cases i with
      | zero =>
          cases t with
          | nil =>
              simp at hi
          | cons b rest =>
              exact (List.chain'_cons.mp hchain).1
      | succ i =>
          have htail : t.Chain' R := List.Chain'.tail hchain
          have hi' : i + 1 < t.length := by simpa using hi
          simpa using ih htail hi'

lemma chain_ofFn {α : Type*} {R : α → α → Prop} {n : ℕ}
    {f : Fin (n + 1) → α}
    (h : ∀ i (hi : i + 1 < n + 1),
      R (f ⟨i, by omega⟩) (f ⟨i + 1, hi⟩)) :
    (List.ofFn f).Chain' R := by
  induction n with
  | zero =>
      rw [List.ofFn_succ]
      exact List.IsChain.singleton (f 0)
  | succ n ih =>
      rw [List.ofFn_succ]
      apply List.IsChain.cons
      · apply ih
        intro i hi
        have hrel := h (i + 1) (by omega)
        simpa using hrel
      · intro y hy
        simp at hy
        subst y
        simpa using h 0 (by omega)

lemma leadTrue_replicate_true (n : ℕ) :
    leadTrue (List.replicate n true) = n := by
  induction n with
  | zero =>
      simp [leadTrue]
  | succ n ih =>
      change leadTrue (true :: List.replicate n true) = n + 1
      simp [leadTrue, ih]

lemma dropLeadTrue_replicate_true (n : ℕ) :
    dropLeadTrue (List.replicate n true) = [] := by
  induction n with
  | zero =>
      simp [dropLeadTrue]
  | succ n ih =>
      change dropLeadTrue (true :: List.replicate n true) = []
      simp [dropLeadTrue, ih]

lemma freeRuns_replicate_true {n : ℕ} (hn : 0 < n) :
    freeRuns (List.replicate n true) = [n] := by
  unfold freeRuns
  rw [freeRunsAux_zero_eq]
  simp [leadTrue_replicate_true, dropLeadTrue_replicate_true, splitRuns, freeRunsAux,
    Nat.ne_of_gt hn]

lemma boardList_empty :
    boardList (∅ : Set (Fin 2022)) = List.replicate 2022 true := by
  classical
  apply List.ext_getElem
  · simp [boardList]
  · intro i hi₁ hi₂
    simp [boardList, List.getElem_map, List.getElem_finRange]

lemma boardRuns_empty :
    boardRuns (∅ : Set (Fin 2022)) = [2022] := by
  rw [boardRuns, boardList_empty, freeRuns_replicate_true (by norm_num)]

lemma boardAlice_empty : boardAlice (∅ : Set (Fin 2022)) = 290 := by
  rw [boardAlice, boardRuns_empty]
  norm_num [runAlice, runBase, runHot, bobValue, hotValue]

end Putnam2022A5

open Putnam2022A5

/--
Alice and Bob play a game on a board consisting of one row of 2022 consecutive squares. They take turns placing tiles that cover two adjacent squares, with Alice going first. By rule, a tile must not cover a square that is already covered by another tile. The game ends when no tile can be placed according to this rule. Alice's goal is to maximize the number of uncovered squares when the game ends; Bob's goal is to minimize it. What is the greatest number of uncovered squares that Alice can ensure at the end of the game, no matter how Bob plays?
-/
theorem putnam_2022_a5
    (IsValidMove : Set (Fin 2022) → Set (Fin 2022) → Prop)
    (IsValidMove_def : ∀ x y, IsValidMove x y ↔
      (x = y ∧ ∀ i < 2021, i ∉ x → i + 1 ∈ x) ∨
      ∃ i < 2021, i ∉ x ∧ i + 1 ∉ x ∧ y = x ∪ {i, i + 1})
    (IsValidGame : List (Set (Fin 2022)) → Prop)
    (IsValidGame_def : ∀ g, IsValidGame g ↔ (∃ gt, g = ∅ :: gt) ∧ g.Chain' IsValidMove)
    (ConformsToStrategy : List (Set (Fin 2022)) → (Set (Fin 2022) → Set (Fin 2022)) → Prop)
    (ConformsToStrategy_def : ∀ g s, ConformsToStrategy g s ↔
      ∀ (i) (h : i + 1 < g.length), Even i → g[i + 1] = s g[i]) :
    IsGreatest
      {n | ∃ s, (∀ x, IsValidMove x (s x)) ∧ ∀ g,
        IsValidGame g → ConformsToStrategy g s → ∃ gh x, g = gh ++ [x] ∧ n ≤ xᶜ.ncard}
      putnam_2022_a5_solution :=
by
  classical
  constructor
  · let s : Set (Fin 2022) → Set (Fin 2022) :=
      fun x => Classical.choose (exists_validMove_alice IsValidMove_def x)
    have hs : ∀ x, IsValidMove x (s x) ∧ boardAlice x ≤ boardBob (s x) := by
      intro x
      exact Classical.choose_spec (exists_validMove_alice IsValidMove_def x)
    refine ⟨s, ?_, ?_⟩
    · intro x
      exact (hs x).1
    · intro g hgvalid hgconf
      rw [IsValidGame_def] at hgvalid
      rcases hgvalid with ⟨⟨gt, rfl⟩, hchain⟩
      rw [ConformsToStrategy_def] at hgconf
      let G : List (Set (Fin 2022)) := ∅ :: gt
      have hInv : ∀ i (hi : i < G.length),
          if Even i then 290 ≤ boardAlice (G[i]'hi) else 290 ≤ boardBob (G[i]'hi) := by
        intro i
        induction i with
        | zero =>
            intro hi
            simp [G, boardAlice_empty]
        | succ i ih =>
            intro hi
            have hiPrev : i < G.length := by omega
            have hiStep : i + 1 < G.length := hi
            have hprev := ih hiPrev
            by_cases he : Even i
            · have hprevA : 290 ≤ boardAlice (G[i]'hiPrev) := by
                simpa [he] using hprev
              have hconfStep : G[i + 1] = s G[i] := hgconf i hiStep he
              have hnext : 290 ≤ boardBob (G[i + 1]'hiStep) := by
                rw [hconfStep]
                exact le_trans hprevA (hs (G[i]'hiPrev)).2
              have hnot : ¬ Even (i + 1) := by
                intro hsucc
                exact (Nat.even_add_one.mp hsucc) he
              simpa [hnot] using hnext
            · have hprevB : 290 ≤ boardBob (G[i]'hiPrev) := by
                simpa [he] using hprev
              have hrel : IsValidMove (G[i]'hiPrev) (G[i + 1]'hiStep) :=
                chain_getElem hchain hiStep
              have hle := validMove_bob_lower IsValidMove_def hrel
              have hnext : 290 ≤ boardAlice (G[i + 1]'hiStep) := le_trans hprevB hle
              have hsucc : Even (i + 1) := Nat.even_add_one.mpr he
              simpa [hsucc] using hnext
      have hne : G ≠ [] := by simp [G]
      refine ⟨G.dropLast, G.getLast hne, ?_, ?_⟩
      · exact (List.dropLast_append_getLast hne).symm
      · change 290 ≤ (G.getLast hne)ᶜ.ncard
        have hlastIndex : G.length - 1 < G.length := by
          simp [G]
        have hlast := hInv (G.length - 1) hlastIndex
        have hget : G.getLast hne = G[G.length - 1]'hlastIndex :=
          List.getLast_eq_getElem hne
        by_cases he : Even (G.length - 1)
        · have hA : 290 ≤ boardAlice (G.getLast hne) := by
            simpa [hget, he] using hlast
          exact le_trans hA (boardAlice_le_uncovered _)
        · have hB : 290 ≤ boardBob (G.getLast hne) := by
            simpa [hget, he] using hlast
          exact le_trans hB (boardBob_le_uncovered _)
  · intro n hn
    rcases hn with ⟨s, hsvalid, hguarantee⟩
    let t : Set (Fin 2022) → Set (Fin 2022) :=
      fun x => Classical.choose (exists_validMove_bob IsValidMove_def x)
    have ht : ∀ x, IsValidMove x (t x) ∧ boardAlice (t x) ≤ boardBob x := by
      intro x
      exact Classical.choose_spec (exists_validMove_bob IsValidMove_def x)
    have htvalid : ∀ x, IsValidMove x (t x) := fun x => (ht x).1
    let st : ℕ → Set (Fin 2022) := playState s t
    have htrans : ∀ k, IsValidMove (st k) (st (k + 1)) := by
      intro k
      simpa [st] using playState_transition hsvalid htvalid k
    have hSmall : ∀ k, k ≤ 2023 →
        if Even k then boardAlice (st k) ≤ 290 else boardBob (st k) ≤ 290 := by
      intro k hk
      induction k with
      | zero =>
          simp [st, playState, boardAlice_empty]
      | succ k ih =>
          have hprev := ih (by omega)
          by_cases he : Even k
          · have hprevA : boardAlice (st k) ≤ 290 := by
              simpa [he] using hprev
            have hstate : st (k + 1) = s (st k) := by
              simp [st, playState, he]
            have hnext : boardBob (st (k + 1)) ≤ 290 := by
              rw [hstate]
              exact le_trans (validMove_alice_upper IsValidMove_def (hsvalid (st k))) hprevA
            have hnot : ¬ Even (k + 1) := by
              intro hsucc
              exact (Nat.even_add_one.mp hsucc) he
            simpa [hnot] using hnext
          · have hprevB : boardBob (st k) ≤ 290 := by
              simpa [he] using hprev
            have hstate : st (k + 1) = t (st k) := by
              simp [st, playState, he]
            have hnext : boardAlice (st (k + 1)) ≤ 290 := by
              rw [hstate]
              exact le_trans (ht (st k)).2 hprevB
            have hsucc : Even (k + 1) := Nat.even_add_one.mpr he
            simpa [hsucc] using hnext
    have hterminal : Terminal (st 2023) := by
      by_contra hnotTerminal
      have hplaceFinal : HasPlace (st 2023) :=
        (not_terminal_iff_hasPlace (st 2023)).1 hnotTerminal
      have hplaceAll : ∀ k, k ≤ 2023 → HasPlace (st k) := by
        intro k hk
        by_contra hnotPlace
        have htermk : Terminal (st k) := by
          by_contra hnotTerm
          exact hnotPlace ((not_terminal_iff_hasPlace (st k)).1 hnotTerm)
        have hpersist := playState_terminal_persist IsValidMove_def hsvalid htvalid k (2023 - k)
          (by simpa [st] using htermk)
        have hsum : k + (2023 - k) = 2023 := by omega
        have htermFinal : Terminal (st 2023) := by
          simpa [st, hsum] using hpersist
        exact hnotTerminal htermFinal
      have hdec : ∀ k, k < 2023 → (st (k + 1))ᶜ.ncard < (st k)ᶜ.ncard := by
        intro k hk
        exact validMove_uncovered_lt_of_hasPlace IsValidMove_def (htrans k)
          (hplaceAll k (by omega))
      have hbound : ∀ k, k ≤ 2023 → (st k)ᶜ.ncard + k ≤ 2022 := by
        intro k hk
        induction k with
        | zero =>
            simp [st, playState]
        | succ k ih =>
            have hprev := ih (by omega)
            have hlt := hdec k (by omega)
            omega
      have hbad := hbound 2023 (by omega)
      omega
    have hFinalSmall : (st 2023)ᶜ.ncard ≤ 290 := by
      have hsmall := hSmall 2023 (by omega)
      have hodd : ¬ Even 2023 := by norm_num [Nat.even_iff]
      have hb : boardBob (st 2023) ≤ 290 := by
        simpa [hodd] using hsmall
      have heq := boardBob_eq_uncovered_of_terminal (st 2023) hterminal
      omega
    let f : Fin 2024 → Set (Fin 2022) := fun k => st k.val
    let g : List (Set (Fin 2022)) := List.ofFn f
    have hgvalid : IsValidGame g := by
      rw [IsValidGame_def]
      constructor
      · refine ⟨List.ofFn (fun i : Fin 2023 => f i.succ), ?_⟩
        change List.ofFn f = ∅ :: List.ofFn (fun i : Fin 2023 => f i.succ)
        rw [List.ofFn_succ]
        rfl
      · dsimp [g]
        apply chain_ofFn
        intro i hi
        change IsValidMove (st i) (st (i + 1))
        exact htrans i
    have hgconf : ConformsToStrategy g s := by
      rw [ConformsToStrategy_def]
      intro i hi he
      have hglen : g.length = 2024 := by
        change (List.ofFn f).length = 2024
        exact List.length_ofFn
      have hi2024 : i + 1 < 2024 := by omega
      have hi0 : i < 2024 := by omega
      have hget1 : g[i + 1] = st (i + 1) := by
        change (List.ofFn f)[i + 1] = st (i + 1)
        rw [List.getElem_ofFn (f := f) (i := i + 1)
          (h := by rwa [List.length_ofFn])]
      have hget0 : g[i] = st i := by
        change (List.ofFn f)[i] = st i
        rw [List.getElem_ofFn (f := f) (i := i)
          (h := by rwa [List.length_ofFn])]
      rw [hget1, hget0]
      simp [st, playState, he]
    rcases hguarantee g hgvalid hgconf with ⟨gh, x, hgx, hnx⟩
    have hgne : g ≠ [] := by
      intro hnil
      have hlen := congrArg List.length hnil
      change (List.ofFn f).length = 0 at hlen
      rw [List.length_ofFn] at hlen
      norm_num at hlen
    have hxlast : x = g.getLast hgne := by
      have hoptLast : g.getLast? = some (g.getLast hgne) := List.getLast?_eq_getLast hgne
      have hoptX : g.getLast? = some x := by
        rw [hgx, List.getLast?_concat]
      rw [hoptLast] at hoptX
      exact (Option.some.inj hoptX).symm
    have hlast : g.getLast hgne = st 2023 := by
      rw [List.getLast_ofFn]
    have hx : x = st 2023 := by rw [hxlast, hlast]
    rw [hx] at hnx
    change n ≤ 290
    exact le_trans hnx hFinalSmall
