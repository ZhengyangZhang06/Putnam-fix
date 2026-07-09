import Mathlib

set_option maxRecDepth 10000

namespace Putnam2022A5

def pRun (k : ℕ) : ℕ :=
  k / 7 + if k % 7 = 1 ∨ k % 7 = 3 ∨ k % 7 = 5 then 1 else 0

@[simp] lemma pRun_zero : pRun 0 = 0 := by
  norm_num [pRun]

@[simp] def scoreAux (v : ℕ → ℕ) : ℕ → List Bool → ℕ
  | r, [] => v r
  | r, true :: xs => v r + scoreAux v 0 xs
  | r, false :: xs => scoreAux v (r + 1) xs

def score (v : ℕ → ℕ) (xs : List Bool) : ℕ :=
  scoreAux v 0 xs

def ListMove (xs ys : List Bool) : Prop :=
  ∃ pre post, xs = pre ++ (false :: false :: post) ∧
    ys = pre ++ (true :: true :: post)

@[simp] def HasPair : List Bool → Prop
  | false :: false :: _ => True
  | _ :: xs => HasPair xs
  | [] => False

@[simp] def falsePrefixLen : List Bool → ℕ
  | false :: xs => falsePrefixLen xs + 1
  | _ => 0

@[simp] def dropFalsePrefix : List Bool → List Bool
  | false :: xs => dropFalsePrefix xs
  | xs => xs

lemma falsePrefix_decomp : ∀ xs : List Bool,
    xs = List.replicate (falsePrefixLen xs) false ++ dropFalsePrefix xs
  | [] => by simp
  | true :: _ => by simp
  | false :: xs => by
      change false :: xs =
        List.replicate (falsePrefixLen xs + 1) false ++ dropFalsePrefix xs
      have h := falsePrefix_decomp xs
      conv_lhs => rw [h]
      rw [show falsePrefixLen xs + 1 = Nat.succ (falsePrefixLen xs) by omega]
      simp [List.replicate_succ]

lemma dropFalsePrefix_boundary (xs : List Bool) :
    dropFalsePrefix xs = [] ∨ ∃ ys, dropFalsePrefix xs = true :: ys := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
      cases b
      · simpa using ih
      · simp

lemma pRun_le_self (k : ℕ) : pRun k ≤ k := by
  unfold pRun
  by_cases h : k % 7 = 1 ∨ k % 7 = 3 ∨ k % 7 = 5
  · rw [if_pos h]
    have hdiv : 7 * (k / 7) + k % 7 = k := Nat.div_add_mod k 7
    omega
  · rw [if_neg h]
    exact Nat.div_le_self k 7

lemma p_preserve_split_exists (k : ℕ) (hk : 2 ≤ k) :
    ∃ a b, a + b + 2 = k ∧ pRun k ≤ pRun a + pRun b := by
  have hdiv : 7 * (k / 7) + k % 7 = k := Nat.div_add_mod k 7
  have hmk : k % 7 < 7 := Nat.mod_lt k (by norm_num)
  have hcases :
      k % 7 = 0 ∨ k % 7 = 1 ∨ k % 7 = 2 ∨ k % 7 = 3 ∨
        k % 7 = 4 ∨ k % 7 = 5 ∨ k % 7 = 6 := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · refine ⟨0, k - 2, by omega, ?_⟩
    unfold pRun
    norm_num
    have hb : 7 * ((k - 2) / 7) + (k - 2) % 7 = k - 2 :=
      Nat.div_add_mod (k - 2) 7
    have hmb : (k - 2) % 7 < 7 := Nat.mod_lt (k - 2) (by norm_num)
    split_ifs <;> omega
  · refine ⟨1, k - 3, by omega, ?_⟩
    unfold pRun
    norm_num
    have hb : 7 * ((k - 3) / 7) + (k - 3) % 7 = k - 3 :=
      Nat.div_add_mod (k - 3) 7
    have hmb : (k - 3) % 7 < 7 := Nat.mod_lt (k - 3) (by norm_num)
    split_ifs <;> omega
  all_goals
    refine ⟨0, k - 2, by omega, ?_⟩
    unfold pRun
    norm_num
    have hb : 7 * ((k - 2) / 7) + (k - 2) % 7 = k - 2 :=
      Nat.div_add_mod (k - 2) 7
    have hmb : (k - 2) % 7 < 7 := Nat.mod_lt (k - 2) (by norm_num)
    split_ifs <;> omega

lemma scoreAux_replicate_false (v : ℕ → ℕ) (r k : ℕ) (rest : List Bool) :
    scoreAux v r (List.replicate k false ++ rest) = scoreAux v (r + k) rest := by
  induction k generalizing r with
  | zero => simp
  | succ k ih =>
      simp [List.replicate_succ, ih, Nat.add_comm, Nat.add_left_comm]

lemma scoreAux_p_boundary (k : ℕ) (rest : List Bool)
    (hrest : rest = [] ∨ ∃ ys, rest = true :: ys) :
    scoreAux pRun k rest = pRun k + scoreAux pRun 0 rest := by
  rcases hrest with rfl | ⟨ys, rfl⟩ <;> simp [scoreAux]

lemma replicate_split_false (a b k : ℕ) (hk : a + b + 2 = k) :
    List.replicate k false =
      List.replicate a false ++ (false :: false :: List.replicate b false) := by
  subst k
  rw [show a + b + 2 = a + (2 + b) by omega]
  rw [List.replicate_add]
  rw [show 2 + b = Nat.succ (Nat.succ b) by omega]
  simp [List.replicate_succ]

lemma ListMove_run (a b k : ℕ) (rest : List Bool) (hk : a + b + 2 = k) :
    ListMove (List.replicate k false ++ rest)
      (List.replicate a false ++ (true :: true :: (List.replicate b false ++ rest))) := by
  refine ⟨List.replicate a false, List.replicate b false ++ rest, ?_, ?_⟩
  · rw [replicate_split_false a b k hk]
    simp
  · simp

lemma exists_p_preserve_run (k : ℕ) (rest : List Bool)
    (hk : 2 ≤ k) (hrest : rest = [] ∨ ∃ ys, rest = true :: ys) :
    ∃ ys, ListMove (List.replicate k false ++ rest) ys ∧
      score pRun (List.replicate k false ++ rest) ≤ score pRun ys := by
  rcases p_preserve_split_exists k hk with ⟨a, b, hk_eq, hscore⟩
  let ys := List.replicate a false ++ (true :: true :: (List.replicate b false ++ rest))
  refine ⟨ys, ListMove_run a b k rest hk_eq, ?_⟩
  unfold score ys
  rw [scoreAux_replicate_false pRun 0 k rest]
  simp only [zero_add]
  rw [scoreAux_p_boundary k rest hrest]
  rw [scoreAux_replicate_false pRun 0 a
    (true :: true :: (List.replicate b false ++ rest))]
  simp only [zero_add]
  simp [scoreAux]
  rw [scoreAux_replicate_false pRun 0 b rest]
  simp only [zero_add]
  rw [scoreAux_p_boundary b rest hrest]
  omega

lemma exists_p_preserve : ∀ xs : List Bool, HasPair xs →
    ∃ ys, ListMove xs ys ∧ score pRun xs ≤ score pRun ys
  | [], h => False.elim h
  | [false], h => False.elim h
  | [true], h => False.elim h
  | true :: x :: xs, h => by
      have ht : HasPair (x :: xs) := by simpa using h
      rcases exists_p_preserve (x :: xs) ht with
        ⟨ys, ⟨pre, post, hpre, hys⟩, hs⟩
      refine ⟨true :: ys, ?_, ?_⟩
      · refine ⟨true :: pre, post, ?_, ?_⟩ <;> simp [hpre, hys]
      · simpa [score, scoreAux] using hs
  | false :: true :: xs, h => by
      have ht : HasPair xs := by simpa using h
      rcases exists_p_preserve xs ht with
        ⟨ys, ⟨pre, post, hpre, hys⟩, hs⟩
      refine ⟨false :: true :: ys, ?_, ?_⟩
      · refine ⟨false :: true :: pre, post, ?_, ?_⟩ <;> simp [hpre, hys]
      · simpa [score, scoreAux] using hs
  | false :: false :: xs, _ => by
      let zs := false :: false :: xs
      have hz : zs = List.replicate (falsePrefixLen zs) false ++ dropFalsePrefix zs :=
        falsePrefix_decomp zs
      have hk : 2 ≤ falsePrefixLen zs := by simp [zs]
      have hrest := dropFalsePrefix_boundary zs
      rcases exists_p_preserve_run (falsePrefixLen zs) (dropFalsePrefix zs) hk hrest with
        ⟨ys, hm, hs⟩
      refine ⟨ys, ?_, ?_⟩
      · simpa [zs, hz] using hm
      · simpa [zs, hz] using hs

lemma scoreAux_le_falseCount {v : ℕ → ℕ} (hv : ∀ k, v k ≤ k) :
    ∀ r xs, scoreAux v r xs ≤ r + xs.count false
  | r, [] => by simpa using hv r
  | r, true :: xs => by
      simp [scoreAux]
      have h1 := hv r
      have h2 := scoreAux_le_falseCount hv 0 xs
      omega
  | r, false :: xs => by
      have h := scoreAux_le_falseCount hv (r + 1) xs
      simp [scoreAux] at h ⊢
      omega

lemma score_p_le_count (xs : List Bool) :
    score pRun xs ≤ xs.count false := by
  simpa [score] using scoreAux_le_falseCount pRun_le_self 0 xs

def GoodRun (k : ℕ) : Prop :=
  k % 7 = 4 ∨ k % 7 = 6

instance (k : ℕ) : Decidable (GoodRun k) := by
  unfold GoodRun
  infer_instance

def goodRunCount (k : ℕ) : ℕ :=
  if GoodRun k then 1 else 0

@[simp] lemma goodRunCount_zero : goodRunCount 0 = 0 := by
  simp [goodRunCount, GoodRun]

@[simp] def goodAux : ℕ → List Bool → ℕ
  | r, [] => goodRunCount r
  | r, true :: xs => goodRunCount r + goodAux 0 xs
  | r, false :: xs => goodAux (r + 1) xs

def goodScore (xs : List Bool) : ℕ :=
  goodAux 0 xs

def aliceScore (xs : List Bool) : ℕ :=
  score pRun xs + 2 * ((goodScore xs + 1) / 2)

def bobScore (xs : List Bool) : ℕ :=
  score pRun xs + 2 * (goodScore xs / 2)

def aliceRC (c r : ℕ) (xs : List Bool) : ℕ :=
  scoreAux pRun r xs + 2 * ((goodAux r xs + c + 1) / 2)

def bobRC (c r : ℕ) (xs : List Bool) : ℕ :=
  scoreAux pRun r xs + 2 * ((goodAux r xs + c) / 2)

lemma local_alice_move_le (a b k c : ℕ) (hk : a + b + 2 = k) :
    pRun a + pRun b + 2 * ((goodRunCount a + goodRunCount b + c) / 2) ≤
      pRun k + 2 * ((goodRunCount k + c + 1) / 2) := by
  subst k
  unfold pRun goodRunCount GoodRun
  have ha : 7 * (a / 7) + a % 7 = a := Nat.div_add_mod a 7
  have hb : 7 * (b / 7) + b % 7 = b := Nat.div_add_mod b 7
  have hab : 7 * ((a + b + 2) / 7) + (a + b + 2) % 7 = a + b + 2 :=
    Nat.div_add_mod (a + b + 2) 7
  have hma : a % 7 < 7 := Nat.mod_lt a (by norm_num)
  have hmb : b % 7 < 7 := Nat.mod_lt b (by norm_num)
  have hmab : (a + b + 2) % 7 < 7 := Nat.mod_lt (a + b + 2) (by norm_num)
  split_ifs <;> omega

lemma local_bob_move_le (a b k c : ℕ) (hk : a + b + 2 = k) :
    pRun k + 2 * ((goodRunCount k + c) / 2) ≤
      pRun a + pRun b + 2 * ((goodRunCount a + goodRunCount b + c + 1) / 2) := by
  subst k
  unfold pRun goodRunCount GoodRun
  have ha : 7 * (a / 7) + a % 7 = a := Nat.div_add_mod a 7
  have hb : 7 * (b / 7) + b % 7 = b := Nat.div_add_mod b 7
  have hab : 7 * ((a + b + 2) / 7) + (a + b + 2) % 7 = a + b + 2 :=
    Nat.div_add_mod (a + b + 2) 7
  have hma : a % 7 < 7 := Nat.mod_lt a (by norm_num)
  have hmb : b % 7 < 7 := Nat.mod_lt b (by norm_num)
  have hmab : (a + b + 2) % 7 < 7 := Nat.mod_lt (a + b + 2) (by norm_num)
  split_ifs <;> omega

lemma pRun_add_two_good_le_self (k : ℕ) :
    pRun k + 2 * goodRunCount k ≤ k := by
  unfold pRun goodRunCount GoodRun
  have hk : 7 * (k / 7) + k % 7 = k := Nat.div_add_mod k 7
  have hmk : k % 7 < 7 := Nat.mod_lt k (by norm_num)
  split_ifs <;> omega

lemma scoreAux_add_two_goodAux_le_falseCount :
    ∀ r xs, scoreAux pRun r xs + 2 * goodAux r xs ≤ r + xs.count false
  | r, [] => by
      simpa using pRun_add_two_good_le_self r
  | r, true :: xs => by
      simp [scoreAux, goodAux]
      have hrun := pRun_add_two_good_le_self r
      have htail := scoreAux_add_two_goodAux_le_falseCount 0 xs
      omega
  | r, false :: xs => by
      have h := scoreAux_add_two_goodAux_le_falseCount (r + 1) xs
      simp [scoreAux, goodAux] at h ⊢
      omega

lemma aliceScore_le_count (xs : List Bool) :
    aliceScore xs ≤ xs.count false := by
  unfold aliceScore goodScore score
  have h := scoreAux_add_two_goodAux_le_falseCount 0 xs
  have hceil : 2 * ((goodAux 0 xs + 1) / 2) ≤ 2 * goodAux 0 xs := by omega
  omega

lemma bobScore_le_count (xs : List Bool) :
    bobScore xs ≤ xs.count false := by
  unfold bobScore goodScore score
  have h := scoreAux_add_two_goodAux_le_falseCount 0 xs
  have hfloor : 2 * (goodAux 0 xs / 2) ≤ 2 * goodAux 0 xs := by omega
  omega

lemma noPair_score_good :
    ∀ xs : List Bool, ¬ HasPair xs →
      score pRun xs = xs.count false ∧ goodScore xs = 0
  | [], _ => by simp [score, goodScore]
  | [true], _ => by simp [score, goodScore]
  | [false], _ => by simp [score, goodScore, pRun, goodRunCount, GoodRun]
  | true :: x :: xs, h => by
      have ht : ¬ HasPair (x :: xs) := by
        intro hp
        exact h (by simpa using hp)
      rcases noPair_score_good (x :: xs) ht with ⟨hs, hg⟩
      simpa [score, goodScore, scoreAux, goodAux] using And.intro hs hg
  | false :: true :: xs, h => by
      have ht : ¬ HasPair xs := by
        intro hp
        exact h (by simpa using hp)
      rcases noPair_score_good xs ht with ⟨hs, hg⟩
      constructor
      · simp [score, scoreAux, pRun] at hs ⊢
        omega
      · have hg' : goodAux 0 xs = 0 := by simpa [goodScore] using hg
        simp [goodScore, goodAux, goodRunCount, GoodRun, hg']
  | false :: false :: xs, h => by
      exact False.elim (h (by simp))

lemma noPair_aliceScore (xs : List Bool) (h : ¬ HasPair xs) :
    aliceScore xs = xs.count false := by
  rcases noPair_score_good xs h with ⟨hs, hg⟩
  simp [aliceScore, hs, hg]

lemma noPair_bobScore (xs : List Bool) (h : ¬ HasPair xs) :
    bobScore xs = xs.count false := by
  rcases noPair_score_good xs h with ⟨hs, hg⟩
  simp [bobScore, hs, hg]

set_option maxHeartbeats 1000000 in
lemma local_alice_exists_even (k c : ℕ) (hk : 2 ≤ k) (hc : c % 2 = 0) :
    ∃ a b, a + b + 2 = k ∧
      pRun k + 2 * ((goodRunCount k + c + 1) / 2) ≤
        pRun a + pRun b + 2 * ((goodRunCount a + goodRunCount b + c) / 2) := by
  have hdiv : 7 * (k / 7) + k % 7 = k := Nat.div_add_mod k 7
  have hmk : k % 7 < 7 := Nat.mod_lt k (by norm_num)
  have hdc : 2 * (c / 2) + c % 2 = c := Nat.div_add_mod c 2
  have hcases :
      k % 7 = 0 ∨ k % 7 = 1 ∨ k % 7 = 2 ∨ k % 7 = 3 ∨
        k % 7 = 4 ∨ k % 7 = 5 ∨ k % 7 = 6 := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · refine ⟨1, k - 3, by omega, ?_⟩
    unfold pRun goodRunCount GoodRun
    have hb : 7 * ((k - 3) / 7) + (k - 3) % 7 = k - 3 :=
      Nat.div_add_mod (k - 3) 7
    have hmb : (k - 3) % 7 < 7 := Nat.mod_lt (k - 3) (by norm_num)
    split_ifs <;> omega
  · refine ⟨1, k - 3, by omega, ?_⟩
    unfold pRun goodRunCount GoodRun
    have hb : 7 * ((k - 3) / 7) + (k - 3) % 7 = k - 3 :=
      Nat.div_add_mod (k - 3) 7
    have hmb : (k - 3) % 7 < 7 := Nat.mod_lt (k - 3) (by norm_num)
    split_ifs <;> omega
  · refine ⟨0, k - 2, by omega, ?_⟩
    unfold pRun goodRunCount GoodRun
    norm_num
    have hb : 7 * ((k - 2) / 7) + (k - 2) % 7 = k - 2 :=
      Nat.div_add_mod (k - 2) 7
    have hmb : (k - 2) % 7 < 7 := Nat.mod_lt (k - 2) (by norm_num)
    split_ifs <;> omega
  · refine ⟨0, k - 2, by omega, ?_⟩
    unfold pRun goodRunCount GoodRun
    norm_num
    have hb : 7 * ((k - 2) / 7) + (k - 2) % 7 = k - 2 :=
      Nat.div_add_mod (k - 2) 7
    have hmb : (k - 2) % 7 < 7 := Nat.mod_lt (k - 2) (by norm_num)
    split_ifs <;> omega
  · refine ⟨1, k - 3, by omega, ?_⟩
    unfold pRun goodRunCount GoodRun
    have hb : 7 * ((k - 3) / 7) + (k - 3) % 7 = k - 3 :=
      Nat.div_add_mod (k - 3) 7
    have hmb : (k - 3) % 7 < 7 := Nat.mod_lt (k - 3) (by norm_num)
    split_ifs <;> omega
  · refine ⟨0, k - 2, by omega, ?_⟩
    unfold pRun goodRunCount GoodRun
    norm_num
    have hb : 7 * ((k - 2) / 7) + (k - 2) % 7 = k - 2 :=
      Nat.div_add_mod (k - 2) 7
    have hmb : (k - 2) % 7 < 7 := Nat.mod_lt (k - 2) (by norm_num)
    split_ifs <;> omega
  · refine ⟨1, k - 3, by omega, ?_⟩
    unfold pRun goodRunCount GoodRun
    have hb : 7 * ((k - 3) / 7) + (k - 3) % 7 = k - 3 :=
      Nat.div_add_mod (k - 3) 7
    have hmb : (k - 3) % 7 < 7 := Nat.mod_lt (k - 3) (by norm_num)
    split_ifs <;> omega

set_option maxHeartbeats 1000000 in
lemma local_alice_exists_good (k c : ℕ) (hk : 2 ≤ k) (hg : GoodRun k) :
    ∃ a b, a + b + 2 = k ∧
      pRun k + 2 * ((goodRunCount k + c + 1) / 2) ≤
        pRun a + pRun b + 2 * ((goodRunCount a + goodRunCount b + c) / 2) := by
  unfold GoodRun at hg
  rcases hg with h4 | h6
  · refine ⟨1, k - 3, by omega, ?_⟩
    unfold pRun goodRunCount GoodRun
    have hdiv : 7 * (k / 7) + k % 7 = k := Nat.div_add_mod k 7
    have hmk : k % 7 < 7 := Nat.mod_lt k (by norm_num)
    have hb : 7 * ((k - 3) / 7) + (k - 3) % 7 = k - 3 :=
      Nat.div_add_mod (k - 3) 7
    have hmb : (k - 3) % 7 < 7 := Nat.mod_lt (k - 3) (by norm_num)
    have hdc : 2 * (c / 2) + c % 2 = c := Nat.div_add_mod c 2
    have hmc : c % 2 < 2 := Nat.mod_lt c (by norm_num)
    split_ifs <;> omega
  · refine ⟨1, k - 3, by omega, ?_⟩
    unfold pRun goodRunCount GoodRun
    have hdiv : 7 * (k / 7) + k % 7 = k := Nat.div_add_mod k 7
    have hmk : k % 7 < 7 := Nat.mod_lt k (by norm_num)
    have hb : 7 * ((k - 3) / 7) + (k - 3) % 7 = k - 3 :=
      Nat.div_add_mod (k - 3) 7
    have hmb : (k - 3) % 7 < 7 := Nat.mod_lt (k - 3) (by norm_num)
    have hdc : 2 * (c / 2) + c % 2 = c := Nat.div_add_mod c 2
    have hmc : c % 2 < 2 := Nat.mod_lt c (by norm_num)
    split_ifs <;> omega

lemma local_alice_exists (k c : ℕ) (hk : 2 ≤ k)
    (h : c % 2 = 0 ∨ GoodRun k) :
    ∃ a b, a + b + 2 = k ∧
      pRun k + 2 * ((goodRunCount k + c + 1) / 2) ≤
        pRun a + pRun b + 2 * ((goodRunCount a + goodRunCount b + c) / 2) := by
  rcases h with hc | hg
  · exact local_alice_exists_even k c hk hc
  · exact local_alice_exists_good k c hk hg

set_option maxHeartbeats 1000000 in
lemma local_bob_exists_even (k c : ℕ) (hk : 2 ≤ k) (hc : c % 2 = 0) :
    ∃ a b, a + b + 2 = k ∧
      pRun a + pRun b + 2 * ((goodRunCount a + goodRunCount b + c + 1) / 2) ≤
        pRun k + 2 * ((goodRunCount k + c) / 2) := by
  have hdiv : 7 * (k / 7) + k % 7 = k := Nat.div_add_mod k 7
  have hmk : k % 7 < 7 := Nat.mod_lt k (by norm_num)
  have hdc : 2 * (c / 2) + c % 2 = c := Nat.div_add_mod c 2
  have hcases :
      k % 7 = 0 ∨ k % 7 = 1 ∨ k % 7 = 2 ∨ k % 7 = 3 ∨
        k % 7 = 4 ∨ k % 7 = 5 ∨ k % 7 = 6 := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6
  all_goals first | refine ⟨2, k - 4, by omega, ?_⟩ | refine ⟨0, k - 2, by omega, ?_⟩
  all_goals
    unfold pRun goodRunCount GoodRun
    norm_num
  · have hb : 7 * ((k - 2) / 7) + (k - 2) % 7 = k - 2 :=
      Nat.div_add_mod (k - 2) 7
    have hmb : (k - 2) % 7 < 7 := Nat.mod_lt (k - 2) (by norm_num)
    split_ifs <;> omega
  · have hb : 7 * ((k - 2) / 7) + (k - 2) % 7 = k - 2 :=
      Nat.div_add_mod (k - 2) 7
    have hmb : (k - 2) % 7 < 7 := Nat.mod_lt (k - 2) (by norm_num)
    split_ifs <;> omega
  · have hb : 7 * ((k - 2) / 7) + (k - 2) % 7 = k - 2 :=
      Nat.div_add_mod (k - 2) 7
    have hmb : (k - 2) % 7 < 7 := Nat.mod_lt (k - 2) (by norm_num)
    split_ifs <;> omega
  · have hb : 7 * ((k - 2) / 7) + (k - 2) % 7 = k - 2 :=
      Nat.div_add_mod (k - 2) 7
    have hmb : (k - 2) % 7 < 7 := Nat.mod_lt (k - 2) (by norm_num)
    split_ifs <;> omega
  · have hb : 7 * ((k - 2) / 7) + (k - 2) % 7 = k - 2 :=
      Nat.div_add_mod (k - 2) 7
    have hmb : (k - 2) % 7 < 7 := Nat.mod_lt (k - 2) (by norm_num)
    split_ifs <;> omega
  · have hb : 7 * ((k - 2) / 7) + (k - 2) % 7 = k - 2 :=
      Nat.div_add_mod (k - 2) 7
    have hmb : (k - 2) % 7 < 7 := Nat.mod_lt (k - 2) (by norm_num)
    split_ifs <;> omega
  · have hb : 7 * ((k - 4) / 7) + (k - 4) % 7 = k - 4 :=
      Nat.div_add_mod (k - 4) 7
    have hmb : (k - 4) % 7 < 7 := Nat.mod_lt (k - 4) (by norm_num)
    split_ifs <;> omega

set_option maxHeartbeats 1000000 in
lemma local_bob_exists_good (k c : ℕ) (hk : 2 ≤ k) (hg : GoodRun k) :
    ∃ a b, a + b + 2 = k ∧
      pRun a + pRun b + 2 * ((goodRunCount a + goodRunCount b + c + 1) / 2) ≤
        pRun k + 2 * ((goodRunCount k + c) / 2) := by
  unfold GoodRun at hg
  rcases hg with h4 | h6
  · refine ⟨0, k - 2, by omega, ?_⟩
    unfold pRun goodRunCount GoodRun
    norm_num
    have hdiv : 7 * (k / 7) + k % 7 = k := Nat.div_add_mod k 7
    have hmk : k % 7 < 7 := Nat.mod_lt k (by norm_num)
    have hb : 7 * ((k - 2) / 7) + (k - 2) % 7 = k - 2 :=
      Nat.div_add_mod (k - 2) 7
    have hmb : (k - 2) % 7 < 7 := Nat.mod_lt (k - 2) (by norm_num)
    have hdc : 2 * (c / 2) + c % 2 = c := Nat.div_add_mod c 2
    have hmc : c % 2 < 2 := Nat.mod_lt c (by norm_num)
    split_ifs <;> omega
  · refine ⟨2, k - 4, by omega, ?_⟩
    unfold pRun goodRunCount GoodRun
    norm_num
    have hdiv : 7 * (k / 7) + k % 7 = k := Nat.div_add_mod k 7
    have hmk : k % 7 < 7 := Nat.mod_lt k (by norm_num)
    have hb : 7 * ((k - 4) / 7) + (k - 4) % 7 = k - 4 :=
      Nat.div_add_mod (k - 4) 7
    have hmb : (k - 4) % 7 < 7 := Nat.mod_lt (k - 4) (by norm_num)
    have hdc : 2 * (c / 2) + c % 2 = c := Nat.div_add_mod c 2
    have hmc : c % 2 < 2 := Nat.mod_lt c (by norm_num)
    split_ifs <;> omega

lemma local_bob_exists (k c : ℕ) (hk : 2 ≤ k)
    (h : c % 2 = 0 ∨ GoodRun k) :
    ∃ a b, a + b + 2 = k ∧
      pRun a + pRun b + 2 * ((goodRunCount a + goodRunCount b + c + 1) / 2) ≤
        pRun k + 2 * ((goodRunCount k + c) / 2) := by
  rcases h with hc | hg
  · exact local_bob_exists_even k c hk hc
  · exact local_bob_exists_good k c hk hg

lemma goodAux_replicate_false (r k : ℕ) (rest : List Bool) :
    goodAux r (List.replicate k false ++ rest) = goodAux (r + k) rest := by
  induction k generalizing r with
  | zero => simp
  | succ k ih =>
      simp [List.replicate_succ, ih, Nat.add_comm, Nat.add_left_comm]

lemma goodAux_boundary (k : ℕ) (rest : List Bool)
    (hrest : rest = [] ∨ ∃ ys, rest = true :: ys) :
    goodAux k rest = goodRunCount k + goodAux 0 rest := by
  rcases hrest with rfl | ⟨ys, rfl⟩ <;> simp [goodAux]

lemma alice_run_move_exists (k : ℕ) (rest : List Bool)
    (hk : 2 ≤ k) (hrest : rest = [] ∨ ∃ ys, rest = true :: ys)
    (hcond : (goodAux 0 rest) % 2 = 0 ∨ GoodRun k) :
    ∃ ys, ListMove (List.replicate k false ++ rest) ys ∧
      aliceScore (List.replicate k false ++ rest) ≤ bobScore ys := by
  rcases local_alice_exists k (goodAux 0 rest) hk hcond with
    ⟨a, b, hk_eq, hscore⟩
  let ys := List.replicate a false ++ (true :: true :: (List.replicate b false ++ rest))
  refine ⟨ys, ListMove_run a b k rest hk_eq, ?_⟩
  unfold aliceScore bobScore goodScore score ys
  rw [scoreAux_replicate_false pRun 0 k rest]
  simp only [zero_add]
  rw [scoreAux_p_boundary k rest hrest]
  rw [goodAux_replicate_false 0 k rest]
  simp only [zero_add]
  rw [goodAux_boundary k rest hrest]
  rw [scoreAux_replicate_false pRun 0 a
    (true :: true :: (List.replicate b false ++ rest))]
  simp only [zero_add]
  rw [goodAux_replicate_false 0 a
    (true :: true :: (List.replicate b false ++ rest))]
  simp [scoreAux, goodAux]
  rw [scoreAux_replicate_false pRun 0 b rest]
  simp only [zero_add]
  rw [scoreAux_p_boundary b rest hrest]
  rw [goodAux_replicate_false 0 b rest]
  simp only [zero_add]
  rw [goodAux_boundary b rest hrest]
  omega

lemma bob_run_move_exists (k : ℕ) (rest : List Bool)
    (hk : 2 ≤ k) (hrest : rest = [] ∨ ∃ ys, rest = true :: ys)
    (hcond : (goodAux 0 rest) % 2 = 0 ∨ GoodRun k) :
    ∃ ys, ListMove (List.replicate k false ++ rest) ys ∧
      aliceScore ys ≤ bobScore (List.replicate k false ++ rest) := by
  rcases local_bob_exists k (goodAux 0 rest) hk hcond with
    ⟨a, b, hk_eq, hscore⟩
  let ys := List.replicate a false ++ (true :: true :: (List.replicate b false ++ rest))
  refine ⟨ys, ListMove_run a b k rest hk_eq, ?_⟩
  unfold aliceScore bobScore goodScore score ys
  rw [scoreAux_replicate_false pRun 0 k rest]
  simp only [zero_add]
  rw [scoreAux_p_boundary k rest hrest]
  rw [goodAux_replicate_false 0 k rest]
  simp only [zero_add]
  rw [goodAux_boundary k rest hrest]
  rw [scoreAux_replicate_false pRun 0 a
    (true :: true :: (List.replicate b false ++ rest))]
  simp only [zero_add]
  rw [goodAux_replicate_false 0 a
    (true :: true :: (List.replicate b false ++ rest))]
  simp [scoreAux, goodAux]
  rw [scoreAux_replicate_false pRun 0 b rest]
  simp only [zero_add]
  rw [scoreAux_p_boundary b rest hrest]
  rw [goodAux_replicate_false 0 b rest]
  simp only [zero_add]
  rw [goodAux_boundary b rest hrest]
  omega

lemma listMove_head_alice_le (c r : ℕ) (post : List Bool) :
    bobRC c r (true :: true :: post) ≤ aliceRC c r (false :: false :: post) := by
  let b := falsePrefixLen post
  let rest := dropFalsePrefix post
  have hpost : post = List.replicate b false ++ rest := by
    simpa [b, rest] using falsePrefix_decomp post
  have hrest : rest = [] ∨ ∃ ys, rest = true :: ys := by
    simpa [rest] using dropFalsePrefix_boundary post
  have hlocal := local_alice_move_le r b (r + b + 2) (goodAux 0 rest + c) (by omega)
  unfold aliceRC bobRC
  conv_lhs => rw [hpost]
  conv_rhs => rw [hpost]
  simp [scoreAux, goodAux]
  rw [scoreAux_replicate_false pRun 0 b rest]
  rw [goodAux_replicate_false 0 b rest]
  rw [scoreAux_replicate_false pRun (r + 2) b rest]
  rw [goodAux_replicate_false (r + 2) b rest]
  simp only [zero_add]
  rw [scoreAux_p_boundary b rest hrest]
  rw [goodAux_boundary b rest hrest]
  rw [scoreAux_p_boundary (r + 2 + b) rest hrest]
  rw [goodAux_boundary (r + 2 + b) rest hrest]
  rw [show r + 2 + b = r + b + 2 by omega]
  ring_nf at hlocal ⊢
  omega

lemma listMove_head_bob_le (c r : ℕ) (post : List Bool) :
    bobRC c r (false :: false :: post) ≤ aliceRC c r (true :: true :: post) := by
  let b := falsePrefixLen post
  let rest := dropFalsePrefix post
  have hpost : post = List.replicate b false ++ rest := by
    simpa [b, rest] using falsePrefix_decomp post
  have hrest : rest = [] ∨ ∃ ys, rest = true :: ys := by
    simpa [rest] using dropFalsePrefix_boundary post
  have hlocal := local_bob_move_le r b (r + b + 2) (goodAux 0 rest + c) (by omega)
  unfold aliceRC bobRC
  conv_lhs => rw [hpost]
  conv_rhs => rw [hpost]
  simp [scoreAux, goodAux]
  rw [scoreAux_replicate_false pRun 0 b rest]
  rw [goodAux_replicate_false 0 b rest]
  rw [scoreAux_replicate_false pRun (r + 2) b rest]
  rw [goodAux_replicate_false (r + 2) b rest]
  simp only [zero_add]
  rw [scoreAux_p_boundary b rest hrest]
  rw [goodAux_boundary b rest hrest]
  rw [scoreAux_p_boundary (r + 2 + b) rest hrest]
  rw [goodAux_boundary (r + 2 + b) rest hrest]
  rw [show r + 2 + b = r + b + 2 by omega]
  ring_nf at hlocal ⊢
  omega

lemma listMove_aliceRC_le (c r : ℕ) {xs ys : List Bool} (h : ListMove xs ys) :
    bobRC c r ys ≤ aliceRC c r xs := by
  rcases h with ⟨pre, post, hxs, hys⟩
  subst xs
  subst ys
  revert c r
  induction pre with
  | nil =>
      intro c r
      exact listMove_head_alice_le c r post
  | cons b pre ih =>
      intro c r
      cases b
      · simpa [aliceRC, bobRC, scoreAux, goodAux] using
          ih c (r + 1)
      · have hih := ih (c + goodRunCount r) 0
        unfold aliceRC bobRC at hih ⊢
        simp [scoreAux, goodAux] at hih ⊢
        omega

lemma listMove_bobRC_le (c r : ℕ) {xs ys : List Bool} (h : ListMove xs ys) :
    bobRC c r xs ≤ aliceRC c r ys := by
  rcases h with ⟨pre, post, hxs, hys⟩
  subst xs
  subst ys
  revert c r
  induction pre with
  | nil =>
      intro c r
      exact listMove_head_bob_le c r post
  | cons b pre ih =>
      intro c r
      cases b
      · simpa [aliceRC, bobRC, scoreAux, goodAux] using
          ih c (r + 1)
      · have hih := ih (c + goodRunCount r) 0
        unfold aliceRC bobRC at hih ⊢
        simp [scoreAux, goodAux] at hih ⊢
        omega

lemma listMove_alice_le {xs ys : List Bool} (h : ListMove xs ys) :
    bobScore ys ≤ aliceScore xs := by
  simpa [aliceScore, bobScore, aliceRC, bobRC, score, goodScore] using
    listMove_aliceRC_le 0 0 h

lemma listMove_bob_le {xs ys : List Bool} (h : ListMove xs ys) :
    bobScore xs ≤ aliceScore ys := by
  simpa [aliceScore, bobScore, aliceRC, bobRC, score, goodScore] using
    listMove_bobRC_le 0 0 h

lemma ListMove_prefix (pre : List Bool) {xs ys : List Bool} (h : ListMove xs ys) :
    ListMove (pre ++ xs) (pre ++ ys) := by
  rcases h with ⟨p, q, hxs, hys⟩
  refine ⟨pre ++ p, q, ?_, ?_⟩
  · rw [hxs, List.append_assoc]
  · rw [hys, List.append_assoc]

lemma score_replicate_boundary (k : ℕ) (rest : List Bool)
    (hrest : rest = [] ∨ ∃ ys, rest = true :: ys) :
    score pRun (List.replicate k false ++ rest) =
      pRun k + scoreAux pRun 0 rest := by
  unfold score
  rw [scoreAux_replicate_false pRun 0 k rest]
  simp only [zero_add]
  exact scoreAux_p_boundary k rest hrest

lemma goodScore_replicate_boundary (k : ℕ) (rest : List Bool)
    (hrest : rest = [] ∨ ∃ ys, rest = true :: ys) :
    goodScore (List.replicate k false ++ rest) =
      goodRunCount k + goodAux 0 rest := by
  unfold goodScore
  rw [goodAux_replicate_false 0 k rest]
  simp only [zero_add]
  exact goodAux_boundary k rest hrest

lemma goodRunCount_eq_zero_of_not (k : ℕ) (h : ¬ GoodRun k) :
    goodRunCount k = 0 := by
  simp [goodRunCount, h]

lemma prefix_nongood_alice_le (k : ℕ) {xs ys : List Bool}
    (hk : ¬ GoodRun k) (h : aliceScore xs ≤ bobScore ys) :
    aliceScore (List.replicate k false ++ true :: xs) ≤
      bobScore (List.replicate k false ++ true :: ys) := by
  have hrestx : (true :: xs : List Bool) = [] ∨ ∃ zs, (true :: xs : List Bool) = true :: zs :=
    Or.inr ⟨xs, rfl⟩
  have hresty : (true :: ys : List Bool) = [] ∨ ∃ zs, (true :: ys : List Bool) = true :: zs :=
    Or.inr ⟨ys, rfl⟩
  have hg0 := goodRunCount_eq_zero_of_not k hk
  unfold aliceScore bobScore goodScore score at h ⊢
  rw [scoreAux_replicate_false pRun 0 k (true :: xs)]
  rw [scoreAux_replicate_false pRun 0 k (true :: ys)]
  rw [goodAux_replicate_false 0 k (true :: xs)]
  rw [goodAux_replicate_false 0 k (true :: ys)]
  simp only [zero_add]
  rw [scoreAux_p_boundary k (true :: xs) hrestx]
  rw [scoreAux_p_boundary k (true :: ys) hresty]
  rw [goodAux_boundary k (true :: xs) hrestx]
  rw [goodAux_boundary k (true :: ys) hresty]
  simp [scoreAux, goodAux, hg0] at h ⊢
  omega

lemma prefix_nongood_bob_le (k : ℕ) {xs ys : List Bool}
    (hk : ¬ GoodRun k) (h : aliceScore ys ≤ bobScore xs) :
    aliceScore (List.replicate k false ++ true :: ys) ≤
      bobScore (List.replicate k false ++ true :: xs) := by
  have hrestx : (true :: xs : List Bool) = [] ∨ ∃ zs, (true :: xs : List Bool) = true :: zs :=
    Or.inr ⟨xs, rfl⟩
  have hresty : (true :: ys : List Bool) = [] ∨ ∃ zs, (true :: ys : List Bool) = true :: zs :=
    Or.inr ⟨ys, rfl⟩
  have hg0 := goodRunCount_eq_zero_of_not k hk
  unfold aliceScore bobScore goodScore score at h ⊢
  rw [scoreAux_replicate_false pRun 0 k (true :: ys)]
  rw [scoreAux_replicate_false pRun 0 k (true :: xs)]
  rw [goodAux_replicate_false 0 k (true :: ys)]
  rw [goodAux_replicate_false 0 k (true :: xs)]
  simp only [zero_add]
  rw [scoreAux_p_boundary k (true :: ys) hresty]
  rw [scoreAux_p_boundary k (true :: xs) hrestx]
  rw [goodAux_boundary k (true :: ys) hresty]
  rw [goodAux_boundary k (true :: xs) hrestx]
  simp [scoreAux, goodAux, hg0] at h ⊢
  omega

lemma not_goodRun_one : ¬ GoodRun 1 := by
  simp [GoodRun]

lemma alice_move_exists_even :
    ∀ xs : List Bool, HasPair xs → goodScore xs % 2 = 0 →
      ∃ ys, ListMove xs ys ∧ aliceScore xs ≤ bobScore ys
  | [], h, _ => False.elim h
  | [false], h, _ => False.elim h
  | [true], h, _ => False.elim h
  | true :: x :: xs, h, hp => by
      have ht : HasPair (x :: xs) := by simpa using h
      have hpt : goodScore (x :: xs) % 2 = 0 := by simpa [goodScore, goodAux] using hp
      rcases alice_move_exists_even (x :: xs) ht hpt with ⟨ys, hm, hs⟩
      refine ⟨true :: ys, ?_, ?_⟩
      · exact ListMove_prefix [true] hm
      · simpa [aliceScore, bobScore, score, goodScore, scoreAux, goodAux] using hs
  | false :: true :: xs, h, hp => by
      have ht : HasPair xs := by simpa using h
      have hpt : goodScore xs % 2 = 0 := by
        simp [goodScore, goodAux, goodRunCount, GoodRun] at hp ⊢
        exact hp
      rcases alice_move_exists_even xs ht hpt with ⟨ys, hm, hs⟩
      refine ⟨false :: true :: ys, ?_, ?_⟩
      · simpa using ListMove_prefix [false, true] hm
      · simpa [List.replicate_succ] using prefix_nongood_alice_le 1 not_goodRun_one hs
  | false :: false :: xs, _h, hp => by
      let zs := false :: false :: xs
      let k := falsePrefixLen zs
      let rest := dropFalsePrefix zs
      have hz : zs = List.replicate k false ++ rest := by
        simpa [k, rest] using falsePrefix_decomp zs
      have hk : 2 ≤ k := by simp [zs, k]
      have hrest : rest = [] ∨ ∃ ys, rest = true :: ys := by
        simpa [rest] using dropFalsePrefix_boundary zs
      have hgood :
          goodScore zs = goodRunCount k + goodAux 0 rest := by
        simpa [hz] using goodScore_replicate_boundary k rest hrest
      have hcond : goodAux 0 rest % 2 = 0 ∨ GoodRun k := by
        by_cases hg : GoodRun k
        · exact Or.inr hg
        · left
          have hg0 := goodRunCount_eq_zero_of_not k hg
          have hpz : goodScore zs % 2 = 0 := by simpa [zs] using hp
          omega
      rcases alice_run_move_exists k rest hk hrest hcond with ⟨ys, hm, hs⟩
      refine ⟨ys, ?_, ?_⟩
      · simpa [zs, hz] using hm
      · simpa [zs, hz] using hs

lemma alice_move_exists_odd :
    ∀ xs : List Bool, goodScore xs % 2 = 1 →
      ∃ ys, ListMove xs ys ∧ aliceScore xs ≤ bobScore ys
  | [], hp => by simp [goodScore] at hp
  | [true], hp => by simp [goodScore, goodAux] at hp
  | [false], hp => by simp [goodScore, goodAux, goodRunCount, GoodRun] at hp
  | true :: x :: xs, hp => by
      have hpt : goodScore (x :: xs) % 2 = 1 := by simpa [goodScore, goodAux] using hp
      rcases alice_move_exists_odd (x :: xs) hpt with ⟨ys, hm, hs⟩
      refine ⟨true :: ys, ?_, ?_⟩
      · exact ListMove_prefix [true] hm
      · simpa [aliceScore, bobScore, score, goodScore, scoreAux, goodAux] using hs
  | false :: true :: xs, hp => by
      have hpt : goodScore xs % 2 = 1 := by
        simp [goodScore, goodAux, goodRunCount, GoodRun] at hp ⊢
        exact hp
      rcases alice_move_exists_odd xs hpt with ⟨ys, hm, hs⟩
      refine ⟨false :: true :: ys, ?_, ?_⟩
      · simpa using ListMove_prefix [false, true] hm
      · simpa [List.replicate_succ] using prefix_nongood_alice_le 1 not_goodRun_one hs
  | false :: false :: xs, hp => by
      let zs := false :: false :: xs
      let k := falsePrefixLen zs
      let rest := dropFalsePrefix zs
      have hz : zs = List.replicate k false ++ rest := by
        simpa [k, rest] using falsePrefix_decomp zs
      have hk : 2 ≤ k := by simp [zs, k]
      have hrest : rest = [] ∨ ∃ ys, rest = true :: ys := by
        simpa [rest] using dropFalsePrefix_boundary zs
      by_cases hg : GoodRun k
      · have hcond : goodAux 0 rest % 2 = 0 ∨ GoodRun k := Or.inr hg
        rcases alice_run_move_exists k rest hk hrest hcond with ⟨ys, hm, hs⟩
        refine ⟨ys, ?_, ?_⟩
        · simpa [zs, hz] using hm
        · simpa [zs, hz] using hs
      · have hgood :
            goodScore zs = goodRunCount k + goodAux 0 rest := by
          simpa [hz] using goodScore_replicate_boundary k rest hrest
        have hg0 := goodRunCount_eq_zero_of_not k hg
        have hrestodd : goodAux 0 rest % 2 = 1 := by
          have hpz : goodScore zs % 2 = 1 := by simpa [zs] using hp
          omega
        rcases hrest with hnil | ⟨tail, htail⟩
        · simp [hnil] at hrestodd
        · have htailodd : goodScore tail % 2 = 1 := by
            rw [htail] at hrestodd
            simpa [goodScore, goodAux] using hrestodd
          rcases alice_move_exists_odd tail htailodd with ⟨ys, hm, hs⟩
          refine ⟨List.replicate k false ++ true :: ys, ?_, ?_⟩
          · simpa [zs, hz, htail] using ListMove_prefix (List.replicate k false ++ [true]) hm
          · simpa [zs, hz, htail] using prefix_nongood_alice_le k hg hs
termination_by xs => xs.length
decreasing_by
  all_goals
    simp_wf
    try omega
    try
      have hlen := congrArg List.length hz
      simp [zs, htail] at hlen
      omega

lemma alice_move_exists (xs : List Bool) (h : HasPair xs) :
    ∃ ys, ListMove xs ys ∧ aliceScore xs ≤ bobScore ys := by
  by_cases hp : goodScore xs % 2 = 0
  · exact alice_move_exists_even xs h hp
  · have hp1 : goodScore xs % 2 = 1 := by
      have hm : goodScore xs % 2 < 2 := Nat.mod_lt _ (by norm_num)
      omega
    exact alice_move_exists_odd xs hp1

lemma bob_move_exists_even :
    ∀ xs : List Bool, HasPair xs → goodScore xs % 2 = 0 →
      ∃ ys, ListMove xs ys ∧ aliceScore ys ≤ bobScore xs
  | [], h, _ => False.elim h
  | [false], h, _ => False.elim h
  | [true], h, _ => False.elim h
  | true :: x :: xs, h, hp => by
      have ht : HasPair (x :: xs) := by simpa using h
      have hpt : goodScore (x :: xs) % 2 = 0 := by simpa [goodScore, goodAux] using hp
      rcases bob_move_exists_even (x :: xs) ht hpt with ⟨ys, hm, hs⟩
      refine ⟨true :: ys, ?_, ?_⟩
      · exact ListMove_prefix [true] hm
      · simpa [aliceScore, bobScore, score, goodScore, scoreAux, goodAux] using hs
  | false :: true :: xs, h, hp => by
      have ht : HasPair xs := by simpa using h
      have hpt : goodScore xs % 2 = 0 := by
        simp [goodScore, goodAux, goodRunCount, GoodRun] at hp ⊢
        exact hp
      rcases bob_move_exists_even xs ht hpt with ⟨ys, hm, hs⟩
      refine ⟨false :: true :: ys, ?_, ?_⟩
      · simpa using ListMove_prefix [false, true] hm
      · simpa [List.replicate_succ] using prefix_nongood_bob_le 1 not_goodRun_one hs
  | false :: false :: xs, _h, hp => by
      let zs := false :: false :: xs
      let k := falsePrefixLen zs
      let rest := dropFalsePrefix zs
      have hz : zs = List.replicate k false ++ rest := by
        simpa [k, rest] using falsePrefix_decomp zs
      have hk : 2 ≤ k := by simp [zs, k]
      have hrest : rest = [] ∨ ∃ ys, rest = true :: ys := by
        simpa [rest] using dropFalsePrefix_boundary zs
      have hgood :
          goodScore zs = goodRunCount k + goodAux 0 rest := by
        simpa [hz] using goodScore_replicate_boundary k rest hrest
      have hcond : goodAux 0 rest % 2 = 0 ∨ GoodRun k := by
        by_cases hg : GoodRun k
        · exact Or.inr hg
        · left
          have hg0 := goodRunCount_eq_zero_of_not k hg
          have hpz : goodScore zs % 2 = 0 := by simpa [zs] using hp
          omega
      rcases bob_run_move_exists k rest hk hrest hcond with ⟨ys, hm, hs⟩
      refine ⟨ys, ?_, ?_⟩
      · simpa [zs, hz] using hm
      · simpa [zs, hz] using hs

lemma bob_move_exists_odd :
    ∀ xs : List Bool, goodScore xs % 2 = 1 →
      ∃ ys, ListMove xs ys ∧ aliceScore ys ≤ bobScore xs
  | [], hp => by simp [goodScore] at hp
  | [true], hp => by simp [goodScore, goodAux] at hp
  | [false], hp => by simp [goodScore, goodAux, goodRunCount, GoodRun] at hp
  | true :: x :: xs, hp => by
      have hpt : goodScore (x :: xs) % 2 = 1 := by simpa [goodScore, goodAux] using hp
      rcases bob_move_exists_odd (x :: xs) hpt with ⟨ys, hm, hs⟩
      refine ⟨true :: ys, ?_, ?_⟩
      · exact ListMove_prefix [true] hm
      · simpa [aliceScore, bobScore, score, goodScore, scoreAux, goodAux] using hs
  | false :: true :: xs, hp => by
      have hpt : goodScore xs % 2 = 1 := by
        simp [goodScore, goodAux, goodRunCount, GoodRun] at hp ⊢
        exact hp
      rcases bob_move_exists_odd xs hpt with ⟨ys, hm, hs⟩
      refine ⟨false :: true :: ys, ?_, ?_⟩
      · simpa using ListMove_prefix [false, true] hm
      · simpa [List.replicate_succ] using prefix_nongood_bob_le 1 not_goodRun_one hs
  | false :: false :: xs, hp => by
      let zs := false :: false :: xs
      let k := falsePrefixLen zs
      let rest := dropFalsePrefix zs
      have hz : zs = List.replicate k false ++ rest := by
        simpa [k, rest] using falsePrefix_decomp zs
      have hk : 2 ≤ k := by simp [zs, k]
      have hrest : rest = [] ∨ ∃ ys, rest = true :: ys := by
        simpa [rest] using dropFalsePrefix_boundary zs
      by_cases hg : GoodRun k
      · have hcond : goodAux 0 rest % 2 = 0 ∨ GoodRun k := Or.inr hg
        rcases bob_run_move_exists k rest hk hrest hcond with ⟨ys, hm, hs⟩
        refine ⟨ys, ?_, ?_⟩
        · simpa [zs, hz] using hm
        · simpa [zs, hz] using hs
      · have hgood :
            goodScore zs = goodRunCount k + goodAux 0 rest := by
          simpa [hz] using goodScore_replicate_boundary k rest hrest
        have hg0 := goodRunCount_eq_zero_of_not k hg
        have hrestodd : goodAux 0 rest % 2 = 1 := by
          have hpz : goodScore zs % 2 = 1 := by simpa [zs] using hp
          omega
        rcases hrest with hnil | ⟨tail, htail⟩
        · simp [hnil] at hrestodd
        · have htailodd : goodScore tail % 2 = 1 := by
            rw [htail] at hrestodd
            simpa [goodScore, goodAux] using hrestodd
          rcases bob_move_exists_odd tail htailodd with ⟨ys, hm, hs⟩
          refine ⟨List.replicate k false ++ true :: ys, ?_, ?_⟩
          · simpa [zs, hz, htail] using ListMove_prefix (List.replicate k false ++ [true]) hm
          · simpa [zs, hz, htail] using prefix_nongood_bob_le k hg hs
termination_by xs => xs.length
decreasing_by
  all_goals
    simp_wf
    try omega
    try
      have hlen := congrArg List.length hz
      simp [zs, htail] at hlen
      omega

lemma bob_move_exists (xs : List Bool) (h : HasPair xs) :
    ∃ ys, ListMove xs ys ∧ aliceScore ys ≤ bobScore xs := by
  by_cases hp : goodScore xs % 2 = 0
  · exact bob_move_exists_even xs h hp
  · have hp1 : goodScore xs % 2 = 1 := by
      have hm : goodScore xs % 2 < 2 := Nat.mod_lt _ (by norm_num)
      omega
    exact bob_move_exists_odd xs hp1

noncomputable def boardList (x : Set (Fin 2022)) : List Bool := by
  exact (List.finRange 2022).map
    (fun i : Fin 2022 => @decide (i ∈ x) (Classical.propDecidable _))

def setOfList (xs : List Bool) : Set (Fin 2022) :=
  {i | xs.getD i.val false = true}

@[simp] lemma boardList_length (x : Set (Fin 2022)) :
    (boardList x).length = 2022 := by
  unfold boardList
  rw [List.length_map, List.length_finRange]

lemma boardList_getD_eq_true (x : Set (Fin 2022)) (i : Fin 2022) :
    (boardList x).getD i.val false = true ↔ i ∈ x := by
  unfold boardList
  rw [List.getD_eq_getElem]
  · rw [List.getElem_map]
    rw [List.getElem_finRange]
    rw [@decide_eq_true_eq
      ((Fin.cast (by rw [List.length_finRange])
        (⟨i.val, by rw [List.length_finRange]; exact i.isLt⟩ :
          Fin (List.finRange 2022).length)) ∈ x) (Classical.propDecidable _)]
    change i ∈ x ↔ i ∈ x
    rfl
  · rw [List.length_map, List.length_finRange]
    exact i.isLt

lemma setOfList_boardList (x : Set (Fin 2022)) :
    setOfList (boardList x) = x := by
  ext i
  exact boardList_getD_eq_true x i

lemma boardList_inj {x y : Set (Fin 2022)}
    (h : boardList x = boardList y) : x = y := by
  ext i
  have hg := congrArg (fun xs : List Bool => xs.getD i.val false) h
  constructor
  · intro hx
    have hxtrue := (boardList_getD_eq_true x i).mpr hx
    have hytrue : (boardList y).getD i.val false = true := by
      exact hg.symm.trans hxtrue
    exact (boardList_getD_eq_true y i).mp hytrue
  · intro hy
    have hytrue := (boardList_getD_eq_true y i).mpr hy
    have hxtrue : (boardList x).getD i.val false = true := by
      exact hg.trans hytrue
    exact (boardList_getD_eq_true x i).mp hxtrue

set_option maxRecDepth 10000 in
lemma boardList_setOfList {xs : List Bool} (hxs : xs.length = 2022) :
    boardList (setOfList xs) = xs := by
  apply List.ext_getElem
  · rw [boardList_length, hxs]
  · intro i hi hix
    have hi2022 : i < 2022 := by rwa [boardList_length] at hi
    let j : Fin 2022 := ⟨i, hi2022⟩
    have hleft_getD :
        (boardList (setOfList xs)).getD j.val false =
          (boardList (setOfList xs))[i] := by
      exact List.getD_eq_getElem (boardList (setOfList xs)) false hi
    have hset : j ∈ setOfList xs ↔ xs[i] = true := by
      change xs.getD i false = true ↔ xs[i] = true
      rw [List.getD_eq_getElem xs false hix]
    have hiff : (boardList (setOfList xs))[i] = true ↔ xs[i] = true := by
      rw [← hleft_getD]
      exact (boardList_getD_eq_true (setOfList xs) j).trans hset
    cases hxi : xs[i]
    · cases hleft : (boardList (setOfList xs))[i]
      · rfl
      · have hf := hiff.mp hleft
        rw [hxi] at hf
        contradiction
    · exact hiff.mpr hxi

lemma boardList_count_false (x : Set (Fin 2022)) :
    (boardList x).count false = xᶜ.ncard := by
  classical
  have hnc : xᶜ.ncard = (Finset.univ.filter fun i : Fin 2022 => i ∉ x).card := by
    rw [Set.ncard_eq_toFinset_card]
    simp
  rw [hnc]
  unfold boardList
  rw [List.count_eq_countP, List.countP_map]
  have hfun :
      ((fun b : Bool => b == false) ∘ fun i : Fin 2022 => decide (i ∈ x)) =
        (fun i : Fin 2022 => decide (i ∉ x)) := by
    funext i
    by_cases hi : i ∈ x <;> simp [hi]
  rw [hfun]
  rw [List.countP_eq_length_filter]
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange 2022).filter _)]
  rw [List.toFinset_filter, List.toFinset_finRange]
  have hset :
      (Finset.filter (fun i : Fin 2022 => decide (i ∉ x) = true) Finset.univ) =
        (Finset.filter (fun i : Fin 2022 => i ∉ x) Finset.univ) := by
    ext i
    simp
  exact congrArg Finset.card hset

lemma HasPair_of_split (pre post : List Bool) :
    HasPair (pre ++ false :: false :: post) := by
  induction pre with
  | nil => simp
  | cons b pre ih =>
      cases b
      · cases pre with
        | nil => simp
        | cons c pre =>
            cases c
            · simp
            · simpa using ih
      · simpa using ih

lemma HasPair.exists_split : ∀ {xs : List Bool}, HasPair xs →
    ∃ pre post, xs = pre ++ false :: false :: post
  | [], h => False.elim h
  | [true], h => False.elim h
  | [false], h => False.elim h
  | false :: false :: xs, _ => ⟨[], xs, rfl⟩
  | true :: x :: xs, h => by
      have ht : HasPair (x :: xs) := by simpa using h
      rcases HasPair.exists_split ht with ⟨pre, post, hp⟩
      exact ⟨true :: pre, post, by simp [hp]⟩
  | false :: true :: xs, h => by
      have ht : HasPair xs := by simpa using h
      rcases HasPair.exists_split ht with ⟨pre, post, hp⟩
      exact ⟨false :: true :: pre, post, by simp [hp]⟩

lemma hasPair_iff_exists_split (xs : List Bool) :
    HasPair xs ↔ ∃ pre post, xs = pre ++ false :: false :: post := by
  refine ⟨fun h => HasPair.exists_split h, ?_⟩
  rintro ⟨pre, post, rfl⟩
  exact HasPair_of_split pre post

lemma ListMove.length_eq {xs ys : List Bool} (h : ListMove xs ys) :
    ys.length = xs.length := by
  rcases h with ⟨pre, post, hxs, hys⟩
  rw [hxs, hys]
  simp

lemma ListMove.count_false {xs ys : List Bool} (h : ListMove xs ys) :
    ys.count false + 2 = xs.count false := by
  rcases h with ⟨pre, post, hxs, hys⟩
  rw [hxs, hys]
  simp [List.count_append]
  omega

lemma ListMove.hasPair {xs ys : List Bool} (h : ListMove xs ys) :
    HasPair xs := by
  rcases h with ⟨pre, post, hxs, _⟩
  rw [hxs]
  exact HasPair_of_split pre post

lemma getD_cons_cons_two {α : Type*} (a b d : α) (l : List α) (k : ℕ) :
    (a :: b :: l).getD (2 + k) d = l.getD k d := by
  rw [show 2 + k = (1 + k) + 1 by omega]
  rw [List.getD_cons_succ]
  rw [show 1 + k = k + 1 by omega]
  rw [List.getD_cons_succ]

lemma getD_move_true_iff (pre post : List Bool) (n : ℕ) :
    ((pre ++ true :: true :: post).getD n false = true) ↔
      ((pre ++ false :: false :: post).getD n false = true) ∨
        n = pre.length ∨ n = pre.length + 1 := by
  by_cases hlt : n < pre.length
  · rw [List.getD_append pre (true :: true :: post) false n hlt]
    rw [List.getD_append pre (false :: false :: post) false n hlt]
    constructor
    · intro h
      exact Or.inl h
    · intro h
      rcases h with h | h | h
      · exact h
      · omega
      · omega
  · have hge : pre.length ≤ n := by omega
    by_cases h0 : n = pre.length
    · subst n
      rw [List.getD_append_right pre (true :: true :: post) false pre.length
        (Nat.le_refl _)]
      rw [List.getD_append_right pre (false :: false :: post) false pre.length
        (Nat.le_refl _)]
      simp
    · by_cases h1 : n = pre.length + 1
      · subst n
        rw [List.getD_append_right pre (true :: true :: post) false
          (pre.length + 1) (by omega)]
        rw [List.getD_append_right pre (false :: false :: post) false
          (pre.length + 1) (by omega)]
        simp
      · rw [List.getD_append_right pre (true :: true :: post) false n hge]
        rw [List.getD_append_right pre (false :: false :: post) false n hge]
        rw [show n - pre.length = 2 + (n - pre.length - 2) by omega]
        rw [getD_cons_cons_two, getD_cons_cons_two]
        simp [h0, h1]

lemma list_eq_take_append_pair_drop {α : Type*} (xs : List α) {n : ℕ}
    (hn : n + 1 < xs.length) :
    xs = xs.take n ++ xs[n] :: xs[n + 1] :: xs.drop (n + 2) := by
  nth_rewrite 1 [← List.take_append_drop n xs]
  rw [List.drop_eq_getElem_cons (l := xs) (i := n) (by omega)]
  rw [List.drop_eq_getElem_cons (l := xs) (i := n + 1) hn]

lemma ListMove.exists_set_pair {x : Set (Fin 2022)} {ys : List Bool}
    (h : ListMove (boardList x) ys) :
    ∃ i : Fin 2022, i < 2021 ∧ i ∉ x ∧ i + 1 ∉ x ∧
      setOfList ys = x ∪ {i, i + 1} := by
  rcases h with ⟨pre, post, hxs, hys⟩
  have hlen : pre.length + post.length + 2 = 2022 := by
    have hlen' := congrArg List.length hxs
    rw [boardList_length] at hlen'
    simp at hlen'
    omega
  let i : Fin 2022 := ⟨pre.length, by omega⟩
  have hi_lt : i < 2021 := by
    rw [Fin.lt_def]
    change pre.length < 2021
    omega
  have hiadd_val : ((i + 1 : Fin 2022).val = pre.length + 1) := by
    rw [Fin.val_add_eq_of_add_lt]
    · rw [Fin.val_one]
    · rw [Fin.val_one]
      change pre.length + 1 < 2022
      omega
  have hget0 : (boardList x).getD i.val false = false := by
    rw [hxs]
    change (pre ++ false :: false :: post).getD pre.length false = false
    rw [List.getD_append_right pre (false :: false :: post) false pre.length
      (Nat.le_refl _)]
    simp
  have hnot0 : i ∉ x := by
    intro hx
    have hxtrue := (boardList_getD_eq_true x i).mpr hx
    rw [hget0] at hxtrue
    cases hxtrue
  have hget1 : (boardList x).getD ((i + 1 : Fin 2022).val) false = false := by
    rw [hiadd_val, hxs]
    rw [List.getD_append_right pre (false :: false :: post) false
      (pre.length + 1) (by omega)]
    simp
  have hnot1 : i + 1 ∉ x := by
    intro hx
    have hxtrue := (boardList_getD_eq_true x (i + 1)).mpr hx
    rw [hget1] at hxtrue
    cases hxtrue
  refine ⟨i, hi_lt, hnot0, hnot1, ?_⟩
  ext j
  change ys.getD j.val false = true ↔ j ∈ x ∪ {i, i + 1}
  rw [hys]
  rw [getD_move_true_iff pre post j.val]
  have hxiff :
      (pre ++ false :: false :: post).getD j.val false = true ↔ j ∈ x := by
    rw [← hxs]
    exact boardList_getD_eq_true x j
  rw [hxiff]
  have hj_i : j.val = pre.length ↔ j = i := by
    constructor
    · intro hj
      exact Fin.ext hj
    · intro hj
      rw [hj]
  have hj_i1 : j.val = pre.length + 1 ↔ j = i + 1 := by
    constructor
    · intro hj
      exact Fin.ext (by rw [hiadd_val]; exact hj)
    · intro hj
      rw [hj, hiadd_val]
  rw [hj_i, hj_i1]
  constructor
  · intro h
    rcases h with hx | hi | hi1
    · exact Or.inl hx
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr (by simp [hi1]))
  · intro h
    rcases h with hx | hi | hsing
    · exact Or.inl hx
    · exact Or.inr (Or.inl hi)
    · have hi1 : j = i + 1 := by simpa using hsing
      exact Or.inr (Or.inr hi1)

lemma valid_add_pair_to_ListMove {x y : Set (Fin 2022)} {i : Fin 2022}
    (hi : i < 2021) (hi0 : i ∉ x) (hi1 : i + 1 ∉ x)
    (hy : y = x ∪ {i, i + 1}) :
    ListMove (boardList x) (boardList y) := by
  let xs := boardList x
  let n := i.val
  have hiNat : n < 2021 := by
    rw [Fin.lt_def] at hi
    exact hi
  have hn_pair : n + 1 < xs.length := by
    simp [xs, n]
    omega
  have hn0 : n < xs.length := by omega
  have hiadd_val : ((i + 1 : Fin 2022).val = n + 1) := by
    rw [Fin.val_add_eq_of_add_lt]
    · rw [Fin.val_one]
    · rw [Fin.val_one]
      change n + 1 < 2022
      omega
  have hget0 : xs.getD n false = false := by
    by_cases htrue : xs.getD n false = true
    · have hxmem : i ∈ x := by
        simpa [xs, n] using (boardList_getD_eq_true x i).mp htrue
      exact False.elim (hi0 hxmem)
    · cases hval : xs.getD n false
      · rfl
      · exact False.elim (htrue hval)
  have hget1 : xs.getD (n + 1) false = false := by
    by_cases htrue : xs.getD (n + 1) false = true
    · have hxmem : i + 1 ∈ x := by
        have htrue' : (boardList x).getD ((i + 1 : Fin 2022).val) false = true := by
          simpa [xs, hiadd_val] using htrue
        exact (boardList_getD_eq_true x (i + 1)).mp htrue'
      exact False.elim (hi1 hxmem)
    · cases hval : xs.getD (n + 1) false
      · rfl
      · exact False.elim (htrue hval)
  have hx0 : xs[n] = false := by
    rw [← List.getD_eq_getElem xs false hn0]
    exact hget0
  have hx1 : xs[n + 1] = false := by
    rw [← List.getD_eq_getElem xs false hn_pair]
    exact hget1
  let pre := xs.take n
  let post := xs.drop (n + 2)
  let ys := pre ++ true :: true :: post
  have hsplit : xs = pre ++ false :: false :: post := by
    have h := list_eq_take_append_pair_drop xs hn_pair
    simpa [pre, post, hx0, hx1] using h
  have hm : ListMove xs ys := by
    exact ⟨pre, post, hsplit, rfl⟩
  have hys_len : ys.length = 2022 := by
    have hlen := ListMove.length_eq hm
    simp [xs] at hlen
    omega
  have hset_y : setOfList ys = y := by
    rw [hy]
    ext j
    change ys.getD j.val false = true ↔ j ∈ x ∪ {i, i + 1}
    rw [show ys = pre ++ true :: true :: post by rfl]
    rw [getD_move_true_iff pre post j.val]
    have hprelen : pre.length = n := by
      simp [pre, List.length_take_of_le (Nat.le_of_lt hn0)]
    have hxiff :
        (pre ++ false :: false :: post).getD j.val false = true ↔ j ∈ x := by
      rw [← hsplit]
      simpa [xs] using boardList_getD_eq_true x j
    rw [hxiff, hprelen]
    have hj_i : j.val = n ↔ j = i := by
      constructor
      · intro hj
        exact Fin.ext hj
      · intro hj
        rw [hj]
    have hj_i1 : j.val = n + 1 ↔ j = i + 1 := by
      constructor
      · intro hj
        exact Fin.ext (by rw [hiadd_val]; exact hj)
      · intro hj
        rw [hj, hiadd_val]
    rw [hj_i, hj_i1]
    constructor
    · intro h
      rcases h with hx | hi | hi1
      · exact Or.inl hx
      · exact Or.inr (Or.inl hi)
      · exact Or.inr (Or.inr (by simp [hi1]))
    · intro h
      rcases h with hx | hi | hsing
      · exact Or.inl hx
      · exact Or.inr (Or.inl hi)
      · have hi1' : j = i + 1 := by simpa using hsing
        exact Or.inr (Or.inr hi1')
  have hboard : boardList y = ys := by
    rw [← hset_y]
    exact boardList_setOfList hys_len
  simpa [xs, hboard] using hm

set_option maxRecDepth 10000

lemma not_hasPair_of_terminal {x : Set (Fin 2022)}
    (hterm : ∀ i < 2021, i ∉ x → i + 1 ∈ x) :
    ¬ HasPair (boardList x) := by
  intro hp
  rcases alice_move_exists (boardList x) hp with ⟨ys, hm, _⟩
  rcases ListMove.exists_set_pair hm with ⟨i, hi, hi0, hi1, _⟩
  exact hi1 (hterm i hi hi0)

lemma valid_self_of_noPair
    {IsValidMove : Set (Fin 2022) → Set (Fin 2022) → Prop}
    (IsValidMove_def : ∀ x y, IsValidMove x y ↔
      (x = y ∧ ∀ i < 2021, i ∉ x → i + 1 ∈ x) ∨
      ∃ i < 2021, i ∉ x ∧ i + 1 ∉ x ∧ y = x ∪ {i, i + 1})
    {x : Set (Fin 2022)} (hno : ¬ HasPair (boardList x)) :
    IsValidMove x x := by
  rw [IsValidMove_def]
  left
  refine ⟨rfl, ?_⟩
  intro i hi hi0
  by_contra hi1
  have hm : ListMove (boardList x) (boardList (x ∪ {i, i + 1})) :=
    valid_add_pair_to_ListMove hi hi0 hi1 rfl
  exact hno hm.hasPair

lemma validMove_alice_le
    {IsValidMove : Set (Fin 2022) → Set (Fin 2022) → Prop}
    (IsValidMove_def : ∀ x y, IsValidMove x y ↔
      (x = y ∧ ∀ i < 2021, i ∉ x → i + 1 ∈ x) ∨
      ∃ i < 2021, i ∉ x ∧ i + 1 ∉ x ∧ y = x ∪ {i, i + 1})
    {x y : Set (Fin 2022)} (hmove : IsValidMove x y) :
    bobScore (boardList y) ≤ aliceScore (boardList x) := by
  rcases (IsValidMove_def x y).mp hmove with hsame | hadd
  · rcases hsame with ⟨rfl, hterm⟩
    have hno := not_hasPair_of_terminal hterm
    rw [noPair_bobScore (boardList x) hno, noPair_aliceScore (boardList x) hno]
  · rcases hadd with ⟨i, hi, hi0, hi1, hy⟩
    exact listMove_alice_le (valid_add_pair_to_ListMove hi hi0 hi1 hy)

lemma validMove_bob_le
    {IsValidMove : Set (Fin 2022) → Set (Fin 2022) → Prop}
    (IsValidMove_def : ∀ x y, IsValidMove x y ↔
      (x = y ∧ ∀ i < 2021, i ∉ x → i + 1 ∈ x) ∨
      ∃ i < 2021, i ∉ x ∧ i + 1 ∉ x ∧ y = x ∪ {i, i + 1})
    {x y : Set (Fin 2022)} (hmove : IsValidMove x y) :
    bobScore (boardList x) ≤ aliceScore (boardList y) := by
  rcases (IsValidMove_def x y).mp hmove with hsame | hadd
  · rcases hsame with ⟨rfl, hterm⟩
    have hno := not_hasPair_of_terminal hterm
    rw [noPair_bobScore (boardList x) hno, noPair_aliceScore (boardList x) hno]
  · rcases hadd with ⟨i, hi, hi0, hi1, hy⟩
    exact listMove_bob_le (valid_add_pair_to_ListMove hi hi0 hi1 hy)

lemma alice_set_move_exists
    {IsValidMove : Set (Fin 2022) → Set (Fin 2022) → Prop}
    (IsValidMove_def : ∀ x y, IsValidMove x y ↔
      (x = y ∧ ∀ i < 2021, i ∉ x → i + 1 ∈ x) ∨
      ∃ i < 2021, i ∉ x ∧ i + 1 ∉ x ∧ y = x ∪ {i, i + 1})
    (x : Set (Fin 2022)) (hpair : HasPair (boardList x)) :
    ∃ y, IsValidMove x y ∧
      aliceScore (boardList x) ≤ bobScore (boardList y) := by
  rcases alice_move_exists (boardList x) hpair with ⟨ys, hm, hs⟩
  let y := setOfList ys
  have hvalid : IsValidMove x y := by
    rcases ListMove.exists_set_pair hm with ⟨i, hi, hi0, hi1, hset⟩
    rw [IsValidMove_def]
    exact Or.inr ⟨i, hi, hi0, hi1, hset⟩
  have hlen : ys.length = 2022 := by
    have h := ListMove.length_eq hm
    simp at h
    omega
  have hboard : boardList y = ys := boardList_setOfList hlen
  exact ⟨y, hvalid, by simpa [y, hboard] using hs⟩

lemma bob_set_move_exists
    {IsValidMove : Set (Fin 2022) → Set (Fin 2022) → Prop}
    (IsValidMove_def : ∀ x y, IsValidMove x y ↔
      (x = y ∧ ∀ i < 2021, i ∉ x → i + 1 ∈ x) ∨
      ∃ i < 2021, i ∉ x ∧ i + 1 ∉ x ∧ y = x ∪ {i, i + 1})
    (x : Set (Fin 2022)) (hpair : HasPair (boardList x)) :
    ∃ y, IsValidMove x y ∧
      aliceScore (boardList y) ≤ bobScore (boardList x) := by
  rcases bob_move_exists (boardList x) hpair with ⟨ys, hm, hs⟩
  let y := setOfList ys
  have hvalid : IsValidMove x y := by
    rcases ListMove.exists_set_pair hm with ⟨i, hi, hi0, hi1, hset⟩
    rw [IsValidMove_def]
    exact Or.inr ⟨i, hi, hi0, hi1, hset⟩
  have hlen : ys.length = 2022 := by
    have h := ListMove.length_eq hm
    simp at h
    omega
  have hboard : boardList y = ys := boardList_setOfList hlen
  exact ⟨y, hvalid, by simpa [y, hboard] using hs⟩

lemma validMove_count_false
    {IsValidMove : Set (Fin 2022) → Set (Fin 2022) → Prop}
    (IsValidMove_def : ∀ x y, IsValidMove x y ↔
      (x = y ∧ ∀ i < 2021, i ∉ x → i + 1 ∈ x) ∨
      ∃ i < 2021, i ∉ x ∧ i + 1 ∉ x ∧ y = x ∪ {i, i + 1})
    {x y : Set (Fin 2022)}
    (hpair : HasPair (boardList x)) (hmove : IsValidMove x y) :
    (boardList y).count false + 2 = (boardList x).count false := by
  rcases (IsValidMove_def x y).mp hmove with hsame | hadd
  · rcases hsame with ⟨rfl, hterm⟩
    exact False.elim ((not_hasPair_of_terminal hterm) hpair)
  · rcases hadd with ⟨i, hi, hi0, hi1, hy⟩
    exact (valid_add_pair_to_ListMove hi hi0 hi1 hy).count_false

def CounterGame
    (IsValidMove : Set (Fin 2022) → Set (Fin 2022) → Prop)
    (s : Set (Fin 2022) → Set (Fin 2022))
    (x : Set (Fin 2022)) (g : List (Set (Fin 2022))) : Prop :=
  (∃ gt, g = x :: gt) ∧
    List.IsChain IsValidMove g ∧
    (∀ i (h : i + 1 < g.length), Even i →
      g[i + 1]'h = s (g[i]'(Nat.lt_of_succ_lt h))) ∧
    ∃ gh y, g = gh ++ [y] ∧ yᶜ.ncard ≤ 290

lemma counterplay_exists
    {IsValidMove : Set (Fin 2022) → Set (Fin 2022) → Prop}
    (IsValidMove_def : ∀ x y, IsValidMove x y ↔
      (x = y ∧ ∀ i < 2021, i ∉ x → i + 1 ∈ x) ∨
      ∃ i < 2021, i ∉ x ∧ i + 1 ∉ x ∧ y = x ∪ {i, i + 1})
    (s : Set (Fin 2022) → Set (Fin 2022))
    (hs_valid : ∀ x, IsValidMove x (s x)) :
    ∀ x, aliceScore (boardList x) ≤ 290 →
      ∃ g, CounterGame IsValidMove s x g := by
  intro x hx
  refine (Nat.strong_induction_on (p := fun m =>
    ∀ x, (boardList x).count false = m → aliceScore (boardList x) ≤ 290 →
      ∃ g, CounterGame IsValidMove s x g) ((boardList x).count false) ?_) x rfl hx
  intro m ih x hcount hxpot
  by_cases hxpair : HasPair (boardList x)
  · let y := s x
    have hvalidxy : IsValidMove x y := by simpa [y] using hs_valid x
    have hyBpot : bobScore (boardList y) ≤ 290 :=
      le_trans (validMove_alice_le IsValidMove_def hvalidxy) hxpot
    by_cases hypair : HasPair (boardList y)
    · rcases bob_set_move_exists IsValidMove_def y hypair with
        ⟨z, hvalidyz, hzpot_step⟩
      have hzpot : aliceScore (boardList z) ≤ 290 :=
        le_trans hzpot_step hyBpot
      have hxy_count := validMove_count_false IsValidMove_def hxpair hvalidxy
      have hyz_count := validMove_count_false IsValidMove_def hypair hvalidyz
      have hzlt : (boardList z).count false < m := by
        rw [← hcount]
        omega
      rcases ih ((boardList z).count false) hzlt z rfl hzpot with
        ⟨tail, ⟨⟨zt, htail_start⟩, htail_chain, htail_conf, htail_final⟩⟩
      subst tail
      refine ⟨x :: y :: z :: zt, ?_⟩
      refine ⟨⟨y :: z :: zt, rfl⟩, ?_, ?_, ?_⟩
      · exact List.IsChain.cons_cons hvalidxy
          (List.IsChain.cons_cons hvalidyz htail_chain)
      · intro i hi he
        cases i with
        | zero =>
            rfl
        | succ i =>
            cases i with
            | zero =>
                rcases he with ⟨k, hk⟩
                omega
            | succ j =>
                have htail_hi : j + 1 < (z :: zt).length := by
                  simpa using hi
                have he_tail : Even j := by
                  rcases he with ⟨k, hk⟩
                  refine ⟨k - 1, ?_⟩
                  omega
                have ht := htail_conf j htail_hi he_tail
                simpa using ht
      · rcases htail_final with ⟨gh, w, hlast, hw⟩
        refine ⟨x :: y :: gh, w, ?_, hw⟩
        simp [hlast]
    · refine ⟨[x, y], ?_⟩
      refine ⟨⟨[y], rfl⟩, ?_, ?_, ?_⟩
      · exact List.IsChain.cons_cons hvalidxy (List.isChain_singleton y)
      · intro i hi he
        have hi0 : i = 0 := by
          simp at hi
          omega
        subst i
        rfl
      · refine ⟨[x], y, rfl, ?_⟩
        rw [← boardList_count_false y,
          ← noPair_bobScore (boardList y) hypair]
        exact hyBpot
  · refine ⟨[x], ?_⟩
    refine ⟨⟨[], rfl⟩, List.isChain_singleton x, ?_, ?_⟩
    · intro i hi _
      simp at hi
    · refine ⟨[], x, rfl, ?_⟩
      rw [← boardList_count_false x,
        ← noPair_aliceScore (boardList x) hxpair]
      exact hxpot

lemma boardList_empty :
    boardList (∅ : Set (Fin 2022)) = List.replicate 2022 false := by
  have hset :
      setOfList (List.replicate 2022 false) = (∅ : Set (Fin 2022)) := by
    ext i
    change (List.replicate 2022 false).getD i.val false = true ↔ False
    rw [List.getD_replicate (x := false) (y := false) i.isLt]
    simp
  rw [← hset]
  exact boardList_setOfList (by rw [List.length_replicate])

lemma aliceScore_empty :
    aliceScore (boardList (∅ : Set (Fin 2022))) = 290 := by
  rw [boardList_empty]
  unfold aliceScore score goodScore
  rw [← List.append_nil (List.replicate 2022 false)]
  rw [scoreAux_replicate_false pRun 0 2022 []]
  rw [goodAux_replicate_false 0 2022 []]
  norm_num [pRun, goodRunCount, GoodRun]

end Putnam2022A5

-- 290
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
      ((290) : ℕ ) := by
  classical
  constructor
  · let s : Set (Fin 2022) → Set (Fin 2022) := fun x =>
      if h : Putnam2022A5.HasPair (Putnam2022A5.boardList x) then
        Classical.choose (Putnam2022A5.alice_set_move_exists IsValidMove_def x h)
      else x
    have hs_valid : ∀ x, IsValidMove x (s x) := by
      intro x
      dsimp [s]
      by_cases h : Putnam2022A5.HasPair (Putnam2022A5.boardList x)
      · rw [dif_pos h]
        exact (Classical.choose_spec
          (Putnam2022A5.alice_set_move_exists IsValidMove_def x h)).1
      · rw [dif_neg h]
        exact Putnam2022A5.valid_self_of_noPair IsValidMove_def h
    refine ⟨s, hs_valid, ?_⟩
    intro g hgvalid hgconf
    rcases (IsValidGame_def g).mp hgvalid with ⟨⟨gt, hgstart⟩, hgchain⟩
    have hconf := (ConformsToStrategy_def g s).mp hgconf
    have hstart_len : 0 < g.length := by
      rw [hgstart]
      simp
    have hstart : g[0] = (∅ : Set (Fin 2022)) := by
      subst g
      rfl
    have hboard_empty :
        Putnam2022A5.boardList (∅ : Set (Fin 2022)) =
          List.replicate 2022 false := by
      have hset :
          Putnam2022A5.setOfList (List.replicate 2022 false) =
            (∅ : Set (Fin 2022)) := by
        ext i
        change (List.replicate 2022 false).getD i.val false = true ↔ False
        rw [List.getD_replicate (x := false) (y := false) i.isLt]
        simp
      rw [← hset]
      exact Putnam2022A5.boardList_setOfList (by rw [List.length_replicate])
    have halice_start :
        Putnam2022A5.aliceScore (Putnam2022A5.boardList (∅ : Set (Fin 2022))) = 290 := by
      rw [hboard_empty]
      unfold Putnam2022A5.aliceScore Putnam2022A5.score Putnam2022A5.goodScore
      rw [← List.append_nil (List.replicate 2022 false)]
      rw [Putnam2022A5.scoreAux_replicate_false Putnam2022A5.pRun 0 2022 []]
      rw [Putnam2022A5.goodAux_replicate_false 0 2022 []]
      norm_num [Putnam2022A5.pRun, Putnam2022A5.goodRunCount, Putnam2022A5.GoodRun]
    have hs_alice :
        ∀ x, Putnam2022A5.aliceScore (Putnam2022A5.boardList x) ≤
          Putnam2022A5.bobScore (Putnam2022A5.boardList (s x)) := by
      intro x
      dsimp [s]
      by_cases h : Putnam2022A5.HasPair (Putnam2022A5.boardList x)
      · rw [dif_pos h]
        exact (Classical.choose_spec
          (Putnam2022A5.alice_set_move_exists IsValidMove_def x h)).2
      · rw [dif_neg h]
        rw [Putnam2022A5.noPair_aliceScore (Putnam2022A5.boardList x) h,
          Putnam2022A5.noPair_bobScore (Putnam2022A5.boardList x) h]
    have hinv :
        ∀ i (hi : i < g.length),
          (Even i → 290 ≤ Putnam2022A5.aliceScore (Putnam2022A5.boardList g[i])) ∧
          (Odd i → 290 ≤ Putnam2022A5.bobScore (Putnam2022A5.boardList g[i])) := by
      intro i
      induction i with
      | zero =>
          intro hi
          constructor
          · intro _
            rw [hstart]
            exact le_of_eq halice_start.symm
          · intro hodd
            rcases hodd with ⟨k, hk⟩
            omega
      | succ i ih =>
          intro hi
          have hiprev : i < g.length := by omega
          have hstep_lt : i + 1 < g.length := by simpa using hi
          have hmove : IsValidMove g[i] g[i + 1] :=
            List.IsChain.getElem hgchain i hstep_lt
          constructor
          · intro heven
            have hodd_prev : Odd i := by
              rcases heven with ⟨k, hk⟩
              refine ⟨k - 1, ?_⟩
              omega
            have hprev := (ih hiprev).2 hodd_prev
            have hle := Putnam2022A5.validMove_bob_le IsValidMove_def hmove
            exact le_trans hprev hle
          · intro hodd
            have heven_prev : Even i := by
              rcases hodd with ⟨k, hk⟩
              refine ⟨k, ?_⟩
              omega
            have hprev := (ih hiprev).1 heven_prev
            have hnext : g[i + 1] = s g[i] := hconf i hstep_lt heven_prev
            have hle := hs_alice g[i]
            rw [hnext]
            exact le_trans hprev hle
    let last := g.getLast (List.ne_nil_of_length_pos hstart_len)
    refine ⟨g.dropLast, last, ?_, ?_⟩
    · exact (List.dropLast_append_getLast (List.ne_nil_of_length_pos hstart_len)).symm
    · have hlast_idx : g.length - 1 < g.length :=
        Nat.sub_one_lt (Nat.ne_of_gt hstart_len)
      have hlast_eq : last = g[g.length - 1] := by
        exact List.getLast_eq_getElem (List.ne_nil_of_length_pos hstart_len)
      rw [hlast_eq]
      by_cases he : Even (g.length - 1)
      · have hpot := (hinv (g.length - 1) hlast_idx).1 he
        have hcount := Putnam2022A5.aliceScore_le_count
          (Putnam2022A5.boardList g[g.length - 1])
        rw [Putnam2022A5.boardList_count_false] at hcount
        exact le_trans hpot hcount
      · have ho : Odd (g.length - 1) := Nat.not_even_iff_odd.mp he
        have hpot := (hinv (g.length - 1) hlast_idx).2 ho
        have hcount := Putnam2022A5.bobScore_le_count
          (Putnam2022A5.boardList g[g.length - 1])
        rw [Putnam2022A5.boardList_count_false] at hcount
        exact le_trans hpot hcount
  · intro n hn
    rcases hn with ⟨s, hs_valid, hs_guarantee⟩
    rcases Putnam2022A5.counterplay_exists IsValidMove_def s hs_valid
        (∅ : Set (Fin 2022)) (by rw [Putnam2022A5.aliceScore_empty]) with
      ⟨g, hcounter⟩
    rcases hcounter with ⟨⟨gt, hgstart⟩, hgchain, hgconf_counter, hfinal⟩
    have hgvalid : IsValidGame g := by
      rw [IsValidGame_def]
      exact ⟨⟨gt, hgstart⟩, hgchain⟩
    have hgconf : ConformsToStrategy g s := by
      rw [ConformsToStrategy_def]
      exact hgconf_counter
    rcases hs_guarantee g hgvalid hgconf with ⟨gh₁, x, hgx, hnx⟩
    rcases hfinal with ⟨gh₂, y, hgy, hy⟩
    have hxy : x = y := by
      have hlast := congrArg (fun l : List (Set (Fin 2022)) => l.getLast?) (hgx.symm.trans hgy)
      simpa using hlast
    rw [hxy] at hnx
    exact le_trans hnx hy
