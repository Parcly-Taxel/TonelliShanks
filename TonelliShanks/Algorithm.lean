import Mathlib.NumberTheory.LegendreSymbol.Basic
import Velvet.Std

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/-- I added this lemma to mathlib in https://github.com/leanprover-community/mathlib4/pull/36799 -/
lemma Nat.Prime.odd_iff {p : ℕ} (hp : Prime p) : Odd p ↔ 3 ≤ p := by
  rw [← not_iff_not, not_odd_iff_even, hp.even_iff, not_le]
  have := hp.two_le
  grind

lemma ZMod.euler_criterion' {p : ℕ} {a : ZMod p} (hp : p.Prime ∧ Odd p) :
    ¬IsSquare a ↔ a ^ (p / 2) = -1 := by
  rw [hp.1.odd_iff] at hp
  have : Fact (1 < p) := ⟨by grind⟩
  obtain rfl | ha := eq_or_ne a 0
  · rw [zero_pow (by grind)]
    simp
  · have : Fact p.Prime := ⟨hp.1⟩
    have nnp : (-1 : ZMod p) ≠ 1 := @ZMod.neg_one_ne_one p ⟨by grind⟩
    rw [euler_criterion _ ha]
    obtain h | h := ZMod.pow_div_two_eq_neg_one_or_one p ha
    · simp [h, nnp.symm]
    · simp [h, nnp]

lemma exists_nonresidue {p : ℕ} (hp : p.Prime ∧ Odd p) : ∃ z : ZMod p, ¬IsSquare z := by
  have : NeZero p := ⟨hp.1.ne_zero⟩
  rw [hp.1.odd_iff] at hp
  let f (z : ZMod p) := z ^ 2
  have nfsurj : ¬f.Injective := by
    rw [Function.not_injective_iff]
    exact ⟨1, -1, by simp [f], (@ZMod.neg_one_ne_one p ⟨by grind⟩).symm⟩
  simp_rw [Finite.injective_iff_surjective, Function.Surjective, f, eq_comm] at nfsurj
  push Not at nfsurj
  obtain ⟨z, hz⟩ := nfsurj
  refine ⟨z, ?_⟩
  rwa [isSquare_iff_exists_sq, not_exists]

method findNonresidue (p : ℕ) (hp : p.Prime ∧ Odd p) return (z : ZMod p)
  ensures ¬IsSquare z
  do
    let mut i := 0
    while (i : ZMod p) ^ (p / 2) ≠ -1 ∧ i < p
      invariant ∀ (j : ℕ), j < i → (j : ZMod p) ^ (p / 2) ≠ -1
      invariant i ≤ p
    do
      i := i + 1
    return i

prove_correct findNonresidue by
  loom_solve
  have : NeZero p := ⟨hp.1.ne_zero⟩
  have inp : i ≠ p := by
    contrapose! invariant_1
    obtain ⟨z, hz⟩ := exists_nonresidue hp
    subst i
    refine ⟨z.val, z.val_lt, ?_⟩
    rwa [← ZMod.euler_criterion' hp, ZMod.natCast_zmod_val]
  replace invariant_2 := invariant_2.lt_of_ne inp
  simp_rw [invariant_2, and_true, not_ne_iff] at done_1
  rwa [ZMod.euler_criterion' hp]

method findQS (n : ℕ) return (qs : ℕ × ℕ)
  ensures qs.1 * 2 ^ qs.2 = n ∧ Odd qs.1
  do
    let mut qs := (n, 0)
    while Even qs.1
      invariant qs.1 * 2 ^ qs.2 = n
    do
      qs := (qs.1 / 2, qs.2 + 1)
    return qs

prove_correct findQS by
  loom_solve
  rwa [pow_succ', ← mul_assoc, Nat.div_mul_cancel (by grind)]

method findExponent (p : ℕ) (t : ZMod p) (m : ℕ) return (i : ℕ)
  require 0 < m
  require t ^ 2 ^ (m - 1) = 1
  ensures t ^ 2 ^ i = 1 ∧ i < m ∧ ∀ j < i, t ^ 2 ^ j ≠ 1
  do
    let mut i := 0
    let mut u := t
    while u ≠ 1
      invariant u = t ^ 2 ^ i
      invariant i < m
      invariant ∀ j < i, t ^ 2 ^ j ≠ 1
    do
      u := u ^ 2
      i := i + 1
    return i

prove_correct findExponent by
  loom_solve
  rw [invariant_1, ← pow_mul, pow_succ]

method tonelliShanks (p : ℕ) (hp : p.Prime ∧ Odd p) (n : ZMod p) return (rout : Option (ZMod p))
  ensures rout = none ∧ ¬IsSquare n ∨ ∃ r, rout = some r ∧ r ^ 2 = n
  do
    if n = 0 then return some 0
    let ⟨q, s⟩ ← findQS (p - 1)
    let mut m := s
    let mut c ← findNonresidue p hp
    c := c ^ q
    let mut t := n ^ q
    let mut r := n ^ ((q + 1) / 2)
    if t ^ 2 ^ (m - 1) = -1 then return none
    while t ≠ 1
      invariant c ^ 2 ^ (m - 1) = -1
      invariant t ^ 2 ^ (m - 1) = 1
      invariant r ^ 2 = t * n
    do
      let i ← findExponent p t m
      let b := c ^ 2 ^ (m - i - 1)
      m := i
      c := b ^ 2
      t := t * b ^ 2
      r := r * b
    return some r

#eval (tonelliShanks 41 (by decide) 5).run -- example given on Wikipedia, 28
#eval (tonelliShanks 41 (by decide) 4).run -- 2
#eval (tonelliShanks 41 (by decide) 3).run -- none
#eval (tonelliShanks 41 (by decide) 2).run -- 17
#eval (tonelliShanks 41 (by decide) 1).run -- 1
#eval (tonelliShanks 41 (by decide) 0).run -- 0
#eval (tonelliShanks 41 (by decide) (-1)).run -- 32

#eval (tonelliShanks 137 (by decide) 2).run -- 106
#eval (tonelliShanks 137 (by decide) 3).run -- none
#eval (tonelliShanks 137 (by decide) 5).run -- none
#eval (tonelliShanks 137 (by decide) 7).run -- 12
#eval (tonelliShanks 137 (by decide) 11).run -- 55

#eval (tonelliShanks 103 (by decide) 2).run -- 38
#eval (tonelliShanks 103 (by decide) 3).run -- none
#eval (tonelliShanks 103 (by decide) 5).run -- none
#eval (tonelliShanks 103 (by decide) 7).run -- 25
#eval (tonelliShanks 103 (by decide) 11).run -- none

section Subgoals

variable {p q s : ℕ} {n : ZMod p} (hp : Nat.Prime p ∧ Odd p) (hq₁ : q * 2 ^ s = p - 1) (hq₂ : Odd q)

section

include hp hq₁ hq₂

lemma s_pos : 0 < s := by
  by_contra! h
  rw [Nat.le_zero] at h
  simp only [h, pow_zero, mul_one] at hq₁
  grind

lemma pow_rewrite : (n ^ q) ^ 2 ^ (s - 1) = n ^ (p / 2) := by
  have spos := s_pos hp hq₁ hq₂
  rw [← Nat.sub_one_add_one spos.ne', pow_succ, ← mul_assoc] at hq₁
  rw [show p / 2 = (p - 1) / 2 by grind, ← hq₁, Nat.mul_div_cancel _ zero_lt_two, ← pow_mul]

@[grind]
lemma subgoal_1 (hn₁ : n ≠ 0) (hn₂ : (n ^ q) ^ 2 ^ (s - 1) = -1) : ¬IsSquare n := by
  have : Fact p.Prime := ⟨hp.1⟩
  rw [pow_rewrite hp hq₁ hq₂] at hn₂
  rw [ZMod.euler_criterion _ hn₁, hn₂]
  exact @ZMod.neg_one_ne_one p ⟨by grind [Nat.Prime.odd_iff]⟩

@[grind]
lemma subgoal_5 {z : ZMod p} (hz : ¬IsSquare z) : (z ^ q) ^ 2 ^ (s - 1) = -1 := by
  rwa [pow_rewrite hp hq₁ hq₂, ← ZMod.euler_criterion' hp]

@[grind]
lemma subgoal_6 (hn₁ : n ≠ 0) (hn₂ : (n ^ q) ^ 2 ^ (s - 1) ≠ -1) : (n ^ q) ^ 2 ^ (s - 1) = 1 := by
  have : Fact p.Prime := ⟨hp.1⟩
  rw [pow_rewrite hp hq₁ hq₂] at hn₂ ⊢
  have key := ZMod.pow_div_two_eq_neg_one_or_one p hn₁
  exact key.resolve_right hn₂

end

@[grind]
lemma subgoal_2 {m : ℕ} {t : ZMod p} (invar₂ : t ^ 2 ^ (m - 1) = 1) (ht : t ≠ 1) : 0 < m := by
  by_contra! h
  simp_all

@[grind]
lemma subgoal_3 {c t : ZMod p} {m i : ℕ} (invar₁ : c ^ 2 ^ (m - 1) = -1) (hi : i < m)
    (ht₁ : t ^ 2 ^ i = 1) (ht₂ : t ≠ 1) : ((c ^ 2 ^ (m - i - 1)) ^ 2) ^ 2 ^ (i - 1) = -1 := by
  have ipos : i ≠ 0 := by
    by_contra! h
    simp_all
  rwa [← pow_mul, ← pow_mul, ← pow_succ', ← pow_add, show m - i - 1 + (i - 1 + 1) = m - 1 by grind]

@[grind]
lemma subgoal_4 {c t : ZMod p} {m i : ℕ} (hp : p.Prime ∧ Odd p)
    (invar₁ : c ^ 2 ^ (m - 1) = -1) (hi : i < m)
    (ht₁ : t ^ 2 ^ i = 1) (ht₂ : t ≠ 1) (ht₃ : ∀ j < i, t ^ 2 ^ j ≠ 1) :
    (t * (c ^ 2 ^ (m - i - 1)) ^ 2) ^ 2 ^ (i - 1) = 1 := by
  have : Fact p.Prime := ⟨hp.1⟩
  have ipos : i ≠ 0 := by
    by_contra! h
    simp_all
  rw [mul_pow, subgoal_3 invar₁ hi ht₁ ht₂, mul_neg_one, neg_eq_iff_eq_neg]
  rw [← Nat.sub_one_add_one ipos, pow_succ, pow_mul, sq_eq_one_iff] at ht₁
  exact ht₁.resolve_left (ht₃ _ (by grind))

end Subgoals

set_option maxHeartbeats 1500000 in
prove_correct tonelliShanks by
  loom_solve
  · exact subgoal_2 invariant_2 if_pos
  · rw [← pow_mul, Nat.div_mul_cancel (by grind), pow_succ]
