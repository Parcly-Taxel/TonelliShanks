import Mathlib.NumberTheory.LegendreSymbol.Basic
import Velvet.Std

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/-- I added this lemma to mathlib in https://github.com/leanprover-community/mathlib4/pull/36799 -/
lemma Nat.Prime.odd_iff {p : ℕ} (hp : Prime p) : Odd p ↔ 3 ≤ p := by
  rw [← not_iff_not, not_odd_iff_even, hp.even_iff, not_le]
  have := hp.two_le
  grind

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

/-- Return the smallest quadratic nonresidue modulo an odd prime `p`.
This is [OEIS A053760](https://oeis.org/A053760). -/
def qnr (p : ℕ) (hp : p.Prime ∧ Odd p) : ℕ :=
  letI : NeZero p := ⟨hp.1.ne_zero⟩
  ((Finset.range p).filter fun z : ℕ ↦ ¬IsSquare (z : ZMod p)).min' (by
    obtain ⟨q, hq⟩ := exists_nonresidue hp
    refine ⟨q.val, ?_⟩
    rw [Finset.mem_filter, Finset.mem_range, ZMod.natCast_zmod_val]
    exact ⟨q.val_lt, hq⟩)

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

lemma not_isSquare_qnr {p : ℕ} (hp : p.Prime ∧ Odd p) : ¬IsSquare (qnr p hp : ZMod p) := by
  unfold qnr
  generalize_proofs nzp nem
  have := Finset.min'_mem _ nem
  rw [Finset.mem_filter] at this
  exact this.2

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
    let mut c : ZMod p := (qnr p hp) ^ q
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
lemma subgoal_5 : (qnr p hp ^ q : ZMod p) ^ 2 ^ (s - 1) = -1 := by
  have : Fact p.Prime := ⟨hp.1⟩
  rw [pow_rewrite hp hq₁ hq₂]
  have not0 := not_isSquare_qnr hp
  have znz : (qnr p hp : ZMod p) ≠ 0 := by
    by_contra! h
    simp [h] at not0
  rw [ZMod.euler_criterion _ znz] at not0
  exact (ZMod.pow_div_two_eq_neg_one_or_one p znz).resolve_left not0

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
    (invar₁ : c ^ 2 ^ (m - 1) = -1) (invar₂ : t ^ 2 ^ (m - 1) = 1) (hi : i < m)
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

prove_correct tonelliShanks by
  loom_solve
  rw [← pow_mul, Nat.div_mul_cancel (by grind), pow_succ]
