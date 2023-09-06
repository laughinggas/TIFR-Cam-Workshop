/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Parity
import Mathlib.Algebra.Order.WithZero
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic

/-!
# Properties of natural numbers
This file describes some properties of natural numbers that are required throughout this project. 
In the end, we keep some `helper` lemmas which are specific to this project.

## Tags
Naturals
-/

namespace Nat
-- useful lemma : dvd_neg
lemma dvd_sub_symm (a b n : ℤ) (h : n ∣ a - b) : n ∣ b - a := by sorry

-- useful tactic : `by_contra`
-- useful lemmas : Nat.Prime.not_coprime_iff_dvd, Nat.dvd_sub, Nat.sub_sub_self
-- what does subtraction on Nat mean?
lemma coprime_sub {n m : ℕ} (h : n.coprime m) (hn : m ≤ n) : (n - m).coprime n := sorry

-- useful lemma : ne_zero_of_lt
lemma ne_zero_of_lt' (b : ℕ) {a : ℕ} [Fact (b < a)] : a ≠ 0 := sorry

variable {p : ℕ} [Fact p.Prime] {d : ℕ}
-- useful lemmas : Nat.one_lt_iff_ne_zero_and_ne_one, Nat.mul_ne_zero, pow_ne_zero, Nat.Prime.ne_zero
lemma one_lt_mul_pow_of_ne_one [Fact (0 < d)] {k : ℕ} (h : d * p^k ≠ 1) : 1 < d * p^k := sorry

-- useful tactic : `cases'`
-- useful lemmas : not_lt_iff_eq_or_lt, Nat.lt_one_iff, Nat.mul_eq_zero
lemma mul_pow_eq_one_of_mul_pow_sq_not_one_lt [Fact (0 < d)] {n : ℕ} (h : ¬ 1 < d * p^(2 * n)) : d * p^n = 1 := sorry

-- useful lemmas : fact_iff, pow_pos, Nat.Prime.pos
instance [Fact (0 < d)] {n : ℕ} : Fact (0 < d * p^n) := sorry

-- try to use inferInstance
lemma mul_prime_pow_pos [Fact (0 < d)] (m : ℕ) : 0 < d * p^m := sorry

-- useful lemmas : mul_lt_mul', Nat.pow_lt_pow_succ
lemma mul_pow_lt_mul_pow_succ [Fact (0 < d)] (m : ℕ) : d * p ^ m < d * p ^ m.succ := sorry

-- useful tactic : `conv`
-- useful lemmas : pow_lt_pow
lemma lt_pow {n a : ℕ} (h1 : 1 < a) (h2 : 1 < n) : a < a^n := sorry

lemma le_pow {n a : ℕ} (h1 : 1 ≤ a) (h2 : 1 ≤ n) : a ≤ a^n := sorry

-- useful lemmas : lt_mul_of_one_lt_left, Nat.succ_le_iff, Fact.out
lemma pow_lt_mul_pow_succ_right [Fact (0 < d)] (m : ℕ) : p ^ m < d * p ^ m.succ := sorry

-- useful lemmas : lt_of_le_of_lt, le_mul_iff_one_le_left, lt_trans, Nat.lt_pow
lemma lt_mul_pow_right {m a b : ℕ} (h1 : 0 < b) (h2 : 1 < a) (h3 : 1 < m) : a < b * a^m := sorry

-- useful lemmas : le_mul_iff_one_le_left
lemma le_mul_pow_right {m a b : ℕ} (h1 : 0 < b) (h2 : 1 < a) (h3 : 1 ≤ m) : a ≤ b * a^m := sorry

-- useful lemmas : Nat.coprime_mul_iff_right, Nat.coprime.pow_right
lemma coprime.mul_pow {a b c : ℕ} (n : ℕ) (hc' : c.coprime a) (hc : c.coprime b) :
  c.coprime (a * b^n) := sorry

-- useful lemmas : Nat.succ_le_succ, Nat.succ_mul
lemma add_sub_pred (n : ℕ) : n + (n - 1) = 2 * n - 1 := sorry

-- useful lemmas : Nat.mod_eq_sub_mod, Nat.odd_iff, Nat.succ_eq_add_one, Nat.succ_le_succ
lemma two_mul_sub_one_mod_two_eq_one {k : ℕ} (hk : 1 ≤ k) : (2 * k - 1) % 2 = 1 := sorry

-- try `library_search`
lemma pred_add_one_eq_self {n : ℕ} (hn : 0 < n) : n.pred + 1 = n := sorry

-- useful tactic : `exfalso`
-- useful lemma : Nat.coprime_or_dvd_of_prime
lemma prime_dvd_of_not_coprime (p : ℕ) [Fact p.Prime] {n : ℕ} (h : ¬ n.coprime p) : p ∣ n := sorry

lemma eq_zero_of_not_pos {n : ℕ} (hn : ¬ 0 < n) : n = 0 := sorry

-- useful tactic : `norm_cast`
-- useful lemmas : Nat.isCoprime_iff_coprime, IsCoprime.of_isCoprime_of_dvd_left, Nat.isCoprime_iff_coprime
lemma coprime_of_dvd_of_coprime {m n x y : ℕ} (h : m.coprime n) (hx : x ∣ m) (hy : y ∣ n) :
  x.coprime y := sorry

-- useful lemmas : Nat.sub_eq_zero_iff_le
lemma sub_ne_zero {n k : ℕ} (h : k < n) : n - k ≠ 0 := sorry
end Nat

-- useful lemmas : lcm_eq_left_iff, dvd_mul_of_dvd_right, dvd_pow_self
lemma helper_4 {x y : ℕ} (m : ℕ) [Fact (0 < m)] : GCDMonoid.lcm (x * y^m) y = x * y^m := sorry

variable {p : ℕ} [Fact p.Prime] {d m : ℕ}
-- useful tactics : `conv_rhs`, `congr`
-- useful lemmas : Nat.sub_succ, Nat.succ_eq_add_one, Nat.succ_pred_eq_of_pos, lt_tsub_iff_right
lemma helper_5 {k : ℕ} (hk : 1 < k) : (d * p^m)^(k - 1) = (d * p^m) * (d * p^m)^(k - 2) := sorry