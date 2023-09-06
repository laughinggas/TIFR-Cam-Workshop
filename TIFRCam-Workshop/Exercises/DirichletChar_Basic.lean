import Mathlib.NumberTheory.LegendreSymbol.MulCharacter
import Mathlib.Data.ZMod.Algebra

/-- This file is about Dirichlet characters. We define them as multiplicative homomorphisms on `ZMod n`. 
  Other important definitions include : 
  * `change_level`
  * `conductor`
  * `is_primitive`
  * `reduction`
  * `mul`
  * `is_odd`
  * `is_even`
  
  Feel free to pick any section you like and solving / building its API! 
  Remember to always have the mathematical proof in mind before solving these.
  A lot of the supporting theory can be found in the files : 
    Mathlib.NumberTheory.LegendreSymbol.MulCharacter 
    Mathlib.Algebra.Group.Units
  If you use `aesop` or `simp`, make sure you know what lemmas it is using.
  The lemmas termed as useful are lemmas you might need (but not know the name of) 
    which are not contained in this file. If you do not need them, that is great! -/

-- useful lemmas : Nat.succ_le_succ_iff, Nat.le_zero
-- extra hint : try `cases`
lemma Nat.le_one {n : ℕ} (h : n ≤ 1) : n = 0 ∨ n = 1 := sorry

@[simp]
lemma castHom_self {n : ℕ} : ZMod.castHom dvd_rfl (ZMod n) = RingHom.id (ZMod n) := sorry

@[reducible]def DirichletChar (R : Type) [Monoid R] (n : ℕ) := (ZMod n)ˣ →* Rˣ

namespace MulChar
-- try the tactic `aesop`
lemma coe_toMonoidHom {R R' : Type} [CommMonoid R] [CommMonoidWithZero R'] (χ : MulChar R R') (x : R) : χ.toMonoidHom x = χ x := sorry
end MulChar

open MulChar
variable {R : Type} [CommMonoidWithZero R] {n : ℕ} (χ : DirichletChar R n)

namespace DirichletChar
-- if you don't know what `ofUnitHom` is, you can press Ctrl+Click on it. 
-- This will take you to the file where it is defined. 
-- Roam around a bit in the file, so you understand its properties.
-- useful lemmas : IsUnit.unit_spec
-- useful tactic : `conv_lhs`
lemma ofUnitHom_eq_char' {a : ZMod n} (ha : IsUnit a) :
  ofUnitHom χ a = χ ha.unit := sorry
  
-- useful lemmas : map_nonunit'
lemma ofUnitHom_eq_zero {a : ZMod n} (ha : ¬ IsUnit a) :
  ofUnitHom χ a = 0 := sorry

lemma ofUnitHom_eq_iff (ψ : DirichletChar R n) :
  χ = ψ ↔ ofUnitHom χ = ofUnitHom ψ := sorry

-- Commutativity required from here
lemma ofUnitHom_eval_sub (x : ZMod n) :
  ofUnitHom χ (n - x) = ofUnitHom χ (-x) := sorry

-- useful lemmas : ZMod.nat_cast_zmod_eq_zero_iff_dvd
lemma is_periodic (m : ℕ) (hm : n ∣ m) (a : ℤ) :
  ofUnitHom χ (a + m) = ofUnitHom χ a := sorry

/-- Extends the Dirichlet character χ of level n to level m, where n ∣ m. -/
def change_level {m : ℕ} (hm : n ∣ m) : DirichletChar R n →* DirichletChar R m :=
{ toFun := λ ψ => ψ.comp (Units.map (ZMod.castHom hm (ZMod n)))
  map_one' := sorry
  map_mul' := sorry }

lemma change_level_def {m : ℕ} (hm : n ∣ m) : change_level hm χ = χ.comp (Units.map (ZMod.castHom hm (ZMod n))) := sorry

namespace change_level
lemma self : change_level (dvd_refl n) χ = χ := sorry

-- a useful tactic is `repeat`, `change` and `congr`
-- useful lemmas are MonoidHom.comp_assoc, Units.map_comp
lemma trans {m d : ℕ} (hm : n ∣ m) (hd : m ∣ d) :
  change_level (dvd_trans hm hd) χ = change_level hd (change_level hm χ) := sorry

lemma ofUnitHom_eq {m : ℕ} (hm : n ∣ m) (a : Units (ZMod m)) :
  ofUnitHom (change_level hm χ) a = ofUnitHom χ a := sorry

-- useful lemmas : IsUnit.unit_spec
lemma ofUnitHom_eq' {m : ℕ} (hm : n ∣ m) {a : ZMod m} (ha : IsUnit a) :
ofUnitHom (change_level hm χ) a = ofUnitHom χ a := sorry

end change_level

/-- χ₀ of level d factors through χ of level n if d ∣ n and χ₀ = χ ∘ (ZMod n → ZMod d). -/
structure factors_through (d : ℕ) : Prop :=
(dvd : d ∣ n)
(ind_char : ∃ χ₀ : DirichletChar R d, χ = change_level dvd χ₀)
-- in this structure, the way to call the property `ind_char` is by `factors_through.ind_char`

namespace factors_through
-- useful lemma : Classical.choose_spec
lemma spec {d : ℕ} (h : factors_through χ d) :
  χ = change_level h.1 (Classical.choose (h.ind_char)) := sorry
end factors_through

/-- The set of natural numbers for which a Dirichlet character is periodic. -/
def conductor_set : Set ℕ := {x : ℕ | χ.factors_through x}

-- compare the output of `aesop` and `Iff.refl`
lemma mem_conductor_set_iff {x : ℕ} : x ∈ χ.conductor_set ↔ χ.factors_through x := sorry

-- you might need the tactic `constructor`
lemma level_mem_conductor_set : n ∈ conductor_set χ := sorry

lemma mem_conductor_set_dvd {x : ℕ} (hx : x ∈ χ.conductor_set) : x ∣ n := sorry

lemma mem_conductor_set_factors_through {x : ℕ} (hx : x ∈ χ.conductor_set) : χ.factors_through x := sorry

/-- The minimum natural number n for which a Dirichlet character is periodic.
  The Dirichlet character χ can then alternatively be reformulated on ℤ/nℤ. -/
noncomputable def conductor : ℕ := sInf (conductor_set χ)

namespace conductor
-- useful lemmas : Nat.sInf_mem, Set.nonempty_of_mem
lemma mem_conductor_set : conductor χ ∈ conductor_set χ := sorry

lemma dvd_lev : χ.conductor ∣ n := sorry

lemma factors_through : χ.factors_through χ.conductor := sorry

-- useful lemmas : Units.eq_iff, MonoidHom.map_one, Subsingleton.elim
lemma eq_one (hχ : χ.conductor = 1) : χ = 1 := sorry

-- useful lemmas : Nat.sInf_le, Nat.le_one
lemma one (hn : 0 < n) : (1 : DirichletChar R n).conductor = 1 := sorry

variable {χ}
lemma eq_one_iff (hn : 0 < n) : χ = 1 ↔ χ.conductor = 1 := sorry

-- useful lemmas : zero_dvd_iff, Nat.sInf_eq_zero
lemma eq_zero_iff_level_eq_zero : χ.conductor = 0 ↔ n = 0 := sorry
end conductor

/-- A character is primitive if its level is equal to its conductor. -/
def is_primitive : Prop := χ.conductor = n

lemma is_primitive_def : χ.is_primitive ↔ χ.conductor = n := sorry

namespace is_primitive
-- useful lemma : Nat.dvd_one
lemma one : is_primitive (1 : DirichletChar R 1) := sorry

-- useful lemmas : Nat.sInf_eq_zero
lemma one_lev_zero : (1 : DirichletChar R 0).is_primitive := sorry
end is_primitive

-- useful lemma : one_dvd
lemma conductor_one_dvd (n : ℕ) : conductor (1 : DirichletChar R 1) ∣ n := sorry

/-- If m = n are positive natural numbers, then ZMod m ≃ ZMod n. -/
def ZMod.mul_equiv {a b : ℕ} (h : a = b) : ZMod a ≃* ZMod b := by { rw [h] }

/-- If m = n are positive natural numbers, then their Dirichlet character spaces are the same. -/
def equiv {a b : ℕ} (h : a = b) : DirichletChar R a ≃* DirichletChar R b := by { rw [h] }

/-- The primitive character associated to a Dirichlet character. -/
noncomputable def reduction : DirichletChar R χ.conductor :=
  Classical.choose ((conductor.factors_through χ).ind_char)

-- useful tactic : `fconstructor`
-- useful lemma : Nat.sInf_le, RingHom.ext_zmod
lemma mem_conductor_set_eq_conductor {d : ℕ} (hd : d ∈ χ.conductor_set) :
  χ.conductor ≤ (Classical.choose hd.2).conductor := sorry

-- useful tactic : `by_cases`, `conv_rhs`
-- useful lemmas : le_antisymm, Nat.le_of_dvd, Nat.pos_of_ne_zero
lemma reduction_is_primitive : (χ.reduction).is_primitive := sorry

-- useful lemma : Nat.one_pos
lemma reduction_one (hn : 0 < n) : (1 : DirichletChar R n).reduction = 1 := sorry

lemma ofUnitHom_mul (ψ : DirichletChar R n) : ofUnitHom (χ * ψ) = (ofUnitHom χ) * (ofUnitHom ψ) := sorry
  
lemma asso_primitive_conductor_eq {n : ℕ} (χ : DirichletChar R n) :
  χ.reduction.conductor = χ.conductor := sorry

open Nat
/-- Primitive character associated to multiplication of Dirichlet characters, 
  after changing both levels to the same -/
noncomputable def mul {m : ℕ} (χ₁ : DirichletChar R n) (χ₂ : DirichletChar R m) :=
reduction (change_level (dvd_lcm_left n m) χ₁ * change_level (dvd_lcm_right n m) χ₂)

lemma mul_def {n m : ℕ} {χ : DirichletChar R n} {ψ : DirichletChar R m} :
  χ.mul ψ = reduction (change_level _ χ * change_level _ ψ) := sorry

namespace is_primitive
lemma mul {m : ℕ} (ψ : DirichletChar R m) : (mul χ ψ).is_primitive := sorry
end is_primitive

variable {S : Type} [CommRing S] {m : ℕ} (ψ : DirichletChar S m)

/-- A Dirichlet character is odd if its value at -1 is -1. -/
def is_odd : Prop := ψ (-1) = -1

/-- A Dirichlet character is even if its value at -1 is 1. -/
def is_even : Prop := ψ (-1) = 1

-- useful lemmas : Units.eq_iff, Units.val_pow_eq_pow_val, Units.val_one, _root_.sq_sub_sq, _root_.mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg
lemma is_odd_or_is_even [NoZeroDivisors S] : ψ.is_odd ∨ ψ.is_even := sorry

-- useful lemma : ofUnitHom_coe
lemma odd_ofUnitHom_eval_neg_one (hψ : ψ.is_odd) :
  ofUnitHom ψ (-1) = -1 := sorry

-- useful lemma : ofUnitHom_coe
lemma even_ofUnitHom_eval_neg_one (hψ : ψ.is_even) :
  ofUnitHom ψ (-1) = 1 := sorry

-- useful lemmas : neg_one_mul, MulChar.coe_toMonoidHom, MonoidHom.map_mul
lemma asso_odd_DirichletChar_eval_sub (x : ZMod m) (hψ : ψ.is_odd) :
  ofUnitHom ψ (m - x) = -(ofUnitHom ψ x) := sorry

lemma asso_even_DirichletChar_eval_sub (x : ZMod m) (hψ : ψ.is_even) :
  ofUnitHom ψ (m - x) = ofUnitHom ψ x := sorry

end DirichletChar