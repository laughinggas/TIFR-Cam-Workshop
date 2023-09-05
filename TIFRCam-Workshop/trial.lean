import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Order.LocallyFinite
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Real.ENNReal
import Mathlib.Data.ZMod.Algebra

open SimpleGraph

--def subset_of_Ico {n i : Nat} (h : i ≤ n) : Fin i ↪ Fin n := (Fin.castLEEmb h).toEmbedding

def pizza {n : Nat} (G : SimpleGraph (ZMod n)) [LocallyFinite G] : Prop := 
∀ (i : Nat), ∃ (j : Nat), j ≤ i ∧ (i.succ : ZMod n) ∈ neighborSet G j
--∀ (i : Nat), SimpleGraph.Connected (SimpleGraph.comap (@ZMod.cast (ZMod n) _ i) G)

--instance {n : Nat} : Zero (ZMod n) := Zero.ofOfNat0

instance {n : Nat} [Fact (1 < n)] : NeZero (1 : ZMod n) := inferInstance --by refine NeZero.one (ZMod n)

def stnd (n : Nat) [Fact (1 < n)] : SimpleGraph (ZMod n) 
    where
  Adj := λ i j => (j = i + 1 ∨ i = j + 1)
  symm := λ a b h => by 
    cases' h with h1 h2
    · right
      assumption
    · left
      assumption
  loopless := λ a h => by -- need hn here
    simp only [or_self, or_self_left] at h 
    simp only [self_eq_add_right] at h
    apply @one_ne_zero (ZMod n)
    assumption

variable {n : Nat} [Fact (1 < n)] [DecidableRel (stnd n).Adj]
instance : LocallyFinite (stnd n) := λ _ => neighborSetFintype _ _ -- hn being explicit is a problem

lemma stnd_Adj (u v : ZMod n) : Adj (stnd n) u v ↔ v = u + 1 ∨ u = v + 1 := by rfl

variable (n)
lemma stnd_pizza : pizza (stnd n) := λ i => ⟨i, by simp [stnd_Adj]⟩

lemma fin : Set.Finite {v : ZMod n | v.val % 2 == 0} := sorry

def succHom : stnd n →g stnd n := 
{ toFun := λ i => i + 1
  map_rel' := λ hab => by 
    rw [stnd_Adj] at *
    simp only [add_left_inj, hab] }

open BigOperators
variable {n}
lemma ge_half_of_add_eq_one {a b : NNReal} (h : a + b = 1) : a ≥ 1/2 ∨ b ≥ 1/2 := by sorry

def is_req_seq (p : Fin (n/2) → ZMod n) : Prop := Function.Injective p ∧ ∀ k, ∃ i ≤ k, p k ∈ neighborSet (stnd n) (p i)

lemma spec (v) : Nonempty (neighborSet (stnd n) v) := sorry

lemma spec_Union : Nonempty (⋃ (i : Nat) (hi : i ≤ k), neighborSet (stnd n) (p (⟨i, _⟩))) := sorry

def asso_seq (p : Fin (n/2) → ZMod n) : Fin n → ZMod n := λ i => ite (Even i.val) (p (⟨i.val / 2, by sorry⟩)) (Classical.choice (spec))

theorem final_even' {w : ZMod n → NNReal} (hn : Even n) (hw : ∑ i : ZMod n, (w i) = 1) : ∃ p : Fin (n/2) → Fin n, 

theorem final_even {w : ZMod n → NNReal} (hn : Even n) (hw : ∑ i : ZMod n, (w i) = 1) : ∃ G, [LocallyFinite G] → pizza G ∧ ∃ φ : G →g (stnd n), ∑ v in (Set.Finite.toFinset (fin n)), w (φ v) ≥ 1/2 := by 
  rw [←Finset.sum_add_sum_compl (Set.Finite.toFinset (fin n)) _] at hw
  have ge_half := ge_half_of_add_eq_one hw
  cases' ge_half with h1 h2
  · refine' ⟨stnd n, stnd_pizza n, Hom.id, h1⟩
  · refine' ⟨stnd n, stnd_pizza n, succHom n, _⟩
    convert h2 using 1
    apply Finset.sum_bij (λ a ha => a + 1) _ _ _ _
    · intros a ha
      rw [Finset.mem_compl]
      intro h
      rw [Set.Finite.mem_toFinset] at *
      simp only [beq_iff_eq, Set.mem_setOf_eq] at *
      rw [ZMod.val_add, ZMod.val_one] at h
      by_cases h' : (a.val + 1) < n
      · rw [Nat.mod_eq_of_lt h'] at h
        apply Nat.one_ne_zero
        rw [← Nat.succ_mod_two_add_mod_two a.val, ha, add_zero, h]
      · have : a.val = n
        · sorry
        rw [this] at h
        have one_lt : 1 < n
        · sorry
        simp only [Nat.add_mod_left, Nat.isUnit_iff, Nat.mod_eq_of_lt one_lt] at h
    · intros a ha
      rfl
    · intros a b ha hb h
      aesop
    · intros b hb
      refine' ⟨b - 1, _, _⟩
      · rw [Finset.mem_compl, Set.Finite.mem_toFinset] at *
        simp only [beq_iff_eq, Set.mem_setOf_eq] at *
        rw [Nat.mod_two_ne_zero] at hb
        by_cases b = 0
        · rw [h, ZMod.val_zero, Nat.zero_mod] at hb
          exfalso
          simp at hb
        · have : ZMod.val (b - 1) + ZMod.val (1 : ZMod n) < n
          · sorry
          rw [← sub_add_cancel b 1, ZMod.val_add, Nat.mod_eq_of_lt this, ZMod.val_one] at hb
          have h' := Nat.succ_mod_two_add_mod_two (b - 1).val
          rw [hb] at h'
          aesop
      · simp

theorem final {w : ZMod n → NNReal} (h : ∑ i : ZMod n, (w i) = 1) : ∃ G, [LocallyFinite G] → pizza G ∧ ∃ φ : G →g (stnd n), ∑ v : {v : ZMod n // v.val % 2 == 0}, w (φ v.val) ≥ 4/9 := sorry