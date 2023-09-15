import Mathlib.Data.ZMod.Basic

/- In this file, we shall discuss the basics of Lean 4. 
  This is a very quick crash course. To know more, please read Mathematics in Lean (link?) 
  or Theorem Proving in Lean. You can also ask for help on the Zulip chat : https://leanprover.zulipchat.com/ -/

-- Let us start with understanding what types are.
-- Every element in Lean has a unique `Type`.  
-- Let us check the inherent `Type` of `0`. 
-- Remove the `--` in the beginning of the next line to uncomment it.
-- #check 0

-- This tells us that Lean automatically takes `0` to have type `Nat`.
-- A Type is similar to a set. It is not the same, because an element can belong to multiple sets, 
-- but every element has a unique `Type`. Let us check the type of the integer `1`
-- #check (1 : Int)
-- To read more about this, hover on the brackets in the above line.

-- Now, uncomment the following two lines :
-- #check (-1 + 1 : Nat)
-- #eval -1 + 1
-- The first line gives an error because Lean cannot find 
-- negation defined on the naturals, and so this is NOT identified as `0 : Nat`.
-- When we dont forcibly give it a `Type`, the second line shows that Lean can 
-- compute the value to be `0 : Int`
-- => `(0 : Nat)` is not the same as `(0 : Int)`!

-- How do we relate the two? Hover over both sides of the equation below
-- #check (0 : Nat) = (0 : Int)
-- The RHS has type `Int`. Lean has automatically taken the RHS to be an element of type `Int`.
-- It has used a function `ofNat : Nat → Int`, to convert the LHS into the type of the RHS.
-- Such functions are called coercions.

-- Notice also that the type of this equality is `Prop`. 
-- This is a special kind of type for propositions, equalities, inequalities etc.
-- The next line is another example :
-- #check ∀ x, x = 0
-- Can you construct some elements which have type `Prop`?

#check ∃ n : ℕ, n = 1 

-- Let us now understand functions.
def fn1 (x : ℕ) : ℕ := x + 3
#print fn1
#eval fn1 0
-- This defines `fn`, which is given an input of `x` which has type `Nat`, 
-- and gives as output a term of type `Nat`, which is defined to be `x + 3`.

-- If we remove the type of the output, Lean is able to infer it since it knows the type of `x` :
def fn2 (x : ℕ) := x + 3
#print fn2

-- Another way to make the same definition is :
def fn3 := λ x : ℕ => x + 3
#print fn3

-- Let us now turn to theorem proofs. We use tactics to prove theorems. 
-- Let us try to prove that the functions we defined above are indeed the same.
lemma fn1_eq_fn2 (x : ℕ) : fn1 x = fn2 x := by sorry
-- The name of the lemma is `fn1_eq_fn2`. The statement we want to prove is put after `:`. 
-- We assume `x` to be an explicit hypothesis, enclosed in round brackets. 
-- The keyword `by` suggests the start of the proof. Look over into the window on the right, 
-- you will see a goal. 
-- What is the proof of this statement? It is reflexivity, given by the `rfl` tactic.
-- Replace `sorry` with `rfl`. The window should say `No goals`

-- Congratulations, you solved your first lemma in Lean!

-- Lets try a variant of the same lemma.
lemma fn1_eq_fn3 : ∀ x, fn1 x = fn3 x := by sorry
-- We need some way to extract the variable `x`. This is done by the tactic `intro`. 
-- `intro x` will call the extracted variable `x`.
-- Try to complete the proof.