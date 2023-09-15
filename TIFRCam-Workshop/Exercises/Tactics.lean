import Mathlib

/- In this file, we are going to learn about some common tactics and how to use them.
For a more complete introduction to tactics, please try out the Natural Number Game : https://adam.math.hhu.de/#/g/hhu-adam/NNG4 
Each tactic is given with an explanation, and example exercises. In a normal proof, you might want to use a combination of these tactics.

The exercises and proof suggestions given here are designed so you understand the use of the tactic. Feel free to experiment with other proofs as well. If you wish to search for theorems, use the following link : https://leanprover-community.github.io/mathlib4_docs/

PS : You can click Alt+Z to see all the text in your window at once.
-/

-- # rewrite
-- The most commonly used tactic is `rw`. If you are given a hypothesis `h : a = b` or `h : a ↔ b`, then `rw [h]` will replace `a` with `b` in the goal. To replace `b` with `a`, use `rw [← h]`. Hover over the arrow to see how it is typed out.
-- Example exercises :
example {a : ℝ} (h : a = 0) : a + 0 = 0 := by sorry
 -- replace a with 0 using `rw [h]`
 -- use the lemma `add_zero`

example (a b c : Prop) (h1 : a ↔ b) (h2 : b ↔ c) : a ↔ c := by sorry

-- You can also rewrite at hypotheses instead of goals, by using `rw [_] at _`
example {a b : ℝ} (h1 : a = 0) (h2 : a + b = 0) : b = 0 := by sorry
 -- replace a in the hypothesis h2 using `rw [h1] at h2`
 -- rewrite the lemma `zero_add` at h2
 -- last step

-- # apply
-- The tactic `rw` only works for equalities and iff statements. For other statements, we have the tactic `apply`. If you want to use a lemma or hypothesis `h` on the goal, then `apply h` is what you are looking for. Note that, unlike `rw`, one cannot use `apply` at hypotheses.

-- Example exercises :
example {a b : ℚ} (h : a ∣ b) : a ∣ b := by sorry
-- try `rw [h]`
-- did it fail? then try `apply h`

example {a : ℚ} (b : ℚ) (h : a = 1) : a ∣ b := by sorry
-- replace a with 1
-- use the lemma `one_dvd`

example {a b c : ℚ} (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ b + c := by sorry
-- use the lemma `dvd_add`, you will then get 2 goals. These are the conditions or hypotheses which need to be satisfied for `dvd_add` to be true. Hover over `dvd_add` to see this.
-- solve each subgoal
-- an alternate approach, try `apply dvd_add _ _`. The `_` are called placeholders, and correspond to each subgoal. In this case, `apply dvd_add h1 h2` should solve the goal immediately.

example {a b c : ℚ} (h : a ∣ b ∧ a ∣ c) : a ∣ b + c := by sorry
-- this is similar to the previous example.
-- how do you extract only the first condition from the and statement?
-- given h : p ∧ q, h.1 refers to p and h.2 refers to q

example {a b c d : ℚ} (h : a ∣ b ∧ a ∣ c ∧ a ∣ d) : a ∣ b + c + d := by sorry
-- what is h.1 and h.2?

-- one can also use apply instead of rw if needed
example (f g : Nat → Nat) (h : ∀ x, f x = 0 ↔ g x = 0) (h' : g = 0) (x : Nat) : f x = 0 := by sorry
-- try `apply (h x).2`, this gives you the `g x = 0 → f x = 0` part of the iff statement
-- the rest is easy
-- a useful tactic that could close the goal is `aesop`. To see what it is doing, type `aesop?`

-- # constructor
-- This tactic is used to break up goals of the form a ∧ b into 2 subgoals : a and b.

-- Example exercises :
example (n : ℕ) : Nat.Prime 2 ∧ 2 = 1 + 1 := by sorry
-- use `constructor` to break the goal into 2
-- use `Nat.prime_two` for the first goal
-- the second goal is the definition of 2 in Lean

-- # use
-- This tactic is useful when you need to prove the existence of something. 

-- Example exercises :
example (n : ℕ) : ∃ p : ℕ, Nat.Prime p ∧ p ∣ 2 * n := by sorry
-- an obvious choice is 2. Try `use 2`
-- you can now split and solve the first case
-- for the second goal, you should know the definition of `∣`. If you hover over it, you will see its definition.

-- # have
-- This tactic is used to make hypothesis inside a proof. If you want to put a hypothesis `h : a = b`, the command is, `have h : a = b`. This will then generate 2 goals, the first is to prove `h`, the second is to prove the main goal along with the added hypothesis `h`. This provides a good way to break down your proof into smaller components which are easier to prove.

-- Example exercises :
example {x y : ℕ} {f : ℝ → ℝ} (hf : Function.Injective f) (h : f x = f y) : x^2 = y^2 := by sorry
-- a helpful intermediate step would be to have x = y
-- try have x_eq_y : x = y
-- solve it by applying the definition of Function.Injective
-- the rest follows easily

-- Sometimes, if you already have the proof of `h`, you can put just the proof without giving the statement.
example {x y : ℕ} (h : x^2 + y^2 = 0) : x^3 - x = 0 := by sorry
-- a helpful intermediate step would be to have `x = 0`, try to write that down
-- take a look at the lemma `Nat.eq_zero_of_add_eq_zero`, it requires one input
-- try have x_eq_zero := Nat.eq_zero_of_add_eq_zero h
-- this gives you the required statement, the rest follows easily using the lemmas `pow_eq_zero_iff` and `two_pos`

-- # cases'
-- This tactic helps to deal with existential hypotheses. If you have a hypothesis `h : ∃ p, f p = 0`, then `cases' h with q hq` will introduce such a `p`, while `hq` will be the property that `f q = 0`.

-- Example exercises :
example {n : ℕ} (h : ∃ p, Nat.Prime p ∧ n ∣ p) : n = 1 ∨ Nat.Prime n := by sorry

-- # by_cases
-- This tactic is for when you want to consider different cases. Suppose you want to break the proof depending on whether a condition, say `p`, is satisfied or not. Applying `by_cases h : p` will give you two goals : the first with the hypothesis `h : p`, and the second with the hypothesis `h : ¬ p`. 

-- Example exercises :
example {f : ℝ → ℝ} (h1 : f 0 = -1) (h2 : ∀ x, x ≠ 0 → f x = 1) (x : ℝ) : (f x)^2 = 1 := by sorry
-- try to break it up into the appropriate cases
-- you could try to solve each goal using the tactic `simp`
-- if you want to see which lemmas `simp` is using, type `simp?`

-- # exfalso
-- This tactic is generally used for contradictions. `exfalso` will turn the goal to `False`. This is used when you think that the given hypotheses have a contradiction. Note that, given a proposition, say `p`, `¬p` is the same as `p → False`.
-- Example exercises :
example {a : Nat} (ha : a = 0) (ha' : a ≠ 0) : ∀ n, ∃ x y z : Nat, x^n + y^n = z^n := by sorry
-- start by using `exfalso`
-- the rest is easy

-- you can now try out the `Nat_properties.lean` file