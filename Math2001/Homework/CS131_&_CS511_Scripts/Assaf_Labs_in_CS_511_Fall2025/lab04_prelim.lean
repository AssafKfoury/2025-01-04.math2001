/- 24 September 2025 -/
/- from Macbeth Sect 6.02 in Chapt 6: three examples -/
/- SEVERAL EXERCISES WITH INDUCTION -/

import Mathlib.Tactic.GCongr
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int

/- From Example 6.2.1 in 06_Induction in Macbeth's -/
def b : ℕ → ℤ
  | 0 => 3
  | n + 1 => b n ^ 2 - 2
/- it's cleaner to include the parentheses in the recursive call: -/
def bb : ℕ → ℤ
  | 0 => 3
  | n + 1 => (bb n) ^ 2 - 2
/- Show that for all n, (bb n) is odd -/
example (n : ℕ) : Odd (bb n) := by
  simple_induction n with k hk
  · -- base case
    dsimp [Odd] -- 'Odd' is defined in Example 3.1.1
    use 1
    calc bb 0 = 3 := by rw [bb]
      _ = 2 * 1 + 1 := by numbers
  · -- inductive step
    dsimp [Odd] at * -- unwind the defn of 'Odd' everywhere
    obtain ⟨x, hx⟩ := hk
    use 2 * x ^ 2 + 2 * x - 1
    calc bb (k + 1) = (bb k) ^ 2 - 2 := by rw [bb]
      _ = (2 * x + 1) ^ 2 - 2 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + 2 * x - 1) + 1 := by ring

/- From Example 6.2.3 in 06_Induction in Macbeth's -/
def x : ℕ → ℤ
  | 0 => 5
  | n + 1 => 2 * (x n) - 1
example (n : ℕ) : x n = 2 ^ (n + 2) + 1 := by
  simple_induction n with k IH
  · -- base case
    calc x 0 = 5 := by rw [x]
      _ = 2 ^ (0 + 2) + 1 := by numbers
  · -- inductive step
    calc x (k + 1) = 2 * (x k) - 1 := by rw [x]
      _ = 2 * (2 ^ (k + 2) + 1) - 1 := by rw [IH]
      _ = 2 ^ ((k + 1) + 2) + 1 := by ring

/- From Example 6.2.6 in 06_Induction in Macbeth's -/
def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

notation:10000 n "!" => factorial n

example (n : ℕ) : (n + 1)! ≥ 2 ^ n := by
  simple_induction n with k IH
  · -- base case
    calc (0 + 1)! = (0 + 1) * 0! := by rw [factorial, factorial, factorial]
      _ = (0 + 1) * 1 := by rw [factorial]
      _ ≥ 2 ^ 0 := by numbers
  · -- inductive step
    calc (k + 1 + 1)! = (k + 1 + 1) * (k + 1)! := by rw [factorial]
      _ ≥ (k + 1 + 1) * 2 ^ k := by rel [IH]
      _ = k * 2 ^ k + 2 * 2 ^ k := by ring
      _ ≥ 2 * 2 ^ k := by extra
      _ = 2 ^ (k + 1) := by ring

/- FORWARD reasoning vs BACKWARD Reasoning

FORWARD reasoning is PREMISE-ORIENTED, e.g. using the command 'have'
to derive new facts from existing ones until desired conclusion is
reached.

BACKWARD reasoning is GOAL-ORIENTED, starting from the conclusion and
applying tactics like 'intro' and 'by_contra' to reduce the goal to
simpler subgoals.

FORWARD and BACKWARD reasoning are not exclusive of each other: The
friendliest approach to writing a proof is often one that mixes the
two forms of reasoning.

-/

/- example of BACKWARD PROOF -/
example (p q : Prop) : p → (q → p) := by
  -- Initial goal: p → q → p
  intro hp  -- Introduce the assumption `hp : p`.
  -- New simpler goal: q → p
  intro hq  -- Introduce the assumption `hq : q`.
  -- New simpler goal: p
  apply hp -- alternative step: `exact hp` or `assumption`

/- example of FORWARD PROOF, using `term mode`, by building a 'proof term'
   directly, starting from premises and combining them to form final conclusion -/
example (p q : Prop) : p → q → p :=
  fun (hp : p) => fun (hq : q) => hp

/- example of BACKWARD PROOF of Peirce's Law -/
example {P Q : Prop} : ((P → Q) → P) → P := by
  -- The goal is ((P → Q) → P) → P.
  intro h
  -- We now need to prove P, given the hypothesis h : (P → Q) → P.
  -- We proceed by contradiction.
  by_contra h2
  -- The goal is now `False`, given `h` and `h2`.
  -- We prove `P` by applying our hypothesis `h`.
  have h3 : P := h (fun x => absurd x h2)
  -- We have now `h3 : P`.
  -- We can use this to contradict our assumption `h2`.
  -- contradiction
  have h4 : False := h2 h3
  exact h4 -- you can replace this line and the preceding one by `contradiction`

/- example of FORWARD PROOF, using `term mode`, of Peirce's Law -/
example {P Q : Prop} : ((P → Q) → P) → P :=
  -- Introduce the hypothesis: h : (P → Q) → P
  fun h : (P → Q) → P =>
    -- The strategy is to prove P by contradiction, using the law of excluded middle (LEM)
    by_contradiction $ -- `$` tells Lean4 the full expression that follows (fun not_P : ¬ P => ...)
                       -- should be treated as a single argument to the function `by_contradiction`
    fun not_P : ¬ P =>
      -- have h_PQ : P → Q
      -- The first step is to establish that P → Q is true from the assumption ¬P.
      have h_PQ : P → Q :=
        -- Assume p : P, and then use the contradiction with not_P to get a proof of Q.
        fun p : P =>
          -- The term for a proof of an arbitrary proposition Q from a contradiction (p and ¬P)
          False.elim (not_P p)
      -- We now have two things:
      -- 1. h : (P → Q) → P
      -- 2. h_PQ : P → Q
      -- We can apply h to h_PQ to get a proof of P.
      have P_from_h : P := h h_PQ
      -- Now we have a proof of P (P_from_h) and our assumption ¬P (not_P).
      -- This is a contradiction, which proves the outer by_contradiction goal.
      -- The term for a contradiction is not_P P_from_h : False
      not_P P_from_h

/- mixing BACKWARD and FORWARD, with emphasis on BACKWARD, in a proof of Peirce's Law -/
example {P Q : Prop} : ((P → Q) → P) → P := by
  -- Goal: ((P → Q) → P) → P
  -- To prove an implication, introduce the antecedent as a hypothesis.
  intro h1
  -- Hypothesis h1 is now: (P → Q) → P
  -- Goal is P. We will prove this by contradiction.
  by_contra h2
  -- Context now includes hypothesis h2 : ¬ P
  -- The current goal is `False`.
  -- Since h1 is `(P → Q) → P`, and we have `¬ P`, we need to show `P → Q`.
  -- To do this, we can introduce a new hypothesis `h3 : P`.
  have h3 : P → Q := by
    -- Goal: P → Q
    intro hp
    -- Hypothesis hp is now: P
    -- We have P (hp) and ¬P (h2), which is a contradiction.
    -- The goal is Q. `contradiction` can solve this because `False` implies anything.
    contradiction
  -- We now have a proof `h3 : P → Q`
  -- We can apply our hypothesis `h1 : (P → Q) → P` to `h3`.
  have h4 : P := h1 h3
  -- This gives us `h4 : P`.
  -- But we also have our assumption `h2 : ¬ P`. This is a contradiction.
  contradiction

/- EXAMPLES FOR HOW to use 'contradiction', 'absurd', 'exfalso' -/

/- If the context contains a contradiction, the tactic 'contradiction'
   can be used to immediately complete the proof and close the goal -/
example {p q : Prop} (h1 : p) (h2 : ¬ p) : q := by
  contradiction
/- Roundabout, less efficient way of proving the same target -/
example {p q : Prop} (h1 : p) (h2 : ¬ p) : q := by
  exfalso -- replaces current goal 'q' by 'False'
  have h3 : False := h2 h1
  apply h3
