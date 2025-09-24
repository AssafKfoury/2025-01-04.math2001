/- 24 September 2025 -/
/- from Macbeth Sect 6.02 in Chapt 6: three examples -/
/-  -/
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
/- next proof is from Macbeth's solutions in 2023-04.math2001-/
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
example (p q : Prop) : p → q → p := by
  -- Initial goal: p → q → p
  intro hp  -- Introduce the assumption `hp : p`.
  -- New simpler goal: q → p
  intro hq  -- Introduce the assumption `hq : q`.
  -- New simpler goal: p
  assumption

/- example of FORWARD PROOF, using 'term mode', by building a 'proof term'
   directly, starting from premises and combining them to form final conclusion -/
example (p q : Prop) : p → q → p :=
  fun (hp : p) => fun (hq : q) => hp

/- example of BACKWARD PROOF of Peirce's Law -/
example {P Q : Prop} : ((P → Q) → P) → P := by
  -- The goal is ((P → Q) → P) → P.
  intro h
  -- We now need to prove P, given the hypothesis h : (P → Q) → P.
  -- We proceed by contradiction.
  by_contra not_P
  -- The goal is now `False`, given `h` and `not_P`.
  -- We prove `P` by applying our hypothesis `h`.
  have p_from_h : P := h (fun p_hyp => absurd p_hyp not_P)
  -- We have now `p_from_h : P`.
  -- We can use this to contradict our assumption `not_P`.
  contradiction

/- example of FORWARD PROOF of Peirce's Law, using 'term mode' -/
example {P Q : Prop} : ((P → Q) → P) → P :=
  fun h : (P → Q) → P ↦ by_contradiction fun not_P : ¬P ↦
    have not_not_P : ¬¬ P := fun h_P : P ↦
      have P_implies_Q : P → Q := fun _ : P ↦
        absurd h_P not_P
      have h_P_derived : P := h P_implies_Q
      absurd h_P_derived not_P
    absurd not_not_P (not_not_P not_P)

/- mixing BACKWARD and FORWARD, with emphasis on BACKWARD, in a proof
   of Peirce's Law -/
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

/- again, mixing BACKWARD and FORWARD, with emphasis on FORWARD, in
   a proof Peirce's Law -/
/- example of FORWARD PROOF, of so-called Peirce's Law -/
example {P Q : Prop} : ((P → Q) → P) → P := by
  -- Goal: ((P → Q) → P) → P
  -- Start by assuming the hypothesis.
  intro h1
  -- Assume the negation of the conclusion to set up a proof by contradiction.
  by_contra not_P
  -- Goal: False
  -- We have h1 : (P → Q) → P and not_P : ¬P.
  -- From not_P, we can prove P → Q. This is a common pattern in classical logic.
  have p_implies_q : P → Q := by
    -- Goal: P → Q
    intro p
    -- We have p : P and not_P : ¬P, which is a contradiction.
    -- From a contradiction, anything follows, including Q.
    contradiction
  -- We now have `p_implies_q : P → Q`.
  -- Use h1 on p_implies_q to get a proof of P.
  have p_proof : P := h1 p_implies_q
  -- We now have `p_proof : P`.
  -- We also have `not_P : ¬P`, which is `P → False`.
  -- We can apply not_P to p_proof to get `False`.
  exact not_P p_proof

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
