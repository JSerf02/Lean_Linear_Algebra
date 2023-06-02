namespace demo

-- An example showcasing the basic syntax of Lean4
  -- Notice how it exactly mirrors propositional logic syntax
def add1 (n : Nat) : Nat := n + 1

-- The 3 common ways of displaying information in Lean4
#check add1 -- Shows the type of a definition
#print add1 -- Shows the **internal** proof of the definition
#eval add1 5 -- Evaluates the definition

-- An example showcasing function application
  -- Notice hot it is similar to Haskell syntax
def add2 (n : Nat) : Nat := add1 (add1 n)

-- A theorem that uses tactics
  -- Tacts allow you to create proofs by telling the computer
  -- how to create the proof instead of explicitly telling the
  -- computer the proof
theorem symmetry {α : Type u} (a b : α) : a = b ↔ b = a := by
  apply Iff.intro
  . intro a_eq_b
    apply Eq.symm
    exact a_eq_b
  . intro b_eq_a
    apply Eq.symm
    exact b_eq_a

-- Printing a tactic proof shows the internal proof generated 
-- by the tactics
#print symmetry

-- The rw tactic takes a statement of equality in the form a=b
-- and replaces every instance of a in the tactic's goal with b
theorem add1_eq_succ (n : Nat) : add1 n = Nat.succ n := by
  rw[add1]

-- Chaining rws can be done in a single call
theorem add2_eq_succ (n : Nat) : add2 n = Nat.succ (Nat.succ n) := by
  rw[add2, add1, add1]

-- The simp tactic repeatedly tries to rw until it reaches the 
-- simplest form it could
  -- This tactic is SUPER stupidly powerful; 
    -- Many proofs are just a single call to this tactic
theorem better_add2_eq_succ (n : Nat) : add2 n = Nat.succ (Nat.succ n) := by
  simp[add1, add2]

-- have and let bindings let you introduce new goals in the middle
-- of proofs and let you name statements for later reuse
theorem add2_add1_eq_add1_add2 (n : Nat) : add2 (add1 n) = add1 (add2 n) := by
  have two_then_one : add2 (add1 n) = Nat.succ (Nat.succ (Nat.succ n)) := by simp[add2, add1]
  let one_then_two : add1 (add2 n) = Nat.succ (Nat.succ (Nat.succ n)) := by simp[add1, add2]
  rw[two_then_one] 
  rw[one_then_two]

-- have and let bindings are capable of assuming the type
theorem add_1_add2_add_1_eq_add_1_add1_add_2 (n : Nat) : add1 (add2 (add1 n)) = (add1 (add1 (add2 n))) := by
  simp[add1]
  have inner_eq := add2_add1_eq_add1_add2 n
  simp[add1] at inner_eq
  simp[inner_eq]

-- Inductive types allow you to store enumerable information
  -- It is not showcased here, but these types also let you
  -- create well-founded recursive types, which lets you do cool 
  -- stuff like creatting natural numbers (see Natural.lean)
inductive Color where
| Red
| Green
| Blue

-- Each item in the inductive type is a constructor
def red : Color := Color.Red

-- Inductive types support induction, and all induction can be handled
-- through match statements which perform pattern matching
def color_to_nat (c : Color) : Nat :=
  match c with
  | Color.Red   => 0
  | Color.Green => 1
  | _           => 2

-- Type classes group together types that have similar properties
class ThreeUniqueElements (α : Type u) where
  three_unique : ∃ (a b c : α), a ≠ b ∧ a ≠ c ∧ b ≠ c

-- The Color type has 3 unique elements, so it can be instanced 
-- into the ThreeUniqueElements type class
theorem three_unique_colors : ∃ (a b c : Color), a ≠ b ∧ a ≠ c ∧ b ≠ c :=
  have red_blue_green_neq : Color.Red ≠ Color.Green ∧ Color.Red ≠ Color.Blue ∧ Color.Green ≠ Color.Blue := by simp
  ⟨Color.Red, Color.Green, Color.Blue, red_blue_green_neq⟩
instance : ThreeUniqueElements Color where
  three_unique := three_unique_colors
#check @ThreeUniqueElements.three_unique Color


-- Congrats, you are now familiar with the basics of Lean4!!
end demo


