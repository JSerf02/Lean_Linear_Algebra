namespace demo
def add1 (n : Nat) : Nat := n + 1

#check add1
#print add1
#eval add1 5


def add2 (n : Nat) : Nat :=
  add1 (add1 n)

theorem symmetry (a b : α) : a = b ↔ b = a := by
  apply Iff.intro
  . intro a_eq_b
    apply Eq.symm
    exact a_eq_b
  . intro b_eq_a
    apply Eq.symm
    exact b_eq_a

#print symmetry

theorem add1_eq_succ (n : Nat) : add1 n = Nat.succ n := by
  rw[add1]

theorem add2_eq_succ (n : Nat) : add2 n = Nat.succ (Nat.succ n) := by
  rw[add2, add1, add1]

theorem better_add2_eq_succ (n : Nat) : add2 n = Nat.succ (Nat.succ n) := by
  simp[add1, add2]

theorem add2_add1_eq_add1_add2 (n : Nat) : add2 (add1 n) = add1 (add2 n) := by
  have two_then_one : add2 (add1 n) = Nat.succ (Nat.succ (Nat.succ n)) := by simp[add2, add1]
  let one_then_two : add1 (add2 n) = Nat.succ (Nat.succ (Nat.succ n)) := by simp[add1, add2]
  rw[two_then_one] 
  rw[one_then_two]

theorem add_1_add2_add_1_eq_add_1_add1_add_2 (n : Nat) : add1 (add2 (add1 n)) = (add1 (add1 (add2 n))) := by
  simp[add1]
  have inner_eq := add2_add1_eq_add1_add2 n
  simp[add1] at inner_eq
  simp[inner_eq]

/- A type representing the only possible colors. Other colors are unacceptable!! -/
inductive Color where
| Red
| Green
| Blue

def red : Color := Color.Red

def color_to_nat (c : Color) : Nat :=
  match c with
  | Color.Red   => 0
  | Color.Green => 1
  | _           => 2

class ThreeUniqueElements (α : Type u) where
  three_unique : ∃ (a b c : α), a ≠ b ∧ a ≠ c ∧ b ≠ c

theorem three_unique_colors : ∃ (a b c : Color), a ≠ b ∧ a ≠ c ∧ b ≠ c :=
  have red_blue_green_neq : Color.Red ≠ Color.Green ∧ Color.Red ≠ Color.Blue ∧ Color.Green ≠ Color.Blue := by simp
  ⟨Color.Red, Color.Green, Color.Blue, red_blue_green_neq⟩

instance : ThreeUniqueElements Color where
  three_unique := three_unique_colors

#check @ThreeUniqueElements.three_unique Color


end demo


