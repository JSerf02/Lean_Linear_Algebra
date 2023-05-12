import Std.Data.List.Basic
import Std.Data.List.Lemmas
import Mathlib.Init.Data.List.Basic
import Mathlib.Init.Data.List.Lemmas

universe u v w

/- 
  We implement vectors as a subtype on lists, instead of as pair
    types, for the following reasons:
    (1) If we implement vectors as a subtype on lists, then we can
        use the lengthy list API in our proofs.
    (2) Implementation of vectors as a subtype on lists serparates
        the definition of functions on vectors in the computational
        part, which operates on lists, and the reasoning part, which
        pertains to demonstrating how the operation acts on the
        length of the vectors.
    The type 'Vector α n' is the type of lists of length 'n' with
    entries of type 'α'
-/

def Vector (α : Type u) (n : ℕ) :=
  {l : List α // l.length = n}

namespace Vector

variable {α : Type u} {β : Type v} {φ : Type w}

variable (n : ℕ)

instance [DecidableEq α] : DecidableEq (Vector α n) :=
  inferInstanceAs (DecidableEq {l : List α // l.length = n})


/- 
  We define 'nil' to be the empty vector with entries of type 'α'.
  Think of this definition as a presentation of the empty list,
  with a proof 'rlf' that the empty list's length is zero.
-/

@[match_pattern]
def nil : Vector α 0 :=
  ⟨[], rfl⟩


/-
  We want to be able to combine vectors. We define 'cons' which,
  given 'a : α' and 'l : Vector α n', produces the vector with
  length 'n + 1' whose first component is 'a' and the rest of
  the list is 'l'.

  The definition is thought of in the following way: To construct
  'cons a ⟨v, h⟩' we must give the list 'a :: v', which appends
  'v' to 'a', along with a proof that 'a :: v' has length 'n + 1'.
  'congrArg' does just that.
  
  If 'f : α → β' is a function, 'a₁ a₂ : α' and 'h : a₁ = a₂' is
  an equals type, then 'congrArg f h' produces a term of type
  'f a₁ = f a₂'.

  Hence '⟨a :: v, congrArg Nat.succ h⟩' is a pair consisting of the
  list 'a :: v' and a proof that 'a :: v' has length 'n + 1'.
-/

@[match_pattern]
def cons : α → Vector α n → Vector α (Nat.succ n)
  | a, ⟨v, h⟩ => ⟨a :: v, congrArg Nat.succ h⟩


/-
  To obtain the length of a vector of type 'Vector α n', we simply
  output 'n'.
-/

@[reducible, nolint unusedArguments]
def length (_ : Vector α n) : ℕ :=
  n


open Nat

/-
  We define a 'head' function of type 'Vector α (Nat.succ n) → α'.
  We use 'Nat.succ n' since there is no head to 'nil'. To construct
  the head, we have two constructors:
  (1) '⟨[], h⟩ => by contradiction'
      'contradiction' closes the main goal if its hypotheses are
      trivially contradictory
  (2) '⟨a :: _, _⟩ => a'
      This takes a vector of length at least one and extracts the
      first component.
-/

def head : Vector α (Nat.succ n) → α
  | ⟨[], h⟩ => by contradiction
  | ⟨a :: _, _⟩ => a

def tail : Vector α n → Vector α (n - 1)
  | ⟨[], h⟩ => ⟨[], congrArg pred h⟩
  | ⟨_ :: v, _⟩ => v