import Std.Data.List.Basic
import Std.Data.List.Lemmas
import Mathlib.Init.Data.List.Basic
import Mathlib.Init.Data.List.Lemmas
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Control.Applicative
import Mathlib.Control.Traversable.Basic

universe u v w

variable {n : ℕ}

/--
  We implement vectors as a subtype on lists, instead of as pair
  types, for the following reasons:

  (1) If we implement vectors as a subtype on lists, then we can
      use the lengthy list API in our proofs.

  (2) Implementation of vectors as a subtype on lists serparates
      the definition of functions on vectors in the computational
      part, which operates on lists, and the reasoning part, which
      pertains to demonstrating how the operation acts on the
      length of the vectors.

  The type `Vector α n` is the type of lists of length `n` with
  entries of type `α`
-/
def Vector (α : Type u) (n : ℕ) :=
  { l : List α // l.length = n }

namespace Vector

section VectorBasic

variable {α : Type u} {β : Type v} {φ : Type w}

instance [DecidableEq α] : DecidableEq (Vector α n) :=
  inferInstanceAs (DecidableEq {l : List α // l.length = n})

/-- `nil` is the empty vector with entries of type α -/
@[match_pattern]
def nil : Vector α 0 :=
  ⟨[], rfl⟩

/-- `cons` preappends an element of type α to a vector whose entries
    have type α -/
@[match_pattern]
def cons : α → Vector α n → Vector α (Nat.succ n)
  | a, ⟨v, h⟩ => ⟨a :: v, congrArg Nat.succ h⟩

/-- `length` is a function that maps a vector to its length -/
@[reducible, nolint unusedArguments]
def length (_ : Vector α n) : ℕ :=
  n

open Nat

/-- `head` takes a vector of nonzero length and returns its first entry -/
def head : Vector α (Nat.succ n) → α
  | ⟨[], h⟩ => by contradiction
  | ⟨a :: _, _⟩ => a

theorem head_cons (a : α) : ∀ v : Vector α n, head (cons a v) = a
  | ⟨_, _⟩ => rfl

/-- `tail` takes a vector and returns its tail -/
def tail : Vector α n → Vector α (n - 1)
  | ⟨[], h⟩ => ⟨[], congrArg pred h⟩
  | ⟨_ :: v, h⟩ => ⟨v, congrArg pred h⟩

theorem tail_cons (a : α) : ∀ v : Vector α n, tail (cons a v) = v
  | ⟨_, _⟩ => rfl

@[simp]
theorem cons_head_tail : ∀ v : Vector α (succ n), cons (head v) (tail v) = v
  | ⟨[], h⟩ => by contradiction
  | ⟨a :: v, h⟩ => rfl

/-- `toList` takes a vector and returns its list -/
def toList (v : Vector α n) : List α :=
  v.1

/-- `get` retrieves the ith entry of a vector -/
def get : ∀ _ : Vector α n, Fin n → α
  | ⟨l, h⟩, i => l.nthLe i.1 (by rw [h] ; exact i.2)

/-- `append` appends one vector to another vector -/
def append {n m : ℕ} : Vector α n → Vector α m → Vector α (n + m)
  | ⟨l₁, h₁⟩, ⟨l₂, h₂⟩ => ⟨l₁ ++ l₂, by simp [*]⟩

/-- `replicate`  takes an n : ℕ and some a : α and constructs a vector of
  length n whose entries are all a -/
def replicate (n : ℕ) (a : α) : Vector α n :=
  ⟨List.replicate n a, List.length_replicate n a⟩

/-- `drop` removes the first i elements of a vector -/
def drop (i : ℕ) : Vector α n → Vector α (n-i)
  | ⟨l, p⟩ => ⟨List.drop i l, by simp [*]⟩

/-- `take` takes a vector and returns its first i elements -/
def take (i : ℕ) : Vector α n → Vector α (min i n)
  | ⟨l, p⟩ => ⟨List.take i l, by simp [*]⟩

/-- `removeNth` removes the ith entry from a vector of length n -/
def removeNth (i : Fin n) : Vector α n → Vector α (n - 1)
  | ⟨l, p⟩ => ⟨List.removeNth l i.1, by rw [l.length_removeNth] <;> rw [p] ; exact i.2⟩

/-- `ofFn` constructs a vector of length n from a function on Fin n -/
def ofFn : ∀ {n}, (Fin n → α) → Vector α n
  | 0, _ => nil
  | _ + 1, f => cons (f 0) (ofFn fun i ↦ f i.succ)

def map (f : α → β) : Vector α n → Vector β n
  | ⟨l, h⟩ => ⟨List.map f l, by simp [*]⟩

protected theorem eq {n : ℕ} : ∀ a₁ a₂ : Vector α n, toList a₁ = toList a₂ → a₁ = a₂
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

protected theorem eq_nil (v : Vector α 0) : v = nil :=
  v.eq nil (List.eq_nil_of_length_eq_zero v.2)

@[simp]
theorem toList_length (v : Vector α n) : (toList v).length = n :=
  v.2

@[simp]
theorem toList_cons (a : α) (v : Vector α n) : toList (cons a v) = a :: toList v := by
  cases v ; rfl

end VectorBasic


section VectorIntermediate

variable {α : Type _}

@[inherit_doc]
infixr:67 " ::ᵥ " => Vector.cons

attribute [simp] head_cons tail_cons

instance [Inhabited α] : Inhabited (Vector α n) :=
  ⟨ofFn default⟩

@[ext]
theorem ext : ∀ {v w : Vector α n} (_ : ∀ m : Fin n, Vector.get v m = Vector.get w m), v=w
  | ⟨v, hv⟩, ⟨w, hw⟩, h =>
    Subtype.eq (List.ext_get (by rw [hv, hw]) fun m hm _ => h ⟨m, hv ▸ hm⟩)

instance zero_subsingleton : Subsingleton (Vector α 0) :=
  ⟨fun _ _ => Vector.ext fun m => Fin.elim0 m⟩

@[simp]
theorem cons_val (a : α) : ∀ v : Vector α n, (a ::ᵥ v).val = a :: v.val
  | ⟨_, _⟩ => rfl

theorem eq_cons_iff (a : α) (v : Vector α n.succ) (v' : Vector α n) :
    v = a ::ᵥ v' ↔ v.head = a ∧ v.tail = v' :=
  ⟨fun h => h.symm ▸ ⟨head_cons a v', tail_cons a v'⟩, fun h =>
    _root_.trans (cons_head_tail v).symm (by rw [h.1, h.2])⟩

theorem ne_cons_iff (a : α) (v : Vector α n.succ) (v' : Vector α n) :
    v ≠ a ::ᵥ v' ↔ v.head ≠ a ∨ v.tail ≠ v' :=
  by rw [Ne.def, eq_cons_iff a v v', not_and_or]

theorem exists_eq_cons (v : Vector α n.succ) : ∃ (a : α) (as : Vector α n), v = a ::ᵥ as :=
  ⟨v.head, v.tail, (eq_cons_iff v.head v v.tail).2 ⟨rfl, rfl⟩⟩

@[simp]
theorem length_val (v : Vector α n) : v.val.length = n :=
  v.2

@[simp]
theorem toList_map {β : Type _} (v : Vector α n) (f : α → β) : (v.map f).toList = v.toList.map f :=
  by cases v ; rfl

/-- The `tail` of a `nil` vector is `nil` -/
@[simp]
theorem tail_nil : (@nil α).tail = nil :=
  rfl

/-- The `tail` of a vector with one entry is `nil` -/
@[simp]
theorem singleton_tail : ∀ (v : Vector α 1), v.tail = Vector.nil
  | ⟨[_], _⟩ => rfl

/-- Mapping under `id` does not change a vector -/
@[simp]
theorem map_id {n : ℕ} (v : Vector α n) : Vector.map id v = v :=
  Vector.eq _ _ (by simp only [List.map_id, Vector.toList_map])

/-- `last` returns the last entry of a vector -/
def last (v : Vector α (n + 1)) : α :=
  v.get (Fin.last n)

theorem last_def {v : Vector α (n + 1)} : v.last = v.get (Fin.last n) :=
  rfl

end VectorIntermediate