import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic

/-
  - Here are all of the MathLib4 type classes used here:
  - [Field 𝔽] - 𝔽 should be a field, self explanatory
  - [AddZeroClass α] - α should have addition defined with a 0 operator
    - Not necessary, but makes it so you can use + instead of the word add which is nice
  - [HMul 𝔽 α α] - You can multiply elements of type 𝔽 with elements of type α to get α 
    - As before, this is not necessary, but it makes it so you can use * instead of mult
-/
structure VectorSpace (𝔽 : Type) [Field 𝔽] (α : Type u) [AddZeroClass α] [HMul 𝔽 α α] where
  V : Set α 

  add_well_defined (u v : α) : (u ∈ V) → (v ∈ V) → ((u + v) ∈ V)
  mult_well_defined (a : 𝔽) (v : α) : (v ∈ V) → ((a * v) ∈ V)

  add_assoc (u v w: α) : u + (v + w) = (u + v) + w
  add_comm (u v : α) : u + v = v + u
  zero_add (u : α) : 0 + u = u := AddZeroClass.zero_add u
  add_zero (u : α) : u + 0 = u := AddZeroClass.add_zero u
  additive_inverse (u : α) : u ∈ V → ∃ u_inv ∈ V, u + u_inv = 0

  mult_id (v : α) : (1 : 𝔽) * v = v
  mult_assoc (a b: 𝔽) (v : α) : (a * b) * v = a * (b * v)
  mult_distrib_vec (a : 𝔽) (u v : α) : a * (u + v) = a * u + a * v
  mult_distrib_add (a b : 𝔽) (v : α) : (a + b) * v = a * v + b * v

namespace VectorSpace
  variable (𝔽 : Type) [Field 𝔽] 
  variable (α : Type u) [AddZeroClass α] [HMul 𝔽 α α]

  /- Allows you to use ∈ for vector spaces -/
  instance : Membership α (VectorSpace 𝔽 α) where
    mem a V := a ∈ V.V

  theorem zero_is_unique (V : VectorSpace 𝔽 α) (v : α) : 0 + v = 0 → v = 0 := by 
    rw[V.zero_add]
    exact id
end VectorSpace