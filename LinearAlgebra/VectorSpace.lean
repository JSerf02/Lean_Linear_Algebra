import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic

/-
  - Here are all of the MathLib4 type classes used here:
  - [Field 𝔽] - 𝔽 should be a field, self explanatory
  - [AddZeroClass V] - V should have addition defined with a 0 operator
    - Not necessary, but makes it so you can use + instead of the word add which is nice
  - extends HMul 𝔽 V V - You can multiply elements of type 𝔽 with elements of type V to get V 
    - extends necessitates that every VectorSpace must be an HMul, elements of a VectorSpace must have
      multiplication defined
-/
class VectorSpace (𝔽 : Type) [Field 𝔽] (V : Type u) [AddZeroClass V] extends HMul 𝔽 V V where
  add_assoc (u v w : V) : u + (v + w) = (u + v) + w
  add_comm (u v : V) : u + v = v + u
  additive_inverse (u : V) : ∃ u_inv, u_inv + u = 0

  mult_id (v : V) : (1 : 𝔽) * v = v
  mult_assoc (a b: 𝔽) (v : V) : (a * b) * v = a * (b * v)
  mult_distrib_vec (a : 𝔽) (u v : V) : a * (u + v) = a * u + a * v
  mult_distrib_add (a b : 𝔽) (v : V) : (a + b) * v = a * v + b * v

/- We are using types instead of sets for Vector spaces to capitalize on some cool mathlib4 features.
   To compensate, this is a type that encapsulates Set membership, allowing you to use Sets
   with Vector Spaces by wrapping the Sets in this type -/
inductive InSet (S : Set V)
| inSet : (a : V) → (a ∈ S) → InSet S

namespace VectorSpace
  variable (𝔽 : Type) [Field 𝔽] 
  variable (V : Type u) [AddZeroClass V]

  theorem zero_is_unique [VectorSpace 𝔽 V] (v : V) : 0 + v = 0 → v = 0 := by 
    rw[AddZeroClass.zero_add]
    exact id
end VectorSpace