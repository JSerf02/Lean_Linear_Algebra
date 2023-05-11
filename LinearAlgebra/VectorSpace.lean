import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic

/-
  - Here are all of the MathLib4 type classes used here:
  - [Field 𝔽] - 𝔽 should be a field, self explanatory
  - [AddCommGroup V] - V should have addition defined with 0, associativity, and commutativity
  - extends HMul 𝔽 V V - You can multiply elements of type 𝔽 with elements of type V to get V 
    - extends necessitates that every VectorSpace must be an HMul, elements of a VectorSpace must have
      multiplication defined
-/
class VectorSpace (𝔽 : Type) [Field 𝔽] (V : Type u) [AddCommGroup V] extends HMul 𝔽 V V where
  mult_id (v : V) : (1 : 𝔽) * v = v
  mult_assoc (a b: 𝔽) (v : V) : (a * b) * v = a * (b * v)
  mult_distrib_vec_add (a : 𝔽) (u v : V) : a * (u + v) = a * u + a * v
  mult_distrib_scalar_add (a b : 𝔽) (v : V) : (a + b) * v = a * v + b * v

/- We are using types instead of sets for Vector spaces to capitalize on some cool mathlib4 features.
   To compensate, this is a type that encapsulates Set membership, allowing you to use Sets
   with Vector Spaces by wrapping the Sets in this type -/
inductive InSet (S : Set V)
| inSet : (a : V) → (a ∈ S) → InSet S

namespace VectorSpace
  variable (𝔽 : Type) [Field 𝔽] 
  variable (V : Type u) [AddCommGroup V]

  @[simp]
  theorem neg_neg_is_id [VectorSpace 𝔽 V] (v : V) : -(-v) = v := by simp

  @[simp]
  theorem neg_one_mul_is_neg [VectorSpace 𝔽 V] (v : V) : (-1 : 𝔽) * v = -v := by 
    have intro_inv : (-1 : 𝔽) * v = (-1 + (1 + -1) : 𝔽) * v := by simp
    rw[mult_distrib_scalar_add, mult_distrib_scalar_add, mult_id] at intro_inv
    have v_plus_neg_one_mult_eq_zero := congrArg (. + -(-1 : 𝔽) * v) intro_inv
    simp at v_plus_neg_one_mult_eq_zero
    have result := congrArg (. + -v) v_plus_neg_one_mult_eq_zero
    simp at result
    exact result
  
  @[simp]
  theorem zero_is_unique [VectorSpace 𝔽 V] (v : V) : 0 + v = 0 → v = 0 := by 
    rw[AddZeroClass.zero_add]
    exact id

  @[simp]
  theorem zero_mult_eq_zero [VectorSpace 𝔽 V] (v : V) : (0 : 𝔽) * v = 0 := by
    have initial_zero : (1 + -1 : 𝔽) * v = (0 : 𝔽) * v := by simp
    rw[mult_distrib_scalar_add, mult_id, neg_one_mul_is_neg] at initial_zero
    simp at initial_zero
    exact (Eq.symm initial_zero)
  
  @[simp]
  theorem neg_vec_is_neg_scalar [VectorSpace 𝔽 V] (a : 𝔽) (v : V) : -(a * v) = -a * v := by
    have right_zero : 0 = (a + -a) * v := by simp
    rw[mult_distrib_scalar_add] at right_zero
    have result := congrArg (-(a * v) + .) right_zero
    simp at result
    exact result
end VectorSpace