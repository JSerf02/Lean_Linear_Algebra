import LinearAlgebra.VectorSpace
import LinearAlgebra.Natural
import LinearAlgebra.Vec
import LinearAlgebra.VecOperations

open Vec.Operations

/- Here, we provide tools for interacting with finite dimensional VectorSpaces 
   Note that certain things like infinite spanning sets will not be supported here -/
namespace Basis
  -- (𝔽 : Type) instead of {𝔽 : Type} is necessary because Lean gets stuck otherwise for some reason
  -- - Theoretically, this should not be necessary though
  variable (𝔽 : Type) [Field 𝔽] (V : Type u) [AddCommGroup V] [VectorSpace 𝔽 V] {n : ℕ₁} (vs : Vec V n)
  class Spanning where
    span : ∀ (v : V), ∃ (factors : Vec 𝔽 n), accum vs factors = v 
  
  class Unique where
    unique : ∀ (v : V), ∀ (factors₁ factors₂ : Vec 𝔽 n), 
        accum vs factors₁ = v ∧ accum vs factors₂ = v 
        → factors₁ = factors₂

  class LinearIndependent where
    linear_independent : ∀ (factors : Vec 𝔽 n),
      accum vs factors = 0 → factors = 0
end Basis

class Basis (𝔽 : Type) [Field 𝔽] (V : Type u) [AddCommGroup V] [VectorSpace 𝔽 V] {n : ℕ₁} (vs : Vec V n) extends Basis.Spanning 𝔽 V vs, Basis.Unique 𝔽 V vs

namespace Basis
  variable (𝔽 : Type) [Field 𝔽] (V : Type u) [AddCommGroup V] [VectorSpace 𝔽 V] {n : ℕ₁} (vs : Vec V n)
  
  open Vec.Operations

  instance [Spanning 𝔽 V vs] [LinearIndependent 𝔽 V vs] : Basis 𝔽 V vs where
    unique := fun (v : V) (factors₁ factors₂ : Vec 𝔽 n) => by
      intro h
      have sum_1 : accum vs factors₁ = v := h.left 
      have sum_2 : accum vs factors₂ = v := h.right
      have neg_sum_2 : -(accum vs factors₂) = -v := congrArg (-. ) sum_2
      rw[neg_passes_through_accum] at neg_sum_2
      let add_sum_1_l : V → V := (accum vs factors₁ + .)
      let add_sum_1_r : V → V := (v + .)
      have add_sum_eq : add_sum_1_l = add_sum_1_r := congrArg (. + .) sum_1
      let final_accum_sum := congr add_sum_eq neg_sum_2
      simp[-accum] at final_accum_sum
      let final_sum := LinearIndependent.linear_independent (factors₁ + -factors₂) final_accum_sum
      let result := congrArg (. + factors₂) final_sum
      simp at result
      exact result
  
  instance [Basis 𝔽 V vs] : LinearIndependent 𝔽 V vs where
    linear_independent := fun (factors : Vec 𝔽 n) => by
      intro h
      have zero_accum : accum vs 0 = 0 := accum_zero_is_zero 𝔽 vs
      have factors_and_zero : accum vs factors = 0 ∧ accum vs 0 = 0 := ⟨h, zero_accum⟩ 
      exact (Unique.unique (0 : V) factors (0 : Vec 𝔽 n) factors_and_zero)

  variable [VectorSpace 𝔽 V] [Spanning 𝔽 V vs] [LinearIndependent 𝔽 V vs]
end Basis
