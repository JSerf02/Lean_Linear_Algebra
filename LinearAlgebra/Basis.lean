-- import LinearAlgebra.VectorSpace
-- import LinearAlgebra.Natural
-- import LinearAlgebra.Vec

/- Here, we provide tools for interacting with finite dimensional VectorSpaces 
   Note that certain things like infinite spanning sets will not be supported here -/
namespace Basis
  variable {𝔽 : Type} [Field 𝔽] {α : Type u} [AddZeroClass α] [HMul 𝔽 α α]
  
  @[simp]
  def accum {n : ℕ₁} (vs : Vec α n) (factors : Vec 𝔽 n) : α :=
    Vec.foldr Add.add Zero.zero (Vec.zip_with HMul.hMul factors vs)
  
  @[simp]
  theorem spanning {n : ℕ₁} (vs : Vec α n) (V : VectorSpace 𝔽 α) : Prop :=
    ∀ (v : α), ∃ (factors : Vec 𝔽 n), accum vs factors = v
  
  @[simp]
  theorem basis {n : ℕ₁} (vs : Vec α n) (V : VectorSpace 𝔽 α) : Prop :=
    let span := spanning vs V
    let unique := 
      ∀ (v : α), ∀ (factors₁ factors₂ : Vec 𝔽 n), 
        accum vs factors₁ = v ∧ accum vs factors₂ = v 
        → factors₁ = factors₂
    span ∧ unique
  
  -- def linear_independent {n : ℕ₁} (vs : Vec α n) (V : VectorSpace 𝔽 α) : Prop :=
    
end Basis