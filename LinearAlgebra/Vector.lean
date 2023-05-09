import LinearAlgebra.VectorSpace

def Vec (𝔽 : Type) [Field 𝔽]  (n : Nat) :=
  Vector 𝔽 n

infix:50 "^" => Vec -- Allows you to write Vec 𝔽 n as 𝔽^n

namespace Vec
  variable {𝔽 : Type} [Field 𝔽]
  variable {n : Nat}

  def add_Vec (u : Vec 𝔽 n) (v : Vec 𝔽 n) : Vec 𝔽 n :=
    Vector.map₂ (fun (x y : 𝔽) => x + y) u v
  def mult_Vec (a : 𝔽) (v : Vec 𝔽 n) : Vec 𝔽 n :=
    Vector.map (fun (x : 𝔽) => a * x) v

  instance : AddZeroClass (Vec 𝔽 n) where
    zero := Vector.replicate n 0
    add := add_Vec
    zero_add := fun (v : Vec 𝔽 n) => sorry
    add_zero := fun (v : Vec 𝔽 n) => sorry

  instance : HMul 𝔽 (Vec 𝔽 n) (Vec 𝔽 n) where
    hMul := mult_Vec
        
  instance : VectorSpace 𝔽 (Vec 𝔽 n) where
    V := setOf (fun (x : (Vec 𝔽 n)) => true)

    add_well_defined := by simp[*]
    mult_well_defined := by simp[*]

    add_assoc := sorry
    add_com := sorry
    additive_inverse := sorry

    mult_id := sorry
    mult_assoc := sorry
    mult_distrib_vec := sorry
    mult_distrib_add := sorry
end Vec
