import LinearAlgebra.Vec
import LinearAlgebra.VecMember

open Vec

namespace Vec.Operations
  @[simp]
  def map {n : ℕ₁} (f : α → β) (v : Vec α n) : Vec β n :=
    match n with
    | 1 => by
      simp at v
      exact f v
    | k + 1 => by
      simp at v
      have fst : β := f v.1
      have snd : Vec β k := map f v.2
      exact ⟨fst, snd⟩ 
  
  @[simp]
  def zip_with {n : ℕ₁} (f : α → β → γ) (u : Vec α n) (v : Vec β n) : Vec γ n :=
    match n with
    | 1     => by
      simp at u
      simp at v
      exact f u v
    | k + 1 => by
      simp at u
      simp at v
      have fst : γ := f u.1 v.1
      have snd : Vec γ k := zip_with f u.2 v.2
      exact ⟨fst, snd⟩ 
  
  @[simp]
  def foldr {n : ℕ₁} (f : α → β → β) (base : β) (v : Vec α n) : β :=
    match n with
    | 1 => by
      simp at v
      exact f v base
    | k + 1 => by
      simp at v
      exact f v.1 (foldr f base v.2)

  @[simp]
  def foldl {n : ℕ₁} (f : α → β → β) (base : β) (v : Vec α n) : β :=
    match n with
    | 1 => by
      simp at v
      exact f v base
    | k + 1 => by
      simp at v
      exact foldl f (f v.1 base) v.2

  @[simp]
  def accum {n : ℕ₁} [AddCommGroup α] [HMul 𝔽 α α] (as : Vec α n) (factors : Vec 𝔽 n) : α :=
    foldr Add.add Zero.zero (zip_with HMul.hMul factors as)
  
  @[simp]
  theorem add_passes_through_accum {n : ℕ₁} [AddCommGroup V] [Field 𝔽] [VectorSpace 𝔽 V]
    (vs : Vec V n) (factors₁ factors₂ : Vec 𝔽 n) : 
    (accum vs factors₁) + (accum vs factors₂) 
    = accum vs (factors₁ + factors₂) := 
      match n with
      | 1     => by
        simp at factors₁
        simp at factors₂
        simp at vs
        let zero_eq_0 : Zero.zero = (0 : V) := by rfl
        let add_eq_plus (x y : V): Add.add x y = x + y := by rfl
        simp[zero_eq_0, add_eq_plus]
        have result := VectorSpace.mult_distrib_scalar_add factors₁ factors₂ vs
        exact (Eq.symm result)
      | k + 1 => by
        simp at factors₁
        simp at factors₂
        simp at vs
        let zero_eq_0 : Zero.zero = (0 : V) := by rfl
        let add_eq_plus (x y : V): Add.add x y = x + y := by rfl
        simp[zero_eq_0, add_eq_plus]
        have prev := add_passes_through_accum vs.2 factors₁.2 factors₂.2
        have next := Eq.symm (VectorSpace.mult_distrib_scalar_add factors₁.1 factors₂.1 vs.1)
        have curried_add := congrArg (fun x y => y + x) prev
        let result := congr curried_add next
        rw[AddSemigroup.add_assoc] at result
        rw[← AddSemigroup.add_assoc (factors₂.1 * vs.1)] at result
        rw[AddCommGroup.add_comm (factors₂.1 * vs.1)] at result
        rw[AddSemigroup.add_assoc] at result
        rw[← AddSemigroup.add_assoc] at result
        simp at result
        exact result

  @[simp]
  theorem neg_passes_through_accum {n : ℕ₁} [AddCommGroup V] [Field 𝔽] [VectorSpace 𝔽 V] 
    (vs : Vec V n) (factors : Vec 𝔽 n) :
    -(accum vs factors) = accum vs (-factors) := 
      match n with
      | 1     => by
        simp at factors
        simp at vs
        simp
        let zero_eq_0 : Zero.zero = (0 : V) := by rfl
        let add_eq_plus (x y : V): Add.add x y = x + y := by rfl
        simp[zero_eq_0, add_eq_plus]
      | k + 1 => by
        simp at factors
        simp at vs
        simp
        let zero_eq_0 : Zero.zero = (0 : V) := by rfl
        let add_eq_plus (x y : V): Add.add x y = x + y := by rfl
        simp[zero_eq_0, add_eq_plus]
        let prev := neg_passes_through_accum vs.2 factors.2
        simp at prev
        rw[zero_eq_0] at prev
        rw[AddCommGroup.add_comm]
        simp
        exact prev
    
    @[simp]
    theorem accum_zero_is_zero {n : ℕ₁} (𝔽 : Type) [AddCommGroup V] [Field 𝔽] [VectorSpace 𝔽 V] (vs : Vec V n) :
      accum vs (0 : Vec 𝔽 n) = 0 := 
        match n with
        | 1     => by 
          simp
          let zero_eq_0 : Zero.zero = (0 : V) := by rfl
          let add_eq_plus (x y : V): Add.add x y = x + y := by rfl
          simp[zero_eq_0, add_eq_plus]
        | k + 1 => by
          simp at vs
          simp
          let zero_eq_0 : Zero.zero = (0 : V) := by rfl
          let add_eq_plus (x y : V): Add.add x y = x + y := by rfl
          simp[zero_eq_0, add_eq_plus]
          have z_eq_0 : (0 : 𝔽^k+1).fst = (0 : 𝔽) := by rfl
          simp[z_eq_0]
          have prev := accum_zero_is_zero 𝔽 vs.2
          simp[zero_eq_0] at prev
          exact prev


  @[simp]
  theorem add_passes_through_zip_with {n : ℕ₁} [AddCommGroup α] (as₁ as₂ : Vec α n) : 
    zip_with (. + .) as₁ as₂ = as₁ + as₂ := 
      match n with
      | 1     => by simp
      | k + 1 => by 
        simp at as₁
        simp at as₂
        simp 
        have prev : zip_with (fun x x_1 => x + x_1) as₁.2 as₂.2 = as₁.2 + as₂.2 := 
          add_passes_through_zip_with as₁.2 as₂.2
        let result := congrArg (Prod.mk (as₁.1 + as₂.1) .) prev
        exact result
  
  @[simp]
  theorem neg_passes_through_map {n : ℕ₁} [AddCommGroup α] (as : Vec α n) :
    map (-.) as = -as := 
      match n with
      | 1 => by simp
      | k + 1 => by
        simp at as
        simp
        have prev : map (-.) as.2 = -as.2 := neg_passes_through_map as.2
        let result := congrArg (Prod.mk (-as.1) .) prev
        exact result
end Vec.Operations