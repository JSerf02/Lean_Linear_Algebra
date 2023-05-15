import LinearAlgebra.Vec
import LinearAlgebra.VectorSpace

open Vec
namespace Vec.Operations
  @[simp]
  def add_Vec {α : Type} [AddCommGroup α] {n : ℕ₁} (u v : Vec α n) : Vec α n :=
    zip_with (. + .) u v
  
  @[simp]
  def mult_Vec {𝔽 α : Type} [AddCommGroup α] [Field 𝔽] [HMul 𝔽 α α] {n : ℕ₁} (a : 𝔽) (v : Vec α n) : Vec α n :=
    map (a * .) v
  
  @[simp]
  def zero_Vec (𝔽 : Type) [AddCommGroup α] (n : ℕ₁) : Vec α n :=
    replicate 0 n
  
  theorem add_comm {α : Type} [AddCommGroup α] {n : ℕ₁} (u v : Vec α n) : 
    add_Vec u v = add_Vec v u := by simp[entrywise_eq, AddCommGroup.add_comm]
  
  @[simp]
  theorem add_assoc {α : Type} [AddCommGroup α] {n : ℕ₁} (u v w : Vec α n) : 
    add_Vec u (add_Vec v w) = add_Vec (add_Vec u v) w := by 
      simp[entrywise_eq, AddSemigroup.add_assoc]
  
  @[simp]
  theorem flip_add_assoc {α : Type} [AddCommGroup α] {n : ℕ₁} (u v w : Vec α n) : 
    add_Vec (add_Vec u v) w = add_Vec u (add_Vec v w) :=
      Eq.symm (add_assoc u v w)
    
  @[simp]
  theorem zero_add {α : Type} [AddCommGroup α] {n : ℕ₁} (v : Vec α n) : 
    add_Vec (zero_Vec α n) v = v := by simp
    
  @[simp]
  theorem add_zero {α : Type} [AddCommGroup α] {n : ℕ₁} (v : Vec α n) : 
    add_Vec v (zero_Vec α n) = v := by
      rw[add_comm v (zero_Vec α n)]
      exact zero_add v
  
  @[simp]
  def neg {α : Type} [AddCommGroup α] {n : ℕ₁} (v : Vec α n) : Vec α n :=
    map (fun x => -x) v
  
  theorem neg_eq_neg_one_mul {𝔽 : Type} [Field 𝔽] {n : ℕ₁} (v : Vec 𝔽 n) : 
    neg v = mult_Vec (-1 : 𝔽) v := by simp
  

  theorem neg_one_mul_eq_neg {𝔽 : Type} [Field 𝔽] {n : ℕ₁} (v : Vec 𝔽 n) :
    mult_Vec (-1 : 𝔽) v = neg v := Eq.symm (neg_eq_neg_one_mul v)

  @[simp]
  theorem neg_is_add_inv {α : Type} [AddCommGroup α] {n : ℕ₁} (v : Vec α n) :
    add_Vec (neg v) v = zero_Vec 𝔽 n := by
      simp[zip_with, replicate_id]
  
  @[simp]
  def add_inv {α : Type} [AddCommGroup α] {n : ℕ₁} (v : Vec α n) :
    ∃ v_inv, add_Vec v_inv v = zero_Vec 𝔽 n :=
      ⟨neg v, neg_is_add_inv v⟩ 
  
  @[simp]
  theorem mult_id {𝔽 : Type} [Field 𝔽] {n : ℕ₁} (v : Vec 𝔽 n) : 
    mult_Vec 1 v = v := by simp
  
  @[simp]
  theorem mult_assoc {𝔽 : Type} [Field 𝔽] {n : ℕ₁} (a b : 𝔽) (v : Vec 𝔽 n) :
    mult_Vec (a * b) v = mult_Vec a (mult_Vec b v) := by simp[Semigroup.mul_assoc]

  @[simp]
  theorem flip_mult_assoc {𝔽 : Type} [Field 𝔽] {n : ℕ₁} (a b : 𝔽) (v : Vec 𝔽 n) :
    mult_Vec a (mult_Vec b v) = mult_Vec (a * b) v := Eq.symm (mult_assoc a b v)
  
  theorem mult_distrib_vec_add {𝔽 : Type} [Field 𝔽] {n : ℕ₁} (a : 𝔽) (u v : Vec 𝔽 n) :
    mult_Vec a (add_Vec u v) = add_Vec (mult_Vec a u) (mult_Vec a v) := by
      simp[zip_with, entrywise_eq, apply_swap v u, left_distrib]

  theorem mult_distrib_scalar_add {𝔽 : Type} [Field 𝔽] {n : ℕ₁} (a b : 𝔽) (v : Vec 𝔽 n) :
    mult_Vec (a + b) v = add_Vec (mult_Vec a v) (mult_Vec b v) := by
      simp[zip_with, entrywise_eq, right_distrib]

  instance {α : Type} [AddCommGroup α] {n : ℕ₁} : AddCommGroup (Vec α n) where
    zero := zero_Vec α n
    add := add_Vec
    zero_add := zero_add
    add_zero := add_zero
    neg := neg
    add_assoc := fun (u v w : Vec α n) => Eq.symm (add_assoc u v w)
    add_left_neg := neg_is_add_inv
    add_comm := add_comm
  
  instance {α 𝔽 : Type} [AddCommGroup α] [Field 𝔽] [HMul 𝔽 α α] : HMul 𝔽 (Vec α n) (Vec α n) where
    hMul := mult_Vec
  
  instance [Field 𝔽] [AddCommGroup V] [VectorSpace 𝔽 V] : HMul 𝔽 (Vec V n) (Vec V n) where
    hMul := mult_Vec
  
  /- Vec is a VectorSpace -/
  instance {𝔽 : Type} [Field 𝔽] {n : ℕ₁} : VectorSpace 𝔽 (Vec 𝔽 n) where
    mult_id := mult_id
    mult_assoc := mult_assoc
    mult_distrib_vec_add := mult_distrib_vec_add
    mult_distrib_scalar_add := mult_distrib_scalar_add 
  
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
        simp[zip_with]
        let zero_eq_0 : Zero.zero = (0 : V) := by rfl
        let add_eq_plus (x y : V): Add.add x y = x + y := by rfl
        simp[zero_eq_0, add_eq_plus]
      | k + 1 => by
        simp at factors
        simp at vs
        simp[zip_with]
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
          simp[zip_with]
          let zero_eq_0 : Zero.zero = (0 : V) := by rfl
          let add_eq_plus (x y : V): Add.add x y = x + y := by rfl
          simp[zero_eq_0, add_eq_plus]
        | k + 1 => by
          simp at vs
          simp[zip_with]
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
      | 1     => by simp[zip_with]
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
      | 1     => by simp
      | k + 1 => by
        simp at as
        simp
        have prev : map (-.) as.2 = -as.2 := neg_passes_through_map as.2
        let result := congrArg (Prod.mk (-as.1) .) prev
        exact result
end Vec.Operations