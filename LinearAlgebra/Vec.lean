import LinearAlgebra.VectorSpace
@[simp]
def Vec (α : Type u) (n : Nat) :=
  match n with 
  | 0 => α 
  | 1 => α 
  | Nat.succ k => α × (Vec α k)

infix:50 "^" => Vec -- Allows you to write Vec 𝔽 n as 𝔽^n

namespace Vec
  @[simp]
  theorem Vec_zero_eq_Vec_one (α : Type u) : Vec α 0 = Vec α 1 := by simp
  @[simp]
  theorem Vec_one_eq_F (α : Type u) : Vec α 1 = α := by simp

  @[simp]
  theorem Vec_succ_k_eq_Prod : Vec 𝔽 (k + 2) = (𝔽 × (Vec 𝔽 (k + 1))) := by simp
  @[simp]
  def add_Vec {𝔽 : Type} [Field 𝔽] {n : Nat} (u : Vec 𝔽 n) (v : Vec 𝔽 n) : Vec 𝔽 n :=
    match n with
    | 0 => by 
        simp at u
        simp at v
        simp
        exact u + v
    | 1 => 
      by 
        simp at u
        simp at v
        simp
        exact u + v
    | k + 2 => 
      by
        simp at u
        simp at v
        simp
        have : 𝔽 × 𝔽^k+1 := ⟨u.1 + v.1, add_Vec u.2 v.2⟩ 
        rw[Eq.symm Vec_succ_k_eq_Prod]
        assumption

  def mult_Vec {𝔽 : Type} [Field 𝔽] {n : Nat} (a : 𝔽) (v : Vec 𝔽 n) : Vec 𝔽 n :=
    match n with
    | 0 => by
      simp at v
      exact a * v
    | 1 => by
      simp at v
      exact a * v
    | k + 2 => by
      simp at v
      simp
      have : 𝔽 × 𝔽^k+1 := ⟨a * v.1, mult_Vec a v.2⟩ 
      rw[Eq.symm Vec_succ_k_eq_Prod]
      assumption
 
  def pair_eq (v : Vec α (n + 2)) : v = ⟨v.fst, v.snd⟩  := by simp
  
  def zero_Vec (𝔽 : Type) [Field 𝔽] (n : Nat) : Vec 𝔽 n :=
    match n with
    | 0 => by
      simp
      exact 0
    | 1 => by
      simp
      exact 0
    | k + 2 => by
      simp
      have : 𝔽 × 𝔽^k+1 := ⟨0, zero_Vec 𝔽 (k + 1)⟩ 
      rw[Eq.symm Vec_succ_k_eq_Prod]
      assumption
  
  def add_comm {𝔽 : Type} [Field 𝔽] {n : Nat} (u v : Vec 𝔽 n) : add_Vec u v = add_Vec v u := 
    match n with
    | 0 => by
      simp at u
      simp at v
      simp[add_Vec]
      exact (AddCommSemigroup.add_comm u v)
    | 1 => by
      simp at u
      simp at v
      simp[add_Vec]
      exact (AddCommSemigroup.add_comm u v)
    | k + 2 => by
      simp at u
      simp at v
      simp[add_Vec]
      exact ⟨AddCommSemigroup.add_comm u.1 v.1, add_comm u.2 v.2⟩ 
  
  def add_assoc {𝔽 : Type} [Field 𝔽] {n : Nat} (u v w : Vec 𝔽 n) : add_Vec u (add_Vec v w) = add_Vec (add_Vec u v) w :=
   match n with
    | 0 => by 
      simp at u
      simp at v
      simp at w
      exact (Eq.symm (AddSemigroup.add_assoc u v w))
    | 1 => by 
      simp at u
      simp at v
      simp at w
      exact (Eq.symm (AddSemigroup.add_assoc u v w))
    | k + 2 => by
      simp at u
      simp at v
      simp at w
      simp
      have fst_eq : u.1 + (v.1 + w.1) = (u.1 + v.1) + w.1 := Eq.symm (AddSemigroup.add_assoc u.1 v.1 w.1)
      have snd_eq : add_Vec u.2 (add_Vec v.2 w.2) = add_Vec (add_Vec u.2 v.2) w.2 := add_assoc u.2 v.2 w.2
      exact ⟨fst_eq, snd_eq⟩ 
  
   def zero_add {𝔽 : Type} [Field 𝔽] {n : Nat} (v : Vec 𝔽 n) : add_Vec (zero_Vec 𝔽 n) v = v :=
      match n with
      | 0 => by simp[zero_Vec, add_Vec]
      | 1 => by simp[zero_Vec, add_Vec]
      | k + 2 => by
        simp[zero_Vec, add_Vec]
        have to_pair : v = ⟨v.1, v.2⟩  := pair_eq v
        have pair_2 : add_Vec (zero_Vec 𝔽 (k + 1)) v.2 = v.2 := zero_add v.2
        rw[← pair_2] at to_pair
        exact (Eq.symm to_pair)
  
  def add_zero {𝔽 : Type} [Field 𝔽] {n : Nat} (v : Vec 𝔽 n) : add_Vec v (zero_Vec 𝔽 n) = v := 
    by
      rw[add_comm v (zero_Vec 𝔽 n)]
      exact zero_add v

  variable {𝔽 : Type} [Field 𝔽] {n : Nat}

  instance : AddZeroClass (Vec 𝔽 n) where
    zero := zero_Vec 𝔽 n
    add := add_Vec
    zero_add := Vec.zero_add
    add_zero := Vec.add_zero


  instance : HMul 𝔽 (Vec 𝔽 n) (Vec 𝔽 n) where
    hMul := mult_Vec
  #check AddSemigroup
  instance : VectorSpace 𝔽 (Vec 𝔽 n) where
    V := setOf (fun (x : (Vec 𝔽 n)) => true)

    add_well_defined := by simp[*]
    mult_well_defined := by simp[*]
    
    add_comm := Vec.add_comm
    add_assoc := Vec.add_assoc
    additive_inverse := sorry

    mult_id := sorry
    mult_assoc := sorry
    mult_distrib_vec := sorry
    mult_distrib_add := sorry
end Vec
