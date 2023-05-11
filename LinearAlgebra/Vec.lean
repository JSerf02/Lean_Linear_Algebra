import LinearAlgebra.VectorSpace
import LinearAlgebra.Natural
@[simp]
def Vec (α : Type u) (n : ℕ₁) :=
  match n with 
  | 1 => α 
  | k + 1 => α × (Vec α k)

infix:50 "^" => Vec -- Allows you to write Vec 𝔽 n as 𝔽^n

/- Vecs are just tuples -/
def Tuple := Vec

namespace Vec
  @[simp]
  theorem Vec_zero_eq_Vec_one (α : Type u) : Vec α 0 = Vec α 1 := by simp

  @[simp]
  theorem Vec_one_eq_F (α : Type u) : Vec α 1 = α := by simp

  @[simp]
  theorem Vec_succ_k_eq_Prod : Vec 𝔽 (k + 1) = (𝔽 × (Vec 𝔽 k)) := by simp

  @[simp]
  def get {n : ℕ₁} (v : Vec α n) (idx : ℕ₁) : α :=
    match n, idx with
    | 1    , _     => by
      simp at v
      exact v
    | k + 1, 0     => by
      simp at v
      exact v.1
    | k + 1, i + 1 => by
      simp at v
      exact get v.2 i
  
  @[simp]
  def zip_with {n : ℕ₁} (f : α → β → γ)  (u : Vec α n) (v : Vec β n) : Vec γ n :=
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
  def add_Vec {𝔽 : Type} [Field 𝔽] {n : ℕ₁} (u : Vec 𝔽 n) (v : Vec 𝔽 n) : Vec 𝔽 n :=
    match n with
    | 1     => by 
      simp at u
      simp at v
      simp
      exact u + v
    | k + 1 => by
      simp at u
      simp at v
      simp
      have : 𝔽 × 𝔽^k := ⟨u.1 + v.1, add_Vec u.2 v.2⟩ 
      rw[Eq.symm Vec_succ_k_eq_Prod]
      assumption
  
  @[simp]
  def mult_Vec {𝔽 : Type} [Field 𝔽] {n : ℕ₁} (a : 𝔽) (v : Vec 𝔽 n) : Vec 𝔽 n :=
    match n with
    | 1     => by
      simp at v
      exact a * v
    | k + 1 => by
      simp at v
      simp
      have : 𝔽 × 𝔽^k := ⟨a * v.1, mult_Vec a v.2⟩ 
      rw[Eq.symm Vec_succ_k_eq_Prod]
      assumption
 
  def pair_eq (v : Vec α (n + 1)) : v = ⟨v.fst, v.snd⟩  := by simp
  
  @[simp]
  def zero_Vec (𝔽 : Type) [Field 𝔽] (n : ℕ₁) : Vec 𝔽 n :=
    match n with
    | 1     => by
      simp
      exact 0
    | k + 1 => by
      simp
      have : 𝔽 × 𝔽^k := ⟨0, zero_Vec 𝔽 k⟩ 
      rw[Eq.symm Vec_succ_k_eq_Prod]
      assumption
  
  
  theorem add_comm {𝔽 : Type} [Field 𝔽] {n : ℕ₁} (u v : Vec 𝔽 n) : add_Vec u v = add_Vec v u := 
    match n with
    | 1     => by
      simp at u
      simp at v
      simp[add_Vec]
      exact (AddCommSemigroup.add_comm u v)
    | k + 1 => by
      simp at u
      simp at v
      simp[add_Vec]
      exact ⟨AddCommSemigroup.add_comm u.1 v.1, add_comm u.2 v.2⟩ 
  
  @[simp]
  theorem add_assoc {𝔽 : Type} [Field 𝔽] {n : ℕ₁} (u v w : Vec 𝔽 n) : add_Vec u (add_Vec v w) = add_Vec (add_Vec u v) w :=
   match n with
    | 1     => by 
      simp at u
      simp at v
      simp at w
      exact (Eq.symm (AddSemigroup.add_assoc u v w))
    | k + 1 => by
      simp at u
      simp at v
      simp at w
      simp
      have fst_eq : u.1 + (v.1 + w.1) = (u.1 + v.1) + w.1 := Eq.symm (AddSemigroup.add_assoc u.1 v.1 w.1)
      have snd_eq : add_Vec u.2 (add_Vec v.2 w.2) = add_Vec (add_Vec u.2 v.2) w.2 := add_assoc u.2 v.2 w.2
      exact ⟨fst_eq, snd_eq⟩ 
    
    @[simp]
    theorem flip_add_assoc {𝔽 : Type} [Field 𝔽] {n : ℕ₁} (u v w : Vec 𝔽 n) : add_Vec (add_Vec u v) w = add_Vec u (add_Vec v w) :=
      Eq.symm (add_assoc u v w)
    
    @[simp]
    theorem zero_add {𝔽 : Type} [Field 𝔽] {n : ℕ₁} (v : Vec 𝔽 n) : 
    add_Vec (zero_Vec 𝔽 n) v = v :=
      match n with
      | 1     => by simp[zero_Vec, add_Vec]
      | k + 1 => by
        simp[zero_Vec, add_Vec]
        have to_pair : v = ⟨v.1, v.2⟩  := pair_eq v
        have pair_2 : add_Vec (zero_Vec 𝔽 k) v.2 = v.2 := zero_add v.2
        rw[← pair_2] at to_pair
        exact (Eq.symm to_pair)
    
  @[simp]
  theorem add_zero {𝔽 : Type} [Field 𝔽] {n : ℕ₁} (v : Vec 𝔽 n) : 
    add_Vec v (zero_Vec 𝔽 n) = v := by
      rw[add_comm v (zero_Vec 𝔽 n)]
      exact zero_add v
  
  @[simp]
  def neg {𝔽 : Type} [Field 𝔽] {n : ℕ₁} (v : Vec 𝔽 n) : Vec 𝔽 n :=
    match n with
    | 1     => by
      simp at v
      exact -v
    | k + 1 => by
      simp at v
      exact ⟨-v.1, neg v.2⟩ 
  
  theorem neg_eq_neg_one_mul {𝔽 : Type} [Field 𝔽] {n : ℕ₁} (v : Vec 𝔽 n) : 
    neg v = mult_Vec (-1 : 𝔽) v :=
      match n with
      | 1     => by
        simp at v
        simp
      | k + 1 => by
        simp at v
        simp
        exact neg_eq_neg_one_mul v.2
    
  theorem neg_one_mul_eq_neg {𝔽 : Type} [Field 𝔽] {n : ℕ₁} (v : Vec 𝔽 n) :
    mult_Vec (-1 : 𝔽) v = neg v := Eq.symm (neg_eq_neg_one_mul v)

  @[simp]
  theorem neg_is_add_inv {𝔽 : Type} [Field 𝔽] {n : ℕ₁} (v : Vec 𝔽 n) :
    add_Vec (neg v) v = zero_Vec 𝔽 n :=
      match n with
      | 1     => by
        simp at v
        simp
      | k + 1 => by
        simp at v
        simp
        exact neg_is_add_inv v.2
  
  @[simp]
  def add_inv {𝔽 : Type} [Field 𝔽] {n : ℕ₁} (v : Vec 𝔽 n) :
    ∃ v_inv, add_Vec v_inv v = zero_Vec 𝔽 n :=
      ⟨neg v, neg_is_add_inv v⟩ 
  
  @[simp]
  theorem mult_id {𝔽 : Type} [Field 𝔽] {n : ℕ₁} (v : Vec 𝔽 n) : 
    mult_Vec 1 v = v :=
      match n with
      | 1     => by
        simp at v
        simp
      | k + 1 => by
        simp at v
        simp
        have eq_pair : (v.1, v.2) = v := pair_eq v
        rw[← mult_id v.2] at eq_pair
        exact eq_pair
  
  @[simp]
  theorem mult_assoc {𝔽 : Type} [Field 𝔽] {n : ℕ₁} (a b : 𝔽) (v : Vec 𝔽 n) :
    mult_Vec (a * b) v = mult_Vec a (mult_Vec b v) :=
      match n with
      | 1     => by
        simp at v
        simp
        exact Semigroup.mul_assoc a b v
      | k + 1 => by
        simp at v
        simp
        have fst : a * b * v.1 = a * (b * v.1) := Semigroup.mul_assoc a b v.1
        have snd : mult_Vec (a * b) v.2 = mult_Vec a (mult_Vec b v.2) := mult_assoc a b v.2
        exact ⟨fst, snd⟩ 

  @[simp]
  theorem flip_mult_assoc {𝔽 : Type} [Field 𝔽] {n : ℕ₁} (a b : 𝔽) (v : Vec 𝔽 n) :
    mult_Vec a (mult_Vec b v) = mult_Vec (a * b) v := Eq.symm (mult_assoc a b v)
  
  theorem mult_distrib_vec {𝔽 : Type} [Field 𝔽] {n : ℕ₁} (a : 𝔽) (u v : Vec 𝔽 n) :
    mult_Vec a (add_Vec u v) = add_Vec (mult_Vec a u) (mult_Vec a v) := 
      match n with
      | 1     => by
        simp
        exact left_distrib a u v
      | k + 1 => by
        simp at u
        simp at v
        simp
        have fst : a * (u.1 + v.1) = a * u.1 + a * v.1 := left_distrib a u.1 v.1
        have snd : mult_Vec a (add_Vec u.2 v.2) = add_Vec (mult_Vec a u.2) (mult_Vec a v.2) := mult_distrib_vec a u.2 v.2
        exact ⟨fst, snd⟩ 

  theorem mult_distrib_add {𝔽 : Type} [Field 𝔽] {n : ℕ₁} (a b : 𝔽) (v : Vec 𝔽 n) :
    mult_Vec (a + b) v = add_Vec (mult_Vec a v) (mult_Vec b v) :=
      match n with
      | 1    => by
        simp
        exact right_distrib a b v
      | k + 1 => by
        simp at v
        simp
        have fst : (a + b) * v.1 = a * v.1 + b * v.1 := right_distrib a b v.1
        have snd : mult_Vec (a + b) v.2 = add_Vec (mult_Vec a v.2) (mult_Vec b v.2) := mult_distrib_add a b v.2
        exact ⟨fst, snd⟩ 

  variable {𝔽 : Type} [Field 𝔽] {n : ℕ₁}

  /- Allows you to use + and 0 with Vec 𝔽 n -/
  instance : AddZeroClass (Vec 𝔽 n) where
    zero := zero_Vec 𝔽 n
    add := add_Vec
    zero_add := Vec.zero_add
    add_zero := Vec.add_zero

  /- Allows you to use * with 𝔽 and Vec 𝔽 n -/
  instance : HMul 𝔽 (Vec 𝔽 n) (Vec 𝔽 n) where
    hMul := mult_Vec
  
  /- Allows you to write -v where (v : Vec 𝔽 n) to get the additive inverse of v-/
  instance : Neg (Vec 𝔽 n) where
    neg := Vec.neg

  /- Allows you to use binary - to denote subtraction of Vec 𝔽 n terms -/
  instance : Sub (Vec 𝔽 n) where
    sub := fun (u v : Vec 𝔽 n) => add_Vec u (-v)
  
  /- Vec is a VectorSpace -/
  instance : VectorSpace 𝔽 (Vec 𝔽 n) where
    add_comm := Vec.add_comm
    add_assoc := Vec.add_assoc
    additive_inverse := add_inv

    mult_id := Vec.mult_id
    mult_assoc := mult_assoc
    mult_distrib_vec := Vec.mult_distrib_vec
    mult_distrib_add := Vec.mult_distrib_add
end Vec

namespace Tuple
  open Vec
end Tuple