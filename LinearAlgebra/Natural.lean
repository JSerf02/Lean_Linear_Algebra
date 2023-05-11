inductive Natural : Type where
| one : Natural
| succ : Natural → Natural

notation:100 "ℕ₁" => Natural

namespace Natural
  instance : Inhabited Natural where
    default := Natural.one

  @[simp]
  def ofNat (n : Nat) : Natural :=
    match n with
    | 0     => default
    | 1     => Natural.one
    | k + 1 => Natural.succ (ofNat k)

  instance : OfNat Natural n where
    ofNat := ofNat n

  @[simp]
  theorem ofNat_add_two_eq_succ_offNat_add_one (n : Nat) : ofNat (n + 2) = Natural.succ (ofNat (n + 1)) := by simp

  @[simp]
  theorem ofNat_one_add_eq_succ (n : Nat) : ofNat (1 + 1 + n) = Natural.succ (ofNat (1 + n)) := by simp[Nat.add_comm]


  @[simp]
  def toNat (n : Natural) : Nat :=
    match n with
    | 1 => 1
    | Natural.succ k => 1 + (toNat k)
  
  theorem zero_lt_toNat (n : Natural) : 0 < toNat n :=
    match n with
    | 1 => by simp
    | Natural.succ k => by
      simp
      let zero_lt_one := Nat.zero_lt_succ 0
      let prev := zero_lt_toNat k
      exact (Nat.add_lt_add zero_lt_one prev)
  
  theorem toNat_neq_zero (n : Natural) : toNat n ≠ 0 := Nat.not_eq_zero_of_lt (zero_lt_toNat n)

  @[simp]
  def ofNat_add_one_toNat_eq_succ (l : Natural) : ofNat (1 + toNat l) = succ l :=
    match l with
    | one => by simp
    | Natural.succ m => by 
      simp
      rw[← Nat.add_assoc]
      simp
      exact (ofNat_add_one_toNat_eq_succ m)
  
  @[simp]
  theorem ofNat_toNat_eq_id (n : Natural) : ofNat (toNat n) = n :=
    match n with
    | one => by simp
    | Natural.succ k => by simp

  @[simp]
  theorem toNat_ofNat_eq_id (n : Nat) (neq_zero : n ≠ 0) : toNat (ofNat n) = n :=
    match n with
    | 0 => by simp at neq_zero
    | 1 => by simp
    | k + 2 => by 
      rw[ofNat]
      simp
      have succ_k_neq_0 : k + 1 ≠ 0 := Nat.not_eq_zero_of_lt (Nat.zero_lt_succ k)
      let prev := toNat_ofNat_eq_id (k + 1) succ_k_neq_0
      rw[prev]
      rw[Nat.add_comm] -- Proof just finished
      exact Nat.not_eq_zero_of_lt (Nat.zero_lt_succ k) -- Proves k + 1 ≠ 0 which is necessary for pattern matching

  @[simp]
  def add (x y : Natural) : Natural :=
    match y with
    | one => Natural.succ x
    | Natural.succ k => Natural.succ (add x k)

  instance : Add Natural where
    add := Natural.add
  
  @[simp]
  theorem add_eq_Nat_add (x y : Natural) : 
    add x y = ofNat ((toNat x) + (toNat y)) := 
      match y with
      | one => by simp[toNat_neq_zero]
      | k + 1 => by 
        simp
        have prev : add x k = ofNat ((toNat x) + (toNat k)) := add_eq_Nat_add x k
        rw[prev, ← ofNat_add_one_toNat_eq_succ]
        have zero_lt_sum : 0 < (toNat x) + (toNat k) := Nat.add_lt_add (zero_lt_toNat x) (zero_lt_toNat k)
        let zero_neq_sum := Nat.not_eq_zero_of_lt zero_lt_sum
        let remove_id := toNat_ofNat_eq_id ((toNat x) + (toNat k)) zero_neq_sum
        rw[remove_id, Nat.add_comm, Nat.add_assoc, Nat.add_comm _ 1]
  
  @[simp]
  theorem Nat_add_eq_add (x y : Natural) : 
    ofNat ((toNat x) + (toNat y)) = add x y := Eq.symm (add_eq_Nat_add x y)
  
  @[simp]
  theorem succ_eq_add_one (n : Natural) : succ n = add n 1 := by simp

  @[simp]
  theorem add_one_eq_succ (n : Natural) : add n 1 = succ n := by simp

  instance : Repr Natural where
    reprPrec := fun (x : Natural) => Repr.reprPrec (toNat x)
end Natural

