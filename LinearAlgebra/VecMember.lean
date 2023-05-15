import LinearAlgebra.Vec

namespace Vec
  @[simp]
  theorem mem : α → (Vec α n) → Prop := 
    fun (a : α) (v : Vec α n) => 
      ∃ (idx : ℕ₁), get v idx = a
  

  @[simp]
  instance {n : ℕ₁} : Membership α (Vec α n) where
    mem := Vec.mem
  
  instance : Membership α α where 
    mem := fun x y => x = y
  
  @[simp]
  theorem get_unit_is_vec (idx : ℕ₁) (v : Vec α 1) : get v idx = (v : α) := by simp

  @[simp]
  theorem exists_elim (α : Type u) [Inhabited α] (p : Prop) : (∃ (a : α), p) ↔ p := by
    apply Iff.intro
    . intro ⟨_, p⟩ 
      exact p
    . intro p
      exact ⟨default, p⟩ 

  @[simp]
  theorem mem_unit_is_eq (a : α) (v : Vec α 1) : (∃ (idx : ℕ₁), get v idx = a) ↔ (v = a) := by 
    simp 

  @[simp]
  theorem mem_k_plus_1_is_mem_unit_or_mem_k {n : ℕ₁} (a : α) (v : Vec α (n + 1)) : 
    (∃ (idx : ℕ₁), get v idx = a) ↔ ((a = v.1) ∨ (∃ (idx : ℕ₁), get v.2 idx = a)) := by
    simp 
    apply Iff.intro
    . intro ⟨idx, left⟩ 
      match idx with
      | 1 => 
        let right := left
        simp at right
        apply Or.intro_left
        . exact (Eq.symm right)
      | k + 1 =>
        simp at v
        simp at left
        apply Or.intro_right
        . exact ⟨k,  left⟩
    . intro h
      apply Or.elim h
      . intro a_eq_v1
        let get_1 : get v 1 = a := by simp[a_eq_v1]
        exact ⟨1, get_1⟩
      . intro ⟨k, vk_eq_a⟩ 
        let get_k_plus_1 : get v (k + 1) = a := by 
          simp[get, vk_eq_a]
        exact ⟨k + 1, get_k_plus_1⟩ 
  
  @[simp]
  def decidable_mem {n : ℕ₁} [inst : DecidableEq α] (a : α) (v : Vec α n) : Decidable ((∃ (idx : ℕ₁), get v idx = a)) := 
    match n with
    | 1 => by 
      simp
      simp[Eq.symm]
      exact decEq v a
    | k + 1 => by
      simp at v
      simp
      let prev := decidable_mem a v.2
      let next := decEq v.1 a
      match prev, next with
      | isFalse h1, isFalse h2 =>
        let prod : Vec α (k + 1) := (Prod.mk v.1 v.2 : Vec α (k + 1))
        let false_proof : ¬∃ (idx : ℕ₁), get prod idx = a := by
          simp
          intro new_h
          apply Or.elim new_h
          . intro a_eq_v1
            exact h2 (Eq.symm a_eq_v1)
          . intro exists_v2
            exact h1 exists_v2
        simp at false_proof
        exact (isFalse false_proof)
      | isTrue h1, _ =>
        exact isTrue (Or.intro_right (a = v.fst) h1)
      | _, isTrue h2 => 
        exact isTrue (Or.intro_left (∃ idx, get v.snd idx = a) (Eq.symm h2))
end Vec

class SubVec (as sub_as: Vec α n) where
  subVec : a ∈ sub_as → a ∈ as