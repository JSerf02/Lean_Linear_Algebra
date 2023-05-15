import LinearAlgebra.Natural

/-
  Here is an implementation of Vectors as a dependent type
  of the Prod datatype, the equivalent of Pi's Pair type.

  This implementaiton has the following advantages:
  
  (1) It is a natural definition from a mathematical perspective,
      as it directly implements the definition of Tuples as nested
      ordered pairs (see https://en.wikipedia.org/wiki/Tuple).

  (2) It does not separate its length from its element, requiring
      every proof that properly constructs elements to necessarily
      also ensure the proper length. Thus, proofs with Vecs only
      require constructing the proper elements and do not include
      additional steps reasoning about length.
  
  (3) It allows for easy construction of Vecs using tuple notation.
      - Ex: (1, 2, 3) : Vec ℝ 3 
        - Lean sometimes gets confused about types though, so you
          may need to write this as (1, 2, (3 : ℝ)) : Vec ℝ 3
-/

@[simp]
def Vec (α : Type u) (n : ℕ₁) :=
  match n with 
  | 1     => α 
  | k + 1 => α × (Vec α k)

infix:50 "^" => Vec -- αllows you to write Vec 𝔽 n as 𝔽^n

/- Vecs are just tuples -/
def Tuple := Vec

namespace Vec

  /- The essential theorems and definitions for interacting with a Vec -/
  section VecBasic
    /- The following 2 theorems are the backend for all of pattern matching -/
    @[simp]
    theorem Vec_one_eq_F (α : Type u) : Vec α 1 = α := by simp

    @[simp]
    theorem Vec_succ_k_eq_Prod : Vec 𝔽 (k + 1) = (𝔽 × (Vec 𝔽 k)) := by simp

    @[simp]
    def pair_eq (v : Vec α (n + 1)) : ⟨v.fst, v.snd⟩ = v := by 
      simp at v
      simp

    /- The remaining theorems and definitions allow for creating, reading, and modifying Vecs -/
    @[simp]
    def get (v : Vec α n) (idx : ℕ₁) : α := by
      match n, idx with
      | 1    , _     =>
        simp at v
        exact v
      | k + 1, 1     =>
        simp at v
        exact v.1
      | k + 1, i + 1 =>
        simp at v
        exact get v.2 i
    -- Notice how the first element in the Vec is at index 1
    
    @[simp]
    def head (v : Vec α n) : α := get v 1

    @[simp]
    def tail (v : Vec α (n + 1)) : Vec α n := v.2

  end VecBasic
  
  /- Funcional programming functions for iterating over Vecs -/
  section VecFunctional

    /- Applys a function f to every element in a Vec v-/
    @[simp]
    def map (f : α → β) (v : Vec α n) : Vec β n :=
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
    theorem map_id (v : Vec α n) : map (fun x => x) v = v := by
      match n with
      | 1     => simp
      | k + 1 => 
        simp
        let prev_eq := map_id v.2
        simp[prev_eq]
      
    /- Tells Lean to simplify nested calls of map whenever possible -/
    @[simp]
    theorem map_comp_is_map (f : α → β) (g : β → γ) (v : Vec α n) : 
      map g (map f v) = map (fun a => g (f a)) v := by
        match n with
        | 1     => simp
        | _ + 1 =>
          simp
          exact map_comp_is_map f g v.2
    
    /- Performs entrywise application of every function in fs on every element in vs -/
    @[simp]
    def apply (fs : Vec (α → β) n) (v : Vec α n) : Vec β n :=
      match n with
      | 1     => fs v
      | _ + 1 => ⟨fs.1 v.1, apply fs.2 v.2⟩ 
    
    /- The remaining apply proofs attempt to simplify nested apply and map calls 
       to a generalized simplest form. As you will later see, many functions use
       apply and map in conjunction with each toher, so these proofs will trivialize
       many future examples.
       
       The simplest form is defined as follows:
       - Nested apply calls must be on the left input of the parent apply
       - Map calls must always happen before apply calls
       - Map calls nested under apply calls must be on the left input of the apply 
       - Nested map calls should simplify to a single map call (theorem proven above)
       - Each nested apply call should have a different Vec as its rightmost input
      
       Here's an example of nested apply and map calls in simplist form
       apply (apply (map f u) v) w)
    -/
    @[simp]
    theorem map_passes_through_apply (f : β → γ) (u : Vec (α → β) n) (v : Vec α n) :
      map f (apply u v) = apply (map (fun a_to_b a => f (a_to_b a)) u) v := by
        match n with
        | 1     => simp
        | _ + 1 =>
          simp
          exact map_passes_through_apply f u.2 v.2

    @[simp]
    theorem apply_on_left (u : Vec (β → γ) n) (v : Vec (α → β) n) (w : Vec α n) :
      apply u (apply v w) = apply (apply (map (fun b_to_c a_to_b a => b_to_c (a_to_b a)) u) v) w := by
        match n with
        | 1     => simp
        | _ + 1 =>
          simp
          exact apply_on_left u.2 v.2 w.2
    
    @[simp]
    theorem apply_map_on_left (f : α → β) (u : Vec (β → γ) n) (v : Vec α n) :
      apply u (map f v) = apply (map (fun b_to_c a => b_to_c (f a)) u) v := by
        match n with
        | 1     => simp
        | _ + 1 =>
          simp
          exact apply_map_on_left f u.2 v.2
    
    @[simp]
    theorem apply_compress (fs : Vec (α → α → β) n) (v : Vec α n) :
      apply (apply fs v) v = apply (map (fun f a => f a a) fs) v := by
        match n with
        | 1     => simp
        | _ + 1 =>
          simp
          exact apply_compress fs.2 v.2
    
    @[simp]
    theorem apply_map_compress (f : α → α → β) (v : Vec α n) :
      apply (map f v) v = map (fun a => f a a) v := by
        match n with
        | 1     => simp
        | _ + 1 =>
          simp 
          exact apply_map_compress f v.2

    theorem apply_swap (u : Vec α n) (v : Vec β n) (fs : Vec (α → β → γ) n) :
      apply (apply fs u) v = apply (apply (map (fun f b a => f a b) fs) v) u := by
        match n with
        | 1 => simp
        | _ + 1 => 
          simp
          exact apply_swap u.2 v.2 fs.2
    
    /- Applies a 2-argument function on each pair of corresponding elements from 2 Vecs -/
    def zip_with {n : ℕ₁} (f : α → β → γ) (u : Vec α n) (v : Vec β n) : Vec γ n :=
      apply (map f u) v
    
    /- The next 2 definitions accumulate all of the elements in a Vec with 
       an accumulation function-/
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
    
    /- Creates a Vec of n of the same element -/
    @[simp]
    def replicate (a : α) (n : ℕ₁) : Vec α n := 
      match n with
      | 1     => a
      | k + 1 => ⟨a, replicate a k⟩ 
    
    theorem replicate_id (a : α) (v : Vec β n) :
      map (fun _ => a) v = replicate a n  := by
        match n with
        | 1     => simp
        | _ + 1 => 
          simp
          exact replicate_id a v.2
    
    @[simp]
    theorem zip_with_replicate_eq_map (f : α → β → γ) (a : α) (v : Vec β n) :
      zip_with f (replicate a n) v = map (f a) v := by
        match n with
        | 1 => simp[zip_with]
        | k + 1 =>
          simp[zip_with]
          exact zip_with_replicate_eq_map f a v.2




  end VecFunctional

  /- The following proofs allow you to capitalize on the prior functional definitions
     to trivialize many proofs.
     
     The main goal of this section is to make properties of operations on a type α 
     seamlessly transfer to entrywise versions of those operations on a Vec α n. -/
  section EntrywiseOperations
    /- Converts a Vec of propositions into a single proposition-/
    def PropVec_to_Prop (v : Vec Prop n) : Prop :=
      foldr (. ∧ .) True v
    
    /- Reduces PropVec_to_Prop to True when possible
       - Unfortunately, there is no way to generalize this for a function of n variables
         so only proofs for common numbers of variables are supplied here. -/
    @[simp]
    theorem true_vec_0 (f : α → Prop) (v : Vec α n) : 
      (∀ a, f a) → PropVec_to_Prop (map f v) := by
        intro h
        match n with
        | 1     => 
          simp[PropVec_to_Prop]
          exact h v
        | _ + 1 =>
          simp[PropVec_to_Prop]
          have next := h v.1
          have prev := true_vec_0 f v.2 h
          simp[PropVec_to_Prop] at prev
          exact ⟨next, prev⟩ 
    
    @[simp]
    theorem true_vec_1 (f : α → β → Prop) (u : Vec α n) (v : Vec β n) : 
      (∀ a b, f a b) → PropVec_to_Prop (apply (map f u) v) := by
        intro h
        match n with
        | 1     => 
          simp[PropVec_to_Prop]
          exact h u v
        | _ + 1 =>
          simp[PropVec_to_Prop]
          have next := h u.1 v.1
          have prev := true_vec_1 f u.2 v.2 h
          simp[PropVec_to_Prop] at prev
          exact ⟨next, prev⟩ 
    
    @[simp]
    theorem true_vec_2 (f : α → β → γ → Prop) (u : Vec α n) (v : Vec β n) (w : Vec γ n) : 
      (∀ a b c, f a b c) → PropVec_to_Prop (apply (apply (map f u) v) w) := by
        intro h
        match n with
        | 1     => 
          simp[PropVec_to_Prop]
          exact h u v w
        | _ + 1 =>
          simp[PropVec_to_Prop]
          have next := h u.1 v.1 w.1
          have prev := true_vec_2 f u.2 v.2 w.2 h
          simp[PropVec_to_Prop] at prev
          exact ⟨next, prev⟩ 
    
    @[simp]
    theorem true_vec_3 (f : α → β → γ → ω → Prop) (v₁ : Vec α n) (v₂ : Vec β n) (v₃ : Vec γ n) (v₄ : Vec ω n): 
      (∀ a b c d, f a b c d) → PropVec_to_Prop (apply (apply (apply (map f v₁) v₂) v₃) v₄) := by
        intro h
        match n with
        | 1     => 
          simp[PropVec_to_Prop]
          exact h v₁ v₂ v₃ v₄
        | _ + 1 =>
          simp[PropVec_to_Prop]
          have next := h v₁.1 v₂.1 v₃.1 v₄.1
          have prev := true_vec_3 f v₁.2 v₂.2 v₃.2 v₄.2 h
          simp[PropVec_to_Prop] at prev
          exact ⟨next, prev⟩ 
    
    @[simp]
    theorem true_vec_4 (f : α₁ → α₂ → α₃ → α₄ → α₅ → Prop) (v₁ : Vec α₁ n) (v₂ : Vec α₂ n) (v₃ : Vec α₃ n) (v₄ : Vec α₄ n) (v₅ : Vec α₅ n): 
      (∀ a₁ a₂ a₃ a₄ a₅, f a₁ a₂ a₃ a₄ a₅) → PropVec_to_Prop (apply (apply (apply (apply (map f v₁) v₂) v₃) v₄) v₅) := by
        intro h
        match n with
        | 1     => 
          simp[PropVec_to_Prop]
          exact h v₁ v₂ v₃ v₄ v₅
        | _ + 1 =>
          simp[PropVec_to_Prop]
          have next := h v₁.1 v₂.1 v₃.1 v₄.1 v₅.1
          have prev := true_vec_4 f v₁.2 v₂.2 v₃.2 v₄.2 v₅.2 h
          simp[PropVec_to_Prop] at prev
          exact ⟨next, prev⟩ 
    
    /- The following theorems allow for quick reduction of common True cases that 
       appear when working with map and zip_with-/
    @[simp]
      def PropVec_map_id (v : Vec α n) : PropVec_to_Prop (map (fun _ => True) v) := 
        match n with
        | 1 => by simp[PropVec_to_Prop]
        | _ + 1 => by
          simp[PropVec_to_Prop]
          exact PropVec_map_id v.2

      @[simp]
      def PropVec_apply_id (u v : Vec α n) : 
        PropVec_to_Prop ((apply (map  (fun _ _ => True) u)) v) :=
          match n with
          | 1 => by simp[PropVec_to_Prop]
          | _ + 1 => by
            simp[PropVec_to_Prop]
            exact PropVec_apply_id u.2 v.2
      
      @[simp]
      def PropVec_zip_with_id (u v : Vec α n) : 
        PropVec_to_Prop (zip_with (fun _ _ => True) u v) := by
          match n with
          | 1 => simp[zip_with, PropVec_to_Prop]
          | _ + 1 =>
            simp[zip_with, PropVec_to_Prop]
            exact PropVec_zip_with_id u.2 v.2

      /- Reduces equality of Vecs to entrywise equality -/
      theorem entrywise_eq_l (u v : Vec α n) :
        u = v → PropVec_to_Prop (zip_with Eq u v) := by
          match n with
          | 1     => 
            simp[PropVec_to_Prop, zip_with]
            intro u_eq_v
            exact u_eq_v
          | _ + 1 => 
            simp[PropVec_to_Prop, zip_with]
            intro h
            have next : u.fst = v.fst := by simp[h]
            have prev := entrywise_eq_l u.2 v.2
            have u2_eq_v2 : u.2 = v.2 := by simp[h]
            exact ⟨next, prev u2_eq_v2⟩ 

      theorem entrywise_eq_r (u v : Vec α n) :
        PropVec_to_Prop (zip_with Eq u v) → u = v := by
          match n with
          | 1     => 
            simp[PropVec_to_Prop, zip_with]
            intro u_eq_v
            exact u_eq_v
          | _ + 1 => 
            simp[PropVec_to_Prop, zip_with]
            intro h
            have u1_eq_v1 := h.left
            have prev_input := h.right
            have u2_eq_v2 := entrywise_eq_r u.2 v.2 prev_input
            have u_eq_v : (u.1, u.2) = (v.1, v.2) := by 
              simp[u1_eq_v1, u2_eq_v2]
            exact u_eq_v

      theorem entrywise_eq (u v : Vec α n) :
        u = v ↔ PropVec_to_Prop (zip_with Eq u v)  := 
          Iff.intro (entrywise_eq_l u v) (entrywise_eq_r u v)
      
      /- Generalized proofs for a variety of simple examples -/
      @[simp]
      theorem prop_passes_through_Vec_1 {p : α → Prop} (v : Vec α n) (proof: ∀ a, p a) : 
        PropVec_to_Prop (map p v) := by
        match n with
        | 1     => 
          simp[PropVec_to_Prop]
          exact proof v
        | _ + 1 => 
          simp[PropVec_to_Prop, proof v.1]
          exact (prop_passes_through_Vec_1 v.2 proof)

      @[simp]
      theorem prop_passes_through_Vec_2 {p : α → β → Prop} (u : Vec α n) (v : Vec β n) (proof : ∀ a b, p a b) :
        PropVec_to_Prop (zip_with p u v) := by
          match n with
          | 1 => 
            simp[PropVec_to_Prop]
            exact proof u v
          | _ + 1 =>
            simp[PropVec_to_Prop, zip_with, proof u.1 v.1]
            exact prop_passes_through_Vec_2 u.2 v.2 proof

      @[simp]
      theorem prop_passes_through_Vec_3 {p : α → β → γ → Prop} (u : Vec α n) (v : Vec β n) (w : Vec γ n)  (proof : ∀ a b c, p a b c) :
        PropVec_to_Prop (apply (zip_with p u v) w) := by
          match n with
          | 1 => 
            simp[PropVec_to_Prop] 
            exact proof u v w
          | _ + 1 =>
            simp[PropVec_to_Prop, zip_with, proof u.1 v.1 w.1]
            exact prop_passes_through_Vec_3 u.2 v.2 w.2 proof
      
      /- Uses the prior tools to simplify common cases for entrywise operations -/
      @[simp]
      theorem zip_with_comm (f g : α → α → β) (h : β → β → γ) (u v : Vec α n) :
        zip_with h (zip_with f u v) (zip_with g v u) = zip_with (fun x y => h (f x y) (g y x)) u v := by
          simp[zip_with, entrywise_eq, apply_swap]

      @[simp]
      theorem zip_with_assoc_l (f : α → α → α) (g : α → α → β)  (u v w : Vec α n) : 
        zip_with g (zip_with f (zip_with f u v) w) (zip_with f u (zip_with f v w))
        = apply (apply (map (fun a₁ a₂ a₃ => g (f (f a₁ a₂) a₃) (f a₁ (f a₂ a₃))) u) v) w := by 
          simp[zip_with]
          simp[apply_swap w u]
          simp[apply_swap w v]
          simp[apply_swap v u]

      @[simp]
      theorem zip_with_assoc_r (f : α → α → α) (g : α → α → β) (u v w : Vec α n) :
        zip_with g (zip_with f u (zip_with f v w)) (zip_with f (zip_with f u v) w)
        = apply (apply (map (fun a₁ a₂ a₃ => g (f a₁ (f a₂ a₃)) (f (f a₁ a₂) a₃)) u) v) w := by
          simp[zip_with]
          simp[apply_swap v w]
          simp[apply_swap v u]
          simp[apply_swap w u]
          simp[apply_swap w v]
      
      #print zip_with_assoc_r
  end EntrywiseOperations
end Vec