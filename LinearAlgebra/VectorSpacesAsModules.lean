import Mathlib.Logic.Nontrivial
import Mathlib.Logic.Basic
import Mathlib.Init.ZeroOne
import Mathlib.Init.Data.Int.Basic
import Mathlib.Init.Algebra.Order
import Std.Data.Rat
import Mathlib.Tactic.Convert
import Mathlib.Data.Rat.Init

/-!
Math:

* Algebra:
  An algebra is a system A = [P, F] in which

    (i) P = {Sᵢ} is a family of nonempty sets Sᵢ of different types of
    elements, each called a phylum of the algebra A. The phyla are
    indexed by some set I.
    
    (ii) F = {fₐ} is a set of finitary operations, where each fₐ is a map
        fₐ : Sᵢ₍₁,ₐ₎ × ⋯ × Sᵢ₍ₙ₍ₐ₎,ₐ₎ → Sᵣ₍ₐ₎,
      where n(a) is a nonnegative integer, iₐ : k ↦ i(k,a) is a map from
      {1, ⋯ , n} to I, and r(a) ∈ I. The operations fₐ are indexed by some
      set Ω.
  
  A heterogeneous algebra is an algebra with more than one phylum.

  A homogeneous algebra is an algebra with exactly one phylum.

* Magma:
  A magma is a set M with a binary operation ⬝ : M × M → M. Magmas are used to
  define semigroups.

  An additive magma is a magma for which we think of the binary operation,
  denote +, as addition in some sense.

  A magma with zero is a magma M for which there exists an element 0 ∈ M such
  that 0 ⬝ x = 0 = x ⬝ 0 for all x ∈ M.

  A unital magma is a magma M with an element 1 ∈ M such that 1 ⬝ x = x = x ⬝ 1
  for all x ∈ M.

  An additive unital magma is a unital magma for which we think of the binary
  operation, denoted +, as addition in some sense.

* Semigroup:
  Semigroups are associative magmas. Semigroups are used to define monoids.

  A semigroup is a set S with a binary operation ⬝ : S × S → S such that
    (a ⬝ b) ⬝ c = a ⬝ (b ⬝ c)
  for all a, b, c ∈ S.

  An additive semigroup is a semigroup where we think of the binary
  operation, denoted +, as addition in some sense.

  A commutative semigroup is a semigroup such that
    a ⬝ b = b ⬝ a
  for all a, b ∈ S.

  An additive, commutative semigroup is an additive semigroup such that
    a + b = b + a
  for all a, b ∈ S.

* Monoid
  A monoid is a unital semigroup. Monoids are used to define groups.

  A monoid is a set M with a binary operation ⬝ : M × M → M such that the
  following hold:

  (i) We have
    (a ⬝ b) ⬝ c = a ⬝ (b ⬝ c)
  for all a, b, c ∈ M

  (ii) There exists e ∈ M such that e ⬝ a = a = a ⬝ e for all a ∈ M.
  
  An additive monoid is a monoid in which we think of the binary operation,
  denoted +, as addition in some sense.

  A commutative monoid is a monoid such that a ⬝ b = b ⬝ a for all a, b ∈ M.

  An additive commutative monoid is a commutative monoid in which we think of
  the binary operation, denoted +, as addition in some sense.

* Group
  A group is a semigroup with inverses.

* Semiring
  A semiring is a ring without inverses.

* Ring
  A ring is an abelian group under addition, a monoid under multiplication
  and has distributive laws.

* Field
  Fields generalize groups to things we are used to working with, e.g. ℚ and ℝ.

* Vector Space
  A vector space is an additive commutative group under addition acted upon by a
  field.
-/

open Function


section HelpfulTypeclasses

universe u

/-- `Inv` is the typeclass for types with an inversion operation. -/
@[to_additive, notation_class]
class Inv (I : Type u) where
  /-- Invert an element of α. -/
  inv : I → I

@[inherit_doc]
postfix:max "⁻¹" => Inv.inv

/-- `Distrib` is the typeclass for types with addition and multiplication operations
      for which multiplication distributes over addition. -/
class Distrib (D : Type _) extends Mul D, Add D where
  protected left_distrib : ∀ a b c : D, a * (b + c) = a * b + a * c
  protected right_distrib : ∀ a b c : D, (a + b) * c = a * c + b * c

end HelpfulTypeclasses


section Algebra

/-- `HVAdd` is the notation typeclass for heterogeneous addition. This is
      used to define a heterogeneous algebra with finitary operation `+ᵥ`. -/
class HVAdd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hAdd : α → β → γ

/-- `HSMul` is the notation typeclass for heterogeneous scalar multiplication.
      This enables the notation `a • b : γ`, where `a : α` and `b : β`, and
      is used to define a heterogeneous algebra with a finitary operation `•`. -/
class HSMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hSMul : α → β → γ

attribute [notation_class smul Simps.copySecond] HSMul
attribute [notation_class nsmul Simps.nsmulArgs] HSMul
attribute [notation_class zsmul Simps.zsmulArgs] HSMul

/-- `VAdd` is the typeclass for the `+ᵥ` notation. -/
class VAdd (G : Type _) (P : Type _) where
  vadd : G → P → P

/-- `SMul` is the typeclass for types with a scalar multiplication
      operation `•`. -/
@[to_additive (attr := ext)]
class SMul (S : Type _) (α : Type _) where
  smul : S → α → α

infixr:73 " • " => HSMul.hSMul

attribute [to_additive existing] Mul Div HMul instHMul HDiv instHDiv HSMul
attribute [to_additive (reorder := 1 2) SMul] Pow
attribute [to_additive (reorder := 1 2)] HPow
attribute [to_additive existing (reorder := 1 2, 5 6) hSMul] HPow.hPow
attribute [to_additive existing (reorder := 1 2, 5 6) smul] Pow.pow

@[to_additive (attr := default_instance)]
instance instHSMul [SMul α β] : HSMul α β β where
  hSMul := SMul.smul

attribute [to_additive existing (reorder := 1 2)] instHPow

end Algebra


section Magma

/-- `MulOneClass` is the typeclass for unital magmas. -/
class MulOneClass (M : Type u) extends One M, Mul M where
  one_mul : ∀ a : M, 1 * a = a
  mul_one : ∀ a : M, a * 1 = a 

/-- `AddZeroClass` is the typeclass for additive, unital magmas. -/
class AddZeroClass (M : Type u) extends Zero M, Add M where
  zero_add : ∀ a : M, 0 + a = a
  add_zero : ∀ a : M, a + 0 = a

attribute [to_additive] MulOneClass


section MulOneClass

/- Note: Missing @[ext] lemma -/

variable {M : Type u} [MulOneClass M]

@[to_additive (attr := simp)]
theorem one_mul : ∀ a : M, 1 * a = a :=
  MulOneClass.one_mul

@[to_additive (attr := simp)]
theorem mul_one : ∀ a : M, a * 1 = a :=
  MulOneClass.mul_one

end MulOneClass


/-- `MulZeroClass` is the typeclass for magmas with a zero. -/
class MulZeroClass (M : Type u) extends Mul M, Zero M where
  zero_mul : ∀ a : M, 0 * a = 0
  mul_zero : ∀ a : M, a * 0 = 0

/-- `MulZeroOneClass` is the typeclass for unital magmas (nonassociative monoids)
      with zeros. -/
class MulZeroOneClass (M : Type u) extends MulZeroClass M, MulOneClass M

end Magma


section Semigroup

/-- `Semigroup` is the typeclass for semigroups. -/
@[ext]
class Semigroup (S : Type u) extends Mul S where
  mul_assoc : ∀ a b c : S, a * b * c = a * (b * c)

/-- `AddSemigroup` is the typeclass for additive semigroups. -/
@[ext]
class AddSemigroup (S : Type u) extends Add S where
  add_assoc : ∀ a b c : S, a + b + c = a + (b + c)

attribute [to_additive] Semigroup


section

variable [Semigroup S]

@[to_additive]
theorem mul_assoc : ∀ a b c : S, a * b * c = a * (b * c) :=
  Semigroup.mul_assoc

end


/-- `CommSemigroup` is the typeclass for commutative semigroups. -/
@[ext]
class CommSemigroup (S : Type u) extends Semigroup S where
  mul_comm : ∀ a b : S, a * b = b * a

/-- `AddCommSemigroup` is the typeclass for commutative additive semigroups. -/
@[ext]
class AddCommSemigroup (S : Type u) extends AddSemigroup S where
  add_comm : ∀ a b : S, a + b = b + a

attribute [to_additive] CommSemigroup

/-- `SemigroupWithZero` is the typeclass for semigroups with zero. -/
class SemigroupWithZero (G : Type u) extends Semigroup G, MulZeroClass G

end Semigroup


section NaturalNumberOperations

variable {M : Type U}

/-- `npowRec` is the fundamental power operation in a monoid. -/
def npowRec [One M] [Mul M] : ℕ → M → M
  | 0, _ => 1
  | n + 1, a => a * npowRec n a

/-- `nsmulRec` is the fundamental scalar multiplication in an
      additive monoid. -/
def nsmulRec [Zero M] [Add M] : ℕ → M → M
  | 0, _ => 0
  | n + 1, a => a + nsmulRec n a

attribute [to_additive existing] npowRec

end NaturalNumberOperations


section Monoid

/-- `AddMonoid` is the typeclass for additive monoids. -/
class AddMonoid (M : Type u) extends AddSemigroup M, AddZeroClass M where
  nsmul : ℕ → M → M := nsmulRec
  nsmul_zero : ∀ x, nsmul 0 x = 0 := by intros; rfl
  nsmul_succ : ∀ (n : ℕ) (x), nsmul (n + 1) x = x + nsmul n x := by intros; rfl

/-- `Monoid` is the typeclass for monoids. -/
@[to_additive]
class Monoid (M : Type u) extends Semigroup M, MulOneClass M where
  npow : ℕ → M → M := npowRec
  npow_zero : ∀ x, npow 0 x = 1 := by intros; rfl
  npow_succ : ∀ (n : ℕ) (x), npow (n + 1) x = x * npow n x := by intros; rfl

attribute [to_additive existing] Monoid.toMulOneClass

@[default_instance high]
instance Monoid.Pow {M : Type _} [Monoid M] : Pow M ℕ :=
  ⟨fun x n ↦ Monoid.npow n x⟩

instance AddMonoid.SMul {M : Type _} [AddMonoid M] : SMul ℕ M :=
  ⟨AddMonoid.nsmul⟩

attribute [to_additive existing SMul] Monoid.Pow


section

variable {M : Type _} [Monoid M]

@[to_additive (attr := simp) nsmul_eq_smul]
theorem npow_eq_pow (n : ℕ) (x : M) : Monoid.npow n x = x ^ n :=
  rfl

@[to_additive zero_nsmul, simp]
theorem pow_zero (a : M) : a ^ 0 = 1 :=
  Monoid.npow_zero _

@[to_additive succ_nsmul]
theorem pow_succ (a : M) (n : ℕ) : a ^ (n + 1) = a * a ^ n :=
  Monoid.npow_succ n a

end


section

variable {M : Type u} [Monoid M]

@[to_additive]
theorem left_inv_eq_right_inv {a b c : M} (hba : b * a = 1 ) (hac : a * c = 1) : b = c := by
  rw [← one_mul c, ← hba, mul_assoc, hac, mul_one b]

end

/-- `AddCommMonoid` is the typeclass for additive commutative monoids. -/
class AddCommMonoid (M : Type u) extends AddMonoid M, AddCommSemigroup M

/-- `CommMonoid` is the typeclass for commutative monoids. -/
@[to_additive]
class CommMonoid (M : Type u) extends Monoid M, CommSemigroup M

attribute [to_additive existing] CommMonoid.toCommSemigroup


section Integer_Operations

/-- `zpowRec` is the fundamental scalar multiplication in a group. -/
def zpowRec {M : Type _} [One M] [Mul M] [Inv M] : ℤ → M → M
  | Int.ofNat n, a => npowRec n a
  | Int.negSucc n, a => (npowRec n.succ a)⁻¹

/-- `zsmulRec` is the fundamental scalar multiplication in an additive group. -/
def zsmulRec {M : Type _} [Zero M] [Add M] [Neg M] : ℤ → M → M
  /- Multiplication by a nonnegative integer is just applying `nsmulRec`. -/
  | Int.ofNat n, a => nsmulRec n a
  /- Multiplication by a negative integer n is the negation of `nsmulRec` applied
      to -n. -/
  | Int.negSucc n, a => -nsmulRec n.succ a

attribute [to_additive existing] zpowRec

end Integer_Operations


/--
  `DivInvMonoid.div'` records what the default definition for `Div` would be,
  that is `a * b⁻¹`, in a class equipped with instances of both `Monoid` and
  `Inv`. This is provided as the default value for the `Div` instance
  in `DivInvMonoid`.

  `DivInvMonoid.div'` exists as a separate definition rather than
  inside `DivInvMonoid` so that the `Div` field of individual `DivInvMonoid`s
  constructed using that default value will not unfold at `.instance` transparency.
-/
def DivInvMonoid.div' {G : Type u} [Monoid G] [Inv G] (a b : G) : G :=
  a * b⁻¹

/--
  `DivInvMonoid` is the typeclass for monoids with an inversion operation `⁻¹`
  and a division operation `/` satisfying `div_eq_mul_inv : ∀ a b, a / b = a * b⁻¹`. 
  (The existence of an inversion operation `⁻¹` does not imply that `⁻¹` is an
  involutive inversion operation, for which it is true that `a⁻¹⁻¹ = a`.)

  The default for `div` is such that `a / b = a * b⁻¹` holds by definition.
-/
class DivInvMonoid (G : Type u) extends Monoid G, Inv G, Div G where
  div := DivInvMonoid.div'
  div_eq_mul_inv : ∀ a b : G, a / b = a * b⁻¹ := by intros; rfl
  zpow : ℤ → G → G := zpowRec
  zpow_zero' : ∀ a : G, zpow 0 a = 1 := by intros; rfl
  zpow_succ' (n : ℕ) (a : G) : zpow (Int.ofNat n.succ) a = a * zpow (Int.ofNat n) a := by
    intros; rfl
  zpow_neg' (n : ℕ) (a : G) : zpow (Int.negSucc n) a = (zpow n.succ a)⁻¹ := by
    intros; rfl

/--
  `SubNegMonoid.sub'` records what the default definition for `Sub` would be, that
  is `a + -b`, in a class equipped with instances of both `AddMonoid` and `Neg`.
  
  `SubNegMonoid.sub'` exists as a separate definition rather than
  inside `SubNegMonoid` so that the `Sub` field of individual `SubNegMonoid`s
  constructed using that default value will not unfold at `.instance` transparency.
-/
def SubNegMonoid.sub' {G : Type u} [AddMonoid G] [Neg G] (a b : G) : G :=
  a + -b

attribute [to_additive existing SubNegMonoid.sub'] DivInvMonoid.div'

/--
  `SubNegMonoid` is the typeclass for additive monoids with a unary and binary `-`
  operations satisfying `sub_eq_add_neg : ∀ a b : G, a - b = a + -b`.

  The default for `sub` is such that `a - b = a + -b` holds by definition.
-/
class SubNegMonoid (G : Type u) extends AddMonoid G, Neg G, Sub G where
  sub := SubNegMonoid.sub'
  sub_eq_add_neg : ∀ a b : G, a - b = a + -b := by intros; rfl
  zsmul : ℤ → G → G := zsmulRec
  zsmul_zero' : ∀ a : G, zsmul 0 a = 0 := by intros; rfl
  zsmul_succ' (n : ℕ) (a : G) : zsmul (Int.ofNat n.succ) a = a + zsmul (Int.ofNat n) a := by
    intros; rfl
  zsmul_neg' (n : ℕ) (a : G) : zsmul (Int.negSucc n) a = -zsmul n.succ a := by
    intros; rfl

attribute [to_additive SubNegMonoid] DivInvMonoid

instance DivInvMonoid.Pow {M} [DivInvMonoid M] : Pow M ℤ :=
  ⟨fun x n ↦ DivInvMonoid.zpow n x⟩

instance SubNegMonoid.SMulInt {M} [SubNegMonoid M] : SMul ℤ M :=
  ⟨SubNegMonoid.zsmul⟩

attribute [to_additive existing SubNegMonoid.SMulInt] DivInvMonoid.Pow

/-- `MonoidWithZero` is the typeclass for monoids with zero -/
class MonoidWithZero (M : Type u) extends Monoid M, MulZeroClass M, SemigroupWithZero M


section

protected def Nat.unaryCast {R : Type u} [One R] [Zero R] [Add R] : ℕ → R
  | 0 => 0
  | n + 1 => Nat.unaryCast n + 1

/-- `AddMonoidWithOne` is the typeclass for an additive monoid with a `1`. -/
class AddMonoidWithOne (R : Type u) extends NatCast R, AddMonoid R, One R where
  natCast := Nat.unaryCast
  natCast_zero : natCast 0 = 0 := by intros; rfl
  natCast_succ : ∀ n, natCast (n + 1) = natCast n + 1 := by intros; rfl

/-- `AddCommMonoidWithOne` is the typeclass for additive monoids `R` with a `1` for
    which `a + b = b + a` for all `a, b : R`. -/
class AddCommMonoidWithOne (R : Type _) extends AddMonoidWithOne R, AddCommMonoid R

end


section MultiplicativeActionByMonoid

/-- `MulAction` is the typeclass for multiplicative actions by monoids. -/
class MulAction (α : Type _) (β : Type _) [Monoid α] extends SMul α β where
  protected one_smul : ∀ b : β, (1 : α) • b = b
  mul_smul : ∀ (x y : α) (b : β), (x * y) • b = x • y • b

/-- `DistribMulAction` is the typeclass for multiplicative actions by a monoid on
      an additive monoid. -/
class DistribMulAction (M A : Type _) [Monoid M] [AddMonoid A] extends MulAction M A where
  smul_zero : ∀ a : M, a • (0 : A)= 0
  smul_add : ∀ (a : M) (x y : A), a • (x + y) = a • x + a • y


section

variable {R M : Type _} [MonoidWithZero R] [Zero M]

variable (R M)

/-- `MulActionWithZero` is the typeclass for multiplicative actions by a monoid
      with zero `R` on a Type with zero `M`, compatible with zero in both `R` and
      `M`. -/
class MulActionWithZero extends MulAction R M where
  smul_zero : ∀ r : R, r • (0 : M) = 0
  zero_smul : ∀ m : M, (0 : R) • m = 0

end


end MultiplicativeActionByMonoid


end Monoid


section Group

/-- `Group` is the typeclass for groups. -/
class Group (G : Type u) extends DivInvMonoid G where
  mul_left_inv : ∀ a : G, a⁻¹ * a = 1

/-- `AddGroup` is the typeclass for additive groups. -/
class AddGroup (A : Type u) extends SubNegMonoid A where
  add_left_neg : ∀ a : A, -a + a = 0

/-- `AddCommGroup` is the typeclass for additive commutative groups. -/
class AddCommGroup (G : Type u) extends AddGroup G, AddCommMonoid G

/-- `CommGroup` is the typeclass for commutative groups. -/
@[to_additive]
class CommGroup (G : Type u) extends Group G, CommMonoid G


section AddGroupWithOne

universe u

protected def Int.castDef {R : Type u} [NatCast R] [Neg R] : ℤ → R
  | (n : ℕ) => n
  | Int.negSucc n => -(n + 1 : ℕ)

/-- `AddGroupWithOne` is the typeclass for additive groups with a `1`. -/
class AddGroupWithOne (R : Type u) extends IntCast R, AddMonoidWithOne R, AddGroup R where
  intCast := Int.castDef
  intCast_ofNat : ∀ n : ℕ, intCast (n : ℕ) = Nat.cast n := by intros; rfl
  intCast_negSucc : ∀ n : ℕ, intCast (Int.negSucc n) = - Nat.cast (n + 1) := by intros; rfl

/-- `AddCommGroupWithOne` is the typeclass for additive commutative groups with a `1`. -/
class AddCommGroupWithOne (R : Type u) extends AddCommGroup R, AddGroupWithOne R, AddCommMonoidWithOne R

end AddGroupWithOne


end Group


section Semiring

class NonUnitalNonAssocSemiring (α : Type u) extends AddCommMonoid α, Distrib α, MulZeroClass α

class NonUnitalSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, SemigroupWithZero α

class NonAssocSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, MulZeroOneClass α, AddCommMonoidWithOne α

class Semiring (α : Type u) extends NonUnitalSemiring α, NonAssocSemiring α, MonoidWithZero α

class CommSemiring (R : Type u) extends Semiring R, CommMonoid R

end Semiring


section Ring

class Ring (R : Type u) extends Semiring R, AddCommGroup R, AddGroupWithOne R

class CommRing (R : Type u) extends Ring R, CommMonoid R


section

open Set

variable {D : Type _}

def Rat.castRec [NatCast D] [IntCast D] [Mul D] [Inv D] : ℚ → D
  | ⟨a, b, _, _⟩ => ↑a * (↑b)⁻¹

def qsmulRec (coe : ℚ → D) [Mul D] (a : ℚ) (x : D) : D :=
  coe a * x

class DivisionRing (D : Type u) extends Ring D, DivInvMonoid D, Nontrivial D, RatCast D where
  protected mul_inv_cancel : ∀ (a : D), a ≠ 0 → a * a⁻¹ = 1
  protected inv_zero : (0 : D)⁻¹ = 0
  protected ratCast := Rat.castRec
  protected ratCast_mk : ∀ (a : ℤ) (b : ℕ) (h1 h2), Rat.cast ⟨a, b, h1, h2⟩ = a * (b : D)⁻¹ := by
    intros; rfl
  protected qsmul : ℚ → D → D := qsmulRec Rat.cast
  protected qsmul_eq_mul' : ∀ (a : ℚ) (x : D), qsmul a x = Rat.cast a * x := by
    intros; rfl

end


end Ring


section Field

universe u

class Field (K : Type u) extends CommRing K, DivisionRing K

end Field


section VectorSpace

universe u v

variable {F G : Type _}

class VectorSpace (F : Type u) (G : Type v) [Field F] [AddCommGroup G] extends DistribMulAction F G where
  protected add_smul : ∀ (r s : F) (x : G), (r + s) • x = r • x + s • x
  protected zero_smul : ∀ x : G, (0 : F) • x = 0


section 

variable [Field 𝔽] [AddCommGroup G] [VectorSpace 𝔽 G] (α β : 𝔽) (x y : G)

theorem add_smul : (α + β) • x = α • x + β • x :=
  VectorSpace.add_smul α β x

end

end VectorSpace


section IsLinear

universe w

variable {F : Type _} {G₁ : Type _} {G₂ : Type _}

class IsLinearMap (F : Type u) (G₁ G₂ : Type _) [Field F]
  [AddCommGroup G₁] [AddCommGroup G₂] [VectorSpace F G₁] [VectorSpace F G₂]
  (f : G₁ → G₂) : Prop where
  map_add : ∀ x y, f (x + y) = f x + f y
  map_smul : ∀ (α : F) (x), f (α • x) = α • f x

end IsLinear