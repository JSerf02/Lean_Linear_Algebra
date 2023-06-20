import Mathlib.Tactic.ScopedNS
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Hom.Equiv.Basic
import Mathlib.Algebra.Hom.Aut
import Mathlib.Data.ZMod.Defs

open MulOpposite

universe u v

class Shelf (α : Type u) where
  act : α → α → α
  self_distrib : ∀ {x y z : α}, act x (act y z) = act (act x y) (act x z)

@[ext]
structure ShelfHom (S₁ : Type _) (S₂ : Type _) [Shelf S₁] [Shelf S₂] where
  toFun : S₁ → S₂
  map_act' : ∀  {x y : S₁}, toFun (Shelf.act x y) = Shelf.act (toFun x) (toFun y)

class Rack (α : Type u) extends Shelf α where
  invAct : α → α → α
  left_inv : ∀ x, Function.LeftInverse (invAct x) (act x)
  right_inv : ∀ x, Function.RightInverse (invAct x) (act x)

scoped[Quandles] infixr:65 " ◃ " => Shelf.act
scoped[Quandles] infixr:65 " ◃⁻¹ " => Rack.invAct
scoped[Quandles] infixr:25 " →◃ " => ShelfHom

open Quandles

namespace Rack

variable {R : Type _} [Rack R]

def act' (x : R) : R ≃ R where
  toFun := Shelf.act x
  invFun := invAct x
  left_inv := left_inv x
  right_inv := right_inv x

@[simp]
theorem invAct_act_eq (x y : R) : x ◃⁻¹ x ◃ y = y :=
  left_inv x y

theorem left_cancel (x : R) {y y' : R} : x ◃ y = x ◃ y' ↔ y = y' := by
  constructor
  apply (act' x).injective
  rintro rfl
  rfl

theorem left_cancel_inv (x : R) {y y' : R} : x ◃⁻¹ y = x ◃⁻¹ y' ↔ y = y' := by
  constructor
  apply (act' x).symm.injective
  rintro rfl
  rfl

class Quandle (α : Type _) extends Rack α where
  fix : ∀ {x : α}, act x x = x

namespace Quandle

open Rack

@[reducible]
def Conj (G : Type _) := G

instance Conj.quandle (G : Type _) [Group G] : Quandle (Conj G) where
  act x := @MulAut.conj G _ x
  self_distrib := by
    intro x y z
    dsimp only [MulAut.conj_apply]
    simp [mul_assoc]
  invAct x := (@MulAut.conj G _ x).symm
  left_inv x y := by
    simp [act', mul_assoc]
  right_inv x y := by
    simp [act', mul_assoc]
  fix := by simp

@[simp]
theorem conj_act_eq_conj {G : Type _} [Group G] (x y : Conj G) :
    x ◃ y = ((x : G) * (y : G) * (x : G)⁻¹ : G) :=
  rfl

theorem conj_swap {G : Type _} [Group G] (x y : Conj G) : x ◃ y = y ↔ y ◃ x = x := by
  dsimp [Conj] at *; constructor
  repeat' intro h; conv_rhs => rw [eq_mul_inv_of_mul_eq (eq_mul_inv_of_mul_eq h)]; simp


def Conj.map {G : Type _} {H : Type _} [Group G] [Group H] (f : G →* H) : Conj G →◃ Conj H where
  toFun := f
  map_act' := by simp

def Dihedral (n : ℕ) := ZMod n

def dihedralAct (n : ℕ) (a : ZMod n) : ZMod n → ZMod n := fun b => 2 * a - b

end Quandle