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

class Quandle (α : Type _) extends Rack α where
  fix : ∀ {x : α}, act x x = x