import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

open Classical

@[ext]
structure Graph (V : Type _) (E : Type _) where
  inc : Bool → E → Finset V
  well_def : ∀ i e, 2 ≤ (inc i e).card → ∃ (u v : V), u ≠ v ∧ ∀ j, inc j e = ({u,v} : Finset V)