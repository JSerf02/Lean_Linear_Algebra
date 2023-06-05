import Mathlib.Combinatorics.SimpleGraph.Init
import Mathlib.Order.CompleteLattice
import Mathlib.Order.GaloisConnection

macro (name := aesop_graph) "aesop_graph" c:Aesop.tactic_clause*: tactic =>
  `(tactic|
    aesop $c*
      (options := { introsTransparency? := some .default, terminal := true })
      (rule_sets [$(Lean.mkIdent `SimpleGraph):ident]))

@[ext]
structure SimpleGraph (V : Type u) where
  Adj : V → V → Prop
  symm : Symmetric Adj := by aesop_graph
  loopless : Irreflexive Adj := by aesop_graph

def completeGraph (V : Type u) : SimpleGraph V where Adj := Ne

def emptyGraph (V : Type u) : SimpleGraph V where Adj _ _ := False