import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

open Classical

/-- Graph is a general structure that admits simple graphs, digraphs, multigraphs, and other degenerate
    flavors as instances. The `inc` constructor takes a boolean value, an edge, and returns a vertex that
    is the head or tail of that edge. -/
@[ext]
structure Graph (V : Type _) (E : Type _) where
  inc : Bool → E → Finset V
  well_def : ∀ i e, 2 ≤ (inc i e).card → ∃ (u v : V), u ≠ v ∧ ∀ j, inc j e = ({u,v} : Finset V)

namespace Graph

variable {V E : Type _} {G : Graph V E} {e f : E} {u v w : V}

def undir (G : Graph V E) (e : E) : Prop :=
  ∃ (S : Finset V), ∀ i, G.inc i e = S

def loop (G : Graph V E) (e : E) : Prop :=
  ∃ u, ∀ i, G.inc i e = {u} 

def free (G : Graph V E) (e : E) : Prop :=
  ∀ i, G.inc i e = ∅

def half_edge (G : Graph V E) (e : E) : Prop :=
  ∃ i u, G.inc i e = {u} ∧ G.inc (!i) e = ∅

def edge_between (G : Graph V E) (e : E) (v₁ v₂ : V) : Prop :=
  ∀ i, G.inc i e = {v₁,v₂}

class PairGraph (G : Graph V (V × V)) where
  h_pair' : ∀ e, G.free e ∨ G.edge_between e e.1 e.2

class LooplessPairGraph (G : Graph V (V × V)) extends PairGraph G where
  no_loops : ∀ e, ¬G.loop e

class UndirectedPairGraph (G : Graph V (V × V)) extends PairGraph G where
  bi_dir : ∀ (e₀ : V × V), ∃ e₁, G.edge_between e₁ e₀.2 e₀.1

class SimplePairGraph (G : Graph V (V × V)) extends PairGraph G, UndirectedPairGraph G

/-
def complement (G : PairGraph) :=
-/