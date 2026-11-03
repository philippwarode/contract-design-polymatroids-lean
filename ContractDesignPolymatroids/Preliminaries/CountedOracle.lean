-- stamp r1 2026-11-03
import ContractDesignPolymatroids.Preliminaries.CountedLists

/-!
# Operation counts: queries of the cost oracle

`lem:ellipsoid` and `thm:convexfptas` (`stoc-sections/appF-convex.tex:121-145`,
`08c-convex.tex:13-18`) count, besides submodular minimizations and arithmetic operations, the
calls of "a cost oracle that returns `c(x)` and a subgradient `g(x)`" (08c-convex.tex:13): "We use
the exact real-arithmetic model of `sec:convex`, counting submodular minimizations, exact calls of
the oracle for `c`, and arithmetic operations and comparisons, including square roots"
(appF-convex.tex:121). This file extends the cost model of `Stoc.Counted`
(`ContractDesignPolymatroids/Preliminaries/Counted.lean`) by this fourth count.

* `CountedQ α` is a value together with a `Cost` (arithmetic operations, submodular minimizations,
  evaluations of `f`) and the number of queries of the cost oracle made in computing it;
  `m >>=ᵠ k` runs `m` and then `k` on its value, adding the costs and the queries.
* `lift` runs a program of `Stoc.Counted`, which makes no query, and `query` is one query.
* `Counted.vec` (`ContractDesignPolymatroids/Preliminaries/CountedLists.lean`), a vector with one entry for each element
  of the ground set, each entry with its own cost, gives the `n` evaluations `f({e})` and the `n`
  products.

Not in the paper: the paper counts in prose.
-/

namespace Stoc

/-- A value together with the cost of computing it and the number of queries of the cost oracle
made in computing it (not in the paper). -/
structure CountedQ (α : Type*) where
  /-- The value. -/
  val : α
  /-- The cost of computing it: arithmetic operations, submodular minimizations, evaluations of
  `f`. -/
  cost : Cost
  /-- The queries of the cost oracle made in computing it. -/
  queries : ℕ

namespace CountedQ

universe u v

/-- A value at no cost. -/
def ret {α : Type u} (a : α) : CountedQ α := ⟨a, 0, 0⟩

/-- Sequencing: the costs and the queries add. -/
def bind {α : Type u} {β : Type v} (m : CountedQ α) (k : α → CountedQ β) : CountedQ β :=
  ⟨(k m.val).val, m.cost + (k m.val).cost, m.queries + (k m.val).queries⟩

/-- `m >>=ᵠ k`: run `m`, then `k` on its value. -/
infixl:55 " >>=ᵠ " => CountedQ.bind

@[simp] lemma val_bind {α : Type u} {β : Type v} (m : CountedQ α) (k : α → CountedQ β) :
    (m >>=ᵠ k).val = (k m.val).val := rfl

@[simp] lemma cost_bind {α : Type u} {β : Type v} (m : CountedQ α) (k : α → CountedQ β) :
    (m >>=ᵠ k).cost = m.cost + (k m.val).cost := rfl

@[simp] lemma queries_bind {α : Type u} {β : Type v} (m : CountedQ α) (k : α → CountedQ β) :
    (m >>=ᵠ k).queries = m.queries + (k m.val).queries := rfl

@[simp] lemma val_ret {α : Type u} (a : α) : (ret a).val = a := rfl

@[simp] lemma cost_ret {α : Type u} (a : α) : (ret a).cost = 0 := rfl

@[simp] lemma queries_ret {α : Type u} (a : α) : (ret a).queries = 0 := rfl

variable {α : Type u}

/-- A program of `Stoc.Counted`, which makes no query of the cost oracle. -/
def lift (m : Counted α) : CountedQ α := ⟨m.val, m.cost, 0⟩

@[simp] lemma val_lift (m : Counted α) : (lift m).val = m.val := rfl

@[simp] lemma cost_lift (m : Counted α) : (lift m).cost = m.cost := rfl

@[simp] lemma queries_lift (m : Counted α) : (lift m).queries = 0 := rfl

/-- One query of the cost oracle, which returns `a`. -/
def query (a : α) : CountedQ α := ⟨a, 0, 1⟩

@[simp] lemma val_query (a : α) : (query a).val = a := rfl

@[simp] lemma cost_query (a : α) : (query a).cost = 0 := rfl

@[simp] lemma queries_query (a : α) : (query a).queries = 1 := rfl

end CountedQ

end Stoc
