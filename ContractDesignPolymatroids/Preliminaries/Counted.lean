-- stamp r1 2026-11-03
import Mathlib

/-!
# Operation counts: the cost model

The paper counts the work of its algorithms in submodular minimizations, evaluations of `f`
outside the minimizations, and further arithmetic operations (for example `lem:ray` and
`thm:waterfilling`, `stoc-sections/appB-quadratic.tex:122-182`). This file gives a model of these
counts in which the counts of an algorithm are proved from a program that performs it, from the
modelling choices listed at the end ("What the model trusts").

* `Cost` is the triple of these numbers: arithmetic operations (comparisons included),
  submodular minimizations, and evaluations of `f`.
* `Counted α` is a value together with the cost of computing it, and `m >>=ᶜ k` runs `m` and then
  `k` on its value, adding the costs.
* The primitives: `ops k a` (`k` arithmetic operations or comparisons that produce `a`),
  `minimize T` (one minimization, which returns the set `T` it is given), `evalF v` (one
  evaluation of `f`, with the value `v`), and the operations on sets of elements with one
  operation per element: `sum` (one addition per term), `inf'` and `max0` (one comparison per
  term), `filterEq` (one comparison per element) and `sdiff` (one membership test per element).

A counted algorithm is written as a program from these primitives that performs the steps of the
paper's algorithm. Its value is proved equal to the library's definition of the algorithm, so the
cost is the cost of the algorithm whose correctness the library proves, and the counts are bounded
from the program's structure. Not in the paper: the paper counts operations in prose.

What the model trusts. The counts are proved from modelling choices made at each call, which a
reader checks there:
* `ops k a` (and `filterL`, `filterK` of `CountedSort` and `CountedLists`) charges the number `k`
  that the caller gives, for any value `a`; each call states in its docstring why `k` operations
  compute `a`.
* `evalF v` is applied to a value of `f`, and `minimize T` to the set the minimization returns:
  the maximal minimizer in `lem:ray` (`ContractDesignPolymatroids/BestResponse/WaterFilling.lean`, proved), some
  minimizer in `lem:ellipsoid` (`ContractDesignPolymatroids/Convex/Ellipsoid.lean`).
* A comparison of two numbers has three outcomes (`<`, `=`, `>`). A set of elements is held as an
  indicator array over `E`, so a membership test or an insertion is one operation.
* Bookkeeping on lists and sets is not counted: splitting and joining lists, forming the pairs of
  a list, going through the elements of a set, writing an entry of a vector. In the programs of
  this library it is bounded by the counted work, so no order of a count changes.
-/

namespace Stoc

/-- The cost of a computation: arithmetic operations (comparisons included), submodular
minimizations, and evaluations of `f` outside the minimizations. -/
abbrev Cost := ℕ × ℕ × ℕ

/-- A value together with the cost of computing it. -/
structure Counted (α : Type*) where
  /-- The value. -/
  val : α
  /-- The cost of computing it. -/
  cost : Cost

namespace Counted

universe u v

/-- A value at no cost. -/
def ret {α : Type u} (a : α) : Counted α := ⟨a, 0⟩

/-- Sequencing: the costs add. -/
def bind {α : Type u} {β : Type v} (m : Counted α) (k : α → Counted β) : Counted β :=
  ⟨(k m.val).val, m.cost + (k m.val).cost⟩

/-- `m >>=ᶜ k`: run `m`, then `k` on its value. -/
infixl:55 " >>=ᶜ " => Counted.bind

@[simp] lemma val_bind {α : Type u} {β : Type v} (m : Counted α) (k : α → Counted β) :
    (m >>=ᶜ k).val = (k m.val).val := rfl

@[simp] lemma cost_bind {α : Type u} {β : Type v} (m : Counted α) (k : α → Counted β) :
    (m >>=ᶜ k).cost = m.cost + (k m.val).cost := rfl

@[simp] lemma val_ret {α : Type u} (a : α) : (ret a).val = a := rfl

@[simp] lemma cost_ret {α : Type u} (a : α) : (ret a).cost = 0 := rfl

variable {α : Type u}

/-- `k` arithmetic operations or comparisons that produce `a`. -/
def ops (k : ℕ) (a : α) : Counted α := ⟨a, (k, 0, 0)⟩

@[simp] lemma val_ops (k : ℕ) (a : α) : (ops k a).val = a := rfl

@[simp] lemma cost_ops (k : ℕ) (a : α) : (ops k a).cost = (k, 0, 0) := rfl

/-- One submodular minimization; the oracle returns `T`. That `T` is the set the minimization
returns (the maximal minimizer, or some minimizer) is the caller's to prove. -/
def minimize {E : Type u} (T : Finset E) : Counted (Finset E) := ⟨T, (0, 1, 0)⟩

@[simp] lemma val_minimize {E : Type u} (T : Finset E) : (minimize T).val = T := rfl

@[simp] lemma cost_minimize {E : Type u} (T : Finset E) : (minimize T).cost = (0, 1, 0) := rfl

/-- One evaluation of `f`, with the value `v`. -/
def evalF (v : ℝ) : Counted ℝ := ⟨v, (0, 0, 1)⟩

@[simp] lemma val_evalF (v : ℝ) : (evalF v).val = v := rfl

@[simp] lemma cost_evalF (v : ℝ) : (evalF v).cost = (0, 0, 1) := rfl

variable {E : Type v}

/-- The sum over `s` of terms that cost `g e` each, with one addition per term. -/
noncomputable def sum (s : Finset E) (g : E → Counted ℝ) : Counted ℝ :=
  ⟨∑ e ∈ s, (g e).val, ∑ e ∈ s, (g e).cost + (s.card, 0, 0)⟩

@[simp] lemma val_sum (s : Finset E) (g : E → Counted ℝ) :
    (sum s g).val = ∑ e ∈ s, (g e).val := rfl

@[simp] lemma cost_sum (s : Finset E) (g : E → Counted ℝ) :
    (sum s g).cost = ∑ e ∈ s, (g e).cost + (s.card, 0, 0) := rfl

/-- The minimum over a nonempty `s` of terms that cost `g e` each, with one comparison per
term. -/
noncomputable def inf' (s : Finset E) (h : s.Nonempty) (g : E → Counted ℝ) : Counted ℝ :=
  ⟨s.inf' h fun e => (g e).val, ∑ e ∈ s, (g e).cost + (s.card, 0, 0)⟩

@[simp] lemma val_inf' (s : Finset E) (h : s.Nonempty) (g : E → Counted ℝ) :
    (inf' s h g).val = s.inf' h fun e => (g e).val := rfl

@[simp] lemma cost_inf' (s : Finset E) (h : s.Nonempty) (g : E → Counted ℝ) :
    (inf' s h g).cost = ∑ e ∈ s, (g e).cost + (s.card, 0, 0) := rfl

/-- `A \ B`: one membership test for each element of `A` (`B` held as an indicator array). -/
def sdiff [DecidableEq E] (A B : Finset E) : Counted (Finset E) := ⟨A \ B, (A.card, 0, 0)⟩

@[simp] lemma val_sdiff [DecidableEq E] (A B : Finset E) : (sdiff A B).val = A \ B := rfl

@[simp] lemma cost_sdiff [DecidableEq E] (A B : Finset E) :
    (sdiff A B).cost = (A.card, 0, 0) := rfl

/-- The maximum of `0` and of terms over `s` that cost `g e` each: one comparison per term and
one with `0`. -/
noncomputable def max0 (s : Finset E) (g : E → Counted ℝ) : Counted ℝ :=
  ⟨(insert 0 (s.image fun e => (g e).val)).max' (Finset.insert_nonempty _ _),
    ∑ e ∈ s, (g e).cost + (s.card + 1, 0, 0)⟩

@[simp] lemma val_max0 (s : Finset E) (g : E → Counted ℝ) :
    (max0 s g).val = (insert 0 (s.image fun e => (g e).val)).max' (Finset.insert_nonempty _ _) :=
  rfl

@[simp] lemma cost_max0 (s : Finset E) (g : E → Counted ℝ) :
    (max0 s g).cost = ∑ e ∈ s, (g e).cost + (s.card + 1, 0, 0) := rfl

/-- The elements of `s` whose term, which costs `g e`, equals `c`: one comparison per element. -/
noncomputable def filterEq (s : Finset E) (g : E → Counted ℝ) (c : ℝ) : Counted (Finset E) :=
  ⟨s.filter fun e => (g e).val = c, ∑ e ∈ s, (g e).cost + (s.card, 0, 0)⟩

@[simp] lemma val_filterEq (s : Finset E) (g : E → Counted ℝ) (c : ℝ) :
    (filterEq s g c).val = s.filter fun e => (g e).val = c := rfl

@[simp] lemma cost_filterEq (s : Finset E) (g : E → Counted ℝ) (c : ℝ) :
    (filterEq s g c).cost = ∑ e ∈ s, (g e).cost + (s.card, 0, 0) := rfl

end Counted

end Stoc
