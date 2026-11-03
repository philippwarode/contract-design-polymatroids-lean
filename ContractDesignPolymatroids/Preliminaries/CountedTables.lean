-- stamp r1 2026-11-03
import ContractDesignPolymatroids.Preliminaries.Counted

/-!
# Operation counts: sums, filters and tables

The results in the bit model `thm:polybits`, `lem:sizes` and `thm:gadget` claim polynomial time,
which the formalization reads as polynomially many arithmetic operations on numbers whose encoding
lengths are polynomial (`stoc-sections/01-introduction.tex:31`: "Some running-time bounds in the
paper follow from the formalized results by a standard bit-complexity analysis"). Their counted
programs compute with integers and with rationals (as real numbers), with tables of numbers, and
with subsets. This file adds to the cost model of `Stoc.Counted` the primitives they use:

* `sumM s g`: the sum over `s` of terms that cost `g e` each, in any commutative monoid (such as
  the integers of `thm:polybits`), with one addition per term (`Counted.sum` is the sum of real
  numbers);
* `filterT s p`: the elements of `s` that satisfy `p`, with one comparison or membership test per
  element;
* `tabulate s g b`: the table of the values of `g` on `s`, each computed at its cost (and `b`
  outside `s`, where nothing is computed), and `table g` on all elements of a finite type;
* `supC s h g`: the maximum over a nonempty `s` of terms that cost `g e` each, with one comparison
  per term (`Counted.inf'` is the minimum of real numbers).

Not in the paper: the paper counts in prose.
-/

namespace Stoc

namespace Counted

universe u v

variable {E : Type v}

/-- The sum over `s` of terms that cost `g e` each, in a commutative monoid `M`, with one addition
per term. -/
def sumM {M : Type u} [AddCommMonoid M] (s : Finset E) (g : E → Counted M) : Counted M :=
  ⟨∑ e ∈ s, (g e).val, ∑ e ∈ s, (g e).cost + (s.card, 0, 0)⟩

@[simp] lemma val_sumM {M : Type u} [AddCommMonoid M] (s : Finset E) (g : E → Counted M) :
    (sumM s g).val = ∑ e ∈ s, (g e).val := rfl

@[simp] lemma cost_sumM {M : Type u} [AddCommMonoid M] (s : Finset E) (g : E → Counted M) :
    (sumM s g).cost = ∑ e ∈ s, (g e).cost + (s.card, 0, 0) := rfl

/-- The elements of `s` that satisfy `p`: one comparison or membership test per element. -/
def filterT (s : Finset E) (p : E → Prop) [DecidablePred p] : Counted (Finset E) :=
  ⟨s.filter p, (s.card, 0, 0)⟩

@[simp] lemma val_filterT (s : Finset E) (p : E → Prop) [DecidablePred p] :
    (filterT s p).val = s.filter p := rfl

@[simp] lemma cost_filterT (s : Finset E) (p : E → Prop) [DecidablePred p] :
    (filterT s p).cost = (s.card, 0, 0) := rfl

/-- The table of the values of `g` on `s`, each computed at its cost; outside `s` the table holds
`b`, and nothing is computed there. -/
def tabulate {β : Type u} [DecidableEq E] (s : Finset E) (g : E → Counted β) (b : β) :
    Counted (E → β) :=
  ⟨fun e => if e ∈ s then (g e).val else b, ∑ e ∈ s, (g e).cost⟩

@[simp] lemma val_tabulate {β : Type u} [DecidableEq E] (s : Finset E) (g : E → Counted β)
    (b : β) : (tabulate s g b).val = fun e => if e ∈ s then (g e).val else b := rfl

@[simp] lemma cost_tabulate {β : Type u} [DecidableEq E] (s : Finset E) (g : E → Counted β)
    (b : β) : (tabulate s g b).cost = ∑ e ∈ s, (g e).cost := rfl

/-- The table of the values of `g` on all elements of a finite type, each computed at its cost. -/
def table {β : Type u} [Fintype E] (g : E → Counted β) : Counted (E → β) :=
  ⟨fun e => (g e).val, ∑ e, (g e).cost⟩

@[simp] lemma val_table {β : Type u} [Fintype E] (g : E → Counted β) :
    (table g).val = fun e => (g e).val := rfl

@[simp] lemma cost_table {β : Type u} [Fintype E] (g : E → Counted β) :
    (table g).cost = ∑ e, (g e).cost := rfl

/-- The maximum over a nonempty `s` of terms that cost `g e` each, with one comparison per term. -/
def supC {α : Type u} [SemilatticeSup α] (s : Finset E) (h : s.Nonempty) (g : E → Counted α) :
    Counted α :=
  ⟨s.sup' h fun e => (g e).val, ∑ e ∈ s, (g e).cost + (s.card, 0, 0)⟩

@[simp] lemma val_supC {α : Type u} [SemilatticeSup α] (s : Finset E) (h : s.Nonempty)
    (g : E → Counted α) : (supC s h g).val = s.sup' h fun e => (g e).val := rfl

@[simp] lemma cost_supC {α : Type u} [SemilatticeSup α] (s : Finset E) (h : s.Nonempty)
    (g : E → Counted α) : (supC s h g).cost = ∑ e ∈ s, (g e).cost + (s.card, 0, 0) := rfl

end Counted

end Stoc
