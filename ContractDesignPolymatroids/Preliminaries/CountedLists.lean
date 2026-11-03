-- stamp r1 2026-11-03
import ContractDesignPolymatroids.Preliminaries.Counted

/-!
# Operation counts: primitives for lists, filters and minima

More primitives of the cost model of `Stoc.Counted`, for the counted affine continuation of
`lem:continuation` (`ContractDesignPolymatroids/OptimalShare/Continuation.lean`) and the counted enumeration of the
pieces of `thm:pieces` (`ContractDesignPolymatroids/OptimalShare/Tracing.lean`). Not in the paper: the paper counts in
prose.

* On sets of elements: `minWith` (the minimum of a value and of terms, one comparison per term and
  one with the value, the counterpart of `max0`), `filterK` (the elements that pass a test of `k`
  comparisons) and `vec` (a vector computed coordinate by coordinate; the costs add).
* On lists: `filterMapL` (terms computed one after another, the costs add, and the values that are
  `some` kept), `allL` (whether every term passes a test, one conjunction per term), `minL` and
  `maxL` (the minimum or the maximum of a value and the terms, one comparison per term), `insertL`
  (a term inserted into a list without duplicates, one comparison with each of its terms) and
  `dedupL` (the duplicates removed by inserting the terms one after another, at most
  `|l| · |dedup l|` comparisons, `dedupL_cost`), and `orderedInsertL` (a term inserted into a
  sorted list at its place, at most one comparison with each term).

The costs of a list of computations add componentwise (`fst_list_sum`, `snd_fst_list_sum`,
`snd_snd_list_sum`), and a bound on the terms bounds their sum (`sum_map_le_mul`).
-/

namespace Stoc

namespace Counted

universe u v

section Sets

variable {E : Type u}

/-- The minimum of `a` and of terms over `s` that cost `g e` each: one comparison per term and one
with `a` (the counterpart of `max0`). -/
noncomputable def minWith (a : ℝ) (s : Finset E) (g : E → Counted ℝ) : Counted ℝ :=
  ⟨(insert a (s.image fun e => (g e).val)).min' (Finset.insert_nonempty _ _),
    ∑ e ∈ s, (g e).cost + (s.card + 1, 0, 0)⟩

@[simp] lemma val_minWith (a : ℝ) (s : Finset E) (g : E → Counted ℝ) :
    (minWith a s g).val =
      (insert a (s.image fun e => (g e).val)).min' (Finset.insert_nonempty _ _) := rfl

@[simp] lemma cost_minWith (a : ℝ) (s : Finset E) (g : E → Counted ℝ) :
    (minWith a s g).cost = ∑ e ∈ s, (g e).cost + (s.card + 1, 0, 0) := rfl

/-- The elements of `s` that pass the test `P`, decided by `k` comparisons for each element. -/
def filterK (k : ℕ) (s : Finset E) (P : E → Prop) [DecidablePred P] : Counted (Finset E) :=
  ⟨s.filter P, (k * s.card, 0, 0)⟩

@[simp] lemma val_filterK (k : ℕ) (s : Finset E) (P : E → Prop) [DecidablePred P] :
    (filterK k s P).val = s.filter P := rfl

@[simp] lemma cost_filterK (k : ℕ) (s : Finset E) (P : E → Prop) [DecidablePred P] :
    (filterK k s P).cost = (k * s.card, 0, 0) := rfl

/-- A vector computed coordinate by coordinate, the coordinate `e` at the cost of `g e` (also the
`n` evaluations `f({e})` and the `n` products of the counted ellipsoid method,
`ContractDesignPolymatroids/Convex/Ellipsoid.lean`). -/
def vec {β : Type v} [Fintype E] (g : E → Counted β) : Counted (E → β) :=
  ⟨fun e => (g e).val, ∑ e, (g e).cost⟩

@[simp] lemma val_vec {β : Type v} [Fintype E] (g : E → Counted β) :
    (vec g).val = fun e => (g e).val := rfl

@[simp] lemma cost_vec {β : Type v} [Fintype E] (g : E → Counted β) :
    (vec g).cost = ∑ e, (g e).cost := rfl

end Sets

section Lists

variable {α : Type u} {β : Type v}

/-- The arithmetic operations of a list of computations: the sum of theirs. -/
lemma fst_list_sum (l : List α) (g : α → Cost) :
    ((l.map g).sum).1 = (l.map fun a => (g a).1).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- The minimizations of a list of computations: the sum of theirs. -/
lemma snd_fst_list_sum (l : List α) (g : α → Cost) :
    ((l.map g).sum).2.1 = (l.map fun a => (g a).2.1).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- The evaluations of `f` of a list of computations: the sum of theirs. -/
lemma snd_snd_list_sum (l : List α) (g : α → Cost) :
    ((l.map g).sum).2.2 = (l.map fun a => (g a).2.2).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- A bound on the terms bounds the sum of a list. -/
lemma sum_map_le_mul (l : List α) (g : α → ℕ) {B : ℕ} (h : ∀ a ∈ l, g a ≤ B) :
    (l.map g).sum ≤ l.length * B := by
  have := List.sum_le_length_nsmul (l.map g) B (by simpa using h)
  simpa using this

/-- The terms of `l` computed one after another by `g`, keeping the values that are `some`; the
costs add. -/
def filterMapL (g : α → Counted (Option β)) : List α → Counted (List β)
  | [] => ret []
  | a :: l => g a >>=ᶜ fun o => filterMapL g l >>=ᶜ fun r => ret (o.toList ++ r)

@[simp] lemma val_filterMapL (g : α → Counted (Option β)) (l : List α) :
    (filterMapL g l).val = l.filterMap fun a => (g a).val := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [filterMapL, val_bind, val_ret, ih, List.filterMap_cons]
    cases (g a).val <;> rfl

lemma cost_filterMapL (g : α → Counted (Option β)) (l : List α) :
    (filterMapL g l).cost = (l.map fun a => (g a).cost).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [filterMapL, ih]

/-- Whether every term of `l` passes the test `g`: the tests, and one conjunction per term. -/
def allL (g : α → Counted Bool) : List α → Counted Bool
  | [] => ret true
  | a :: l => g a >>=ᶜ fun b => allL g l >>=ᶜ fun r => ops 1 (b && r)

@[simp] lemma val_allL (g : α → Counted Bool) (l : List α) :
    (allL g l).val = l.all fun a => (g a).val := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [allL, ih]

lemma cost_allL (g : α → Counted Bool) (l : List α) :
    (allL g l).cost = (l.map fun a => (g a).cost + (1, 0, 0)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [allL, cost_bind, cost_ops, ih, List.map_cons, List.sum_cons]
    abel

/-- The minimum of `a` and the terms of `l`: one comparison per term. -/
noncomputable def minL (a : ℝ) (l : List ℝ) : Counted ℝ :=
  ⟨(insert a l.toFinset).min' (Finset.insert_nonempty _ _), (l.length, 0, 0)⟩

@[simp] lemma val_minL (a : ℝ) (l : List ℝ) :
    (minL a l).val = (insert a l.toFinset).min' (Finset.insert_nonempty _ _) := rfl

@[simp] lemma cost_minL (a : ℝ) (l : List ℝ) : (minL a l).cost = (l.length, 0, 0) := rfl

/-- The maximum of `a` and the terms of `l`: one comparison per term. -/
noncomputable def maxL (a : ℝ) (l : List ℝ) : Counted ℝ :=
  ⟨(insert a l.toFinset).max' (Finset.insert_nonempty _ _), (l.length, 0, 0)⟩

@[simp] lemma val_maxL (a : ℝ) (l : List ℝ) :
    (maxL a l).val = (insert a l.toFinset).max' (Finset.insert_nonempty _ _) := rfl

@[simp] lemma cost_maxL (a : ℝ) (l : List ℝ) : (maxL a l).cost = (l.length, 0, 0) := rfl

/-- `a` inserted into the list `l` unless it occurs in it: one comparison with each term (used on
lists of real numbers, where an equality test is one comparison). -/
def insertL [DecidableEq α] (a : α) (l : List α) : Counted (List α) := ops l.length (l.insert a)

/-- The duplicates of `l` removed, by inserting its terms one after another, from the last one
(`insertL`). -/
def dedupL [DecidableEq α] : List α → Counted (List α)
  | [] => ret []
  | a :: l => dedupL l >>=ᶜ fun r => insertL a r

@[simp] lemma val_dedupL [DecidableEq α] (l : List α) : (dedupL l).val = l.dedup := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [dedupL, insertL, val_bind, val_ops, ih]
    by_cases ha : a ∈ l
    · rw [List.dedup_cons_of_mem ha, List.insert_of_mem (List.mem_dedup.2 ha)]
    · rw [List.dedup_cons_of_notMem ha, List.insert_of_not_mem (mt List.mem_dedup.1 ha)]

/-- `dedupL` makes at most `|l| · |dedup l|` comparisons, and no minimization or evaluation. -/
lemma dedupL_cost [DecidableEq α] (l : List α) :
    (dedupL l).cost.2 = 0 ∧ (dedupL l).cost.1 ≤ l.length * l.dedup.length := by
  induction l with
  | nil => exact ⟨rfl, le_of_eq rfl⟩
  | cons a l ih =>
    simp only [dedupL, insertL, cost_bind, cost_ops, val_dedupL, Prod.snd_add, Prod.fst_add, ih.1,
      List.length_cons]
    refine ⟨rfl, ?_⟩
    have hle : l.dedup.length ≤ (a :: l).dedup.length := by
      by_cases ha : a ∈ l
      · rw [List.dedup_cons_of_mem ha]
      · rw [List.dedup_cons_of_notMem ha, List.length_cons]
        omega
    have := ih.2
    nlinarith

/-- `a` inserted into the list `l`, sorted for `r`, at its place: at most one comparison with each
term. -/
def orderedInsertL (r : α → α → Prop) [DecidableRel r] (a : α) (l : List α) :
    Counted (List α) :=
  ops l.length (l.orderedInsert r a)

@[simp] lemma val_orderedInsertL (r : α → α → Prop) [DecidableRel r] (a : α) (l : List α) :
    (orderedInsertL r a l).val = l.orderedInsert r a := rfl

@[simp] lemma cost_orderedInsertL (r : α → α → Prop) [DecidableRel r] (a : α) (l : List α) :
    (orderedInsertL r a l).cost = (l.length, 0, 0) := rfl

end Lists

end Counted

end Stoc
