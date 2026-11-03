-- stamp r1 2026-11-03
import ContractDesignPolymatroids.Preliminaries.Counted

/-!
# Operation counts: lists and merge sort

Not in the paper. The proof of `lem:A-lineartime` (`stoc-sections/appA-proofs.tex:180-181`) counts
`O(n log n)` time for the greedy construction of one share, the sort of the elements by their
coefficients, without naming a sorting method. This file proves such a count for merge sort in the
cost model of `Stoc.Counted`, and adds two primitives on lists.

* `filterL l k p`: the elements of the list `l` that satisfy `p`, with `k` comparisons for each
  element; `mapL l g`: a counted step `g a` for each element `a` of `l`, in order, the costs
  added (`cost_mapL_ops`).
* `mergeC le w xs ys` merges two lists with the comparison `le`, at `w` operations for each
  comparison: it returns Lean's `List.merge xs ys le` (`mergeC_val`) with at most
  `w(|xs| + |ys|)` operations (`mergeC_cost`).
* `msortC le w l` sorts `l` by merge sort: it splits `l` into its first `⌈|l|/2⌉` elements and the
  rest, sorts both halves and merges them. It returns Lean's `List.mergeSort l le` (`msortC_val`),
  which is a permutation of `l` (`List.mergeSort_perm`) and sorted if `le` is transitive and total
  (`List.pairwise_mergeSort`), with no minimizations or evaluations of `f` and at most
  `w · n⌈log₂ n⌉` operations, `n = |l|` (`msortC_cost`).
-/

namespace Stoc

namespace Counted

universe u v

/-! ### Primitives on lists -/

section Lists

variable {α : Type u} {β : Type v}

/-- The elements of the list `l` that satisfy `p`, with `k` comparisons for each element. -/
def filterL (l : List α) (k : ℕ) (p : α → Bool) : Counted (List α) :=
  ⟨l.filter p, (k * l.length, 0, 0)⟩

@[simp] lemma val_filterL (l : List α) (k : ℕ) (p : α → Bool) :
    (filterL l k p).val = l.filter p := rfl

@[simp] lemma cost_filterL (l : List α) (k : ℕ) (p : α → Bool) :
    (filterL l k p).cost = (k * l.length, 0, 0) := rfl

/-- A counted step `g a` for each element `a` of the list `l`, in order: the list of the values,
at the sum of the costs. -/
def mapL (l : List α) (g : α → Counted β) : Counted (List β) :=
  ⟨l.map fun a => (g a).val, (l.map fun a => (g a).cost).sum⟩

@[simp] lemma val_mapL (l : List α) (g : α → Counted β) :
    (mapL l g).val = l.map fun a => (g a).val := rfl

@[simp] lemma cost_mapL (l : List α) (g : α → Counted β) :
    (mapL l g).cost = (l.map fun a => (g a).cost).sum := rfl

/-- `k` operations for each element: `k|l|` in all. -/
lemma cost_mapL_ops (l : List α) (k : ℕ) (g : α → β) :
    (mapL l fun a => ops k (g a)).cost = (k * l.length, 0, 0) := by
  simp only [cost_mapL, cost_ops, List.map_const', List.sum_replicate, Prod.smul_mk, smul_eq_mul,
    mul_zero, Nat.mul_comm]

end Lists

/-! ### Merge sort -/

section MergeSort

variable {α : Type u} (le : α → α → Bool) (w : ℕ)

/-- Merging the lists `xs` and `ys` with the comparison `le`, at `w` operations for each
comparison: the smaller of the two first elements comes first, ties to `xs`. -/
def mergeC : List α → List α → Counted (List α)
  | [], ys => ret ys
  | x :: xs, [] => ret (x :: xs)
  | x :: xs, y :: ys =>
      ops w (le x y) >>=ᶜ fun b =>
      if b then mergeC xs (y :: ys) >>=ᶜ fun r => ret (x :: r)
      else mergeC (x :: xs) ys >>=ᶜ fun r => ret (y :: r)
termination_by xs ys => xs.length + ys.length

/-- Merge sort of the list `l` with the comparison `le`, at `w` operations for each comparison:
the first `⌈|l|/2⌉` elements and the rest are sorted, and the two sorted lists merged. -/
def msortC : List α → Counted (List α)
  | [] => ret []
  | [a] => ret [a]
  | a :: b :: xs =>
      msortC ((a :: b :: xs).take (((a :: b :: xs).length + 1) / 2)) >>=ᶜ fun s₁ =>
      msortC ((a :: b :: xs).drop (((a :: b :: xs).length + 1) / 2)) >>=ᶜ fun s₂ =>
      mergeC le w s₁ s₂
termination_by l => l.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop, List.length_cons]; omega

/-- The counted merge returns Lean's merge (not in the paper). -/
theorem mergeC_val : ∀ xs ys : List α, (mergeC le w xs ys).val = xs.merge ys le
  | [], ys => by simp [mergeC]
  | x :: xs, [] => by simp [mergeC]
  | x :: xs, y :: ys => by
      rw [mergeC, List.cons_merge_cons]
      cases h : le x y
      · simp only [val_bind, val_ops, Bool.false_eq_true, ite_false, val_ret,
          mergeC_val (x :: xs) ys]
      · simp only [val_bind, val_ops, ite_true, val_ret, mergeC_val xs (y :: ys)]
termination_by xs ys => xs.length + ys.length

/-- The counted merge makes no minimizations or evaluations of `f` and at most `|xs| + |ys|`
comparisons, `w(|xs| + |ys|)` operations (not in the paper). -/
theorem mergeC_cost : ∀ xs ys : List α,
    (mergeC le w xs ys).cost.2 = 0 ∧ (mergeC le w xs ys).cost.1 ≤ w * (xs.length + ys.length)
  | [], ys => by simp [mergeC]
  | x :: xs, [] => by simp [mergeC]
  | x :: xs, y :: ys => by
      rw [mergeC]
      cases h : le x y
      · obtain ⟨h2, h1⟩ := mergeC_cost (x :: xs) ys
        simp only [cost_bind, val_ops, cost_ops, Bool.false_eq_true, ite_false, cost_ret,
          add_zero, Prod.snd_add, h2, Prod.fst_add, List.length_cons] at h1 ⊢
        refine ⟨rfl, ?_⟩
        nlinarith
      · obtain ⟨h2, h1⟩ := mergeC_cost xs (y :: ys)
        simp only [cost_bind, val_ops, cost_ops, ite_true, cost_ret, add_zero, Prod.snd_add, h2,
          Prod.fst_add, List.length_cons] at h1 ⊢
        refine ⟨rfl, ?_⟩
        nlinarith
termination_by xs ys => xs.length + ys.length

/-- The counted merge sort returns Lean's merge sort, a permutation of `l`
(`List.mergeSort_perm`) that is sorted if `le` is transitive and total
(`List.pairwise_mergeSort`) (not in the paper). -/
theorem msortC_val : ∀ l : List α, (msortC le w l).val = l.mergeSort le
  | [] => by simp [msortC]
  | [a] => by simp [msortC]
  | a :: b :: xs => by
      rw [msortC, List.mergeSort]
      simp only [val_bind, mergeC_val,
        msortC_val ((a :: b :: xs).take (((a :: b :: xs).length + 1) / 2)),
        msortC_val ((a :: b :: xs).drop (((a :: b :: xs).length + 1) / 2)),
        List.MergeSort.Internal.splitInTwo_fst, List.MergeSort.Internal.splitInTwo_snd]
termination_by l => l.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop, List.length_cons]; omega

/-- The recursion of the count of merge sort (not in the paper): for `n ≥ 2`, `p = ⌈n/2⌉` and
`q = n − p ≤ p`, `⌈log₂ n⌉ = ⌈log₂ p⌉ + 1`, so the halves, at most `w p⌈log₂ p⌉` and
`w q⌈log₂ q⌉` operations, and the merge, at most `w(p + q)`, take at most `w n⌈log₂ n⌉`. -/
lemma msortC_count_step (w : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    w * ((n + 1) / 2 * Nat.clog 2 ((n + 1) / 2)) +
        w * ((n - (n + 1) / 2) * Nat.clog 2 (n - (n + 1) / 2)) +
        w * ((n + 1) / 2 + (n - (n + 1) / 2)) ≤ w * (n * Nat.clog 2 n) := by
  have hlog : Nat.clog 2 n = Nat.clog 2 ((n + 1) / 2) + 1 := by
    rw [Nat.clog_of_two_le (by norm_num) hn, show n + 2 - 1 = n + 1 by omega]
  have hq : Nat.clog 2 (n - (n + 1) / 2) ≤ Nat.clog 2 ((n + 1) / 2) :=
    Nat.clog_mono_right 2 (by omega)
  rw [hlog]
  generalize hP : (n + 1) / 2 = P at hq ⊢
  obtain ⟨q, rfl⟩ : ∃ q, n = P + q := ⟨n - P, by omega⟩
  rw [Nat.add_sub_cancel_left] at hq ⊢
  have h1 := Nat.mul_le_mul_left w (Nat.mul_le_mul_left q hq)
  calc w * (P * Nat.clog 2 P) + w * (q * Nat.clog 2 q) + w * (P + q)
      ≤ w * (P * Nat.clog 2 P) + w * (q * Nat.clog 2 P) + w * (P + q) := by omega
    _ = w * ((P + q) * (Nat.clog 2 P + 1)) := by ring

/-- The counted merge sort makes no minimizations or evaluations of `f` and at most `n⌈log₂ n⌉`
comparisons, `w · n⌈log₂ n⌉` operations, `n = |l|` (`msortC_count_step`; not in the paper: the
proof of `lem:A-lineartime` counts `O(n log n)` for the sort). -/
theorem msortC_cost : ∀ l : List α,
    (msortC le w l).cost.2 = 0 ∧ (msortC le w l).cost.1 ≤ w * (l.length * Nat.clog 2 l.length)
  | [] => by simp [msortC]
  | [a] => by simp [msortC]
  | a :: b :: xs => by
      have hn : 2 ≤ (a :: b :: xs).length := by simp
      have hp : ((a :: b :: xs).length + 1) / 2 ≤ (a :: b :: xs).length := by omega
      obtain ⟨h₁, h₁'⟩ := msortC_cost ((a :: b :: xs).take (((a :: b :: xs).length + 1) / 2))
      obtain ⟨h₂, h₂'⟩ := msortC_cost ((a :: b :: xs).drop (((a :: b :: xs).length + 1) / 2))
      obtain ⟨hm, hm'⟩ := mergeC_cost le w
        (msortC le w ((a :: b :: xs).take (((a :: b :: xs).length + 1) / 2))).val
        (msortC le w ((a :: b :: xs).drop (((a :: b :: xs).length + 1) / 2))).val
      have hlen₁ : (msortC le w ((a :: b :: xs).take
          (((a :: b :: xs).length + 1) / 2))).val.length = ((a :: b :: xs).length + 1) / 2 := by
        rw [msortC_val, List.length_mergeSort, List.length_take, Nat.min_eq_left hp]
      have hlen₂ : (msortC le w ((a :: b :: xs).drop
          (((a :: b :: xs).length + 1) / 2))).val.length =
          (a :: b :: xs).length - ((a :: b :: xs).length + 1) / 2 := by
        rw [msortC_val, List.length_mergeSort, List.length_drop]
      rw [hlen₁, hlen₂] at hm'
      simp only [List.length_take, List.length_drop, Nat.min_eq_left hp] at h₁' h₂'
      rw [msortC]
      simp only [cost_bind, Prod.snd_add, Prod.fst_add, h₁, h₂, hm, add_zero, true_and]
      have := msortC_count_step w hn
      omega
termination_by l => l.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop, List.length_cons]; omega

end MergeSort

end Counted

end Stoc
