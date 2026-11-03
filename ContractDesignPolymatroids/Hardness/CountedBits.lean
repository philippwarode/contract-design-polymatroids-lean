-- stamp r1 2026-11-03
import ContractDesignPolymatroids.Preliminaries.Counted
import ContractDesignPolymatroids.Hardness.Encoding

/-!
# Operation counts in the bit model: rational arithmetic, evaluations of `f`, maximum flows

The cost model of `Stoc.Counted` (`ContractDesignPolymatroids/Preliminaries/Counted.lean`) counts arithmetic operations
(comparisons included), submodular minimizations and evaluations of `f`. Its primitives `sum`,
`inf'`, `max0` and `filterEq` compute in `ℝ`. The bit model of Appendix C (`lem:exactbr`,
`thm:nphard`) computes in `ℚ`, on an instance given by its data (`RatInst`), and its minimizations
are maximum flows. This file extends the model for it (not in the paper: the paper counts in
prose).

In the bit model the three components of a cost read as follows. The first counts all arithmetic
operations, comparisons and membership tests, also those of the evaluations of `f`, which are
explicit sums of input numbers, but not those inside the maximum flows. The second counts the
maximum flows, which the paper cites. The third counts the evaluations of `f`, as the paper counts
them. (In the oracle model of the pilot, `rayC` and `waterFillC`, the second component counts
submodular minimizations, and the evaluations of `f` are oracle calls whose work is not in the
first component.)

* `Counted.sumQ`: a sum in `ℚ`, one addition per term; `Counted.filterC`: a filter with `k` tests
  per element; `Counted.allC`: whether all of some counted tests hold, one conjunction per test.
* `Counted.evalMark`: one evaluation of `f`, counted in the third component. In the bit model `f` is
  given by its cut form, and the program that evaluates it counts its arithmetic (`RatInst.fC`).
* `Counted.maxFlow`: one maximum flow, counted in the second component (cited): "the algorithm of
  Edmonds and Karp computes a maximum flow in polynomial time [Sch03, Thm. 10.5]", and the largest
  minimizer is "the set of nodes of `E` from which `s'` cannot be reached in the residual network
  [GGT89, §2.1–2.2]" (`stoc-sections/appD-hardness.tex:1849-1851`). The arithmetic operations of
  the flow algorithm itself are not in the first component; totals that include them take a bound
  on them as a hypothesis (`K N M²` on `N` nodes and `M` arcs, the bound `O(NM²)` of Edmonds and
  Karp's algorithm [Sch03, Thm. 10.5]; the paper's text says only "polynomial time"). The primitive
  stands for a maximum flow only if the capacities are nonnegative, as for instances of `𝒞_cut`.
* `RatInst.fC`: one evaluation of `f = cut_D + ω` at `S`, "each a sum of input numbers"
  (`lem:exactbr`(b), line 1856), with at most `3|D| + |E| + 1` arithmetic operations and
  membership tests (`fC_val`, `fC_cost`, `fC_cost_le`).
* `RatInst.flowC`: one maximum flow in the network `G_y` of `lem:exactbr`(b) (lines 1840-1851),
  with the arithmetic around it, `8|E| + 2|D| + 2` operations: the capacities of the arcs at the
  source and the sink, the product of the denominators of all capacities and the integer
  capacities, and the minimum of `cut_D + y` from the value of the flow (`flowC_val`,
  `flowC_cost`); the product of the denominators is at most `2` to the sum of the encoding lengths
  of the capacities (`denProd_le`).
* `RatInst.inCcutC`: the recognition of the inputs in the proof of membership in NP in
  `thm:nphard`, "The inputs are recognized in polynomial time by `lem:cutforms`(b)" (line 1892),
  counted: it returns `decide I.InCcut` with at most `2|E||D| + 3|D| + 5|E| + 2` arithmetic
  operations, comparisons and tests, and no maximum flow and no evaluation of `f`
  (`inCcutC_val`, `inCcutC_cost`).
-/

namespace Stoc

namespace Counted

universe u

variable {ι : Type u}

/-- The sum over `s` of rational terms that cost `g i` each, with one addition per term. -/
def sumQ (s : Finset ι) (g : ι → Counted ℚ) : Counted ℚ :=
  ⟨∑ i ∈ s, (g i).val, ∑ i ∈ s, (g i).cost + (s.card, 0, 0)⟩

@[simp] lemma val_sumQ (s : Finset ι) (g : ι → Counted ℚ) :
    (sumQ s g).val = ∑ i ∈ s, (g i).val := rfl

@[simp] lemma cost_sumQ (s : Finset ι) (g : ι → Counted ℚ) :
    (sumQ s g).cost = ∑ i ∈ s, (g i).cost + (s.card, 0, 0) := rfl

/-- The elements of `s` that satisfy `p`, with `k` tests (comparisons or membership tests) for each
element. -/
def filterC (k : ℕ) (s : Finset ι) (p : ι → Prop) [DecidablePred p] : Counted (Finset ι) :=
  ⟨s.filter p, (k * s.card, 0, 0)⟩

@[simp] lemma val_filterC (k : ℕ) (s : Finset ι) (p : ι → Prop) [DecidablePred p] :
    (filterC k s p).val = s.filter p := rfl

@[simp] lemma cost_filterC (k : ℕ) (s : Finset ι) (p : ι → Prop) [DecidablePred p] :
    (filterC k s p).cost = (k * s.card, 0, 0) := rfl

/-- Whether all the counted tests `g i`, `i ∈ s`, hold: their costs and one conjunction per
test. -/
def allC (s : Finset ι) (g : ι → Counted Bool) : Counted Bool :=
  ⟨decide (∀ i ∈ s, (g i).val = true), ∑ i ∈ s, (g i).cost + (s.card, 0, 0)⟩

@[simp] lemma val_allC (s : Finset ι) (g : ι → Counted Bool) :
    (allC s g).val = decide (∀ i ∈ s, (g i).val = true) := rfl

@[simp] lemma cost_allC (s : Finset ι) (g : ι → Counted Bool) :
    (allC s g).cost = ∑ i ∈ s, (g i).cost + (s.card, 0, 0) := rfl

/-- One evaluation of `f`, counted in the third component. Its arithmetic operations, if any, are
counted by the program that performs it (`Hardness.RatInst.fC`). -/
def evalMark : Counted Unit := ⟨(), (0, 0, 1)⟩

@[simp] lemma val_evalMark : evalMark.val = () := rfl

@[simp] lemma cost_evalMark : evalMark.cost = (0, 0, 1) := rfl

/-- One maximum flow, counted as one minimization (cited): "the algorithm of Edmonds and Karp
computes a maximum flow in polynomial time [Sch03, Thm. 10.5]", and the largest minimizer is read
off the residual network [GGT89, §2.1–2.2] (`stoc-sections/appD-hardness.tex:1849-1851`). It
returns the value `V` of a maximum flow and the set `T`; the arithmetic operations of the flow
algorithm are not counted here. -/
def maxFlow {E : Type*} (V : ℚ) (T : Finset E) : Counted (ℚ × Finset E) := ⟨(V, T), (0, 1, 0)⟩

@[simp] lemma val_maxFlow {E : Type*} (V : ℚ) (T : Finset E) : (maxFlow V T).val = (V, T) := rfl

@[simp] lemma cost_maxFlow {E : Type*} (V : ℚ) (T : Finset E) :
    (maxFlow V T).cost = (0, 1, 0) := rfl

end Counted

namespace Hardness

open Counted Finset

namespace RatInst

variable {E : Type*} [Fintype E] [DecidableEq E] (I : RatInst E)

/-- One evaluation of `f = cut_D + ω` at `S` (`eq:cutform`), "a sum of input numbers"
(`lem:exactbr`(b), `stoc-sections/appD-hardness.tex:1856`): the arcs of `D` that leave `S` (two
membership tests for each arc), the sum of their capacities, the sum of the weights on `S`, and
the sum of the two. It counts as one evaluation of `f`. -/
def fC (S : Finset E) : Counted ℚ :=
  evalMark >>=ᶜ fun _ =>
  filterC 2 I.D (fun a => a.1 ∈ S ∧ a.2 ∉ S) >>=ᶜ fun L =>
  sumQ L (fun a => Counted.ret (I.cap a)) >>=ᶜ fun c =>
  sumQ S (fun e => Counted.ret (I.ω e)) >>=ᶜ fun w =>
  Counted.ops 1 (c + w)

omit [Fintype E] in
lemma fC_val (S : Finset E) : (I.fC S).val = I.fQ S := by
  simp [fC, fQ]

omit [Fintype E] in
lemma fC_cost (S : Finset E) :
    (I.fC S).cost =
      (2 * I.D.card + (I.D.filter fun a => a.1 ∈ S ∧ a.2 ∉ S).card + S.card + 1, 0, 1) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (simp [fC]; try ring)

/-- An evaluation of `f` takes at most `3|D| + |E| + 1` arithmetic operations and membership tests,
no minimization and one evaluation of `f`. -/
lemma fC_cost_le (S : Finset E) :
    (I.fC S).cost.1 ≤ 3 * I.D.card + Fintype.card E + 1 ∧ (I.fC S).cost.2.1 = 0 ∧
      (I.fC S).cost.2.2 = 1 := by
  rw [fC_cost]
  have h1 := card_filter_le I.D (fun a => a.1 ∈ S ∧ a.2 ∉ S)
  have h2 := card_le_univ S
  refine ⟨?_, rfl, rfl⟩
  dsimp only
  omega

/-- The product of the denominators of the capacities of the network `G_y` of `lem:exactbr`(b): of
the arcs of `D` and of the arcs `s → e` and `e → s'`, of capacities `max(−y_e, 0)` and
`max(y_e, 0)`. -/
def denProd (y : E → ℚ) : ℕ :=
  (∏ a ∈ I.D, (I.cap a).den) * ∏ e, ((max (-y e) 0).den * (max (y e) 0).den)

omit [DecidableEq E] in
lemma denProd_pos (y : E → ℚ) : 0 < I.denProd y :=
  Nat.mul_pos (prod_pos fun a _ => (I.cap a).den_pos)
    (prod_pos fun e _ => Nat.mul_pos (max (-y e) 0).den_pos (max (y e) 0).den_pos)

omit [DecidableEq E] in
/-- The product of the denominators of the capacities of `G_y` is at most `2` to the sum of their
encoding lengths (not in the paper: "After multiplication by the product of their denominators,
the capacities are integers of polynomial encoding length", `lem:exactbr`(b), line 1849; the
same bound for a general product of denominators is part of `exists_common_den` in
`ContractDesignPolymatroids/Hardness/ExactBits.lean`). A conjunct of `exactbr`. -/
lemma denProd_le (y : E → ℚ) :
    I.denProd y ≤ 2 ^ (∑ a ∈ I.D, enc (I.cap a) +
      ∑ e, (enc (max (-y e) 0) + enc (max (y e) 0))) := by
  rw [pow_add, ← prod_pow_eq_pow_sum, ← prod_pow_eq_pow_sum]
  refine Nat.mul_le_mul (prod_le_prod fun a _ => (den_lt (I.cap a)).le)
    (prod_le_prod fun e _ => ?_)
  rw [pow_add]
  exact Nat.mul_le_mul (den_lt _).le (den_lt _).le

/-- One maximum flow in the network `G_y` of `lem:exactbr`(b) (`stoc-sections/
appD-hardness.tex:1840-1851`), with the arithmetic around it, for the minimum `v` of `cut_D + y` and
its largest minimizer `T`, which the flow computes:
(1) the capacities `max(−y_e, 0)` of the arcs `s → e` and `max(y_e, 0)` of the arcs `e → s'` (a
negation and two comparisons for each `e`);
(2) "After multiplication by the product of their denominators, the capacities are integers of
polynomial encoding length": the product `P` of the denominators of the `|D| + 2|E|` capacities
(`denProd`) and the capacities times `P` (one multiplication each). This step returns `P`; the
integer capacities are the input of the cited flow and are not values of the program;
(3) "the algorithm of Edmonds and Karp computes a maximum flow in polynomial time [Sch03, Thm.
10.5]. This gives the minimum of `cut_D + y` and its largest minimizer" (cited, `maxFlow`): the
value `V = P (v + ∑_e max(−y_e, 0))` of a maximum flow and the largest minimizer `T`;
(4) the minimum `v = V/P − ∑_e max(−y_e, 0)`, as the cut `{s} ∪ S` of `G_y` has capacity
`cut_D(S) + y(S) + ∑_e max(−y_e, 0)` (lines 1842-1847, `netCut_srcSide`): a division, `|E|`
additions and a subtraction (not in the paper, which says "This gives the minimum of
`cut_D + y`").
`P` is at most `2` to the sum of the encoding lengths of the capacities (`denProd_le`). That the
integer capacities have absolute value less than `2` to this sum is `exists_common_den` in
`ContractDesignPolymatroids/Hardness/ExactBits.lean` for a common denominator of the same kind; it is not applied to `P`
here, and the integer capacities are not bounded by a lemma about `flowC`. -/
def flowC (y : E → ℚ) (v : ℚ) (T : Finset E) : Counted (ℚ × Finset E) :=
  Counted.ops (3 * Fintype.card E) (fun e => (max (-y e) 0, max (y e) 0)) >>=ᶜ fun c =>
  Counted.ops (2 * (I.D.card + 2 * Fintype.card E)) (I.denProd y) >>=ᶜ fun P =>
  maxFlow ((P : ℚ) * (v + ∑ e, (c e).1)) T >>=ᶜ fun r =>
  Counted.ops (Fintype.card E + 2) (r.1 / P - ∑ e, (c e).1, r.2)

omit [DecidableEq E] in
lemma flowC_val (y : E → ℚ) (v : ℚ) (T : Finset E) : (I.flowC y v T).val = (v, T) := by
  have hP : (I.denProd y : ℚ) ≠ 0 := by exact_mod_cast (I.denProd_pos y).ne'
  simp only [flowC, val_bind, Counted.val_ops, val_maxFlow, Prod.mk.injEq, and_true]
  field_simp
  ring

omit [DecidableEq E] in
lemma flowC_cost (y : E → ℚ) (v : ℚ) (T : Finset E) :
    (I.flowC y v T).cost = (8 * Fintype.card E + 2 * I.D.card + 2, 1, 0) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (simp [flowC]; try ring)

/-- The recognition of the inputs in the proof of membership in NP in `thm:nphard` ("The inputs are
recognized in polynomial time by `lem:cutforms`(b)", `stoc-sections/appD-hardness.tex:1892`),
counted: the checks of the proof of `lem:cutforms`(b) (lines 138-139), "to check that `D` has no
loops, that all capacities are nonnegative, and that `m` and `β` are positive, and to compare, for
each `e ∈ E`, the weight `ω_e` with the sum of the capacities of the arcs entering `e`. These are
polynomially many additions and comparisons of input numbers." For each arc, a test of its end
points and a comparison of its capacity with `0`; for each element, two comparisons; for each
element `e`, the arcs entering `e` (one test per arc), the sum of their capacities and one
comparison; one conjunction per test and two for the three results. -/
def inCcutC : Counted Bool :=
  allC I.D (fun a => Counted.ops 2 (decide (a.1 ≠ a.2 ∧ 0 ≤ I.cap a))) >>=ᶜ fun b₁ =>
  allC univ (fun e => Counted.ops 2 (decide (0 < I.m e ∧ 0 < I.β e))) >>=ᶜ fun b₂ =>
  allC univ (fun e =>
    filterC 1 I.D (fun a => a.2 = e) >>=ᶜ fun L =>
    sumQ L (fun a => Counted.ret (I.cap a)) >>=ᶜ fun s =>
    Counted.ops 1 (decide (s ≤ I.ω e))) >>=ᶜ fun b₃ =>
  Counted.ops 2 (b₁ && b₂ && b₃)

lemma inCcutC_val : I.inCcutC.val = decide I.InCcut := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, inCcut_iff]
  simp only [inCcutC, val_bind, val_allC, Counted.val_ops, Bool.and_eq_true, decide_eq_true_eq,
    mem_univ, true_implies, val_filterC, val_sumQ, Counted.val_ret]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨fun a ha => (h1 a ha).1, fun a ha => (h1 a ha).2, fun e => (h2 e).1,
      fun e => (h2 e).2, fun e => of_decide_eq_true (h3 e)⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨fun a ha => ⟨h1 a ha, h2 a ha⟩, fun e => ⟨h3 e, h4 e⟩⟩,
      fun e => decide_eq_true (h5 e)⟩

lemma inCcutC_cost :
    I.inCcutC.cost.1 ≤ 2 * Fintype.card E * I.D.card + 3 * I.D.card + 5 * Fintype.card E + 2 ∧
      I.inCcutC.cost.2 = (0, 0) := by
  have hL : ∀ e : E, (I.D.filter fun a => a.2 = e).card ≤ I.D.card := fun e =>
    card_filter_le _ _
  constructor
  · simp only [inCcutC, cost_bind, cost_allC, Counted.cost_ops, cost_filterC, val_filterC,
      cost_sumQ, Counted.cost_ret, sum_const_zero, zero_add, Prod.fst_add, Prod.fst_sum,
      sum_const, card_univ, Prod.smul_fst, smul_eq_mul, one_mul]
    have h3 : ∑ e : E, (I.D.card + ((I.D.filter fun a => a.2 = e).card + 1)) ≤
        ∑ e : E, (2 * I.D.card + 1) := sum_le_sum fun e _ => by have := hL e; omega
    simp only [sum_const, card_univ, smul_eq_mul] at h3
    nlinarith [h3]
  · simp [inCcutC, Prod.snd_sum]

end RatInst

end Hardness

end Stoc
