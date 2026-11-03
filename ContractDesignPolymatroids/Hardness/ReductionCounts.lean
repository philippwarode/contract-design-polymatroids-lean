-- stamp r1 2026-11-03
import ContractDesignPolymatroids.Hardness.ReductionSizes
import ContractDesignPolymatroids.Hardness.CountedBits

/-!
# The reduction counted: the arithmetic operations of `def:reduction`

The STOC version's proof of `thm:nphard` (Appendix C.8, `stoc-sections/appD-hardness.tex:1883-1903`)
counts the work of the reduction of `def:reduction` (lines 255-264) in prose (lines 1885-1887):
"The reduction of `def:reduction` runs in time polynomial in the encoding length of `(a, T)`.
Indeed, the algorithm of `thm:gadget` computes `N_0` and both combs in polynomial time, as its
inputs have `log μ_k, log μ'_k = O(k + log(2 + ∑_i a_i))` and the integers `N_0` and `N_0 + T` have
bit lengths bounded in the same way (`lem:sizes`, the proof of `thm:gadget`, and `T ≤ ∑_i a_i`).
Apart from the choice of `σ`, the steps (3) to (5) take `O(k)` arithmetic operations, and `σ` is a
power of `2` that is at least half the smallest right-hand side in step (4), so `log(1/σ)` is
polynomial and `σ` is found by as many comparisons."

This file counts these operations in the cost model of `Stoc.Counted`
(`ContractDesignPolymatroids/Preliminaries/Counted.lean`): counted programs perform the steps (1)-(5) of
`def:reduction`, their values are proved equal to the definitions of
`ContractDesignPolymatroids/Hardness/Reduction.lean` and `ContractDesignPolymatroids/Hardness/ReductionSizes.lean`, and their arithmetic
operations (comparisons included) are counted exactly (not in the paper: the paper counts in
prose). Here `k` is the length of the input `a`, `k'` the length after step (1), and `σ = 2^{−J}`.

* `step1C`: step (1), with `k + 2` operations (`step1C_val`, `step1C_cost`).
* `inputsC`: `H`, `μ` and `μ'` of step (2), with `4k' + 1` operations (`inputsC_val`,
  `inputsC_cost`).
* `GadgetCost`, `nminC`, `combC`: the four calls of the algorithm of `thm:gadget` in step (2),
  `N_min(μ)`, `N_min(μ')`, `I_1` and `I_2`, at a cost that is a parameter here; the algorithm is
  counted in `ContractDesignPolymatroids/Hardness/GadgetCounts.lean` (`gadgetCost`, `reductionC_gadget`).
* `condC`, `searchC`: the search for `σ` in step (4) through the candidates `1, 1/2, 1/4, …`: the
  `J` candidates that fail cost ten operations each (the test and the halving), the one that passes
  nine (`searchC_spec`, `searchC_val`, `searchC_cost`).
* `stepsC`: the steps (2)-(5). It returns the numbers `p`, `q`, `κ*`, `c`, `ℓ`, `σ`, `α_∘`, `C` and
  `ϑ` and the output `Î`, by its cut form (`outForm`), its rewards (`mHat`) and its curvatures
  (`βHat`) (`stepsC_val`). Besides the four calls of the gadget, it takes `4k' + 3` operations in
  step (2), `10k' + 47` in the steps (3)-(5) apart from the choice of `σ`, and `10J + 9` for the
  search (`stepsC_cost`).
* `reductionC`, `reductionC_spec`: the whole reduction, with `k + 14k' + 10J + 61` operations
  besides the gadget, at most `2^{35}⟨(a, T)⟩`, as `k' ≤ k ≤ ⟨(a, T)⟩` and `J ≤ 2^{31}⟨(a, T)⟩`
  (`σ_search`, `Bg_le`).

The sizes of the numbers are bounded in `ContractDesignPolymatroids/Hardness/ReductionSizes.lean`: the numbers of the
steps (3)-(5) and of the output have encoding length polynomial in `⟨(a, T)⟩` (`steps_bits`,
`out_bits`), and the candidates `2^{−j}`, `j ≤ J`, have at most `J` bits (`Bits.half_pow`). The
other intermediate results of the programs, such as `σ(c + ℓ)` in the test of step (4), are
products and quotients of a few of these numbers and are not bounded separately here. The
algorithm of `thm:gadget` enters here as the parameter `GadgetCost`; it is counted in
`ContractDesignPolymatroids/Hardness/GadgetCounts.lean` (part (4) of the proof of `thm:gadget`, with the evaluations of
`g` of `lem:sizes`), where `reductionC_gadget` gives the reduction with that cost. Not formalised:
the step from the counts to the running time of a Turing machine
(`stoc-sections/01-introduction.tex:31`).
-/

namespace Stoc

namespace Hardness

open Finset Counted

noncomputable section

namespace SubsetSum

/-! ### Step (1) -/

/-- The sum over `s` of natural numbers that cost `g i` each, with one addition per term (not in
the paper: `Counted.sum` and `Counted.sumQ` in `ℕ`). -/
def sumNatC {ι : Type*} (s : Finset ι) (g : ι → Counted ℕ) : Counted ℕ :=
  ⟨∑ i ∈ s, (g i).val, ∑ i ∈ s, (g i).cost + (s.card, 0, 0)⟩

@[simp] lemma cost_sumNatC {ι : Type*} (s : Finset ι) (g : ι → Counted ℕ) :
    (sumNatC s g).cost = ∑ i ∈ s, (g i).cost + (s.card, 0, 0) := rfl

/-- **Step (1) of `def:reduction`, counted** (`stoc-sections/appD-hardness.tex:258`): "If `T < 0`
or `T > ∑_i a_i`, replace `(a, T)` by the no-instance `a = (2)`, `T = 1`." The sum `∑_i a_i`
(`k` additions) and the two comparisons `T < 0` and `T > ∑_i a_i` (not in the paper: its count
starts with the gadget). It returns the pair `P.step1` (`step1C_val`). -/
def step1C (P : SubsetSum) : Counted SubsetSum :=
  sumNatC (range P.k) (fun i => Counted.ret (P.a i)) >>=ᶜ fun s =>
  Counted.ops 2
    (if P.T < 0 ∨ (s : ℤ) < P.T then ⟨1, le_rfl, fun _ => 2, fun _ _ => two_pos, 1⟩ else P)

lemma step1C_val (P : SubsetSum) : (step1C P).val = P.step1 := rfl

lemma step1C_cost (P : SubsetSum) : (step1C P).cost = (P.k + 2, 0, 0) := by
  simp [step1C]

/-- Step (1) does not increase the number of items: `k' ≤ k` (not in the paper). -/
lemma step1_k_le (P : SubsetSum) : P.step1.k ≤ P.k := by
  unfold step1
  split_ifs
  · exact P.one_le_k
  · exact le_rfl

/-! ### Step (2) -/

/-- **`H`, `μ` and `μ'` of step (2), counted** (`stoc-sections/appD-hardness.tex:259`, "With
`H, μ, μ'` as in `lem:coincidence`"; `lem:coincidence`, lines 203-214: `H := 10∑_i a_i + 1`,
`μ_i := H 8^{i−1} + a_i` and `μ'_i := H 8^{i−1}`; indices from `0`): the sum `∑_i a_i` (`k`
additions), `H` (a multiplication and an addition), the powers `8^i = 8 · 8^{i−1}` for
`1 ≤ i < k` by repeated multiplication (`k − 1` multiplications), and for each `i < k` the product
`μ'_i = H 8^i` and the sum `μ_i = μ'_i + a_i` (two operations); `4k + 1` operations in all (not in
the paper, which bounds the sizes of the inputs, not their computation). It returns `(μ, μ')`
(`inputsC_val`). -/
def inputsC (R : SubsetSum) : Counted ((ℕ → ℕ) × (ℕ → ℕ)) :=
  sumNatC (range R.k) (fun i => Counted.ret (R.a i)) >>=ᶜ fun s =>
  Counted.ops 2 (10 * s + 1) >>=ᶜ fun H =>
  Counted.ops (R.k - 1) (fun i => 8 ^ i) >>=ᶜ fun pw =>
  Counted.ops (2 * R.k) (fun i => H * pw i + R.a i, fun i => H * pw i)

lemma inputsC_val (R : SubsetSum) : (inputsC R).val = (R.μ, R.μ') := rfl

lemma inputsC_cost (R : SubsetSum) : (inputsC R).cost = (4 * R.k + 1, 0, 0) := by
  have := R.one_le_k
  simp only [inputsC, cost_bind, cost_sumNatC, Counted.cost_ret, Counted.cost_ops, sum_const_zero,
    card_range, zero_add, Prod.mk_add_mk, add_zero, Prod.mk.injEq, and_true]
  omega

/-- The output of the algorithm of `thm:gadget` that the reduction uses
(`stoc-sections/appD-hardness.tex:191-197`), for an input `μ^in` of length `k`: the instance
`I(μ^in, N)`, by its cut form, its rewards and its curvatures, and its width `δ`, its dip `κ` and
its line `p + qα`. -/
structure Comb (k : ℕ) where
  /-- the cut form of the instance -/
  form : CutForm (Gr (k - 1) ⊕ Unit)
  /-- the rewards -/
  m : Gr (k - 1) ⊕ Unit → ℝ
  /-- the curvatures -/
  β : Gr (k - 1) ⊕ Unit → ℝ
  /-- the width -/
  δ : ℝ
  /-- the dip -/
  κ : ℝ
  /-- the line `p + qα`: `p` -/
  p : ℝ
  /-- the line `p + qα`: `q` -/
  q : ℝ

/-- The comb `I(μ^in, N)` of `thm:gadget`: the cut form `gadgetForm`, the rewards `gadgetM`, the
curvatures `gadgetB`, the width `δT`, the dip `κT` and the line `gp + gq α`. -/
def gadgetComb (μin : ℕ → ℕ) (k N : ℕ) : Comb k :=
  ⟨gadgetForm μin k N, gadgetM μin k, gadgetB μin k N, δT μin, κT μin, gp μin k N, gq μin k⟩

/-- The cost of the algorithm of `thm:gadget` (a parameter here; counted in
`ContractDesignPolymatroids/Hardness/GadgetCounts.lean`, `gadgetCost`): `nmin μ^in k` is the cost of `N_min(μ^in)` for an
input `μ^in` of length `k`, and `comb μ^in k N` the cost of the comb `I(μ^in, N)` with its width,
dip and line. -/
structure GadgetCost where
  /-- the cost of `N_min(μ^in)` -/
  nmin : (ℕ → ℕ) → ℕ → Cost
  /-- the cost of `I(μ^in, N)` with `δ`, `κ`, `p` and `q` -/
  comb : (ℕ → ℕ) → ℕ → ℕ → Cost

/-- `N_min(μ^in)` by the algorithm of `thm:gadget`, at the cost `G.nmin μ^in k` (a parameter
here; counted in `ContractDesignPolymatroids/Hardness/GadgetCounts.lean`, `nminCount`). -/
def nminC (G : GadgetCost) (μin : ℕ → ℕ) (k : ℕ) : Counted ℕ := ⟨gNmin μin k, G.nmin μin k⟩

/-- The comb `I(μ^in, N)` by the algorithm of `thm:gadget`, at the cost `G.comb μ^in k N` (a
parameter here; counted in `ContractDesignPolymatroids/Hardness/GadgetCounts.lean`, `combCount`). -/
def combC (G : GadgetCost) (μin : ℕ → ℕ) (k N : ℕ) : Counted (Comb k) :=
  ⟨gadgetComb μin k N, G.comb μin k N⟩

/-- The cost of the four calls of the algorithm of `thm:gadget` in step (2) for the pair `R`:
`N_min(μ)`, `N_min(μ')`, `I_1 = I(μ, N_0)` and `I_2 = I(μ', N_0 + T)` (a parameter here; counted in
`ContractDesignPolymatroids/Hardness/GadgetCounts.lean`). -/
def GadgetCost.total (G : GadgetCost) (R : SubsetSum) : Cost :=
  G.nmin R.μ R.k + G.nmin R.μ' R.k + G.comb R.μ R.k R.N₀ + G.comb R.μ' R.k R.N₂

/-! ### The search for `σ` in step (4) -/

/-- The test of the four conditions of step (4) at a candidate `s`
(`stoc-sections/appD-hardness.tex:261`: "`σ ≤ 1`, `σ ≤ κ*δ_1/(4qℓ²)`, `σ(c + ℓ) ≤ 1/4`, and
`σ(p + 2qc) < q`"), with the right-hand side `A = κ*δ_1/(4qℓ²)` and the factors `B = c + ℓ` and
`D = p + 2qc` computed once before the search: four comparisons, two multiplications and three
conjunctions (not in the paper). -/
def condC (A B D q s : ℝ) : Counted Bool :=
  Counted.ops 9 (decide (s ≤ 1 ∧ s ≤ A ∧ s * B ≤ 1 / 4 ∧ s * D < q))

/-- The search for `σ` in step (4) (`stoc-sections/appD-hardness.tex:261`, "Let `σ` be the largest
power of `2` with" the four conditions; the proof of `thm:nphard`, line 1887: "`σ` is found by as
many comparisons"), from the candidate `s` with at most `n` candidates: it tests `s`, returns it if
it passes, and otherwise goes on with `s/2` (one operation). As `σ ≤ 1`, the search starts at `1`;
the search order and the bound `n` on the candidates are not in the paper (`σ_search`). -/
def searchC (A B D q : ℝ) : ℕ → ℝ → Counted ℝ
  | 0, s => Counted.ret s
  | n + 1, s =>
      condC A B D q s >>=ᶜ fun b =>
      if b then Counted.ret s else Counted.ops 1 (s / 2) >>=ᶜ fun s' => searchC A B D q n s'

/-- The search returns the first candidate that passes: if `2^{−J}` passes the test and every
`2^{−j}`, `j < J`, fails, then from the candidate `2^{−j}`, `j ≤ J`, with more than `J − j`
candidates left, the search returns `2^{−J}` after `J − j` failed tests and halvings and one test
that passes, `10(J − j) + 9` operations (not in the paper). -/
lemma searchC_spec (R : SubsetSum) {A B D q : ℝ}
    (h : ∀ s, (s ≤ 1 ∧ s ≤ A ∧ s * B ≤ 1 / 4 ∧ s * D < q) ↔ R.Cond4 s) {J : ℕ}
    (hJ : R.Cond4 ((1 / 2) ^ J)) (hlt : ∀ j < J, ¬ R.Cond4 ((1 / 2) ^ j)) :
    ∀ n j, j ≤ J → J < j + n →
      (searchC A B D q n ((1 / 2) ^ j)).val = (1 / 2) ^ J ∧
      (searchC A B D q n ((1 / 2) ^ j)).cost = (10 * (J - j) + 9, 0, 0) := by
  intro n
  induction n with
  | zero => intro j hj hjn; omega
  | succ n ih =>
    intro j hj hjn
    rcases hj.lt_or_eq with hj' | rfl
    · have hf : decide ((1 / 2 : ℝ) ^ j ≤ 1 ∧ (1 / 2 : ℝ) ^ j ≤ A ∧
          (1 / 2 : ℝ) ^ j * B ≤ 1 / 4 ∧ (1 / 2 : ℝ) ^ j * D < q) = false := by
        rw [decide_eq_false_iff_not, h]
        exact hlt j hj'
      have hs : (1 / 2 : ℝ) ^ j / 2 = (1 / 2) ^ (j + 1) := by rw [pow_succ]; ring
      obtain ⟨h1, h2⟩ := ih (j + 1) hj' (by omega)
      simp only [searchC, condC, val_bind, cost_bind, Counted.val_ops, Counted.cost_ops, hf,
        Bool.false_eq_true, ↓reduceIte, hs, h1, h2, true_and, Prod.mk_add_mk, Prod.mk.injEq,
        add_zero, and_true]
      omega
    · have ht : decide ((1 / 2 : ℝ) ^ j ≤ 1 ∧ (1 / 2 : ℝ) ^ j ≤ A ∧
          (1 / 2 : ℝ) ^ j * B ≤ 1 / 4 ∧ (1 / 2 : ℝ) ^ j * D < q) = true := by
        rw [decide_eq_true_iff, h]
        exact hJ
      simp only [searchC, condC, val_bind, cost_bind, Counted.val_ops, Counted.cost_ops, ht,
        ↓reduceIte, Counted.val_ret, Counted.cost_ret, Nat.sub_self, mul_zero, zero_add, add_zero,
        and_self]

/-- The search from `σ = 1` returns `2^{−J}` (`searchC_spec`; not in the paper). -/
lemma searchC_val (R : SubsetSum) {A B D q : ℝ} {J n : ℕ} (hJ : R.Cond4 ((1 / 2) ^ J))
    (hlt : ∀ j < J, ¬ R.Cond4 ((1 / 2) ^ j)) (hn : J < n)
    (h : ∀ s, (s ≤ 1 ∧ s ≤ A ∧ s * B ≤ 1 / 4 ∧ s * D < q) ↔ R.Cond4 s) :
    (searchC A B D q n 1).val = (1 / 2) ^ J := by
  have := (searchC_spec R h hJ hlt n 0 (Nat.zero_le _) (by omega)).1
  rwa [pow_zero] at this

/-- The search from `σ = 1` tests the `J + 1` candidates `1, 1/2, …, 2^{−J}` and halves `J` times,
`10J + 9` operations (`searchC_spec`; not in the paper). -/
lemma searchC_cost (R : SubsetSum) {A B D q : ℝ} {J n : ℕ} (hJ : R.Cond4 ((1 / 2) ^ J))
    (hlt : ∀ j < J, ¬ R.Cond4 ((1 / 2) ^ j)) (hn : J < n)
    (h : ∀ s, (s ≤ 1 ∧ s ≤ A ∧ s * B ≤ 1 / 4 ∧ s * D < q) ↔ R.Cond4 s) :
    (searchC A B D q n 1).cost = (10 * J + 9, 0, 0) := by
  have := (searchC_spec R h hJ hlt n 0 (Nat.zero_le _) (by omega)).2
  rwa [pow_zero, Nat.sub_zero] at this

/-! ### The steps (2)-(5) -/

/-- The output of the steps (2)-(5) of `def:reduction` for the pair `R` after step (1): the numbers
`p`, `q`, `κ*`, `c`, `ℓ` of step (3), `σ`, `α_∘`, `C` of step (4), and the output `(Î, ϑ)` of step
(5), the instance `Î` given by its cut form, its rewards and its curvatures. -/
structure Output (R : SubsetSum) where
  /-- `p = p_1 + (δ_2/δ_1)p_2` -/
  p : ℝ
  /-- `q = q_1 + (δ_2/δ_1)²q_2` -/
  q : ℝ
  /-- `κ* = min(κ_1, (δ_2/δ_1)²κ_2)` -/
  κStar : ℝ
  /-- the center `c` -/
  c : ℝ
  /-- the half-length `ℓ` -/
  ℓ : ℝ
  /-- `σ` -/
  σ : ℝ
  /-- `α_∘ = σδ_1N_0` -/
  αknob : ℝ
  /-- `C = (q(1 − 2σc) − σp)/σ²` -/
  C : ℝ
  /-- the cut form of `Î` -/
  form : CutForm (((Gr (R.k - 1) ⊕ Unit) ⊕ (Gr (R.k - 1) ⊕ Unit)) ⊕ Unit)
  /-- the rewards of `Î` -/
  m : ((Gr (R.k - 1) ⊕ Unit) ⊕ (Gr (R.k - 1) ⊕ Unit)) ⊕ Unit → ℝ
  /-- the curvatures of `Î` -/
  β : ((Gr (R.k - 1) ⊕ Unit) ⊕ (Gr (R.k - 1) ⊕ Unit)) ⊕ Unit → ℝ
  /-- `ϑ = (q/σ²)((1 − σc)² − σ²ℓ²)` -/
  ϑ : ℝ

/-- The output of the steps (2)-(5) as `ContractDesignPolymatroids/Hardness/Reduction.lean` defines it (`p`, `q`,
`κStar`, `c`, `ℓ`, `σ`, `αknob`, `C`, `mHat`, `βHat`, `ϑ`), with the cut form `outForm` of `Î`
(`ContractDesignPolymatroids/Hardness/ReductionSizes.lean`; `outForm_fn`: its function is `fHat`). -/
def output (R : SubsetSum) : Output R :=
  ⟨R.p, R.q, R.κStar, R.c, R.ℓ, R.σ, R.αknob, R.C, outForm R, R.mHat, R.βHat, R.ϑ⟩

/-- **The steps (2)-(5) of `def:reduction`, counted** (`stoc-sections/appD-hardness.tex:259-262`),
for the pair `R` after step (1).

(2) "With `H, μ, μ'` as in `lem:coincidence`, let `N_0 := max(N_min(μ), N_min(μ'))`,
`I_1 := I(μ, N_0)`, and `I_2 := I(μ', N_0 + T)` (`thm:gadget`), with widths `δ_1, δ_2`, dips
`κ_1, κ_2`, and lines `p_1 + q_1α`, `p_2 + q_2α`." `H`, `μ`, `μ'` (`inputsC`), the four calls of
the algorithm of `thm:gadget` (a parameter here; counted in `ContractDesignPolymatroids/Hardness/GadgetCounts.lean`), a
comparison for `N_0` and an addition for `N_0 + T`.

(3) "Let `I_2'` be `I_2` with `m` replaced by `(δ_2/δ_1)m`, let `I* := I_1 ⊕ I_2'`,
`p := p_1 + (δ_2/δ_1)p_2`, `q := q_1 + (δ_2/δ_1)²q_2`, and `κ* := min(κ_1, (δ_2/δ_1)²κ_2)`, and let
`c` and `ℓ` be the center and the half-length of `[δ_1N_0, δ_1(N_0 + ∑_iμ_i)]`." `δ_2/δ_1`, one
multiplication for each of the `3k + 1` rewards of `I_2`, `p`, `q`, `κ*`, the sum `∑_iμ_i` (`k`
additions), the endpoints and `c`, `ℓ`: `4k + 16` operations.

(4) "Let `σ` be the largest power of `2` with `σ ≤ 1`, `σ ≤ κ*δ_1/(4qℓ²)`, `σ(c + ℓ) ≤ 1/4`, and
`σ(p + 2qc) < q`. Let `Î` be `I*` with `m` replaced by `m/σ`, plus a capped linear summand
(`lem:ops`(c)), the centering summand, with `α_∘ := σδ_1N_0` and
`C := (q(1 − 2σc) − σp)/σ²`." The right-hand side `κ*δ_1/(4qℓ²)` and the factors `c + ℓ` and
`p + 2qc` (nine operations), the search for `σ` (`searchC`), `α_∘`, `C`, one division for each of
the `6k + 2` rewards of `I*`, and the curvature `α_∘/C` of the centering summand, whose reward is
`1`. The cut form of `Î` is the disjoint union of the gadgets' forms and an isolated node of
weight `C` (`outForm`; the proof of `thm:nphard`, line 1888): no arithmetic operation (not in the
paper). The search is given `6561Bg + 2` candidates, more than it uses (`J ≤ 6561Bg + 1`,
`σ_search`); this bound only makes the recursion terminate and is not computed (not in the paper).

(5) "Output `Î` and `ϑ := (q/σ²)((1 − σc)² − σ²ℓ²)`." Nine operations. -/
def stepsC (G : GadgetCost) (R : SubsetSum) : Counted (Output R) :=
  -- step (2)
  inputsC R >>=ᶜ fun μs =>
  nminC G μs.1 R.k >>=ᶜ fun n₁ =>
  nminC G μs.2 R.k >>=ᶜ fun n₂ =>
  Counted.ops 1 (max n₁ n₂) >>=ᶜ fun N₀ =>
  Counted.ops 1 (N₀ + R.T.toNat) >>=ᶜ fun N₂ =>
  combC G μs.1 R.k N₀ >>=ᶜ fun I₁ =>
  combC G μs.2 R.k N₂ >>=ᶜ fun I₂ =>
  -- step (3)
  Counted.ops 1 (I₂.δ / I₁.δ) >>=ᶜ fun r =>
  Counted.ops (Fintype.card (Gr (R.k - 1) ⊕ Unit)) (fun e => r * I₂.m e) >>=ᶜ fun m₂ =>
  Counted.ops 2 (I₁.p + r * I₂.p) >>=ᶜ fun p =>
  Counted.ops 1 (r ^ 2) >>=ᶜ fun r₂ =>
  Counted.ops 2 (I₁.q + r₂ * I₂.q) >>=ᶜ fun q =>
  Counted.ops 2 (min I₁.κ (r₂ * I₂.κ)) >>=ᶜ fun κ =>
  Counted.sum (range R.k) (fun i => Counted.ret (μs.1 i : ℝ)) >>=ᶜ fun sμ =>
  Counted.ops 1 (I₁.δ * N₀) >>=ᶜ fun x₀ =>
  Counted.ops 2 (I₁.δ * (N₀ + sμ)) >>=ᶜ fun x₁ =>
  Counted.ops 2 ((x₀ + x₁) / 2) >>=ᶜ fun c =>
  Counted.ops 2 ((x₁ - x₀) / 2) >>=ᶜ fun ℓ =>
  -- step (4)
  Counted.ops 5 (κ * I₁.δ / (4 * q * ℓ ^ 2)) >>=ᶜ fun A =>
  Counted.ops 1 (c + ℓ) >>=ᶜ fun B =>
  Counted.ops 3 (p + 2 * q * c) >>=ᶜ fun D =>
  searchC A B D q (6561 * R.Bg + 2) 1 >>=ᶜ fun σ =>
  Counted.ops 2 (σ * I₁.δ * N₀) >>=ᶜ fun αk =>
  Counted.ops 8 ((q * (1 - 2 * σ * c) - σ * p) / σ ^ 2) >>=ᶜ fun C =>
  Counted.ops (Fintype.card ((Gr (R.k - 1) ⊕ Unit) ⊕ (Gr (R.k - 1) ⊕ Unit)))
    (fun e => Sum.elim I₁.m m₂ e / σ) >>=ᶜ fun mσ =>
  Counted.ops 1 (αk / C) >>=ᶜ fun βC =>
  -- step (5)
  Counted.ops 9 (q / σ ^ 2 * ((1 - σ * c) ^ 2 - σ ^ 2 * ℓ ^ 2)) >>=ᶜ fun ϑ =>
  Counted.ret ⟨p, q, κ, c, ℓ, σ, αk, C, (I₁.form.dsumForm I₂.form).dsumForm (CutForm.node C),
    Sum.elim mσ fun _ => 1, Sum.elim (Sum.elim I₁.β I₂.β) fun _ => βC, ϑ⟩

/-- The steps (2)-(5), counted, return the output of `def:reduction` (`output`) for a pair with
`0 ≤ T ≤ ∑_i a_i`, such as the pair after step (1) (`correct_step1`). -/
theorem stepsC_val (G : GadgetCost) (R : SubsetSum) (hT : 0 ≤ R.T) (hTA : R.T ≤ R.sumA) :
    (stepsC G R).val = R.output := by
  obtain ⟨J, hσ, hJ, hmin, hJle⟩ := σ_search R hT hTA
  simp only [stepsC, val_bind, Counted.val_ops, Counted.val_ret, Counted.val_sum, inputsC_val,
    nminC, combC, gadgetComb]
  rw [searchC_val R hJ hmin (show J < 6561 * R.Bg + 2 by omega), ← hσ]
  · rfl
  · exact fun s => Iff.rfl

/-- **The operations of the steps (2)-(5)** (the proof of `thm:nphard`,
`stoc-sections/appD-hardness.tex:1886-1887`), for a pair with `0 ≤ T ≤ ∑_i a_i`: with
`σ = 2^{−J}` and `J ≤ 6561Bg + 1` (`σ_search`), the steps take `4k + 3` operations in step (2)
(`H`, `μ`, `μ'`, `N_0` and `N_0 + T`), "Apart from the choice of `σ`, the steps (3) to (5) take
`O(k)` arithmetic operations": `10k + 47`, and "`σ` is found by as many comparisons": `10J + 9`
operations for the `J + 1` candidates, besides the four calls of the algorithm of `thm:gadget` (a
parameter here; counted in `ContractDesignPolymatroids/Hardness/GadgetCounts.lean`). -/
theorem stepsC_cost (G : GadgetCost) (R : SubsetSum) (hT : 0 ≤ R.T) (hTA : R.T ≤ R.sumA) :
    ∃ J : ℕ, R.σ = (1 / 2) ^ J ∧ J ≤ 6561 * R.Bg + 1 ∧
      (stepsC G R).cost = (4 * R.k + 3, 0, 0) + (10 * R.k + 47, 0, 0) + (10 * J + 9, 0, 0) +
        G.total R := by
  obtain ⟨J, hσ, hJ, hmin, hJle⟩ := σ_search R hT hTA
  refine ⟨J, hσ, hJle, ?_⟩
  have hk := R.one_le_k
  have hN₀ : max (gNmin R.μ R.k) (gNmin R.μ' R.k) = R.N₀ := rfl
  have hN₂ : R.N₀ + R.T.toNat = R.N₂ := rfl
  simp only [stepsC, cost_bind, Counted.val_ops, Counted.cost_ops, Counted.val_ret,
    Counted.cost_ret, Counted.val_sum, Counted.cost_sum, inputsC_val, inputsC_cost, nminC, combC,
    gadgetComb, hN₀, hN₂]
  rw [searchC_cost R hJ hmin (show J < 6561 * R.Bg + 2 by omega)]
  · simp only [GadgetCost.total, Fintype.card_sum, card_Gr, Fintype.card_unit, sum_const_zero,
      card_range]
    -- `ring`, not `omega`: the costs of the gadget are atoms that must not be unfolded
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp only [Prod.fst_add, Prod.fst_zero, Nat.sub_add_cancel hk]
      ring
    · simp only [Prod.snd_add, Prod.fst_add, Prod.snd_zero, Prod.fst_zero]
      ring
    · simp only [Prod.snd_add, Prod.snd_zero]
      ring
  · exact fun s => Iff.rfl

/-! ### The reduction -/

/-- **The reduction of `def:reduction`, counted** (`stoc-sections/appD-hardness.tex:255-264`): step
(1) (`step1C`), then the steps (2)-(5) on the pair it returns (`stepsC`). It returns that pair and
the output. -/
def reductionC (G : GadgetCost) (P : SubsetSum) : Counted (Σ R : SubsetSum, Output R) :=
  step1C P >>=ᶜ fun R => stepsC G R >>=ᶜ fun o => Counted.ret ⟨R, o⟩

/-- **The operations of the reduction in the proof of `thm:nphard`**
(`stoc-sections/appD-hardness.tex:1885-1887`): "The reduction of `def:reduction` runs in time
polynomial in the encoding length of `(a, T)`." The counted reduction returns the pair `P.step1`
after step (1) and the output of the steps (2)-(5) as `ContractDesignPolymatroids/Hardness/Reduction.lean` defines it
(`output`: `p`, `q`, `κ*`, `c`, `ℓ`, `σ`, `α_∘`, `C`, the cut form `outForm`, `mHat`, `βHat` and
`ϑ`). With `σ = 2^{−J}`, `J ≤ 2^{31}⟨(a, T)⟩`, it takes exactly `k + 14k' + 10J + 61` arithmetic
operations (comparisons included) besides the four calls of the algorithm of `thm:gadget`, where
`k' ≤ k` is the number of items after step (1); so at most `2^{35}⟨(a, T)⟩`. Its minimizations and
evaluations are those of the calls of the gadget, whose cost is a parameter here (counted in
`ContractDesignPolymatroids/Hardness/GadgetCounts.lean`: `reductionC_gadget`).

The proof's steps: (1) step (1) takes `k + 2` operations (`step1C_cost`; not in the paper); (2) "the
algorithm of `thm:gadget` computes `N_0` and both combs in polynomial time": its cost is the
parameter `G`, and `H`, `μ`, `μ'`, `N_0` and `N_0 + T` take `4k' + 3` operations (`stepsC_cost`;
not in the paper); (3) "Apart from the choice of `σ`, the steps (3) to (5) take `O(k)` arithmetic
operations": `10k' + 47` (`stepsC_cost`); (4) "and `σ` is a power of `2` that is at least half the
smallest right-hand side in step (4), so `log(1/σ)` is polynomial and `σ` is found by as many
comparisons": `σ = 2^{−J}` with `J ≤ 6561Bg + 1 ≤ 2^{31}⟨(a, T)⟩` (`σ_search`, `Bg_le`,
`encLen_step1`), found after `J + 1` tests, `10J + 9` operations (`searchC_cost`); (5) the total,
with `k' ≤ k ≤ ⟨(a, T)⟩` (`step1_k_le`, `k_le_encLen`). -/
theorem reductionC_spec (G : GadgetCost) (P : SubsetSum) :
    (reductionC G P).val = ⟨P.step1, P.step1.output⟩ ∧
    ∃ J : ℕ, P.step1.σ = (1 / 2) ^ J ∧ J ≤ 2 ^ 31 * P.encLen ∧
      (reductionC G P).cost = (P.k + 14 * P.step1.k + 10 * J + 61, 0, 0) + G.total P.step1 ∧
      (reductionC G P).cost.1 ≤ 2 ^ 35 * P.encLen + (G.total P.step1).1 ∧
      (reductionC G P).cost.2 = (G.total P.step1).2 := by
  obtain ⟨hT, hTA, -⟩ := correct_step1 P
  -- (1) step (1): `k + 2` operations (`step1C_cost`), and it returns `P.step1` (`step1C_val`),
  -- a pair with `0 ≤ T ≤ ∑_i a_i` (`correct_step1`)
  have h1 := step1C_cost P
  -- (2) "the algorithm of `thm:gadget` computes `N_0` and both combs in polynomial time": the
  -- parameter `G`, and `4k' + 3` operations for `H`, `μ`, `μ'`, `N_0` and `N_0 + T`;
  -- (3) "Apart from the choice of `σ`, the steps (3) to (5) take `O(k)` arithmetic operations":
  -- `10k' + 47`; and the search, `10J + 9` (`stepsC_cost`, `stepsC_val`)
  obtain ⟨J, hσ, hJle, hcost⟩ := stepsC_cost G P.step1 hT hTA
  have hval : (reductionC G P).val = ⟨P.step1, P.step1.output⟩ := by
    show (⟨(step1C P).val, (stepsC G (step1C P).val).val⟩ : Σ R : SubsetSum, Output R) = _
    rw [step1C_val, stepsC_val G P.step1 hT hTA]
  -- (4) "so `log(1/σ)` is polynomial and `σ` is found by as many comparisons":
  -- `J ≤ 6561Bg + 1 ≤ 2^{31}⟨(a, T)⟩`
  have hBg := P.step1.Bg_le hTA
  have hE1 := encLen_step1 P
  obtain ⟨hkE, hE2⟩ := k_le_encLen P
  have hJ : J ≤ 2 ^ 31 * P.encLen := by
    rw [show (2 : ℕ) ^ 31 = 2147483648 by norm_num]
    omega
  -- (5) the total, with `k' ≤ k ≤ ⟨(a, T)⟩`
  have hk := step1_k_le P
  have hc : (reductionC G P).cost =
      (P.k + 14 * P.step1.k + 10 * J + 61, 0, 0) + G.total P.step1 := by
    show (step1C P).cost + ((stepsC G P.step1).cost + 0) = _
    rw [h1, hcost]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp only [Prod.fst_add, add_zero]
      ring
    · simp only [Prod.snd_add, Prod.fst_add, add_zero]
      ring
    · simp only [Prod.snd_add, add_zero]
      ring
  refine ⟨hval, J, hσ, hJ, hc, ?_, ?_⟩
  · rw [hc, Prod.fst_add, show (2 : ℕ) ^ 35 = 34359738368 by norm_num]
    dsimp only
    omega
  · rw [hc, Prod.snd_add]
    simp

end SubsetSum

end

end Hardness

end Stoc
