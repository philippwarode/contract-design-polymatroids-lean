-- stamp r7 2026-11-02
import ContractDesignPolymatroids.Approximation.PRule
import ContractDesignPolymatroids.BestResponse.WaterFilling

/-!
# The scheme for homogeneous costs, the FPTAS for quadratic costs and the half rule

The STOC version's Section 5.1 (`sec:fptas-quadratic`, 08-approximation.tex:25-45) after
`thm:prule`, with the proofs in Appendix D (appE-halfrule.tex:27-37):

* `fptashom` (`cor:fptashom`): for costs homogeneous of degree `p > 1` on a compact convex
  `K ⊆ ℝ^E_{≥0}` containing zero, a `(1 − ε)`-optimal contract is found with
  `O(1 + ε⁻¹ log(p/(p − 1)))` exact best-response calls, at shares that do not depend on the
  instance ("Combining `thm:fptas,thm:prule` gives the following guarantee",
  08-approximation.tex:35). Its proof, with what "Substituting this bound into `thm:fptas` gives",
  the shares, their number and their bit length, is `fptashom_aux`.
* `fptasquad` (`cor:fptasquad`): for quadratic costs with rational data, on explicitly described
  rational polytopes containing zero (`ratPolytope`) and on value-oracle polymatroids, with the
  shares of `cor:fptashom` for `p = 2` ("Taking `p = 2` therefore gives the following runtime
  guarantees", 08-approximation.tex:40).
* `halfrule`: the half rule, the case `p = 2` of `thm:prule` for quadratic costs on `P₊(f)`, which
  the introduction, the abstract and the caption of `fig:intro` state (not in the paper as a
  result).

The model's reward of success `r̄` (02-preliminaries.tex:12) is not used by these results and is
not a parameter of their Lean statements (see `ContractDesignPolymatroids/Approximation/Agent.lean`).

Taken over on 2026-10-20 from `Research/S05/StarShaped.lean` (series 05, `thm:starshaped` and
`cor:alphahalf`) for the STOC version (`stoc.tex`); from then on this copy follows the STOC
version, which since b90de56 proves the half rule as the case `p = 2` of `thm:prule` and since
429ca68 states it only in the introduction, the abstract and the caption of `fig:intro`.
-/

namespace Stoc

open Finset Stoc.Convex

noncomputable section

variable {E : Type*} [Fintype E]

/-- With `ᾱ = 1/p`, `1/(1 − ᾱ) = p/(p − 1)`. -/
lemma one_div_one_sub_inv {p : ℝ} (hp : 1 < p) : 1 / (1 - 1 / p) = p / (p - 1) := by
  have hp0 : p ≠ 0 := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  field_simp

/-- A continuous reward is bounded above on a compact action set by a positive number (not in the
paper: the model gives the reward bound `r̄ > 0`, 02-preliminaries.tex:12, which an exact
best-response oracle on a compact action set `K` has, `IsExactOracle.bounded`). -/
lemma exists_rbar {K : Set (E → ℝ)} (hKc : IsCompact K) (m : E → ℝ) :
    ∃ rb > 0, ∀ x ∈ K, reward m x ≤ rb := by
  obtain ⟨B, hB⟩ := hKc.bddAbove_image (continuous_reward m).continuousOn
  refine ⟨max B 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun x hx => ?_⟩
  exact (hB (Set.mem_image_of_mem _ hx)).trans (le_max_left _ _)

/-! ### `cor:fptashom` -/

/-- **`cor:fptashom`** with what its proof gives: "Substituting this bound into `thm:fptas` gives
the shares, their number and their bit length" (appE-halfrule.tex:29). For `p > 1` and `ε ∈ (0, 1)`,
there is a list `Q` of at most `⌈2ε⁻¹ ln(p/(p − 1))⌉ + 1` shares, dyadic rationals in `[0, 1]` with
`s ≤ 3 + log₂(1/ε) + log₂(p/(p − 1))` bits (those of `thm:fptas` for `ᾱ = 1/p`), such that for costs
homogeneous of degree `p` on every compact convex `K ⊆ ℝ^E_{≥0}` with `0 ∈ K` and rewards `m ≥ 0`,
every share of `Q` with the largest utility `(1 − q) r(x*(q))` is `(1 − ε)`-optimal. The exact
statement `fptashom` follows from it, and the proof of `cor:fptasquad` ("Apply `cor:fptashom` with
`p = 2`") takes this form, as it uses the bit length of the shares ("each with `O(1 + log(1/ε))`
bits", appE-halfrule.tex:34).

The proof (appE-halfrule.tex:28-30): (1) "By `thm:prule`, `ᾱ = 1/p` is a share bound"
(`PRule.prule`); (2) "Substituting this bound into `thm:fptas` gives the shares, their number and
their bit length" (`fptas` with `ᾱ = 1/p`, and `1/(1 − 1/p) = p/(p − 1)`, `one_div_one_sub_inv`;
the exact best-response oracle is `IsExactOracle`, whose reward bound `r̄` is `exists_rbar`);
(3) "Evaluate `(1 − α) r(x*(α))` at each share and return one with the largest value". -/
theorem fptashom_aux {p : ℝ} (hp : 1 < p) {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ Q : List ℝ, Q ≠ [] ∧ Q.length ≤ ⌈2 / ε * Real.log (p / (p - 1))⌉₊ + 1 ∧
      (∃ s : ℕ, (s : ℝ) ≤ 3 + Real.logb 2 (1 / ε) + Real.logb 2 (p / (p - 1)) ∧
        ∀ q ∈ Q, q ∈ Set.Icc (0 : ℝ) 1 ∧ IsDyadic s q) ∧
      ∀ (K : Set (E → ℝ)) (m : E → ℝ) (c : (E → ℝ) → ℝ), IsCompact K → Convex ℝ K →
        (∀ x ∈ K, 0 ≤ x) → (0 : E → ℝ) ∈ K → (∀ e, 0 ≤ m e) → PRule.IsHomogeneous p c →
        ∀ xs : ℝ → E → ℝ, (∀ α ∈ Set.Icc (0 : ℝ) 1, IsPBR K m c α (xs α)) →
          ∀ q ∈ Q, (∀ q' ∈ Q, profit (fun α => reward m (xs α)) q' ≤
              profit (fun α => reward m (xs α)) q) →
            IsApproxOptimal (profit fun α => reward m (xs α)) ε q := by
  have hp0 : 0 ≤ 1 / p := by apply div_nonneg zero_le_one; linarith
  have hplt : 1 / p < 1 := by rw [div_lt_one (by linarith)]; exact hp
  -- (1) "By `thm:prule`, `ᾱ = 1/p` is a share bound." (for every instance, below)
  -- (2) "Substituting this bound into `thm:fptas` gives the shares, their number and their bit
  -- length."
  obtain ⟨Q, hne, hlen, ⟨s, hs, hQ⟩, hguar⟩ := fptas (E := E) hε ⟨hp0, hplt⟩
  rw [one_div_one_sub_inv hp] at hlen hs
  refine ⟨Q, hne, hlen, ⟨s, hs, hQ⟩, fun K m c hKc hK hKnn h0 hm hc xs hxs => ?_⟩
  -- (1) on this instance
  have hsb := (PRule.prule hKc hK hKnn h0 hm hc hp).1 xs hxs
  -- (3) "Evaluate `(1 − α) r(x*(α))` at each share and return one with the largest value."
  exact hguar K m c xs ⟨⟨0, h0⟩, hKnn, hm, hc.toIsCost, exists_rbar hKc m, hxs⟩ hsb

/-- **`cor:fptashom`** (Corollary 5.4; 08-approximation.tex:36-38, proof appE-halfrule.tex:28-30):
"For homogeneous costs of degree `p > 1` on a compact convex set `K ⊆ ℝ^E_{≥0}` containing zero, a
`(1 − ε)`-optimal contract can be found with `O(1 + ε⁻¹ log(p/(p − 1)))` exact best-response calls,
for every `ε ∈ (0, 1)`. For fixed `p`, this is `O(1/ε)` calls."

Here: for `p > 1` and `ε ∈ (0, 1)` there is a list `Q` of at most
`2(1 + ε⁻¹ ln(p/(p − 1)))` shares, and so at most `2(1 + ln(p/(p − 1)))/ε` of them, such that for
costs homogeneous of degree `p` (`PRule.IsHomogeneous`) on every compact convex `K ⊆ ℝ^E_{≥0}` with
`0 ∈ K`, rewards `m ≥ 0` and every choice of the best responses `x*(α)` of the model (`IsPBR`), the
answers of the exact best-response oracle, every share of `Q` with the largest utility
`U_P(q) = (1 − q) r(x*(q))` is `(1 − ε)`-optimal. The scheme calls the oracle at the shares of `Q`,
which do not depend on the instance (see `ContractDesignPolymatroids/Approximation/Scheme.lean`).

The proof is `fptashom_aux`, whose count `⌈2ε⁻¹ ln(p/(p − 1))⌉ + 1` is at most
`2(1 + ε⁻¹ ln(p/(p − 1)))`, and at most `2(1 + ln(p/(p − 1)))/ε` as `ε < 1` (the `O`, not in the
paper). -/
theorem fptashom {p : ℝ} (hp : 1 < p) {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ Q : List ℝ, Q ≠ [] ∧ (Q.length : ℝ) ≤ 2 * (1 + 1 / ε * Real.log (p / (p - 1))) ∧
      (Q.length : ℝ) ≤ 2 * (1 + Real.log (p / (p - 1))) / ε ∧
      (∀ q ∈ Q, q ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ (K : Set (E → ℝ)) (m : E → ℝ) (c : (E → ℝ) → ℝ), IsCompact K → Convex ℝ K →
        (∀ x ∈ K, 0 ≤ x) → (0 : E → ℝ) ∈ K → (∀ e, 0 ≤ m e) → PRule.IsHomogeneous p c →
        ∀ xs : ℝ → E → ℝ, (∀ α ∈ Set.Icc (0 : ℝ) 1, IsPBR K m c α (xs α)) →
          ∀ q ∈ Q, (∀ q' ∈ Q, profit (fun α => reward m (xs α)) q' ≤
              profit (fun α => reward m (xs α)) q) →
            IsApproxOptimal (profit fun α => reward m (xs α)) ε q := by
  obtain ⟨Q, hne, hlen, ⟨s, -, hQ⟩, hguar⟩ := fptashom_aux (E := E) hp hε
  set L := Real.log (p / (p - 1)) with hLdef
  have hε0 := hε.1
  have hL : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
  have hceil : (⌈2 / ε * L⌉₊ : ℝ) ≤ 2 / ε * L + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hlenR : (Q.length : ℝ) ≤ ⌈2 / ε * L⌉₊ + 1 := by exact_mod_cast hlen
  -- the `O(1 + ε⁻¹ log(p/(p − 1)))`
  have h1 : (Q.length : ℝ) ≤ 2 * (1 + 1 / ε * L) := by
    have e : 2 / ε * L = 2 * (1 / ε * L) := by ring
    linarith
  -- "For fixed `p`, this is `O(1/ε)` calls": `1 ≤ 1/ε`
  have h2 : (Q.length : ℝ) ≤ 2 * (1 + L) / ε := by
    have hε1 : 1 ≤ 1 / ε := by rw [le_div_iff₀ hε0]; linarith [hε.2]
    have e : 2 * (1 + L) / ε = 2 * (1 / ε) + 2 * (1 / ε * L) := by ring
    rw [e]
    linarith
  exact ⟨Q, hne, h1, h2, fun q hq => (hQ q hq).1, hguar⟩

/-! ### `cor:fptasquad` -/

/-- The polytope `K = {x ∈ ℝ^E_{≥0} : A x ≤ b}` of a rational system of inequalities with the rows
`A i` and the right-hand sides `b i`: an explicitly described rational polytope `K ⊆ ℝ^E_{≥0}`
(`cor:fptasquad`, 08-approximation.tex:42) when it is bounded. -/
def ratPolytope {ι : Type*} [Fintype ι] (A : ι → E → ℚ) (b : ι → ℚ) : Set (E → ℝ) :=
  {x | 0 ≤ x ∧ ∀ i, ∑ e, (A i e : ℝ) * x e ≤ (b i : ℝ)}

section Polytope

variable {ι : Type*} [Fintype ι] (A : ι → E → ℚ) (b : ι → ℚ)

lemma convex_ratPolytope : Convex ℝ (ratPolytope A b) := by
  intro x hx y hy a c ha hc hac
  refine ⟨fun e => ?_, fun i => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact add_nonneg (mul_nonneg ha (hx.1 e)) (mul_nonneg hc (hy.1 e))
  · have h1 := hx.2 i
    have h2 := hy.2 i
    have e : ∑ e, (A i e : ℝ) * (a • x + c • y) e =
        a * ∑ e, (A i e : ℝ) * x e + c * ∑ e, (A i e : ℝ) * y e := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun e _ => by ring
    rw [e]
    have : a * ∑ e, (A i e : ℝ) * x e + c * ∑ e, (A i e : ℝ) * y e ≤ a * b i + c * b i :=
      add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hc)
    rw [← add_mul, hac, one_mul] at this
    exact this

lemma isClosed_ratPolytope : IsClosed (ratPolytope A b) := by
  have h1 : IsClosed {x : E → ℝ | 0 ≤ x} := isClosed_le continuous_const continuous_id
  have h2 : IsClosed {x : E → ℝ | ∀ i, ∑ e, (A i e : ℝ) * x e ≤ (b i : ℝ)} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le
      (continuous_finsetSum _ fun e _ => continuous_const.mul (continuous_apply e))
      continuous_const
  rw [ratPolytope, Set.ofPred_and]
  exact h1.inter h2

/-- An explicitly described rational polytope is compact (not in the paper: a polytope is bounded
and closed). -/
lemma isCompact_ratPolytope (hbd : Bornology.IsBounded (ratPolytope A b)) :
    IsCompact (ratPolytope A b) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_ratPolytope A b) hbd

end Polytope

/-- **`cor:fptasquad`** (Corollary 5.5, 08-approximation.tex:41-43, proof appE-halfrule.tex:33-37):
"For quadratic costs with rational data and `ε ∈ (0, 1)`, a `(1 − ε)`-optimal contract can be
computed by an FPTAS on explicitly described rational polytopes `K ⊆ ℝ^E_{≥0}` containing zero. On
value-oracle polymatroids, its runtime is `O(n⁷ log n/ε)·FO + O(n⁸ log n/ε)`."

What is formalised, for `ε ∈ (0, 1)`: the scheme of `cor:fptashom` with `p = 2`, a list `Q` of at
most `⌈2ε⁻¹ ln 2⌉ + 1` shares (`O(1/ε)`), each a dyadic rational in `[0, 1]` with
`s ≤ 4 + log₂(1/ε)` bits (`O(1 + log(1/ε))`), which do not depend on the instance, and
(a) on every explicitly described rational polytope `K = {x ∈ ℝ^E_{≥0} : A x ≤ b}` (`ratPolytope`,
bounded) with `0 ∈ K`, for quadratic costs `c(x) = ∑_e β_e x_e²/2` (`quadCost`) with rational data
`m ≥ 0`, `β > 0`, `A` and `b`: the best response is unique at every share in `[0, 1]`, and every
share of `Q` with the largest utility `(1 − q) r(x*(q))` is `(1 − ε)`-optimal;
(b) on every polymatroid `P₊(f)` (a rank function `f`, accessed by its values) with rational
`m ≥ 0` and `β > 0`: every share of `Q` with the largest utility is `(1 − ε)`-optimal, water-filling
computes the best response `x*(q)` at every share `q ∈ Q` (`WaterFilling.waterFill`, by
`thm:waterfilling`), and summed over `Q` it makes at most `(⌈2ε⁻¹ ln 2⌉ + 1)·2n(n + 1)` submodular
minimizations (`WaterFilling.oracleCalls`) and at most `(⌈2ε⁻¹ ln 2⌉ + 1)·2n(2n + 1)` further
evaluations of `f` (`WaterFilling.fEvals`, the accounting of `thm:waterfilling`), with `n = |E|`.
Not formalised: the running times, that is, rational convex quadratic programming in polynomial time
[KTK80], the polynomial bound in the encoding length, the time `O(n⁷ log n)·FO + O(n⁸ log n)` of a
best response by `thm:waterfilling` (Iwata and Orlin's algorithm), the `O(n)` operations for each
reward, and the total runtime.

The proof (appE-halfrule.tex:34-36): (1) "Apply `cor:fptashom` with `p = 2`" (`fptashom_aux`, the
corollary with the bit length of the shares, for the quadratic costs, which are homogeneous of
degree `2`, `PRule.isHomogeneous_quadCost`); (2) "On an explicitly described rational polytope, the
unique best response minimizes the strictly convex quadratic function `∑_e β_e x_e²/2 − α mᵀx` over
`K`" (`IsBestResponse.unique`; it exists as `K` is compact, `isCompact_ratPolytope`); (3) "Rational
convex quadratic programming computes this response exactly in polynomial time [KTK80], and its
reward is evaluated exactly" (not formalised); (4) "The grid has `O(1/ε)` shares, each with
`O(1 + log(1/ε))` bits, so the total running time is polynomial in the input encoding length and in
`1/ε`" (the count and the bits; the time is not formalised); (5) "For a polymatroid, each of the
`O(1/ε)` best responses takes time `O(n⁷ log n)·FO + O(n⁸ log n)` by `thm:waterfilling`"
(`WaterFilling.waterfilling`, with its counts; `P₊(f)` is a compact convex set containing zero, and
the best response `x*(α)` of the quadratic model is the model's, `isPBR_bestResponse`); (6)
"Evaluating the reward takes `O(n)` further operations per response, so the total runtime is
`O(n⁷ log n/ε)·FO + O(n⁸ log n/ε)`" (not formalised; the counts are summed over the shares). -/
theorem fptasquad [DecidableEq E] {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ Q : List ℝ, Q ≠ [] ∧ Q.length ≤ ⌈2 / ε * Real.log 2⌉₊ + 1 ∧
      (∃ s : ℕ, (s : ℝ) ≤ 4 + Real.logb 2 (1 / ε) ∧
        ∀ q ∈ Q, q ∈ Set.Icc (0 : ℝ) 1 ∧ IsDyadic s q) ∧
      (∀ {ι : Type} [Fintype ι] (A : ι → E → ℚ) (b : ι → ℚ) (m β : E → ℚ),
        Bornology.IsBounded (ratPolytope A b) → (0 : E → ℝ) ∈ ratPolytope A b →
        (∀ e, 0 ≤ m e) → (∀ e, 0 < β e) →
        (∀ α ∈ Set.Icc (0 : ℝ) 1, ∃! x, IsBR (ratPolytope A b) (fun e => (m e : ℝ))
          (quadCost fun e => (β e : ℝ)) α x) ∧
        ∀ xs : ℝ → E → ℝ, (∀ α ∈ Set.Icc (0 : ℝ) 1, IsBR (ratPolytope A b)
            (fun e => (m e : ℝ)) (quadCost fun e => (β e : ℝ)) α (xs α)) →
          ∀ q ∈ Q, (∀ q' ∈ Q, profit (fun α => reward (fun e => (m e : ℝ)) (xs α)) q' ≤
              profit (fun α => reward (fun e => (m e : ℝ)) (xs α)) q) →
            IsApproxOptimal (profit fun α => reward (fun e => (m e : ℝ)) (xs α)) ε q) ∧
      ∀ (f : Finset E → ℝ) (m β : E → ℚ), IsRankFunction f → (∀ e, 0 ≤ m e) →
        (∀ e, 0 < β e) →
        (∀ q ∈ Q, (∀ q' ∈ Q, profit (grossValue f (fun e => (m e : ℝ)) fun e => (β e : ℝ)) q' ≤
            profit (grossValue f (fun e => (m e : ℝ)) fun e => (β e : ℝ)) q) →
          IsApproxOptimal (profit (grossValue f (fun e => (m e : ℝ)) fun e => (β e : ℝ))) ε q) ∧
        (∀ q ∈ Q, WaterFilling.waterFill f (fun e => (m e : ℝ)) (fun e => (β e : ℝ)) q =
          bestResponse f (fun e => (m e : ℝ)) (fun e => (β e : ℝ)) q) ∧
        (Q.map (WaterFilling.oracleCalls f (fun e => (m e : ℝ)) fun e => (β e : ℝ))).sum ≤
          (⌈2 / ε * Real.log 2⌉₊ + 1) * (2 * Fintype.card E * (Fintype.card E + 1)) ∧
        (Q.map (WaterFilling.fEvals f (fun e => (m e : ℝ)) fun e => (β e : ℝ))).sum ≤
          (⌈2 / ε * Real.log 2⌉₊ + 1) * (2 * Fintype.card E * (2 * Fintype.card E + 1)) := by
  -- (1) "Apply `cor:fptashom` with `p = 2`."
  obtain ⟨Q, hne, hlen, ⟨s, hs, hQ⟩, hguar⟩ := fptashom_aux (E := E) one_lt_two hε
  have e2 : (2 : ℝ) / (2 - 1) = 2 := by norm_num
  rw [e2] at hlen hs
  have hs' : (s : ℝ) ≤ 4 + Real.logb 2 (1 / ε) := by
    rw [Real.logb_self_eq_one one_lt_two] at hs
    linarith
  refine ⟨Q, hne, hlen, ⟨s, hs', hQ⟩, fun A b m β hbd h0 hm hβ => ?_, fun f m β hf hm hβ => ?_⟩
  · -- (2) "On an explicitly described rational polytope, the unique best response minimizes the
    -- strictly convex quadratic function `∑_e β_e x_e²/2 − α mᵀx` over `K`."
    set K := ratPolytope A b with hKdef
    have hKc : IsCompact K := isCompact_ratPolytope A b hbd
    have hK : Convex ℝ K := convex_ratPolytope A b
    have hKnn : ∀ x ∈ K, 0 ≤ x := fun x hx => hx.1
    have hm' : ∀ e, 0 ≤ (m e : ℝ) := fun e => Rat.cast_nonneg.2 (hm e)
    have hβ' : ∀ e, 0 < (β e : ℝ) := fun e => Rat.cast_pos.2 (hβ e)
    have hcont : ContinuousOn (quadCost fun e => (β e : ℝ)) K :=
      (PRule.isHomogeneous_quadCost fun e => (hβ' e).le).continuousOn.mono fun x hx => hKnn x hx
    have huniq : ∀ α ∈ Set.Icc (0 : ℝ) 1, ∀ x y, IsBR K (fun e => (m e : ℝ))
        (quadCost fun e => (β e : ℝ)) α x → IsBR K (fun e => (m e : ℝ))
        (quadCost fun e => (β e : ℝ)) α y → x = y := fun α _ x y hx hy =>
      (isBR_quadCost_iff.1 hx).unique hK hβ' (isBR_quadCost_iff.1 hy)
    refine ⟨fun α hα => ?_, fun xs hxs => ?_⟩
    · obtain ⟨x, hx⟩ := exists_isBR (m := fun e => (m e : ℝ)) hKc ⟨0, h0⟩ hcont α
      exact ⟨x, hx, fun y hy => huniq α hα y x hy hx⟩
    -- (3) "Rational convex quadratic programming computes this response exactly in polynomial time
    -- [KTK80], and its reward is evaluated exactly." (not formalised) (4) "The grid has `O(1/ε)`
    -- shares, each with `O(1 + log(1/ε))` bits, so the total running time is polynomial in the
    -- input encoding length and in `1/ε`." (the count and the bits; the time is not formalised) The
    -- unique best responses are those of the model (`IsPBR`).
    have hpbr : ∀ α ∈ Set.Icc (0 : ℝ) 1, IsPBR K (fun e => (m e : ℝ))
        (quadCost fun e => (β e : ℝ)) α (xs α) := fun α hα =>
      ⟨hxs α hα, fun y hy => by rw [huniq α hα y (xs α) hy (hxs α hα)]⟩
    exact hguar K _ _ hKc hK hKnn h0 hm' (PRule.isHomogeneous_quadCost fun e => (hβ' e).le) xs
      hpbr
  · -- (5) "For a polymatroid, each of the `O(1/ε)` best responses takes time
    -- `O(n⁷ log n)·FO + O(n⁸ log n)` by `thm:waterfilling`."
    set m' : E → ℝ := fun e => (m e : ℝ) with hm'def
    set β' : E → ℝ := fun e => (β e : ℝ) with hβ'def
    have hm' : ∀ e, 0 ≤ m' e := fun e => Rat.cast_nonneg.2 (hm e)
    have hβ' : ∀ e, 0 < β' e := fun e => Rat.cast_pos.2 (hβ e)
    -- `P₊(f)` is a compact convex set containing zero, and the best response `x*(α)` of the
    -- quadratic model is the model's
    have hopt := hguar (indepPoly f) m' (quadCost β') (isCompact_indepPoly f) (convex_indepPoly f)
      (fun _ hx => hx.1) (zero_mem_indepPoly hf) hm'
      (PRule.isHomogeneous_quadCost fun e => (hβ' e).le) (fun α => bestResponse f m' β' α)
      (fun α _ => isPBR_bestResponse hf hβ' α)
    have hwf : ∀ q ∈ Q, WaterFilling.waterFill f m' β' q = bestResponse f m' β' q ∧
        WaterFilling.oracleCalls f m' β' q ≤ 2 * Fintype.card E * (Fintype.card E + 1) ∧
        WaterFilling.fEvals f m' β' q ≤ 2 * Fintype.card E * (2 * Fintype.card E + 1) :=
      fun q hq => WaterFilling.waterfilling ⟨hf, hβ', hm', (hQ q hq).1.1⟩
    -- (6) "Evaluating the reward takes `O(n)` further operations per response, so the total runtime
    -- is `O(n⁷ log n/ε)·FO + O(n⁸ log n/ε)`." (not formalised; the counts summed over the shares)
    refine ⟨hopt, fun q hq => (hwf q hq).1, ?_, ?_⟩
    · calc (Q.map (WaterFilling.oracleCalls f m' β')).sum
          ≤ (Q.map fun _ => 2 * Fintype.card E * (Fintype.card E + 1)).sum :=
            List.sum_le_sum fun q hq => (hwf q hq).2.1
        _ = Q.length * (2 * Fintype.card E * (Fintype.card E + 1)) := by
            rw [List.map_const', List.sum_replicate, smul_eq_mul]
        _ ≤ (⌈2 / ε * Real.log 2⌉₊ + 1) * (2 * Fintype.card E * (Fintype.card E + 1)) :=
            Nat.mul_le_mul_right _ hlen
    · calc (Q.map (WaterFilling.fEvals f m' β')).sum
          ≤ (Q.map fun _ => 2 * Fintype.card E * (2 * Fintype.card E + 1)).sum :=
            List.sum_le_sum fun q hq => (hwf q hq).2.2
        _ = Q.length * (2 * Fintype.card E * (2 * Fintype.card E + 1)) := by
            rw [List.map_const', List.sum_replicate, smul_eq_mul]
        _ ≤ (⌈2 / ε * Real.log 2⌉₊ + 1) * (2 * Fintype.card E * (2 * Fintype.card E + 1)) :=
            Nat.mul_le_mul_right _ hlen

/-! ### The half rule -/

/-- The half rule, the case `p = 2` of `thm:prule`, for quadratic costs `c(x) = ∑_e β_e x_e²/2` with
`β > 0` on `P₊(f)`: `1/2` is a share bound, and `U_P` is nonincreasing on `[1/2, 1]`, strictly
decreasing there if `r(z) > 0` for some `z ∈ P₊(f)`. Not in the paper as a result: the introduction
states it, "Nevertheless, a share of at most `1/2` suffices (`thm:prule`)" (01-introduction.tex:23),
as do the abstract ("an optimal contract for quadratic costs always exists with a share of at most
`1/2`", abstract.tex:4) and the caption of `fig:intro` ("By our share bound (`thm:prule`), `U_P` is
decreasing on the shaded interval `[1/2, 1]`", fig-intro.tex:63); Section 5 no longer takes `p = 2`
in `thm:prule` (the earlier version's sentence "Taking `p = 2` in `thm:prule` gives the half rule on
every compact convex action set containing zero, including `P₊(f)`" is gone). The proof takes
`thm:prule` (`PRule.prule`) and the steps (1)–(9) of its proof with `p = 2`, as quadratic costs are
homogeneous of degree `2` (`PRule.isHomogeneous_quadCost`) and `P₊(f)` is a compact convex set
containing zero; the best response is that of the quadratic model (`isPBR_bestResponse`). -/
theorem halfrule [DecidableEq E] {f : Finset E → ℝ} (hf : IsRankFunction f) {m β : E → ℝ}
    (hm : ∀ e, 0 ≤ m e) (hβ : ∀ e, 0 < β e) :
    IsShareBound (profit (grossValue f m β)) (1 / 2) ∧
    AntitoneOn (profit (grossValue f m β)) (Set.Icc (1 / 2) 1) ∧
    ((∃ z ∈ indepPoly f, 0 < reward m z) →
      StrictAntiOn (profit (grossValue f m β)) (Set.Icc (1 / 2) 1)) := by
  have hKc := isCompact_indepPoly f
  have hK := convex_indepPoly f
  have hKnn : ∀ x ∈ indepPoly f, 0 ≤ x := fun _ hx => hx.1
  have h0 := zero_mem_indepPoly hf
  have hc := PRule.isHomogeneous_quadCost fun e => (hβ e).le
  have hxs : ∀ α, IsPBR (indepPoly f) m (quadCost β) α (bestResponse f m β α) :=
    fun α => isPBR_bestResponse hf hβ α
  -- `thm:prule` with `p = 2`
  have hsb := (PRule.prule hKc hK hKnn h0 hm hc one_lt_two).1 (fun α => bestResponse f m β α)
    fun α _ => hxs α
  -- steps (1)–(8) of its proof with `p = 2`
  have h15 : ∀ α α', 0 < α → α < α' → reward m (bestResponse f m β α') ≤
      (α' / α) ^ (1 / ((2 : ℝ) - 1)) * reward m (bestResponse f m β α) :=
    fun α α' hα hαα' => PRule.reward_le_rpow_mul hc one_lt_two hKc hK hKnn h0 hα hαα' (hxs α).isBR
      (hxs α').isBR
  have hR := PRule.antitoneOn_ratio h15
  have hR0 : ∀ α, 0 < α → 0 ≤ PRule.ratio 2 m (fun α => bestResponse f m β α) α :=
    fun α hα => PRule.ratio_nonneg _ hKnn hm hα (hxs α).isBR.1
  have hU := PRule.profit_antitoneOn (fun α => bestResponse f m β α) one_lt_two hR hR0
  -- step (9) of its proof with `p = 2`
  refine ⟨hsb, hU, fun ⟨z, hz, hrz⟩ => ?_⟩
  exact PRule.profit_strictAntiOn (fun α => bestResponse f m β α) hc one_lt_two hK hKnn h0
    (fun α _ => (hxs α).isBR) hR hz hrz

end

end Stoc
