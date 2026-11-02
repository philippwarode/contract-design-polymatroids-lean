-- stamp r8 2026-11-02
import Mathlib
import ContractDesignPolymatroids.OptimalShare.Tracing
import ContractDesignPolymatroids.Subclasses.Partition
import ContractDesignPolymatroids.Subclasses.LaminarHeight

/-!
# Polymatroids with polynomially many breakpoints

The STOC version, Section 3 (`stoc-sections/06-optimal-share.tex`) and Appendix B.8
(`sec:A-subclasses`).

Proposition `rem:subclasses` (`stoc-sections/06-optimal-share.tex:83-85`): the number `B` of
breakpoints of `x*` in `(0, 1)` satisfies `B ≤ n` for partition polymatroids and
`B ≤ n + 2h(n + 1)|𝓛| 3^{h−1}` for laminar polymatroids of height `h` (`subclasses`). It has no
proof environment; its proof is the sentence before it (`06-optimal-share.tex:81`): (1) "The two
bounds follow from `prop:partition`, `thm:laminar`, respectively, in `sec:A-subclasses`"
(`subclasses_partition`, `subclasses_laminar`); (2) these bound the breakpoints in all of
`(0, ∞)`, and Appendix B.8 notes that this number "is at least the number of breakpoints in
`(0, 1)`, so the bounds below also hold for the `B` of `sec:bestresponse`"
(`appB-quadratic.tex:601-602`; `ncard_inter_Ioo_le`). That the bound for laminar polymatroids is
polynomial for `h = O(log n)`, which the overview of Section 3 attributes to `rem:subclasses`
(`05-best-response.tex:8`), is the second sentence of `thm:laminar` (`Stoc.laminar`).

The sentence before `rem:subclasses` (`stoc-sections/06-optimal-share.tex:80`), "For structured
polymatroids, polynomial bounds on `B` instead yield polynomial-time exact optimization via
`thm:pieces`": `Stoc.Tracing.tracing_of_ncard_le` (if at most `N` breakpoints, `alg:pieces` stops
after at most `(n + 2)²(N + 1)` iterations, each with one best-response computation, and returns an
optimal contract), and, for the classes of `rem:subclasses`, `Stoc.Tracing.polynomial_partition`
and `polynomial_laminar`. The work of an iteration (one water-filling computation and the procedure
of `lem:continuation`) is counted in `Stoc.Tracing.pieces_theorem`, without the arithmetic
operations.

Taken over on 2026-10-21 from `Paper/Subclasses/PolynomialClasses.lean` (the long paper's
`cor:polynomial-classes`) for the STOC version (`stoc.tex`); from then on this copy follows the STOC
version. Adapted on 2026-11-02 to Max Klimm's final STOC version (repository 429ca68), which keeps
only the partition and laminar polymatroids: `prop:A-subclasses` (equal rewards, chains,
`f(S) = g(|S|)`, multiples of matroid rank functions) and the results behind it are gone, and so is
their Lean (`EqualRewards.lean`, `LevelSetCount.lean`, `LevelSetClasses.lean`, `Sectors.lean`).
-/

namespace Stoc

open Finset

variable {E : Type*} [DecidableEq E]

/-- The breakpoints in `(0, 1)` are among those in `(0, ∞)`, which Appendix B.8 counts: "It is at
least the number of breakpoints in `(0, 1)`, so the bounds below also hold for the `B` of
`sec:bestresponse`" (`stoc-sections/appB-quadratic.tex:601-602`). -/
theorem ncard_inter_Ioo_le {s : Set ℝ} (hfin : s.Finite) : (s ∩ Set.Ioo 0 1).ncard ≤ s.ncard :=
  Set.ncard_le_ncard Set.inter_subset_left hfin

section Subclasses

variable [Fintype E] {f : Finset E → ℝ} {m β : E → ℝ}

/-- **`rem:subclasses`**, partition polymatroids: `B ≤ n` (`prop:partition`). -/
theorem subclasses_partition (hf : IsRankFunction f) (hpart : IsPartitionPolymatroid f)
    (hm : ∀ e, 0 ≤ m e) (hβ : ∀ e, 0 < β e) :
    (breakpoints (bestResponse f m β) ∩ Set.Ioo 0 1).ncard ≤ Fintype.card E :=
  (ncard_inter_Ioo_le (partition_breakpoints hf hpart hm hβ).1).trans
    (partition_breakpoints hf hpart hm hβ).2

/-- **`rem:subclasses`**, laminar polymatroids of height `h`: `B ≤ n + 2h(n + 1)|𝓛| 3^{h−1}`
(`thm:laminar`). -/
theorem subclasses_laminar (hf : IsRankFunction f) {𝓛 : Finset (Finset E)} (h𝓛 : IsLaminar 𝓛)
    (hP : indepPoly f = {x | (∀ e, 0 ≤ x e) ∧ ∀ L ∈ 𝓛, ∑ e ∈ L, x e ≤ f L})
    (hβ : ∀ e, 0 < β e) (hm : ∀ e, 0 ≤ m e) :
    (breakpoints (bestResponse f m β) ∩ Set.Ioo 0 1).ncard ≤
      Fintype.card E + 2 * height 𝓛 * (Fintype.card E + 1) * 𝓛.card * 3 ^ (height 𝓛 - 1) := by
  obtain ⟨hfin, hB, -⟩ := laminar hf h𝓛 hP hβ hm
  exact (ncard_inter_Ioo_le hfin).trans hB

/-- **`rem:subclasses`** (Proposition 3.11, `stoc-sections/06-optimal-share.tex:83-85`, proof
`:81`): the number `B` of breakpoints of `x*` in `(0, 1)` satisfies `B ≤ n` for partition
polymatroids and `B ≤ n + 2h(n + 1)|𝓛| 3^{h−1}` for laminar polymatroids with a family `𝓛` of
height `h`.

The STOC version's proof is the sentence before the proposition: (1) "The two bounds follow from
`prop:partition`, `thm:laminar`, respectively, in `sec:A-subclasses`" (`subclasses_partition`,
`subclasses_laminar`); (2) the two bound the breakpoints in `(0, ∞)`, whose number "is at least
the number of breakpoints in `(0, 1)`, so the bounds below also hold for the `B` of
`sec:bestresponse`" (`stoc-sections/appB-quadratic.tex:601-602`; `ncard_inter_Ioo_le`, inside each
part). -/
theorem subclasses (hf : IsRankFunction f) (hβ : ∀ e, 0 < β e) (hm : ∀ e, 0 ≤ m e) :
    (IsPartitionPolymatroid f →
      (breakpoints (bestResponse f m β) ∩ Set.Ioo 0 1).ncard ≤ Fintype.card E) ∧
    (∀ 𝓛 : Finset (Finset E), IsLaminar 𝓛 →
      indepPoly f = {x | (∀ e, 0 ≤ x e) ∧ ∀ L ∈ 𝓛, ∑ e ∈ L, x e ≤ f L} →
      (breakpoints (bestResponse f m β) ∩ Set.Ioo 0 1).ncard ≤
        Fintype.card E + 2 * height 𝓛 * (Fintype.card E + 1) * 𝓛.card * 3 ^ (height 𝓛 - 1)) :=
  ⟨fun hpart => subclasses_partition hf hpart hm hβ,
    fun _ h𝓛 hP => subclasses_laminar hf h𝓛 hP hβ hm⟩

end Subclasses

namespace Tracing

variable [Fintype E] {f : Finset E → ℝ} {m β : E → ℝ}

/-- The sentence before `rem:subclasses` (`stoc-sections/06-optimal-share.tex:80`), "For structured
polymatroids, polynomial bounds on `B` instead yield polynomial-time exact optimization via
`thm:pieces`": if at most `N` breakpoints lie in `(0, ∞)`, then at most `N` lie in `(0, 1)`, and
`alg:pieces` stops after at most `(n + 2)²(N + 1)` iterations, with the outcome of `thm:pieces`. -/
theorem tracing_of_ncard_le (H : Hyp f m β) {N : ℕ} (hN : (BP f m β).ncard ≤ N) :
    ∃ K ≤ (Fintype.card E + 2) ^ 2 * (N + 1), Outcome f m β K := by
  obtain ⟨K, hK, hout⟩ := tracing H
  have hB : (BP f m β ∩ Set.Ioo 0 1).ncard ≤ N :=
    (Set.ncard_le_ncard Set.inter_subset_left (bp_finite H)).trans hN
  exact ⟨K, hK.trans (Nat.mul_le_mul_left _ (by omega)), hout⟩

/-- The sentence before `rem:subclasses` (`stoc-sections/06-optimal-share.tex:80`) for partition
polymatroids: `B ≤ n` (`prop:partition`), so `alg:pieces` stops after at most `(n + 2)²(n + 1)`
iterations and returns an optimal contract (`tracing_of_ncard_le`). -/
theorem polynomial_partition (H : Hyp f m β) (hpart : IsPartitionPolymatroid f) :
    ∃ K ≤ (Fintype.card E + 2) ^ 2 * (Fintype.card E + 1), Outcome f m β K :=
  tracing_of_ncard_le H (partition_breakpoints H.rank hpart H.reward H.beta).2

/-- The sentence before `rem:subclasses` (`stoc-sections/06-optimal-share.tex:80`) for laminar
polymatroids of height `h`: `B ≤ n + 2h(n + 1)|𝓛|3^{h−1}` (`thm:laminar`) and `|𝓛| ≤ 2n − 1`, so
`alg:pieces` stops after at most `(n + 2)²(n + 2h(n + 1)(2n − 1)3^{h−1} + 1)` iterations, a
polynomial in `n` for fixed `h`, and returns an optimal contract (`tracing_of_ncard_le`). -/
theorem polynomial_laminar (H : Hyp f m β) {𝓛 : Finset (Finset E)} (h𝓛 : IsLaminar 𝓛)
    (hP : indepPoly f = {x | (∀ e, 0 ≤ x e) ∧ ∀ L ∈ 𝓛, ∑ e ∈ L, x e ≤ f L}) :
    ∃ K ≤ (Fintype.card E + 2) ^ 2 * (Fintype.card E +
      2 * height 𝓛 * (Fintype.card E + 1) * (2 * Fintype.card E - 1) * 3 ^ (height 𝓛 - 1) + 1),
      Outcome f m β K :=
  tracing_of_ncard_le H (laminar H.rank h𝓛 hP H.beta H.reward).2.2.2.1

end Tracing

end Stoc
