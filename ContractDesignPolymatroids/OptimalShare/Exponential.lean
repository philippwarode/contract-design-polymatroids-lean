-- stamp r10 2026-11-03
import Mathlib
import ContractDesignPolymatroids.OptimalShare.Tracing
import ContractDesignPolymatroids.OptimalShare.Pencil
import ContractDesignPolymatroids.OptimalShare.Network
import ContractDesignPolymatroids.Hardness.Operations

/-!
# Exponentially many breakpoints

The STOC version, Section 3 (`stoc-sections/06-optimal-share.tex`, the exponentially many
breakpoints), with the proofs in Appendix B.5 (`sec:A-expbp`): Theorem `thm:alm` of Allman, Lo,
and McCormick, Lemma `lem:embed`, which Section 3 refers to and Appendix B.5 states and proves
after the proof of `thm:alm`, and Theorem `thm:expbp`; this file follows the appendix.
(`thm:levelsets` is `Stoc.levelsets` in `ContractDesignPolymatroids/BestResponse/LevelSets.lean`, and `lem:ops` (b) is
`Stoc.Hardness.ops_b_aux` in `ContractDesignPolymatroids/Hardness/Operations.lean`.)

* `thm:alm`: `Stoc.Exp.alm`, along the paper's proof from the network of Allman, Lo, and McCormick.
  Their Theorem 1.1, which the paper cites, is `Stoc.Network.almNetwork` (not in the paper), proved
  from the network of the proof of `thm:polybits` (ii) (`Stoc.Network.polybits_ii`); `f̃` is the
  cut function `cutFun` of the graph with the sink, and that a cut function with nonnegative
  capacities is nonnegative and submodular, for which the paper cites [Sch03, (44.16), (44.77)], is
  `cutFun_nonneg_submodular`;
* `lem:embed`: `Stoc.Exp.embed`, with `thm:levelsets` and the D3 lemma `monotone_of_insert`;
* `thm:expbp`: `Stoc.Exp.expbp`, with the step from the strict inequalities to a point off the
  breakpoints (`strict_near_point`, `exists_point_of_near`, the latter shared with the bound on
  `B_∞` in the proof of `thm:polybits`), the line-arrangement count `two_pow_le_cells` (also
  shared) and the dilation
  by `lem:ops` (b) (`Stoc.Hardness.ops_b_aux`). The D3 lemmas: `IsMaxMin.eq_of_unique`,
  `continuousAt_rho`, `cut_intervals`, `affine_of_no_bp` (with `affine_Icc_of_no_bp`),
  `Stoc.above_eq_of_mem_cell` and `Stoc.cells_finite_ncard_le` (`ContractDesignPolymatroids/OptimalShare/Pencil.lean`),
  `breakpoints_comp_div`, and `two_pow_div_sub_one_ge` (with `four_sq_le_two_pow`) for
  "which is `2^{n−O(log n)}`".

`thm:polybits` is in `ContractDesignPolymatroids/OptimalShare/PolyBit.lean`.

Taken over on 2026-10-20 from `Paper/OptimalShare/Exponential.lean` (the paper at Overleaf f035b19)
for the STOC version (`stoc.tex`); from then on this copy follows the STOC version.
-/

namespace Stoc

namespace Exp

open Finset Set

variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ### The theorem of Allman, Lo, and McCormick (`thm:alm`) -/

/-- `S ↦ f̃(S) − λ a(S) − θ b(S)`. -/
def tilt (ft : Finset E → ℝ) (a b : E → ℝ) (l θ : ℝ) (S : Finset E) : ℝ :=
  ft S - l * ∑ e ∈ S, a e - θ * ∑ e ∈ S, b e

/-- The cut function of the directed graph with the nodes `E` and a sink `s'`, with the arcs
`i → j` of capacity `u_ij` and `i → s'` of capacity `u'_i`: the total capacity
`∑_{i∈S} u_{is'} + ∑_{i∈S, j∈E∖S} u_ij` of the arcs that leave `S ⊆ E`. -/
def cutFun (u : E → E → ℝ) (u' : E → ℝ) (S : Finset E) : ℝ :=
  ∑ i ∈ S, u' i + ∑ i ∈ S, ∑ j ∈ univ \ S, u i j

/-- The cut function as a sum over all arcs: an arc `i → s'` counts if `i ∈ S`, an arc `i → j` if
`i ∈ S` and `j ∉ S`. -/
lemma cutFun_eq (u : E → E → ℝ) (u' : E → ℝ) (S : Finset E) :
    cutFun u u' S = ∑ i, ((if i ∈ S then u' i else 0) +
      ∑ j, if i ∈ S ∧ j ∉ S then u i j else 0) := by
  have h1 : ∑ i ∈ S, u' i = ∑ i, if i ∈ S then u' i else 0 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have h2 : ∀ i, ∑ j ∈ univ \ S, u i j = ∑ j, if j ∉ S then u i j else 0 := fun i => by
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp
  have h3 : ∑ i ∈ S, ∑ j ∈ univ \ S, u i j =
      ∑ i, ∑ j, if i ∈ S ∧ j ∉ S then u i j else 0 := by
    have h4 : ∑ i ∈ S, ∑ j ∈ univ \ S, u i j =
        ∑ i, if i ∈ S then ∑ j ∈ univ \ S, u i j else 0 := by
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [h4]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h2]
    by_cases hi : i ∈ S
    · simp [hi]
    · simp [hi]
  rw [cutFun, h1, h3, ← Finset.sum_add_distrib]

/-- A cut function of a directed graph with nonnegative capacities is nonnegative and submodular
(not in the paper: the proof of `thm:alm` cites [Sch03, (44.16), (44.77)] for the submodularity of a
cut function, and the nonnegativity holds as the capacities are nonnegative). By `cutFun_eq`, an arc
`i → s'` leaves `X ∪ Y` and `X ∩ Y` together as often as it leaves `X` and `Y`, and an arc `i → j`
at most as often. -/
theorem cutFun_nonneg_submodular {u : E → E → ℝ} {u' : E → ℝ} (hu : ∀ i j, 0 ≤ u i j)
    (hu' : ∀ i, 0 ≤ u' i) : (∀ S, 0 ≤ cutFun u u' S) ∧ Submodular (cutFun u u') := by
  refine ⟨fun S => add_nonneg (Finset.sum_nonneg fun i _ => hu' i)
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hu i j), fun X Y => ?_⟩
  simp only [cutFun_eq]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hsink : (if i ∈ X ∪ Y then u' i else 0) + (if i ∈ X ∩ Y then u' i else 0) =
      (if i ∈ X then u' i else 0) + (if i ∈ Y then u' i else 0) := by
    by_cases h1 : i ∈ X <;> by_cases h2 : i ∈ Y <;> simp [h1, h2]
  have harcs : (∑ j, if i ∈ X ∪ Y ∧ j ∉ X ∪ Y then u i j else 0) +
      (∑ j, if i ∈ X ∩ Y ∧ j ∉ X ∩ Y then u i j else 0) ≤
      (∑ j, if i ∈ X ∧ j ∉ X then u i j else 0) + (∑ j, if i ∈ Y ∧ j ∉ Y then u i j else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have := hu i j
    by_cases h1 : i ∈ X <;> by_cases h2 : i ∈ Y <;> by_cases h3 : j ∈ X <;>
      by_cases h4 : j ∈ Y <;> simp [h1, h2, h3, h4] <;> linarith
  linarith

/-- **`thm:alm`** (Theorem 3.8, Allman, Lo, and McCormick; statement
`stoc-sections/06-optimal-share.tex:58-60`, proof `stoc-sections/appB-quadratic.tex:518-534`). For
every `n ≥ 1` and `E = [n]` (here `Fin n`), there are `a, b ∈ ℝ^E_{>0}` and a submodular
`f̃ : 2^E → ℝ_{≥0}` with `f̃(∅) = 0` such that every `S ⊆ E` is the unique minimizer of
`f̃ − λ_S a − θ_S b` for some `(λ_S, θ_S) ∈ (0, 1)²`.

The paper's steps: (1) the network of Allman, Lo, and McCormick, with the source arcs
`a_j λ + b_j θ`, `a_j, b_j > 0`, and constant nonnegative capacities `u_ij` on the other arcs, in
which (2) every `S ⊆ E` is the unique minimum cut `{s} ∪ S` at some `(λ_S, θ_S) ∈ (0, 1)²`
(cited from [ALM22, Theorem 1.1]: here `Stoc.Network.almNetwork`, proved from the network of the
proof of `thm:polybits` (ii)); (3) the capacity of `{s} ∪ S` is
`λ a(E) + θ b(E) + f̃(S) − λ a(S) − θ b(S)` with
`f̃(S) = ∑_{i∈S} u_{is'} + ∑_{i∈S, j∈E∖S} u_ij` (`cutFun`); (4) so `S` is the unique minimizer of
`f̃ − λ_S a − θ_S b`; (5) `f̃` is a cut function of a directed graph with nonnegative capacities,
so it is nonnegative and submodular [Sch03, (44.16), (44.77)] (`cutFun_nonneg_submodular`), and
`f̃(∅) = 0`. -/
theorem alm (n : ℕ) (hn : 1 ≤ n) :
    ∃ (a b : Fin n → ℝ) (ft : Finset (Fin n) → ℝ), (∀ e, 0 < a e) ∧ (∀ e, 0 < b e) ∧
      Submodular ft ∧ (∀ S, 0 ≤ ft S) ∧ ft ∅ = 0 ∧
      ∀ S : Finset (Fin n), ∃ l θ : ℝ, l ∈ Ioo (0 : ℝ) 1 ∧ θ ∈ Ioo (0 : ℝ) 1 ∧
        ∀ T, T ≠ S → tilt ft a b l θ S < tilt ft a b l θ T := by
  -- (1) "The network of Allman, Lo, and McCormick has a source `s`, a sink `s'`, and the nodes
  -- `E` (we avoid the letter `t`, which denotes the vector `m_e/β_e`). The arcs `s → j` have
  -- capacity `a_j λ + b_j θ` with `a_j, b_j > 0`, and all other arcs have constant nonnegative
  -- capacities `u_ij`." (2) "Every `S ⊆ E` is the unique minimum cut `{s} ∪ S` at some point
  -- `(λ_S, θ_S) ∈ (0, 1)²` [ALM22, Theorem 1.1, with the network of Section 2]."
  obtain ⟨a, b, u, u', ha, hb, hu, hu', hcut⟩ := Network.almNetwork hn
  -- (3) "The capacity of the cut `{s} ∪ S` is `λ a(E∖S) + θ b(E∖S) + f̃(S)` with
  -- `f̃(S) := ∑_{i∈S} u_{is'} + ∑_{i∈S, j∈E∖S} u_ij`, that is, `λ a(E) + θ b(E)` plus
  -- `f̃(S) − λ a(S) − θ b(S)`."
  set ft : Finset (Fin n) → ℝ := cutFun u u'
  have hcap : ∀ l θ S, Network.cutCap a b u u' l θ S =
      l * ∑ e, a e + θ * ∑ e, b e + tilt ft a b l θ S := by
    intro l θ S
    have h1 := Finset.sum_sdiff (Finset.subset_univ S) (f := fun j => a j * l + b j * θ)
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul] at h1
    simp only [Network.cutCap, tilt, ft, cutFun, Finset.sum_add_distrib, ← Finset.sum_mul]
    linear_combination h1
  -- (4) "So `S` is the unique minimizer of `f̃ − λ_S a − θ_S b`."
  have huniq : ∀ S : Finset (Fin n), ∃ l θ : ℝ, l ∈ Ioo (0 : ℝ) 1 ∧ θ ∈ Ioo (0 : ℝ) 1 ∧
      ∀ T, T ≠ S → tilt ft a b l θ S < tilt ft a b l θ T := fun S => by
    obtain ⟨l, θ, hl, hθ, hS⟩ := hcut S
    refine ⟨l, θ, hl, hθ, fun T hT => ?_⟩
    have := hS T hT
    rw [hcap, hcap] at this
    linarith
  -- (5) "The function `f̃` is a cut function of a directed graph with nonnegative capacities, so it
  -- is nonnegative and submodular [Sch03, (44.16), (44.77)], and `f̃(∅) = 0`."
  obtain ⟨hnn, hsub⟩ := cutFun_nonneg_submodular hu hu'
  exact ⟨a, b, ft, ha, hb, hsub, hnn, by simp [ft, cutFun], huniq⟩

/-! ### The embedding (`lem:embed`) -/

/-- The rank function of `lem:embed`: `f(S) = f̃(S) + ∑_{e ∈ S} (Λ a_e − Θ b_e)`. -/
def embedF (ft : Finset E → ℝ) (a b : E → ℝ) (Λ Θ : ℝ) (S : Finset E) : ℝ :=
  ft S + ∑ e ∈ S, (Λ * a e - Θ * b e)

/-- `A` is the maximal minimizer of `g`: it minimizes `g` and contains every minimizer. -/
def IsMaxMin (g : Finset E → ℝ) (A : Finset E) : Prop :=
  (∀ S, g A ≤ g S) ∧ ∀ S, g S ≤ g A → S ⊆ A

omit [Fintype E] in
/-- A set function whose marginals are nonnegative is monotone (not in the paper: the proof of
`lem:embed` passes from nonnegative marginals to monotonicity without argument). -/
lemma monotone_of_insert {g : Finset E → ℝ} (h : ∀ S e, e ∉ S → g S ≤ g (insert e S)) :
    Monotone g := by
  have key : ∀ U S : Finset E, g S ≤ g (S ∪ U) := by
    intro U
    induction U using Finset.induction_on with
    | empty => intro S; simp
    | insert e U heU ih =>
      intro S
      calc g S ≤ g (S ∪ U) := ih S
        _ ≤ g (S ∪ insert e U) := by
          rw [Finset.union_insert]
          by_cases he : e ∈ S ∪ U
          · rw [Finset.insert_eq_of_mem he]
          · exact h _ e he
  intro S T hST
  have := key T S
  rwa [Finset.union_eq_right.2 hST] at this

/-- **`lem:embed`** (Lemma B.9, statement `stoc-sections/appB-quadratic.tex:536-540`, proof
:541-556). Let `f̃ : 2^E → ℝ` be submodular with `f̃(∅) = 0`, let
`a, b ∈ ℝ^E_{>0}`, `Θ > 0`, and `Λ ≥ max{0, max_{S ⊆ E, e ∈ E∖S} (f̃(S) − f̃(S ∪ {e}) + Θ b_e)/a_e}`
(here the two hypotheses `0 ≤ Λ` and `(f̃(S) − f̃(S ∪ {e}) + Θ b_e)/a_e ≤ Λ` for all `S` and
`e ∉ S`). Then `f(S) = f̃(S) + ∑_{e∈S} (Λ a_e − Θ b_e)` is a rank function, and in the instance
with `f`, `m_e = a_e/b_e`, and `β_e = 1/b_e`, the level set `A_{Θ−θ}(Λ + λ)` is the maximal
minimizer of `f̃ − λ a − θ b` for all `λ ≥ −Λ` and `θ < Θ`.

The paper's steps: (1) `f` is submodular and `f(∅) = 0`; (2) by the choice of `Λ` every marginal
`f(S ∪ {e}) − f(S) = f̃(S ∪ {e}) − f̃(S) + Λ a_e − Θ b_e` is nonnegative, so `f` is monotone
(`monotone_of_insert`); (3) `t_e = a_e` and `β_e⁻¹ = b_e`, so
`F_{Λ+λ, Θ−θ} = f̃ − λ a − θ b`; (4) `thm:levelsets` (`Stoc.levelsets`) applies with `Λ + λ ≥ 0`
and `Θ − θ > 0`.
The hypotheses `Θ > 0` and `Λ ≥ 0` are the paper's; its proof does not use them. -/
theorem embed {ft : Finset E → ℝ} (hsub : Submodular ft) (h0 : ft ∅ = 0) {a b : E → ℝ}
    (ha : ∀ e, 0 < a e) (hb : ∀ e, 0 < b e) {Θ Λ : ℝ} (_hΘ : 0 < Θ) (_hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ S e, e ∉ S → (ft S - ft (insert e S) + Θ * b e) / a e ≤ Λ) :
    IsRankFunction (embedF ft a b Λ Θ) ∧
      ∀ l θ : ℝ, -Λ ≤ l → θ < Θ →
        IsMaxMin (tilt ft a b l θ)
          (levelSet (fun e => a e / b e) (fun e => 1 / b e) (Λ + l)
            (bestResponse (embedF ft a b Λ Θ) (fun e => a e / b e) (fun e => 1 / b e) (Λ + l))
            (Θ - θ)) := by
  -- (1) "The function `f` is submodular, as `f̃` is and the second term is modular, and
  -- `f(∅) = 0`."
  have hfsub : Submodular (embedF ft a b Λ Θ) := fun X Y => by
    have h1 := hsub X Y
    have h2 := Finset.sum_union_inter (s₁ := X) (s₂ := Y) (f := fun e => Λ * a e - Θ * b e)
    simp only [embedF]
    linarith
  have hf0 : embedF ft a b Λ Θ ∅ = 0 := by simp [embedF, h0]
  -- (2) "By the choice of `Λ`, every marginal
  -- `f(S ∪ {e}) − f(S) = f̃(S ∪ {e}) − f̃(S) + Λ a_e − Θ b_e`, `S ⊆ E`, `e ∈ E∖S`, is
  -- nonnegative, so `f` is monotone."
  have hmarg : ∀ S e, e ∉ S → embedF ft a b Λ Θ (insert e S) - embedF ft a b Λ Θ S =
      ft (insert e S) - ft S + Λ * a e - Θ * b e := fun S e he => by
    simp only [embedF, Finset.sum_insert he]
    ring
  have hmarg0 : ∀ S e, e ∉ S → 0 ≤ ft (insert e S) - ft S + Λ * a e - Θ * b e :=
    fun S e he => by
      have := (div_le_iff₀ (ha e)).1 (hΛ S e he)
      linarith
  have hrank : IsRankFunction (embedF ft a b Λ Θ) :=
    ⟨hf0, monotone_of_insert fun S e he => by linarith [hmarg S e he, hmarg0 S e he], hfsub⟩
  refine ⟨hrank, fun l θ hl hθ => ?_⟩
  -- (3) "In the instance, `t_e = m_e/β_e = a_e` and `β_e⁻¹ = b_e`, so for all `λ ≥ −Λ` and
  -- `θ < Θ`, `F_{Λ+λ, Θ−θ}(S) = f̃(S) − λ a(S) − θ b(S)` for all `S ⊆ E`, …"
  have ht : ∀ e, a e / b e / (1 / b e) = a e := fun e => by field_simp [(hb e).ne']
  have hbinv : ∀ e, 1 / (1 / b e) = b e := fun e => one_div_one_div (b e)
  have hF : ∀ S, levelFun (embedF ft a b Λ Θ) (fun e => a e / b e) (fun e => 1 / b e) (Λ + l)
      (Θ - θ) S = tilt ft a b l θ S := fun S => by
    simp only [levelFun, embedF, tilt, ht, hbinv, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  -- (4) "… and `thm:levelsets` applies with `Λ + λ ≥ 0` and `Θ − θ > 0`."
  have hα : 0 ≤ Λ + l := by linarith
  have hθ' : 0 < Θ - θ := by linarith
  obtain ⟨h1, h2⟩ := levelsets hrank (fun e => one_div_pos.2 (hb e))
    (fun e => div_nonneg (ha e).le (hb e).le) hα hθ'
  simp only [hF] at h1 h2
  exact ⟨h1, h2⟩

/-! ### The breakpoints of a dilated instance -/

section Dilation

omit [Fintype E] [DecidableEq E] in
/-- The breakpoints of a curve `g'` that is `α ↦ g(α/σ)` on `[0, ∞)`, for `σ > 0`, are those of `g`
multiplied by `σ` (not in the paper: the proofs of `thm:expbp` and `thm:polybits` state "Its
breakpoints are the old breakpoints multiplied by `σ`" and "its breakpoints are the `B_∞`
breakpoints of `(f, t, 1)` multiplied by `σ`" without proof). A breakpoint is positive,
and whether `g'` is affine near a share `α > 0` depends only on its values near `α`, which are
those of `α ↦ g(α/σ)`. -/
lemma breakpoints_comp_div (g g' : ℝ → E → ℝ) {σ : ℝ} (hσ : 0 < σ)
    (hg' : ∀ α, 0 ≤ α → g' α = g (α / σ)) :
    breakpoints g' = (fun b => σ * b) '' breakpoints g := by
  have key : ∀ α, 0 < α → (AffineNear g' α ↔ AffineNear g (α / σ)) := by
    intro α hα
    constructor
    · rintro ⟨ε, hε, a, b, h⟩
      -- shrink the neighborhood to `(α − ε', α + ε') ⊆ (0, ∞)`
      have hε' : 0 < min ε α := lt_min hε hα
      have hεε : min ε α ≤ ε := min_le_left ε α
      have hεα : min ε α ≤ α := min_le_right ε α
      refine ⟨min ε α / σ, div_pos hε' hσ, a, fun e => σ * b e, fun γ hγ => ?_⟩
      have hγ' : γ * σ ∈ Ioo (α - min ε α) (α + min ε α) := by
        obtain ⟨h1, h2⟩ := hγ
        rw [← sub_div] at h1
        rw [← add_div] at h2
        exact ⟨(div_lt_iff₀ hσ).1 h1, (lt_div_iff₀ hσ).1 h2⟩
      have hγ0 : 0 ≤ γ * σ := by linarith [hγ'.1]
      have := h (γ * σ) ⟨by linarith [hγ'.1], by linarith [hγ'.2]⟩
      rw [hg' _ hγ0, mul_div_cancel_right₀ γ hσ.ne'] at this
      rw [this]
      funext e
      ring
    · rintro ⟨ε, hε, a, b, h⟩
      have hε' : 0 < min (ε * σ) α := lt_min (mul_pos hε hσ) hα
      have hεε : min (ε * σ) α ≤ ε * σ := min_le_left (ε * σ) α
      have hεα : min (ε * σ) α ≤ α := min_le_right (ε * σ) α
      refine ⟨min (ε * σ) α, hε', a, fun e => b e / σ, fun γ hγ => ?_⟩
      obtain ⟨h1, h2⟩ := hγ
      have hγ0 : 0 ≤ γ := by linarith
      have hγ' : γ / σ ∈ Ioo (α / σ - ε) (α / σ + ε) := by
        have e1 : α / σ - ε = (α - ε * σ) / σ := by field_simp
        have e2 : α / σ + ε = (α + ε * σ) / σ := by field_simp
        rw [e1, e2]
        exact ⟨div_lt_div_of_pos_right (by linarith) hσ, div_lt_div_of_pos_right (by linarith) hσ⟩
      rw [hg' γ hγ0, h _ hγ']
      funext e
      ring
  ext α
  simp only [breakpoints, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨hα, hna⟩
    refine ⟨α / σ, ⟨div_pos hα hσ, fun h => hna ((key α hα).2 h)⟩, ?_⟩
    field_simp
  · rintro ⟨b, ⟨hb, hnb⟩, rfl⟩
    refine ⟨mul_pos hσ hb, fun h => hnb ?_⟩
    have := (key (σ * b) (mul_pos hσ hb)).1 h
    rwa [mul_div_cancel_left₀ b hσ.ne'] at this

end Dilation

/-! ### Exponentially many breakpoints (`thm:expbp`) -/

section ExpBP

variable {f : Finset E → ℝ} {m β : E → ℝ}

/-- `x*` is affine on a closed interval of shares in `[0, ∞)` with no breakpoint inside (not in
the paper: part of `affine_of_no_bp`; the proof of `thm:expbp` uses without proof that `x*` is
affine between consecutive breakpoints). -/
lemma affine_Icc_of_no_bp (H : Tracing.Hyp f m β) {a c : ℝ} (hac : a < c) (h0 : 0 ≤ a)
    (hno : ∀ α ∈ Ioo a c, α ∉ Tracing.BP f m β) :
    ∃ p w : E → ℝ, ∀ α ∈ Icc a c, bestResponse f m β α = fun e => p e + α * w e := by
  have hcoord : ∀ e, ∃ c₀ d : ℝ, ∀ α ∈ Icc a c, bestResponse f m β α e = c₀ + d * α := by
    intro e
    refine exists_affine_of_affineAt hac ((continuous_apply e).comp_continuousOn
      ((pwaffine H).1.mono fun α hα => h0.trans hα.1)) fun α hα => ?_
    have hpos : 0 < α := lt_of_le_of_lt h0 hα.1
    have hnot := hno α hα
    simp only [Tracing.BP, breakpoints, Set.mem_ofPred_eq, not_and, not_not] at hnot
    obtain ⟨ε, hε, A, W, hAW⟩ := hnot hpos
    exact ⟨ε, hε, A e, W e, fun α' hα' => by
      show bestResponse f m β α' e = _
      rw [hAW α' hα']; ring⟩
  choose c₀ d hcd using hcoord
  exact ⟨c₀, d, fun α hα => funext fun e => by rw [hcd e α hα]; ring⟩

/-- `x*` is affine on an interval of positive shares without breakpoints (not in the paper: the
proof of `thm:expbp` uses without proof that `x*` is affine on the open intervals between the
breakpoints). -/
lemma affine_of_no_bp (H : Tracing.Hyp f m β) {I : Set ℝ} (hI : I.OrdConnected)
    (hI0 : I ⊆ Ioi 0) (hno : ∀ α ∈ I, α ∉ Tracing.BP f m β) :
    ∃ p w : E → ℝ, ∀ α ∈ I, bestResponse f m β α = fun e => p e + α * w e := by
  by_cases hsub : ∀ α ∈ I, ∀ α' ∈ I, α = α'
  · by_cases hne : I.Nonempty
    · obtain ⟨α₀, h₀⟩ := hne
      exact ⟨bestResponse f m β α₀, 0, fun α hα => by rw [hsub α hα α₀ h₀]; simp⟩
    · exact ⟨0, 0, fun α hα => absurd ⟨α, hα⟩ hne⟩
  push Not at hsub
  obtain ⟨α₀, h₀, α₁, h₁, hne⟩ := hsub
  wlog hlt : α₀ < α₁ generalizing α₀ α₁
  · exact this α₁ h₁ α₀ h₀ (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne))
  -- the affine form on `[α₀, α₁]`
  have hIcc : ∀ a c, a ∈ I → c ∈ I → a < c → ∃ p w : E → ℝ, ∀ α ∈ Icc a c,
      bestResponse f m β α = fun e => p e + α * w e := fun a c ha hc hac =>
    affine_Icc_of_no_bp H hac (hI0 ha).le fun α hα => hno α (hI.out ha hc ⟨hα.1.le, hα.2.le⟩)
  obtain ⟨p, w, hpw⟩ := hIcc α₀ α₁ h₀ h₁ hlt
  refine ⟨p, w, fun α hα => ?_⟩
  -- the affine form on `[min α₀ α, max α₁ α]` agrees with it at `α₀` and `α₁`
  obtain ⟨p', w', hpw'⟩ := hIcc (min α₀ α) (max α₁ α)
    (by rcases min_choice α₀ α with h | h <;> rw [h] <;> assumption)
    (by rcases max_choice α₁ α with h | h <;> rw [h] <;> assumption)
    (lt_of_le_of_lt (min_le_left _ _) (lt_of_lt_of_le hlt (le_max_left _ _)))
  have hm₀ : α₀ ∈ Icc (min α₀ α) (max α₁ α) := ⟨min_le_left _ _, hlt.le.trans (le_max_left _ _)⟩
  have hm₁ : α₁ ∈ Icc (min α₀ α) (max α₁ α) := ⟨(min_le_left _ _).trans hlt.le, le_max_left _ _⟩
  have hm : α ∈ Icc (min α₀ α) (max α₁ α) := ⟨min_le_right _ _, le_max_right _ _⟩
  have e₀ := (hpw α₀ ⟨le_rfl, hlt.le⟩).symm.trans (hpw' α₀ hm₀)
  have e₁ := (hpw α₁ ⟨hlt.le, le_rfl⟩).symm.trans (hpw' α₁ hm₁)
  rw [hpw' α hm]
  funext e
  have a₀ : p e + α₀ * w e = p' e + α₀ * w' e := congrFun e₀ e
  have a₁ : p e + α₁ * w e = p' e + α₁ * w' e := congrFun e₁ e
  have hw : w e = w' e := by
    have : (α₁ - α₀) * (w e - w' e) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (sub_ne_zero.2 (ne_of_gt hlt))
    · linarith
  have hp : p e = p' e := by rw [hw] at a₀; linarith
  rw [hp, hw]

omit [Fintype E] [DecidableEq E] in
/-- The `k` points of a finite set `B` in an interval `J` cut `J` into `k + 1` intervals, the open
intervals between consecutive points when `J` is open (not in the paper: the proof of `thm:expbp`
states this without proof). The interval of a share `α ∈ J ∖ B` is given by the largest point of
`B ∩ J` below `α`, `left α` (`⊥` if there is none): `left` takes at most `k + 1` values (the set
`L`), and the shares of `J ∖ B` with the same value of `left` form an interval. -/
lemma cut_intervals {B J : Set ℝ} (hJ : J.OrdConnected) (hfin : (B ∩ J).Finite) :
    ∃ (L : Finset (WithBot ℝ)) (left : ℝ → WithBot ℝ), L.card ≤ (B ∩ J).ncard + 1 ∧
      (∀ α, left α ∈ L) ∧ ∀ a₀, {α | α ∈ J ∧ α ∉ B ∧ left α = a₀}.OrdConnected := by
  classical
  set T := hfin.toFinset with hT_def
  set left : ℝ → WithBot ℝ := fun α => (T.filter (· < α)).max with hleft
  set L : Finset (WithBot ℝ) :=
    insert (⊥ : WithBot ℝ) (Finset.image (fun b : ℝ => (b : WithBot ℝ)) T) with hL_def
  have hL : L.card ≤ (B ∩ J).ncard + 1 := by
    calc L.card ≤ (Finset.image (fun b : ℝ => (b : WithBot ℝ)) T).card + 1 :=
          Finset.card_insert_le _ _
      _ ≤ T.card + 1 := by gcongr; exact Finset.card_image_le
      _ = _ := by rw [Set.ncard_eq_toFinset_card _ hfin]
  have hleft_mem : ∀ α, left α ∈ L := fun α => by
    rcases (T.filter (· < α)).eq_empty_or_nonempty with h | h
    · simp only [left, h, Finset.max_empty, L]
      exact Finset.mem_insert_self _ _
    · obtain ⟨b, hb⟩ := Finset.max_of_nonempty h
      refine Finset.mem_insert_of_mem (Finset.mem_image.2
        ⟨b, (Finset.mem_filter.1 (Finset.mem_of_max hb)).1, ?_⟩)
      simp only [left, hb]
  have hleft_le : ∀ α, left α ≤ (α : WithBot ℝ) := fun α =>
    Finset.max_le fun b hb => WithBot.coe_le_coe.2 (Finset.mem_filter.1 hb).2.le
  have hleft_mono : ∀ {α γ : ℝ}, α ≤ γ → left α ≤ left γ := fun hαγ =>
    Finset.max_mono fun b hb => Finset.mem_filter.2
      ⟨(Finset.mem_filter.1 hb).1, (Finset.mem_filter.1 hb).2.trans_le hαγ⟩
  refine ⟨L, left, hL, hleft_mem, fun a₀ => ⟨fun x hx y hy z hz => ?_⟩⟩
  obtain ⟨hxJ, hxB, hxa⟩ := hx
  obtain ⟨hyJ, hyB, hya⟩ := hy
  have hzJ : z ∈ J := hJ.out hxJ hyJ hz
  refine ⟨hzJ, fun hzB => ?_, ?_⟩
  · rcases hz.1.lt_or_eq with hxz | rfl
    · rcases hz.2.lt_or_eq with hzy | rfl
      · have hzT : z ∈ T.filter (· < y) :=
          Finset.mem_filter.2 ⟨(Set.Finite.mem_toFinset _).2 ⟨hzB, hzJ⟩, hzy⟩
        have h1 : (z : WithBot ℝ) ≤ left y := Finset.le_max hzT
        have h2 : left x < (z : WithBot ℝ) := (hleft_le x).trans_lt (WithBot.coe_lt_coe.2 hxz)
        rw [hxa, ← hya] at h2
        exact absurd h1 (not_le.2 h2)
      · exact hyB hzB
    · exact hxB hzB
  · exact le_antisymm (hya ▸ hleft_mono hz.2) (hxa ▸ hleft_mono hz.1)

/-- `1 + n + C(n, 2) = 1 + n(n + 1)/2`, the computation in the last sentence of the second
paragraph of the proof of `thm:expbp`. -/
lemma one_add_add_choose_two (n : ℕ) : 1 + n + n.choose 2 = 1 + n * (n + 1) / 2 := by
  have h1 : (n + 1).choose 2 = n + n.choose 2 := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
  have h2 : (n + 1).choose 2 = n * (n + 1) / 2 := by
    rw [Nat.choose_two_right, Nat.add_sub_cancel, mul_comm]
  omega

/-- The line-arrangement argument of the proof of `thm:expbp` (its second paragraph,
`stoc-sections/appB-quadratic.tex:574-583`), for an interval `J ⊆ (0, ∞)` of shares (`(Λ, Λ + 1)` in
`thm:expbp`; `(0, ∞)` for the bound on `B_∞` in the proof of `thm:polybits`): if every `S ⊆ E` is
the level set `A_{θ'_S}(α'_S)` at a point `(α'_S, θ'_S)` such that `α'_S ∈ J` is not a breakpoint
and `ρ_e(α'_S) ≠ θ'_S` for all `e`, then `2^n ≤ (k + 1)(1 + n(n + 1)/2)`, where `k` is the number
of breakpoints in `J`.

The paper's steps: (1) the `k` breakpoints cut `J` into `k + 1` open intervals (`cut_intervals`:
the interval of a share is given by the largest breakpoint in `J` below it, or `⊥` if there is
none), on each of which `x*`, and hence every `ρ_e`, is affine (`affine_of_no_bp`); (2) on such an
interval `I`, the graph of `ρ_e` lies on a line `ℓ_e`, and for `α ∈ I` the level set `A_θ(α)` is
the set of `e` whose line passes through or above `(α, θ)`; (3) the points `(α'_S, θ'_S)` with
`α'_S ∈ I` in the same cell of the arrangement of the lines `ℓ_e` have the same set `S`
(`above_eq_of_mem_cell`); (4) `n` lines cut the plane into at most
`1 + n + C(n, 2) = 1 + n(n + 1)/2` cells (`cells_finite_ncard_le`), so
`2^n ≤ (k + 1)(1 + n(n + 1)/2)`. -/
theorem two_pow_le_cells (H : Tracing.Hyp f m β) {J : Set ℝ} (hJ : J.OrdConnected)
    (hJ0 : J ⊆ Ioi 0)
    (hpts : ∀ S : Finset E, ∃ α θ : ℝ, α ∈ J ∧ α ∉ Tracing.BP f m β ∧
      (∀ e, rho f m β α e ≠ θ) ∧ levelSet m β α (bestResponse f m β α) θ = S) :
    2 ^ Fintype.card E ≤ ((Tracing.BP f m β ∩ J).ncard + 1) *
      (1 + Fintype.card E * (Fintype.card E + 1) / 2) := by
  classical
  have hTfin : (Tracing.BP f m β ∩ J).Finite := (Tracing.bp_finite H).inter_of_left J
  -- (1) "Let `k` be the number of breakpoints in `(Λ, Λ + 1)`. They cut this interval into `k + 1`
  -- open intervals, …"
  -- Here for the interval `J` in place of `(Λ, Λ + 1)`.
  obtain ⟨Lefts, left, hLefts, hleft_mem, hI⟩ := cut_intervals hJ hTfin
  set I : WithBot ℝ → Set ℝ := fun a₀ => {α | α ∈ J ∧ α ∉ Tracing.BP f m β ∧ left α = a₀}
  -- "… on each of which `x*`, and hence every `ρ_e`, is affine."
  have haff : ∀ a₀, ∃ p w : E → ℝ, ∀ α ∈ I a₀, bestResponse f m β α = fun e => p e + α * w e :=
    fun a₀ => affine_of_no_bp H (hI a₀) (fun α hα => hJ0 hα.1) fun α hα => hα.2.1
  choose p w hpw using haff
  -- (2) "Fix one of them, `I`. For `e ∈ E`, the graph of `ρ_e` over `I` lies on a line `ℓ_e` in
  -- the `(α, θ)`-plane, and for `α ∈ I` the level set `A_θ(α)` is the set of elements `e` whose
  -- line `ℓ_e` passes through or above `(α, θ)`."
  -- The Lean takes every interval `I a₀` at once.
  set c : WithBot ℝ → E → ℝ := fun a₀ e => -(β e * p a₀ e)
  set d : WithBot ℝ → E → ℝ := fun a₀ e => m e - β e * w a₀ e
  have hrho : ∀ a₀, ∀ α ∈ I a₀, ∀ e, rho f m β α e = c a₀ e + d a₀ e * α := by
    intro a₀ α hα e
    simp only [rho, marg, hpw a₀ α hα, c, d]
    ring
  have hlev : ∀ a₀, ∀ α ∈ I a₀, ∀ θ, levelSet m β α (bestResponse f m β α) θ =
      above (c a₀) (d a₀) (α, θ) := by
    intro a₀ α hα θ
    ext e
    simp only [levelSet, above, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hrho a₀ α hα e]
    rfl
  -- (3) "So all points `(α'_S, θ̄'_S)` with `α'_S ∈ I` that lie in the same cell of the
  -- arrangement of the lines `ℓ_e` have the same set `S`."
  choose α' θ' hα'J hα'bp hα'ne hα'S using hpts
  have hI' : ∀ S, α' S ∈ I (left (α' S)) := fun S => ⟨hα'J S, hα'bp S, rfl⟩
  have hoff : ∀ S, (α' S, θ' S) ∈ offLines (c (left (α' S))) (d (left (α' S))) := by
    intro S e h
    apply hα'ne S e
    rw [hrho _ (α' S) (hI' S) e]
    exact h.symm
  have hS : ∀ S, above (c (left (α' S))) (d (left (α' S))) (α' S, θ' S) = S := fun S => by
    rw [← hlev _ (α' S) (hI' S), hα'S]
  set cell : Finset E → WithBot ℝ × Set (ℝ × ℝ) := fun S =>
    (left (α' S), connectedComponentIn (offLines (c (left (α' S))) (d (left (α' S))))
      (α' S, θ' S))
  have hinj : Set.InjOn cell ↑(univ : Finset (Finset E)) := by
    intro S _ S' _ h
    obtain ⟨h1, h2⟩ := Prod.ext_iff.1 h
    simp only [cell] at h1 h2
    rw [← h1] at h2
    have hmem : (α' S', θ' S') ∈ connectedComponentIn
        (offLines (c (left (α' S))) (d (left (α' S)))) (α' S, θ' S) := by
      rw [h2]
      have := hoff S'
      rw [← h1] at this
      exact mem_connectedComponentIn this
    have := above_eq_of_mem_cell (hoff S) hmem
    rw [hS S] at this
    have h3 := hS S'
    rw [← h1, this] at h3
    exact h3
  -- (4) "As `n` lines cut the plane into at most `1 + n + C(n, 2) = 1 + n(n + 1)/2` cells, we get
  -- `2^n ≤ (k + 1)(1 + n(n + 1)/2)`."
  set cellsF : WithBot ℝ → Finset (Set (ℝ × ℝ)) :=
    fun a₀ => (cells_finite_ncard_le (c a₀) (d a₀)).1.toFinset
  set target := Lefts.biUnion fun a₀ => (cellsF a₀).image fun C => (a₀, C)
  have hmaps : ∀ S ∈ (univ : Finset (Finset E)), cell S ∈ target := by
    intro S _
    refine Finset.mem_biUnion.2 ⟨left (α' S), hleft_mem _, Finset.mem_image.2 ⟨_, ?_, rfl⟩⟩
    exact (Set.Finite.mem_toFinset _).2 ⟨(α' S, θ' S), hoff S, rfl⟩
  have hcard : ∀ a₀, (cellsF a₀).card ≤ 1 + Fintype.card E + (Fintype.card E).choose 2 :=
    fun a₀ => by
      rw [← Set.ncard_eq_toFinset_card _ (cells_finite_ncard_le (c a₀) (d a₀)).1]
      exact (cells_finite_ncard_le (c a₀) (d a₀)).2
  calc 2 ^ Fintype.card E = (univ : Finset (Finset E)).card := by
        rw [Finset.card_univ, Fintype.card_finset]
    _ ≤ target.card := Finset.card_le_card_of_injOn cell hmaps hinj
    _ ≤ ∑ a₀ ∈ Lefts, ((cellsF a₀).image fun C => (a₀, C)).card := Finset.card_biUnion_le
    _ ≤ ∑ _a₀ ∈ Lefts, (1 + Fintype.card E + (Fintype.card E).choose 2) :=
        Finset.sum_le_sum fun a₀ _ => Finset.card_image_le.trans (hcard a₀)
    _ = Lefts.card * (1 + Fintype.card E + (Fintype.card E).choose 2) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ((Tracing.BP f m β ∩ J).ncard + 1) *
          (1 + Fintype.card E + (Fintype.card E).choose 2) :=
        Nat.mul_le_mul_right _ hLefts
    _ = _ := by rw [one_add_add_choose_two]

/-- The marginal `ρ_e` is continuous at every positive share, as `x*` is continuous on `[0, ∞)`
(`lem:pwaffine`, `Stoc.pwaffine`) (not in the paper: the proofs of `thm:expbp` and `thm:polybits`
take the continuity of `ρ` from `lem:pwaffine`, which states that of `x*`). -/
lemma continuousAt_rho (H : Tracing.Hyp f m β) {α : ℝ} (hα : 0 < α) (e : E) :
    ContinuousAt (fun γ => rho f m β γ e) α := by
  have hx : ContinuousAt (fun γ => bestResponse f m β γ e) α :=
    (continuous_apply e).continuousAt.comp ((pwaffine H).1.continuousAt (Ici_mem_nhds hα))
  unfold rho marg
  exact (continuousAt_id.mul continuousAt_const).sub (continuousAt_const.mul hx)

/-- The step "these inequalities hold strictly at `(α_S, θ̄)`, and by continuity of `ρ`
(`lem:pwaffine`) they hold strictly near `(α_S, θ̄)`" of the proof of `thm:expbp`: strict
inequalities between the marginals and the level at a point `(α₀, θ)` with `α₀ > 0` hold at every
point `(α, θ')` near it. -/
lemma strict_near_point (H : Tracing.Hyp f m β) {α₀ θ : ℝ} (hα₀0 : 0 < α₀) {S : Finset E}
    (hin : ∀ e ∈ S, θ < rho f m β α₀ e) (hout : ∀ e ∉ S, rho f m β α₀ e < θ) :
    ∀ᶠ q in nhds ((α₀, θ) : ℝ × ℝ),
      (∀ e ∈ S, q.2 < rho f m β q.1 e) ∧ ∀ e ∉ S, rho f m β q.1 e < q.2 := by
  have hcont : ∀ e, ContinuousAt (fun q : ℝ × ℝ => rho f m β q.1 e - q.2) (α₀, θ) := fun e => by
    have h1 : ContinuousAt (fun q : ℝ × ℝ => rho f m β q.1 e) (α₀, θ) :=
      (continuousAt_rho H hα₀0 e).fst'
    exact h1.sub continuousAt_snd
  have h1 : ∀ᶠ q in nhds ((α₀, θ) : ℝ × ℝ), ∀ e ∈ S, q.2 < rho f m β q.1 e := by
    refine (Filter.eventually_all_finset S).2 fun e he => ?_
    have := (hcont e).eventually (Ioi_mem_nhds (a := 0)
      (show (0 : ℝ) < rho f m β (α₀, θ).1 e - (α₀, θ).2 by linarith [hin e he]))
    filter_upwards [this] with q hq
    have hq' : 0 < rho f m β q.1 e - q.2 := hq
    linarith
  have h2 : ∀ᶠ q in nhds ((α₀, θ) : ℝ × ℝ), ∀ e ∈ Finset.univ \ S, rho f m β q.1 e < q.2 := by
    refine (Filter.eventually_all_finset (Finset.univ \ S)).2 fun e he => ?_
    have := (hcont e).eventually (Iio_mem_nhds (a := 0)
      (show rho f m β (α₀, θ).1 e - (α₀, θ).2 < 0 by
        linarith [hout e (Finset.mem_sdiff.1 he).2]))
    filter_upwards [this] with q hq
    have hq' : rho f m β q.1 e - q.2 < 0 := hq
    linarith
  filter_upwards [h1, h2] with q hq1 hq2
  exact ⟨hq1, fun e he => hq2 e (Finset.mem_sdiff.2 ⟨Finset.mem_univ e, he⟩)⟩

/-- The step "by continuity of `ρ` (`lem:pwaffine`), these strict inequalities hold at every share
near `α_S`" of the proof of `thm:polybits` (the bound on `B_∞`): strict inequalities between the
marginals at a share `α₀ > 0` and a fixed level `θ` hold at every share near `α₀`. -/
lemma strict_near_share (H : Tracing.Hyp f m β) {α₀ θ : ℝ} (hα₀0 : 0 < α₀) {S : Finset E}
    (hin : ∀ e ∈ S, θ < rho f m β α₀ e) (hout : ∀ e ∉ S, rho f m β α₀ e < θ) :
    ∀ᶠ α in nhds α₀, (∀ e ∈ S, θ < rho f m β α e) ∧ ∀ e ∉ S, rho f m β α e < θ := by
  have h1 : ∀ᶠ α in nhds α₀, ∀ e ∈ S, θ < rho f m β α e :=
    (Filter.eventually_all_finset S).2 fun e he =>
      (continuousAt_rho H hα₀0 e).eventually (Ioi_mem_nhds (hin e he))
  have h2 : ∀ᶠ α in nhds α₀, ∀ e ∈ Finset.univ \ S, rho f m β α e < θ :=
    (Filter.eventually_all_finset (Finset.univ \ S)).2 fun e he =>
      (continuousAt_rho H hα₀0 e).eventually (Iio_mem_nhds (hout e (Finset.mem_sdiff.1 he).2))
  filter_upwards [h1, h2] with α hα1 hα2
  exact ⟨hα1, fun e he => hα2 e (Finset.mem_sdiff.2 ⟨Finset.mem_univ e, he⟩)⟩

/-- The step "So there is a point `(α'_S, θ̄'_S)` with `A_{θ̄'_S}(α'_S) = S`, where
`α'_S ∈ (Λ, Λ + 1)` is not a breakpoint and `ρ_e(α'_S) ≠ θ̄'_S` for all `e ∈ E`" of the proof of
`thm:expbp` and "As `θ'_S > 0` and there are finitely many breakpoints, there is a share
`α'_S > 0` that is not a breakpoint such that `A_{θ'_S}(α'_S) = S` and `ρ_e(α'_S) ≠ θ'_S` for all
`e ∈ E`" of the proof of `thm:polybits` (the bound on `B_∞`): if the strict inequalities hold at
every share near `α₀`, a share near `α₀` in the open set `J` that is not a breakpoint has them
(there are finitely many breakpoints). -/
lemma exists_point_of_near (H : Tracing.Hyp f m β) {J : Set ℝ} (hJ : IsOpen J) {α₀ θ : ℝ}
    (hα₀ : α₀ ∈ J) {S : Finset E}
    (hnear : ∀ᶠ α in nhds α₀, (∀ e ∈ S, θ < rho f m β α e) ∧ ∀ e ∉ S, rho f m β α e < θ) :
    ∃ α', α' ∈ J ∧ α' ∉ Tracing.BP f m β ∧ (∀ e, rho f m β α' e ≠ θ) ∧
      levelSet m β α' (bestResponse f m β α') θ = S := by
  classical
  have hJev : ∀ᶠ α in nhds α₀, α ∈ J := hJ.mem_nhds hα₀
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hJev.and hnear)
  obtain ⟨α', hα', hα'B⟩ := ((Set.Ioo_infinite (show α₀ - ε < α₀ + ε by linarith)).sdiff
    (Tracing.bp_finite H)).nonempty
  have hmem : α' ∈ Metric.ball α₀ ε := by rw [Real.ball_eq_Ioo]; exact hα'
  obtain ⟨hα'J, hS1, hS2⟩ := hball hmem
  refine ⟨α', hα'J, hα'B, fun e => ?_, ?_⟩
  · by_cases he : e ∈ S
    · exact (hS1 e he).ne'
    · exact (hS2 e he).ne
  · ext e
    simp only [levelSet, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases he : e ∈ S
    · exact ⟨fun _ => he, fun _ => (hS1 e he).le⟩
    · exact ⟨fun h => absurd h (not_le.2 (hS2 e he)), fun h => absurd h he⟩

omit [Fintype E] [DecidableEq E] in
/-- The maximal minimizer of a function with the unique minimizer `S` is `S` (not in the paper: the
proofs of `thm:expbp` and `thm:polybits` leave this implicit). -/
lemma IsMaxMin.eq_of_unique {g : Finset E → ℝ} {A S : Finset E} (hA : IsMaxMin g A)
    (hS : ∀ T, T ≠ S → g S < g T) : A = S := by
  by_contra hne
  exact absurd (hA.1 S) (not_le.2 (hS A hne))

/-- `4n² ≤ 2^n` for `n ≥ 8` (not in the paper: part of `two_pow_div_sub_one_ge`). -/
lemma four_sq_le_two_pow {n : ℕ} (hn : 8 ≤ n) : 4 * n ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h1 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    have h2 : 4 * (n + 1) ^ 2 ≤ 2 * (4 * n ^ 2) := by nlinarith
    omega

/-- The bound of `thm:expbp` is `2^{n − O(log n)}`: for `n ≥ 8`,
`2^n/(1 + n(n + 1)/2) − 1 ≥ 2^n/(4n²) = 2^{n − 2 log₂ n − 2}` (not in the paper: the statement of
`thm:expbp` says "which is `2^{n−O(log n)}`" without proof). -/
lemma two_pow_div_sub_one_ge {n : ℕ} (hn : 8 ≤ n) :
    (2 : ℝ) ^ ((n : ℝ) - 2 * Real.logb 2 n - 2) ≤ (2 : ℝ) ^ n / (1 + n * (n + 1) / 2) - 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h1 : (2 : ℝ) ^ ((n : ℝ) - 2 * Real.logb 2 n - 2) = 2 ^ n / (4 * (n : ℝ) ^ 2) := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_sub (by norm_num), Real.rpow_natCast,
      mul_comm (2 : ℝ), Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hn0]
    norm_num
    ring
  rw [h1]
  have h4 : (4 : ℝ) * n ^ 2 ≤ 2 ^ n := by exact_mod_cast four_sq_le_two_pow hn
  have hD : (1 : ℝ) + n * (n + 1) / 2 ≤ n ^ 2 := by
    have : (8 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hDpos : (0 : ℝ) < 1 + n * (n + 1) / 2 := by positivity
  have h2 : (2 : ℝ) ^ n / n ^ 2 ≤ 2 ^ n / (1 + n * (n + 1) / 2) :=
    div_le_div_of_nonneg_left (by positivity) hDpos hD
  have h3 : (2 : ℝ) ^ n / (4 * n ^ 2) + 1 ≤ 2 ^ n / n ^ 2 := by
    rw [div_add_one (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (n : ℝ), (by positivity : (0 : ℝ) < 2 ^ n)]
  linarith

/-- `2^n ≤ (k + 1)(1 + n(n + 1)/2)` in `ℕ` gives `2^n/(1 + n(n + 1)/2) − 1 ≤ k` in `ℝ` (the
computation that turns the count of the proofs of `thm:expbp` and `thm:polybits` into their
bound). -/
lemma sub_one_le_of_two_pow_le {n k : ℕ} (h : 2 ^ n ≤ (k + 1) * (1 + n * (n + 1) / 2)) :
    (2 : ℝ) ^ n / (1 + n * (n + 1) / 2) - 1 ≤ k := by
  have hD : ((1 + n * (n + 1) / 2 : ℕ) : ℝ) = 1 + (n : ℝ) * (n + 1) / 2 := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_div (Nat.even_mul_succ_self _).two_dvd (by norm_num)]
    push_cast
    ring
  have hpos : (0 : ℝ) < 1 + (n : ℝ) * (n + 1) / 2 := by positivity
  have hR : (2 : ℝ) ^ n ≤ ((k : ℝ) + 1) * (1 + (n : ℝ) * (n + 1) / 2) := by
    rw [← hD]
    exact_mod_cast h
  rw [sub_le_iff_le_add, div_le_iff₀ hpos]
  linarith

/-- **`thm:expbp`** (Theorem 3.9, statement `stoc-sections/06-optimal-share.tex:65-67`, proof
`stoc-sections/appB-quadratic.tex:559-590`). For every `n ≥ 1`, there is an instance on `n` elements
(`Fin n`) whose best response has at least `2^n/(1 + n(n + 1)/2) − 1` breakpoints in `(0, 1)`,
which is `2^{n − O(log n)}` (the second part: at least `2^{n − 2 log₂ n − 2}` for `n ≥ 8`,
`two_pow_div_sub_one_ge`).

The paper's steps: (1) `a`, `b`, and `f̃` from `thm:alm` (`alm`), and the instance of `lem:embed`
(`embed`) with `Θ = 2` and `Λ = max{0, max_{S, e∉S} (f̃(S) − f̃(S ∪ {e}) + 2 b_e)/a_e}`; (2) for
`S ⊆ E`, `α_S = Λ + λ_S ∈ (Λ, Λ + 1)` and `θ̄_S = Θ − θ_S ∈ (1, 2)`, and `lem:embed` gives
`A_{θ̄_S}(α_S) = S` (the maximal minimizer of a function with the unique minimizer `S` is `S`:
`IsMaxMin.eq_of_unique`); (3) a level `θ̄` with `max{1, ρ_e(α_S) : e ∉ S} < θ̄ < θ̄_S`, continuity
of `ρ` (`strict_near_point`), and a point `(α'_S, θ̄'_S)` with `A_{θ̄'_S}(α'_S) = S`,
`α'_S ∈ (Λ, Λ + 1)` not a breakpoint and `ρ_e(α'_S) ≠ θ̄'_S` (`exists_point_of_near`); (4) the
line-arrangement count (`two_pow_le_cells`): `2^n ≤ (k + 1)(1 + n(n + 1)/2)` for the number `k` of
breakpoints in `(Λ, Λ + 1)`; (5) with `σ = 1/(Λ + 1)` and the rewards `m/σ`, `lem:ops`(b)
(`Stoc.Hardness.ops_b_aux`) gives the new best response `α ↦ x*(α/σ)`, its breakpoints are the old
ones multiplied by `σ` (`breakpoints_comp_div`), and the `k` breakpoints in `(Λ, Λ + 1)` move into
`(σΛ, 1) ⊆ (0, 1)`. -/
theorem expbp (n : ℕ) (hn : 1 ≤ n) :
    (∃ (f : Finset (Fin n) → ℝ) (m β : Fin n → ℝ), Tracing.Hyp f m β ∧
      (breakpoints (bestResponse f m β) ∩ Ioo 0 1).Finite ∧
      (2 : ℝ) ^ n / (1 + n * (n + 1) / 2) - 1 ≤
        (breakpoints (bestResponse f m β) ∩ Ioo 0 1).ncard) ∧
    (8 ≤ n → (2 : ℝ) ^ ((n : ℝ) - 2 * Real.logb 2 n - 2) ≤
      (2 : ℝ) ^ n / (1 + n * (n + 1) / 2) - 1) := by
  refine ⟨?_, two_pow_div_sub_one_ge⟩
  classical
  -- (1) "Take `a`, `b`, and `f̃` from `thm:alm`, and the instance of `lem:embed` with `Θ := 2` and
  -- `Λ` as there."
  obtain ⟨a, b, ft, ha, hb, hsub, -, h0, hS⟩ := alm n hn
  set pairs : Finset (Finset (Fin n) × Fin n) := Finset.univ.filter fun q => q.2 ∉ q.1
  have hpairs : pairs.Nonempty := ⟨(∅, ⟨0, hn⟩), by simp [pairs]⟩
  set Λ : ℝ := max 0 (pairs.sup' hpairs fun q => (ft q.1 - ft (insert q.2 q.1) + 2 * b q.2) / a q.2)
    with hΛ_def
  have hΛ0 : 0 ≤ Λ := le_max_left _ _
  have hΛ : ∀ S e, e ∉ S → (ft S - ft (insert e S) + 2 * b e) / a e ≤ Λ := fun S e he =>
    le_max_of_le_right (Finset.le_sup' (fun q : Finset (Fin n) × Fin n =>
      (ft q.1 - ft (insert q.2 q.1) + 2 * b q.2) / a q.2) (by simp [pairs, he] : (S, e) ∈ pairs))
  obtain ⟨hrank, hlev⟩ := embed hsub h0 ha hb two_pos hΛ0 hΛ
  set f' := embedF ft a b Λ 2
  set m' : Fin n → ℝ := fun e => a e / b e
  set β' : Fin n → ℝ := fun e => 1 / b e
  have H : Tracing.Hyp f' m' β' :=
    ⟨hrank, fun e => one_div_pos.2 (hb e), fun e => div_nonneg (ha e).le (hb e).le⟩
  have hpts : ∀ S : Finset (Fin n), ∃ α θ : ℝ, α ∈ Ioo Λ (Λ + 1) ∧ α ∉ Tracing.BP f' m' β' ∧
      (∀ e, rho f' m' β' α e ≠ θ) ∧ levelSet m' β' α (bestResponse f' m' β' α) θ = S := by
    intro S
    obtain ⟨l, θS, hl, hθS, huniq⟩ := hS S
    -- (2) "For `S ⊆ E`, let `α_S := Λ + λ_S ∈ (Λ, Λ + 1)` and `θ̄_S := Θ − θ_S ∈ (1, 2)`. As
    -- `λ_S > 0 ≥ −Λ` and `θ_S < Θ`, `lem:embed` gives `A_{θ̄_S}(α_S) = S`, that is,
    -- `ρ_e(α_S) ≥ θ̄_S` for `e ∈ S` and `ρ_e(α_S) < θ̄_S` for `e ∉ S`."
    have hαS : Λ + l ∈ Ioo Λ (Λ + 1) := ⟨by linarith [hl.1], by linarith [hl.2]⟩
    have hθbarS : 2 - θS ∈ Ioo (1 : ℝ) 2 := ⟨by linarith [hθS.2], by linarith [hθS.1]⟩
    have hAS : levelSet m' β' (Λ + l) (bestResponse f' m' β' (Λ + l)) (2 - θS) = S :=
      (hlev l θS (by linarith [hl.1]) (by linarith [hθS.2])).eq_of_unique huniq
    have hin : ∀ e ∈ S, 2 - θS ≤ rho f' m' β' (Λ + l) e := fun e he => by
      rw [← hAS] at he
      exact (Finset.mem_filter.1 he).2
    have hout : ∀ e ∉ S, rho f' m' β' (Λ + l) e < 2 - θS := fun e he => by
      rw [← hAS] at he
      simp only [levelSet, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at he
      exact he
    -- (3) "For a level `θ̄` with `max{1, ρ_e(α_S) : e ∉ S} < θ̄ < θ̄_S`, these inequalities hold
    -- strictly at `(α_S, θ̄)`,"
    set M := (insert 1 ((Finset.univ.filter (· ∉ S)).image (rho f' m' β' (Λ + l)))).max'
      (Finset.insert_nonempty _ _) with hM_def
    have hM : M < 2 - θS := by
      rw [Finset.max'_lt_iff]
      intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact hθbarS.1
      · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hy
        exact hout e (Finset.mem_filter.1 he).2
    set θbar := (M + (2 - θS)) / 2
    have hsin : ∀ e ∈ S, θbar < rho f' m' β' (Λ + l) e := fun e he => by
      have := hin e he
      simp only [θbar]
      linarith
    have hsout : ∀ e ∉ S, rho f' m' β' (Λ + l) e < θbar := fun e he => by
      have : rho f' m' β' (Λ + l) e ≤ M := Finset.le_max' _ _
        (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨e, by simp [he], rfl⟩))
      simp only [θbar]
      linarith
    -- "and by continuity of `ρ` (`lem:pwaffine`) they hold strictly near `(α_S, θ̄)`."
    have hnear := strict_near_point H (lt_of_le_of_lt hΛ0 hαS.1) hsin hsout
    -- "So there is a point `(α'_S, θ̄'_S)` with `A_{θ̄'_S}(α'_S) = S`, where `α'_S ∈ (Λ, Λ + 1)` is
    -- not a breakpoint and `ρ_e(α'_S) ≠ θ̄'_S` for all `e ∈ E`" (here `θ̄'_S = θ̄`).
    obtain ⟨α', hα'J, hα'B, hne, hA⟩ := exists_point_of_near H isOpen_Ioo hαS
      (((continuous_id.prodMk continuous_const).tendsto (Λ + l)).eventually hnear)
    exact ⟨α', θbar, hα'J, hα'B, hne, hA⟩
  -- (4) "Let `k` be the number of breakpoints in `(Λ, Λ + 1)`. … As `n` lines cut the plane into
  -- at most `1 + n + C(n, 2) = 1 + n(n + 1)/2` cells, we get `2^n ≤ (k + 1)(1 + n(n + 1)/2)`."
  have hcount := two_pow_le_cells H ordConnected_Ioo (fun α hα => lt_of_le_of_lt hΛ0 hα.1) hpts
  rw [Fintype.card_fin] at hcount
  -- (5) "Finally, let `σ := 1/(Λ + 1)` and replace `m` by `m/σ`. By `lem:ops`(b), the new best
  -- response is `α ↦ x*(α/σ)`."
  set σ : ℝ := 1 / (Λ + 1) with hσ_def
  have hσ : 0 < σ := one_div_pos.2 (by linarith)
  have hbr := (Hardness.ops_b_aux f' m' β' hσ).1
  -- "Its breakpoints are the old breakpoints multiplied by `σ`,"
  have hbp : breakpoints (bestResponse f' (fun e => m' e / σ) β') =
      (fun b => σ * b) '' breakpoints (bestResponse f' m' β') :=
    breakpoints_comp_div _ _ hσ hbr
  -- "and the `k` breakpoints in `(Λ, Λ + 1)` move into `(σΛ, 1) ⊆ (0, 1)`."
  have hmove : (fun b => σ * b) '' (Tracing.BP f' m' β' ∩ Ioo Λ (Λ + 1)) ⊆
      breakpoints (bestResponse f' (fun e => m' e / σ) β') ∩ Ioo (σ * Λ) 1 := by
    rintro _ ⟨b', ⟨hb'B, hb'1, hb'2⟩, rfl⟩
    refine ⟨hbp ▸ ⟨b', hb'B, rfl⟩, mul_lt_mul_of_pos_left hb'1 hσ, ?_⟩
    show 1 / (Λ + 1) * b' < 1
    rw [one_div_mul_eq_div, div_lt_one (by linarith)]
    exact hb'2
  have hIoo : Ioo (σ * Λ) 1 ⊆ Ioo 0 1 := Ioo_subset_Ioo_left (mul_nonneg hσ.le hΛ0)
  have H' : Tracing.Hyp f' (fun e => m' e / σ) β' :=
    ⟨hrank, H.beta, fun e => div_nonneg (H.reward e) hσ.le⟩
  have hfin : (breakpoints (bestResponse f' (fun e => m' e / σ) β') ∩ Ioo 0 1).Finite :=
    (Tracing.bp_finite H').inter_of_left _
  have hk : (Tracing.BP f' m' β' ∩ Ioo Λ (Λ + 1)).ncard ≤
      (breakpoints (bestResponse f' (fun e => m' e / σ) β') ∩ Ioo 0 1).ncard := by
    rw [← Set.ncard_image_of_injective _ (mul_right_injective₀ hσ.ne')]
    exact Set.ncard_le_ncard (hmove.trans (Set.inter_subset_inter_right _ hIoo)) hfin
  refine ⟨f', fun e => m' e / σ, β', H', hfin, ?_⟩
  exact (sub_one_le_of_two_pow_le hcount).trans (by exact_mod_cast hk)

end ExpBP

end Exp

end Stoc
