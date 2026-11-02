-- stamp r8 2026-11-02
import Mathlib
import ContractDesignPolymatroids.BestResponse.WaterFilling
import ContractDesignPolymatroids.OptimalShare.Continuation
import ContractDesignPolymatroids.OptimalShare.Reward

/-!
# Enumerating the pieces and an optimal contract

The STOC version, Section 3 (`stoc-sections/06-optimal-share.tex:45-51`, enumerating the pieces),
with the construction and the proof in Appendix B.4 (`sec:A-pieces`,
`stoc-sections/appB-quadratic.tex:455-512`): the enumeration of the pieces (`eq:A-enum`), Theorem
`thm:pieces` and Algorithm `alg:pieces`; and the remark after `lem:pwaffine`
(`06-optimal-share.tex:25`) that `U_P` is maximized on a piece at an end or at the vertex. The
pieces, event points, `B` (`numBP`) and `lem:eventcount` are in `ContractDesignPolymatroids/OptimalShare/Pieces.lean`,
the affine continuation and `lem:continuation` in `ContractDesignPolymatroids/OptimalShare/Continuation.lean`.

The enumeration (`appB-quadratic.tex:458-471`) runs with shares `α̂_0, α̂_1, …` (a sequence `s`):
`C_0 = ∅`, `𝓘_0 = ∅`, and while `C_k ≠ [0, 1]`, `α̂_k` is the midpoint of any connected component
of `[0, 1] \ C_k` (`midShare`), `C_{k+1} = C_k ∪ I(α̂_k)` (`covered`), and `I(α̂_k)` joins `𝓘_k`,
with its affine map `y_{α̂_k}`, if it is nondegenerate (`stored`); `IsRun f m β s K` says that `K`
iterations ran so. After covering `[0, 1]`, `(1 − α) mᵀy(α)` is maximized on each stored piece and
the best share is taken (`IsBestShare`).

`alg:pieces` is `AlgPieces`: a run of the while loop (lines 504-509, `IsRun`) that stops
(`C_K = [0, 1]`) and returns a best share over the stored pieces with its affine response (line
510, `IsBestShare`). Line 508 computes `x*(α̂_k)` by water-filling (`thm:waterfilling`): its output
`WaterFilling.waterFill f m β α̂_k` is `x*(α̂_k)` by `Stoc.WaterFilling.waterfilling`, and `v(α̂_k)`
is the vector of (`eq:velocity`) (`Stoc.velocity`); line 508 computes `I(α̂_k)` from them by the
procedure of `lem:continuation` (`Stoc.Tracing.continuation`): `I(α̂_k)` is the interval
`[Cont.lo, Cont.hi]` of the procedure for `x̂ = WaterFilling.waterFill f m β α̂_k` (`alg_step`).
The work of a run is counted as `WaterFilling.lean` counts that of water-filling: its submodular
minimizations (`runCalls`) and further evaluations of `f` (`runEvals`) are those of water-filling
(`WaterFilling.oracleCalls`, `WaterFilling.fEvals`) and of the affine continuation
(`Cont.contCalls`, `Cont.contEvals`) in every iteration. The ray computation of [GGJ17] inside the
affine continuation is cited, and its work is a parameter (`Cont.RayCost`) with the cited bounds as
hypotheses.

`thm:pieces` is `pieces_theorem`. Its proof follows the STOC version's, step by step:

1. each `C_k` is a finite union of closed intervals, so the midpoint of a component of
   `[0, 1] \ C_k` lies in `(0, 1)` and not in `C_k` (`run_mem`, with `midShare_mem`);
2. by `lem:continuation`, each step finds a new piece or a singleton event point that is never
   tried again (`run_step`);
3. by `lem:eventcount`, there are at most `(B + 1)(1 + C(n, 2)) + B ≤ (n + 2)²(B + 1)` steps
   (`run_length_le`);
4. at termination, the stored pieces cover `[0, 1]`, as a nonempty complement of their union would
   contain an interval (`stored_cover`), so every piece has been found (`stored_eq_pieces`);
5. maximizing on each piece gives an optimal contract (`isBestShare_optimal`; the maximum on a
   piece is attained, `quad_max`, so a best share exists, `exists_isBestShare`);
6. each step uses one best-response computation (water-filling, `waterfilling`: at most `2n(n + 1)`
   minimizations and `2n(2n + 1)` evaluations of `f`) and one affine continuation (`continuation`:
   at most `2c n²` minimizations and `(2c + 2) n³` evaluations, if each ray computation makes at
   most `c n²` minimizations and `c n²` evaluations, the cited `n² + O(n log² n)` and `O(n²)` of
   [GGJ17]) (`alg_step`); multiplying by the number of steps gives at most
   `(n + 2)²(B + 1)(2n(n + 1) + 2c n²)` minimizations and
   `(n + 2)²(B + 1)(2n(2n + 1) + (2c + 2) n³)` further evaluations of `f` (`run_costs`), that is, at
   most `(18c + 36) n⁴ (B + 1)` and `(18c + 72) n⁵ (B + 1)` (`costs_poly`);
7. with the time of a minimization by the algorithm of Iwata and Orlin [IO09], this gives the
   running time of `thm:pieces` (not formalised).

Not formalised: the running time of `thm:pieces` (step (7)); the arithmetic operations (the
`O(n⁶(B + 1) + n⁴(B + 1)²)` of its proof, with the `O(n²(B + 1))` operations per step for the sorted
interval list of `C_k`), which are not counted, as in `WaterFilling.lean`; and the ray computation
of [GGJ17], which is cited. Lemmas for
steps that the STOC version leaves implicit are marked "not in the paper": `quad_max` (the remark
after `lem:pwaffine` is stated without proof), `exists_isBestShare` (a best share exists, in "take
the best share"), `exists_run_stop` (the loop can always continue while `C ≠ [0, 1]`),
`costs_poly` (the explicit constants of the `O`-bounds), and the bookkeeping of `covered` and
`stored`.

`tracing` and `Outcome` state `thm:pieces` for one run (`share`, with a fixed choice of the
components), in the form that `ContractDesignPolymatroids/Subclasses/PolynomialClasses.lean` uses.

Taken over on 2026-10-20 from `Paper/OptimalShare/Tracing.lean` (the paper at Overleaf f035b19) for
the STOC version (`stoc.tex`); from then on this copy follows the STOC version. Reworked on
2026-10-25 to follow the STOC version's proof step by step: the enumeration keeps `𝓘_k`, any
component may be chosen, the pieces are found by the covering argument, the pieces, the event
points and the affine continuation moved to `Pieces.lean` and `Continuation.lean`, and the costs
are counted with water-filling in every iteration. Adapted on 2026-10-27 to the STOC version after
PR #88: step (3) counts with the new bound of `lem:eventcount`, `B + (B + 1) C(n, 2)` event points.
Adapted on 2026-11-02 to Max Klimm's final STOC version (repository 429ca68), whose `thm:pieces`
states a running time: `pieces_theorem` keeps the counts of its proof, and step (7) is quoted.
-/

namespace Stoc

namespace Tracing

open Finset Set

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {f : Finset E → ℝ} {m β : E → ℝ}

/-! ### The quadratic utility on a piece (`06-optimal-share.tex:25`) -/

omit [DecidableEq E] in
/-- On the affine continuation `y`, the reward `r(y(α)) = ∑ m_e y_e(α)` is affine in `α`:
`r⁰ + r¹ α` with `r⁰ = r(x̂) − α̂ r(v)` and `r¹ = r(v)`. -/
lemma reward_line (αh α : ℝ) : reward m (line f m β αh α) =
    (reward m (bestResponse f m β αh) - αh * reward m (velocity f m β αh)) +
      reward m (velocity f m β αh) * α := by
  unfold reward line
  have : ∀ e, m e * (bestResponse f m β αh e + (α - αh) * velocity f m β αh e) =
      m e * bestResponse f m β αh e + (α - αh) * (m e * velocity f m β αh e) := fun e => by ring
  rw [Finset.sum_congr rfl fun e _ => this e, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- The remark after `lem:pwaffine` (`stoc-sections/06-optimal-share.tex:25`; not in the paper:
the STOC version states it without proof): `(1 − α)(r⁰ + r¹ α)` is maximized over `[a, b]` at an
end or, if `r¹ > 0` and it lies in `[a, b]`, at the vertex `(r¹ − r⁰)/(2r¹)`; here `p = r⁰`,
`d = r¹`. For `d > 0`, by completing the square; for `d ≤ 0` the function is convex. -/
theorem quad_max {a b : ℝ} (hab : a ≤ b) (p d : ℝ) :
    ∃ α ∈ Icc a b, (α = a ∨ α = b ∨ (0 < d ∧ α = (d - p) / (2 * d))) ∧
      ∀ α' ∈ Icc a b, (1 - α') * (p + d * α') ≤ (1 - α) * (p + d * α) := by
  by_cases hd : 0 < d
  · set v := (d - p) / (2 * d)
    have hv : d - p = 2 * d * v := by simp only [v]; field_simp
    have hg : ∀ α, (1 - α) * (p + d * α) = (1 - v) * (p + d * v) - d * (α - v) ^ 2 := by
      intro α
      linear_combination (α - v) * hv
    rcases lt_or_ge v a with hva | hva
    · -- the vertex lies left of `[a, b]`
      refine ⟨a, ⟨le_rfl, hab⟩, Or.inl rfl, fun α' hα' => ?_⟩
      have h := mul_nonneg (mul_nonneg hd.le (sub_nonneg.2 hα'.1))
        (show 0 ≤ α' + a - 2 * v by linarith [hα'.1])
      rw [hg α', hg a]
      nlinarith [h]
    rcases le_or_gt v b with hvb | hvb
    · -- the vertex lies in `[a, b]`
      refine ⟨v, ⟨hva, hvb⟩, Or.inr (Or.inr ⟨hd, rfl⟩), fun α' _ => ?_⟩
      rw [hg α', hg v]
      nlinarith [mul_nonneg hd.le (sq_nonneg (α' - v))]
    · -- the vertex lies right of `[a, b]`
      refine ⟨b, ⟨hab, le_rfl⟩, Or.inr (Or.inl rfl), fun α' hα' => ?_⟩
      have h := mul_nonneg (mul_nonneg hd.le (sub_nonneg.2 hα'.2))
        (show 0 ≤ 2 * v - α' - b by linarith [hα'.2])
      rw [hg α', hg b]
      nlinarith [h]
  · -- `d ≤ 0`: the function is convex, so its maximum is at an end
    push Not at hd
    have key : ∀ α' ∈ Icc a b, (b - a) * ((1 - α') * (p + d * α')) ≤
        (b - α') * ((1 - a) * (p + d * a)) + (α' - a) * ((1 - b) * (p + d * b)) := by
      intro α' hα'
      have h3 : 0 ≤ -d * ((b - a) * ((α' - a) * (b - α'))) :=
        mul_nonneg (by linarith) (mul_nonneg (by linarith [hα'.1, hα'.2])
          (mul_nonneg (by linarith [hα'.1]) (by linarith [hα'.2])))
      nlinarith [h3]
    rcases le_total ((1 - b) * (p + d * b)) ((1 - a) * (p + d * a)) with hga | hga
    · refine ⟨a, ⟨le_rfl, hab⟩, Or.inl rfl, fun α' hα' => ?_⟩
      rcases hab.lt_or_eq with hlt | heq
      · have h4 := key α' hα'
        have h5 := mul_le_mul_of_nonneg_left hga (sub_nonneg.2 hα'.1)
        refine le_of_mul_le_mul_left ?_ (sub_pos.2 hlt)
        nlinarith [h4, h5]
      · have : α' = a := le_antisymm (heq ▸ hα'.2) hα'.1
        rw [this]
    · refine ⟨b, ⟨hab, le_rfl⟩, Or.inr (Or.inl rfl), fun α' hα' => ?_⟩
      rcases hab.lt_or_eq with hlt | heq
      · have h4 := key α' hα'
        have h5 := mul_le_mul_of_nonneg_left hga (sub_nonneg.2 hα'.2)
        refine le_of_mul_le_mul_left ?_ (sub_pos.2 hlt)
        nlinarith [h4, h5]
      · have : α' = b := le_antisymm hα'.2 (heq ▸ hα'.1)
        rw [this]

/-! ### The enumeration (`eq:A-enum`) and `alg:pieces` -/

/-- The midpoint rule of the enumeration (`appB-quadratic.tex:459-460`, `alg:pieces`, line 506): the
midpoint of the connected component of `[0, 1] \ C` that contains `p`. -/
noncomputable def midShare (C : Set ℝ) (p : ℝ) : ℝ :=
  (sInf (connectedComponentIn (Set.Icc (0 : ℝ) 1 \ C) p) +
    sSup (connectedComponentIn (Set.Icc (0 : ℝ) 1 \ C) p)) / 2

/-- The midpoint of a component of `[0, 1] \ C` lies in `[0, 1]` (plumbing). -/
lemma midShare_mem_Icc {C : Set ℝ} {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1 \ C) :
    midShare C p ∈ Icc (0 : ℝ) 1 := by
  set I := connectedComponentIn (Icc (0 : ℝ) 1 \ C) p
  have hIF : I ⊆ Icc (0 : ℝ) 1 \ C := connectedComponentIn_subset _ p
  have hne : I.Nonempty := ⟨p, mem_connectedComponentIn hp⟩
  have h1 : 0 ≤ sInf I := le_csInf hne fun x hx => (hIF hx).1.1
  have h2 : sSup I ≤ 1 := csSup_le hne fun x hx => (hIF hx).1.2
  have h3 : sInf I ≤ sSup I :=
    (csInf_le ⟨0, fun x hx => (hIF hx).1.1⟩ (mem_connectedComponentIn hp)).trans
      (le_csSup ⟨1, fun x hx => (hIF hx).1.2⟩ (mem_connectedComponentIn hp))
  show (sInf I + sSup I) / 2 ∈ Set.Icc (0 : ℝ) 1
  constructor <;> linarith

/-- Step (1) of the proof of `thm:pieces`: "every nonempty complementary component has positive
length and its midpoint lies in `(0, 1)`": if `C` is closed and `p ∈ [0, 1] \ C`, the connected
component of `[0, 1] \ C` that contains `p` has two distinct points (a ball about `p` avoids `C`),
and its midpoint lies in it, so in `(0, 1)` and not in `C`. -/
theorem midShare_mem {C : Set ℝ} (hC : IsClosed C) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1 \ C) :
    midShare C p ∈ Ioo (0 : ℝ) 1 \ C := by
  set F := Icc (0 : ℝ) 1 \ C
  set I := connectedComponentIn F p
  have hIF : I ⊆ F := connectedComponentIn_subset F p
  have hpI : p ∈ I := mem_connectedComponentIn hp
  have hne : I.Nonempty := ⟨p, hpI⟩
  have hoc : OrdConnected I := isPreconnected_connectedComponentIn.ordConnected
  have hbdd : BddAbove I := ⟨1, fun x hx => (hIF hx).1.2⟩
  have hbdd' : BddBelow I := ⟨0, fun x hx => (hIF hx).1.1⟩
  -- `I` contains a share `q ≠ p`, as `C` is closed.
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hC.isOpen_compl p hp.2
  have hsub : Icc (0 : ℝ) 1 ∩ Ioo (p - ε) (p + ε) ⊆ I := by
    refine IsPreconnected.subset_connectedComponentIn
      (ordConnected_Icc.inter ordConnected_Ioo).isPreconnected
      ⟨hp.1, by linarith, by linarith⟩ fun x hx => ⟨hx.1, fun hxC => hball ?_ hxC⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.2.1, hx.2.2]
  obtain ⟨q, hqI, hqp⟩ : ∃ q ∈ I, q ≠ p := by
    rcases lt_or_ge p 1 with h | h
    · refine ⟨min (p + ε / 2) 1, hsub ⟨⟨le_min (by linarith [hp.1.1]) zero_le_one,
        min_le_right _ _⟩, lt_min (by linarith) (by linarith),
        lt_of_le_of_lt (min_le_left _ _) (by linarith)⟩, ?_⟩
      exact (lt_min (by linarith) h).ne'
    · refine ⟨max (p - ε / 2) 0, hsub ⟨⟨le_max_right _ _, max_le (by linarith [hp.1.2])
        zero_le_one⟩, lt_of_lt_of_le (by linarith) (le_max_left _ _),
        max_lt (by linarith) (by linarith)⟩, ?_⟩
      exact (max_lt (by linarith) (by linarith)).ne
  set a := sInf I
  set b := sSup I
  have ha0 : 0 ≤ a := le_csInf hne fun x hx => (hIF hx).1.1
  have hb1 : b ≤ 1 := csSup_le hne fun x hx => (hIF hx).1.2
  have hab : a < b := by
    rcases lt_or_gt_of_ne hqp with h | h
    · exact lt_of_le_of_lt (csInf_le hbdd' hqI) (lt_of_lt_of_le h (le_csSup hbdd hpI))
    · exact lt_of_le_of_lt (csInf_le hbdd' hpI) (lt_of_lt_of_le h (le_csSup hbdd hqI))
  have hc : midShare C p = (a + b) / 2 := rfl
  obtain ⟨x, hxI, hx⟩ := exists_lt_of_csInf_lt hne (show a < (a + b) / 2 by linarith)
  obtain ⟨y, hyI, hy⟩ := exists_lt_of_lt_csSup hne (show (a + b) / 2 < b by linarith)
  have hcI : (a + b) / 2 ∈ I := hoc.out hxI hyI ⟨hx.le, hy.le⟩
  rw [hc]
  exact ⟨⟨by linarith, by linarith⟩, (hIF hcI).2⟩

section Enum

variable (f m β)

/-- (`eq:A-enum`): the covered set `C_k` after the steps with the shares `s 0, …, s (k − 1)`:
`C_0 = ∅` and `C_{k+1} = C_k ∪ I(α̂_k)`. -/
def covered (s : ℕ → ℝ) : ℕ → Set ℝ
  | 0 => ∅
  | k + 1 => covered s k ∪ found f m β (s k)

open Classical in
/-- (`eq:A-enum`) with the sentence after it: the collection `𝓘_k` of pieces after the steps with
the shares `s 0, …, s (k − 1)`, each stored with its affine map ("For each stored piece, retain its
affine map `y_{α̂_k}`"): `𝓘_0 = ∅`, and `𝓘_{k+1}` adds `I(α̂_k)`, with `y_{α̂_k}`, if `I(α̂_k)` is
nondegenerate. -/
noncomputable def stored (s : ℕ → ℝ) : ℕ → Set (Set ℝ × (ℝ → E → ℝ))
  | 0 => ∅
  | k + 1 => if (found f m β (s k)).Nontrivial then
      insert (found f m β (s k), line f m β (s k)) (stored s k) else stored s k

/-- `alg:pieces`, lines 504-509: a run of `K` iterations of the while loop with the shares
`s 0, …, s (K − 1)`: in iteration `k`, `C_k ≠ [0, 1]` and `α̂_k` is the midpoint of a connected
component of `[0, 1] \ C_k` (any one); `C` and `𝓘` are updated by (`eq:A-enum`) (`covered`,
`stored`), with `I(α̂_k)` computed from `x*(α̂_k)` and `v(α̂_k)` (`alg_step`). The loop stops after
a run of `K` iterations when `C_K = [0, 1]`. -/
def IsRun (s : ℕ → ℝ) (K : ℕ) : Prop :=
  ∀ k < K, covered f m β s k ≠ Set.Icc (0 : ℝ) 1 ∧
    ∃ p ∈ Icc (0 : ℝ) 1 \ covered f m β s k, s k = midShare (covered f m β s k) p

/-- `alg:pieces`, line 510, as described after (`eq:A-enum`): "maximize the corresponding
quadratic utility `U_P(α) = (1 − α) mᵀy_{α̂_k}(α)` on each piece and take the best share": `α⋆`,
with the affine map `y` of its piece, maximizes `U_P` on its stored piece, and is at least as good
as every maximizer on every stored piece; the algorithm returns `α⋆` and its affine response
`y(α⋆)`. -/
def IsBestShare (s : ℕ → ℝ) (K : ℕ) (αs : ℝ) (y : ℝ → E → ℝ) : Prop :=
  (∃ P, (P, y) ∈ stored f m β s K ∧ αs ∈ P ∧
    ∀ α ∈ P, (1 - α) * reward m (y α) ≤ (1 - αs) * reward m (y αs)) ∧
  ∀ P' y', (P', y') ∈ stored f m β s K → ∀ α' ∈ P',
    (∀ α ∈ P', (1 - α) * reward m (y' α) ≤ (1 - α') * reward m (y' α')) →
      (1 - α') * reward m (y' α') ≤ (1 - αs) * reward m (y αs)

/-- **`alg:pieces`** (Algorithm 2, `stoc-sections/appB-quadratic.tex:499-512`, "Computing an optimal
contract from the affine pieces"): the algorithm runs `K` iterations with the shares
`s 0, …, s (K − 1)` and returns the share `α⋆` with the affine response `y(α⋆)`:
* line 504, `C ← ∅`, `𝓘 ← ∅`: `covered` and `stored` at `0`;
* lines 505-506, while `C ≠ [0, 1]`, the midpoint `α̂` of a component of `[0, 1] \ C`: `IsRun`,
  and the loop stops at `C_K = [0, 1]`;
* line 507, `x*(α̂)` by `thm:waterfilling` and `v(α̂)` by (`eq:velocity`): the output
  `WaterFilling.waterFill f m β α̂_k` of water-filling, which is `x*(α̂_k)` (`waterfilling`), and
  `velocity f m β α̂_k`;
* line 508, `I(α̂)` by `lem:continuation` and the update of `C` and `𝓘` by (`eq:A-enum`): the
  interval `[Cont.lo, Cont.hi]` of the procedure from these, which is `I(α̂_k)` (`alg_step`), and
  `covered`, `stored`;
* line 510, the best share over the pieces in `𝓘` and its affine response: `IsBestShare`.
The work of the run is counted by `runCalls` and `runEvals`. -/
def AlgPieces (s : ℕ → ℝ) (K : ℕ) (αs : ℝ) (y : ℝ → E → ℝ) : Prop :=
  IsRun f m β s K ∧ covered f m β s K = Set.Icc (0 : ℝ) 1 ∧ IsBestShare f m β s K αs y

/-- The number of submodular minimizations of a run of `K` iterations: in iteration `k`, those of
water-filling at `α̂_k` (line 507, `WaterFilling.oracleCalls`) and those of the affine continuation
from its output (line 508, `Cont.contCalls`), for a ray computation with the work `R`. -/
noncomputable def runCalls (R : Cont.RayCost E) (s : ℕ → ℝ) (K : ℕ) : ℕ :=
  ∑ k ∈ Finset.range K, (WaterFilling.oracleCalls f m β (s k) +
    Cont.contCalls (WaterFilling.waterFill f m β (s k)) (velocity f m β (s k)) R)

/-- The number of further evaluations of `f` of a run of `K` iterations: in iteration `k`, those of
water-filling at `α̂_k` (line 507, `WaterFilling.fEvals`) and those of the affine continuation from
its output (line 508, `Cont.contEvals`), for a ray computation with the work `R`. -/
noncomputable def runEvals (R : Cont.RayCost E) (s : ℕ → ℝ) (K : ℕ) : ℕ :=
  ∑ k ∈ Finset.range K, (WaterFilling.fEvals f m β (s k) +
    Cont.contEvals f m β (s k) (WaterFilling.waterFill f m β (s k)) (velocity f m β (s k)) R)

end Enum

omit [DecidableEq E] in
/-- `C_k` is the union of the intervals `I(α̂_i)`, `i < k` (bookkeeping of (`eq:A-enum`), not in the
paper). -/
lemma mem_covered {s : ℕ → ℝ} {k : ℕ} {α : ℝ} :
    α ∈ covered f m β s k ↔ ∃ i < k, α ∈ found f m β (s i) := by
  induction k with
  | zero => simp [covered]
  | succ k ih =>
    rw [covered, Set.mem_union, ih]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · exact ⟨i, by omega, h⟩
      · exact ⟨k, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inl ⟨i, hi, h⟩
      · exact Or.inr h

omit [DecidableEq E] in
/-- `C_k ⊆ [0, 1]` (bookkeeping of (`eq:A-enum`), not in the paper). -/
lemma covered_subset (s : ℕ → ℝ) (k : ℕ) : covered f m β s k ⊆ Set.Icc (0 : ℝ) 1 := fun _ hα => by
  obtain ⟨i, -, hi⟩ := mem_covered.1 hα
  exact found_subset hi

omit [DecidableEq E] in
/-- The stored pieces with their maps are the pairs `(I(α̂_i), y_{α̂_i})` of the steps `i < k`
with a nondegenerate `I(α̂_i)` (bookkeeping of (`eq:A-enum`), not in the paper). -/
lemma mem_stored {s : ℕ → ℝ} {k : ℕ} {P : Set ℝ} {y : ℝ → E → ℝ} :
    (P, y) ∈ stored f m β s k ↔ ∃ i < k, (found f m β (s i)).Nontrivial ∧
      P = found f m β (s i) ∧ y = line f m β (s i) := by
  induction k with
  | zero => simp [stored]
  | succ k ih =>
    simp only [stored]
    split_ifs with h
    · rw [Set.mem_insert_iff, ih, Prod.mk.injEq]
      constructor
      · rintro (⟨rfl, rfl⟩ | ⟨i, hi, hrest⟩)
        · exact ⟨k, by omega, h, rfl, rfl⟩
        · exact ⟨i, by omega, hrest⟩
      · rintro ⟨i, hi, hnt, rfl, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact Or.inr ⟨i, hi, hnt, rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
    · rw [ih]
      constructor
      · rintro ⟨i, hi, hrest⟩
        exact ⟨i, by omega, hrest⟩
      · rintro ⟨i, hi, hnt, hP, hy⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact ⟨i, hi, hnt, hP, hy⟩
        · exact absurd hnt h

omit [DecidableEq E] in
/-- `𝓘_k` is finite (bookkeeping of (`eq:A-enum`), not in the paper). -/
lemma stored_finite (s : ℕ → ℝ) (k : ℕ) : (stored f m β s k).Finite := by
  induction k with
  | zero => simp [stored]
  | succ k ih =>
    simp only [stored]
    split_ifs
    · exact ih.insert _
    · exact ih

/-! ### The proof of `thm:pieces`, step by step -/

/-- Step (1) of the proof of `thm:pieces`: "Each `C_k` is a finite union of closed intervals, so
every nonempty complementary component has positive length and its midpoint lies in `(0, 1)`": in a
run, every share `α̂_k` lies in `(0, 1)` and not in `C_k`. -/
theorem run_mem (H : Hyp f m β) {s : ℕ → ℝ} {K : ℕ} (hrun : IsRun f m β s K) :
    ∀ k < K, s k ∈ Ioo (0 : ℝ) 1 \ covered f m β s k := by
  have h01 : ∀ k < K, s k ∈ Icc (0 : ℝ) 1 := fun k hk => by
    obtain ⟨-, p, hp, hsk⟩ := hrun k hk
    rw [hsk]
    exact midShare_mem_Icc hp
  intro k hk
  -- "Each `C_k` is a finite union of closed intervals", the intervals `I(α̂_i)` (`found_eq_Icc`)
  have hC : covered f m β s k =
      ⋃ i ∈ Finset.range k, Icc (loEnd f m β (s i)) (hiEnd f m β (s i)) := by
    ext α
    rw [mem_covered]
    simp only [Set.mem_iUnion, Finset.mem_range, exists_prop]
    refine exists_congr fun i => and_congr_right fun hi => ?_
    have h := h01 i (by omega)
    rw [found_eq_Icc H h.1 h.2]
  have hclosed : IsClosed (covered f m β s k) := by
    rw [hC]
    exact isClosed_biUnion_finset fun _ _ => isClosed_Icc
  -- "so every nonempty complementary component has positive length and its midpoint lies in
  -- `(0, 1)`" (`midShare_mem`)
  obtain ⟨-, p, hp, hsk⟩ := hrun k hk
  rw [hsk]
  exact midShare_mem hclosed hp

/-- Step (2) of the proof of `thm:pieces`: "By `lem:continuation`, each step discovers a new piece
or a singleton event point that is never tried again": at step `k` of a run, either `I(α̂_k)` is
nondegenerate, a piece (`continuation`), and not in `𝓘_k`, as `α̂_k ∉ C_k`; or `I(α̂_k) = {α̂_k}`,
and `α̂_k ∈ (0, 1)` is an event point (a non-event point lies in the interior of `I(α̂_k)`,
`continuation`) that no later step tries, as it lies in `C_j` for `j > k`. -/
theorem run_step (H : Hyp f m β) {s : ℕ → ℝ} {K : ℕ} (hrun : IsRun f m β s K) {k : ℕ}
    (hk : k < K) :
    ((found f m β (s k)).Nontrivial ∧ found f m β (s k) ∈ pieces f m β ∧
        found f m β (s k) ∉ Prod.fst '' stored f m β s k) ∨
      (found f m β (s k) = {s k} ∧ s k ∈ Ioo (0 : ℝ) 1 ∧ IsEvent f m β (s k) ∧
        ∀ j, k < j → j < K → s j ≠ s k) := by
  have hmem := run_mem H hrun
  obtain ⟨hk01, hkC⟩ := hmem k hk
  have hcont := continuation H hk01
  have hsk : s k ∈ found f m β (s k) := mem_found hk01.1.le hk01.2.le
  by_cases hnt : (found f m β (s k)).Nontrivial
  · -- "a new piece": a piece by `lem:continuation`, not stored before, as `α̂_k ∉ C_k`
    left
    refine ⟨hnt, hcont.2.1 hnt, ?_⟩
    rintro ⟨⟨P, y⟩, hPy, hP⟩
    obtain ⟨i, hi, -, hPi, -⟩ := mem_stored.1 hPy
    apply hkC
    rw [mem_covered]
    refine ⟨i, hi, ?_⟩
    rw [← hPi, show P = found f m β (s k) from hP]
    exact hsk
  · -- "or a singleton event point": by `lem:continuation`, a non-event point would lie in the
    -- interior of `I(α̂_k) = {α̂_k}`
    right
    have hsing : found f m β (s k) = {s k} :=
      (Set.not_nontrivial_iff.1 hnt).eq_singleton_of_mem hsk
    refine ⟨hsing, hk01, ?_, fun j hkj hj heq => ?_⟩
    · by_contra hne
      have := hcont.2.2 hne
      rw [hsing, interior_singleton] at this
      exact this
    · -- "that is never tried again": `α̂_k ∈ C_j`, but `α̂_j ∉ C_j`
      apply (hmem j hj).2
      rw [mem_covered]
      exact ⟨k, hkj, by rw [heq]; exact hsk⟩

/-- Step (3) of the proof of `thm:pieces`: "By `lem:eventcount`, the number of steps is at most
`(B + 1)(1 + C(n, 2)) + B ≤ (n + 2)²(B + 1)`": by step (2), the steps with a nondegenerate
`I(α̂_k)` find distinct pieces, of which there are at most `B + 1` (`appB-quadratic.tex:353`,
`pieces_finite_ncard_le`), and the other steps distinct event points in `(0, 1)`, of which there are
at most `B + (B + 1) C(n, 2)` (`eventcount`). -/
theorem run_length_le (H : Hyp f m β) {s : ℕ → ℝ} {K : ℕ} (hrun : IsRun f m β s K) :
    K ≤ (Fintype.card E + 2) ^ 2 * (numBP f m β + 1) := by
  classical
  set B := numBP f m β
  set n := Fintype.card E
  -- the steps with a nondegenerate `I(α̂_k)` and the others
  set N := (Finset.range K).filter fun k => (found f m β (s k)).Nontrivial
  set D := (Finset.range K).filter fun k => ¬ (found f m β (s k)).Nontrivial
  have hK : K = N.card + D.card := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_range]
  -- "each step discovers a new piece": the pieces of the steps in `N` are distinct
  obtain ⟨hPfin, hPcard⟩ := pieces_finite_ncard_le H
  have hN : N.card ≤ B + 1 := by
    have hmaps : Set.MapsTo (fun k => found f m β (s k)) (N : Set ℕ) (hPfin.toFinset : Set _) := by
      intro k hk
      obtain ⟨hkK, hnt⟩ := Finset.mem_filter.1 hk
      rcases run_step H hrun (Finset.mem_range.1 hkK) with ⟨-, hp, -⟩ | ⟨hsing, -⟩
      · exact (Set.Finite.mem_toFinset _).2 hp
      · exact absurd (hsing ▸ hnt) Set.not_nontrivial_singleton
    have hinj : Set.InjOn (fun k => found f m β (s k)) (N : Set ℕ) := by
      -- the piece of a later step is new
      have key : ∀ i ∈ N, ∀ j ∈ N, i < j → found f m β (s i) ≠ found f m β (s j) := by
        intro i hi j hj hij heq
        obtain ⟨hjK, -⟩ := Finset.mem_filter.1 hj
        obtain ⟨-, hnti⟩ := Finset.mem_filter.1 hi
        rcases run_step H hrun (Finset.mem_range.1 hjK) with ⟨-, -, hnew⟩ | ⟨hsing, -⟩
        · exact hnew ⟨(found f m β (s i), line f m β (s i)),
            mem_stored.2 ⟨i, hij, hnti, rfl, rfl⟩, heq⟩
        · exact absurd (hsing ▸ (Finset.mem_filter.1 hj).2) Set.not_nontrivial_singleton
      intro i hi j hj heq
      rcases lt_trichotomy i j with h | h | h
      · exact absurd heq (key i hi j hj h)
      · exact h
      · exact absurd heq.symm (key j hj i hi h)
    have := Finset.card_le_card_of_injOn _ hmaps hinj
    rw [← Set.ncard_eq_toFinset_card _ hPfin] at this
    exact this.trans hPcard
  -- "or a singleton event point that is never tried again": the shares of the steps in `D` are
  -- distinct event points in `(0, 1)`
  obtain ⟨-, hEfin, hEcard⟩ := eventcount H
  have hD : D.card ≤ B + (B + 1) * n.choose 2 := by
    have hstepD : ∀ k ∈ D, found f m β (s k) = {s k} ∧ s k ∈ Ioo (0 : ℝ) 1 ∧
        IsEvent f m β (s k) ∧ ∀ j, k < j → j < K → s j ≠ s k := by
      intro k hk
      obtain ⟨hkK, hnt⟩ := Finset.mem_filter.1 hk
      rcases run_step H hrun (Finset.mem_range.1 hkK) with ⟨hnt', -⟩ | h
      · exact absurd hnt' hnt
      · exact h
    have hmaps : Set.MapsTo s (D : Set ℕ) (hEfin.toFinset : Set ℝ) := fun k hk =>
      (Set.Finite.mem_toFinset _).2 ⟨(hstepD k hk).2.1, (hstepD k hk).2.2.1⟩
    have hinj : Set.InjOn s (D : Set ℕ) := by
      intro i hi j hj heq
      have hjK := Finset.mem_range.1 (Finset.mem_filter.1 hj).1
      have hiK := Finset.mem_range.1 (Finset.mem_filter.1 hi).1
      rcases lt_trichotomy i j with h | h | h
      · exact absurd heq.symm ((hstepD i hi).2.2.2 j h hjK)
      · exact h
      · exact absurd heq ((hstepD j hj).2.2.2 i h hiK)
    have := Finset.card_le_card_of_injOn s hmaps hinj
    rw [← Set.ncard_eq_toFinset_card _ hEfin] at this
    exact this.trans hEcard
  have hch : n.choose 2 ≤ n * n := by
    have := Nat.choose_le_pow n 2
    rwa [pow_two] at this
  -- "the number of steps is at most `(B + 1)(1 + C(n, 2)) + B ≤ (n + 2)²(B + 1)`"
  calc K = N.card + D.card := hK
    _ ≤ (B + 1) + (B + (B + 1) * n.choose 2) := add_le_add hN hD
    _ = (B + 1) * (1 + n.choose 2) + B := by ring
    _ ≤ (n + 2) ^ 2 * (B + 1) := by
        have h1 : 1 + n.choose 2 + 1 ≤ (n + 2) ^ 2 := by nlinarith [hch]
        nlinarith [Nat.mul_le_mul_left (B + 1) h1]

omit [DecidableEq E] in
/-- On a stored piece, `x*` is its affine map (`lem:continuation`: `x* = y_{α̂_k}` on `I(α̂_k)`,
`agree_on_found`). -/
lemma stored_agree {s : ℕ → ℝ} {K : ℕ} {P : Set ℝ} {y : ℝ → E → ℝ}
    (hPy : (P, y) ∈ stored f m β s K) : ∀ α ∈ P, bestResponse f m β α = y α := by
  obtain ⟨i, -, -, rfl, rfl⟩ := mem_stored.1 hPy
  exact fun α hα => agree_on_found α hα

/-- Step (4) of the proof of `thm:pieces`: "At termination, finitely many closed pieces and
singletons cover `[0, 1]`. The pieces alone cover it, since a nonempty complement of their union
would contain an interval": the union `U` of the stored pieces is closed, and `[0, 1] \ U` lies in
the finite set of the shares of the steps with a singleton (step (2)); a share of `[0, 1] \ U` would
have a neighborhood in `[0, 1] \ U`, an infinite set. -/
theorem stored_cover (H : Hyp f m β) {s : ℕ → ℝ} {K : ℕ} (hrun : IsRun f m β s K)
    (hstop : covered f m β s K = Set.Icc (0 : ℝ) 1) :
    Icc (0 : ℝ) 1 ⊆ ⋃ P ∈ Prod.fst '' stored f m β s K, P := by
  classical
  set U := ⋃ P ∈ Prod.fst '' stored f m β s K, P
  -- "finitely many closed pieces and singletons cover `[0, 1]`"
  have hcov : ∀ α ∈ Icc (0 : ℝ) 1, α ∈ U ∨ ∃ k < K, α = s k := by
    intro α hα
    rw [← hstop, mem_covered] at hα
    obtain ⟨k, hk, hαk⟩ := hα
    rcases run_step H hrun hk with ⟨hnt, -, -⟩ | ⟨hsing, -⟩
    · left
      exact Set.mem_biUnion (x := found f m β (s k))
        ⟨(found f m β (s k), line f m β (s k)), mem_stored.2 ⟨k, hk, hnt, rfl, rfl⟩, rfl⟩ hαk
    · right
      rw [hsing] at hαk
      exact ⟨k, hk, hαk⟩
  -- the union of the stored pieces is closed
  have hUcl : IsClosed U := by
    refine Set.Finite.isClosed_biUnion ((stored_finite s K).image _) fun P hP => ?_
    obtain ⟨⟨P', y⟩, hPy, rfl⟩ := hP
    obtain ⟨i, hi, -, hPi, -⟩ := mem_stored.1 hPy
    have h := (run_mem H hrun i hi).1
    show IsClosed P'
    rw [hPi, found_eq_Icc H h.1.le h.2.le]
    exact isClosed_Icc
  -- "a nonempty complement of their union would contain an interval": a share `α ∈ [0, 1] \ U` has
  -- a neighborhood `J` in `[0, 1]` that avoids `U`, so `J` lies in the finite set of the shares,
  -- but `J` contains an interval
  intro α hα
  by_contra hαU
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hUcl.isOpen_compl α hαU
  have hJ : Ioo (max (α - ε) 0) (min (α + ε) 1) ⊆ ((Finset.range K).image s : Set ℝ) := by
    intro γ hγ
    have hγ01 : γ ∈ Icc (0 : ℝ) 1 :=
      ⟨(le_max_right _ _).trans hγ.1.le, hγ.2.le.trans (min_le_right _ _)⟩
    rcases hcov γ hγ01 with h | ⟨k, hk, rfl⟩
    · refine absurd h (hball ?_)
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor
      · linarith [le_max_left (α - ε) 0, hγ.1]
      · linarith [min_le_left (α + ε) 1, hγ.2]
    · exact Finset.mem_coe.2 (Finset.mem_image_of_mem s (Finset.mem_range.2 hk))
  have hlt : max (α - ε) 0 < min (α + ε) 1 :=
    max_lt (lt_min (by linarith) (by linarith [hα.2])) (lt_min (by linarith [hα.1]) one_pos)
  exact Set.Ioo_infinite hlt ((Finset.finite_toSet _).subset hJ)

/-- Step (4) of the proof of `thm:pieces`, the conclusion: "so every piece has been found": when the
run stops, the stored pieces are exactly the pieces of `x*`. The stored pieces are pieces by step
(2); conversely, the midpoint of a piece, a non-breakpoint share of `(0, 1)`, lies in a stored piece
(`stored_cover`), and inside it, so the two pieces coincide (`piece_eq_of_mem`). -/
theorem stored_eq_pieces (H : Hyp f m β) {s : ℕ → ℝ} {K : ℕ} (hrun : IsRun f m β s K)
    (hstop : covered f m β s K = Set.Icc (0 : ℝ) 1) :
    Prod.fst '' stored f m β s K = pieces f m β := by
  have hsub : Prod.fst '' stored f m β s K ⊆ pieces f m β := by
    rintro _ ⟨⟨P, y⟩, hPy, rfl⟩
    obtain ⟨i, hi, hnt, hPi, -⟩ := mem_stored.1 hPy
    rcases run_step H hrun hi with ⟨-, hp, -⟩ | ⟨hsing, -⟩
    · show P ∈ pieces f m β
      rw [hPi]
      exact hp
    · exact absurd (hsing ▸ hnt) Set.not_nontrivial_singleton
  refine Set.Subset.antisymm hsub fun P hP => ?_
  obtain ⟨a, b, hp, rfl⟩ := (mem_pieces_iff H).1 hP
  -- the midpoint `μ` of the piece `[a, b]` lies in a stored piece `Q`
  have hμ : (a + b) / 2 ∈ Ioo a b := ⟨by linarith [hp.2.1], by linarith [hp.2.1]⟩
  set μ := (a + b) / 2
  obtain ⟨Q, hQ, hμQ⟩ := Set.mem_iUnion₂.1
    (stored_cover H hrun hstop ⟨hp.1.trans hμ.1.le, hμ.2.le.trans hp.2.2.1⟩)
  obtain ⟨a', b', hp', rfl⟩ := (mem_pieces_iff H).1 (hsub hQ)
  -- `μ` is no end of `Q = [a', b']`: the ends are `0`, `1` or breakpoints
  have hμ' : μ ∈ Ioo a' b' := by
    refine ⟨lt_of_le_of_ne hμQ.1 fun h => ?_, lt_of_le_of_ne hμQ.2 fun h => ?_⟩
    · rcases hp'.2.2.2.2.1 with h0 | h0
      · linarith [hp.1, hμ.1]
      · exact hp.2.2.2.1 μ hμ (h ▸ h0)
    · rcases hp'.2.2.2.2.2 with h1 | h1
      · linarith [hp.2.2.1, hμ.2]
      · exact hp.2.2.2.1 μ hμ (h.symm ▸ h1)
  obtain ⟨rfl, rfl⟩ := piece_eq_of_mem hp hp' hμ hμ'
  exact hQ

/-- The maximum of `U_P(α) = (1 − α) mᵀy(α)` on a stored piece is attained, at an end or at the
vertex (`quad_max`, the remark after `lem:pwaffine`), as `mᵀy` is affine (`reward_line`) and the
piece is a closed interval (`found_eq_Icc`). -/
lemma exists_max_stored (H : Hyp f m β) {s : ℕ → ℝ} {K : ℕ} (hrun : IsRun f m β s K) {P : Set ℝ}
    {y : ℝ → E → ℝ} (hPy : (P, y) ∈ stored f m β s K) :
    ∃ α ∈ P, ∀ α' ∈ P, (1 - α') * reward m (y α') ≤ (1 - α) * reward m (y α) := by
  obtain ⟨i, hi, hnt, rfl, rfl⟩ := mem_stored.1 hPy
  have h := (run_mem H hrun i hi).1
  rw [found_eq_Icc H h.1.le h.2.le] at hnt ⊢
  have hle : loEnd f m β (s i) ≤ hiEnd f m β (s i) := by
    by_contra hlt
    exact hnt.not_subsingleton (Set.subsingleton_Icc_of_ge (not_le.1 hlt).le)
  obtain ⟨α, hα, -, hmax⟩ := quad_max hle
    (reward m (bestResponse f m β (s i)) - s i * reward m (velocity f m β (s i)))
    (reward m (velocity f m β (s i)))
  refine ⟨α, hα, fun α' hα' => ?_⟩
  rw [reward_line, reward_line]
  exact hmax α' hα'

/-- Step (5) of the proof of `thm:pieces`: "Maximizing on each piece therefore gives an optimal
share": a best share `α⋆` over the stored pieces, with the affine map `y` of its piece, maximizes
`U_P(α) = (1 − α) r(x*(α))` over `[0, 1]`, and `y(α⋆) = x*(α⋆)`. Every `α ∈ [0, 1]` lies in a stored
piece (step (4)), on which `x*` is its affine map (`stored_agree`), and `U_P(α)` is at most the
maximum on that piece (`exists_max_stored`), which is at most `U_P(α⋆)`. -/
theorem isBestShare_optimal (H : Hyp f m β) {s : ℕ → ℝ} {K : ℕ} (hrun : IsRun f m β s K)
    (hstop : covered f m β s K = Set.Icc (0 : ℝ) 1) {αs : ℝ} {y : ℝ → E → ℝ}
    (hbest : IsBestShare f m β s K αs y) :
    αs ∈ Icc (0 : ℝ) 1 ∧
      (∀ α ∈ Icc (0 : ℝ) 1, profit (grossValue f m β) α ≤ profit (grossValue f m β) αs) ∧
      y αs = bestResponse f m β αs := by
  obtain ⟨⟨P, hPy, hαsP, -⟩, hbest2⟩ := hbest
  have hag : bestResponse f m β αs = y αs := stored_agree hPy αs hαsP
  have hP01 : P ⊆ Set.Icc (0 : ℝ) 1 := by
    obtain ⟨i, -, -, rfl, -⟩ := mem_stored.1 hPy
    exact found_subset
  refine ⟨hP01 hαsP, fun α hα => ?_, hag.symm⟩
  obtain ⟨P', ⟨⟨P'', y'⟩, hP'y', rfl⟩, hαP'⟩ := Set.mem_iUnion₂.1 (stored_cover H hrun hstop hα)
  obtain ⟨α', hα'P, hα'max⟩ := exists_max_stored H hrun hP'y'
  calc profit (grossValue f m β) α = (1 - α) * reward m (y' α) := by
        rw [profit, grossValue, stored_agree hP'y' α hαP']
    _ ≤ (1 - α') * reward m (y' α') := hα'max α hαP'
    _ ≤ (1 - αs) * reward m (y αs) := hbest2 _ _ hP'y' α' hα'P hα'max
    _ = profit (grossValue f m β) αs := by rw [profit, grossValue, hag]

/-- Step (5): a best share exists when the run stops (not in the paper: the STOC version leaves it
implicit, in "take the best share"): there is a stored piece (the stored pieces cover `[0, 1]`,
step (4)), there are finitely many, and the maximum on each is attained (`exists_max_stored`); the
best of these maximizers is a best share. -/
theorem exists_isBestShare (H : Hyp f m β) {s : ℕ → ℝ} {K : ℕ} (hrun : IsRun f m β s K)
    (hstop : covered f m β s K = Set.Icc (0 : ℝ) 1) : ∃ αs y, IsBestShare f m β s K αs y := by
  classical
  -- a maximizer `a q` on every stored piece `q = (P, y)`
  have hmax : ∀ q : Set ℝ × (ℝ → E → ℝ), ∃ α : ℝ, q ∈ stored f m β s K →
      α ∈ q.1 ∧ ∀ α' ∈ q.1, (1 - α') * reward m (q.2 α') ≤ (1 - α) * reward m (q.2 α) := by
    intro q
    by_cases hq : q ∈ stored f m β s K
    · obtain ⟨α, hα, hα'⟩ := exists_max_stored H hrun (P := q.1) (y := q.2) hq
      exact ⟨α, fun _ => ⟨hα, hα'⟩⟩
    · exact ⟨0, fun h => absurd h hq⟩
  choose a ha using hmax
  -- the stored pieces form a nonempty finite set
  set T := (stored_finite (f := f) (m := m) (β := β) s K).toFinset
  have hT : T.Nonempty := by
    obtain ⟨_, ⟨q, hq, rfl⟩, -⟩ := Set.mem_iUnion₂.1
      (stored_cover H hrun hstop ⟨le_rfl, zero_le_one⟩)
    exact ⟨q, (Set.Finite.mem_toFinset _).2 hq⟩
  -- the best of the maximizers
  obtain ⟨q₀, hq₀T, hbest⟩ := T.exists_max_image (fun q => (1 - a q) * reward m (q.2 (a q))) hT
  have hq₀ : q₀ ∈ stored f m β s K := (Set.Finite.mem_toFinset _).1 hq₀T
  refine ⟨a q₀, q₀.2, ⟨q₀.1, hq₀, (ha q₀ hq₀).1, (ha q₀ hq₀).2⟩,
    fun P' y' hP'y' α' hα'P hα'max => ?_⟩
  -- a maximizer `α'` on `(P', y')` has the value of `a (P', y')`
  have h1 := (ha (P', y') hP'y').2 α' hα'P
  have h2 := hbest (P', y') ((Set.Finite.mem_toFinset _).2 hP'y')
  exact h1.trans h2

/-- Lines 508-509 of `alg:pieces`: in every iteration `k` of a run, water-filling computes
`x*(α̂_k)` (`thm:waterfilling`, `waterfilling`); the procedure of `lem:continuation` computes
`I(α̂_k)` from its output `x̂_k` and `v(α̂_k)` (`continuation`); and the affine map retained with
`I(α̂_k)` is `y_{α̂_k}(α) = x̂_k + (α − α̂_k) v(α̂_k)` (`eq:A-cont`). -/
theorem alg_step (H : Hyp f m β) {s : ℕ → ℝ} {K : ℕ} (hrun : IsRun f m β s K) {k : ℕ}
    (hk : k < K) :
    WaterFilling.waterFill f m β (s k) = bestResponse f m β (s k) ∧
      found f m β (s k) =
        Icc (Cont.lo f m β (s k) (WaterFilling.waterFill f m β (s k)) (velocity f m β (s k)))
          (Cont.hi f m β (s k) (WaterFilling.waterFill f m β (s k)) (velocity f m β (s k))) ∧
      line f m β (s k) = fun α e =>
        WaterFilling.waterFill f m β (s k) e + (α - s k) * velocity f m β (s k) e := by
  have hk01 := (run_mem H hrun k hk).1
  -- line 507: water-filling computes `x*(α̂_k)` (`thm:waterfilling`)
  have hwf := (WaterFilling.waterfilling ⟨H.rank, H.beta, H.reward, hk01.1.le⟩).1
  -- line 508: the procedure of `lem:continuation` from `x*(α̂_k)` and `v(α̂_k)` computes `I(α̂_k)`,
  -- and `y_{α̂_k}` is the affine continuation of `x*(α̂_k)`
  refine ⟨hwf, ?_, ?_⟩
  · rw [hwf]
    exact (continuation H hk01).1.2.1
  · rw [hwf]
    rfl

/-- Step (6) of the proof of `thm:pieces`: "Each step uses one best-response computation and one
affine continuation, costing `O(n²)` minimizations, `O(n³)` further rank evaluations, and `O(n⁴)`
further arithmetic operations by the proof of `thm:waterfilling` and `lem:continuation`. …
Multiplying gives `O(n⁴(B + 1))` submodular minimizations, `O(n⁵(B + 1))` further evaluations of
`f`, …". If each ray computation makes at most `c n²` submodular minimizations and at most `c n²`
further evaluations of `f` (the cited bounds), then in iteration `k` water-filling makes at most
`2n(n + 1)` minimizations and `2n(2n + 1)` further evaluations (the counts of the proof of
`thm:waterfilling`, which `waterfilling` states), and the affine
continuation from its output `x*(α̂_k)` at most `2c n²` and `(2c + 2) n³` (`continuation`); and
there are at most `(n + 2)²(B + 1)` iterations (step (3)). The arithmetic operations, with the
`O(n²(B + 1))` operations per step for the sorted interval list of `C_k`, are not counted. -/
theorem run_costs (H : Hyp f m β) {s : ℕ → ℝ} {K : ℕ} (hrun : IsRun f m β s K)
    (R : Cont.RayCost E) {c : ℕ}
    (hc : ∀ x w, R.calls x w ≤ c * Fintype.card E ^ 2 ∧ R.evals x w ≤ c * Fintype.card E ^ 2) :
    runCalls f m β R s K ≤ (Fintype.card E + 2) ^ 2 * (numBP f m β + 1) *
        (2 * Fintype.card E * (Fintype.card E + 1) + 2 * c * Fintype.card E ^ 2) ∧
      runEvals f m β R s K ≤ (Fintype.card E + 2) ^ 2 * (numBP f m β + 1) *
        (2 * Fintype.card E * (2 * Fintype.card E + 1) + (2 * c + 2) * Fintype.card E ^ 3) := by
  set n := Fintype.card E
  -- "Each step uses one best-response computation and one affine continuation, costing … by the
  -- proof of `thm:waterfilling` and `lem:continuation`."
  have hstep : ∀ k ∈ Finset.range K,
      WaterFilling.oracleCalls f m β (s k) +
          Cont.contCalls (WaterFilling.waterFill f m β (s k)) (velocity f m β (s k)) R ≤
        2 * n * (n + 1) + 2 * c * n ^ 2 ∧
      WaterFilling.fEvals f m β (s k) + Cont.contEvals f m β (s k)
          (WaterFilling.waterFill f m β (s k)) (velocity f m β (s k)) R ≤
        2 * n * (2 * n + 1) + (2 * c + 2) * n ^ 3 := by
    intro k hk
    have hk01 := (run_mem H hrun k (Finset.mem_range.1 hk)).1
    -- water-filling computes `x*(α̂_k)` with the counts of the proof of `thm:waterfilling`,
    obtain ⟨hwf, hcalls, hevals⟩ :=
      WaterFilling.waterfilling ⟨H.rank, H.beta, H.reward, hk01.1.le⟩
    -- and the affine continuation from `x*(α̂_k)` has its counts (`lem:continuation`)
    obtain ⟨hc1, hc2⟩ := (continuation H hk01).1.2.2 R c hc
    rw [hwf]
    exact ⟨Nat.add_le_add hcalls hc1, Nat.add_le_add hevals hc2⟩
  -- "Multiplying gives `O(n⁴(B + 1))` submodular minimizations, `O(n⁵(B + 1))` further evaluations
  -- of `f`, …", with at most `(n + 2)²(B + 1)` steps (step (3))
  have hK := run_length_le H hrun
  constructor
  · calc runCalls f m β R s K ≤ ∑ _k ∈ Finset.range K, (2 * n * (n + 1) + 2 * c * n ^ 2) :=
          Finset.sum_le_sum fun k hk => (hstep k hk).1
      _ = K * (2 * n * (n + 1) + 2 * c * n ^ 2) := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ hK
  · calc runEvals f m β R s K
          ≤ ∑ _k ∈ Finset.range K, (2 * n * (2 * n + 1) + (2 * c + 2) * n ^ 3) :=
          Finset.sum_le_sum fun k hk => (hstep k hk).2
      _ = K * (2 * n * (2 * n + 1) + (2 * c + 2) * n ^ 3) := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ hK

/-- The totals of step (6) as the `O(n⁴(B + 1))` and `O(n⁵(B + 1))` of `thm:pieces` with explicit
constants (not in the paper, which states the `O`-bounds): `(n + 2)² ≤ 9n²` for `n ≥ 1`, so
`(n + 2)²(B + 1)(2n(n + 1) + 2c n²) ≤ (18c + 36) n⁴ (B + 1)` and
`(n + 2)²(B + 1)(2n(2n + 1) + (2c + 2) n³) ≤ (18c + 72) n⁵ (B + 1)`. -/
lemma costs_poly (n B c : ℕ) :
    (n + 2) ^ 2 * (B + 1) * (2 * n * (n + 1) + 2 * c * n ^ 2) ≤
        (18 * c + 36) * n ^ 4 * (B + 1) ∧
      (n + 2) ^ 2 * (B + 1) * (2 * n * (2 * n + 1) + (2 * c + 2) * n ^ 3) ≤
        (18 * c + 72) * n ^ 5 * (B + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : (n + 2) ^ 2 ≤ 9 * n ^ 2 := by nlinarith
    have h2 : 2 * n * (n + 1) + 2 * c * n ^ 2 ≤ (4 + 2 * c) * n ^ 2 := by nlinarith
    have e1 : n ^ 2 ≤ n ^ 3 := Nat.pow_le_pow_right hn (by norm_num)
    have e2 : n ≤ n ^ 3 := by
      calc n = n ^ 1 := (pow_one n).symm
        _ ≤ n ^ 3 := Nat.pow_le_pow_right hn (by norm_num)
    have h3 : 2 * n * (2 * n + 1) + (2 * c + 2) * n ^ 3 ≤ (2 * c + 8) * n ^ 3 := by nlinarith
    constructor
    · calc (n + 2) ^ 2 * (B + 1) * (2 * n * (n + 1) + 2 * c * n ^ 2)
          ≤ 9 * n ^ 2 * (B + 1) * ((4 + 2 * c) * n ^ 2) := by gcongr
        _ = (18 * c + 36) * n ^ 4 * (B + 1) := by ring
    · calc (n + 2) ^ 2 * (B + 1) * (2 * n * (2 * n + 1) + (2 * c + 2) * n ^ 3)
          ≤ 9 * n ^ 2 * (B + 1) * ((2 * c + 8) * n ^ 3) := by gcongr
        _ = (18 * c + 72) * n ^ 5 * (B + 1) := by ring

/-! ### A run that stops -/

section Canonical

variable (f m β)

open Classical in
/-- A choice of the component (not in the paper, for the existence of a run): the midpoint of the
component of `[0, 1] \ C` that contains some share of `[0, 1] \ C`, and `0` if there is none. -/
noncomputable def nextShare (C : Set ℝ) : ℝ :=
  if h : (Icc (0 : ℝ) 1 \ C).Nonempty then midShare C h.some else 0

/-- The covered sets of the run with the choice `nextShare` (not in the paper). -/
noncomputable def cov : ℕ → Set ℝ
  | 0 => ∅
  | k + 1 => cov k ∪ found f m β (nextShare (cov k))

/-- The shares of the run with the choice `nextShare` (not in the paper). -/
noncomputable def share (k : ℕ) : ℝ := nextShare (cov f m β k)

end Canonical

omit [DecidableEq E] in
lemma covered_share (k : ℕ) : covered f m β (share f m β) k = cov f m β k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [covered, ih, cov, share]

/-- The while loop can always continue while `C ≠ [0, 1]`, so by step (3) some run stops (not in
the paper: the STOC version leaves implicit that a component can always be chosen). The run
`share` stops after at most `(n + 2)²(B + 1)` iterations. -/
theorem exists_run_stop (H : Hyp f m β) :
    ∃ K ≤ (Fintype.card E + 2) ^ 2 * (numBP f m β + 1),
      IsRun f m β (share f m β) K ∧ covered f m β (share f m β) K = Set.Icc (0 : ℝ) 1 := by
  classical
  set N := (Fintype.card E + 2) ^ 2 * (numBP f m β + 1)
  -- while `C_k ≠ [0, 1]`, the share `nextShare C_k` is the midpoint of a component
  have hrun : ∀ K, (∀ k < K, covered f m β (share f m β) k ≠ Set.Icc (0 : ℝ) 1) →
      IsRun f m β (share f m β) K := by
    intro K hK k hk
    refine ⟨hK k hk, ?_⟩
    have hne : (Icc (0 : ℝ) 1 \ covered f m β (share f m β) k).Nonempty :=
      Set.sdiff_nonempty.2 fun h => hK k hk ((covered_subset _ k).antisymm h)
    refine ⟨hne.some, hne.some_mem, ?_⟩
    show nextShare (cov f m β k) = _
    rw [← covered_share, nextShare, dite_eq_left hne]
  have hex : ∃ K, covered f m β (share f m β) K = Set.Icc (0 : ℝ) 1 := by
    by_contra hcon
    push Not at hcon
    have := run_length_le H (hrun (N + 1) fun k _ => hcon k)
    omega
  refine ⟨Nat.find hex, ?_, hrun _ fun k hk => Nat.find_min hex hk, Nat.find_spec hex⟩
  by_contra hlt
  push Not at hlt
  have := run_length_le H (hrun (N + 1) fun k hk => Nat.find_min hex (by omega))
  omega

/-! ### `thm:pieces` -/

/-- **`thm:pieces`** (Theorem 3.7, statement `stoc-sections/06-optimal-share.tex:48-51`, proof
`stoc-sections/appB-quadratic.tex:474-495`, with the enumeration (`eq:A-enum`) :458-471 and
`alg:pieces` :499-512), under the standing assumptions, with `B` the number of breakpoints in
`(0, 1)` (`numBP`) and `n = |E|`: all pieces of `x*` in `[0, 1]`, their affine responses, and an
optimal contract can be computed in time `O(n⁹(B + 1) log n)·FO + O(n¹⁰(B + 1) log n + n⁴(B + 1)²)`.
The running time is not formalised; the Lean has what the proof derives it from: `alg:pieces`
(`AlgPieces`) computes them with at most `(n + 2)²(B + 1)` best-response computations, and
altogether `O(n⁴(B + 1))` submodular minimizations and `O(n⁵(B + 1))` further evaluations of `f`:

1. every run has at most `(n + 2)²(B + 1)` iterations, and some run stops (`C = [0, 1]`);
2. when the algorithm returns `α⋆` and `y`, the stored pieces are all pieces of `x*`, each with its
   affine response (`x* = y'` on it), and `α⋆` is an optimal contract with `y(α⋆) = x*(α⋆)`; and
   when a run stops, the algorithm returns (a best share exists);
3. in every iteration `k`, one best-response computation, by water-filling, computes `x*(α̂_k)`,
   and the affine continuation computes `I(α̂_k)` and its affine map `y_{α̂_k}` from it
   (`alg_step`);
4. the costs: if each ray computation of [GGJ17] (cited, `Cont.RayCost`) makes at most `c n²`
   submodular minimizations and at most `c n²` further evaluations of `f` (the cited `n² + O(n log²
   n)` and `O(n²)`, with a common constant `c`), a run makes at most `(18c + 36) n⁴ (B + 1)`
   submodular minimizations (`runCalls`) and at most `(18c + 72) n⁵ (B + 1)` further evaluations of
   `f` (`runEvals`), the `O(n⁴(B + 1))` and `O(n⁵(B + 1))` of the STOC version with explicit
   constants. The `O(n⁶(B + 1) + n⁴(B + 1)²)` further arithmetic operations are not counted.

Steps: (1) `run_mem`; (2) `run_step`; (3) `run_length_le`; (4) `stored_cover`, `stored_eq_pieces`;
(5) `isBestShare_optimal`, with `exists_isBestShare`; (6) `alg_step` and `run_costs`, with the
explicit constants of `costs_poly`; (7) the time of a minimization by the algorithm of Iwata and
Orlin [IO09], `O(n⁵ log n)·FO + O(n⁶ log n)`, substituted into the counts of (6), gives the stated
running time (not formalised). -/
theorem pieces_theorem (H : Hyp f m β) :
    (∀ s K, IsRun f m β s K → K ≤ (Fintype.card E + 2) ^ 2 * (numBP f m β + 1)) ∧
    (∃ s K, IsRun f m β s K ∧ covered f m β s K = Set.Icc (0 : ℝ) 1) ∧
    (∀ s K αs y, AlgPieces f m β s K αs y →
      Prod.fst '' stored f m β s K = pieces f m β ∧
      (∀ P y', (P, y') ∈ stored f m β s K → ∀ α ∈ P, bestResponse f m β α = y' α) ∧
      αs ∈ Icc (0 : ℝ) 1 ∧
      (∀ α ∈ Icc (0 : ℝ) 1, profit (grossValue f m β) α ≤ profit (grossValue f m β) αs) ∧
      y αs = bestResponse f m β αs) ∧
    (∀ s K, IsRun f m β s K → covered f m β s K = Set.Icc (0 : ℝ) 1 →
      ∃ αs y, AlgPieces f m β s K αs y) ∧
    (∀ s K, IsRun f m β s K → ∀ k < K,
      WaterFilling.waterFill f m β (s k) = bestResponse f m β (s k) ∧
        found f m β (s k) =
          Icc (Cont.lo f m β (s k) (WaterFilling.waterFill f m β (s k)) (velocity f m β (s k)))
            (Cont.hi f m β (s k) (WaterFilling.waterFill f m β (s k)) (velocity f m β (s k))) ∧
        line f m β (s k) = fun α e =>
          WaterFilling.waterFill f m β (s k) e + (α - s k) * velocity f m β (s k) e) ∧
    ∀ (R : Cont.RayCost E) (c : ℕ),
      (∀ x w, R.calls x w ≤ c * Fintype.card E ^ 2 ∧ R.evals x w ≤ c * Fintype.card E ^ 2) →
      ∀ s K, IsRun f m β s K →
        runCalls f m β R s K ≤ (18 * c + 36) * Fintype.card E ^ 4 * (numBP f m β + 1) ∧
          runEvals f m β R s K ≤ (18 * c + 72) * Fintype.card E ^ 5 * (numBP f m β + 1) := by
  refine ⟨fun s K hrun => ?_, ?_, fun s K αs y halg => ⟨?_, ?_, ?_⟩, fun s K hrun hstop => ?_,
    fun s K hrun k hk => ?_, fun R c hc s K hrun => ?_⟩
  -- (1) "Each `C_k` is a finite union of closed intervals, so every nonempty complementary
  -- component has positive length and its midpoint lies in `(0, 1)`." (`run_mem`)
  -- (2) "By `lem:continuation`, each step discovers a new piece or a singleton event point that is
  -- never tried again." (`run_step`)
  -- (3) "By `lem:eventcount`, the number of steps is at most
  -- `(B + 1)(1 + C(n, 2)) + B ≤ (n + 2)²(B + 1)`." (`run_length_le`)
  · exact run_length_le H hrun
  -- The loop stops, by the bound of step (3).
  · obtain ⟨K, -, hrun, hstop⟩ := exists_run_stop H
    exact ⟨_, K, hrun, hstop⟩
  -- (4) "At termination, finitely many closed pieces and singletons cover `[0, 1]`. The pieces
  -- alone cover it, since a nonempty complement of their union would contain an interval, so
  -- every piece has been found."
  · exact stored_eq_pieces H halg.1 halg.2.1
  -- With their affine maps: "For each stored piece, retain its affine map `y_{α̂_k}`."
  · exact fun P y' hPy => stored_agree hPy
  -- (5) "Maximizing on each piece therefore gives an optimal contract."
  · exact isBestShare_optimal H halg.1 halg.2.1 halg.2.2
  -- (5) When the loop stops, a best share exists: "After covering `[0, 1]`, maximize the
  -- corresponding quadratic utility `U_P(α) = (1 − α) mᵀy_{α̂_k}(α)` on each piece and take the
  -- best share."
  · obtain ⟨αs, y, hbest⟩ := exists_isBestShare H hrun hstop
    exact ⟨αs, y, hrun, hstop, hbest⟩
  -- (6) "Each step uses one best-response computation and one affine continuation, …" (lines
  -- 507-508 of `alg:pieces`)
  · exact alg_step H hrun hk
  -- (6) "… costing `O(n²)` minimizations, `O(n³)` further rank evaluations, and `O(n⁴)` further
  -- arithmetic operations by the proof of `thm:waterfilling` and `lem:continuation`. Maintaining
  -- `C_k` as a sorted interval list costs at most `O(n²(B + 1))` operations per step. Multiplying
  -- gives `O(n⁴(B + 1))` submodular minimizations, `O(n⁵(B + 1))` further evaluations of `f`, and
  -- `O(n⁶(B + 1) + n⁴(B + 1)²)` further arithmetic operations."
  -- The minimizations and the evaluations of `f`, with the explicit constants of `costs_poly`;
  -- the arithmetic operations are not formalised.
  · obtain ⟨h1, h2⟩ := run_costs H hrun R hc
    obtain ⟨h3, h4⟩ := costs_poly (Fintype.card E) (numBP f m β) c
    exact ⟨h1.trans h3, h2.trans h4⟩
  -- (7) "As in the proof of `thm:waterfilling`, each submodular minimization takes time
  -- `O(n⁵ log n)·FO + O(n⁶ log n)` using Iwata and Orlin's algorithm [IO09]: its objective is `f`
  -- minus a modular function, evaluated in time `FO + O(n)`. Substituting this bound gives the
  -- stated total runtime." Not formalised.

/-! ### The form used by `ContractDesignPolymatroids/Subclasses/PolynomialClasses.lean` -/

section Outcome

variable (f m β)

/-- What `thm:pieces` says about a run of `alg:pieces` that stops after `K` iterations: the
algorithm runs `K` iterations with shares `s` and returns `α⋆` and `y` (`AlgPieces`), the stored
pieces are all pieces, each with its affine response, and `α⋆` is an optimal contract with
`y(α⋆) = x*(α⋆)`. -/
def Outcome (K : ℕ) : Prop :=
  ∃ (s : ℕ → ℝ) (αs : ℝ) (y : ℝ → E → ℝ), AlgPieces f m β s K αs y ∧
    Prod.fst '' stored f m β s K = pieces f m β ∧
    (∀ P y', (P, y') ∈ stored f m β s K → ∀ α ∈ P, bestResponse f m β α = y' α) ∧
    αs ∈ Icc (0 : ℝ) 1 ∧
    (∀ α ∈ Icc (0 : ℝ) 1, profit (grossValue f m β) α ≤ profit (grossValue f m β) αs) ∧
    y αs = bestResponse f m β αs

end Outcome

/-- `thm:pieces` for one run (from `pieces_theorem`, with the run `share` of `exists_run_stop`):
`alg:pieces` stops after `K ≤ (n + 2)²(B + 1)` iterations with the `Outcome` above (`B` written
out as `(BP f m β ∩ Ioo 0 1).ncard`, the form `ContractDesignPolymatroids/Subclasses/PolynomialClasses.lean` uses). -/
theorem tracing (H : Hyp f m β) :
    ∃ K ≤ (Fintype.card E + 2) ^ 2 * ((BP f m β ∩ Ioo 0 1).ncard + 1), Outcome f m β K := by
  obtain ⟨K, hK, hrun, hstop⟩ := exists_run_stop H
  obtain ⟨-, -, hout, hret, -⟩ := pieces_theorem H
  obtain ⟨αs, y, halg⟩ := hret _ K hrun hstop
  exact ⟨K, hK, _, αs, y, halg, hout _ K αs y halg⟩

end Tracing

end Stoc
