-- stamp r9 2026-11-03
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
   most `(18c + 36) n⁴ (B + 1)` and `(18c + 72) n⁵ (B + 1)` (`costs_poly`); with the arithmetic
   operations, the counted enumeration `piecesC` makes exactly `runCalls` minimizations and
   `runEvals` evaluations of `f`, and at most `(c + 7)(n + 2)⁶(B + 1) + 7(n + 2)⁴(B + 1)²` further
   arithmetic operations if each ray computation makes at most `c n³` (assumed, not cited: the
   STOC version does not state them; `piecesC_spec`);
7. with the time of a minimization by the algorithm of Iwata and Orlin [IO09], cited as a
   hypothesis, this gives the running time of `thm:pieces` (`piecesC_time`).

The arithmetic operations (the `O(n⁶(B + 1) + n⁴(B + 1)²)` of the proof, with the `O(n²(B + 1))`
operations per step for the sorted interval list of `C_k`) are counted by the counted enumeration
`piecesC` (`piecesC_spec`), as `WaterFilling.lean` counts those of water-filling. Not formalised:
the running time of `thm:pieces` (step (7)), and the ray computation of [GGJ17], which is cited.
Lemmas for steps that the STOC version leaves implicit are marked "not in the paper": `quad_max`
(the remark after `lem:pwaffine` is stated without proof), `exists_isBestShare` (a best share
exists, in "take the best share"), `exists_run_stop` (the loop can always continue while
`C ≠ [0, 1]`), `costs_poly` (the explicit constants of the `O`-bounds), the bookkeeping of `covered`
and `stored`, and the counted enumeration `piecesC` with `piecesC_spec` (the paper counts in
prose).

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
Extended on 2026-11-03 with the counted enumeration `piecesC`, which proves the arithmetic
operations of `thm:pieces` and leaves its proof as it was.
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
`O(n²(B + 1))` operations per step for the sorted interval list of `C_k`, are counted by the counted
enumeration `piecesC` (`piecesC_spec`). -/
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
    obtain ⟨hwf, hcalls, hevals, -⟩ :=
      WaterFilling.waterfilling ⟨H.rank, H.beta, H.reward, hk01.1.le⟩
    -- and the affine continuation from `x*(α̂_k)` has its counts (`lem:continuation`)
    obtain ⟨hc1, hc2⟩ := (continuation H hk01).1.2.2.1 R c hc
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

/-! ### The enumeration with its operation counts

Step (6) of the proof of `thm:pieces` counts the arithmetic operations as well: "Each step uses one
best-response computation and one affine continuation, costing `O(n²)` minimizations, `O(n³)`
further rank evaluations, and `O(n⁴)` further arithmetic operations by the proof of
`thm:waterfilling` and `lem:continuation`. Maintaining `C_k` as a sorted interval list costs at most
`O(n²(B + 1))` operations per step. Multiplying gives `O(n⁴(B + 1))` submodular minimizations,
`O(n⁵(B + 1))` further evaluations of `f`, and `O(n⁶(B + 1) + n⁴(B + 1)²)` further arithmetic
operations." The counted enumeration `piecesC` performs the while loop of `alg:pieces` (lines
504-509) in the cost model of `Stoc.Counted` on a run `s` that stops after `K` steps (`IsRun`,
`C_K = [0, 1]`), with `C_k` as a list of intervals sorted by their left ends and `𝓘_k` as a list of
pieces with their affine maps (`PieceRec`). Each pass makes the test `C = [0, 1]` (`coverC`, one
pass over the list); the midpoint `α̂` of the component of `[0, 1] \ C` that the run chooses, given
by a point of it (`runPt`; `midC`, two passes over the list); `x*(α̂)` by the counted water-filling
`WaterFilling.waterFillC` and `v(α̂)` by (`eq:velocity`) (`velC`); `I(α̂)` by the counted procedure
`Cont.contC` of `lem:continuation`; and the insertion of `I(α̂)` into the sorted list (one pass) and
the piece stored if it is nondegenerate (`storeC`) (`iterC`, `whileC`). The last pass makes only
the test, which passes, as `C_K = [0, 1]`, and ends the loop (`coverC_true`). `piecesC_spec` shows
that it ends with the sorted list of the intervals `I(α̂_k)`, whose union is `C_K`, and with the
pieces of `𝓘_K` and their affine maps, makes exactly `runCalls` submodular minimizations and
`runEvals` further evaluations of `f`, and, if each ray computation makes at most `c n³` arithmetic
operations, at most `(c + 7)(n + 2)⁶(B + 1) + 7(n + 2)⁴(B + 1)²` further arithmetic operations. The
list has `k` intervals at step `k < K ≤ (n + 2)²(B + 1)`, so its maintenance takes at most `7k + 4`
operations at step `k`, the `O(n²(B + 1))` per step of the proof; the other work of a step is at
most `(c + 7)(n + 2)⁴` operations (`step_ops_le`), with the `O(n²)` operations of `v(α̂)` by
(`eq:velocity`), which the proof does not mention; the last test takes at most `2K + 1`, paid for
by the slack of at least `7` in each of the `K ≥ 1` steps. The point that names the chosen component
is taken at no cost (`runPt`). Line 510, the best share over the stored pieces, is not counted, as
in the proof. (Not in the paper: the paper counts in prose.) -/

/-- A stored piece of the counted enumeration: the interval `[lo, hi]`, with the share `α̂` and the
point `x̂` and the vector `v` of its affine map `y(α) = x̂ + (α − α̂) v`. -/
structure PieceRec (E : Type*) where
  /-- The left end of the piece. -/
  lo : ℝ
  /-- The right end of the piece. -/
  hi : ℝ
  /-- The share `α̂`. -/
  share : ℝ
  /-- The point `x̂ = x*(α̂)`. -/
  x : E → ℝ
  /-- The vector `v(α̂)`. -/
  v : E → ℝ

section Counts

open Counted

variable (f m β)

/-- (`eq:velocity`) for the element `e`, from the marginals `ρ` and the point `x̂`: whether `e` is
free (one comparison), and if so `t_e = m_e/β_e` (one operation); else whether it is zero (one
comparison), and if not its block `D ∖ Z` (two comparisons for each element), `t(D ∖ Z)` and
`β⁻¹(D ∖ Z)` (two operations for each of its elements) and `v_e` (three operations). -/
noncomputable def velCoordC (ρ xh : E → ℝ) (e : E) : Counted ℝ :=
  ops 1 (decide (ρ e = 0)) >>=ᶜ fun b0 =>
  if b0 then ops 1 (m e / β e) else
  ops 1 (decide (xh e = 0)) >>=ᶜ fun b1 =>
  if b1 then ret 0 else
  filterK 2 Finset.univ (fun g => ρ g = ρ e ∧ xh g ≠ 0) >>=ᶜ fun D =>
  Counted.sum D (fun g => ops 1 (m g / β g)) >>=ᶜ fun t =>
  Counted.sum D (fun g => ops 1 (1 / β g)) >>=ᶜ fun b =>
  ops 3 ((m e - t / b) / β e)

/-- Line 507, `v(α̂)` by (`eq:velocity`) from `x̂ = x*(α̂)`: the marginals `ρ_e = α̂ m_e − β_e x̂_e`
(three operations for each element), and `v_e` for each element (`velCoordC`). -/
noncomputable def velC (α : ℝ) (xh : E → ℝ) : Counted (E → ℝ) :=
  ops (3 * Fintype.card E) (marg m β α xh) >>=ᶜ fun ρ => vec (velCoordC m β ρ xh)

/-- Line 505, the test `C = [0, 1]` on the list of intervals sorted by their left ends, from a point
`r` up to which `[0, r]` is covered: each interval `[a, b]` must start at most at `r` (one
comparison), and then `r` becomes `max(r, b)` (one comparison); at the end `r ≥ 1` (one
comparison). -/
noncomputable def coverC : ℝ → List (ℝ × ℝ) → Counted Bool
  | r, [] => ops 1 (decide (1 ≤ r))
  | r, I :: L => ops 2 (decide (I.1 ≤ r)) >>=ᶜ fun b =>
      if b then coverC (max r I.2) L else ret false

/-- Line 506, the midpoint of the component of `[0, 1] \ C` that contains the point `p`: the largest
right end `a` below `p` of an interval of the list, or `0` (one comparison for each interval, and
one for each candidate), the least left end `b` above `p`, or `1` (likewise), and `(a + b)/2` (two
operations). -/
noncomputable def midC (p : ℝ) (L : List (ℝ × ℝ)) : Counted ℝ :=
  filterMapL (fun I => ops 1 (if I.2 < p then some I.2 else none)) L >>=ᶜ fun B =>
  maxL 0 B >>=ᶜ fun a =>
  filterMapL (fun I => ops 1 (if p < I.1 then some I.1 else none)) L >>=ᶜ fun A =>
  minL 1 A >>=ᶜ fun b =>
  ops 2 ((a + b) / 2)

/-- Line 508, `𝓘`: the piece `I = [lo, hi]` stored with its affine map if it is nondegenerate (one
comparison). -/
noncomputable def storeC (αh : ℝ) (xh vh : E → ℝ) (I : ℝ × ℝ) (S : List (PieceRec E)) :
    Counted (List (PieceRec E)) :=
  ops 1 (if I.1 < I.2 then ⟨I.1, I.2, αh, xh, vh⟩ :: S else S)

/-- Lines 506-508 of `alg:pieces` with their operation counts, for the component of `[0, 1] \ C`
that contains the point `p`: its midpoint `α̂` (`midC`); `x*(α̂)` by water-filling
(`WaterFilling.waterFillC`) and `v(α̂)` by (`eq:velocity`) (`velC`); `I(α̂)` by the procedure of
`lem:continuation` (`Cont.contC`); `I(α̂)` inserted into the list of intervals, sorted by their
left ends (at most one comparison with each interval); and the piece stored with its affine map
if it is nondegenerate (`storeC`). -/
noncomputable def iterC (R : Cont.RayCostOps E) (p : ℝ) (L : List (ℝ × ℝ))
    (S : List (PieceRec E)) : Counted (List (ℝ × ℝ) × List (PieceRec E)) :=
  midC p L >>=ᶜ fun αh =>
  WaterFilling.waterFillC f m β αh >>=ᶜ fun xh =>
  velC m β αh xh >>=ᶜ fun vh =>
  Cont.contC f m β αh xh vh R >>=ᶜ fun I =>
  orderedInsertL (fun I J : ℝ × ℝ => I.1 ≤ J.1) I L >>=ᶜ fun L' =>
  storeC αh xh vh I S >>=ᶜ fun S' =>
  ret (L', S')

/-- The point of `[0, 1] \ C_k` whose component the run `s` chooses at step `k`: a point `p` with
`α̂_k = ` the midpoint of the component of `[0, 1] \ C_k` that contains `p` (`IsRun`). The counted
enumeration takes it at no cost (not in the paper): the paper lets any component be chosen, and the
first one could be found in the pass of the test `C = [0, 1]` (`coverC`), at the first left end
beyond the covered part, which changes no count by more than a constant per step. -/
noncomputable def runPt (s : ℕ → ℝ) (k : ℕ) : ℝ :=
  Classical.epsilon fun p => p ∈ Icc (0 : ℝ) 1 \ covered f m β s k ∧
    s k = midShare (covered f m β s k) p

/-- The while loop of `alg:pieces` (lines 505-509), at most `j` passes from step `k`: each pass
tests `C = [0, 1]` (`coverC`) and, if not, takes a step (`iterC`) for the component chosen by the
point `p k`. -/
noncomputable def whileC (R : Cont.RayCostOps E) (p : ℕ → ℝ) :
    ℕ → ℕ → List (ℝ × ℝ) → List (PieceRec E) → Counted (List (ℝ × ℝ) × List (PieceRec E))
  | 0, _, L, S => ret (L, S)
  | j + 1, k, L, S =>
      coverC 0 L >>=ᶜ fun b =>
      if b then ret (L, S) else
        iterC f m β R (p k) L S >>=ᶜ fun r => whileC R p j (k + 1) r.1 r.2

/-- `alg:pieces`, lines 504-509, with its operation counts, for the run `s` of `K` steps: `C = ∅`
and `𝓘 = ∅` (empty lists), and the while loop with the components chosen by the run (`runPt`):
`K + 1` passes, the `K` steps and the last test `C = [0, 1]`, which ends the loop when the run
stops (`coverC_true`). -/
noncomputable def piecesC (R : Cont.RayCostOps E) (s : ℕ → ℝ) (K : ℕ) :
    Counted (List (ℝ × ℝ) × List (PieceRec E)) :=
  whileC f m β R (runPt f m β s) (K + 1) 0 [] []

/-- The state of the counted enumeration after `k` steps of the run `s` (not in the paper): the
list holds `k` intervals `[a, b] ⊆ [0, 1]` with `a ≤ b`, sorted by their left ends, whose union is
`C_k`, and the stored pieces are those of `𝓘_k` with their affine maps. -/
def PiecesInv (s : ℕ → ℝ) (k : ℕ) (L : List (ℝ × ℝ)) (S : List (PieceRec E)) : Prop :=
  L.length = k ∧ L.Pairwise (fun I J => I.1 ≤ J.1) ∧ (∀ I ∈ L, 0 ≤ I.1 ∧ I.1 ≤ I.2 ∧ I.2 ≤ 1) ∧
    (∀ α, α ∈ covered f m β s k ↔ ∃ I ∈ L, α ∈ Icc I.1 I.2) ∧
    ∀ P y, (P, y) ∈ stored f m β s k ↔
      ∃ q ∈ S, P = Icc q.lo q.hi ∧ y = fun α e => q.x e + (α - q.share) * q.v e

variable {f m β}

omit [DecidableEq E] in
/-- The value of `velCoordC`: the coordinate `e` of (`eq:velocity`). -/
lemma velCoordC_val (ρ xh : E → ℝ) (e : E) :
    (velCoordC m β ρ xh e).val =
      if ρ e = 0 then m e / β e
      else if xh e = 0 then 0
      else (m e - (∑ g ∈ Finset.univ.filter (fun g => ρ g = ρ e ∧ xh g ≠ 0), m g / β g) /
        ∑ g ∈ Finset.univ.filter (fun g => ρ g = ρ e ∧ xh g ≠ 0), 1 / β g) / β e := by
  unfold velCoordC
  by_cases h0 : ρ e = 0
  · simp [h0]
  · by_cases h1 : xh e = 0
    · simp [h0, h1]
    · simp only [h0, h1, decide_false, val_bind, val_ops, Bool.false_eq_true, ↓reduceIte,
        val_filterK, val_sum, val_ops]

omit [DecidableEq E] in
/-- `velC` computes `v(α)` of (`eq:velocity`) from `x*(α)`. -/
lemma velC_val (α : ℝ) : (velC m β α (bestResponse f m β α)).val = velocity f m β α := by
  funext e
  simp only [velC, val_bind, val_ops, val_vec, velCoordC_val]
  rfl

omit [DecidableEq E] in
/-- A coordinate of `v(α)`: at most `6n + 5` operations. -/
lemma velCoordC_cost (ρ xh : E → ℝ) (e : E) :
    (velCoordC m β ρ xh e).cost.2.1 = 0 ∧ (velCoordC m β ρ xh e).cost.2.2 = 0 ∧
      (velCoordC m β ρ xh e).cost.1 ≤ 6 * Fintype.card E + 5 := by
  unfold velCoordC
  by_cases h0 : ρ e = 0
  · simp [h0]
  · by_cases h1 : xh e = 0
    · simp [h0, h1]
    · have hD : (Finset.univ.filter fun g => ρ g = ρ e ∧ xh g ≠ 0).card ≤ Fintype.card E :=
        (Finset.card_filter_le _ _).trans (by simp)
      simp only [h0, h1, decide_false, cost_bind, val_ops, cost_ops, Bool.false_eq_true,
        ↓reduceIte, cost_filterK, val_filterK, cost_sum, Finset.sum_const, smul_eq_mul,
        Prod.fst_add, Prod.snd_add, Prod.smul_mk, mul_one, mul_zero, Finset.card_univ]
      refine ⟨by simp, by simp, ?_⟩
      omega

omit [DecidableEq E] in
/-- `v(α)`: at most `6n² + 8n` operations. -/
lemma velC_cost (α : ℝ) (xh : E → ℝ) :
    (velC m β α xh).cost.2.1 = 0 ∧ (velC m β α xh).cost.2.2 = 0 ∧
      (velC m β α xh).cost.1 ≤ 6 * Fintype.card E ^ 2 + 8 * Fintype.card E := by
  simp only [velC, cost_bind, cost_ops, val_ops, cost_vec, Prod.fst_add, Prod.snd_add,
    Prod.fst_sum, Prod.snd_sum]
  refine ⟨by simp [fun e => (velCoordC_cost (m := m) (β := β) (marg m β α xh) xh e).1],
    by simp [fun e => (velCoordC_cost (m := m) (β := β) (marg m β α xh) xh e).2.1], ?_⟩
  have := Finset.sum_le_sum fun e (_ : e ∈ (Finset.univ : Finset E)) =>
    (velCoordC_cost (m := m) (β := β) (marg m β α xh) xh e).2.2
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at this
  nlinarith

/-- The test `coverC` is sound: if it passes from `r`, the intervals cover `(r, 1]`. -/
lemma coverC_sound : ∀ (L : List (ℝ × ℝ)) (r : ℝ), (coverC r L).val = true →
    ∀ q, r < q → q ≤ 1 → ∃ I ∈ L, I.1 ≤ q ∧ q ≤ I.2
  | [], r, h, q, hrq, hq1 => by
    simp only [coverC, val_ops, decide_eq_true_eq] at h
    linarith
  | I :: L, r, h, q, hrq, hq1 => by
    by_cases hI : I.1 ≤ r
    · simp only [coverC, hI, decide_true, val_bind, val_ops, ↓reduceIte] at h
      by_cases hq : q ≤ I.2
      · exact ⟨I, List.mem_cons_self, by linarith, hq⟩
      · obtain ⟨J, hJ, hJq⟩ := coverC_sound L (max r I.2) h q
          (max_lt hrq (not_le.1 hq)) hq1
        exact ⟨J, List.mem_cons_of_mem I hJ, hJq⟩
    · simp [coverC, hI] at h

/-- The test `coverC` is complete (not in the paper): on a list sorted by left ends whose intervals
start at most at `1`, if the intervals cover `(r, 1]`, the test passes from `r`. -/
lemma coverC_complete : ∀ (L : List (ℝ × ℝ)) (r : ℝ), L.Pairwise (fun I J => I.1 ≤ J.1) →
    (∀ I ∈ L, I.1 ≤ 1) → (∀ q, r < q → q ≤ 1 → ∃ I ∈ L, I.1 ≤ q ∧ q ≤ I.2) →
    (coverC r L).val = true
  | [], r, _, _, h => by
    simp only [coverC, val_ops, decide_eq_true_eq]
    by_contra hr
    obtain ⟨I, hI, -⟩ := h 1 (not_le.1 hr) le_rfl
    exact absurd hI List.not_mem_nil
  | I :: L, r, hs, h1, h => by
    -- the first interval starts at most at `r`: else the points between `r` and its left end are
    -- not covered, as the list is sorted by left ends
    have hIr : I.1 ≤ r := by
      by_contra hIr
      rw [not_le] at hIr
      have hI1 := h1 I List.mem_cons_self
      obtain ⟨J, hJ, hJq, -⟩ := h ((r + I.1) / 2) (by linarith) (by linarith)
      rcases List.mem_cons.1 hJ with rfl | hJ
      · linarith
      · linarith [(List.pairwise_cons.1 hs).1 J hJ]
    simp only [coverC, hIr, decide_true, val_bind, val_ops, ↓reduceIte]
    refine coverC_complete L (max r I.2) (List.pairwise_cons.1 hs).2
      (fun J hJ => h1 J (List.mem_cons_of_mem I hJ)) fun q hq hq1 => ?_
    obtain ⟨J, hJ, hJq⟩ := h q (lt_of_le_of_lt (le_max_left _ _) hq) hq1
    rcases List.mem_cons.1 hJ with rfl | hJ
    · exact absurd hJq.2 (not_le.2 (lt_of_le_of_lt (le_max_right _ _) hq))
    · exact ⟨J, hJ, hJq⟩

/-- The test: at most `2|L| + 1` comparisons. -/
lemma coverC_cost : ∀ (L : List (ℝ × ℝ)) (r : ℝ),
    (coverC r L).cost.2.1 = 0 ∧ (coverC r L).cost.2.2 = 0 ∧ (coverC r L).cost.1 ≤ 2 * L.length + 1
  | [], r => by simp [coverC]
  | I :: L, r => by
    by_cases hI : I.1 ≤ r
    · obtain ⟨h1, h2, h3⟩ := coverC_cost L (max r I.2)
      simp only [coverC, hI, decide_true, cost_bind, val_ops, cost_ops, ↓reduceIte, Prod.fst_add,
        Prod.snd_add, h1, h2, List.length_cons]
      refine ⟨by simp, by simp, ?_⟩
      omega
    · simp [coverC, hI]
      omega

/-- `midC` finds the midpoint of the component of `[0, 1] \ C` that contains a point `p ∉ C`, for
the union `C` of the intervals `[a, b]`, `a ≤ b`, of the list: the component reaches from the
largest right end below `p` (or `0`) to the least left end above `p` (or `1`), as no interval meets
the gap between them and its ends lie in `C` or are `0` and `1`. -/
lemma midC_val {L : List (ℝ × ℝ)} (hL : ∀ I ∈ L, I.1 ≤ I.2) {C : Set ℝ}
    (hC : ∀ α, α ∈ C ↔ ∃ I ∈ L, α ∈ Icc I.1 I.2) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1 \ C) :
    (midC p L).val = midShare C p := by
  simp only [midC, val_bind, val_filterMapL, val_ops, val_maxL, val_minL]
  set Bs := L.filterMap fun I => if I.2 < p then some I.2 else none
  set As := L.filterMap fun I => if p < I.1 then some I.1 else none
  set a := (insert 0 Bs.toFinset).max' (Finset.insert_nonempty _ _)
  set b := (insert 1 As.toFinset).min' (Finset.insert_nonempty _ _)
  have hmemB : ∀ t, t ∈ insert 0 Bs.toFinset ↔ t = 0 ∨ ∃ I ∈ L, I.2 < p ∧ I.2 = t := by
    intro t
    simp [Bs, Option.ite_none_right_eq_some]
  have hmemA : ∀ t, t ∈ insert 1 As.toFinset ↔ t = 1 ∨ ∃ I ∈ L, p < I.1 ∧ I.1 = t := by
    intro t
    simp [As, Option.ite_none_right_eq_some]
  have h0a : 0 ≤ a := Finset.le_max' _ _ ((hmemB 0).2 (Or.inl rfl))
  have hb1 : b ≤ 1 := Finset.min'_le _ _ ((hmemA 1).2 (Or.inl rfl))
  have hale : ∀ I ∈ L, I.2 < p → I.2 ≤ a := fun I hI h =>
    Finset.le_max' _ _ ((hmemB _).2 (Or.inr ⟨I, hI, h, rfl⟩))
  have hble : ∀ I ∈ L, p < I.1 → b ≤ I.1 := fun I hI h =>
    Finset.min'_le _ _ ((hmemA _).2 (Or.inr ⟨I, hI, h, rfl⟩))
  have hap : a ≤ p := by
    refine Finset.max'_le _ _ _ fun t ht => ?_
    rcases (hmemB t).1 ht with rfl | ⟨I, -, h, rfl⟩
    · exact hp.1.1
    · exact h.le
  have hpb : p ≤ b := by
    refine Finset.le_min' _ _ _ fun t ht => ?_
    rcases (hmemA t).1 ht with rfl | ⟨I, -, h, rfl⟩
    · exact hp.1.2
    · exact h.le
  -- `a` is `0` or a right end of an interval, so in `C`; likewise `b`
  have haC : a = 0 ∨ a ∈ C := by
    rcases (hmemB a).1 (Finset.max'_mem _ _) with h | ⟨I, hI, -, h⟩
    · exact Or.inl h
    · exact Or.inr ((hC a).2 ⟨I, hI, h ▸ hL I hI, h.ge⟩)
  have hbC : b = 1 ∨ b ∈ C := by
    rcases (hmemA b).1 (Finset.min'_mem _ _) with h | ⟨I, hI, -, h⟩
    · exact Or.inl h
    · exact Or.inr ((hC b).2 ⟨I, hI, h.le, h ▸ hL I hI⟩)
  -- no interval meets the gap `(a, b)`
  have hgap : ∀ q, a < q → q < b → q ∉ C := by
    intro q haq hqb hqC
    obtain ⟨I, hI, h1, h2⟩ := (hC q).1 hqC
    by_cases hIp : I.2 < p
    · linarith [hale I hI hIp]
    · have hpI : p < I.1 := by
        by_contra h
        exact hp.2 ((hC p).2 ⟨I, hI, not_lt.1 h, not_lt.1 hIp⟩)
      linarith [hble I hI hpI]
  set F := Icc (0 : ℝ) 1 \ C
  set Ic := connectedComponentIn F p
  have hpI : p ∈ Ic := mem_connectedComponentIn hp
  have hIF : Ic ⊆ F := connectedComponentIn_subset F p
  have hoc : Ic.OrdConnected := isPreconnected_connectedComponentIn.ordConnected
  -- the points of `[a, b] ∩ [0, 1]` outside `C` form an interval around `p` in the component
  set J := {q | q ∈ Icc a b ∧ q ∈ Icc (0 : ℝ) 1 ∧ q ∉ C}
  have hJ : J.OrdConnected := by
    refine ⟨fun x hx y hy z hz => ⟨⟨hx.1.1.trans hz.1, hz.2.trans hy.1.2⟩,
      ⟨hx.2.1.1.trans hz.1, hz.2.trans hy.2.1.2⟩, fun hzC => ?_⟩⟩
    rcases hz.1.lt_or_eq with hxz | rfl
    · rcases hz.2.lt_or_eq with hzy | rfl
      · exact hgap z (lt_of_le_of_lt hx.1.1 hxz) (lt_of_lt_of_le hzy hy.1.2) hzC
      · exact hy.2.2 hzC
    · exact hx.2.2 hzC
  have hJI : J ⊆ Ic :=
    hJ.isPreconnected.subset_connectedComponentIn ⟨⟨hap, hpb⟩, hp.1, hp.2⟩
      fun q hq => ⟨hq.2.1, hq.2.2⟩
  -- the component lies in `[a, b]`
  have hIab : Ic ⊆ Icc a b := by
    intro q hq
    constructor
    · by_contra hqa
      push Not at hqa
      have haI : a ∈ Ic := hoc.out hq hpI ⟨hqa.le, hap⟩
      rcases haC with h | h
      · have := (hIF hq).1.1
        linarith
      · exact (hIF haI).2 h
    · by_contra hqb
      push Not at hqb
      have hbI : b ∈ Ic := hoc.out hpI hq ⟨hpb, hqb.le⟩
      rcases hbC with h | h
      · have := (hIF hq).1.2
        linarith
      · exact (hIF hbI).2 h
  have hbdd : BddBelow Ic := ⟨a, fun q hq => (hIab hq).1⟩
  have hbdd' : BddAbove Ic := ⟨b, fun q hq => (hIab hq).2⟩
  have hInf : sInf Ic = a := by
    refine le_antisymm ?_ (le_csInf ⟨p, hpI⟩ fun q hq => (hIab hq).1)
    rcases hap.lt_or_eq with hlt | heq
    · have hsub : Ioc a p ⊆ Ic := fun q hq => hJI ⟨⟨hq.1.le, hq.2.trans hpb⟩,
        ⟨h0a.trans hq.1.le, hq.2.trans hp.1.2⟩, fun hqC => by
          rcases hq.2.lt_or_eq with h | rfl
          · exact hgap q hq.1 (lt_of_lt_of_le h hpb) hqC
          · exact hp.2 hqC⟩
      calc sInf Ic ≤ sInf (Ioc a p) := csInf_le_csInf hbdd (nonempty_Ioc.2 hlt) hsub
        _ = a := csInf_Ioc hlt
    · rw [heq]
      exact csInf_le hbdd hpI
  have hSup : sSup Ic = b := by
    refine le_antisymm (csSup_le ⟨p, hpI⟩ fun q hq => (hIab hq).2) ?_
    rcases hpb.lt_or_eq with hlt | heq
    · have hsub : Ico p b ⊆ Ic := fun q hq => hJI ⟨⟨hap.trans hq.1, hq.2.le⟩,
        ⟨hp.1.1.trans hq.1, hq.2.le.trans hb1⟩, fun hqC => by
          rcases hq.1.lt_or_eq with h | rfl
          · exact hgap q (lt_of_le_of_lt hap h) hq.2 hqC
          · exact hp.2 hqC⟩
      calc b = sSup (Ico p b) := (csSup_Ico hlt).symm
        _ ≤ sSup Ic := csSup_le_csSup hbdd' (nonempty_Ico.2 hlt) hsub
    · rw [← heq]
      exact le_csSup hbdd' hpI
  show (a + b) / 2 = (sInf Ic + sSup Ic) / 2
  rw [hInf, hSup]

/-- The midpoint: at most `4|L| + 2` operations. -/
lemma midC_cost (p : ℝ) (L : List (ℝ × ℝ)) :
    (midC p L).cost.2.1 = 0 ∧ (midC p L).cost.2.2 = 0 ∧ (midC p L).cost.1 ≤ 4 * L.length + 2 := by
  have hB := List.length_filterMap_le
    (fun I : ℝ × ℝ => (ops 1 (if I.2 < p then some I.2 else none)).val) L
  have hA := List.length_filterMap_le
    (fun I : ℝ × ℝ => (ops 1 (if p < I.1 then some I.1 else none)).val) L
  simp only [midC, cost_bind, cost_filterMapL, cost_maxL, cost_minL, cost_ops, val_filterMapL,
    Prod.fst_add, Prod.snd_add, fst_list_sum, snd_fst_list_sum, snd_snd_list_sum]
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, mul_zero]
  refine ⟨by simp, by simp, ?_⟩
  simp only [mul_one] at *
  omega

omit [DecidableEq E] in
/-- The point chosen at step `k` of a run lies in `[0, 1] \ C_k`, and `α̂_k` is the midpoint of its
component (`IsRun`). -/
lemma runPt_spec {s : ℕ → ℝ} {K : ℕ} (hrun : IsRun f m β s K) {k : ℕ} (hk : k < K) :
    runPt f m β s k ∈ Icc (0 : ℝ) 1 \ covered f m β s k ∧
      s k = midShare (covered f m β s k) (runPt f m β s k) := by
  obtain ⟨-, p, hp, hsk⟩ := hrun k hk
  exact Classical.epsilon_spec (p := fun p => p ∈ Icc (0 : ℝ) 1 \ covered f m β s k ∧
    s k = midShare (covered f m β s k) p) ⟨p, hp, hsk⟩

/-- The operations of a step outside the interval list (plumbing): water-filling, `v(α̂)` and the
affine continuation, with the constant operations of the list, are at most `(c + 7)(n + 2)⁴`. -/
lemma step_ops_le (n c : ℕ) :
    (6 * n ^ 3 + 56 * n ^ 2 + 29 * n + 2) + (6 * n ^ 2 + 8 * n) +
        (3 * n ^ 4 + (2 * c + 5) * n ^ 3 + 44 * n ^ 2 + 57 * n + 62) + 4 ≤
      (c + 7) * (n + 2) ^ 4 := by
  have e1 : (c + 7) * (n + 2) ^ 4 = c * n ^ 4 + 8 * (c * n ^ 3) + 24 * (c * n ^ 2) +
      32 * (c * n) + 16 * c + 7 * n ^ 4 + 56 * n ^ 3 + 168 * n ^ 2 + 224 * n + 112 := by ring
  have e2 : (2 * c + 5) * n ^ 3 = 2 * (c * n ^ 3) + 5 * n ^ 3 := by ring
  rw [e1, e2]
  omega

/-- The value of a step, stage by stage (plumbing). -/
lemma iterC_val_eq (R : Cont.RayCostOps E) (p : ℝ) (L : List (ℝ × ℝ)) (S : List (PieceRec E)) :
    (iterC f m β R p L S).val =
      (L.orderedInsert (fun I J : ℝ × ℝ => I.1 ≤ J.1)
        (Cont.contC f m β (midC p L).val (WaterFilling.waterFillC f m β (midC p L).val).val
          (velC m β (midC p L).val (WaterFilling.waterFillC f m β (midC p L).val).val).val R).val,
        (storeC (midC p L).val (WaterFilling.waterFillC f m β (midC p L).val).val
          (velC m β (midC p L).val (WaterFilling.waterFillC f m β (midC p L).val).val).val
          (Cont.contC f m β (midC p L).val (WaterFilling.waterFillC f m β (midC p L).val).val
            (velC m β (midC p L).val (WaterFilling.waterFillC f m β (midC p L).val).val).val
            R).val S).val) := rfl

/-- The value of a step at step `k < K` of a run, from a state for `C_k`: the interval
`I(α̂_k) = [lo, hi]` of the procedure of `lem:continuation` inserted into the list, and the piece
stored with its affine map if it is nondegenerate. -/
lemma iterC_val (H : Hyp f m β) {s : ℕ → ℝ} {K : ℕ} (hrun : IsRun f m β s K) {k : ℕ}
    (hk : k < K) (R : Cont.RayCostOps E) {L : List (ℝ × ℝ)} {S : List (PieceRec E)}
    (hinv : PiecesInv f m β s k L S) :
    (iterC f m β R (runPt f m β s k) L S).val =
      (L.orderedInsert (fun I J : ℝ × ℝ => I.1 ≤ J.1)
        (Cont.lo f m β (s k) (bestResponse f m β (s k)) (velocity f m β (s k)),
          Cont.hi f m β (s k) (bestResponse f m β (s k)) (velocity f m β (s k))),
        if Cont.lo f m β (s k) (bestResponse f m β (s k)) (velocity f m β (s k)) <
            Cont.hi f m β (s k) (bestResponse f m β (s k)) (velocity f m β (s k))
          then ⟨Cont.lo f m β (s k) (bestResponse f m β (s k)) (velocity f m β (s k)),
            Cont.hi f m β (s k) (bestResponse f m β (s k)) (velocity f m β (s k)), s k,
            WaterFilling.waterFill f m β (s k), velocity f m β (s k)⟩ :: S
          else S) := by
  obtain ⟨-, -, hint, hcov, -⟩ := hinv
  obtain ⟨hpt, hsk⟩ := runPt_spec hrun hk
  have hk01 := (run_mem H hrun k hk).1
  have hmid : (midC (runPt f m β s k) L).val = s k := by
    rw [midC_val (fun I hI => (hint I hI).2.1) hcov hpt, ← hsk]
  have WH : WaterFilling.Hyp f m β (s k) := ⟨H.rank, H.beta, H.reward, hk01.1.le⟩
  have hwv := (WaterFilling.waterFillC_spec WH).1
  have hwf : WaterFilling.waterFill f m β (s k) = bestResponse f m β (s k) :=
    (WaterFilling.waterfilling WH).1
  have hvel : (velC m β (s k) (WaterFilling.waterFill f m β (s k))).val =
      velocity f m β (s k) := by
    rw [hwf]
    exact velC_val (s k)
  obtain ⟨-, hαK⟩ := Cont.K_facts H hk01.1.le hk01.2.le
  have hcont : (Cont.contC f m β (s k) (WaterFilling.waterFill f m β (s k))
      (velocity f m β (s k)) R).val =
      (Cont.lo f m β (s k) (bestResponse f m β (s k)) (velocity f m β (s k)),
        Cont.hi f m β (s k) (bestResponse f m β (s k)) (velocity f m β (s k))) := by
    rw [hwf]
    exact Cont.contC_val R hαK.1 hαK.2
  rw [iterC_val_eq, hmid, hwv, hvel, hcont]
  rfl

/-- A step at step `k < K` of a run takes a state for `C_k` and `𝓘_k` to one for `C_{k+1}` and
`𝓘_{k+1}`: `C_{k+1} = C_k ∪ I(α̂_k)`, and `I(α̂_k)` is stored with `y_{α̂_k}` if it is
nondegenerate (`eq:A-enum`). -/
lemma iterC_inv (H : Hyp f m β) {s : ℕ → ℝ} {K : ℕ} (hrun : IsRun f m β s K) {k : ℕ}
    (hk : k < K) (R : Cont.RayCostOps E) {L : List (ℝ × ℝ)} {S : List (PieceRec E)}
    (hinv : PiecesInv f m β s k L S) :
    PiecesInv f m β s (k + 1) (iterC f m β R (runPt f m β s k) L S).val.1
      (iterC f m β R (runPt f m β s k) L S).val.2 := by
  rw [iterC_val H hrun hk R hinv]
  obtain ⟨hlen, hsort, hint, hcov, hsto⟩ := hinv
  have hk01 := (run_mem H hrun k hk).1
  have hwf : WaterFilling.waterFill f m β (s k) = bestResponse f m β (s k) :=
    (WaterFilling.waterfilling ⟨H.rank, H.beta, H.reward, hk01.1.le⟩).1
  set lo := Cont.lo f m β (s k) (bestResponse f m β (s k)) (velocity f m β (s k))
  set hi := Cont.hi f m β (s k) (bestResponse f m β (s k)) (velocity f m β (s k))
  have hfound : found f m β (s k) = Icc lo hi := (continuation H hk01).1.2.1
  have hline : line f m β (s k) = fun α e =>
      WaterFilling.waterFill f m β (s k) e + (α - s k) * velocity f m β (s k) e := by
    rw [hwf]
    rfl
  -- the interval `[lo, hi] = I(α̂_k) ⊆ [0, 1]` contains `α̂_k`
  have hsk_mem : s k ∈ Icc lo hi := hfound ▸ mem_found hk01.1.le hk01.2.le
  have hlo0 : 0 ≤ lo := by
    have h : lo ∈ found f m β (s k) := by
      rw [hfound]
      exact ⟨le_rfl, hsk_mem.1.trans hsk_mem.2⟩
    exact (found_subset h).1
  have hhi1 : hi ≤ 1 := by
    have h : hi ∈ found f m β (s k) := by
      rw [hfound]
      exact ⟨hsk_mem.1.trans hsk_mem.2, le_rfl⟩
    exact (found_subset h).2
  have hnt : (found f m β (s k)).Nontrivial ↔ lo < hi := by
    rw [hfound]
    constructor
    · intro h
      by_contra hle
      exact h.not_subsingleton (Set.subsingleton_Icc_of_ge (not_lt.1 hle))
    · intro h
      exact ⟨lo, ⟨le_rfl, h.le⟩, hi, ⟨h.le, le_rfl⟩, h.ne⟩
  refine ⟨by rw [List.orderedInsert_length, hlen], ?_, ?_, ?_, ?_⟩
  · have : Std.Total (fun I J : ℝ × ℝ => I.1 ≤ J.1) := ⟨fun I J => le_total I.1 J.1⟩
    have : IsTrans (ℝ × ℝ) (fun I J : ℝ × ℝ => I.1 ≤ J.1) := ⟨fun _ _ _ h1 h2 => h1.trans h2⟩
    exact hsort.orderedInsert _ _
  · intro I hI
    rcases (List.mem_orderedInsert _).1 hI with rfl | hI
    · exact ⟨hlo0, hsk_mem.1.trans hsk_mem.2, hhi1⟩
    · exact hint I hI
  · intro α
    rw [covered, Set.mem_union, hcov, hfound]
    simp only [List.mem_orderedInsert]
    constructor
    · rintro (⟨I, hI, h⟩ | h)
      · exact ⟨I, Or.inr hI, h⟩
      · exact ⟨_, Or.inl rfl, h⟩
    · rintro ⟨I, rfl | hI, h⟩
      · exact Or.inr h
      · exact Or.inl ⟨I, hI, h⟩
  · intro P y
    by_cases h : lo < hi
    · have hst : stored f m β s (k + 1) =
          insert (found f m β (s k), line f m β (s k)) (stored f m β s k) := by
        rw [stored]
        exact ite_eq_left (hnt.2 h)
      rw [hst, Set.mem_insert_iff, hsto, Prod.mk.injEq, hfound, hline, ite_eq_left h]
      simp only [List.mem_cons]
      constructor
      · rintro (⟨rfl, rfl⟩ | ⟨q, hq, hrest⟩)
        · exact ⟨_, Or.inl rfl, rfl, rfl⟩
        · exact ⟨q, Or.inr hq, hrest⟩
      · rintro ⟨q, rfl | hq, hP, hy⟩
        · exact Or.inl ⟨hP, hy⟩
        · exact Or.inr ⟨q, hq, hP, hy⟩
    · have hst : stored f m β s (k + 1) = stored f m β s k := by
        rw [stored]
        exact ite_eq_right fun h' => h (hnt.1 h')
      rw [hst, hsto, ite_eq_right h]

/-- The cost of a step, stage by stage (plumbing). -/
lemma iterC_cost_eq (R : Cont.RayCostOps E) (p : ℝ) (L : List (ℝ × ℝ)) (S : List (PieceRec E)) :
    (iterC f m β R p L S).cost =
      (midC p L).cost + ((WaterFilling.waterFillC f m β (midC p L).val).cost +
        ((velC m β (midC p L).val (WaterFilling.waterFillC f m β (midC p L).val).val).cost +
          ((Cont.contC f m β (midC p L).val (WaterFilling.waterFillC f m β (midC p L).val).val
            (velC m β (midC p L).val (WaterFilling.waterFillC f m β (midC p L).val).val).val
              R).cost + ((L.length, 0, 0) + ((1, 0, 0) + 0))))) := rfl

/-- The costs of a step at step `k < K` of a run: the minimizations and evaluations of `f` of
water-filling at `α̂_k` and of the affine continuation from its output, and at most `5k + 3`
operations besides those of water-filling, of `v(α̂_k)` and of the affine continuation. -/
lemma iterC_cost (H : Hyp f m β) {s : ℕ → ℝ} {K : ℕ} (hrun : IsRun f m β s K) {k : ℕ}
    (hk : k < K) (R : Cont.RayCostOps E) {c : ℕ}
    (hR : ∀ x w, R.arith x w ≤ c * Fintype.card E ^ 3) {L : List (ℝ × ℝ)}
    {S : List (PieceRec E)} (hinv : PiecesInv f m β s k L S) :
    (iterC f m β R (runPt f m β s k) L S).cost.2.1 =
        WaterFilling.oracleCalls f m β (s k) + Cont.contCalls (WaterFilling.waterFill f m β (s k))
          (velocity f m β (s k)) R.toRayCost ∧
      (iterC f m β R (runPt f m β s k) L S).cost.2.2 =
        WaterFilling.fEvals f m β (s k) + Cont.contEvals f m β (s k)
          (WaterFilling.waterFill f m β (s k)) (velocity f m β (s k)) R.toRayCost ∧
      (iterC f m β R (runPt f m β s k) L S).cost.1 ≤ 5 * k + 3 +
        ((6 * Fintype.card E ^ 3 + 56 * Fintype.card E ^ 2 + 29 * Fintype.card E + 2) +
          (6 * Fintype.card E ^ 2 + 8 * Fintype.card E) +
          (3 * Fintype.card E ^ 4 + (2 * c + 5) * Fintype.card E ^ 3 +
            44 * Fintype.card E ^ 2 + 57 * Fintype.card E + 62)) := by
  obtain ⟨hlen, -, hint, hcov, -⟩ := hinv
  obtain ⟨hpt, hsk⟩ := runPt_spec hrun hk
  have hk01 := (run_mem H hrun k hk).1
  have hmid : (midC (runPt f m β s k) L).val = s k := by
    rw [midC_val (fun I hI => (hint I hI).2.1) hcov hpt, ← hsk]
  have WH : WaterFilling.Hyp f m β (s k) := ⟨H.rank, H.beta, H.reward, hk01.1.le⟩
  obtain ⟨hwv, hwc, hwe, hwa⟩ := WaterFilling.waterFillC_spec WH
  have hwf : WaterFilling.waterFill f m β (s k) = bestResponse f m β (s k) :=
    (WaterFilling.waterfilling WH).1
  have hvel : (velC m β (s k) (WaterFilling.waterFill f m β (s k))).val =
      velocity f m β (s k) := by
    rw [hwf]
    exact velC_val (s k)
  rw [iterC_cost_eq, hmid, hwv, hvel]
  obtain ⟨mc1, mc2, mc3⟩ := midC_cost (runPt f m β s k) L
  obtain ⟨vc1, vc2, vc3⟩ := velC_cost (m := m) (β := β) (s k) (WaterFilling.waterFill f m β (s k))
  obtain ⟨cc1, cc2, cc3⟩ := Cont.contC_cost (f := f) (m := m) (β := β) (αh := s k)
    (x := WaterFilling.waterFill f m β (s k)) (v := velocity f m β (s k)) R
  have h4 := hR (WaterFilling.waterFill f m β (s k)) (velocity f m β (s k))
  have h5 := hR (WaterFilling.waterFill f m β (s k)) (-velocity f m β (s k))
  have e : (2 * c + 5) * Fintype.card E ^ 3 =
      c * Fintype.card E ^ 3 + c * Fintype.card E ^ 3 + 5 * Fintype.card E ^ 3 := by ring
  rw [hlen] at mc3
  simp only [Prod.fst_add, Prod.snd_add, add_zero] at *
  refine ⟨by simp [mc1, hwc, vc1, cc1], by simp [mc2, hwe, vc2, cc2], ?_⟩
  rw [e]
  generalize (Cont.contC f m β (s k) (WaterFilling.waterFill f m β (s k))
    (velocity f m β (s k)) R).cost.1 = t at cc3 ⊢
  generalize (WaterFilling.waterFillC f m β (s k)).cost.1 = w at hwa ⊢
  generalize (velC m β (s k) (WaterFilling.waterFill f m β (s k))).cost.1 = u at vc3 ⊢
  generalize (midC (runPt f m β s k) L).cost.1 = q at mc3 ⊢
  omega

/-- A pass of the while loop whose test fails takes a step and continues (plumbing). -/
lemma whileC_succ {R : Cont.RayCostOps E} {p : ℕ → ℝ} {j k : ℕ} {L : List (ℝ × ℝ)}
    {S : List (PieceRec E)} (h : (coverC 0 L).val = false) :
    (whileC f m β R p (j + 1) k L S).val =
        (whileC f m β R p j (k + 1) (iterC f m β R (p k) L S).val.1
          (iterC f m β R (p k) L S).val.2).val ∧
      (whileC f m β R p (j + 1) k L S).cost = (coverC 0 L).cost +
        ((iterC f m β R (p k) L S).cost + (whileC f m β R p j (k + 1)
          (iterC f m β R (p k) L S).val.1 (iterC f m β R (p k) L S).val.2).cost) := by
  have e : whileC f m β R p (j + 1) k L S = (coverC 0 L >>=ᶜ fun b =>
      if b then ret (L, S) else
        iterC f m β R (p k) L S >>=ᶜ fun r => whileC f m β R p j (k + 1) r.1 r.2) := rfl
  rw [e, val_bind, cost_bind, h]
  exact ⟨rfl, rfl⟩

omit [DecidableEq E] in
/-- The test `C = [0, 1]` fails at step `k < K` of a run, as `C_k ≠ [0, 1]` (`IsRun`). -/
lemma coverC_false {s : ℕ → ℝ} {K : ℕ} (hrun : IsRun f m β s K) {k : ℕ} (hk : k < K)
    {L : List (ℝ × ℝ)} {S : List (PieceRec E)} (hinv : PiecesInv f m β s k L S) :
    (coverC 0 L).val = false := by
  obtain ⟨-, -, hint, hcov, -⟩ := hinv
  by_contra hb
  rw [Bool.not_eq_false] at hb
  apply (hrun k hk).1
  refine (covered_subset s k).antisymm fun q hq => (hcov q).2 ?_
  rcases hq.1.lt_or_eq with hq0 | rfl
  · obtain ⟨I, hI, h⟩ := coverC_sound L 0 hb q hq0 hq.2
    exact ⟨I, hI, h⟩
  · -- `q = 0`: the first interval starts at most at `0`, so at `0`
    cases L with
    | nil =>
      simp only [coverC, val_ops, decide_eq_true_eq] at hb
      linarith
    | cons I L' =>
      have hI0 : I.1 ≤ 0 := by
        by_contra h
        simp [coverC, h] at hb
      have hI := hint I List.mem_cons_self
      exact ⟨I, List.mem_cons_self, hI0, hI.1.trans hI.2.1⟩

omit [DecidableEq E] in
/-- The test `C = [0, 1]` passes at the end of a run that stops, `C_K = [0, 1]` (not in the
paper). -/
lemma coverC_true {s : ℕ → ℝ} {K : ℕ} (hstop : covered f m β s K = Set.Icc (0 : ℝ) 1)
    {L : List (ℝ × ℝ)} {S : List (PieceRec E)} (hinv : PiecesInv f m β s K L S) :
    (coverC 0 L).val = true := by
  obtain ⟨-, hs, hint, hcov, -⟩ := hinv
  refine coverC_complete L 0 hs (fun I hI => (hint I hI).2.1.trans (hint I hI).2.2)
    fun q hq0 hq1 => ?_
  have hq : q ∈ covered f m β s K := by
    rw [hstop]
    exact ⟨hq0.le, hq1⟩
  obtain ⟨I, hI, hqI⟩ := (hcov q).1 hq
  exact ⟨I, hI, hqI.1, hqI.2⟩

/-- The while loop on a run that stops: from a state for `C_k` and `𝓘_k` with `K − k + 1` passes
left, the test `C = [0, 1]` fails before each step (`coverC_false`) and passes after the last
(`coverC_true`), and the loop takes the steps `k, …, K − 1`, ending with a state for `C_K` and
`𝓘_K`, with the minimizations and evaluations of `f` of these steps; each step takes at most
`7K + (c + 7)(n + 2)⁴ − 7` further arithmetic operations, and the last test at most `2K + 1`. -/
lemma whileC_spec (H : Hyp f m β) {s : ℕ → ℝ} {K : ℕ} (hrun : IsRun f m β s K)
    (hstop : covered f m β s K = Set.Icc (0 : ℝ) 1)
    (R : Cont.RayCostOps E) {c : ℕ} (hR : ∀ x w, R.arith x w ≤ c * Fintype.card E ^ 3) :
    ∀ j k L S, k + j = K → PiecesInv f m β s k L S →
      PiecesInv f m β s K (whileC f m β R (runPt f m β s) (j + 1) k L S).val.1
          (whileC f m β R (runPt f m β s) (j + 1) k L S).val.2 ∧
        (whileC f m β R (runPt f m β s) (j + 1) k L S).cost.2.1 =
          ∑ i ∈ Finset.Ico k K, (WaterFilling.oracleCalls f m β (s i) +
            Cont.contCalls (WaterFilling.waterFill f m β (s i)) (velocity f m β (s i))
              R.toRayCost) ∧
        (whileC f m β R (runPt f m β s) (j + 1) k L S).cost.2.2 =
          ∑ i ∈ Finset.Ico k K, (WaterFilling.fEvals f m β (s i) + Cont.contEvals f m β (s i)
            (WaterFilling.waterFill f m β (s i)) (velocity f m β (s i)) R.toRayCost) ∧
        (whileC f m β R (runPt f m β s) (j + 1) k L S).cost.1 + 7 * j ≤
          j * (7 * K + (c + 7) * (Fintype.card E + 2) ^ 4) + (2 * K + 1) := by
  intro j
  induction j with
  | zero =>
    -- the last pass: the test `C = [0, 1]` passes and ends the loop
    intro k L S hk hinv
    rw [add_zero] at hk
    subst hk
    have hb := coverC_true hstop hinv
    obtain ⟨c1, c2, c3⟩ := coverC_cost L 0
    have e : whileC f m β R (runPt f m β s) (0 + 1) k L S = (coverC 0 L >>=ᶜ fun b =>
        if b then ret (L, S) else
          iterC f m β R (runPt f m β s k) L S >>=ᶜ fun r =>
            whileC f m β R (runPt f m β s) 0 (k + 1) r.1 r.2) := rfl
    have hv : (whileC f m β R (runPt f m β s) (0 + 1) k L S).val = (L, S) := by
      rw [e, val_bind, hb]
      rfl
    have hc : (whileC f m β R (runPt f m β s) (0 + 1) k L S).cost = (coverC 0 L).cost := by
      rw [e, cost_bind, hb]
      simp
    rw [hv, hc, Finset.Ico_self, Finset.sum_empty, Finset.sum_empty]
    rw [hinv.1] at c3
    refine ⟨hinv, c1, c2, ?_⟩
    simp only [mul_zero, add_zero, zero_mul, zero_add]
    exact c3
  | succ j ih =>
    intro k L S hk hinv
    have hkK : k < K := by omega
    obtain ⟨hv, hc⟩ := whileC_succ (f := f) (m := m) (β := β) (R := R) (p := runPt f m β s)
      (j := j + 1) (S := S) (coverC_false hrun hkK hinv)
    have hinv' := iterC_inv H hrun hkK R hinv
    obtain ⟨i1, i2, i3⟩ := iterC_cost H hrun hkK R hR hinv
    obtain ⟨w1, w2, w3, w4⟩ := ih (k + 1) _ _ (by omega) hinv'
    obtain ⟨c1, c2, c3⟩ := coverC_cost L 0
    have hlen := hinv.1
    rw [hv, hc]
    refine ⟨w1, ?_, ?_, ?_⟩
    · simp only [Prod.snd_add, Prod.fst_add, c1, i1, w2, zero_add]
      rw [Finset.sum_eq_sum_Ico_succ_bot hkK]
    · simp only [Prod.snd_add, c2, i2, w3, zero_add]
      rw [Finset.sum_eq_sum_Ico_succ_bot hkK]
    · simp only [Prod.fst_add]
      have hstep := step_ops_le (Fintype.card E) c
      rw [hlen] at c3
      generalize (coverC 0 L).cost.1 = a at c3 ⊢
      generalize (iterC f m β R (runPt f m β s k) L S).cost.1 = b at i3 ⊢
      generalize (whileC f m β R (runPt f m β s) (j + 1) (k + 1)
        (iterC f m β R (runPt f m β s k) L S).val.1
        (iterC f m β R (runPt f m β s k) L S).val.2).cost.1 = d at w4 ⊢
      generalize (c + 7) * (Fintype.card E + 2) ^ 4 = Q at hstep w4 ⊢
      have : (j + 1) * (7 * K + Q) = j * (7 * K + Q) + (7 * K + Q) := by ring
      rw [this]
      omega

/-- The counted enumeration (`alg:pieces`, lines 504-509) on a run of `K` steps that stops,
`C_K = [0, 1]` (not in the paper: the paper counts in prose): it performs the `K` steps and the last
test `C = [0, 1]`, which ends the loop, and ends with the list of the intervals `I(α̂_k)`, sorted
by their left ends, whose union is `C_K`, and the stored pieces of `𝓘_K` with their affine maps; it
makes exactly
`runCalls` submodular minimizations and `runEvals` further evaluations of `f`, and, if each ray
computation makes at most `c n³` arithmetic operations, at most
`(c + 7)(n + 2)⁶(B + 1) + 7(n + 2)⁴(B + 1)²` further arithmetic operations. -/
theorem piecesC_spec (H : Hyp f m β) (R : Cont.RayCostOps E) {c : ℕ}
    (hR : ∀ x w, R.arith x w ≤ c * Fintype.card E ^ 3) {s : ℕ → ℝ} {K : ℕ}
    (hrun : IsRun f m β s K) (hstop : covered f m β s K = Set.Icc (0 : ℝ) 1) :
    (piecesC f m β R s K).val.1.Pairwise (fun I J => I.1 ≤ J.1) ∧
      (∀ α, α ∈ covered f m β s K ↔ ∃ I ∈ (piecesC f m β R s K).val.1, α ∈ Icc I.1 I.2) ∧
      (∀ P y, (P, y) ∈ stored f m β s K ↔ ∃ q ∈ (piecesC f m β R s K).val.2,
        P = Icc q.lo q.hi ∧ y = fun α e => q.x e + (α - q.share) * q.v e) ∧
      (piecesC f m β R s K).cost.2.1 = runCalls f m β R.toRayCost s K ∧
      (piecesC f m β R s K).cost.2.2 = runEvals f m β R.toRayCost s K ∧
      (piecesC f m β R s K).cost.1 ≤
        (c + 7) * (Fintype.card E + 2) ^ 6 * (numBP f m β + 1) +
          7 * (Fintype.card E + 2) ^ 4 * (numBP f m β + 1) ^ 2 := by
  have hinv0 : PiecesInv f m β s 0 [] [] := by
    refine ⟨rfl, List.Pairwise.nil, fun I hI => absurd hI List.not_mem_nil, fun α => ?_,
      fun P y => ?_⟩
    · simp [covered]
    · simp [stored]
  obtain ⟨⟨-, h1, -, h2, h3⟩, h4, h5, h6⟩ :=
    whileC_spec H hrun hstop R hR K 0 [] [] (zero_add K) hinv0
  refine ⟨h1, h2, h3, ?_, ?_, ?_⟩
  · rw [piecesC, h4, runCalls, Finset.range_eq_Ico]
  · rw [piecesC, h5, runEvals, Finset.range_eq_Ico]
  · rw [piecesC]
    -- the run takes at least one step, as `C_0 = ∅`; so the slack of `7` in each step pays for the
    -- last test
    have hK1 : 1 ≤ K := by
      rcases Nat.eq_zero_or_pos K with rfl | h
      · have h0 : (0 : ℝ) ∈ covered f m β s 0 := by
          rw [hstop]
          exact ⟨le_rfl, zero_le_one⟩
        simp [covered] at h0
      · exact h
    have h6' : (whileC f m β R (runPt f m β s) (K + 1) 0 [] []).cost.1 ≤
        K * (7 * K + (c + 7) * (Fintype.card E + 2) ^ 4) := by
      omega
    refine h6'.trans ?_
    have hK := run_length_le H hrun
    set N := (Fintype.card E + 2) ^ 2 * (numBP f m β + 1)
    calc K * (7 * K + (c + 7) * (Fintype.card E + 2) ^ 4)
        ≤ N * (7 * N + (c + 7) * (Fintype.card E + 2) ^ 4) :=
          Nat.mul_le_mul hK (Nat.add_le_add_right (Nat.mul_le_mul_left 7 hK) _)
      _ = (c + 7) * (Fintype.card E + 2) ^ 6 * (numBP f m β + 1) +
          7 * (Fintype.card E + 2) ^ 4 * (numBP f m β + 1) ^ 2 := by
          simp only [N]
          ring

/-- The running time of `thm:pieces`, step (7) of its proof (`stoc-sections/appB-quadratic.tex:494`;
not in the paper: the paper counts in prose), for `n = |E| ≥ 1` and `B = numBP`: "As in the proof
of `thm:waterfilling`, each submodular minimization takes time `O(n⁵ log n)·FO + O(n⁶ log n)` using
Iwata and Orlin's algorithm [IO09]: its objective is `f` minus a modular function, evaluated in time
`FO + O(n)`. Substituting this bound gives the stated total runtime." If each ray computation of
[GGJ17] makes at most `c n²` submodular minimizations and `c n²` further evaluations of `f` (cited,
`Cont.RayCost`) and `d n³` arithmetic operations (assumed, not cited: the STOC version does not
state them; `Cont.RayCostOps`), an evaluation of `f` takes time `FO ≥ 0` and a
minimization time `TS ≤ sfmTime C₁ C₂ n FO` (cited, [IO09]; `Counted.sfmTime`), then the counted
enumeration `piecesC` of a run that stops takes time at most
`((18c + 72) + (18c + 36)C₁) n⁹ (B + 1) lg n · FO +
(729(d + 7) + (18c + 36)C₁(C₂ + 1)) n¹⁰ (B + 1) lg n + 567 n⁴ (B + 1)²`, the
`O(n⁹(B + 1) log n)·FO + O(n¹⁰(B + 1) log n + n⁴(B + 1)²)` of the theorem
(`lg n = ⌈log₂ n⌉ + 1`): at most `(18c + 36) n⁴ (B + 1)` minimizations and `(18c + 72) n⁵ (B + 1)`
further evaluations of `f` (`run_costs`, `costs_poly`), and at most
`(d + 7)(n + 2)⁶(B + 1) + 7(n + 2)⁴(B + 1)²` further arithmetic operations (`piecesC_spec`), with
`n + 2 ≤ 3n`. -/
theorem piecesC_time (H : Hyp f m β) (hn : 0 < Fintype.card E) (R : Cont.RayCostOps E) {c d : ℕ}
    (hc : ∀ x w, R.calls x w ≤ c * Fintype.card E ^ 2 ∧ R.evals x w ≤ c * Fintype.card E ^ 2)
    (hd : ∀ x w, R.arith x w ≤ d * Fintype.card E ^ 3) {s : ℕ → ℝ} {K : ℕ}
    (hrun : IsRun f m β s K) (hstop : covered f m β s K = Set.Icc (0 : ℝ) 1) {FO TS C₁ C₂ : ℝ}
    (hFO : 0 ≤ FO) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hTS : TS ≤ Counted.sfmTime C₁ C₂ (Fintype.card E) FO) :
    Counted.time FO TS (piecesC f m β R s K).cost ≤
      ((18 * c + 72) + (18 * c + 36) * C₁) * (Fintype.card E : ℝ) ^ 9 * (numBP f m β + 1) *
          Counted.lg (Fintype.card E) * FO +
        (729 * (d + 7) + (18 * c + 36) * C₁ * (C₂ + 1)) * (Fintype.card E : ℝ) ^ 10 *
          (numBP f m β + 1) * Counted.lg (Fintype.card E) +
        567 * (Fintype.card E : ℝ) ^ 4 * (numBP f m β + 1) ^ 2 := by
  obtain ⟨-, -, -, h1, h2, h3⟩ := piecesC_spec H R hd hrun hstop
  obtain ⟨hc1, hc2⟩ := run_costs H hrun R.toRayCost hc
  obtain ⟨hp1, hp2⟩ := costs_poly (Fintype.card E) (numBP f m β) c
  have key := Counted.time_le hFO (Counted.sfmTime_nonneg (Fintype.card E) hC₁ hC₂ hFO) hTS h3
    (h2.le.trans (hc2.trans hp2)) (h1.le.trans (hc1.trans hp1))
  refine key.trans ?_
  have hx : (1 : ℝ) ≤ Fintype.card E := by exact_mod_cast hn
  have hL1 : (1 : ℝ) ≤ (Counted.lg (Fintype.card E) : ℝ) := by exact_mod_cast Counted.one_le_lg _
  have hb0 : (0 : ℝ) ≤ (numBP f m β : ℝ) + 1 := by positivity
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have hd7 : (0 : ℝ) ≤ (d : ℝ) + 7 := by positivity
  unfold Counted.sfmTime
  push_cast
  set x : ℝ := (Fintype.card E : ℝ)
  set g : ℝ := (Counted.lg (Fintype.card E) : ℝ)
  set b : ℝ := (numBP f m β : ℝ) + 1
  have hx0 : (0 : ℝ) ≤ x := by linarith
  -- `n + 2 ≤ 3n`
  have h3x : x + 2 ≤ 3 * x := by linarith
  have e6 : x ^ 6 ≤ x ^ 10 := pow_le_pow_right₀ hx (by norm_num)
  have e5 : x ^ 5 ≤ x ^ 9 := pow_le_pow_right₀ hx (by norm_num)
  have g10 : x ^ 10 ≤ x ^ 10 * g := le_mul_of_one_le_right (pow_nonneg hx0 10) hL1
  have g9 : x ^ 9 ≤ x ^ 9 * g := le_mul_of_one_le_right (pow_nonneg hx0 9) hL1
  -- (i) the arithmetic operations of the pieces: `(x + 2)⁶ ≤ 729x⁶ ≤ 729x¹⁰g`
  have q6 : (x + 2) ^ 6 ≤ 729 * (x ^ 10 * g) :=
    calc (x + 2) ^ 6 ≤ (3 * x) ^ 6 := pow_le_pow_left₀ (by linarith) h3x 6
      _ = 729 * x ^ 6 := by ring
      _ ≤ 729 * (x ^ 10 * g) := by linarith [e6.trans g10]
  have i1 : ((d : ℝ) + 7) * (x + 2) ^ 6 * b ≤ ((d : ℝ) + 7) * (729 * (x ^ 10 * g)) * b :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left q6 hd7) hb0
  -- (ii) the sorted interval list: `(x + 2)⁴ ≤ 81x⁴`
  have q4 : (x + 2) ^ 4 ≤ 81 * x ^ 4 :=
    calc (x + 2) ^ 4 ≤ (3 * x) ^ 4 := pow_le_pow_left₀ (by linarith) h3x 4
      _ = 81 * x ^ 4 := by ring
  have i2 : 7 * (x + 2) ^ 4 * b ^ 2 ≤ 7 * (81 * x ^ 4) * b ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left q4 (by norm_num)) (sq_nonneg b)
  -- (iii) the evaluations of `f`: `x⁵ ≤ x⁹g`
  have i3 : FO * ((18 * c + 72) * x ^ 5 * b) ≤ FO * ((18 * c + 72) * (x ^ 9 * g) * b) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (e5.trans g9) (by linarith)) hb0) hFO
  -- (iv) the minimizations: an identity
  have i4 : C₁ * (x ^ 5 * g * (FO + C₂ * x) + x ^ 6 * g) * ((18 * c + 36) * x ^ 4 * b) =
      (18 * c + 36) * C₁ * x ^ 9 * b * g * FO +
        (18 * c + 36) * C₁ * (C₂ + 1) * x ^ 10 * b * g := by ring
  linarith [i1, i2, i3, i4]

end Counts

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
The Lean has the running time from what the proof derives it from, with the time of a
minimization cited: `alg:pieces` (`AlgPieces`) computes them with at most `(n + 2)²(B + 1)`
best-response computations, and
altogether `O(n⁴(B + 1))` submodular minimizations, `O(n⁵(B + 1))` further evaluations of `f`, and
`O(n⁶(B + 1) + n⁴(B + 1)²)` further arithmetic operations:

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
   constants;
5. the arithmetic operations: if each ray computation also makes at most `c n³` arithmetic
   operations (assumed, not cited: the STOC version does not state them; `Cont.RayCostOps`), the
   counted enumeration `piecesC`, which performs the
   while loop of `alg:pieces` in the cost model of `Stoc.Counted` on a run that stops (with the
   counted water-filling, `v(α̂)` by (`eq:velocity`), the counted procedure `Cont.contC` of
   `lem:continuation`, the sorted interval list of `C_k` and the last test `C = [0, 1]`, which ends
   the loop), ends with the sorted list of the intervals `I(α̂_k)`, whose union
   is `C_K`, and with the pieces of `𝓘_K` and their affine maps, makes exactly `runCalls`
   minimizations and `runEvals` further evaluations of `f`, and at most
   `(c + 7)(n + 2)⁶(B + 1) + 7(n + 2)⁴(B + 1)²` further arithmetic operations, comparisons
   included: the `O(n⁶(B + 1) + n⁴(B + 1)²)` of the STOC version, as `n + 2 ≤ 3n` for `n ≥ 1`
   (`piecesC_spec`; not in the paper: the paper counts in prose).

Steps: (1) `run_mem`; (2) `run_step`; (3) `run_length_le`; (4) `stored_cover`, `stored_eq_pieces`;
(5) `isBestShare_optimal`, with `exists_isBestShare`; (6) `alg_step` and `run_costs`, with the
explicit constants of `costs_poly`, and the counted enumeration `piecesC` (`piecesC_spec`); (7) the
time of a minimization by the algorithm of Iwata and Orlin [IO09], `O(n⁵ log n)·FO + O(n⁶ log n)`,
substituted into the counts of (6), gives the stated running time (`piecesC_time`): for `n ≥ 1`,
with the cited bounds of a ray computation (`c n²` minimizations and evaluations), its assumed
`d n³` operations and the time `TS ≤ sfmTime C₁ C₂ n FO` of a minimization (cited, a hypothesis),
the counted enumeration takes time at most `((18c + 72) + (18c + 36)C₁) n⁹ (B + 1) lg n · FO +
(729(d + 7) + (18c + 36)C₁(C₂ + 1)) n¹⁰ (B + 1) lg n + 567 n⁴ (B + 1)²`,
`O(n⁹(B + 1) log n)·FO + O(n¹⁰(B + 1) log n + n⁴(B + 1)²)`. -/
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
    (∀ (R : Cont.RayCost E) (c : ℕ),
      (∀ x w, R.calls x w ≤ c * Fintype.card E ^ 2 ∧ R.evals x w ≤ c * Fintype.card E ^ 2) →
      ∀ s K, IsRun f m β s K →
        runCalls f m β R s K ≤ (18 * c + 36) * Fintype.card E ^ 4 * (numBP f m β + 1) ∧
          runEvals f m β R s K ≤ (18 * c + 72) * Fintype.card E ^ 5 * (numBP f m β + 1)) ∧
    (∀ (R : Cont.RayCostOps E) (c : ℕ), (∀ x w, R.arith x w ≤ c * Fintype.card E ^ 3) →
      ∀ s K, IsRun f m β s K → covered f m β s K = Set.Icc (0 : ℝ) 1 →
        (piecesC f m β R s K).val.1.Pairwise (fun I J => I.1 ≤ J.1) ∧
        (∀ α, α ∈ covered f m β s K ↔ ∃ I ∈ (piecesC f m β R s K).val.1, α ∈ Icc I.1 I.2) ∧
        (∀ P y, (P, y) ∈ stored f m β s K ↔ ∃ q ∈ (piecesC f m β R s K).val.2,
          P = Icc q.lo q.hi ∧ y = fun α e => q.x e + (α - q.share) * q.v e) ∧
        (piecesC f m β R s K).cost.2.1 = runCalls f m β R.toRayCost s K ∧
        (piecesC f m β R s K).cost.2.2 = runEvals f m β R.toRayCost s K ∧
        (piecesC f m β R s K).cost.1 ≤
          (c + 7) * (Fintype.card E + 2) ^ 6 * (numBP f m β + 1) +
            7 * (Fintype.card E + 2) ^ 4 * (numBP f m β + 1) ^ 2) ∧
    (0 < Fintype.card E → ∀ (R : Cont.RayCostOps E) (c d : ℕ),
      (∀ x w, R.calls x w ≤ c * Fintype.card E ^ 2 ∧ R.evals x w ≤ c * Fintype.card E ^ 2) →
      (∀ x w, R.arith x w ≤ d * Fintype.card E ^ 3) → ∀ s K, IsRun f m β s K →
      covered f m β s K = Set.Icc (0 : ℝ) 1 → ∀ FO TS C₁ C₂ : ℝ, 0 ≤ FO → 0 ≤ C₁ → 0 ≤ C₂ →
        TS ≤ Counted.sfmTime C₁ C₂ (Fintype.card E) FO →
        Counted.time FO TS (piecesC f m β R s K).cost ≤
          ((18 * c + 72) + (18 * c + 36) * C₁) * (Fintype.card E : ℝ) ^ 9 * (numBP f m β + 1) *
              Counted.lg (Fintype.card E) * FO +
            (729 * (d + 7) + (18 * c + 36) * C₁ * (C₂ + 1)) * (Fintype.card E : ℝ) ^ 10 *
              (numBP f m β + 1) * Counted.lg (Fintype.card E) +
            567 * (Fintype.card E : ℝ) ^ 4 * (numBP f m β + 1) ^ 2) := by
  refine ⟨fun s K hrun => ?_, ?_, fun s K αs y halg => ⟨?_, ?_, ?_⟩, fun s K hrun hstop => ?_,
    fun s K hrun k hk => ?_, fun R c hc s K hrun => ?_, fun R c hR s K hrun hstop => ?_,
    fun hn R c d hc hd s K hrun hstop _ _ _ _ hFO hC₁ hC₂ hTS => ?_⟩
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
  -- the arithmetic operations below.
  · obtain ⟨h1, h2⟩ := run_costs H hrun R hc
    obtain ⟨h3, h4⟩ := costs_poly (Fintype.card E) (numBP f m β) c
    exact ⟨h1.trans h3, h2.trans h4⟩
  -- The arithmetic operations: the counted enumeration `piecesC` performs the while loop in the
  -- cost model of `Stoc.Counted`, with the counted water-filling, `v(α̂)`, the counted procedure
  -- of `lem:continuation` and the sorted interval list of `C_k`; it ends with `C_K` and `𝓘_K`, with
  -- the minimizations and evaluations above and `O(n⁶(B + 1) + n⁴(B + 1)²)` further arithmetic
  -- operations (`piecesC_spec`; not in the paper: the paper counts in prose).
  · exact piecesC_spec H R hR hrun hstop
  -- (7) "As in the proof of `thm:waterfilling`, each submodular minimization takes time
  -- `O(n⁵ log n)·FO + O(n⁶ log n)` using Iwata and Orlin's algorithm [IO09]: its objective is `f`
  -- minus a modular function, evaluated in time `FO + O(n)`. Substituting this bound gives the
  -- stated total runtime." (`piecesC_time`, with the time of a minimization by [IO09] as a
  -- hypothesis, cited; not in the paper: the paper counts in prose)
  · exact piecesC_time H hn R hc hd hrun hstop hFO hC₁ hC₂ hTS

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
