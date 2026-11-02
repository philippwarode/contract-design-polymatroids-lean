-- stamp r7 2026-11-02
import Stoc.OptimalShare.Pieces

/-!
# Affine continuation

The STOC version, Appendix B.4 (`sec:A-pieces`), the paragraph "Affine continuation"
(`stoc-sections/appB-quadratic.tex:401-410`) and Lemma `lem:continuation` (statement :412-418, proof
:420-453).

For a share `α̂ ∈ (0, 1)`, `x̂ = x*(α̂)` and the vector `v(α̂)` that (`eq:velocity`) assigns to its
state, the affine continuation is `y(α) = x̂ + (α − α̂) v(α̂)` (`line`, `eq:A-cont`), and `I(α̂)` is
the connected component containing `α̂` of the shares `α ∈ [0, 1]` with `y(α) = x*(α)` (`found`);
it is a closed interval, possibly a singleton, by `lem:pwaffine` (`found_eq_Icc`).

`lem:continuation` is `Stoc.Tracing.continuation`. Its proof follows the STOC version's, step by
step:

1. by `prop:optchar` (`optchar`), `y = x*` exactly where `y` is feasible, `ρ̃ ≥ 0` and every
   positive level set of `ρ̃` is tight, with `ρ̃_e(α) = α m_e − β_e y_e(α)` (`agree_iff`);
2. feasibility along `y` is an interval: coordinate nonnegativity gives ratio bounds (`ratioLo`,
   `ratioHi`, `ratio_iff`), and the rank constraints are handled by ray computations from `x̂` in
   the directions `v` and `−v` (`rayMax`, the largest feasible steps `d⁺, d⁻ ∈ [0, ∞]`, and the
   bounds `α̂ + d⁺`, `α̂ − d⁻`, `rankHi`, `rankLo`; `rank_y_iff`);
3. intersecting with `[0, 1]` and the inequalities `ρ̃_e ≥ 0` gives the closed interval
   `K = [κ⁻, κ⁺] ∋ α̂` (`kLo`, `kHi`, `mem_K_iff`, `K_facts`);
4. `K` is cut at `α̂` and at the crossings of distinct affine functions `ρ̃_e`, `ρ̃_g` (`cuts`, at
   most `C(n, 2) + 3` cut points, `card_cuts_le`); on each open interval `J` between consecutive cut
   points (a cell), the positive level sets form a fixed chain `L_1 ⊊ ⋯ ⊊ L_q` with `q ≤ n`
   (`chainSet`, `cell_chain`, from `cell_order` and `cell_pos`);
5. for the midpoint `c` of `J`, tightness throughout `J` is equivalent to the tests
   `y(c)(L_i) = f(L_i)`, `v(L_i) = 0` (`Test`), and if these fail, tightness holds at at most one
   point of `J` (`cell_tests`);
6. starting at `α̂`, the consecutive cells on either side that pass the tests are retained (`hi`,
   `lo`, `retained`), and the union of their closures with `{α̂}` is exactly `I(α̂)`
   (`found_eq_walk`);
7. if `I(α̂)` is nondegenerate, an end in `(0, 1)` is a breakpoint, as otherwise the affine response
   there would extend the component, so `I(α̂)` is a piece (`found_mem_pieces`);
8. at a non-event point, `lem:velocity` gives `x* = y` on a neighborhood (`mem_interior_found`).

The procedure takes `x̂` and `v` as inputs (the arguments `x` and `v` of the definitions in the
namespace `Cont`). The ray computation of step 2 is cited from Goemans, Gupta and Jaillet [GGJ17]
(the discrete Newton method for arbitrary directions, `n² + O(n log² n)` minimizations and `O(n²)`
evaluations of `f` per ray): it is not formalised, `rayMax` is defined as its result, the largest
feasible step `d ∈ [0, ∞]` (uncapped, as in the STOC version; `K` is intersected with `[0, 1]`
afterwards), and its work enters as a parameter (`RayCost`: `calls x w` minimizations and
`evals x w` further evaluations of `f` for the ray from `x` in the direction `w`), with the cited
bounds as hypotheses.

The costs of the first sentence of `lem:continuation` are counted as `WaterFilling.lean` counts
those of water-filling: the submodular minimizations (`contCalls`, those of the two ray
computations) and the further evaluations of `f` (`contEvals`, those of the two ray computations
and one for each set `L_i` tested on each cell, `cellEvals`). With at most `N` minimizations and
`N'` further evaluations per ray, the procedure makes at most `2N` minimizations (`contCalls_le`)
and at most `2N' + n(C(n, 2) + 2)` further evaluations of `f` (`contEvals_le`: at most
`C(n, 2) + 2` cells, `card_cells_le`, each with at most `n` set tests). With the cited bounds in
the form `N = N' = c n²` ([GGJ17]: `n² + O(n log² n)` minimizations and `O(n²)` evaluations of `f`
per ray), these are the `O(n²)` and `O(n³)` of `lem:continuation` with explicit constants, `2c n²`
and `(2c + 2) n³` (`cont_costs_poly`). The
arithmetic operations (`O(n⁴)` in the STOC version) are not counted.

Steps that the STOC version cites or leaves implicit are proved in lemmas of their own, marked "not
in the paper": `rayMax_spec` (in step 2, that the feasible steps of a ray form `[0, d]` or
`[0, ∞)`, which the STOC version takes from the cited ray computation), `card_cuts_le` and
`card_cells_le` (the explicit counts `C(n, 2) + 3` and `C(n, 2) + 2` behind the `O(n²)` intervals
of step 4), `tests_le_cube` and `cont_costs_poly` (the explicit constants of the costs), and
`agree_of_two` and `not_mem_BP_of_mem_Ioo` (in step 7).

Written on 2026-10-25 for the STOC version; it replaces the affine continuation of
`Stoc/OptimalShare/Tracing.lean`, where `I(α̂)` was defined as the largest interval around `α̂` on
which `x* = y` and the procedure of the proof was not formalised.
-/

namespace Stoc

namespace Tracing

open Finset Set

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {f : Finset E → ℝ} {m β : E → ℝ}

/-! ### The affine continuation and `I(α̂)` -/

section Defs

variable (f m β)

/-- The affine continuation `y(α) = x̂ + (α − α̂) v(α̂)` of (`eq:A-cont`), with `x̂ = x*(α̂)` and
`v(α̂) = velocity f m β α̂`. -/
noncomputable def line (αh α : ℝ) : E → ℝ :=
  fun e => bestResponse f m β αh e + (α - αh) * velocity f m β αh e

/-- `y(α) = x*(α)`. -/
def Agree (αh α : ℝ) : Prop := bestResponse f m β α = line f m β αh α

/-- The shares `α ∈ [0, 1]` with `y(α) = x*(α)`. -/
def agreeSet (αh : ℝ) : Set ℝ := {α | α ∈ Set.Icc (0 : ℝ) 1 ∧ Agree f m β αh α}

/-- `I(α̂)`: the connected component containing `α̂` of the shares `α ∈ [0, 1]` with
`y(α) = x*(α)`. -/
def found (αh : ℝ) : Set ℝ := connectedComponentIn (agreeSet f m β αh) αh

/-- The left end of `I(α̂)`. -/
noncomputable def loEnd (αh : ℝ) : ℝ := sInf (found f m β αh)

/-- The right end of `I(α̂)`. -/
noncomputable def hiEnd (αh : ℝ) : ℝ := sSup (found f m β αh)

end Defs

omit [DecidableEq E] in
lemma agree_self (αh : ℝ) : Agree f m β αh αh := by
  funext e
  simp [line]

omit [DecidableEq E] in
lemma line_continuous (αh : ℝ) : Continuous (line f m β αh) := by
  unfold line
  fun_prop

/-- The shares of `[0, 1]` with `y = x*` form a closed set, as `x*` is continuous on `[0, ∞)`
(`lem:pwaffine`). -/
lemma isClosed_agreeSet (H : Hyp f m β) (αh : ℝ) : IsClosed (agreeSet f m β αh) := by
  have hcont : ContinuousOn (fun α => bestResponse f m β α - line f m β αh α) (Set.Icc 0 1) :=
    ((pwaffine H).1.mono fun _ h => h.1).sub (line_continuous αh).continuousOn
  have h := hcont.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_singleton (x := 0))
  convert h using 1
  ext α
  simp only [agreeSet, Agree, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_singleton_iff, sub_eq_zero]

section Ends

variable {αh : ℝ}

omit [DecidableEq E] in
lemma mem_found (h0 : 0 ≤ αh) (h1 : αh ≤ 1) : αh ∈ found f m β αh :=
  mem_connectedComponentIn ⟨⟨h0, h1⟩, agree_self αh⟩

omit [DecidableEq E] in
lemma found_subset_agreeSet : found f m β αh ⊆ agreeSet f m β αh :=
  connectedComponentIn_subset _ _

omit [DecidableEq E] in
lemma found_subset : found f m β αh ⊆ Set.Icc 0 1 := fun _ h => (found_subset_agreeSet h).1

omit [DecidableEq E] in
/-- `x* = y` on `I(α̂)`. -/
theorem agree_on_found : ∀ α ∈ found f m β αh, Agree f m β αh α :=
  fun _ h => (found_subset_agreeSet h).2

/-- "It is a closed interval, possibly a singleton, by `lem:pwaffine`": `y = x*` on a closed set,
as `x*` is continuous (`isClosed_agreeSet`), so the connected component `I(α̂)` is closed, and it is
an interval. -/
theorem found_eq_Icc (H : Hyp f m β) (h0 : 0 ≤ αh) (h1 : αh ≤ 1) :
    found f m β αh = Icc (loEnd f m β αh) (hiEnd f m β αh) := by
  set C := found f m β αh
  have hαC : αh ∈ C := mem_found h0 h1
  have hpre : IsPreconnected C := isPreconnected_connectedComponentIn
  have hclosed : IsClosed C := by
    have : closure C ⊆ C := hpre.closure.subset_connectedComponentIn (subset_closure hαC)
      (closure_minimal found_subset_agreeSet (isClosed_agreeSet H αh))
    exact closure_subset_iff_isClosed.1 this
  have hbb : BddBelow C := ⟨0, fun x hx => (found_subset hx).1⟩
  have hba : BddAbove C := ⟨1, fun x hx => (found_subset hx).2⟩
  have hne : C.Nonempty := ⟨αh, hαC⟩
  ext x
  constructor
  · intro hx
    exact ⟨csInf_le hbb hx, le_csSup hba hx⟩
  · intro hx
    exact hpre.ordConnected.out (hclosed.csInf_mem hne hbb) (hclosed.csSup_mem hne hba) hx

omit [DecidableEq E] in
lemma loEnd_le (h0 : 0 ≤ αh) (h1 : αh ≤ 1) : loEnd f m β αh ≤ αh :=
  csInf_le ⟨0, fun _ hx => (found_subset hx).1⟩ (mem_found h0 h1)

omit [DecidableEq E] in
lemma le_hiEnd (h0 : 0 ≤ αh) (h1 : αh ≤ 1) : αh ≤ hiEnd f m β αh :=
  le_csSup ⟨1, fun _ hx => (found_subset hx).2⟩ (mem_found h0 h1)

omit [DecidableEq E] in
lemma zero_le_loEnd (h0 : 0 ≤ αh) (h1 : αh ≤ 1) : 0 ≤ loEnd f m β αh :=
  le_csInf ⟨αh, mem_found h0 h1⟩ fun _ hx => (found_subset hx).1

omit [DecidableEq E] in
lemma hiEnd_le_one (h0 : 0 ≤ αh) (h1 : αh ≤ 1) : hiEnd f m β αh ≤ 1 :=
  csSup_le ⟨αh, mem_found h0 h1⟩ fun _ hx => (found_subset hx).2

omit [DecidableEq E] in
/-- An interval `[a, b] ⊆ [0, 1]` around `α̂` on which `x* = y` lies in the component `I(α̂)`. -/
theorem subset_found {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (haα : a ≤ αh) (hαb : αh ≤ b)
    (hag : ∀ α ∈ Icc a b, Agree f m β αh α) : Icc a b ⊆ found f m β αh :=
  isPreconnected_Icc.subset_connectedComponentIn ⟨haα, hαb⟩
    fun α hα => ⟨⟨ha.trans hα.1, hα.2.trans hb⟩, hag α hα⟩

end Ends

/-! ### Step (1): the test by `prop:optchar` -/

/-- Step (1) of the proof of `lem:continuation`: "By `prop:optchar`, `y = x*` exactly where `y` is
feasible, `ρ̃ ≥ 0`, and every positive level set of `ρ̃` is tight", with
`ρ̃_e(α) = α m_e − β_e y_e(α)` (`optchar`, and the uniqueness of `x*(α)`). -/
theorem agree_iff (H : Hyp f m β) {αh α : ℝ} (hα : 0 ≤ α) :
    Agree f m β αh α ↔ line f m β αh α ∈ indepPoly f ∧
      (∀ e, 0 ≤ marg m β α (line f m β αh α) e) ∧
      ∀ θ > 0, IsTight f (line f m β αh α) (levelSet m β α (line f m β αh α) θ) := by
  constructor
  · -- `y(α) = x*(α)` is feasible, and `prop:optchar` gives `ρ̃ ≥ 0` and the tight level sets
    intro h
    have hbr := isBestResponse_bestResponse H.rank m β α
    rw [Agree] at h
    rw [← h]
    exact ⟨hbr.1, (optchar H.rank H.beta H.reward hα hbr.1).1.1 hbr⟩
  · -- by `prop:optchar`, a feasible `y(α)` with these properties is the best response
    rintro ⟨hy, hρ, ht⟩
    exact (((optchar H.rank H.beta H.reward hα hy).1.2 ⟨hρ, ht⟩).eq_bestResponse H.beta
      H.rank).symm

/-! ### The procedure of the proof of `lem:continuation`

Given `α̂`, `x̂` and `v = v(α̂)`, the proof computes `I(α̂)` as follows (steps (2) to (6)); the
definitions take `x̂` and `v` as arguments `x` and `v`.

2. "Feasibility along `y` is an interval: coordinate nonnegativity gives ratio bounds, and the
   rank constraints are handled by ray computations from `x̂` in the directions `v` and `−v`. The
   discrete Newton method for arbitrary directions uses `n² + O(n log² n)` minimizations and
   `O(n²)` evaluations of `f` per ray [GGJ17]." The ratio bounds are `ratioLo` and `ratioHi`; the
   ray computation is `rayMax`, the result `d ∈ [0, ∞]` of the ray computation of [GGJ17], cited;
   the rank constraints bound the shares by `α̂ + d⁺` and `α̂ − d⁻` (`rankHi`, `rankLo`).
3. "Intersect the feasible interval with `[0, 1]` and the inequalities `ρ̃_e ≥ 0`, obtaining a
   closed interval `K ∋ α̂`." The inequalities `ρ̃_e ≥ 0` are again ratio bounds, and
   `K = [κ⁻, κ⁺]` (`kLo`, `kHi`).
4. `K` is cut at `α̂` and at the crossings of distinct affine functions `ρ̃_e`, `ρ̃_g` (`cuts`); a
   cell is an open interval `(p, next p)` between consecutive cut points.
5. At the midpoint `c` of a cell, the tests `y(c)(L_i) = f(L_i)` and `v(L_i) = 0` for the chain
   `L_1 ⊊ ⋯ ⊊ L_q` of positive level sets of `ρ̃(c)` (`chainSet`, `Test`).
6. From `α̂`, the consecutive cells on either side that pass the tests are retained (`hi`, `lo`: the
   first cut point on either side that is an end of `K` or whose next cell fails the tests;
   `retained`: the left ends `p` of the retained cells `(p, next p)`).
-/

namespace Cont

section Procedure

variable (f m β) (αh : ℝ) (x v : E → ℝ)

/-- `y(α) = x̂ + (α − α̂) v`. -/
def y (α : ℝ) : E → ℝ := fun e => x e + (α - αh) * v e

/-- `ρ̃_e(α) = α m_e − β_e y_e(α)`. -/
def rhoT (α : ℝ) (e : E) : ℝ := α * m e - β e * y αh x v α e

/-- The feasible steps of the ray from `x` in the direction `w`: the `d ≥ 0` for which `x + d w`
satisfies the rank constraints `x(S) ≤ f(S)`. -/
def raySteps (w : E → ℝ) : Set ℝ :=
  {d | 0 ≤ d ∧ ∀ S : Finset E, ∑ e ∈ S, (x e + d * w e) ≤ f S}

/-- The ray computation from `x` in the direction `w` (step (2)), cited from [GGJ17] and not
formalised: its result, the largest feasible step `d ∈ [0, ∞]`, which is `∞` (`⊤`) if every step
`d ≥ 0` is feasible. It is defined here as this largest step, the supremum of `raySteps` in
`WithTop ℝ`. -/
noncomputable def rayMax (w : E → ℝ) : WithTop ℝ := sSup ((↑) '' raySteps f x w)

/-- The bound `α̂ − d⁻` from below of the rank constraints along `y`, from the ray computation in
the direction `−v` (and `0`, the bound of `[0, 1]`, if `d⁻ = ∞`, as for `ratioLo`). -/
noncomputable def rankLo : ℝ :=
  if h : rayMax f x (-v) = ⊤ then 0 else αh - (rayMax f x (-v)).untop h

/-- The bound `α̂ + d⁺` from above of the rank constraints along `y`, from the ray computation in
the direction `v` (and `1`, the bound of `[0, 1]`, if `d⁺ = ∞`, as for `ratioHi`). -/
noncomputable def rankHi : ℝ :=
  if h : rayMax f x v = ⊤ then 1 else αh + (rayMax f x v).untop h

/-- The ratio bound from below of `c + (α − α̂) d ≥ 0`: `α ≥ α̂ − c/d` if `d > 0` (and `0`, the
bound of `[0, 1]`, otherwise). -/
noncomputable def ratioLo (c d : ℝ) : ℝ := if 0 < d then αh - c / d else 0

/-- The ratio bound from above of `c + (α − α̂) d ≥ 0`: `α ≤ α̂ − c/d` if `d < 0` (and `1`, the
bound of `[0, 1]`, otherwise). -/
noncomputable def ratioHi (c d : ℝ) : ℝ := if d < 0 then αh - c / d else 1

/-- The lower end `κ⁻` of `K`: the largest of `0`, `α̂ − d⁻` (the ray computation in the direction
`−v`, `rankLo`) and the ratio bounds of `y_e ≥ 0` and `ρ̃_e ≥ 0`. -/
noncomputable def kLo : ℝ :=
  (insert (0 : ℝ) (insert (rankLo f αh x v) ((Finset.univ : Finset E).image fun e =>
    max (ratioLo αh (x e) (v e)) (ratioLo αh (αh * m e - β e * x e) (m e - β e * v e))))).max'
    (Finset.insert_nonempty _ _)

/-- The upper end `κ⁺` of `K`: the smallest of `1`, `α̂ + d⁺` (the ray computation in the direction
`v`, `rankHi`) and the ratio bounds of `y_e ≥ 0` and `ρ̃_e ≥ 0`. -/
noncomputable def kHi : ℝ :=
  (insert (1 : ℝ) (insert (rankHi f αh x v) ((Finset.univ : Finset E).image fun e =>
    min (ratioHi αh (x e) (v e)) (ratioHi αh (αh * m e - β e * x e) (m e - β e * v e))))).min'
    (Finset.insert_nonempty _ _)

/-- The crossing of the affine functions `ρ̃_e` and `ρ̃_g`, for distinct slopes:
`ρ̃_e(α) − ρ̃_g(α) = (s_e − s_g)(α − crossing)` with the slopes `s_e = m_e − β_e v_e`. -/
noncomputable def crossing (e g : E) : ℝ :=
  αh - ((αh * m e - β e * x e) - (αh * m g - β g * x g)) /
    ((m e - β e * v e) - (m g - β g * v g))

/-- Step (4): the cut points of `K`, its ends, `α̂` and the crossings inside `K` of distinct affine
functions `ρ̃_e`, `ρ̃_g` (those with distinct slopes; distinct ones with equal slopes do not
cross). -/
noncomputable def cuts : Finset ℝ :=
  insert (kLo f m β αh x v) (insert (kHi f m β αh x v) (insert αh
    ((((Finset.univ : Finset (E × E)).filter fun p =>
      m p.1 - β p.1 * v p.1 ≠ m p.2 - β p.2 * v p.2).image
        fun p => crossing m β αh x v p.1 p.2).filter
          fun c => kLo f m β αh x v < c ∧ c < kHi f m β αh x v)))

/-- The cut point after `p`; the cell after a cut point `p < κ⁺` is `(p, next p)`. -/
noncomputable def next (p : ℝ) : ℝ := sInf {q | q ∈ cuts f m β αh x v ∧ p < q}

/-- The cut point before `p`; the cell before a cut point `p > κ⁻` is `(prev p, p)`. -/
noncomputable def prev (p : ℝ) : ℝ := sSup {q | q ∈ cuts f m β αh x v ∧ q < p}

/-- Step (4): the positive level sets of `ρ̃(c)`, `L_i = {e | ρ̃_e(c) ≥ θ_i}` for the distinct
positive values `θ_0 > θ_1 > ⋯ > θ_{q−1}` of `ρ̃(c)` (`theta`, indices from 0, so the STOC version's
`L_1 ⊊ ⋯ ⊊ L_q` is `L_0 ⊊ ⋯ ⊊ L_{q−1}`). -/
noncomputable def chainSet (c : ℝ) (i : ℕ) : Finset E :=
  Finset.univ.filter fun e => theta (rhoT m β αh x v c) 0 i ≤ rhoT m β αh x v c e

/-- Step (5): the tests at the share `c`, `y(c)(L_i) = f(L_i)` and `v(L_i) = 0` for every set of
the chain of positive level sets of `ρ̃(c)`. -/
def Test (c : ℝ) : Prop :=
  ∀ i < numVals (rhoT m β αh x v c) 0,
    ∑ e ∈ chainSet m β αh x v c i, y αh x v c e = f (chainSet m β αh x v c i) ∧
      ∑ e ∈ chainSet m β αh x v c i, v e = 0

/-- Step (6), the walk to the right: the first cut point `p ≥ α̂` that is `κ⁺` or whose cell
`(p, next p)` fails the tests at its midpoint. The cells between `α̂` and `hi` are the retained
ones on the right. -/
noncomputable def hi : ℝ :=
  sInf {p | p ∈ cuts f m β αh x v ∧ αh ≤ p ∧
    (p = kHi f m β αh x v ∨ ¬ Test f m β αh x v ((p + next f m β αh x v p) / 2))}

/-- Step (6), the walk to the left: the first cut point `p ≤ α̂` that is `κ⁻` or whose cell
`(prev p, p)` fails the tests at its midpoint. -/
noncomputable def lo : ℝ :=
  sSup {p | p ∈ cuts f m β αh x v ∧ p ≤ αh ∧
    (p = kLo f m β αh x v ∨ ¬ Test f m β αh x v ((prev f m β αh x v p + p) / 2))}

/-- Step (6), the retained cells: the cells `(p, next p)` with `lo ≤ p < hi`, the consecutive cells
on either side of `α̂` that pass the tests (`retained_pass`). -/
noncomputable def retained : Finset ℝ :=
  (cuts f m β αh x v).filter fun p => lo f m β αh x v ≤ p ∧ p < hi f m β αh x v

end Procedure

/-! ### Steps (2) and (3): the closed interval `K` -/

section K

variable {αh : ℝ} {x v : E → ℝ}

omit [Fintype E] [DecidableEq E] in
/-- Step (2), the ray computation (not in the paper: the STOC version takes from the cited ray
computation of [GGJ17] that it returns the largest feasible step): from a point `x` that satisfies
the rank constraints, the feasible steps `d ≥ 0` of the ray in the direction `w` are those with
`d ≤ rayMax`, that is, they form `[0, d]` or `[0, ∞)`, as they form a closed set that contains `0`
and is convex (each constraint is affine in `d`). -/
theorem rayMax_spec {w : E → ℝ} (hx : ∀ S : Finset E, ∑ e ∈ S, x e ≤ f S) (d : ℝ) :
    d ∈ raySteps f x w ↔ 0 ≤ d ∧ (d : WithTop ℝ) ≤ rayMax f x w := by
  set R := raySteps f x w
  have hsplit : ∀ (S : Finset E) (c : ℝ),
      ∑ e ∈ S, (x e + c * w e) = ∑ e ∈ S, x e + c * ∑ e ∈ S, w e := by
    intro S c
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  have h0 : (0 : ℝ) ∈ R := ⟨le_rfl, fun S => by simpa using hx S⟩
  have hclosed : IsClosed R := by
    have hR : R = Set.Ici 0 ∩ ⋂ S : Finset E, {d | ∑ e ∈ S, x e + d * ∑ e ∈ S, w e ≤ f S} := by
      ext d
      simp only [R, raySteps, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Ici, Set.mem_iInter,
        hsplit]
    rw [hR]
    exact isClosed_Ici.inter (isClosed_iInter fun S => isClosed_le (by fun_prop) continuous_const)
  have hconv : R.OrdConnected := by
    constructor
    intro a ha b hb d hd
    refine ⟨ha.1.trans hd.1, fun S => ?_⟩
    have h1 := ha.2 S
    have h2 := hb.2 S
    rw [hsplit] at h1 h2 ⊢
    rcases le_total 0 (∑ e ∈ S, w e) with hw | hw
    · nlinarith [mul_le_mul_of_nonneg_right hd.2 hw]
    · nlinarith [mul_le_mul_of_nonpos_right hd.1 hw]
  by_cases hbdd : BddAbove R
  · -- bounded: the largest feasible step is attained, and the feasible steps are `[0, rayMax]`
    have hmax : rayMax f x w = ↑(sSup R) := (WithTop.coe_sSup' hbdd).symm
    rw [hmax, WithTop.coe_le_coe]
    constructor
    · intro hd
      exact ⟨hd.1, le_csSup hbdd hd⟩
    · rintro ⟨hd0, hd⟩
      exact hconv.out h0 (hclosed.csSup_mem ⟨0, h0⟩ hbdd) ⟨hd0, hd⟩
  · -- unbounded: every step `d ≥ 0` is feasible, and `rayMax = ∞`
    have hmax : rayMax f x w = ⊤ := by
      apply WithTop.sSup_of_not_bddAbove
      rwa [Set.preimage_image_eq _ WithTop.coe_injective]
    rw [hmax]
    constructor
    · intro hd
      exact ⟨hd.1, le_top⟩
    · rintro ⟨hd0, -⟩
      rw [not_bddAbove_iff] at hbdd
      obtain ⟨d', hd', hdd'⟩ := hbdd d
      exact hconv.out h0 hd' ⟨hd0, hdd'.le⟩

omit [Fintype E] [DecidableEq E] in
/-- Step (2): the rank constraints along `y` are the two ray computations from `x̂` in the
directions `v` and `−v`: for `α ∈ [0, 1]`, `y(α)` satisfies them exactly for
`α̂ − d⁻ ≤ α ≤ α̂ + d⁺` (`rankLo`, `rankHi`). -/
theorem rank_y_iff (hx : ∀ S : Finset E, ∑ e ∈ S, x e ≤ f S) {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    (∀ S : Finset E, ∑ e ∈ S, y αh x v α e ≤ f S) ↔
      rankLo f αh x v ≤ α ∧ α ≤ rankHi f αh x v := by
  -- the results of the two ray computations are at least `0`, as `x` is feasible
  have hpos : ∀ w : E → ℝ, ((0 : ℝ) : WithTop ℝ) ≤ rayMax f x w := fun w =>
    ((rayMax_spec hx 0).1 ⟨le_rfl, fun S => by simpa using hx S⟩).2
  -- the bounds `α̂ + d⁺` and `α̂ − d⁻`, as inequalities in `[0, ∞]`
  have hHi : α ≤ rankHi f αh x v ↔ ((α - αh : ℝ) : WithTop ℝ) ≤ rayMax f x v := by
    unfold rankHi
    split_ifs with h
    · rw [h]
      exact ⟨fun _ => le_top, fun _ => hα.2⟩
    · rw [← WithTop.le_untop_iff h]
      constructor <;> intro <;> linarith
  have hLo : rankLo f αh x v ≤ α ↔ ((αh - α : ℝ) : WithTop ℝ) ≤ rayMax f x (-v) := by
    unfold rankLo
    split_ifs with h
    · rw [h]
      exact ⟨fun _ => le_top, fun _ => hα.1⟩
    · rw [← WithTop.le_untop_iff h]
      constructor <;> intro <;> linarith
  rw [hLo, hHi]
  rcases le_total αh α with hle | hle
  · -- `α = α̂ + d` with `d ≥ 0`: the ray in the direction `v`; the other bound holds trivially
    have hy : ∀ S : Finset E, ∑ e ∈ S, y αh x v α e = ∑ e ∈ S, (x e + (α - αh) * v e) :=
      fun S => rfl
    simp only [hy]
    have key := rayMax_spec (w := v) hx (α - αh)
    have hother : ((αh - α : ℝ) : WithTop ℝ) ≤ rayMax f x (-v) :=
      (WithTop.coe_le_coe.2 (by linarith)).trans (hpos (-v))
    constructor
    · intro h
      exact ⟨hother, (key.1 ⟨sub_nonneg.2 hle, h⟩).2⟩
    · rintro ⟨-, h⟩
      exact (key.2 ⟨sub_nonneg.2 hle, h⟩).2
  · -- `α = α̂ − d` with `d ≥ 0`: the ray in the direction `−v`
    have hy : ∀ S : Finset E, ∑ e ∈ S, y αh x v α e = ∑ e ∈ S, (x e + (αh - α) * (-v) e) := by
      intro S
      refine Finset.sum_congr rfl fun e _ => ?_
      simp only [y, Pi.neg_apply]
      ring
    simp only [hy]
    have key := rayMax_spec (w := -v) hx (αh - α)
    have hother : ((α - αh : ℝ) : WithTop ℝ) ≤ rayMax f x v :=
      (WithTop.coe_le_coe.2 (by linarith)).trans (hpos v)
    constructor
    · intro h
      exact ⟨(key.1 ⟨sub_nonneg.2 hle, h⟩).2, hother⟩
    · rintro ⟨h, -⟩
      exact (key.2 ⟨sub_nonneg.2 hle, h⟩).2

/-- Step (2): the ratio bounds. For `c ≥ 0` and `α ∈ [0, 1]`, `c + (α − α̂) d ≥ 0` exactly when `α`
lies between the ratio bounds. -/
lemma ratio_iff {c d : ℝ} (hc : 0 ≤ c) {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ c + (α - αh) * d ↔ ratioLo αh c d ≤ α ∧ α ≤ ratioHi αh c d := by
  unfold ratioLo ratioHi
  rcases lt_trichotomy 0 d with hd | rfl | hd
  · rw [ite_eq_left hd, ite_eq_right (not_lt.2 hd.le)]
    constructor
    · intro h
      refine ⟨?_, hα.2⟩
      have : -c / d ≤ α - αh := by rw [div_le_iff₀ hd]; linarith
      rw [neg_div] at this
      linarith
    · rintro ⟨h, -⟩
      have : -c / d ≤ α - αh := by rw [neg_div]; linarith
      rw [div_le_iff₀ hd] at this
      linarith
  · simp only [lt_irrefl, ite_false, mul_zero, add_zero]
    exact ⟨fun _ => hα, fun _ => hc⟩
  · rw [ite_eq_right (not_lt.2 hd.le), ite_eq_left hd]
    constructor
    · intro h
      refine ⟨hα.1, ?_⟩
      have : α - αh ≤ -c / d := by rw [le_div_iff_of_neg hd]; linarith
      rw [neg_div] at this
      linarith
    · rintro ⟨-, h⟩
      have : α - αh ≤ -c / d := by rw [neg_div]; linarith
      rw [le_div_iff_of_neg hd] at this
      linarith

omit [Fintype E] [DecidableEq E] in
lemma rhoT_eq (α : ℝ) (e : E) :
    rhoT m β αh x v α e = (αh * m e - β e * x e) + (α - αh) * (m e - β e * v e) := by
  simp only [rhoT, y]
  ring

omit [DecidableEq E] in
/-- Step (3): "Intersect the feasible interval with `[0, 1]` and the inequalities `ρ̃_e ≥ 0`,
obtaining a closed interval `K ∋ α̂`.": `K = [κ⁻, κ⁺]` is the set of shares `α ∈ [0, 1]` at which
`y(α)` is feasible and `ρ̃(α) ≥ 0`, for a feasible `x` with `ρ̃(α̂) ≥ 0`. -/
theorem mem_K_iff (hx : x ∈ indepPoly f) (hρ : ∀ e, 0 ≤ αh * m e - β e * x e) {α : ℝ} :
    α ∈ Set.Icc (kLo f m β αh x v) (kHi f m β αh x v) ↔
      α ∈ Set.Icc 0 1 ∧ y αh x v α ∈ indepPoly f ∧ ∀ e, 0 ≤ rhoT m β αh x v α e := by
  simp only [Set.mem_Icc, kLo, kHi, Finset.max'_le_iff, Finset.le_min'_iff, Finset.mem_insert,
    Finset.mem_image, Finset.mem_univ, true_and, forall_eq_or_imp, forall_exists_index,
    forall_apply_eq_imp_iff, max_le_iff, le_min_iff]
  constructor
  · rintro ⟨⟨h0α, hlo, hlos⟩, h1α, hhi, his⟩
    have hα : α ∈ Set.Icc (0 : ℝ) 1 := ⟨h0α, h1α⟩
    refine ⟨⟨h0α, h1α⟩, ⟨fun e => ?_, (rank_y_iff hx.2 hα).2 ⟨hlo, hhi⟩⟩, fun e => ?_⟩
    · exact (ratio_iff (hx.1 e) hα).2 ⟨(hlos e).1, (his e).1⟩
    · rw [rhoT_eq]
      exact (ratio_iff (hρ e) hα).2 ⟨(hlos e).2, (his e).2⟩
  · rintro ⟨hα, hyP, hρα⟩
    have hrank := (rank_y_iff (v := v) hx.2 hα).1 hyP.2
    have hy : ∀ e, ratioLo αh (x e) (v e) ≤ α ∧ α ≤ ratioHi αh (x e) (v e) :=
      fun e => (ratio_iff (hx.1 e) hα).1 (hyP.1 e)
    have hr : ∀ e, ratioLo αh (αh * m e - β e * x e) (m e - β e * v e) ≤ α ∧
        α ≤ ratioHi αh (αh * m e - β e * x e) (m e - β e * v e) := fun e => by
      have := hρα e
      rw [rhoT_eq] at this
      exact (ratio_iff (hρ e) hα).1 this
    exact ⟨⟨hα.1, hrank.1, fun e => ⟨(hy e).1, (hr e).1⟩⟩, hα.2, hrank.2,
      fun e => ⟨(hy e).2, (hr e).2⟩⟩

end K

/-! ### Step (4): the cells and the fixed chain -/

section Cells

variable {αh : ℝ} {x v : E → ℝ}

omit [DecidableEq E] in
lemma kLo_mem_cuts : kLo f m β αh x v ∈ cuts f m β αh x v := Finset.mem_insert_self _ _

omit [DecidableEq E] in
lemma kHi_mem_cuts : kHi f m β αh x v ∈ cuts f m β αh x v :=
  Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

omit [DecidableEq E] in
lemma αh_mem_cuts : αh ∈ cuts f m β αh x v :=
  Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))

omit [DecidableEq E] in
/-- The cut points lie in `K`, when `α̂` does. -/
lemma mem_K_of_mem_cuts (hlo : kLo f m β αh x v ≤ αh) (hhi : αh ≤ kHi f m β αh x v) {p : ℝ}
    (hp : p ∈ cuts f m β αh x v) : kLo f m β αh x v ≤ p ∧ p ≤ kHi f m β αh x v := by
  simp only [cuts, Finset.mem_insert, Finset.mem_filter] at hp
  rcases hp with rfl | rfl | rfl | ⟨-, h1, h2⟩
  · exact ⟨le_rfl, hlo.trans hhi⟩
  · exact ⟨hlo.trans hhi, le_rfl⟩
  · exact ⟨hlo, hhi⟩
  · exact ⟨h1.le, h2.le⟩

omit [DecidableEq E] in
/-- A crossing inside `K` of `ρ̃_e`, `ρ̃_g` with distinct slopes is a cut point. -/
lemma crossing_mem_cuts {e g : E} (hs : m e - β e * v e ≠ m g - β g * v g)
    (h1 : kLo f m β αh x v < crossing m β αh x v e g)
    (h2 : crossing m β αh x v e g < kHi f m β αh x v) :
    crossing m β αh x v e g ∈ cuts f m β αh x v := by
  refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_))
  refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨(e, g), Finset.mem_filter.2
    ⟨Finset.mem_univ _, hs⟩, rfl⟩, h1, h2⟩

omit [DecidableEq E] in
/-- The cut point after `p`, if there is a cut point `r₀ > p`: it is a cut point, and no cut point
lies strictly between `p` and it. -/
lemma next_spec' {p r₀ : ℝ} (hr₀ : r₀ ∈ cuts f m β αh x v) (hpr : p < r₀) :
    next f m β αh x v p ∈ cuts f m β αh x v ∧ p < next f m β αh x v p ∧
      ∀ r ∈ cuts f m β αh x v, p < r → next f m β αh x v p ≤ r := by
  set S := {q | q ∈ cuts f m β αh x v ∧ p < q}
  have hne : S.Nonempty := ⟨r₀, hr₀, hpr⟩
  have hfin : S.Finite := (cuts f m β αh x v).finite_toSet.subset fun q hq => hq.1
  have hmem := hne.csInf_mem hfin
  exact ⟨hmem.1, hmem.2, fun r hr hpr => csInf_le ⟨p, fun q hq => hq.2.le⟩ ⟨hr, hpr⟩⟩

omit [DecidableEq E] in
/-- The cut point after a share `p < κ⁺`. -/
lemma next_spec {p : ℝ} (hlt : p < kHi f m β αh x v) :
    next f m β αh x v p ∈ cuts f m β αh x v ∧ p < next f m β αh x v p ∧
      ∀ r ∈ cuts f m β αh x v, p < r → next f m β αh x v p ≤ r :=
  next_spec' kHi_mem_cuts hlt

omit [DecidableEq E] in
/-- The cut point before `p`, if there is a cut point `r₀ < p`: it is a cut point, and no cut
point lies strictly between it and `p`. -/
lemma prev_spec' {p r₀ : ℝ} (hr₀ : r₀ ∈ cuts f m β αh x v) (hrp : r₀ < p) :
    prev f m β αh x v p ∈ cuts f m β αh x v ∧ prev f m β αh x v p < p ∧
      ∀ r ∈ cuts f m β αh x v, r < p → r ≤ prev f m β αh x v p := by
  set S := {q | q ∈ cuts f m β αh x v ∧ q < p}
  have hne : S.Nonempty := ⟨r₀, hr₀, hrp⟩
  have hfin : S.Finite := (cuts f m β αh x v).finite_toSet.subset fun q hq => hq.1
  have hmem := hne.csSup_mem hfin
  exact ⟨hmem.1, hmem.2, fun r hr hrp => le_csSup ⟨p, fun q hq => hq.2.le⟩ ⟨hr, hrp⟩⟩

omit [DecidableEq E] in
/-- The cut point before a share `p > κ⁻`. -/
lemma prev_spec {p : ℝ} (hlt : kLo f m β αh x v < p) :
    prev f m β αh x v p ∈ cuts f m β αh x v ∧ prev f m β αh x v p < p ∧
      ∀ r ∈ cuts f m β αh x v, r < p → r ≤ prev f m β αh x v p :=
  prev_spec' kLo_mem_cuts hlt

omit [Fintype E] [DecidableEq E] in
lemma rhoT_sub_eq_mul {e g : E} (hs : m e - β e * v e ≠ m g - β g * v g) (γ : ℝ) :
    rhoT m β αh x v γ e - rhoT m β αh x v γ g =
      ((m e - β e * v e) - (m g - β g * v g)) * (γ - crossing m β αh x v e g) := by
  rw [rhoT_eq, rhoT_eq]
  unfold crossing
  have hs' : (m e - β e * v e) - (m g - β g * v g) ≠ 0 := sub_ne_zero.2 hs
  field_simp
  ring

omit [DecidableEq E] in
/-- Step (4), the order: on a cell `(p, next p)` the order of the marginals `ρ̃_e` does not change,
as no crossing of distinct `ρ̃_e`, `ρ̃_g` lies inside a cell. -/
theorem cell_order (hlo : kLo f m β αh x v ≤ αh) (hhi : αh ≤ kHi f m β αh x v) {p : ℝ}
    (hp : p ∈ cuts f m β αh x v) (hpk : p < kHi f m β αh x v) {α α' : ℝ}
    (hα : α ∈ Set.Ioo p (next f m β αh x v p)) (hα' : α' ∈ Set.Ioo p (next f m β αh x v p))
    (e g : E) :
    rhoT m β αh x v α e ≤ rhoT m β αh x v α g ↔ rhoT m β αh x v α' e ≤ rhoT m β αh x v α' g := by
  obtain ⟨-, -, hnext⟩ := next_spec (f := f) (m := m) (β := β) (x := x) (v := v) hpk
  have hpK := mem_K_of_mem_cuts hlo hhi hp
  have hqK := mem_K_of_mem_cuts hlo hhi (next_spec (f := f) (m := m) (β := β) (x := x) (v := v)
    hpk).1
  by_cases hs : m e - β e * v e = m g - β g * v g
  · -- equal slopes: `ρ̃_e − ρ̃_g` is constant
    rw [rhoT_eq, rhoT_eq, rhoT_eq, rhoT_eq, hs]
    constructor <;> intro h <;> linarith
  · set c := crossing m β αh x v e g
    -- the crossing is not inside the cell
    have hc : c ≤ p ∨ next f m β αh x v p ≤ c := by
      by_contra hcon
      push Not at hcon
      have hcut := crossing_mem_cuts (f := f) hs (lt_of_le_of_lt hpK.1 hcon.1)
        (lt_of_lt_of_le hcon.2 hqK.2)
      exact absurd (hnext c hcut hcon.1) (not_le.2 hcon.2)
    have h1 := rhoT_sub_eq_mul (αh := αh) (x := x) hs α
    have h2 := rhoT_sub_eq_mul (αh := αh) (x := x) hs α'
    rw [← sub_nonpos, h1, ← sub_nonpos (a := rhoT m β αh x v α' e), h2]
    rcases hc with hc | hc
    · have ha : 0 < α - c := by linarith [hα.1]
      have ha' : 0 < α' - c := by linarith [hα'.1]
      constructor <;> intro h
      · have : (m e - β e * v e) - (m g - β g * v g) ≤ 0 := by
          by_contra hpos
          push Not at hpos
          have := mul_pos hpos ha
          linarith
        nlinarith
      · have : (m e - β e * v e) - (m g - β g * v g) ≤ 0 := by
          by_contra hpos
          push Not at hpos
          have := mul_pos hpos ha'
          linarith
        nlinarith
    · have ha : α - c < 0 := by linarith [hα.2]
      have ha' : α' - c < 0 := by linarith [hα'.2]
      constructor <;> intro h
      · have : (m e - β e * v e) - (m g - β g * v g) ≥ 0 := by
          by_contra hneg
          push Not at hneg
          have := mul_pos_of_neg_of_neg hneg ha
          linarith
        nlinarith
      · have : (m e - β e * v e) - (m g - β g * v g) ≥ 0 := by
          by_contra hneg
          push Not at hneg
          have := mul_pos_of_neg_of_neg hneg ha'
          linarith
        nlinarith

omit [DecidableEq E] in
/-- Step (4), the signs: on a cell, a marginal `ρ̃_e` is positive throughout or zero throughout:
"an affine function nonnegative on `K` cannot have an isolated zero in its interior". -/
theorem cell_pos (hK : ∀ α ∈ Set.Icc (kLo f m β αh x v) (kHi f m β αh x v),
      ∀ e, 0 ≤ rhoT m β αh x v α e)
    (hlo : kLo f m β αh x v ≤ αh) (hhi : αh ≤ kHi f m β αh x v) {p : ℝ}
    (hp : p ∈ cuts f m β αh x v) (hpk : p < kHi f m β αh x v) {α α' : ℝ}
    (hα : α ∈ Set.Ioo p (next f m β αh x v p)) (hα' : α' ∈ Set.Ioo p (next f m β αh x v p))
    (e : E) : 0 < rhoT m β αh x v α e ↔ 0 < rhoT m β αh x v α' e := by
  obtain ⟨hqc, -, -⟩ := next_spec (f := f) (m := m) (β := β) (x := x) (v := v) hpk
  have hpK := mem_K_of_mem_cuts hlo hhi hp
  have hqK := mem_K_of_mem_cuts hlo hhi hqc
  -- a zero at an interior share of `K` forces the slope, and so `ρ̃_e`, to vanish
  have key : ∀ γ ∈ Set.Ioo p (next f m β αh x v p), ∀ γ' ∈ Set.Ioo p (next f m β αh x v p),
      rhoT m β αh x v γ' e = 0 → rhoT m β αh x v γ e = 0 := by
    intro γ hγ γ' hγ' h0
    set δ := min (γ' - p) (next f m β αh x v p - γ')
    have hδ : 0 < δ := lt_min (by linarith [hγ'.1]) (by linarith [hγ'.2])
    have hδ1 := min_le_left (γ' - p) (next f m β αh x v p - γ')
    have hδ2 := min_le_right (γ' - p) (next f m β αh x v p - γ')
    have hp1 := hK (γ' + δ) ⟨by linarith [hpK.1, hγ'.1], by linarith [hqK.2]⟩ e
    have hp2 := hK (γ' - δ) ⟨by linarith [hpK.1], by linarith [hqK.2, hγ'.2]⟩ e
    rw [rhoT_eq] at hp1 hp2 h0 ⊢
    have hs : m e - β e * v e = 0 := by nlinarith
    rw [hs] at h0 ⊢
    linarith
  constructor
  · intro h
    by_contra h'
    have h0 : rhoT m β αh x v α' e = 0 :=
      le_antisymm (not_lt.1 h') (hK α' ⟨by linarith [hpK.1, hα'.1], by linarith [hqK.2, hα'.2]⟩ e)
    exact absurd (key α hα α' hα' h0) h.ne'
  · intro h
    by_contra h'
    have h0 : rhoT m β αh x v α e = 0 :=
      le_antisymm (not_lt.1 h') (hK α ⟨by linarith [hpK.1, hα.1], by linarith [hqK.2, hα.2]⟩ e)
    exact absurd (key α' hα' α hα h0) h.ne'

omit [Fintype E] [DecidableEq E] in
/-- The crossing of `ρ̃_e` and `ρ̃_g` is the crossing of `ρ̃_g` and `ρ̃_e`. -/
lemma crossing_comm (e g : E) : crossing m β αh x v e g = crossing m β αh x v g e := by
  unfold crossing
  rw [show (αh * m g - β g * x g) - (αh * m e - β e * x e) =
      -((αh * m e - β e * x e) - (αh * m g - β g * x g)) by ring,
    show (m g - β g * v g) - (m e - β e * v e) = -((m e - β e * v e) - (m g - β g * v g)) by ring,
    neg_div_neg_eq]

/-- Step (4), the count: `K` is cut at at most `C(n, 2) + 3` points, its two ends, `α̂` and one
crossing for each unordered pair `{e, g}`; so there are `O(n²)` cells (the explicit count is not in
the paper, which states `O(n²)` intervals without proof). -/
theorem card_cuts_le : (cuts f m β αh x v).card ≤ (Fintype.card E).choose 2 + 3 := by
  classical
  set X := ((Finset.univ : Finset (E × E)).filter fun p =>
    m p.1 - β p.1 * v p.1 ≠ m p.2 - β p.2 * v p.2).image fun p => crossing m β αh x v p.1 p.2
  have hX : X.card ≤ (Fintype.card E).choose 2 := by
    have hsub : X ⊆ ((Finset.univ : Finset E).offDiag.image (Function.uncurry Sym2.mk)).image
        (Sym2.lift ⟨fun e g => crossing m β αh x v e g, fun e g => crossing_comm e g⟩) := by
      intro c hc
      obtain ⟨⟨e, g⟩, hp, rfl⟩ := Finset.mem_image.1 hc
      have hne : e ≠ g := fun h => (Finset.mem_filter.1 hp).2 (by rw [h])
      exact Finset.mem_image.2 ⟨s(e, g), Finset.mem_image.2 ⟨(e, g), Finset.mem_offDiag.2
        ⟨Finset.mem_univ e, Finset.mem_univ g, hne⟩, rfl⟩, rfl⟩
    refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
    rw [Sym2.card_image_offDiag]
    simp
  have hfilt := Finset.card_filter_le X fun c => kLo f m β αh x v < c ∧ c < kHi f m β αh x v
  have h1 := Finset.card_insert_le αh
    (X.filter fun c => kLo f m β αh x v < c ∧ c < kHi f m β αh x v)
  have h2 := Finset.card_insert_le (kHi f m β αh x v) (insert αh (X.filter fun c =>
    kLo f m β αh x v < c ∧ c < kHi f m β αh x v))
  have h3 := Finset.card_insert_le (kLo f m β αh x v) (insert (kHi f m β αh x v) (insert αh
    (X.filter fun c => kLo f m β αh x v < c ∧ c < kHi f m β αh x v)))
  have hcuts : cuts f m β αh x v = insert (kLo f m β αh x v) (insert (kHi f m β αh x v)
      (insert αh (X.filter fun c => kLo f m β αh x v < c ∧ c < kHi f m β αh x v))) := rfl
  rw [hcuts]
  omega

omit [DecidableEq E] in
/-- Step (4), `q ≤ n`: a vector has at most `n` distinct positive values, so the chain of positive
level sets has at most `n` members. -/
lemma numVals_le_card (ρ : E → ℝ) : numVals ρ 0 ≤ Fintype.card E := by
  unfold numVals valsAbove
  exact (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans (by simp))

omit [Fintype E] [DecidableEq E] in
lemma marg_y (α : ℝ) (e : E) : marg m β α (y αh x v α) e = rhoT m β αh x v α e := rfl

omit [DecidableEq E] in
/-- Step (4) of the proof of `lem:continuation`: "On each of the `O(n²)` resulting open intervals
`J`, the positive level sets form a fixed chain `L_1 ⊊ ⋯ ⊊ L_q` with `q ≤ n`: an affine function
nonnegative on `K` cannot have an isolated zero in its interior." For the cell `J = (p, next p)`
with midpoint `c`: `q ≤ n` (`numVals_le_card`); the sets `L_i = chainSet c i`, `i < q`, increase
strictly; and at every share `α ∈ J`, every positive level set of `ρ̃(α)` is empty or one of the
`L_i`, and every `L_i` is one. The signs of the `ρ̃_e` are constant on `J` (`cell_pos`: no isolated
zero), and so is their order (`cell_order`: no crossing inside `J`). -/
theorem cell_chain (hK : ∀ α ∈ Set.Icc (kLo f m β αh x v) (kHi f m β αh x v),
      ∀ e, 0 ≤ rhoT m β αh x v α e)
    (hlo : kLo f m β αh x v ≤ αh) (hhi : αh ≤ kHi f m β αh x v) {p c : ℝ}
    (hp : p ∈ cuts f m β αh x v) (hpk : p < kHi f m β αh x v)
    (hc : c = (p + next f m β αh x v p) / 2) :
    numVals (rhoT m β αh x v c) 0 ≤ Fintype.card E ∧
    (∀ i j, i < j → j < numVals (rhoT m β αh x v c) 0 →
      chainSet m β αh x v c i ⊂ chainSet m β αh x v c j) ∧
    ∀ α ∈ Set.Ioo p (next f m β αh x v p),
      (∀ θ > 0, levelSet m β α (y αh x v α) θ = ∅ ∨
        ∃ i < numVals (rhoT m β αh x v c) 0,
          levelSet m β α (y αh x v α) θ = chainSet m β αh x v c i) ∧
      ∀ i < numVals (rhoT m β αh x v c) 0, ∃ θ > 0,
        levelSet m β α (y αh x v α) θ = chainSet m β αh x v c i := by
  obtain ⟨-, hpq, -⟩ := next_spec (f := f) (m := m) (β := β) (x := x) (v := v) hpk
  have hcJ : c ∈ Set.Ioo p (next f m β αh x v p) := by
    rw [hc]
    constructor <;> linarith
  -- the order and the signs of the `ρ̃_e` are those at `c` throughout `J`
  have hord : ∀ α ∈ Set.Ioo p (next f m β αh x v p), ∀ e g,
      rhoT m β αh x v c e ≤ rhoT m β αh x v c g ↔ rhoT m β αh x v α e ≤ rhoT m β αh x v α g :=
    fun α hα e g => cell_order hlo hhi hp hpk hcJ hα e g
  have hpos : ∀ α ∈ Set.Ioo p (next f m β αh x v p), ∀ e,
      0 < rhoT m β αh x v c e ↔ 0 < rhoT m β αh x v α e :=
    fun α hα e => cell_pos hK hlo hhi hp hpk hcJ hα e
  refine ⟨numVals_le_card _, fun i j hij hj => ?_, fun α hα => ⟨fun θ hθ => ?_, fun i hi => ?_⟩⟩
  · -- the chain increases strictly, as `θ_j < θ_i`
    have hθ : theta (rhoT m β αh x v c) 0 j < theta (rhoT m β αh x v c) 0 i :=
      theta_lt_theta hij hj.le
    refine Finset.ssubset_iff_subset_ne.2 ⟨fun e he => ?_, fun heq => ?_⟩
    · simp only [chainSet, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
      exact hθ.le.trans he
    · obtain ⟨g, -, hg⟩ := Finset.mem_image.1 (Finset.mem_filter.1 (theta_mem hj)).1
      have hgj : g ∈ chainSet m β αh x v c j := by
        simp only [chainSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hg.symm.le
      rw [← heq] at hgj
      simp only [chainSet, Finset.mem_filter, Finset.mem_univ, true_and] at hgj
      have : theta (rhoT m β αh x v c) 0 i ≤ theta (rhoT m β αh x v c) 0 j := hg ▸ hgj
      linarith
  · -- a positive level set of `ρ̃(α)` is empty or `L_j`, for the value `θ_j = ρ̃_g(c)` of its
    -- element `g` with the least marginal
    by_cases hne : (levelSet m β α (y αh x v α) θ).Nonempty
    · right
      obtain ⟨g, hgS, hmin⟩ := (levelSet m β α (y αh x v α) θ).exists_min_image
        (fun e => rhoT m β αh x v α e) hne
      have hgθ : θ ≤ rhoT m β αh x v α g := (Finset.mem_filter.1 hgS).2
      have hgc : 0 < rhoT m β αh x v c g := (hpos α hα g).2 (lt_of_lt_of_le hθ hgθ)
      obtain ⟨j, hj, hθj⟩ := exists_theta_eq hgc
      refine ⟨j, hj, ?_⟩
      ext e
      simp only [levelSet, chainSet, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [marg_y, hθj, hord α hα g e]
      constructor
      · intro he
        exact hmin e (Finset.mem_filter.2 ⟨Finset.mem_univ e, he⟩)
      · intro he
        exact hgθ.trans he
    · left
      exact Finset.not_nonempty_iff_eq_empty.1 hne
  · -- `L_i` is the level set of `ρ̃(α)` at the value `ρ̃_g(α) > 0` of an element `g` with
    -- `ρ̃_g(c) = θ_i`
    obtain ⟨g, -, hg⟩ := Finset.mem_image.1 (Finset.mem_filter.1 (theta_mem hi)).1
    have hgpos : 0 < rhoT m β αh x v α g := (hpos α hα g).1 (by rw [hg]; exact c_lt_theta hi)
    refine ⟨rhoT m β αh x v α g, hgpos, ?_⟩
    ext e
    simp only [levelSet, chainSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [marg_y, ← hg]
    exact (hord α hα g e).symm

omit [DecidableEq E] in
/-- Step (5) of the proof of `lem:continuation`: "For the midpoint `c` of `J`, tightness throughout
`J` is equivalent to `y(c)(L_i) = f(L_i)`, `v(L_i) = 0` (`i = 1, …, q`). If these tests fail,
tightness can hold at at most one point of `J`." Each test is an affine equation in the share:
`y(α)(L_i) = y(c)(L_i) + (α − c) v(L_i)`. -/
theorem cell_tests {p q c : ℝ} (hpq : p < q) (hc : c = (p + q) / 2) :
    ((∀ α ∈ Set.Ioo p q, ∀ i < numVals (rhoT m β αh x v c) 0,
        IsTight f (y αh x v α) (chainSet m β αh x v c i)) ↔ Test f m β αh x v c) ∧
    (¬ Test f m β αh x v c → ∀ α ∈ Set.Ioo p q, ∀ α' ∈ Set.Ioo p q,
      (∀ i < numVals (rhoT m β αh x v c) 0, IsTight f (y αh x v α) (chainSet m β αh x v c i)) →
      (∀ i < numVals (rhoT m β αh x v c) 0, IsTight f (y αh x v α') (chainSet m β αh x v c i)) →
        α = α') := by
  have hcJ : c ∈ Set.Ioo p q := by
    rw [hc]
    constructor <;> linarith
  have hc' : (c + q) / 2 ∈ Set.Ioo p q := by
    rw [hc]
    constructor <;> linarith
  -- `y(α)(L) = y(c)(L) + (α − c) v(L)`
  have hlin : ∀ (α : ℝ) (L : Finset E), ∑ e ∈ L, y αh x v α e =
      ∑ e ∈ L, y αh x v c e + (α - c) * ∑ e ∈ L, v e := by
    intro α L
    simp only [y, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun e _ => by ring
  refine ⟨⟨fun hall i hi => ?_, fun htest α _ i hi => ?_⟩, fun htest α hα α' hα' h h' => ?_⟩
  · -- tightness at `c` and at a second share of `J` gives both tests
    have e1 : ∑ e ∈ chainSet m β αh x v c i, y αh x v c e = f (chainSet m β αh x v c i) :=
      hall c hcJ i hi
    have e2 : ∑ e ∈ chainSet m β αh x v c i, y αh x v ((c + q) / 2) e =
        f (chainSet m β αh x v c i) := hall _ hc' i hi
    rw [hlin] at e2
    have hcq : (c + q) / 2 - c ≠ 0 := by
      have := hcJ.2
      intro h
      linarith
    have hV : ((c + q) / 2 - c) * ∑ e ∈ chainSet m β αh x v c i, v e = 0 := by linarith
    exact ⟨e1, (mul_eq_zero.1 hV).resolve_left hcq⟩
  · -- the tests give tightness at every share
    show ∑ e ∈ chainSet m β αh x v c i, y αh x v α e = f (chainSet m β αh x v c i)
    rw [hlin, (htest i hi).1, (htest i hi).2]
    ring
  · -- a failing test is an affine equation that holds at at most one share
    simp only [Test, not_forall, not_and_or] at htest
    obtain ⟨i, hi, hfail⟩ := htest
    have e1 : ∑ e ∈ chainSet m β αh x v c i, y αh x v α e = f (chainSet m β αh x v c i) := h i hi
    have e2 : ∑ e ∈ chainSet m β αh x v c i, y αh x v α' e = f (chainSet m β αh x v c i) :=
      h' i hi
    rw [hlin] at e1 e2
    by_contra hne
    have hV : ∑ e ∈ chainSet m β αh x v c i, v e = 0 := by
      have : (α - α') * ∑ e ∈ chainSet m β αh x v c i, v e = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
    rw [hV, mul_zero, add_zero] at e1
    rcases hfail with hf | hf
    · exact hf e1
    · exact hf hV

end Cells

/-! ### The costs of the procedure

The first sentence of `lem:continuation`, "`I(α̂)` can be computed with `O(n²)` submodular
minimizations, `O(n³)` further evaluations of `f`, and `O(n⁴)` further arithmetic operations", with
the costs as the proof accounts for them: "The ray computations and at most `n` set tests on each
of the `O(n²)` intervals give the stated costs". As `Stoc/BestResponse/WaterFilling.lean` counts the
work of water-filling, the procedure's work is counted in submodular minimizations (`contCalls`)
and further evaluations of `f` (`contEvals`); arithmetic operations are not counted. The ray
computation of [GGJ17] is cited and not formalised, so its work is a parameter (`RayCost`), with
the cited bounds as hypotheses. -/

/-- The work of the ray computation of [GGJ17] (cited, not formalised), a parameter of the counts:
`calls x w` submodular minimizations and `evals x w` further evaluations of `f` for the ray from
`x` in the direction `w`. The STOC version cites both bounds ("The discrete Newton method for
arbitrary directions uses `n² + O(n log² n)` minimizations and `O(n²)` evaluations of `f` per
ray [GGJ17]"); they enter the statements as hypotheses, as `calls x w ≤ N` and `evals x w ≤ N'`
(`contCalls_le`, `contEvals_le`), and in `lem:continuation` as `calls x w ≤ c n²` and
`evals x w ≤ c n²` (the cited bounds, with a common constant `c`) (`cont_costs_poly`). -/
structure RayCost (E : Type*) where
  /-- The submodular minimizations of the ray computation from `x` in the direction `w`. -/
  calls : (E → ℝ) → (E → ℝ) → ℕ
  /-- The further evaluations of `f` of the ray computation from `x` in the direction `w`. -/
  evals : (E → ℝ) → (E → ℝ) → ℕ

section Costs

variable (f m β) (αh : ℝ) (x v : E → ℝ)

/-- The number of submodular minimizations of the procedure: those of the two ray computations
from `x̂` in the directions `v` and `−v` (step (2)); the other steps make none. -/
def contCalls (R : RayCost E) : ℕ := R.calls x v + R.calls x (-v)

/-- The cells `(p, next p)` of step (4), by their left ends: the cut points `p < κ⁺`. -/
noncomputable def cells : Finset ℝ := (cuts f m β αh x v).filter fun p => p < kHi f m β αh x v

/-- The number of evaluations of `f` of the set tests on the cell `(p, next p)` (step (5)): one, of
`f(L_i)`, for each set `L_i` of the chain at the midpoint `c` (the test `y(c)(L_i) = f(L_i)`; the
test `v(L_i) = 0` needs none), `q` in all. -/
noncomputable def cellEvals (p : ℝ) : ℕ :=
  numVals (rhoT m β αh x v ((p + next f m β αh x v p) / 2)) 0

/-- The number of further evaluations of `f` of the procedure: those of the two ray computations
(step (2)) and those of the set tests on the cells (step (5), `cellEvals`). -/
noncomputable def contEvals (R : RayCost E) : ℕ :=
  R.evals x v + R.evals x (-v) + ∑ p ∈ cells f m β αh x v, cellEvals f m β αh x v p

variable {f m β αh x v}

/-- Step (4), the count of the cells, "the `O(n²)` resulting open intervals" (the explicit count is
not in the paper): at most `C(n, 2) + 2`, as there are at most `C(n, 2) + 3` cut points
(`card_cuts_le`) and no cell starts at `κ⁺`. -/
lemma card_cells_le : (cells f m β αh x v).card ≤ (Fintype.card E).choose 2 + 2 := by
  have hsub : cells f m β αh x v ⊆ (cuts f m β αh x v).erase (kHi f m β αh x v) :=
    fun p hp => Finset.mem_erase.2 ⟨(Finset.mem_filter.1 hp).2.ne, (Finset.mem_filter.1 hp).1⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem kHi_mem_cuts] at h1
  have h2 := card_cuts_le (f := f) (m := m) (β := β) (αh := αh) (x := x) (v := v)
  omega

omit [Fintype E] [DecidableEq E] in
/-- The submodular minimizations of the procedure: at most `2N` if each ray computation makes at
most `N` (`O(n²)` with the `N = n² + O(n log² n)` of [GGJ17]). -/
lemma contCalls_le (R : RayCost E) {N : ℕ} (hN : ∀ x w, R.calls x w ≤ N) :
    contCalls x v R ≤ 2 * N := by
  have h1 := hN x v
  have h2 := hN x (-v)
  unfold contCalls
  omega

/-- The further evaluations of `f` of the procedure: at most `2N' + n(C(n, 2) + 2)` if each ray
computation makes at most `N'`, by "at most `n` set tests on each of the `O(n²)` intervals": at
most `C(n, 2) + 2` cells (`card_cells_le`), each with `q ≤ n` set tests (`numVals_le_card`). -/
lemma contEvals_le (R : RayCost E) {N' : ℕ} (hN' : ∀ x w, R.evals x w ≤ N') :
    contEvals f m β αh x v R ≤ 2 * N' + Fintype.card E * ((Fintype.card E).choose 2 + 2) := by
  have htests : ∑ p ∈ cells f m β αh x v, cellEvals f m β αh x v p ≤
      Fintype.card E * ((Fintype.card E).choose 2 + 2) :=
    calc ∑ p ∈ cells f m β αh x v, cellEvals f m β αh x v p
        ≤ ∑ _p ∈ cells f m β αh x v, Fintype.card E :=
          Finset.sum_le_sum fun p _ => numVals_le_card _
      _ = (cells f m β αh x v).card * Fintype.card E := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ((Fintype.card E).choose 2 + 2) * Fintype.card E :=
          Nat.mul_le_mul_right _ card_cells_le
      _ = Fintype.card E * ((Fintype.card E).choose 2 + 2) := Nat.mul_comm _ _
  have h1 := hN' x v
  have h2 := hN' x (-v)
  unfold contEvals
  omega

/-- `n(C(n, 2) + 2) ≤ 2n³`: the explicit constant of the `O(n³)` evaluations of the tests (not in
the paper, which states `O(n³)`). -/
lemma tests_le_cube (n : ℕ) : n * (n.choose 2 + 2) ≤ 2 * n ^ 3 := by
  have hch : n.choose 2 ≤ n ^ 2 := Nat.choose_le_pow n 2
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp
  · nlinarith [Nat.mul_le_mul_left n hch]

/-- The costs of the procedure as polynomials, the `O(n²)` minimizations and `O(n³)` further
evaluations of `f` of `lem:continuation` with explicit constants (the constants are not in the
paper): if each ray computation makes at most `c n²` submodular minimizations and at most `c n²`
further evaluations of `f` (the cited `n² + O(n log² n)` and `O(n²)`), the procedure makes at most
`2c n²` minimizations (`contCalls_le`) and at most `(2c + 2) n³` further evaluations of `f`
(`contEvals_le`, `tests_le_cube`, and `n² ≤ n³`). -/
lemma cont_costs_poly (R : RayCost E) {c : ℕ}
    (hc : ∀ x w, R.calls x w ≤ c * Fintype.card E ^ 2 ∧ R.evals x w ≤ c * Fintype.card E ^ 2) :
    contCalls x v R ≤ 2 * c * Fintype.card E ^ 2 ∧
      contEvals f m β αh x v R ≤ (2 * c + 2) * Fintype.card E ^ 3 := by
  have h1 := contCalls_le (x := x) (v := v) R fun x w => (hc x w).1
  have h2 := contEvals_le (f := f) (m := m) (β := β) (αh := αh) (x := x) (v := v) R
    fun x w => (hc x w).2
  have h3 := tests_le_cube (Fintype.card E)
  have h4 : Fintype.card E ^ 2 ≤ Fintype.card E ^ 3 := by
    rcases Nat.eq_zero_or_pos (Fintype.card E) with h0 | h0
    · simp [h0]
    · exact Nat.pow_le_pow_right h0 (by norm_num)
  constructor
  · calc contCalls x v R ≤ 2 * (c * Fintype.card E ^ 2) := h1
      _ = 2 * c * Fintype.card E ^ 2 := by ring
  · calc contEvals f m β αh x v R
        ≤ 2 * (c * Fintype.card E ^ 2) + Fintype.card E * ((Fintype.card E).choose 2 + 2) := h2
      _ ≤ 2 * (c * Fintype.card E ^ 3) + 2 * Fintype.card E ^ 3 :=
          Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h4)) h3
      _ = (2 * c + 2) * Fintype.card E ^ 3 := by ring

end Costs

/-! ### Steps (5) and (6), for `x̂ = x*(α̂)` and `v = v(α̂)` -/

section Correct

variable {αh : ℝ}

omit [DecidableEq E] in
lemma y_eq_line (α : ℝ) :
    y αh (bestResponse f m β αh) (velocity f m β αh) α = line f m β αh α := rfl

/-- Step (3), for `x̂ = x*(α̂)` and `v(α̂)`: `K` is the set of shares of `[0, 1]` at which `y` is
feasible and `ρ̃ ≥ 0` (`mem_K_iff`), and it contains `α̂`, where `y = x*` and `ρ̃ = ρ ≥ 0`. -/
lemma K_facts (H : Hyp f m β) (h0 : 0 ≤ αh) (h1 : αh ≤ 1) :
    (∀ α, α ∈ Set.Icc (kLo f m β αh (bestResponse f m β αh) (velocity f m β αh))
        (kHi f m β αh (bestResponse f m β αh) (velocity f m β αh)) ↔
      α ∈ Set.Icc 0 1 ∧ line f m β αh α ∈ indepPoly f ∧
        ∀ e, 0 ≤ marg m β α (line f m β αh α) e) ∧
    αh ∈ Set.Icc (kLo f m β αh (bestResponse f m β αh) (velocity f m β αh))
      (kHi f m β αh (bestResponse f m β αh) (velocity f m β αh)) := by
  have hbr := isBestResponse_bestResponse H.rank m β αh
  have hρ : ∀ e, 0 ≤ αh * m e - β e * bestResponse f m β αh e :=
    fun e => hbr.marg_nonneg H.beta (fun e => mul_nonneg h0 (H.reward e)) e
  have hK : ∀ α, α ∈ Set.Icc (kLo f m β αh (bestResponse f m β αh) (velocity f m β αh))
      (kHi f m β αh (bestResponse f m β αh) (velocity f m β αh)) ↔
      α ∈ Set.Icc 0 1 ∧ line f m β αh α ∈ indepPoly f ∧
        ∀ e, 0 ≤ marg m β α (line f m β αh α) e :=
    fun α => mem_K_iff (f := f) hbr.1 hρ
  refine ⟨hK, (hK αh).2 ⟨⟨h0, h1⟩, ?_, fun e => ?_⟩⟩
  · rw [show line f m β αh αh = bestResponse f m β αh from (agree_self αh).symm]
    exact hbr.1
  · rw [show line f m β αh αh = bestResponse f m β αh from (agree_self αh).symm]
    exact hρ e

/-- Steps (1), (3) and (4) on a cell `J = (p, next p)` with midpoint `c`, for `x̂ = x*(α̂)` and
`v = v(α̂)`: `y = x*` at a share `α ∈ J` exactly when the sets `L_i` of the fixed chain are tight
for `y(α)`. By step (1), `y = x*` exactly where `y` is feasible, `ρ̃ ≥ 0` and every positive level
set of `ρ̃` is tight; the first two hold on `J ⊆ K` (step (3)), and the positive level sets are the
`L_i` (step (4)). -/
lemma agree_iff_chain (H : Hyp f m β) (h0 : 0 ≤ αh) (h1 : αh ≤ 1) {p c : ℝ}
    (hp : p ∈ cuts f m β αh (bestResponse f m β αh) (velocity f m β αh))
    (hpk : p < kHi f m β αh (bestResponse f m β αh) (velocity f m β αh))
    (hc : c = (p + next f m β αh (bestResponse f m β αh) (velocity f m β αh) p) / 2) {α : ℝ}
    (hα : α ∈ Set.Ioo p (next f m β αh (bestResponse f m β αh) (velocity f m β αh) p)) :
    Agree f m β αh α ↔
      ∀ i < numVals (rhoT m β αh (bestResponse f m β αh) (velocity f m β αh) c) 0,
        IsTight f (y αh (bestResponse f m β αh) (velocity f m β αh) α)
          (chainSet m β αh (bestResponse f m β αh) (velocity f m β αh) c i) := by
  obtain ⟨hK, hαK⟩ := K_facts H h0 h1
  obtain ⟨hqc, -, -⟩ := next_spec (f := f) (m := m) (β := β)
    (x := bestResponse f m β αh) (v := velocity f m β αh) hpk
  have hpK := mem_K_of_mem_cuts hαK.1 hαK.2 hp
  have hqK := mem_K_of_mem_cuts hαK.1 hαK.2 hqc
  have hρK : ∀ γ ∈ Set.Icc (kLo f m β αh (bestResponse f m β αh) (velocity f m β αh))
      (kHi f m β αh (bestResponse f m β αh) (velocity f m β αh)),
      ∀ e, 0 ≤ rhoT m β αh (bestResponse f m β αh) (velocity f m β αh) γ e :=
    fun γ hγ e => ((hK γ).1 hγ).2.2 e
  obtain ⟨-, -, hchain⟩ := cell_chain hρK hαK.1 hαK.2 hp hpk hc
  obtain ⟨hlev, hL⟩ := hchain α hα
  -- `y(α)` is feasible and `ρ̃(α) ≥ 0`, as `α ∈ K` (step (3))
  have hfeas := (hK α).1 ⟨hpK.1.trans hα.1.le, hα.2.le.trans hqK.2⟩
  -- (1) `y = x*` iff every positive level set of `ρ̃(α)` is tight; (4) these are the `L_i`
  rw [agree_iff H hfeas.1.1]
  constructor
  · rintro ⟨-, -, ht⟩ i hi
    obtain ⟨θ, hθ, hθL⟩ := hL i hi
    rw [← hθL]
    exact ht θ hθ
  · intro ht
    refine ⟨hfeas.2.1, hfeas.2.2, fun θ hθ => ?_⟩
    rcases hlev θ hθ with h | ⟨i, hi, h⟩
    · rw [← y_eq_line, h]
      simp [IsTight, H.rank.empty]
    · rw [← y_eq_line, h]
      exact ht i hi

/-- The walk to the right (step (6)): `hi` is a cut point in `[α̂, κ⁺]` that is `κ⁺` or whose next
cell fails the tests, and every cut point in `[α̂, hi)` has a next cell that passes them. -/
lemma hi_spec (H : Hyp f m β) (h0 : 0 ≤ αh) (h1 : αh ≤ 1) :
    let x := bestResponse f m β αh
    let v := velocity f m β αh
    hi f m β αh x v ∈ cuts f m β αh x v ∧ αh ≤ hi f m β αh x v ∧
      hi f m β αh x v ≤ kHi f m β αh x v ∧
      (hi f m β αh x v = kHi f m β αh x v ∨
        ¬ Test f m β αh x v ((hi f m β αh x v + next f m β αh x v (hi f m β αh x v)) / 2)) ∧
      ∀ p ∈ cuts f m β αh x v, αh ≤ p → p < hi f m β αh x v →
        p < kHi f m β αh x v ∧ Test f m β αh x v ((p + next f m β αh x v p) / 2) := by
  intro x v
  obtain ⟨-, hαK⟩ := K_facts H h0 h1
  set S := {p | p ∈ cuts f m β αh x v ∧ αh ≤ p ∧
    (p = kHi f m β αh x v ∨ ¬ Test f m β αh x v ((p + next f m β αh x v p) / 2))}
  have hne : S.Nonempty := ⟨_, kHi_mem_cuts, hαK.2, Or.inl rfl⟩
  have hfin : S.Finite := (cuts f m β αh x v).finite_toSet.subset fun q hq => hq.1
  have hmem : hi f m β αh x v ∈ S := hne.csInf_mem hfin
  have hbdd : BddBelow S := ⟨αh, fun q hq => hq.2.1⟩
  refine ⟨hmem.1, hmem.2.1, (mem_K_of_mem_cuts hαK.1 hαK.2 hmem.1).2, hmem.2.2,
    fun p hp hαp hph => ?_⟩
  have hnot : p ∉ S := fun hpS => absurd (csInf_le hbdd hpS) (not_le.2 hph)
  simp only [S, Set.mem_ofPred_eq, not_and, not_or, not_not] at hnot
  obtain ⟨hpk, htest⟩ := hnot hp hαp
  exact ⟨lt_of_le_of_ne (mem_K_of_mem_cuts hαK.1 hαK.2 hp).2 hpk, htest⟩

/-- The walk to the left (step (6)), symmetric to `hi_spec`. -/
lemma lo_spec (H : Hyp f m β) (h0 : 0 ≤ αh) (h1 : αh ≤ 1) :
    let x := bestResponse f m β αh
    let v := velocity f m β αh
    lo f m β αh x v ∈ cuts f m β αh x v ∧ lo f m β αh x v ≤ αh ∧
      kLo f m β αh x v ≤ lo f m β αh x v ∧
      (lo f m β αh x v = kLo f m β αh x v ∨
        ¬ Test f m β αh x v ((prev f m β αh x v (lo f m β αh x v) + lo f m β αh x v) / 2)) ∧
      ∀ p ∈ cuts f m β αh x v, p ≤ αh → lo f m β αh x v < p →
        kLo f m β αh x v < p ∧ Test f m β αh x v ((prev f m β αh x v p + p) / 2) := by
  intro x v
  obtain ⟨-, hαK⟩ := K_facts H h0 h1
  set S := {p | p ∈ cuts f m β αh x v ∧ p ≤ αh ∧
    (p = kLo f m β αh x v ∨ ¬ Test f m β αh x v ((prev f m β αh x v p + p) / 2))}
  have hne : S.Nonempty := ⟨_, kLo_mem_cuts, hαK.1, Or.inl rfl⟩
  have hfin : S.Finite := (cuts f m β αh x v).finite_toSet.subset fun q hq => hq.1
  have hmem : lo f m β αh x v ∈ S := hne.csSup_mem hfin
  have hbdd : BddAbove S := ⟨αh, fun q hq => hq.2.1⟩
  refine ⟨hmem.1, hmem.2.1, (mem_K_of_mem_cuts hαK.1 hαK.2 hmem.1).1, hmem.2.2,
    fun p hp hpα hlp => ?_⟩
  have hnot : p ∉ S := fun hpS => absurd (le_csSup hbdd hpS) (not_le.2 hlp)
  simp only [S, Set.mem_ofPred_eq, not_and, not_or, not_not] at hnot
  obtain ⟨hpk, htest⟩ := hnot hp hpα
  exact ⟨lt_of_le_of_ne (mem_K_of_mem_cuts hαK.1 hαK.2 hp).1 (Ne.symm hpk), htest⟩

omit [DecidableEq E] in
/-- The cell before a cut point `q > κ⁻` is the cell after its predecessor: `next (prev q) = q`. -/
lemma next_prev {x v : E → ℝ} {q : ℝ} (hq : q ∈ cuts f m β αh x v)
    (hqk : kLo f m β αh x v < q) : next f m β αh x v (prev f m β αh x v q) = q := by
  obtain ⟨hpc, hpq, hpmax⟩ := prev_spec (f := f) (m := m) (β := β) (x := x) (v := v) hqk
  obtain ⟨hnc, hpn, hnmin⟩ := next_spec' (f := f) (m := m) (β := β) (x := x) (v := v) hq hpq
  refine le_antisymm (hnmin q hq hpq) ?_
  by_contra hlt
  push Not at hlt
  exact absurd (hpmax _ hnc hlt) (not_le.2 hpn)

/-- Step (6): the retained cells pass the tests: a retained cut point `p` lies below `κ⁺`, and the
tests hold at the midpoint of its cell `(p, next p)` (on the right of `α̂` by `hi_spec`, on the left
by `lo_spec`). -/
lemma retained_pass (H : Hyp f m β) (h0 : 0 ≤ αh) (h1 : αh ≤ 1) {p : ℝ}
    (hp : p ∈ retained f m β αh (bestResponse f m β αh) (velocity f m β αh)) :
    p < kHi f m β αh (bestResponse f m β αh) (velocity f m β αh) ∧
      Test f m β αh (bestResponse f m β αh) (velocity f m β αh)
        ((p + next f m β αh (bestResponse f m β αh) (velocity f m β αh) p) / 2) := by
  obtain ⟨hpc, hlp, hph⟩ := Finset.mem_filter.1 hp
  obtain ⟨hic, hαi, hik, -, hipass⟩ := hi_spec H h0 h1
  obtain ⟨-, -, -, -, hlpass⟩ := lo_spec H h0 h1
  rcases le_or_gt αh p with hαp | hpα
  · exact hipass p hpc hαp hph
  · -- `p < α̂`: the cell `(p, next p)` is the cell before `q = next p ≤ α̂`
    have hpk : p < kHi f m β αh (bestResponse f m β αh) (velocity f m β αh) :=
      lt_of_lt_of_le hph hik
    obtain ⟨hqc, hpq, hqmin⟩ := next_spec (f := f) (m := m) (β := β)
      (x := bestResponse f m β αh) (v := velocity f m β αh) hpk
    have hqα := hqmin αh αh_mem_cuts hpα
    obtain ⟨hqk, htest⟩ := hlpass _ hqc hqα (lt_of_le_of_lt hlp hpq)
    -- `prev (next p) = p`
    have hprev : prev f m β αh (bestResponse f m β αh) (velocity f m β αh)
        (next f m β αh (bestResponse f m β αh) (velocity f m β αh) p) = p := by
      obtain ⟨hpc', hpq', hpmax⟩ := prev_spec (f := f) (m := m) (β := β)
        (x := bestResponse f m β αh) (v := velocity f m β αh) hqk
      refine le_antisymm ?_ (hpmax p hpc hpq)
      by_contra hlt
      push Not at hlt
      exact absurd (hqmin _ hpc' hlt) (not_le.2 hpq')
    rw [hprev] at htest
    exact ⟨hpk, htest⟩

omit [DecidableEq E] in
/-- Step (6), the shape of the union: the closures of the cells `(p, next p)` with `lo ≤ p < hi`,
together with `{α̂}`, make up the interval `[lo, hi]` (plumbing: consecutive cells). -/
lemma Icc_lo_hi_eq {x v : E → ℝ} (hlc : lo f m β αh x v ∈ cuts f m β αh x v)
    (hlα : lo f m β αh x v ≤ αh) (hkl : kLo f m β αh x v ≤ lo f m β αh x v)
    (hic : hi f m β αh x v ∈ cuts f m β αh x v)
    (hαi : αh ≤ hi f m β αh x v) (hik : hi f m β αh x v ≤ kHi f m β αh x v) :
    Set.Icc (lo f m β αh x v) (hi f m β αh x v) =
      insert αh (⋃ p ∈ retained f m β αh x v, closure (Set.Ioo p (next f m β αh x v p))) := by
  ext α
  simp only [Set.mem_insert_iff, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨hlα', hαi'⟩
    rcases lt_trichotomy α αh with hlt | heq | hgt
    · -- `α < α̂`: `α` lies in the closure of the cell `(p, q)` with `q = next α`, `p = prev q`
      right
      obtain ⟨hqc, hαq, hqmin⟩ := next_spec' (f := f) (m := m) (β := β) (x := x) (v := v)
        αh_mem_cuts hlt
      have hlq : lo f m β αh x v < next f m β αh x v α := lt_of_le_of_lt hlα' hαq
      obtain ⟨hpc, hpq, hpmax⟩ := prev_spec' (f := f) (m := m) (β := β) (x := x) (v := v)
        hlc hlq
      have hpα : prev f m β αh x v (next f m β αh x v α) ≤ α := by
        by_contra h
        push Not at h
        exact absurd (hqmin _ hpc h) (not_le.2 hpq)
      have hkq : kLo f m β αh x v < next f m β αh x v α := lt_of_le_of_lt hkl hlq
      refine ⟨prev f m β αh x v (next f m β αh x v α),
        Finset.mem_filter.2 ⟨hpc, hpmax _ hlc hlq, lt_of_lt_of_le hpq
          ((hqmin _ αh_mem_cuts hlt).trans hαi)⟩, ?_⟩
      rw [next_prev hqc hkq, closure_Ioo hpq.ne]
      exact ⟨hpα, hαq.le⟩
    · exact Or.inl heq
    · -- `α > α̂`: `α` lies in the closure of the cell `(p, next p)` with `p = prev α`
      right
      obtain ⟨hpc, hpα, hpmax⟩ := prev_spec' (f := f) (m := m) (β := β) (x := x) (v := v)
        αh_mem_cuts hgt
      have hpk : prev f m β αh x v α < kHi f m β αh x v :=
        lt_of_lt_of_le hpα (hαi'.trans hik)
      obtain ⟨hqc, hpq, -⟩ := next_spec (f := f) (m := m) (β := β) (x := x) (v := v) hpk
      have hαq : α ≤ next f m β αh x v (prev f m β αh x v α) := by
        by_contra h
        push Not at h
        exact absurd (hpmax _ hqc h) (not_le.2 hpq)
      refine ⟨prev f m β αh x v α, Finset.mem_filter.2 ⟨hpc,
        hlα.trans (hpmax αh αh_mem_cuts hgt), lt_of_lt_of_le hpα hαi'⟩, ?_⟩
      rw [closure_Ioo hpq.ne]
      exact ⟨hpα.le, hαq⟩
  · rintro (rfl | ⟨p, hp, hαp⟩)
    · exact ⟨hlα, hαi⟩
    · obtain ⟨hpc, hlp, hph⟩ := Finset.mem_filter.1 hp
      obtain ⟨hqc, hpq, hqmin⟩ := next_spec' (f := f) (m := m) (β := β) (x := x) (v := v)
        hic hph
      rw [closure_Ioo hpq.ne] at hαp
      exact ⟨hlp.trans hαp.1, hαp.2.trans (hqmin _ hic hph)⟩

/-- Step (6) of the proof of `lem:continuation`: "Starting at `α̂`, retain the consecutive intervals
on either side that pass the tests. By continuity, the union of their closures with `{α̂}` is
exactly `I(α̂)`, including when `K` is a singleton." The union is the interval `[lo, hi]`
(`Icc_lo_hi_eq`); `y = x*` on the retained cells (steps (1), (4) and (5)) and so, by continuity, on
their closures, and `I(α̂)` stops at a failing cell (at most one share of it agrees, step (5)) and
at the ends of `K` (step (3)). -/
theorem found_eq_walk (H : Hyp f m β) (h0 : 0 ≤ αh) (h1 : αh ≤ 1) :
    found f m β αh = insert αh (⋃ p ∈ retained f m β αh (bestResponse f m β αh)
        (velocity f m β αh), closure (Set.Ioo p
          (next f m β αh (bestResponse f m β αh) (velocity f m β αh) p))) ∧
      found f m β αh = Set.Icc (lo f m β αh (bestResponse f m β αh) (velocity f m β αh))
        (hi f m β αh (bestResponse f m β αh) (velocity f m β αh)) := by
  set x := bestResponse f m β αh
  set v := velocity f m β αh
  obtain ⟨hK, hαK⟩ := K_facts H h0 h1
  obtain ⟨hic, hαi, hik, hifail, -⟩ := hi_spec H h0 h1
  obtain ⟨hlc, hlα, hkl, hlfail, -⟩ := lo_spec H h0 h1
  have hcl := isClosed_agreeSet H αh
  have hI := found_eq_Icc H h0 h1
  have h0K : 0 ≤ kLo f m β αh x v := ((hK _).1 ⟨le_rfl, hαK.1.trans hαK.2⟩).1.1
  have h1K : kHi f m β αh x v ≤ 1 := ((hK _).1 ⟨hαK.1.trans hαK.2, le_rfl⟩).1.2
  have hwalk := Icc_lo_hi_eq (f := f) (m := m) (β := β) hlc hlα hkl hic hαi hik
  -- `I(α̂) ⊆ K`, by steps (1) and (3)
  have hfK : ∀ α ∈ found f m β αh, α ∈ Set.Icc (kLo f m β αh x v) (kHi f m β αh x v) := by
    intro α hα
    have h := found_subset_agreeSet hα
    have := (agree_iff H h.1.1).1 h.2
    exact (hK α).2 ⟨h.1, this.1, this.2.1⟩
  -- (6) "… retain the consecutive intervals on either side that pass the tests": `y = x*` on a
  -- retained cell (steps (1), (4) and (5)), and "by continuity" on its closure
  have hcell : ∀ p ∈ retained f m β αh x v,
      closure (Set.Ioo p (next f m β αh x v p)) ⊆ agreeSet f m β αh := by
    intro p hp
    obtain ⟨hpk, htest⟩ := retained_pass H h0 h1 hp
    have hpc : p ∈ cuts f m β αh x v := (Finset.mem_filter.1 hp).1
    obtain ⟨hqc, hpq, -⟩ := next_spec (f := f) (m := m) (β := β) (x := x) (v := v) hpk
    have hpK := mem_K_of_mem_cuts hαK.1 hαK.2 hpc
    have hqK := mem_K_of_mem_cuts hαK.1 hαK.2 hqc
    have htight := ((cell_tests (f := f) (m := m) (β := β) (αh := αh) (x := x) (v := v) hpq
      rfl).1.2 htest)
    refine closure_minimal (fun γ hγ => ⟨⟨h0K.trans (hpK.1.trans hγ.1.le),
      hγ.2.le.trans (hqK.2.trans h1K)⟩, ?_⟩) hcl
    exact (agree_iff_chain H h0 h1 hpc hpk rfl hγ).2 (htight γ hγ)
  -- (6) "… the union of their closures with `{α̂}` …" agrees, and it is the interval
  -- `[lo, hi] ∋ α̂`, so it lies in the component `I(α̂)`
  have hsub : Set.Icc (lo f m β αh x v) (hi f m β αh x v) ⊆ found f m β αh := by
    refine subset_found (h0K.trans hkl) (hik.trans h1K) hlα hαi fun α hα => ?_
    rw [hwalk] at hα
    rcases hα with rfl | hα
    · exact agree_self _
    · obtain ⟨p, hp, hαp⟩ := Set.mem_iUnion₂.1 hα
      exact (hcell p hp hαp).2
  -- (6) "… is exactly `I(α̂)` …": conversely, `I(α̂)` stops at a failing cell, where `y = x*` holds
  -- at at most one share (step (5)), or at an end of `K` (step (3))
  have hhiEnd : hiEnd f m β αh ≤ hi f m β αh x v := by
    by_contra hlt
    push Not at hlt
    have hEK : hiEnd f m β αh ∈ Set.Icc (kLo f m β αh x v) (kHi f m β αh x v) := by
      refine hfK _ ?_
      rw [hI]
      exact ⟨(loEnd_le h0 h1).trans (le_hiEnd h0 h1), le_rfl⟩
    have hik' : hi f m β αh x v < kHi f m β αh x v := lt_of_lt_of_le hlt hEK.2
    have hfail : ¬ Test f m β αh x v
        ((hi f m β αh x v + next f m β αh x v (hi f m β αh x v)) / 2) :=
      hifail.resolve_left hik'.ne
    obtain ⟨-, hiq, -⟩ := next_spec (f := f) (m := m) (β := β) (x := x) (v := v) hik'
    set q := next f m β αh x v (hi f m β αh x v)
    set δ := min (q - hi f m β αh x v) (hiEnd f m β αh - hi f m β αh x v) / 3
    have hδ : 0 < δ := by
      have := lt_min (sub_pos.2 hiq) (sub_pos.2 hlt)
      simp only [δ]
      linarith
    have hδ1 : 3 * δ ≤ q - hi f m β αh x v := by
      simp only [δ]
      linarith [min_le_left (q - hi f m β αh x v) (hiEnd f m β αh - hi f m β αh x v)]
    have hδ2 : 3 * δ ≤ hiEnd f m β αh - hi f m β αh x v := by
      simp only [δ]
      linarith [min_le_right (q - hi f m β αh x v) (hiEnd f m β αh - hi f m β αh x v)]
    have hmem : ∀ k : ℝ, 0 < k → k ≤ 2 → hi f m β αh x v + k * δ ∈ found f m β αh := by
      intro k hk0 hk2
      rw [hI]
      exact ⟨(loEnd_le h0 h1).trans (hαi.trans (by nlinarith)), by nlinarith⟩
    have hJ1 : hi f m β αh x v + 1 * δ ∈ Set.Ioo (hi f m β αh x v) q :=
      ⟨by nlinarith, by nlinarith⟩
    have hJ2 : hi f m β αh x v + 2 * δ ∈ Set.Ioo (hi f m β αh x v) q :=
      ⟨by nlinarith, by nlinarith⟩
    have heq := (cell_tests (f := f) (m := m) (β := β) (αh := αh) (x := x) (v := v) hiq rfl).2
      hfail _ hJ1 _ hJ2
      ((agree_iff_chain H h0 h1 hic hik' rfl hJ1).1 (agree_on_found _ (hmem 1 one_pos one_le_two)))
      ((agree_iff_chain H h0 h1 hic hik' rfl hJ2).1 (agree_on_found _ (hmem 2 two_pos le_rfl)))
    nlinarith
  have hloEnd : lo f m β αh x v ≤ loEnd f m β αh := by
    by_contra hlt
    push Not at hlt
    have hEK : loEnd f m β αh ∈ Set.Icc (kLo f m β αh x v) (kHi f m β αh x v) := by
      refine hfK _ ?_
      rw [hI]
      exact ⟨le_rfl, (loEnd_le h0 h1).trans (le_hiEnd h0 h1)⟩
    have hkl' : kLo f m β αh x v < lo f m β αh x v := lt_of_le_of_lt hEK.1 hlt
    have hfail : ¬ Test f m β αh x v
        ((prev f m β αh x v (lo f m β αh x v) + lo f m β αh x v) / 2) :=
      hlfail.resolve_left hkl'.ne'
    obtain ⟨hpc, hpl, -⟩ := prev_spec (f := f) (m := m) (β := β) (x := x) (v := v) hkl'
    set p := prev f m β αh x v (lo f m β αh x v)
    -- the cell before `lo` is the cell after `p`
    have hnp : next f m β αh x v p = lo f m β αh x v := next_prev hlc hkl'
    have hpk : p < kHi f m β αh x v :=
      lt_of_lt_of_le hpl (mem_K_of_mem_cuts hαK.1 hαK.2 hlc).2
    set δ := min (lo f m β αh x v - p) (lo f m β αh x v - loEnd f m β αh) / 3
    have hδ : 0 < δ := by
      have := lt_min (sub_pos.2 hpl) (sub_pos.2 hlt)
      simp only [δ]
      linarith
    have hδ1 : 3 * δ ≤ lo f m β αh x v - p := by
      simp only [δ]
      linarith [min_le_left (lo f m β αh x v - p) (lo f m β αh x v - loEnd f m β αh)]
    have hδ2 : 3 * δ ≤ lo f m β αh x v - loEnd f m β αh := by
      simp only [δ]
      linarith [min_le_right (lo f m β αh x v - p) (lo f m β αh x v - loEnd f m β αh)]
    have hmem : ∀ k : ℝ, 0 < k → k ≤ 2 → lo f m β αh x v - k * δ ∈ found f m β αh := by
      intro k hk0 hk2
      rw [hI]
      exact ⟨by nlinarith, (by nlinarith : lo f m β αh x v - k * δ ≤ αh).trans
        (le_hiEnd h0 h1)⟩
    have hfail' : ¬ Test f m β αh x v ((p + next f m β αh x v p) / 2) := by
      rw [hnp]
      exact hfail
    have hpq : p < next f m β αh x v p := by rw [hnp]; exact hpl
    have hJ1 : lo f m β αh x v - 1 * δ ∈ Set.Ioo p (next f m β αh x v p) :=
      ⟨by nlinarith, by rw [hnp]; nlinarith⟩
    have hJ2 : lo f m β αh x v - 2 * δ ∈ Set.Ioo p (next f m β αh x v p) :=
      ⟨by nlinarith, by rw [hnp]; nlinarith⟩
    have heq := (cell_tests (f := f) (m := m) (β := β) (αh := αh) (x := x) (v := v) hpq rfl).2
      hfail' _ hJ1 _ hJ2
      ((agree_iff_chain H h0 h1 hpc hpk rfl hJ1).1 (agree_on_found _ (hmem 1 one_pos one_le_two)))
      ((agree_iff_chain H h0 h1 hpc hpk rfl hJ2).1 (agree_on_found _ (hmem 2 two_pos le_rfl)))
    nlinarith
  have heq : found f m β αh = Set.Icc (lo f m β αh x v) (hi f m β αh x v) := by
    refine Set.Subset.antisymm ?_ hsub
    rw [hI]
    exact fun α hα => ⟨hloEnd.trans hα.1, hα.2.trans hhiEnd⟩
  exact ⟨heq.trans hwalk, heq⟩

end Correct

end Cont

/-! ### Steps (7) and (8), and `lem:continuation` -/

section Piece

variable {αh : ℝ}

omit [DecidableEq E] in
/-- If `x*` is affine on a set `I` and agrees with `y` at two distinct shares of `I`, it agrees with
`y` on all of `I` (not in the paper: the STOC version uses without proof, in step (7), that the
affine response near an end of `I(α̂)`, which agrees with `y` on the part of `I(α̂)` near that end,
agrees with `y` on a whole interval around it, as two affine maps that agree at two shares are
equal). -/
lemma agree_of_two {I : Set ℝ} {A W : E → ℝ}
    (hI : ∀ α ∈ I, bestResponse f m β α = fun e => A e + α * W e) {α₁ α₂ : ℝ} (h1 : α₁ ∈ I)
    (h2 : α₂ ∈ I) (hne : α₁ ≠ α₂) (ha1 : Agree f m β αh α₁) (ha2 : Agree f m β αh α₂) :
    ∀ α ∈ I, Agree f m β αh α := by
  intro α hα
  have hsub : α₁ - α₂ ≠ 0 := sub_ne_zero.2 hne
  unfold Agree line at *
  rw [hI α₁ h1] at ha1
  rw [hI α₂ h2] at ha2
  rw [hI α hα]
  funext e
  have e1 := congrFun ha1 e
  have e2 := congrFun ha2 e
  have hW : W e = velocity f m β αh e := by
    have : (α₁ - α₂) * (W e - velocity f m β αh e) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hsub
    · linarith
  rw [hW] at e1 ⊢
  linarith

/-- No breakpoint lies inside `I(α̂)` (not in the paper: the STOC version leaves implicit, in "Thus
`I(α̂)` is a piece", that `x* = y` is affine on `I(α̂)`, so that its interior has no breakpoint). -/
lemma not_mem_BP_of_mem_Ioo (H : Hyp f m β) (h0 : 0 ≤ αh) (h1 : αh ≤ 1) {α : ℝ}
    (hα : α ∈ Ioo (loEnd f m β αh) (hiEnd f m β αh)) : α ∉ BP f m β := by
  intro hbp
  apply hbp.2
  have hI := found_eq_Icc H h0 h1
  have h1' := min_le_left (α - loEnd f m β αh) (hiEnd f m β αh - α)
  have h2' := min_le_right (α - loEnd f m β αh) (hiEnd f m β αh - α)
  refine ⟨min (α - loEnd f m β αh) (hiEnd f m β αh - α),
    lt_min (by linarith [hα.1]) (by linarith [hα.2]),
    fun e => bestResponse f m β αh e - αh * velocity f m β αh e, velocity f m β αh,
    fun α' hα' => ?_⟩
  have hα'I : α' ∈ found f m β αh := by
    rw [hI]
    exact ⟨by linarith [hα'.1], by linarith [hα'.2]⟩
  rw [agree_on_found α' hα'I]
  funext e
  simp only [line]
  ring

/-- Step (7) of the proof of `lem:continuation`: "If `I(α̂)` is nondegenerate, any endpoint in
`(0, 1)` must be a breakpoint: otherwise the affine response there agrees with `y` on an interval
and extends the component, a contradiction. Thus `I(α̂)` is a piece." -/
theorem found_mem_pieces (H : Hyp f m β) (h0 : 0 ≤ αh) (h1 : αh ≤ 1)
    (hnd : (found f m β αh).Nontrivial) : found f m β αh ∈ pieces f m β := by
  have hI := found_eq_Icc H h0 h1
  set lo := loEnd f m β αh
  set hi := hiEnd f m β αh
  have hlt : lo < hi := by
    rw [hI] at hnd
    by_contra h
    push Not at h
    exact hnd.not_subsingleton (Set.subsingleton_Icc_of_ge h)
  have hag : ∀ γ ∈ Icc lo hi, Agree f m β αh γ := fun γ hγ => agree_on_found γ (hI ▸ hγ)
  -- (7) "any endpoint in `(0, 1)` must be a breakpoint": first the right end
  have hhi : hi = 1 ∨ hi ∈ BP f m β := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hne1, hnbp⟩ := hcon
    have hlt1 : hi < 1 := lt_of_le_of_ne (hiEnd_le_one h0 h1) hne1
    have hpos : 0 < hi := lt_of_le_of_lt (zero_le_loEnd h0 h1) hlt
    -- "otherwise the affine response there agrees with `y` on an interval": `x*` is affine on
    -- `(hi − ε, hi + ε)` and agrees with `y` at two shares of `I(α̂)` there
    obtain ⟨ε, hε, A, W, hAW⟩ : AffineNear (bestResponse f m β) hi := by
      by_contra h
      exact hnbp ⟨hpos, h⟩
    set η := min (ε / 2) (hi - lo)
    have hη : 0 < η := lt_min (by linarith) (by linarith)
    have hη1 : η ≤ ε / 2 := min_le_left _ _
    have hη2 : η ≤ hi - lo := min_le_right _ _
    have hall := agree_of_two hAW (α₁ := hi - η / 2) (α₂ := hi - η)
      ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
      (hag _ ⟨by linarith, by linarith⟩) (hag _ ⟨by linarith, by linarith⟩)
    -- "and extends the component, a contradiction": `[lo, s] ⊆ I(α̂)` with `s > hi`
    set s := min (hi + ε / 2) 1
    have hs : hi < s := lt_min (by linarith) hlt1
    have hsub := subset_found (f := f) (m := m) (β := β) (zero_le_loEnd h0 h1) (min_le_right _ _)
      (loEnd_le h0 h1) ((le_hiEnd h0 h1).trans hs.le) fun γ hγ => by
        rcases le_or_gt γ hi with h | h
        · exact hag γ ⟨hγ.1, h⟩
        · exact hall γ ⟨by linarith, lt_of_le_of_lt hγ.2
            (lt_of_le_of_lt (min_le_left _ _) (by linarith))⟩
    rw [hI] at hsub
    have := (hsub ⟨(loEnd_le h0 h1).trans ((le_hiEnd h0 h1).trans hs.le), le_rfl⟩).2
    linarith
  -- and the left end
  have hlo : lo = 0 ∨ lo ∈ BP f m β := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hne0, hnbp⟩ := hcon
    have hpos : 0 < lo := lt_of_le_of_ne (zero_le_loEnd h0 h1) (Ne.symm hne0)
    obtain ⟨ε, hε, A, W, hAW⟩ : AffineNear (bestResponse f m β) lo := by
      by_contra h
      exact hnbp ⟨hpos, h⟩
    set η := min (ε / 2) (hi - lo)
    have hη : 0 < η := lt_min (by linarith) (by linarith)
    have hη1 : η ≤ ε / 2 := min_le_left _ _
    have hη2 : η ≤ hi - lo := min_le_right _ _
    have hall := agree_of_two hAW (α₁ := lo + η / 2) (α₂ := lo + η)
      ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
      (hag _ ⟨by linarith, by linarith⟩) (hag _ ⟨by linarith, by linarith⟩)
    set s := max (lo - ε / 2) 0
    have hs : s < lo := max_lt (by linarith) hpos
    have hsub := subset_found (f := f) (m := m) (β := β) (le_max_right _ _) (hiEnd_le_one h0 h1)
      (hs.le.trans (loEnd_le h0 h1)) (le_hiEnd h0 h1) fun γ hγ => by
        rcases le_or_gt lo γ with h | h
        · exact hag γ ⟨h, hγ.2⟩
        · exact hall γ ⟨lt_of_lt_of_le (lt_of_lt_of_le (by linarith) (le_max_left _ _)) hγ.1,
            by linarith⟩
    rw [hI] at hsub
    have := (hsub ⟨le_rfl, hs.le.trans ((loEnd_le h0 h1).trans (le_hiEnd h0 h1))⟩).1
    linarith
  -- (7) "Thus `I(α̂)` is a piece" (`mem_pieces_iff`), as its interior has no breakpoint
  exact (mem_pieces_iff H).2 ⟨lo, hi, ⟨zero_le_loEnd h0 h1, hlt, hiEnd_le_one h0 h1,
    fun α hα => not_mem_BP_of_mem_Ioo H h0 h1 hα, hlo, hhi⟩, hI⟩

/-- Step (8) of the proof of `lem:continuation`: "At a non-event point, `lem:velocity` gives
`x* = y` on a neighborhood, proving the last claim": on an interval around `α̂` with constant
state, `x*(α) = x*(α̂) + (α − α̂) v(α̂) = y(α)` (`velocity_lemma`), so a neighborhood of `α̂` lies
in `I(α̂)`. -/
theorem mem_interior_found (H : Hyp f m β) (hα : αh ∈ Ioo (0 : ℝ) 1)
    (hne : ¬ IsEvent f m β αh) : αh ∈ interior (found f m β αh) := by
  rw [isEvent_iff] at hne
  push Not at hne
  obtain ⟨a, b, ha, hb, hS⟩ := hne hα.1
  set a' := max a 0
  set b' := min b 1
  have ha' : a' < αh := max_lt ha hα.1
  have hb' : αh < b' := lt_min hb hα.2
  have hsub : Ioo a' b' ⊆ Ioo a b := fun γ hγ =>
    ⟨lt_of_le_of_lt (le_max_left _ _) hγ.1, lt_of_lt_of_le hγ.2 (min_le_left _ _)⟩
  have hS' : ∀ γ ∈ Ioo a' b', ∀ γ' ∈ Ioo a' b', state f m β γ = state f m β γ' :=
    fun γ hγ γ' hγ' => hS γ (hsub hγ) γ' (hsub hγ')
  -- (8) "`lem:velocity` gives `x* = y` on a neighborhood": on `(a', b')`
  have hag : ∀ γ ∈ Ioo a' b', Agree f m β αh γ := fun γ hγ =>
    (velocity_lemma H (le_max_right a 0) hS' ⟨ha', hb'⟩).1 γ hγ
  -- so the neighborhood `(a'', b'')` of `α̂` lies in `I(α̂)`
  set a'' := (a' + αh) / 2
  set b'' := (αh + b') / 2
  have hsub := subset_found (f := f) (m := m) (β := β) (αh := αh) (a := a'') (b := b'')
    (by have := le_max_right a 0; simp only [a'']; linarith [hα.1])
    (by have := min_le_right b 1; simp only [b'']; linarith [hα.2])
    (by simp only [a'']; linarith) (by simp only [b'']; linarith)
    fun γ hγ => hag γ ⟨by simp only [a''] at hγ; linarith [hγ.1], by
      simp only [b''] at hγ; linarith [hγ.2]⟩
  exact mem_interior.2 ⟨Ioo a'' b'', Ioo_subset_Icc_self.trans hsub, isOpen_Ioo,
    ⟨by simp only [a'']; linarith, by simp only [b'']; linarith⟩⟩

end Piece

/-- **`lem:continuation`** (Lemma B.8, statement `stoc-sections/appB-quadratic.tex:412-418`, proof
:420-453), for `α̂ ∈ (0, 1)` (the paragraph "Affine continuation", :401-410), with `x̂ = x*(α̂)` and
`v = v(α̂)`:

1. given `x̂` and `v(α̂)`, `I(α̂)` is computed by the procedure of the proof: it is the union of the
   closures of the retained cells with `{α̂}`, which is the interval `[lo, hi]`; if each ray
   computation of [GGJ17] (cited, `RayCost`) makes at most `c n²` submodular minimizations and at
   most `c n²` further evaluations of `f` (the cited `n² + O(n log² n)` and `O(n²)`), the procedure
   makes at
   most `2c n²` submodular minimizations (`contCalls`) and at most `(2c + 2) n³` further
   evaluations of `f` (`contEvals`), the `O(n²)` and `O(n³)` of the STOC version with explicit
   constants; the `O(n⁴)` further arithmetic operations are not counted;
2. every nondegenerate `I(α̂)` is a piece;
3. if `α̂` is not an event point, it lies in the interior of `I(α̂)`.

Steps (1)-(6) of the proof: `agree_iff`, `ratio_iff`, `rayMax_spec`, `rank_y_iff`, `mem_K_iff`,
`cell_chain`, `cell_tests`, `found_eq_walk`, and for the costs `contCalls_le` and `contEvals_le`
(with `card_cells_le` and `numVals_le_card`) and their polynomial form `cont_costs_poly`; step (7):
`found_mem_pieces`; step (8): `mem_interior_found`. -/
theorem continuation (H : Hyp f m β) {αh : ℝ} (hα : αh ∈ Ioo (0 : ℝ) 1) :
    (found f m β αh = insert αh (⋃ p ∈ Cont.retained f m β αh (bestResponse f m β αh)
        (velocity f m β αh), closure (Ioo p
          (Cont.next f m β αh (bestResponse f m β αh) (velocity f m β αh) p))) ∧
      found f m β αh = Icc (Cont.lo f m β αh (bestResponse f m β αh) (velocity f m β αh))
        (Cont.hi f m β αh (bestResponse f m β αh) (velocity f m β αh)) ∧
      ∀ (R : Cont.RayCost E) (c : ℕ),
        (∀ x w, R.calls x w ≤ c * Fintype.card E ^ 2 ∧ R.evals x w ≤ c * Fintype.card E ^ 2) →
        Cont.contCalls (bestResponse f m β αh) (velocity f m β αh) R ≤
            2 * c * Fintype.card E ^ 2 ∧
          Cont.contEvals f m β αh (bestResponse f m β αh) (velocity f m β αh) R ≤
            (2 * c + 2) * Fintype.card E ^ 3) ∧
    ((found f m β αh).Nontrivial → found f m β αh ∈ pieces f m β) ∧
    (¬ IsEvent f m β αh → αh ∈ interior (found f m β αh)) := by
  -- (1)-(5) are the lemmas named in the docstring; `found_eq_walk` combines them with (6).
  -- (6) "Starting at `α̂`, retain the consecutive intervals on either side that pass the tests. By
  -- continuity, the union of their closures with `{α̂}` is exactly `I(α̂)`, including when `K` is
  -- a singleton." (`found_eq_walk`)
  obtain ⟨hw1, hw2⟩ := Cont.found_eq_walk H hα.1.le hα.2.le
  -- (6) "The ray computations and at most `n` set tests on each of the `O(n²)` intervals give the
  -- stated costs."
  -- Two ray computations (step (2), with the cited bounds per ray), and one evaluation of `f` for
  -- each of the at most `n` sets tested on each of the at most `C(n, 2) + 2` cells (steps (4) and
  -- (5)) (`contCalls_le`, `contEvals_le`, `cont_costs_poly`); the arithmetic operations are not
  -- formalised.
  refine ⟨⟨hw1, hw2, fun R c hc => Cont.cont_costs_poly R hc⟩, ?_, ?_⟩
  -- (7) "If `I(α̂)` is nondegenerate, any endpoint in `(0, 1)` must be a breakpoint: otherwise the
  -- affine response there agrees with `y` on an interval and extends the component, a
  -- contradiction. Thus `I(α̂)` is a piece."
  · exact found_mem_pieces H hα.1.le hα.2.le
  -- (8) "At a non-event point, `lem:velocity` gives `x* = y` on a neighborhood, proving the last
  -- claim."
  · exact mem_interior_found H hα

end Tracing

end Stoc
