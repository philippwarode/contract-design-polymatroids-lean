-- stamp r9 2026-11-03
import ContractDesignPolymatroids.Convex.Model
import ContractDesignPolymatroids.Preliminaries.CountedOracle

/-!
# Convex costs: computing `δ`-optimal responses (`lem:ellipsoid`)

The STOC version's `lem:ellipsoid` (`sec:F-ellipsoid`, `stoc-sections/appF-convex.tex`:117-139),
in the exact real-arithmetic model of `sec:convex` (08c-convex.tex:13, appF-convex.tex:121):
submodular minimizations, exact calls of the oracle for `c` at feasible real ellipsoid centers,
"exact separating cuts, subgradients, and objective values"; "its proof does not establish a
finite-precision implementation" (appF-convex.tex:139).

What is formalised, paragraph by paragraph of the proof (appF-convex.tex:127-137), which we number
(1) to (5):
* (1) "We first reduce to the case that `f({e}) > 0` for all `e`" (appF:128):
  `E' = {e : f({e}) > 0}` (`posElems`); `x_e = 0` on `P₊(f)` for `e ∉ E'`
  (`eq_zero_of_not_mem_posElems`); `f(S) = f(S ∩ E')`, from
  `f(S ∩ E') ≤ f(S) ≤ f(S ∩ E') + ∑_{e ∈ S ∖ E'} f({e})` (`rank_inter_posElems`, with the
  subadditivity `rank_union_le`); `P₊(f)` is `P₊(f|E')` padded with zeros (`indepPoly_eq_image_pad`,
  with the rank function `f|E'` of `restrictRank`, `isRankFunction_restrictRank`, and the padding
  `pad`), so "we may assume that `f({e}) > 0` for all `e ∈ E`": the reduced instance lies in the
  setting of `sec:convex` with the same `G` and `r̄` (`PolySetting.restrict`), its singletons have
  positive rank (`restrictRank_singleton_pos`), it has the same `f(E)` and at most `n` elements
  (`restrictRank_univ`, `card_posElems_le`), and its `δ`-optimal responses,
  padded with zeros, are those of the original instance (`isDeltaOpt_pad_iff`); if `E' = ∅`, then
  `P₊(f) = {0}` (`indepPoly_eq_zero`).
* (2) "Next we place `P₊(f)` between two cubes" (appF:130): in the coordinates `y_e = x_e/f({e})`
  (`scaledPoly`), `[0, 1/n]^E ⊆ K ⊆ [0, 1]^E` (`box_subset_scaledPoly`, `scaledPoly_subset_box`),
  so `K` contains the ball of radius `1/(2n)` about `(1/(2n)) 𝟙` (`ball_subset_scaledPoly`) and
  lies in the ball of radius `√n/2` about `(1/2) 𝟙` (`scaledPoly_subset_ball`), and the ratio of
  the radii is `n^{3/2}` (`radii_ratio`).
* (3) "A separation oracle needs one submodular minimization" (appF:132): at a center `y` in
  normalized coordinates, `z_e = f({e}) y_e`, and either `z_e < 0` for some `e`, or the minimizer
  `T` of `f(T) − z(T)` has `z(T) > f(T) ≥ x(T)` on `P₊(f)`, or `z ∈ P₊(f)` (`separation`); in
  normalized coordinates the violated inequality is `y_e ≥ 0` or `∑_{e ∈ T} f({e}) y_e ≤ f(T)`, and
  its normal gives the central cut through the center, a half-space through `y` that contains `K`
  (`separation_normalized`).
* (4) "Next we bound the objective" (appF:134): `c − α r` is convex on `P₊(f)` with the subgradient
  `g(x) − α m` (`convexOn_cost_sub`, `subgrad_cost_sub`); `0 ≤ c(x) ≤ G x(E) ≤ G f(E)` (`cost_le`,
  with `PolySetting.G_mul_le`), and `|U_A(· | α)| ≤ M = r̄ + G f(E)` on `P₊(f)` (`abs_util_le`).
* (5) "Finally, we apply the ellipsoid method" (appF:136): the subgradients in the coordinates `y`
  are scaled by `f({e})` (`subgrad_scaled`); `t = ⌈2n² ln(2n^{3/2} M/δ)⌉` (`ellipsoidIters`) "is
  positive and exceeds `2n² ln(n^{3/2})` since `δ < M`", and `n^{3/2} = R_out/R_in`
  (`ellipsoidIters_ge`); the bound `(2M R_out/R_in) exp(−t/(2n²))` is at most `δ`
  (`ellipsoid_bound_le`), which makes a point within this bound of the optimum `δ`-optimal; for
  `δ ≥ M` the response `0` is `δ`-optimal (`zero_isDeltaOpt`, with `G f(E) ≥ 0`,
  `PolySetting.G_mul_nonneg`). `ellipsoid` collects (1) and (5), and the counts.
* The counts: "at most `⌈2n² ln(2n^{3/2}(r̄ + G f(E))/δ)⌉` iterations, each of which makes at most
  one submodular minimization, at most one call of the oracle for `c`, and `O(n²)` further
  arithmetic operations" (appF:124), in the cost model of `Stoc.CountedQ`
  (`ContractDesignPolymatroids/Preliminaries/CountedOracle.lean`: submodular minimizations, evaluations of `f`,
  arithmetic operations with comparisons, and calls of the oracle for `c`). The counted method
  `ellipsoidC` performs (1) and (4) once (`prepC`: the `n + 1` evaluations of `f({e})` and `f(E)`),
  and in each iteration (`ellIterC`) the separation of (3) (`sepC`: its cuts are central cuts that
  contain `K`, `sepC_inl`, and it finds no cut exactly at the centers in `K`, `sepC_inr`,
  `sepC_of_mem`), at a center in `K` one call of the oracle for `c`, the value of the objective and
  its subgradient in the coordinates `y` (`objC`, `objC_subgrad`) and one comparison for the best
  center, and the update of the ellipsoid, with the paper's count `O(n²)` as a hypothesis
  (`EllMethod`, `EllMethod.Cited`). An iteration makes at most one minimization, one call of the
  oracle for `c`, one evaluation of `f` and `cE n² + 9n + 4` further arithmetic operations
  (`ellIterC_cost`); the method returns the best center `x_t` in `K`, padded with zeros, with its
  cost (`IsBestCenter`, `respC_spec`), with at most `t` minimizations and calls, `n + 1 + t`
  evaluations of `f` and `t (cE n² + 9n + 4) + cE n² + n + 4` further arithmetic operations
  (`ellipsoidC_spec`). Not in the paper: the paper counts in prose.

Not formalised: the central-cut ellipsoid method and the bound it attains (Bubeck, Thm. 2.4, which
the STOC version cites for a convex body in a ball of radius `R_out` that contains a ball of radius
`R_in`, and a continuous convex function with absolute values at most `M` on it: after
`t ≥ 2n² ln(R_out/R_in)` iterations, some center lies in the body, and the best such center is
within `(2M R_out/R_in) exp(−t/(2n²))` of the minimum), and bisection in dimension one. The method
enters the counts as a parameter (`EllMethod`: its ellipsoids, their centers and the update by a
central cut), with the paper's count `O(n²)` of an update as a hypothesis (appF:136; the paper's
count, not cited, and not proved here), and in `ellipsoid` the cited bound enters as a
hypothesis on the returned point. So the lemma's claim that the method computes a `δ`-optimal
response within `t` iterations is not proved here: what is proved is that a point satisfying the
cited bound for `t` iterations is `δ`-optimal, that `t` is positive and exceeds
`2n² ln(R_out/R_in)`, as the cited bound requires, and that the counted method, run for `t`
iterations with the cuts of (3) and the subgradients of (4) and (5), returns the best center in `K`
with the stated counts; with the cited bound for the run of the parameter as a hypothesis
(`EllConverges`), this point is a `δ`-optimal response (`ellipsoidC_isDeltaOpt`). The counted
method `respC` takes `t = ellipsoidIters n M δ` from its
definition at no cost: computing it needs `ln` and `⌈·⌉`, which are not operations of the model of
08c-convex.tex:13, and the paper does not count it. The lemmas of the paragraphs (2) and (4)
(`box_subset_scaledPoly`, `ball_subset_scaledPoly`, `scaledPoly_subset_ball`, `radii_ratio`,
`convexOn_cost_sub`, `cost_le`, `abs_util_le`) are not used by `ellipsoid`: they state the facts
on which the method is run. Those of (3) and of the subgradients (`separation`,
`separation_normalized`, `scaledPoly_subset_box`, `subgrad_cost_sub`, `subgrad_scaled`) are used by
the counted method.

The lemmas of (2) were taken over on 2026-10-20 from `Research/S14/Inner.lean` (series 14,
`lem:cvxround`) for the STOC version (`stoc.tex`); from then on this copy follows the STOC version.
-/

namespace Stoc.Convex

open Finset

variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ### (1) The reduction to `f({e}) > 0` -/

section Reduction

variable {f : Finset E → ℝ}

/-- `E' = {e ∈ E : f({e}) > 0}` (appF-convex.tex:128). -/
noncomputable def posElems (f : Finset E → ℝ) : Finset E := univ.filter fun e => 0 < f {e}

omit [Fintype E] in
/-- The subadditivity of a rank function over the elements of a set,
`f(A ∪ B) ≤ f(A) + ∑_{e ∈ B} f({e})` (not in the paper: (1) of the proof of `lem:ellipsoid`
uses it "by monotonicity and submodularity" without proof). -/
lemma rank_union_le (hf : IsRankFunction f) (A B : Finset E) :
    f (A ∪ B) ≤ f A + ∑ e ∈ B, f {e} := by
  induction B using Finset.induction_on with
  | empty => simp
  | insert b B hb ih =>
    rw [union_insert, sum_insert hb]
    have h := hf.submod {b} (A ∪ B)
    have h0 := hf.nonneg ({b} ∩ (A ∪ B))
    rw [← insert_eq] at h
    linarith

/-- (1) of the proof of `lem:ellipsoid` (appF-convex.tex:128): `f(S) = f(S ∩ E')` for all `S ⊆ E`,
"since `f(S ∩ E') ≤ f(S) ≤ f(S ∩ E') + ∑_{e ∈ S ∖ E'} f({e})` by monotonicity and submodularity",
and `f({e}) = 0` for `e ∉ E'`. -/
theorem rank_inter_posElems (hf : IsRankFunction f) (S : Finset E) :
    f S = f (S ∩ posElems f) := by
  have h1 : f (S ∩ posElems f) ≤ f S := hf.mono inter_subset_left
  have h2 : f S ≤ f (S ∩ posElems f) + ∑ e ∈ S \ posElems f, f {e} := by
    have := rank_union_le hf (S ∩ posElems f) (S \ posElems f)
    rwa [union_comm, sdiff_union_inter] at this
  have h3 : ∑ e ∈ S \ posElems f, f {e} = 0 := by
    refine sum_eq_zero fun e he => ?_
    have : ¬ 0 < f {e} := by simpa [posElems] using (mem_sdiff.1 he).2
    exact le_antisymm (not_lt.1 this) (hf.nonneg _)
  linarith

omit [DecidableEq E] in
/-- (1) of the proof of `lem:ellipsoid` (appF-convex.tex:128): "For `e ∉ E'`, every `x ∈ P₊(f)` has
`x_e = 0`." -/
lemma eq_zero_of_not_mem_posElems {x : E → ℝ} (hx : x ∈ indepPoly f) {e : E}
    (he : e ∉ posElems f) : x e = 0 := by
  have h1 : ¬ 0 < f {e} := by simpa [posElems] using he
  have h2 : x e ≤ f {e} := by simpa using hx.2 {e}
  exact le_antisymm (by linarith [not_lt.1 h1]) (hx.1 e)

/-- The restriction `f|E'` of `f` to the subsets of `E'` (appF-convex.tex:128). -/
def restrictRank (f : Finset E → ℝ) (T : Finset {e // e ∈ posElems f}) : ℝ :=
  f (T.map (Function.Embedding.subtype _))

/-- A vector on `E'`, padded with zeros. -/
noncomputable def pad (f : Finset E → ℝ) (y : {e // e ∈ posElems f} → ℝ) (e : E) : ℝ :=
  if he : e ∈ posElems f then y ⟨e, he⟩ else 0

/-- `f|E'` is a rank function (not in the paper: it uses this tacitly). -/
lemma isRankFunction_restrictRank (hf : IsRankFunction f) : IsRankFunction (restrictRank f) where
  empty := by simp [restrictRank, hf.empty]
  mono T T' hTT' := hf.mono (map_subset_map.2 hTT')
  submod T T' := by
    have := hf.submod (T.map (Function.Embedding.subtype _)) (T'.map (Function.Embedding.subtype _))
    simpa [restrictRank, map_union, map_inter] using this

omit [DecidableEq E] in
/-- The reduced instance has `f|E'({e}) > 0` for all `e ∈ E'`. -/
lemma restrictRank_singleton_pos (e : {e // e ∈ posElems f}) : 0 < restrictRank f {e} := by
  have := e.2
  simp only [posElems, mem_filter, mem_univ, true_and] at this
  simpa [restrictRank] using this

/-- (1) of the proof of `lem:ellipsoid` (appF-convex.tex:128): "So `P₊(f)` is `P₊(f|E')`, padded
with zeros." -/
theorem indepPoly_eq_image_pad (hf : IsRankFunction f) :
    indepPoly f = pad f '' indepPoly (restrictRank f) := by
  ext x
  constructor
  · intro hx
    refine ⟨fun e => x e, ⟨fun e => hx.1 e, fun T => ?_⟩, funext fun e => ?_⟩
    · have := hx.2 (T.map (Function.Embedding.subtype _))
      simpa [restrictRank, sum_map] using this
    · unfold pad
      split_ifs with he
      · rfl
      · exact (eq_zero_of_not_mem_posElems hx he).symm
  · rintro ⟨y, hy, rfl⟩
    refine ⟨fun e => ?_, fun S => ?_⟩
    · unfold pad
      split_ifs with he
      · exact hy.1 _
      · exact le_rfl
    · -- `∑_{e ∈ S} pad(y)_e = ∑_{e ∈ S ∩ E'} y_e ≤ f|E'(S ∩ E') = f(S ∩ E') = f(S)`
      have hsum : ∑ e ∈ S, pad f y e =
          ∑ e ∈ (S.subtype (· ∈ posElems f)).map (Function.Embedding.subtype _), pad f y e := by
        rw [subtype_map]
        refine (sum_filter_of_ne fun e _ hne => ?_).symm
        by_contra hnot
        exact hne (by simp [pad, hnot])
      rw [hsum, sum_map]
      have hle := hy.2 (S.subtype (· ∈ posElems f))
      have e1 : ∑ e ∈ S.subtype (· ∈ posElems f), pad f y ((Function.Embedding.subtype _) e) =
          ∑ e ∈ S.subtype (· ∈ posElems f), y e :=
        sum_congr rfl fun e _ => by simp [pad, e.2]
      rw [e1]
      refine hle.trans (le_of_eq ?_)
      rw [restrictRank, subtype_map, filter_mem_eq_inter, ← rank_inter_posElems hf]

/-- (1) of the proof of `lem:ellipsoid` (appF-convex.tex:128): "If `E' = ∅`, then `P₊(f) = {0}`." -/
theorem indepPoly_eq_zero (hf : IsRankFunction f) (hE : posElems f = ∅) :
    indepPoly f = {0} := by
  ext x
  refine ⟨fun hx => funext fun e => eq_zero_of_not_mem_posElems hx (by simp [hE]), ?_⟩
  rintro rfl
  exact zero_mem_indepPoly hf

/-- The reward on `E'`: `r(pad(y)) = ∑_{e ∈ E'} m_e y_e`. -/
lemma reward_pad (m : E → ℝ) (y : {e // e ∈ posElems f} → ℝ) :
    reward m (pad f y) = reward (fun e : {e // e ∈ posElems f} => m e.1) y := by
  unfold reward
  rw [← sum_subset (subset_univ (posElems f)) fun e _ he => by simp [pad, he],
    ← sum_coe_sort (posElems f)]
  exact sum_congr rfl fun e _ => by simp [pad, e.2]

/-- (1) of the proof of `lem:ellipsoid`, "we may assume that `f({e}) > 0` for all `e ∈ E`" (not in
the paper: it leaves this implicit): with the reward `m|E'` and the cost `c ∘ pad` on `E'`, a vector
`y` is a `δ`-optimal response of the reduced instance if and only if `pad(y)` is one of the original
instance. -/
theorem isDeltaOpt_pad_iff (hf : IsRankFunction f) (m : E → ℝ) (c : (E → ℝ) → ℝ) (α δ : ℝ)
    (y : {e // e ∈ posElems f} → ℝ) :
    IsDeltaOpt (indepPoly (restrictRank f)) (fun e : {e // e ∈ posElems f} => m e.1)
        (fun y => c (pad f y)) α δ y ↔ IsDeltaOpt (indepPoly f) m c α δ (pad f y) := by
  have hutil : ∀ z : {e // e ∈ posElems f} → ℝ,
      util (fun e : {e // e ∈ posElems f} => m e.1) (fun y => c (pad f y)) α z =
        util m c α (pad f z) :=
    fun z => by simp only [util, reward_pad]
  have hV : V (indepPoly (restrictRank f)) (fun e : {e // e ∈ posElems f} => m e.1)
      (fun y => c (pad f y)) α = V (indepPoly f) m c α := by
    unfold V
    rw [indepPoly_eq_image_pad hf, Set.image_image]
    exact congrArg sSup (Set.image_congr fun z _ => hutil z)
  have hinj : Function.Injective (pad f) := fun y y' hyy' => funext fun e => by
    have := congrFun hyy' e.1
    simpa [pad, e.2] using this
  have hmem : pad f y ∈ indepPoly f ↔ y ∈ indepPoly (restrictRank f) := by
    rw [indepPoly_eq_image_pad hf]
    exact hinj.mem_set_image
  unfold IsDeltaOpt
  rw [hV, hutil, hmem]

/-- Padding with zeros is linear: `pad(a y + b y') = a pad(y) + b pad(y')`. -/
lemma pad_add_smul (y y' : {e // e ∈ posElems f} → ℝ) (a b : ℝ) :
    pad f (a • y + b • y') = a • pad f y + b • pad f y' := by
  funext e
  by_cases he : e ∈ posElems f <;> simp [pad, he]

/-- A vector `y ≥ 0` on `E'`, padded with zeros, is `≥ 0`. -/
lemma pad_nonneg {y : {e // e ∈ posElems f} → ℝ} (hy : 0 ≤ y) : 0 ≤ pad f y := fun e => by
  unfold pad
  split_ifs
  · exact hy _
  · exact le_rfl

/-- `0` padded with zeros is `0`. -/
lemma pad_zero : pad f (0 : {e // e ∈ posElems f} → ℝ) = 0 := by
  funext e
  unfold pad
  split_ifs <;> rfl

/-- A point of `P₊(f|E')`, padded with zeros, lies in `P₊(f)` (`indepPoly_eq_image_pad`). -/
lemma pad_mem (hf : IsRankFunction f) {y : {e // e ∈ posElems f} → ℝ}
    (hy : y ∈ indepPoly (restrictRank f)) : pad f y ∈ indepPoly f := by
  rw [indepPoly_eq_image_pad hf]
  exact ⟨y, hy, rfl⟩

/-- (1) of the proof of `lem:ellipsoid`, "we may assume that `f({e}) > 0` for all `e ∈ E`" (not in
the paper: it leaves implicit that the reduced instance lies again in the setting of `sec:convex`):
with the rank function `f|E'`, the rewards `m|E'`, the cost `c ∘ pad` and the subgradients `g ∘ pad`
restricted to `E'`, and the same bounds `G` and `r̄` (the rewards of `P₊(f|E')` are those of
`P₊(f)` at the padded points, `reward_pad`). -/
theorem PolySetting.restrict {m : E → ℝ} {c : (E → ℝ) → ℝ} {g : (E → ℝ) → E → ℝ} {G rb : ℝ}
    (h : PolySetting f m c g G rb) :
    PolySetting (restrictRank f) (fun e : {e // e ∈ posElems f} => m e.1) (fun y => c (pad f y))
      (fun y e => g (pad f y) e.1) G rb where
  rank := isRankFunction_restrictRank h.rank
  m_nonneg e := h.m_nonneg e.1
  rbar_pos := h.rbar_pos
  reward_le y hy := by
    rw [← reward_pad]
    exact h.reward_le _ (pad_mem h.rank hy)
  cost := ⟨fun y hy => h.cost.nonneg _ (pad_nonneg hy), by rw [pad_zero]; exact h.cost.zero⟩
  convexOn := ⟨convex_indepPoly _, fun y hy y' hy' a b ha hb hab => by
    have := h.convexOn.2 (pad_mem h.rank hy) (pad_mem h.rank hy') ha hb hab
    simpa only [pad_add_smul] using this⟩
  subgrad y hy y' hy' := by
    have h1 := h.subgrad _ (pad_mem h.rank hy) _ (pad_mem h.rank hy')
    -- the terms of `e ∉ E'` vanish (`reward_pad`)
    have e1 : ∑ e, g (pad f y) e * (pad f y' e - pad f y e) =
        ∑ e : {e // e ∈ posElems f}, g (pad f y) e.1 * (y' e - y e) := by
      have := congrArg₂ (· - ·) (reward_pad (g (pad f y)) y') (reward_pad (g (pad f y)) y)
      simpa only [reward, ← Finset.sum_sub_distrib, ← mul_sub] using this
    rwa [e1] at h1
  bound y hy e := h.bound _ (pad_mem h.rank hy) e.1

/-- (1) of the proof of `lem:ellipsoid`: the reduced instance has the same `f(E)`,
`f|E'(E') = f(E') = f(E)` (`rank_inter_posElems`) (not in the paper, as above). -/
lemma restrictRank_univ (hf : IsRankFunction f) : restrictRank f univ = f univ := by
  rw [restrictRank, rank_inter_posElems hf univ, univ_inter, univ_eq_attach, attach_map_val]

omit [DecidableEq E] in
/-- (1) of the proof of `lem:ellipsoid`: the reduced instance has at most `n` elements (not in the
paper, as above). -/
lemma card_posElems_le : Fintype.card {e // e ∈ posElems f} ≤ Fintype.card E := by
  rw [Fintype.card_coe]
  exact card_le_univ _

end Reduction

/-! ### (2) `P₊(f)` between two cubes -/

section Cubes

variable {f : Finset E → ℝ}

/-- The image `K` of `P₊(f)` in the coordinates `y_e = x_e/f({e})` (appF-convex.tex:130): `y ∈ K` if
and only if `x = (f({e}) y_e)_e ∈ P₊(f)`. -/
def scaledPoly (f : Finset E → ℝ) : Set (E → ℝ) :=
  {y | (fun e => f {e} * y e) ∈ indepPoly f}

/-- (2) of the proof of `lem:ellipsoid` (appF-convex.tex:130): `[0, 1/n]^E ⊆ K`. "Indeed, if
`0 ≤ x_e ≤ f({e})/n` for all `e` and `∅ ≠ S ⊆ E`, then `x(S) ≤ |S| max_{e ∈ S} f({e})/n ≤ f(S)` by
monotonicity." -/
theorem box_subset_scaledPoly (hf : IsRankFunction f) (hu : ∀ e, 0 < f {e}) {y : E → ℝ}
    (hy : ∀ e, 0 ≤ y e ∧ y e ≤ 1 / Fintype.card E) : y ∈ scaledPoly f := by
  refine ⟨fun e => mul_nonneg (hu e).le (hy e).1, fun S => ?_⟩
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp [hf.empty]
  · obtain ⟨e₀, he₀, hmax⟩ := S.exists_max_image (fun e => f {e}) hS
    have hn : 0 < (Fintype.card E : ℝ) := by
      have : 0 < Fintype.card E := Fintype.card_pos_iff.2 ⟨e₀⟩
      exact_mod_cast this
    have hxe : ∀ e, f {e} * y e ≤ f {e} / Fintype.card E := fun e => by
      have := mul_le_mul_of_nonneg_left (hy e).2 (hu e).le
      rwa [mul_one_div] at this
    calc ∑ e ∈ S, f {e} * y e ≤ ∑ _e ∈ S, f {e₀} / Fintype.card E :=
          sum_le_sum fun e he => (hxe e).trans (div_le_div_of_nonneg_right (hmax e he) hn.le)
      _ = S.card / Fintype.card E * f {e₀} := by rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ 1 * f {e₀} := by
          refine mul_le_mul_of_nonneg_right ?_ (hu e₀).le
          rw [div_le_one hn]
          exact_mod_cast card_le_univ S
      _ ≤ f S := by rw [one_mul]; exact hf.mono (singleton_subset_iff.2 he₀)

omit [Fintype E] [DecidableEq E] in
/-- (2) of the proof of `lem:ellipsoid` (appF-convex.tex:130): `K ⊆ [0, 1]^E`, as "every `x ∈ P₊(f)`
has `x_e ≤ f({e})`". -/
theorem scaledPoly_subset_box (hu : ∀ e, 0 < f {e}) {y : E → ℝ}
    (hy : y ∈ scaledPoly f) (e : E) : 0 ≤ y e ∧ y e ≤ 1 := by
  have h0 := hy.1 e
  have h1 : f {e} * y e ≤ f {e} := by simpa using hy.2 {e}
  constructor
  · exact nonneg_of_mul_nonneg_right (by simpa [mul_comm] using h0) (hu e)
  · nlinarith [hu e]

/-- (2) of the proof of `lem:ellipsoid` (appF-convex.tex:130): "So `K` contains a ball of radius
`1/(2n)`", the ball about `(1/(2n)) 𝟙` (the STOC version names no center). -/
theorem ball_subset_scaledPoly (hf : IsRankFunction f) (hu : ∀ e, 0 < f {e}) {y : E → ℝ}
    (hy : ∑ e, (y e - 1 / (2 * (Fintype.card E : ℝ))) ^ 2 ≤ (1 / (2 * (Fintype.card E : ℝ))) ^ 2) :
    y ∈ scaledPoly f := by
  refine box_subset_scaledPoly hf hu fun e => ?_
  have hn : 0 < (Fintype.card E : ℝ) := by
    have : 0 < Fintype.card E := Fintype.card_pos_iff.2 ⟨e⟩
    exact_mod_cast this
  have h1 : (y e - 1 / (2 * (Fintype.card E : ℝ))) ^ 2 ≤ (1 / (2 * (Fintype.card E : ℝ))) ^ 2 :=
    (single_le_sum (fun e' _ => sq_nonneg (y e' - 1 / (2 * (Fintype.card E : ℝ))))
      (mem_univ e)).trans hy
  have hpos : 0 ≤ 1 / (2 * (Fintype.card E : ℝ)) := by positivity
  obtain ⟨h2, h3⟩ := abs_le.1 (abs_le_of_sq_le_sq' h1 hpos |>.elim fun h1 h2 => abs_le.2 ⟨h1, h2⟩)
  have e1 : 1 / (2 * (Fintype.card E : ℝ)) + 1 / (2 * Fintype.card E) = 1 / Fintype.card E := by
    field_simp
    ring
  constructor <;> linarith

omit [DecidableEq E] in
/-- (2) of the proof of `lem:ellipsoid` (appF-convex.tex:130): "and lies in a ball of radius
`√n/2`", the ball about `(1/2) 𝟙`. -/
theorem scaledPoly_subset_ball (hu : ∀ e, 0 < f {e}) {y : E → ℝ}
    (hy : y ∈ scaledPoly f) : ∑ e, (y e - 1 / 2) ^ 2 ≤ (Real.sqrt (Fintype.card E) / 2) ^ 2 := by
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  calc ∑ e, (y e - 1 / 2) ^ 2 ≤ ∑ _e : E, (1 / 4 : ℝ) := by
        refine sum_le_sum fun e _ => ?_
        obtain ⟨h0, h1⟩ := scaledPoly_subset_box hu hy e
        nlinarith
    _ = Fintype.card E / 2 ^ 2 := by simp; ring

omit [Fintype E] [DecidableEq E] in
/-- (2) of the proof of `lem:ellipsoid` (appF-convex.tex:130): "the ratio of the radii is
`n^{3/2}`". -/
theorem radii_ratio {n : ℝ} (hn : 0 < n) : (Real.sqrt n / 2) / (1 / (2 * n)) = n ^ (3 / 2 : ℝ) := by
  have e : n ^ (3 / 2 : ℝ) = n * Real.sqrt n := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hn, Real.rpow_one,
      Real.sqrt_eq_rpow]
  rw [e]
  field_simp

end Cubes

/-! ### (3) The separation oracle -/

omit [DecidableEq E] in
/-- (3) of the proof of `lem:ellipsoid` (appF-convex.tex:132): "A separation oracle needs one
submodular minimization. At a center `y` in normalized coordinates, set `z_e := f({e}) y_e`. Either
`z_e < 0` for some `e`, which gives the cut `x_e ≥ 0`, or one submodular minimization of
`T ↦ f(T) − z(T)` returns a set `T` with `z(T) > f(T) ≥ x(T)` for all `x ∈ P₊(f)`, or it shows
`z ∈ P₊(f)`." Here `y ∈ ℝ^E` is any center and `T` a minimizer of `f(T) − z(T)` (one exists, as `E`
is finite). -/
theorem separation {f : Finset E → ℝ} (y : E → ℝ) {T : Finset E}
    (hT : ∀ T', f T - ∑ e ∈ T, f {e} * y e ≤ f T' - ∑ e ∈ T', f {e} * y e) :
    (∃ e, f {e} * y e < 0 ∧ ∀ x ∈ indepPoly f, f {e} * y e < x e) ∨
      (f T < ∑ e ∈ T, f {e} * y e ∧ ∀ x ∈ indepPoly f, ∑ e ∈ T, x e ≤ f T) ∨
      (fun e => f {e} * y e) ∈ indepPoly f := by
  -- "Either `z_e < 0` for some `e`, which gives the cut `x_e ≥ 0`,"
  by_cases hneg : ∃ e, f {e} * y e < 0
  · obtain ⟨e, he⟩ := hneg
    exact Or.inl ⟨e, he, fun x hx => he.trans_le (hx.1 e)⟩
  push Not at hneg
  -- "or one submodular minimization of `T ↦ f(T) − z(T)` returns a set `T` with
  -- `z(T) > f(T) ≥ x(T)` for all `x ∈ P₊(f)`, or it shows `z ∈ P₊(f)`."
  by_cases hT0 : f T - ∑ e ∈ T, f {e} * y e < 0
  · exact Or.inr (Or.inl ⟨by linarith, fun x hx => hx.2 T⟩)
  · refine Or.inr (Or.inr ⟨hneg, fun S => ?_⟩)
    have := hT S
    simp only
    linarith

/-- (3) of the proof of `lem:ellipsoid` (appF-convex.tex:132), continued: "In normalized coordinates
the violated inequality is `y_e ≥ 0` or `∑_{e ∈ T} f({e}) y_e ≤ f(T)`. Its normal gives the central
cut through the current center." With `f({e}) > 0` for all `e` (from (1)), the cases of
`separation` at the center `y` are: `y_e < 0`, while every `y' ∈ K` has `y'_e ≥ 0`, and the normal
`−𝟙_e` gives the central cut `{y' : y'_e ≥ y_e}`, which contains `K`; or
`∑_{e ∈ T} f({e}) y_e > f(T) ≥ ∑_{e ∈ T} f({e}) y'_e` for every `y' ∈ K`, and the normal
`(f({e}) [e ∈ T])_e` gives the central cut `{y' : ∑_{e ∈ T} f({e}) y'_e ≤ ∑_{e ∈ T} f({e}) y_e}`,
which contains `K`; or `y ∈ K`. That this normal is not zero, `T ≠ ∅` as `f(∅) = 0`, is not in
the paper. -/
theorem separation_normalized {f : Finset E → ℝ} (hf : IsRankFunction f) (hu : ∀ e, 0 < f {e})
    (y : E → ℝ) {T : Finset E}
    (hT : ∀ T', f T - ∑ e ∈ T, f {e} * y e ≤ f T' - ∑ e ∈ T', f {e} * y e) :
    (∃ e, y e < 0 ∧ ∀ y' ∈ scaledPoly f, 0 ≤ y' e ∧ y e ≤ y' e) ∨
      (T.Nonempty ∧ f T < ∑ e ∈ T, f {e} * y e ∧ ∀ y' ∈ scaledPoly f,
        ∑ e ∈ T, f {e} * y' e ≤ f T ∧ ∑ e ∈ T, f {e} * y' e ≤ ∑ e ∈ T, f {e} * y e) ∨
      y ∈ scaledPoly f := by
  rcases separation y hT with ⟨e, he, -⟩ | ⟨hlt, -⟩ | hin
  · -- "the violated inequality is `y_e ≥ 0`": `z_e = f({e}) y_e < 0` with `f({e}) > 0`, and every
    -- `y' ∈ K` has `y'_e ≥ 0`; its normal gives the central cut `y'_e ≥ y_e`
    have hye : y e < 0 := by
      by_contra h
      push Not at h
      exact absurd he (not_lt.2 (mul_nonneg (hu e).le h))
    refine Or.inl ⟨e, hye, fun y' hy' => ?_⟩
    have h0 := (scaledPoly_subset_box hu hy' e).1
    exact ⟨h0, by linarith⟩
  · -- "or `∑_{e ∈ T} f({e}) y_e ≤ f(T)`", which every `y' ∈ K` satisfies, as
    -- `(f({e}) y'_e)_e ∈ P₊(f)`; its normal gives the central cut through `y`
    have hT0 : T.Nonempty := by
      rcases T.eq_empty_or_nonempty with rfl | h
      · simp [hf.empty] at hlt
      · exact h
    refine Or.inr (Or.inl ⟨hT0, hlt, fun y' hy' => ?_⟩)
    have h1 : ∑ e ∈ T, f {e} * y' e ≤ f T := hy'.2 T
    exact ⟨h1, by linarith⟩
  · exact Or.inr (Or.inr hin)

/-! ### (4) The bound on the objective -/

section Objective

variable {f : Finset E → ℝ} {m : E → ℝ} {c : (E → ℝ) → ℝ} {g : (E → ℝ) → E → ℝ} {G rb : ℝ}

omit [DecidableEq E] in
/-- The reward is linear: `r(a x + b y) = a r(x) + b r(y)`. -/
lemma reward_add_smul (m x y : E → ℝ) (a b : ℝ) :
    reward m (a • x + b • y) = a * reward m x + b * reward m y := by
  simp only [reward, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact sum_congr rfl fun e _ => by ring

/-- (4) of the proof of `lem:ellipsoid` (appF-convex.tex:134): "We minimize `−U_A(· | α) = c − α r`,
which is convex on `P₊(f)`". -/
lemma convexOn_cost_sub (h : PolySetting f m c g G rb) (α : ℝ) :
    ConvexOn ℝ (indepPoly f) (fun x => c x - α * reward m x) := by
  refine ⟨h.convexOn.1, fun x hx y hy a b ha hb hab => ?_⟩
  have h1 := h.convexOn.2 hx hy ha hb hab
  simp only [smul_eq_mul] at h1 ⊢
  rw [reward_add_smul]
  nlinarith

/-- (4) of the proof of `lem:ellipsoid` (appF-convex.tex:134): `c − α r` has "the subgradient
`g(x) − α m` at `x`". -/
lemma subgrad_cost_sub (h : PolySetting f m c g G rb) (α : ℝ) {x y : E → ℝ} (hx : x ∈ indepPoly f)
    (hy : y ∈ indepPoly f) :
    (c x - α * reward m x) + ∑ e, (g x e - α * m e) * (y e - x e) ≤ c y - α * reward m y := by
  have h1 := h.subgrad x hx y hy
  have h2 : ∑ e, (g x e - α * m e) * (y e - x e) =
      ∑ e, g x e * (y e - x e) - α * (reward m y - reward m x) := by
    simp only [reward, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact sum_congr rfl fun e _ => by ring
  rw [h2]
  linarith

/-- (4) of the proof of `lem:ellipsoid` (appF-convex.tex:134), the last inequality of
"`0 ≤ c(x) ≤ G x(E) ≤ G f(E)`": `G x(E) ≤ G f(E)` for `x ∈ P₊(f)`, as `x(E) ≤ f(E)` and `G ≥ 0`.
That `G ≥ 0` is left implicit: `G ≥ |g_e(0)| ≥ 0` if `E ≠ ∅`, and `x(E) = f(E) = f(∅) = 0` if
`E = ∅`. -/
lemma PolySetting.G_mul_le (h : PolySetting f m c g G rb) {x : E → ℝ} (hx : x ∈ indepPoly f) :
    G * ∑ e, x e ≤ G * f univ := by
  rcases isEmpty_or_nonempty E with hE | hne
  · simp [univ_eq_empty, h.rank.empty]
  · obtain ⟨e₀⟩ := hne
    have hG : 0 ≤ G := (abs_nonneg _).trans (h.bound 0 (zero_mem_indepPoly h.rank) e₀)
    exact mul_le_mul_of_nonneg_left (hx.2 univ) hG

/-- `G f(E) ≥ 0`, `PolySetting.G_mul_le` at `x = 0` (not in the paper: it uses this tacitly in the
last sentence of `lem:ellipsoid`, where `δ ≥ M = r̄ + G f(E)` gives `r̄ ≤ δ` (appF-convex.tex:136),
and in (T5) of the proof of `thm:convexfptas`, where it gives `M ≥ r̄ ≥ w` (appF-convex.tex:144)).
-/
lemma PolySetting.G_mul_nonneg (h : PolySetting f m c g G rb) : 0 ≤ G * f univ := by
  simpa using h.G_mul_le (zero_mem_indepPoly h.rank)

/-- (4) of the proof of `lem:ellipsoid` (appF-convex.tex:134): "For `x ∈ P₊(f)`, the subgradient
inequality with `y = 0` gives `0 = c(0) ≥ c(x) − g(x)ᵀx`, so `0 ≤ c(x) ≤ G x(E) ≤ G f(E)`". -/
theorem cost_le (h : PolySetting f m c g G rb) {x : E → ℝ} (hx : x ∈ indepPoly f) :
    0 ≤ c x ∧ c x ≤ G * ∑ e, x e ∧ G * ∑ e, x e ≤ G * f univ := by
  have hsub := h.subgrad x hx 0 (zero_mem_indepPoly h.rank)
  rw [h.cost.zero] at hsub
  have h1 : c x ≤ ∑ e, g x e * x e := by
    have : ∑ e, g x e * ((0 : E → ℝ) e - x e) = -∑ e, g x e * x e := by
      rw [← sum_neg_distrib]
      exact sum_congr rfl fun e _ => by simp
    linarith
  refine ⟨h.c_nonneg hx, h1.trans ?_, h.G_mul_le hx⟩
  rw [Finset.mul_sum]
  exact sum_le_sum fun e _ => mul_le_mul_of_nonneg_right ((le_abs_self _).trans (h.bound x hx e))
    (hx.1 e)

/-- (4) of the proof of `lem:ellipsoid` (appF-convex.tex:134): "and `0 ≤ α r(x) ≤ r̄`. Hence
`|U_A(· | α)| ≤ M := r̄ + G f(E)` on `P₊(f)`" (for `α ∈ [0, 1]`). -/
theorem abs_util_le (h : PolySetting f m c g G rb) {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) {x : E → ℝ}
    (hx : x ∈ indepPoly f) : |util m c α x| ≤ rb + G * f univ := by
  obtain ⟨c0, c1, c2⟩ := cost_le h hx
  have r0 := reward_nonneg_of_mem h.m_nonneg hx
  have r1 := h.reward_le x hx
  have h1 : 0 ≤ α * reward m x := mul_nonneg hα.1 r0
  have h2 : α * reward m x ≤ rb := by nlinarith [hα.2]
  unfold util
  rw [abs_le]
  constructor <;> linarith

end Objective

/-! ### (5) The ellipsoid method -/

section Method

/-- The iteration number `t = ⌈2n² ln(2n^{3/2} M/δ)⌉` of `lem:ellipsoid` (appF-convex.tex:124, 136).
This is a formula; that the ellipsoid method attains it is not formalised (see the module
docstring). -/
noncomputable def ellipsoidIters (n : ℕ) (M δ : ℝ) : ℕ :=
  ⌈2 * (n : ℝ) ^ 2 * Real.log (2 * (n : ℝ) ^ (3 / 2 : ℝ) * M / δ)⌉₊

/-- (5) of the proof of `lem:ellipsoid` (appF-convex.tex:136): for `n ≥ 1` and `0 < δ < M`,
`t = ⌈2n² ln(2n^{3/2} M/δ)⌉` "is positive and exceeds `2n² ln(n^{3/2})` since `δ < M`": as
`M/δ > 1`, `2n^{3/2} M/δ > n^{3/2} ≥ 1`, so `t ≥ 2n² ln(2n^{3/2} M/δ) > 2n² ln(n^{3/2}) ≥ 0`. So
`t` exceeds `2n² ln(R_out/R_in)` for `R_out/R_in = n^{3/2}`, as the cited bound requires. -/
theorem ellipsoidIters_ge {n : ℕ} (hn : 1 ≤ n) {M δ : ℝ} (hδ : 0 < δ) (hδM : δ < M) :
    0 < ellipsoidIters n M δ ∧
      2 * (n : ℝ) ^ 2 * Real.log ((n : ℝ) ^ (3 / 2 : ℝ)) < ellipsoidIters n M δ := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (1 : ℝ) ≤ (n : ℝ) ^ (3 / 2 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
  have hMδ : 1 < M / δ := by rw [lt_div_iff₀ hδ]; linarith
  have hn2 : 0 < 2 * (n : ℝ) ^ 2 := by positivity
  -- "since `δ < M`": `ln(2n^{3/2} M/δ) > ln(n^{3/2})`, as `2n^{3/2} M/δ > n^{3/2} > 0`
  have hlog : Real.log ((n : ℝ) ^ (3 / 2 : ℝ)) < Real.log (2 * (n : ℝ) ^ (3 / 2 : ℝ) * M / δ) := by
    apply Real.log_lt_log (by linarith)
    rw [mul_div_assoc]
    nlinarith
  have ht := Nat.le_ceil (2 * (n : ℝ) ^ 2 * Real.log (2 * (n : ℝ) ^ (3 / 2 : ℝ) * M / δ))
  -- "exceeds `2n² ln(n^{3/2})`"
  have h1 : 2 * (n : ℝ) ^ 2 * Real.log ((n : ℝ) ^ (3 / 2 : ℝ)) < ellipsoidIters n M δ :=
    (mul_lt_mul_of_pos_left hlog hn2).trans_le ht
  -- "is positive", as `2n² ln(n^{3/2}) ≥ 0`
  have h0 : 0 ≤ 2 * (n : ℝ) ^ 2 * Real.log ((n : ℝ) ^ (3 / 2 : ℝ)) :=
    mul_nonneg hn2.le (Real.log_nonneg hnp)
  exact ⟨by exact_mod_cast h0.trans_lt h1, h1⟩

/-- (5) of the proof of `lem:ellipsoid` (appF-convex.tex:136): with `R_out/R_in = n^{3/2}` and
`t = ⌈2n² ln(2n^{3/2} M/δ)⌉`, the bound `(2M R_out/R_in) exp(−t/(2n²))` of the ellipsoid method is
at most `δ`. -/
theorem ellipsoid_bound_le {n : ℕ} (hn : 1 ≤ n) {M δ : ℝ} (hδ : 0 < δ) (hδM : δ < M) :
    2 * M * (n : ℝ) ^ (3 / 2 : ℝ) * Real.exp (-(ellipsoidIters n M δ : ℝ) / (2 * (n : ℝ) ^ 2)) ≤
      δ := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hM : 0 < M := hδ.trans hδM
  have hnp : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hn2 : 0 < 2 * (n : ℝ) ^ 2 := by positivity
  set L := Real.log (2 * (n : ℝ) ^ (3 / 2 : ℝ) * M / δ) with hL
  have ht : 2 * (n : ℝ) ^ 2 * L ≤ ellipsoidIters n M δ := Nat.le_ceil _
  -- `exp(−t/(2n²)) ≤ exp(−L) = δ/(2n^{3/2} M)`
  have hexp : Real.exp (-(ellipsoidIters n M δ : ℝ) / (2 * (n : ℝ) ^ 2)) ≤ Real.exp (-L) := by
    rw [Real.exp_le_exp, neg_div, neg_le_neg_iff, le_div_iff₀ hn2]
    linarith
  have hexpL : Real.exp (-L) = δ / (2 * (n : ℝ) ^ (3 / 2 : ℝ) * M) := by
    rw [Real.exp_neg, hL, Real.exp_log (by positivity)]
    field_simp
  calc 2 * M * (n : ℝ) ^ (3 / 2 : ℝ) * Real.exp (-(ellipsoidIters n M δ : ℝ) / (2 * (n : ℝ) ^ 2))
      ≤ 2 * M * (n : ℝ) ^ (3 / 2 : ℝ) * Real.exp (-L) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = δ := by rw [hexpL]; field_simp

omit [DecidableEq E] in
/-- (5) of the proof of `lem:ellipsoid` (appF-convex.tex:136): "We apply this to `K` and to
`−U_A(· | α)` in the coordinates `y`, where the subgradients are scaled by `f({e})`": if `γ` is a
subgradient of `φ` at `x = (f({e}) y_e)_e` on `P₊(f)`, then `(f({e}) γ_e)_e` is a subgradient of
`y ↦ φ((f({e}) y_e)_e)` at `y` on `K`. -/
theorem subgrad_scaled {f : Finset E → ℝ} {φ : (E → ℝ) → ℝ} {γ y : E → ℝ}
    (hγ : ∀ x' ∈ indepPoly f, φ (fun e => f {e} * y e) + ∑ e, γ e * (x' e - f {e} * y e) ≤ φ x') :
    ∀ y' ∈ scaledPoly f, φ (fun e => f {e} * y e) + ∑ e, (f {e} * γ e) * (y' e - y e) ≤
      φ (fun e => f {e} * y' e) := by
  intro y' hy'
  have := hγ _ hy'
  have e : ∑ e, γ e * (f {e} * y' e - f {e} * y e) = ∑ e, (f {e} * γ e) * (y' e - y e) :=
    sum_congr rfl fun e _ => by ring
  rwa [e] at this

variable {f : Finset E → ℝ} {m : E → ℝ} {c : (E → ℝ) → ℝ} {g : (E → ℝ) → E → ℝ} {G rb : ℝ}

/-- `lem:ellipsoid`, its last sentence (appF-convex.tex:124, 136): "For `δ ≥ r̄ + G f(E)`, the
response `0` is `δ`-optimal", as "`V(α) − U_A(0 | α) = V(α) ≤ r̄ ≤ δ`" (for `α ∈ [0, 1]`; `r̄ ≤ δ`
uses `G f(E) ≥ 0`, `PolySetting.G_mul_nonneg`). -/
theorem zero_isDeltaOpt (h : PolySetting f m c g G rb) {α δ : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hδ : rb + G * f univ ≤ δ) : IsDeltaOpt (indepPoly f) m c α δ 0 := by
  have h0 := zero_mem_indepPoly h.rank
  refine ⟨h0, ?_⟩
  -- "`V(α) − U_A(0 | α) = V(α)`"
  have hu0 : util m c α 0 = 0 := by simp [util, reward, h.cost.zero]
  -- "`V(α) ≤ r̄`": `V(α) = U_A(y | α) ≤ α r(y) ≤ r̄` at a best response `y`, as `c ≥ 0`
  have hV : V (indepPoly f) m c α ≤ rb := by
    obtain ⟨y, hy⟩ := h.toSetting.exists_isBR α
    rw [hy.V_eq]
    have := h.c_nonneg hy.1
    have r0 := reward_nonneg_of_mem h.m_nonneg hy.1
    have r1 := h.reward_le _ hy.1
    unfold util
    nlinarith [hα.1, hα.2]
  -- "`r̄ ≤ δ`", as `δ ≥ r̄ + G f(E)` and `G f(E) ≥ 0`
  have hG := h.G_mul_nonneg
  rw [hu0]
  linarith

/-! #### The method with its operation counts

`lem:ellipsoid` counts the work of the method: "at most `⌈2n² ln(2n^{3/2}(r̄ + G f(E))/δ)⌉`
iterations, each of which makes at most one submodular minimization, at most one call of the oracle
for `c`, and `O(n²)` further arithmetic operations" (appF-convex.tex:124). Its proof counts in (3),
"A separation oracle needs one submodular minimization" (appF:132), and in (5), "The values of `c`
at the centers in `P₊(f)` select `x_t`, and each iteration updates the ellipsoid with `O(n²)`
operations" (appF:136). The method is cited ([Bub15, Thm. 2.4]) and not formalised: its ellipsoids,
their centers and the update by a central cut are a parameter (`EllMethod`), and the operations of
an update enter as the hypothesis `EllMethod.Cited` (the paper's count `O(n²)`, not cited: the
citation is for the bound, and the paper states the count without proof). The counted method
performs the steps of the proof in the cost model of `Stoc.CountedQ`
(`ContractDesignPolymatroids/Preliminaries/CountedOracle.lean`): `prepC` ((1) and (4): the `n` evaluations `f({e})` and
the `n` tests that give `E'`, and `f(E)` and `M`), `sepC` ((3): the separation at a center), `objC`
((4) and (5): at a center in `K`, one query of the oracle for `c`, the value of the objective and
its subgradient in the coordinates `y`), `ellIterC` (one iteration: the separation; at a center in
`K` the objective and one comparison for the best center so far; and the update), `ellRunC` (`t`
iterations), `respC` (one response: the method on the reduced instance and its best center `x_t`,
padded with zeros) and `ellipsoidC` (`prepC`, then `respC`). `respC` takes
`t = ellipsoidIters n M δ` from its definition at no cost: computing it needs `ln` and `⌈·⌉`, which
are not operations of the model of 08c-convex.tex:13, and the paper does not count it. (Not in the
paper: the paper counts in prose.) -/

section Counts

open Counted

variable {D σ : Type*} [Fintype D] [DecidableEq D]

/-- The central-cut ellipsoid method of [Bub15, Thm. 2.4] (cited, not formalised), a parameter of
the counts of `lem:ellipsoid`, in the coordinates `y` of the reduced instance: its ellipsoids, of a
type `σ`, the initial ellipsoid (the ball of radius `√n/2` about `(1/2) 𝟙` of (2), which contains
`K`), the center of an ellipsoid, the next ellipsoid after the central cut with the normal `a`
through the center ("Its normal gives the central cut through the current center", appF:132; at a
center in `K`, the normal is the subgradient), and the arithmetic operations of the initial
ellipsoid and of an update. In dimension one the method is bisection ("which halves the length of
the interval in each step", appF:136), which is also of this form. -/
structure EllMethod (D : Type*) (σ : Type*) where
  /-- The initial ellipsoid. -/
  init : σ
  /-- The center of an ellipsoid. -/
  center : σ → D → ℝ
  /-- The next ellipsoid after the central cut with the normal `a` through the center. -/
  update : σ → (D → ℝ) → σ
  /-- The arithmetic operations of the initial ellipsoid. -/
  initOps : ℕ
  /-- The arithmetic operations of the update with the normal `a`. -/
  updOps : σ → (D → ℝ) → ℕ

/-- The cost of the method, as a hypothesis: "each iteration updates the ellipsoid with `O(n²)`
operations" (appF-convex.tex:136; the paper's count, not cited: [Bub15, Thm. 2.4] is cited for the
bound, and the paper states this count without proof), here at most `cE n²` operations for each
update, `n = |D|`; and at most `cE n²` operations for the initial ellipsoid (not in the paper: the
paper does not count the initial ellipsoid; the ball of (2) has `O(n²)` entries). The name
`Cited` says only that the method is cited. -/
def EllMethod.Cited (Ell : EllMethod D σ) (cE : ℕ) : Prop :=
  Ell.initOps ≤ cE * Fintype.card D ^ 2 ∧ ∀ s a, Ell.updOps s a ≤ cE * Fintype.card D ^ 2

/-- The set `T` that "one submodular minimization of `T ↦ f(T) − z(T)` returns"
(appF-convex.tex:132): a minimizer, chosen by `Classical.choice` (the separation works with any
minimizer; one exists, as `D` is finite). -/
noncomputable def sepMin (φ : Finset D → ℝ) (z : D → ℝ) : Finset D :=
  (exists_min_image univ (fun T => φ T - ∑ e ∈ T, z e) univ_nonempty).choose

omit [DecidableEq D] in
lemma sepMin_le (φ : Finset D → ℝ) (z : D → ℝ) (T' : Finset D) :
    φ (sepMin φ z) - ∑ e ∈ sepMin φ z, z e ≤ φ T' - ∑ e ∈ T', z e :=
  (exists_min_image univ (fun T => φ T - ∑ e ∈ T, z e) univ_nonempty).choose_spec.2 T'
    (mem_univ _)

/-- (3) of the proof of `lem:ellipsoid`, counted: "A separation oracle needs one submodular
minimization. At a center `y` in normalized coordinates, set `z_e := f({e}) y_e`" (one
multiplication for each `e`, with the values `f({e})` of `prepC`). "Either `z_e < 0` for some `e`"
(one comparison for each `e`), "which gives the cut `x_e ≥ 0`, or one submodular minimization of
`T ↦ f(T) − z(T)` returns a set `T` with `z(T) > f(T) ≥ x(T)` for all `x ∈ P₊(f)`" (the test
`z(T) > f(T)`: one evaluation of `f` at `T`, the sum `z(T)` and one comparison), "or it shows
`z ∈ P₊(f)`. In normalized coordinates the violated inequality is `y_e ≥ 0` or
`∑_{e ∈ T} f({e}) y_e ≤ f(T)`. Its normal gives the central cut through the current center": the
result is `inl a` with the normal `a = −𝟙_e` or `a = (f({e}) [e ∈ T])_e` (one operation for each
entry), or `inr z` when `z ∈ P₊(f)`. -/
noncomputable def sepC (φ : Finset D → ℝ) (y : D → ℝ) : Counted ((D → ℝ) ⊕ (D → ℝ)) :=
  vec (fun e => ops 1 (φ {e} * y e)) >>=ᶜ fun z =>
  ops (Fintype.card D) () >>=ᶜ fun _ =>
  if h : ∃ e, z e < 0 then
    ops (Fintype.card D) (Sum.inl fun e => if e = h.choose then -1 else 0)
  else
    minimize (sepMin φ z) >>=ᶜ fun T =>
    evalF (φ T) >>=ᶜ fun fT =>
    Counted.sum T (fun e => ret (z e)) >>=ᶜ fun zT =>
    ops 1 () >>=ᶜ fun _ =>
    if fT < zT then ops (Fintype.card D) (Sum.inl fun e => if e ∈ T then φ {e} else 0)
    else ret (Sum.inr z)

/-- The cost of the separation (not in the paper, which counts "one submodular minimization"): at
most one minimization, at most one evaluation of `f`, and at most `4n + 1` arithmetic operations,
`n = |D|`. -/
lemma sepC_cost (φ : Finset D → ℝ) (y : D → ℝ) :
    (sepC φ y).cost.1 ≤ 4 * Fintype.card D + 1 ∧ (sepC φ y).cost.2.1 ≤ 1 ∧
      (sepC φ y).cost.2.2 ≤ 1 := by
  have hT := card_le_univ (sepMin φ fun e => φ {e} * y e)
  by_cases h : ∃ e, φ {e} * y e < 0
  · simp [sepC, h]
    omega
  · by_cases h2 : φ (sepMin φ fun e => φ {e} * y e) <
        ∑ e ∈ sepMin φ fun e => φ {e} * y e, φ {e} * y e
    · simp [sepC, h, h2]
      omega
    · simp [sepC, h, h2]
      omega

/-- (3) of the proof of `lem:ellipsoid`: a cut of `sepC` is a central cut through `y` that contains
`K`, with a nonzero normal ("Its normal gives the central cut through the current center"): for
`y_e < 0` the cut `y'_e ≥ y_e`, as `K ⊆ [0, 1]^E` (`scaledPoly_subset_box`), and for the set `T`
the cut of `separation_normalized`. -/
lemma sepC_inl {φ : Finset D → ℝ} (hφ : IsRankFunction φ) (hu : ∀ e, 0 < φ {e}) {y a : D → ℝ}
    (h : (sepC φ y).val = Sum.inl a) :
    a ≠ 0 ∧ ∀ y' ∈ scaledPoly φ, ∑ e, a e * y' e ≤ ∑ e, a e * y e := by
  by_cases hneg : ∃ e, φ {e} * y e < 0
  · -- "which gives the cut `x_e ≥ 0`", with the normal `−𝟙_e`
    have hval : (sepC φ y).val = Sum.inl fun e => if e = hneg.choose then -1 else 0 := by
      simp [sepC, hneg]
      rfl
    rw [hval, Sum.inl.injEq] at h
    subst h
    have he₀ := hneg.choose_spec
    have hy : y hneg.choose < 0 := by
      by_contra hc
      exact absurd he₀ (not_lt.2 (mul_nonneg (hu _).le (not_lt.1 hc)))
    refine ⟨fun h0 => by simpa using congrFun h0 hneg.choose, fun y' hy' => ?_⟩
    have h0 := (scaledPoly_subset_box hu hy' hneg.choose).1
    simp only [ite_mul, neg_one_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]
    linarith
  · by_cases hlt : φ (sepMin φ fun e => φ {e} * y e) <
        ∑ e ∈ sepMin φ fun e => φ {e} * y e, φ {e} * y e
    · -- "`∑_{e ∈ T} f({e}) y_e ≤ f(T)`", with the normal `(f({e}) [e ∈ T])_e`
      have hval : (sepC φ y).val =
          Sum.inl fun e => if e ∈ sepMin φ (fun e => φ {e} * y e) then φ {e} else 0 := by
        simp [sepC, hneg, hlt]
        rfl
      rw [hval, Sum.inl.injEq] at h
      subst h
      rcases separation_normalized hφ hu y (sepMin_le φ fun e => φ {e} * y e) with
        ⟨e, hye, -⟩ | ⟨hT0, -, hcut⟩ | hin
      · exact absurd ⟨e, mul_neg_of_pos_of_neg (hu e) hye⟩ hneg
      · obtain ⟨e, he⟩ := hT0
        refine ⟨fun h0 => absurd he (by simpa [(hu e).ne'] using congrFun h0 e),
          fun y' hy' => ?_⟩
        simp only [ite_mul, zero_mul, sum_ite_mem, univ_inter]
        exact (hcut y' hy').2
      · exact absurd (hin.2 _) (not_le.2 hlt)
    · have hval : (sepC φ y).val = Sum.inr fun e => φ {e} * y e := by
        simp [sepC, hneg, hlt]
      rw [hval] at h
      exact absurd h (by simp)

/-- (3) of the proof of `lem:ellipsoid`: if `sepC` finds no cut, then "it shows `z ∈ P₊(f)`",
that is, `y ∈ K`, by `separation`. -/
lemma sepC_inr {φ : Finset D → ℝ} {y x : D → ℝ} (h : (sepC φ y).val = Sum.inr x) :
    x = (fun e => φ {e} * y e) ∧ y ∈ scaledPoly φ := by
  by_cases hneg : ∃ e, φ {e} * y e < 0
  · have hval : (sepC φ y).val = Sum.inl fun e => if e = hneg.choose then -1 else 0 := by
      simp [sepC, hneg]
      rfl
    rw [hval] at h
    exact absurd h (by simp)
  · by_cases hlt : φ (sepMin φ fun e => φ {e} * y e) <
        ∑ e ∈ sepMin φ fun e => φ {e} * y e, φ {e} * y e
    · have hval : (sepC φ y).val =
          Sum.inl fun e => if e ∈ sepMin φ (fun e => φ {e} * y e) then φ {e} else 0 := by
        simp [sepC, hneg, hlt]
        rfl
      rw [hval] at h
      exact absurd h (by simp)
    · have hval : (sepC φ y).val = Sum.inr fun e => φ {e} * y e := by
        simp [sepC, hneg, hlt]
      rw [hval, Sum.inr.injEq] at h
      subst h
      refine ⟨rfl, ?_⟩
      rcases separation y (sepMin_le φ fun e => φ {e} * y e) with ⟨e, he, -⟩ | ⟨hlt', -⟩ | hin
      · exact absurd ⟨e, he⟩ hneg
      · exact absurd hlt' hlt
      · exact hin

/-- At a center `y ∈ K`, `sepC` finds no cut (not in the paper: it leaves this implicit). -/
lemma sepC_of_mem {φ : Finset D → ℝ} {y : D → ℝ} (hy : y ∈ scaledPoly φ) :
    (sepC φ y).val = Sum.inr fun e => φ {e} * y e := by
  have hneg : ¬ ∃ e, φ {e} * y e < 0 := fun ⟨e, he⟩ => absurd (hy.1 e) (not_le.2 he)
  have hlt : ¬ φ (sepMin φ fun e => φ {e} * y e) <
      ∑ e ∈ sepMin φ fun e => φ {e} * y e, φ {e} * y e := not_lt.2 (hy.2 _)
  simp [sepC, hneg, hlt]

/-- (4) and (5) of the proof of `lem:ellipsoid`, counted: at a center `y ∈ K`, with
`x = (f({e}) y_e)_e ∈ P₊(f)`, one call of the oracle for `c`, which returns `c(x)` and `g(x)`; the
reward `r(x)` (one multiplication and one addition for each `e`), the value `c(x) − α r(x)` of the
objective `−U_A(· | α) = c − α r` (two operations), and its subgradient "`g(x) − α m` at `x`" in
the coordinates `y`, "where the subgradients are scaled by `f({e})`" (three operations for each
`e`). It returns the value, `c(x)` and the subgradient. -/
noncomputable def objC (φ : Finset D → ℝ) (μ : D → ℝ) (κ : (D → ℝ) → ℝ)
    (γ : (D → ℝ) → D → ℝ) (α : ℝ) (x : D → ℝ) : CountedQ (ℝ × ℝ × (D → ℝ)) :=
  CountedQ.query (κ x, γ x) >>=ᵠ fun q =>
  CountedQ.lift (Counted.sum univ fun e => ops 1 (μ e * x e)) >>=ᵠ fun r =>
  CountedQ.lift (ops 2 (q.1 - α * r)) >>=ᵠ fun v =>
  CountedQ.lift (vec fun e => ops 3 (φ {e} * (q.2 e - α * μ e))) >>=ᵠ fun a =>
  CountedQ.ret (v, q.1, a)

omit [DecidableEq D] in
lemma objC_val (φ : Finset D → ℝ) (μ : D → ℝ) (κ : (D → ℝ) → ℝ) (γ : (D → ℝ) → D → ℝ)
    (α : ℝ) (x : D → ℝ) :
    (objC φ μ κ γ α x).val =
      (κ x - α * reward μ x, κ x, fun e => φ {e} * (γ x e - α * μ e)) := rfl

omit [DecidableEq D] in
/-- The cost of `objC` (not in the paper): one query of the oracle for `c` and `5n + 2` arithmetic
operations. -/
lemma objC_cost (φ : Finset D → ℝ) (μ : D → ℝ) (κ : (D → ℝ) → ℝ) (γ : (D → ℝ) → D → ℝ)
    (α : ℝ) (x : D → ℝ) :
    (objC φ μ κ γ α x).cost = (5 * Fintype.card D + 2, 0, 0) ∧
      (objC φ μ κ γ α x).queries = 1 := by
  simp [objC, Prod.ext_iff]
  ring

/-- (4) and (5) of the proof of `lem:ellipsoid`: the vector of `objC` at a center `y ∈ K` is a
subgradient on `K` of the objective in the coordinates `y`: `c − α r` "is convex on `P₊(f)` with
the subgradient `g(x) − α m` at `x`" (`subgrad_cost_sub`), and in the coordinates `y` "the
subgradients are scaled by `f({e})`" (`subgrad_scaled`). -/
lemma objC_subgrad {φ : Finset D → ℝ} {μ : D → ℝ} {κ : (D → ℝ) → ℝ} {γ : (D → ℝ) → D → ℝ}
    {G rb : ℝ} (h : PolySetting φ μ κ γ G rb) (α : ℝ) {y : D → ℝ} (hy : y ∈ scaledPoly φ) :
    ∀ y' ∈ scaledPoly φ,
      (objC φ μ κ γ α (fun e => φ {e} * y e)).val.1 +
          ∑ e, (objC φ μ κ γ α (fun e => φ {e} * y e)).val.2.2 e * (y' e - y e) ≤
        κ (fun e => φ {e} * y' e) - α * reward μ (fun e => φ {e} * y' e) :=
  subgrad_scaled (φ := fun x => κ x - α * reward μ x)
    (γ := fun e => γ (fun e => φ {e} * y e) e - α * μ e) fun _ hx' => subgrad_cost_sub h α hy hx'

/-- The record of the best center in `K` so far: the value `c(x) − α r(x)` of the objective, the
point `x` and `c(x)`; `none` before the first center in `K`. -/
abbrev BestRec (D : Type*) := Option (ℝ × (D → ℝ) × ℝ)

/-- The record after a center in `K` with the triple `p` ("The values of `c` at the centers in
`P₊(f)` select `x_t`", appF-convex.tex:136): `p` replaces the record if its value is smaller. -/
noncomputable def bestUpd : BestRec D → ℝ × (D → ℝ) × ℝ → BestRec D
  | none, p => some p
  | some q, p => if p.1 < q.1 then some p else some q

/-- The record `b` holds a triple of `S` with the least value, and it is `none` only if `S = ∅`. -/
def IsBestOf (b : BestRec D) (S : Set (ℝ × (D → ℝ) × ℝ)) : Prop :=
  (b = none → S = ∅) ∧ ∀ p, b = some p → p ∈ S ∧ ∀ q ∈ S, p.1 ≤ q.1

omit [Fintype D] [DecidableEq D] in
lemma isBestOf_upd {b : BestRec D} {S : Set (ℝ × (D → ℝ) × ℝ)} (h : IsBestOf b S)
    (p : ℝ × (D → ℝ) × ℝ) : IsBestOf (bestUpd b p) (insert p S) := by
  refine ⟨fun h0 => by cases b <;> simp [bestUpd] at h0; split_ifs at h0, fun p' hp' => ?_⟩
  cases b with
  | none =>
    simp only [bestUpd, Option.some.injEq] at hp'
    subst hp'
    rw [h.1 rfl]
    simp
  | some q =>
    obtain ⟨hqS, hqmin⟩ := h.2 q rfl
    simp only [bestUpd] at hp'
    split_ifs at hp' with hlt
    · simp only [Option.some.injEq] at hp'
      subst hp'
      refine ⟨Set.mem_insert _ _, fun q' hq' => ?_⟩
      rcases hq' with rfl | hq'
      · exact le_rfl
      · exact hlt.le.trans (hqmin q' hq')
    · simp only [Option.some.injEq] at hp'
      subst hp'
      refine ⟨Set.mem_insert_of_mem _ hqS, fun q' hq' => ?_⟩
      rcases hq' with rfl | hq'
      · exact not_lt.1 hlt
      · exact hqmin q' hq'

variable (φ : Finset D → ℝ) (μ : D → ℝ) (κ : (D → ℝ) → ℝ) (γ : (D → ℝ) → D → ℝ) (α : ℝ)

/-- One iteration of the method at the ellipsoid `s`, counted: the separation at its center
(`sepC`); after a cut, the update with its normal; at a center in `K`, the objective (`objC`), one
comparison with the record (`bestUpd`) and the update with the subgradient. The update has the
cost `updOps`, bounded by the paper's count `O(n²)` (`EllMethod.Cited`). -/
noncomputable def ellIterC (Ell : EllMethod D σ) (s : σ) (b : BestRec D) :
    CountedQ (σ × BestRec D) :=
  CountedQ.lift (sepC φ (Ell.center s)) >>=ᵠ fun r =>
  match r with
  | Sum.inl a => CountedQ.lift (ops (Ell.updOps s a) (Ell.update s a, b))
  | Sum.inr x =>
      objC φ μ κ γ α x >>=ᵠ fun o =>
      CountedQ.lift (ops 1 (bestUpd b (o.1, x, o.2.1))) >>=ᵠ fun b' =>
      CountedQ.lift (ops (Ell.updOps s o.2.2) (Ell.update s o.2.2, b'))

/-- `t` iterations of the method from the ellipsoid `s` with the record `b`. -/
noncomputable def ellRunC (Ell : EllMethod D σ) : ℕ → σ → BestRec D → CountedQ (σ × BestRec D)
  | 0, s, b => CountedQ.ret (s, b)
  | k + 1, s, b => ellIterC φ μ κ γ α Ell s b >>=ᵠ fun p => ellRunC Ell k p.1 p.2

/-- The ellipsoid after `k` iterations from the initial one (the update does not depend on the
record, `ellIterC_val_fst`). -/
noncomputable def ellState (Ell : EllMethod D σ) : ℕ → σ
  | 0 => Ell.init
  | k + 1 => (ellIterC φ μ κ γ α Ell (ellState Ell k) none).val.1

/-- The triples (value of the objective, point, its cost) of the centers in `K` among the first `k`
iterations. -/
def feasTriples (Ell : EllMethod D σ) (k : ℕ) : Set (ℝ × (D → ℝ) × ℝ) :=
  {p | ∃ i < k, ∃ x, (sepC φ (Ell.center (ellState φ μ κ γ α Ell i))).val = Sum.inr x ∧
    p = (κ x - α * reward μ x, x, κ x)}

variable {φ μ κ γ α}

lemma ellIterC_val_inl {Ell : EllMethod D σ} {s : σ} {a : D → ℝ}
    (hr : (sepC φ (Ell.center s)).val = Sum.inl a) (b : BestRec D) :
    (ellIterC φ μ κ γ α Ell s b).val = (Ell.update s a, b) := by
  simp [ellIterC, hr]

lemma ellIterC_val_inr {Ell : EllMethod D σ} {s : σ} {x : D → ℝ}
    (hr : (sepC φ (Ell.center s)).val = Sum.inr x) (b : BestRec D) :
    (ellIterC φ μ κ γ α Ell s b).val =
      (Ell.update s (objC φ μ κ γ α x).val.2.2, bestUpd b (κ x - α * reward μ x, x, κ x)) := by
  simp [ellIterC, hr, objC_val]

lemma ellIterC_val_fst (Ell : EllMethod D σ) (s : σ) (b : BestRec D) :
    (ellIterC φ μ κ γ α Ell s b).val.1 = (ellIterC φ μ κ γ α Ell s none).val.1 := by
  rcases hr : (sepC φ (Ell.center s)).val with a | x
  · rw [ellIterC_val_inl hr, ellIterC_val_inl hr]
  · rw [ellIterC_val_inr hr, ellIterC_val_inr hr]

/-- An iteration "makes at most one submodular minimization, at most one call of the oracle for
`c`, and `O(n²)` further arithmetic operations" (`lem:ellipsoid`): with the paper's count of the
update (`EllMethod.Cited`), at most one minimization, at most one query, at most one evaluation
of `f` (at the set `T` of the separation, which 08c-convex.tex:13 counts as an arithmetic
operation) and at most `cE n² + 9n + 4` arithmetic operations, `n = |D|` (not in the paper: the
explicit constants). -/
lemma ellIterC_cost {Ell : EllMethod D σ} {cE : ℕ} (hU : Ell.Cited cE) (s : σ) (b : BestRec D) :
    (ellIterC φ μ κ γ α Ell s b).cost.1 ≤ cE * Fintype.card D ^ 2 + 9 * Fintype.card D + 4 ∧
      (ellIterC φ μ κ γ α Ell s b).cost.2.1 ≤ 1 ∧ (ellIterC φ μ κ γ α Ell s b).cost.2.2 ≤ 1 ∧
      (ellIterC φ μ κ γ α Ell s b).queries ≤ 1 := by
  obtain ⟨h1, h2, h3⟩ := sepC_cost φ (Ell.center s)
  rcases hr : (sepC φ (Ell.center s)).val with a | x
  · have hu := hU.2 s a
    simp only [ellIterC, CountedQ.cost_bind, CountedQ.queries_bind, CountedQ.cost_lift,
      CountedQ.queries_lift, CountedQ.val_lift, hr, cost_ops]
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  · obtain ⟨ho, hq⟩ := objC_cost φ μ κ γ α x
    have hu := hU.2 s (objC φ μ κ γ α x).val.2.2
    simp only [ellIterC, CountedQ.cost_bind, CountedQ.queries_bind, CountedQ.cost_lift,
      CountedQ.queries_lift, CountedQ.val_lift, hr, cost_ops, ho, hq]
    simp only [Prod.fst_add, Prod.snd_add]
    omega

/-- `t` iterations make at most `t` minimizations, `t` queries, `t` evaluations of `f` and
`t (cE n² + 9n + 4)` arithmetic operations (`ellIterC_cost`). -/
lemma ellRunC_cost {Ell : EllMethod D σ} {cE : ℕ} (hU : Ell.Cited cE) :
    ∀ (t : ℕ) (s : σ) (b : BestRec D),
      (ellRunC φ μ κ γ α Ell t s b).cost.1 ≤
          t * (cE * Fintype.card D ^ 2 + 9 * Fintype.card D + 4) ∧
        (ellRunC φ μ κ γ α Ell t s b).cost.2.1 ≤ t ∧
        (ellRunC φ μ κ γ α Ell t s b).cost.2.2 ≤ t ∧ (ellRunC φ μ κ γ α Ell t s b).queries ≤ t
  | 0, s, b => by simp [ellRunC]
  | t + 1, s, b => by
    obtain ⟨h1, h2, h3, h4⟩ := ellIterC_cost (φ := φ) (μ := μ) (κ := κ) (γ := γ) (α := α) hU s b
    obtain ⟨k1, k2, k3, k4⟩ := ellRunC_cost hU t (ellIterC φ μ κ γ α Ell s b).val.1
      (ellIterC φ μ κ γ α Ell s b).val.2
    simp only [ellRunC, CountedQ.cost_bind, CountedQ.queries_bind, Prod.fst_add, Prod.snd_add,
      add_one_mul]
    omega

/-- The run of the method: from the ellipsoid after `j` iterations, with a record that holds the
best of the first `j` centers in `K`, `k` iterations give the ellipsoid after `j + k` iterations
and a record that holds the best of the first `j + k` centers in `K` ("the best such center
`x_t`", appF-convex.tex:136). -/
lemma ellRunC_spec (Ell : EllMethod D σ) :
    ∀ (k j : ℕ) (b : BestRec D), IsBestOf b (feasTriples φ μ κ γ α Ell j) →
      (ellRunC φ μ κ γ α Ell k (ellState φ μ κ γ α Ell j) b).val.1 =
          ellState φ μ κ γ α Ell (j + k) ∧
        IsBestOf (ellRunC φ μ κ γ α Ell k (ellState φ μ κ γ α Ell j) b).val.2
          (feasTriples φ μ κ γ α Ell (j + k))
  | 0, j, b, hb => by simpa [ellRunC] using hb
  | k + 1, j, b, hb => by
    have hs : (ellIterC φ μ κ γ α Ell (ellState φ μ κ γ α Ell j) b).val.1 =
        ellState φ μ κ γ α Ell (j + 1) := by
      rw [ellIterC_val_fst]
      rfl
    have hb' : IsBestOf (ellIterC φ μ κ γ α Ell (ellState φ μ κ γ α Ell j) b).val.2
        (feasTriples φ μ κ γ α Ell (j + 1)) := by
      rcases hr : (sepC φ (Ell.center (ellState φ μ κ γ α Ell j))).val with a | x
      · -- a cut: no new center in `K`
        rw [ellIterC_val_inl hr]
        have hv : feasTriples φ μ κ γ α Ell (j + 1) = feasTriples φ μ κ γ α Ell j := by
          ext p
          simp only [feasTriples, Set.mem_ofPred_eq]
          constructor
          · rintro ⟨i, hi, x, hx, rfl⟩
            rcases (Nat.lt_succ_iff.1 hi).lt_or_eq with hi' | rfl
            · exact ⟨i, hi', x, hx, rfl⟩
            · rw [hr] at hx
              exact absurd hx (by simp)
          · rintro ⟨i, hi, x, hx, rfl⟩
            exact ⟨i, by omega, x, hx, rfl⟩
        rw [hv]
        exact hb
      · -- a center in `K`: its triple is compared with the record
        rw [ellIterC_val_inr hr]
        have hv : feasTriples φ μ κ γ α Ell (j + 1) =
            insert (κ x - α * reward μ x, x, κ x) (feasTriples φ μ κ γ α Ell j) := by
          ext p
          simp only [feasTriples, Set.mem_ofPred_eq, Set.mem_insert_iff]
          constructor
          · rintro ⟨i, hi, x', hx', rfl⟩
            rcases (Nat.lt_succ_iff.1 hi).lt_or_eq with hi' | rfl
            · exact Or.inr ⟨i, hi', x', hx', rfl⟩
            · rw [hr, Sum.inr.injEq] at hx'
              subst hx'
              exact Or.inl rfl
          · rintro (rfl | ⟨i, hi, x', hx', rfl⟩)
            · exact ⟨j, by omega, x, hr, rfl⟩
            · exact ⟨i, by omega, x', hx', rfl⟩
        rw [hv]
        exact isBestOf_upd hb _
    obtain ⟨h1, h2⟩ := ellRunC_spec Ell k (j + 1) _ hb'
    rw [← hs] at h1 h2
    rw [show j + (k + 1) = j + 1 + k by omega]
    exact ⟨h1, h2⟩

end Counts

section Response

open Counted

variable (f m c g G rb) {σ : Type*}

/-- (1) and (4) of the proof of `lem:ellipsoid`, counted, once for all responses: "We first reduce
to the case that `f({e}) > 0` for all `e`. Let `E' := {e ∈ E : f({e}) > 0}`" (the `n` evaluations
`f({e})` and `n` comparisons), and `M := r̄ + G f(E)` (one evaluation of `f` and two operations).
These are "the `n + 1` evaluations of `f` for the coordinate bounds `f({e})` used by the ellipsoid
method and for `f(E)`" of the proof of `thm:convexfptas` (appF-convex.tex:144). Returns `E'` and
`M`. -/
noncomputable def prepC : Counted (Finset E × ℝ) :=
  vec (fun e => evalF (f {e})) >>=ᶜ fun fs =>
  ops (Fintype.card E) (univ.filter fun e => 0 < fs e) >>=ᶜ fun E' =>
  evalF (f univ) >>=ᶜ fun fE =>
  ops 2 (E', rb + G * fE)

/-- The response of the record of the method on the reduced instance: the best center `x_t` in `K`,
padded with zeros, with `c(x_t)`; `0` with `c(0) = 0` if no center lies in `K`. -/
noncomputable def recResp : BestRec {e // e ∈ posElems f} → (E → ℝ) × ℝ
  | none => (0, 0)
  | some p => (pad f p.2.1, p.2.2)

/-- One response of `lem:ellipsoid` at the share `α` with the precision `δ`, counted, after
`prepC`, which gives `P = (E', M)`: if `δ < M` and `E' ≠ ∅` (two comparisons), the method with
`t = ⌈2n² ln(2n^{3/2} M/δ)⌉` iterations (`t` taken from `ellipsoidIters` at no cost, see the
module docstring) on the reduced instance on `E'` (the rank function `f|E'`,
the rewards `m|E'`, the cost `c ∘ pad` and the subgradients `g ∘ pad`), starting from the initial
ellipsoid, and its best center `x_t`, padded with zeros, with `c(x_t)`; otherwise the response `0`
("If `E' = ∅`, then `P₊(f) = {0}` and there is nothing to compute", and "If `δ ≥ M`, then
`V(α) − U_A(0 | α) = V(α) ≤ r̄ ≤ δ`"). -/
noncomputable def respC (Ell : EllMethod {e // e ∈ posElems f} σ) (P : Finset E × ℝ)
    (α δ : ℝ) : CountedQ ((E → ℝ) × ℝ) :=
  CountedQ.lift (ops 2 ()) >>=ᵠ fun _ =>
  if δ < P.2 ∧ P.1.Nonempty then
    CountedQ.lift (ops Ell.initOps Ell.init) >>=ᵠ fun s0 =>
    ellRunC (restrictRank f) (fun e => m e.1) (fun y => c (pad f y)) (fun y e => g (pad f y) e.1)
      α Ell (ellipsoidIters (Fintype.card E) P.2 δ) s0 none >>=ᵠ fun p =>
    CountedQ.ret (recResp f p.2)
  else CountedQ.ret (0, 0)

/-- The center of the ellipsoid after `i` iterations of the method on the reduced instance. -/
noncomputable def ellCenter (Ell : EllMethod {e // e ∈ posElems f} σ) (α : ℝ) (i : ℕ) :
    {e // e ∈ posElems f} → ℝ :=
  Ell.center (ellState (restrictRank f) (fun e => m e.1) (fun y => c (pad f y))
    (fun y e => g (pad f y) e.1) α Ell i)

/-- `x` is the best center of the first `t` iterations of the method on the reduced instance,
padded with zeros, "the best such center `x_t`" (appF-convex.tex:136): no center lies in `K` and
`x = 0`, or `x` is a center in `K` (in the coordinates `x = (f({e}) y_e)_e`, padded) at which
`U_A(· | α)` is at least its value at every center in `K`. -/
def IsBestCenter (Ell : EllMethod {e // e ∈ posElems f} σ) (α : ℝ) (t : ℕ) (x : E → ℝ) : Prop :=
  ((∀ i < t, ellCenter f m c g Ell α i ∉ scaledPoly (restrictRank f)) ∧ x = 0) ∨
    ((∃ i < t, ellCenter f m c g Ell α i ∈ scaledPoly (restrictRank f) ∧
        x = pad f fun e => restrictRank f {e} * ellCenter f m c g Ell α i e) ∧
      ∀ i < t, ellCenter f m c g Ell α i ∈ scaledPoly (restrictRank f) →
        util m c α (pad f fun e => restrictRank f {e} * ellCenter f m c g Ell α i e) ≤
          util m c α x)

/-- The bound of the method, cited ([Bub15, Thm. 2.4], appF-convex.tex:136), for the run of `Ell`
on the reduced instance with `t` iterations: "some center lies in the body, and the best such center
`x_t` is within `(2M R_out/R_in) exp(−t/(2n²))` of the minimum", with `R_out/R_in = n^{3/2}` and
`n = |E|`. The citation gives this for the ellipsoid method in dimension `|E'| ≤ |E|`, with the
ratio `|E'|^{3/2}`, for `t ≥ 2|E'|² ln(|E'|^{3/2})` (`ellipsoidIters_ge`); that bound implies this
one, as `|E'|^{3/2} exp(−t/(2|E'|²)) ≤ n^{3/2} exp(−t/(2n²))`. As some center lies in `K`, the
bound concerns only best centers in `K` (`IsBestCenter`). A hypothesis on `Ell`, as the method is
not formalised. -/
def EllConverges (Ell : EllMethod {e // e ∈ posElems f} σ) (α M : ℝ) (t : ℕ) : Prop :=
  (∃ i < t, ellCenter f m c g Ell α i ∈ scaledPoly (restrictRank f)) ∧
    ∀ x, IsBestCenter f m c g Ell α t x →
      V (indepPoly f) m c α - util m c α x ≤
        2 * M * (Fintype.card E : ℝ) ^ (3 / 2 : ℝ) *
          Real.exp (-(t : ℝ) / (2 * (Fintype.card E : ℝ) ^ 2))

/-- `lem:ellipsoid`, counted: `prepC`, then `respC`. -/
noncomputable def ellipsoidC (Ell : EllMethod {e // e ∈ posElems f} σ) (α δ : ℝ) :
    CountedQ ((E → ℝ) × ℝ) :=
  CountedQ.lift (prepC f G rb) >>=ᵠ fun P => respC f m c g Ell P α δ

variable {f m c g G rb}

omit [DecidableEq E] in
lemma prepC_val : (prepC f G rb).val = (posElems f, rb + G * f univ) := rfl

omit [DecidableEq E] in
/-- The cost of `prepC`: `n + 1` evaluations of `f` and `n + 2` arithmetic operations. -/
lemma prepC_cost : (prepC f G rb).cost = (Fintype.card E + 2, 0, Fintype.card E + 1) := by
  simp [prepC]

/-- The response is a point of `P₊(f)` with its exact cost ("returns such an action, together with
its exact reward and cost", 08c-convex.tex:4; the reward is computed by the caller), and for
`δ < M` and `E' ≠ ∅` it is the best center `x_t` of the `t` iterations (`IsBestCenter`); by (1) the
centers in `K` give points of `P₊(f)` (`sepC_inr`, `pad_mem`). -/
lemma respC_spec (h : PolySetting f m c g G rb) (Ell : EllMethod {e // e ∈ posElems f} σ)
    (M α δ : ℝ) :
    (respC f m c g Ell (posElems f, M) α δ).val.1 ∈ indepPoly f ∧
      (respC f m c g Ell (posElems f, M) α δ).val.2 =
        c (respC f m c g Ell (posElems f, M) α δ).val.1 ∧
      (δ < M → (posElems f).Nonempty → IsBestCenter f m c g Ell α
        (ellipsoidIters (Fintype.card E) M δ) (respC f m c g Ell (posElems f, M) α δ).val.1) := by
  set φ := restrictRank f
  set μ : {e // e ∈ posElems f} → ℝ := fun e => m e.1
  set κ : ({e // e ∈ posElems f} → ℝ) → ℝ := fun y => c (pad f y)
  set γ : ({e // e ∈ posElems f} → ℝ) → {e // e ∈ posElems f} → ℝ := fun y e => g (pad f y) e.1
  set t := ellipsoidIters (Fintype.card E) M δ
  by_cases hcond : δ < M ∧ (posElems f).Nonempty
  · have hval : (respC f m c g Ell (posElems f, M) α δ).val =
        recResp f (ellRunC φ μ κ γ α Ell t Ell.init none).val.2 := by
      simp [respC, hcond]
      rfl
    have h0 : IsBestOf (none : BestRec {e // e ∈ posElems f}) (feasTriples φ μ κ γ α Ell 0) :=
      ⟨fun _ => by ext p; simp [feasTriples], fun p hp => by simp at hp⟩
    obtain ⟨-, hrec⟩ := ellRunC_spec Ell t 0 none h0
    rw [zero_add] at hrec
    have hs0 : ellState φ μ κ γ α Ell 0 = Ell.init := rfl
    rw [hs0] at hrec
    rw [hval]
    rcases hb : (ellRunC φ μ κ γ α Ell t Ell.init none).val.2 with _ | ⟨v, x, cx⟩
    · -- no center in `K`: the response `0`
      rw [hb] at hrec
      have hempty := hrec.1 rfl
      refine ⟨zero_mem_indepPoly h.rank, h.cost.zero.symm,
        fun _ _ => Or.inl ⟨fun i hi hK => ?_, rfl⟩⟩
      have hsep := sepC_of_mem hK
      have : (κ (fun e => φ {e} * ellCenter f m c g Ell α i e) -
          α * reward μ (fun e => φ {e} * ellCenter f m c g Ell α i e),
          (fun e => φ {e} * ellCenter f m c g Ell α i e),
          κ (fun e => φ {e} * ellCenter f m c g Ell α i e)) ∈ feasTriples φ μ κ γ α Ell t :=
        ⟨i, hi, _, hsep, rfl⟩
      rw [hempty] at this
      exact this
    · -- the best center in `K`
      rw [hb] at hrec
      obtain ⟨⟨i, hi, x', hx', hp⟩, hmin⟩ := hrec.2 _ rfl
      simp only [Prod.mk.injEq] at hp
      obtain ⟨hv, rfl, hcx⟩ := hp
      obtain ⟨hxeq, hK⟩ := sepC_inr hx'
      have hxmem : x ∈ indepPoly φ := by rw [hxeq]; exact hK
      refine ⟨pad_mem h.rank hxmem, hcx, fun _ _ => Or.inr ⟨⟨i, hi, hK, by rw [hxeq]; rfl⟩,
        fun i' hi' hK' => ?_⟩⟩
      have hsep := sepC_of_mem hK'
      have hq := hmin _ ⟨i', hi', _, hsep, rfl⟩
      simp only [recResp]
      rw [hv] at hq
      simp only [util, reward_pad]
      have e1 : c (pad f fun e => φ {e} * ellCenter f m c g Ell α i' e) =
          κ (fun e => φ {e} * ellCenter f m c g Ell α i' e) := rfl
      have e2 : c (pad f x) = κ x := rfl
      rw [e1, e2]
      linarith
  · have hval : (respC f m c g Ell (posElems f, M) α δ).val = (0, 0) := by
      simp [respC, hcond]
    rw [hval]
    exact ⟨zero_mem_indepPoly h.rank, h.cost.zero.symm, fun h1 h2 => absurd ⟨h1, h2⟩ hcond⟩

/-- The cost of a response: at most `t` minimizations, `t` queries and `t` evaluations of `f`, and
at most `cE n² + 2 + t (cE n² + 9n + 4)` arithmetic operations, for
`t = ⌈2n² ln(2n^{3/2} M/δ)⌉` and `n = |E| ≥ |E'|` (`ellRunC_cost`, `card_posElems_le`). -/
lemma respC_cost {Ell : EllMethod {e // e ∈ posElems f} σ} {cE : ℕ} (hU : Ell.Cited cE)
    (P : Finset E × ℝ) (α δ : ℝ) :
    (respC f m c g Ell P α δ).cost.1 ≤ cE * Fintype.card E ^ 2 + 2 +
        ellipsoidIters (Fintype.card E) P.2 δ *
          (cE * Fintype.card E ^ 2 + 9 * Fintype.card E + 4) ∧
      (respC f m c g Ell P α δ).cost.2.1 ≤ ellipsoidIters (Fintype.card E) P.2 δ ∧
      (respC f m c g Ell P α δ).cost.2.2 ≤ ellipsoidIters (Fintype.card E) P.2 δ ∧
      (respC f m c g Ell P α δ).queries ≤ ellipsoidIters (Fintype.card E) P.2 δ := by
  have hn : Fintype.card {e // e ∈ posElems f} ≤ Fintype.card E := card_posElems_le
  have hn2 : cE * Fintype.card {e // e ∈ posElems f} ^ 2 ≤ cE * Fintype.card E ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn 2)
  have hper : cE * Fintype.card {e // e ∈ posElems f} ^ 2 +
      9 * Fintype.card {e // e ∈ posElems f} + 4 ≤
      cE * Fintype.card E ^ 2 + 9 * Fintype.card E + 4 := by omega
  by_cases hcond : P.2 > δ ∧ P.1.Nonempty
  · obtain ⟨k1, k2, k3, k4⟩ := ellRunC_cost (φ := restrictRank f) (μ := fun e => m e.1)
      (κ := fun y => c (pad f y)) (γ := fun y e => g (pad f y) e.1) (α := α) hU
      (ellipsoidIters (Fintype.card E) P.2 δ) Ell.init none
    have hmul := Nat.mul_le_mul_left (ellipsoidIters (Fintype.card E) P.2 δ) hper
    have hinit := hU.1
    simp only [respC, CountedQ.cost_bind, CountedQ.queries_bind, CountedQ.cost_lift,
      CountedQ.queries_lift, CountedQ.val_lift, cost_ops, val_ops, gt_iff_lt.1 hcond.1, hcond.2,
      and_self, ite_true, CountedQ.cost_ret, CountedQ.queries_ret, Prod.fst_add, Prod.snd_add]
    simp only [Prod.fst_zero, Prod.snd_zero, add_zero]
    omega
  · have hc : ¬ (δ < P.2 ∧ P.1.Nonempty) := hcond
    simp only [respC, CountedQ.cost_bind, CountedQ.queries_bind, CountedQ.cost_lift,
      CountedQ.queries_lift, cost_ops, hc, ite_false, CountedQ.cost_ret, CountedQ.queries_ret,
      add_zero]
    omega

/-- `lem:ellipsoid`, counted (not in the paper: the paper counts in prose): `ellipsoidC` returns a
point of `P₊(f)` with its exact cost, for `δ < M` and `E' ≠ ∅` the best center `x_t` of the
`t = ⌈2n² ln(2n^{3/2} M/δ)⌉` iterations, padded with zeros, with at most `t` submodular
minimizations, at most `t` queries of the oracle for `c`, at most `n + 1 + t` evaluations of `f`
(the `n + 1` of `prepC` and one in each iteration) and at most
`t (cE n² + 9n + 4) + cE n² + n + 4` further arithmetic operations. -/
lemma ellipsoidC_spec (h : PolySetting f m c g G rb) (Ell : EllMethod {e // e ∈ posElems f} σ)
    {cE : ℕ} (hU : Ell.Cited cE) (α δ : ℝ) :
    (ellipsoidC f m c g G rb Ell α δ).val.1 ∈ indepPoly f ∧
      (ellipsoidC f m c g G rb Ell α δ).val.2 = c (ellipsoidC f m c g G rb Ell α δ).val.1 ∧
      (δ < rb + G * f univ → (posElems f).Nonempty → IsBestCenter f m c g Ell α
        (ellipsoidIters (Fintype.card E) (rb + G * f univ) δ)
        (ellipsoidC f m c g G rb Ell α δ).val.1) ∧
      (ellipsoidC f m c g G rb Ell α δ).cost.2.1 ≤
        ellipsoidIters (Fintype.card E) (rb + G * f univ) δ ∧
      (ellipsoidC f m c g G rb Ell α δ).queries ≤
        ellipsoidIters (Fintype.card E) (rb + G * f univ) δ ∧
      (ellipsoidC f m c g G rb Ell α δ).cost.2.2 ≤
        Fintype.card E + 1 + ellipsoidIters (Fintype.card E) (rb + G * f univ) δ ∧
      (ellipsoidC f m c g G rb Ell α δ).cost.1 ≤
        ellipsoidIters (Fintype.card E) (rb + G * f univ) δ *
            (cE * Fintype.card E ^ 2 + 9 * Fintype.card E + 4) +
          cE * Fintype.card E ^ 2 + Fintype.card E + 4 := by
  have hval : (ellipsoidC f m c g G rb Ell α δ).val =
      (respC f m c g Ell (posElems f, rb + G * f univ) α δ).val := rfl
  obtain ⟨v1, v2, v3⟩ := respC_spec h Ell (rb + G * f univ) α δ
  obtain ⟨k1, k2, k3, k4⟩ := respC_cost (f := f) (m := m) (c := c) (g := g) hU
    (posElems f, rb + G * f univ) α δ
  dsimp only at k1 k2 k3 k4
  have hcost : (ellipsoidC f m c g G rb Ell α δ).cost =
      (prepC f G rb).cost + (respC f m c g Ell (posElems f, rb + G * f univ) α δ).cost := rfl
  have hq : (ellipsoidC f m c g G rb Ell α δ).queries =
      (respC f m c g Ell (posElems f, rb + G * f univ) α δ).queries := by
    simp only [ellipsoidC, CountedQ.queries_bind, CountedQ.queries_lift, zero_add,
      CountedQ.val_lift, prepC_val]
  rw [hval]
  refine ⟨v1, v2, v3, ?_, ?_, ?_, ?_⟩
  · rw [hcost, prepC_cost]
    simpa using k2
  · rw [hq]
    exact k4
  · rw [hcost, prepC_cost]
    simp only [Prod.snd_add]
    omega
  · rw [hcost, prepC_cost]
    simp only [Prod.fst_add]
    omega

/-- `lem:ellipsoid`: "the central-cut ellipsoid method computes a `δ`-optimal response at `α`"
(appF-convex.tex:124), for the counted method `ellipsoidC`, under the cited bound for its run
(`EllConverges`): for `0 < δ < M` and `E' ≠ ∅` its point, the best center `x_t` of
`t = ⌈2n² ln(2n^{3/2} M/δ)⌉` iterations (`ellipsoidC_spec`), is a `δ`-optimal response, as "this
gives `U_A(x_t | α) ≥ V(α) − δ`" (`ellipsoid_bound_le`). -/
lemma ellipsoidC_isDeltaOpt [Nonempty E] (h : PolySetting f m c g G rb)
    (Ell : EllMethod {e // e ∈ posElems f} σ) {cE : ℕ} (hU : Ell.Cited cE) {α δ : ℝ}
    (hδ : 0 < δ) (hδM : δ < rb + G * f univ) (hE : (posElems f).Nonempty)
    (hC : EllConverges f m c g Ell α (rb + G * f univ)
      (ellipsoidIters (Fintype.card E) (rb + G * f univ) δ)) :
    IsDeltaOpt (indepPoly f) m c α δ (ellipsoidC f m c g G rb Ell α δ).val.1 := by
  obtain ⟨hmem, -, hbest, -⟩ := ellipsoidC_spec h Ell hU α δ
  have hb := hC.2 _ (hbest hδM hE)
  have := ellipsoid_bound_le (Fintype.card_pos (α := E)) hδ hδM
  exact ⟨hmem, by linarith⟩

end Response

/-- **`lem:ellipsoid`** (Lemma D.8, appF-convex.tex:123-125, proof 127-137): "Let `α ∈ [0, 1]` and
`0 < δ < r̄ + G f(E)`. Then the central-cut ellipsoid method computes a `δ`-optimal response at `α`
with at most `⌈2n² ln(2n^{3/2}(r̄ + G f(E))/δ)⌉` iterations, each of which makes at most one
submodular minimization, at most one call of the oracle for `c`, and `O(n²)` further arithmetic
operations. For `δ ≥ r̄ + G f(E)`, the response `0` is `δ`-optimal."

Here, as far as it is formalised (see the module docstring): let `α ∈ [0, 1]`, `M = r̄ + G f(E)`
and `n = |E| ≥ 1` (the ground set is nonempty: "Let `E` be a finite nonempty ground set",
02-preliminaries.tex:4).
(i) The reduction of (1), "we may assume that `f({e}) > 0` for all `e ∈ E`": the reduced instance on
`E' = {e : f({e}) > 0}` (the rank function `f|E'`, the rewards `m|E'`, the cost `c ∘ pad` and the
subgradients `g ∘ pad` on `E'`, where `pad` pads with zeros) lies in the setting of `sec:convex`
with the same `G` and `r̄`, has `f|E'({e}) > 0` for all `e ∈ E'`, the same `f(E)` (so the same `M`)
and at most `n` elements, and `y` is a `δ`-optimal response at `α` of it if and only if `pad(y)` is
one of the original instance; "If `E' = ∅`, then `P₊(f) = {0}`".
(ii) If `0 < δ < M`, the number `t = ⌈2n² ln(2n^{3/2} M/δ)⌉` is positive and exceeds
`2n² ln(R_out/R_in)` for `R_out/R_in = n^{3/2}` (the radii of (2), which needs
`f({e}) > 0`: `ball_subset_scaledPoly`, `scaledPoly_subset_ball`, `radii_ratio`), and every
`x ∈ P₊(f)` within the bound `(2M R_out/R_in) exp(−t/(2n²))` of the ellipsoid method of the optimum,
that is, `V(α) − U_A(x | α) ≤ 2M n^{3/2} exp(−t/(2n²))` (the cited bound for the best center after
`t` iterations, Bubeck, Thm. 2.4, here a hypothesis on `x`), is a `δ`-optimal response at `α`: "this
gives `U_A(x_t | α) ≥ V(α) − δ`, so `x_t` is a `δ`-optimal response".
(iii) "For `δ ≥ r̄ + G f(E)`, the response `0` is `δ`-optimal" (`zero_isDeltaOpt`).
(iv) The counts, for the method as a parameter (`EllMethod`: its ellipsoids, centers and updates
on the reduced instance, cited) with at most `cE n²` operations for each update (the paper's
count `O(n²)`, not cited) and for the initial ellipsoid (not in the paper) (`EllMethod.Cited`):
the cuts of the counted separation `sepC` are central cuts through the center that contain `K`,
with nonzero normals; where it finds no cut, the center lies in `K` and the normal of the counted
method is the subgradient of `c − α r` in the coordinates `y`; "each" iteration `ellIterC` "makes at
most one submodular minimization, at most one call of the oracle for `c`" and at most one evaluation
of `f`, which 08c-convex.tex:13 counts as an arithmetic operation, and at most `cE n² + 9n + 4`
further arithmetic operations (the `O(n²)`); and the counted method `ellipsoidC` returns a point `x`
of `P₊(f)` with its cost `c(x)`, for `δ < M` and `E' ≠ ∅` the best center `x_t` in `K` of
`t = ⌈2n² ln(2n^{3/2} M/δ)⌉` iterations, padded with zeros (`IsBestCenter`), with at most `t`
minimizations, `t` calls of the oracle for `c`, `n + 1 + t` evaluations of `f` (the `n + 1` of
`f({e})` and `f(E)`, and one per iteration), and at most `t (cE n² + 9n + 4) + cE n² + n + 4`
further arithmetic operations (not in the paper: the explicit constants; the paper counts in prose);
if the run of the parameter attains the cited bound (`EllConverges`, a hypothesis), then for
`0 < δ < M` and `E' ≠ ∅` this point is a `δ`-optimal response (`ellipsoidC_isDeltaOpt`).

The proof follows the paragraphs (1) to (5) of the STOC version's (see the module docstring): (1)
"We first reduce to the case that `f({e}) > 0` for all `e`" (`PolySetting.restrict`,
`restrictRank_singleton_pos`, `restrictRank_univ`, `card_posElems_le`,
`isDeltaOpt_pad_iff`, `indepPoly_eq_zero`); (5) "Finally, we apply the ellipsoid method": "For
`t := ⌈2n² ln(2n^{3/2} M/δ)⌉`, which is positive and exceeds `2n² ln(n^{3/2})` since `δ < M`, this
gives `U_A(x_t | α) ≥ V(α) − δ`" (`ellipsoidIters_ge`, `ellipsoid_bound_le`), and "If `δ ≥ M`, then
`V(α) − U_A(0 | α) = V(α) ≤ r̄ ≤ δ`" (`zero_isDeltaOpt`). The paper takes `n` after the reduction,
where `E' ≠ ∅`, as otherwise "there is nothing to compute"; the Lean states (ii) with `n = |E|`,
which is at least `|E'|`. The paragraphs (2) "Next we place `P₊(f)` between two cubes" and (4)
"Next we bound the objective" state the facts on which the method is run (`ball_subset_scaledPoly`,
`scaledPoly_subset_ball`, `radii_ratio`, `convexOn_cost_sub`, `cost_le`, `abs_util_le`); as the
method is not formalised, `ellipsoid` does not use them. (iv) follows (3) "A separation oracle
needs one submodular minimization" (`sepC`, with `sepC_inl` from `separation_normalized` and
`sepC_inr` from `separation`), the subgradient of (4) scaled as in (5) (`objC_subgrad`, from
`subgrad_cost_sub` and `subgrad_scaled`), and (5) "The values of `c` at the centers in `P₊(f)`
select `x_t`, and each iteration updates the ellipsoid with `O(n²)` operations" (`ellIterC_cost`,
`ellipsoidC_spec`). Not formalised: the method and the cited bound. `respC` takes
`t = ellipsoidIters n M δ` from its definition at no cost (computing it needs `ln` and `⌈·⌉`, which
are not operations of the model of 08c-convex.tex:13; the paper does not count it). -/
theorem ellipsoid [Nonempty E] (h : PolySetting f m c g G rb) {α δ : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    (PolySetting (restrictRank f) (fun e : {e // e ∈ posElems f} => m e.1) (fun y => c (pad f y))
        (fun y e => g (pad f y) e.1) G rb ∧
      (∀ e : {e // e ∈ posElems f}, 0 < restrictRank f {e}) ∧
      restrictRank f univ = f univ ∧ Fintype.card {e // e ∈ posElems f} ≤ Fintype.card E ∧
      (∀ y, IsDeltaOpt (indepPoly (restrictRank f)) (fun e : {e // e ∈ posElems f} => m e.1)
          (fun y => c (pad f y)) α δ y ↔ IsDeltaOpt (indepPoly f) m c α δ (pad f y)) ∧
      (posElems f = ∅ → indepPoly f = {0})) ∧
    (0 < δ → δ < rb + G * f univ →
      0 < ellipsoidIters (Fintype.card E) (rb + G * f univ) δ ∧
      2 * (Fintype.card E : ℝ) ^ 2 * Real.log ((Fintype.card E : ℝ) ^ (3 / 2 : ℝ)) <
        ellipsoidIters (Fintype.card E) (rb + G * f univ) δ ∧
      ∀ x ∈ indepPoly f, V (indepPoly f) m c α - util m c α x ≤
          2 * (rb + G * f univ) * (Fintype.card E : ℝ) ^ (3 / 2 : ℝ) *
            Real.exp (-(ellipsoidIters (Fintype.card E) (rb + G * f univ) δ : ℝ) /
              (2 * (Fintype.card E : ℝ) ^ 2)) →
        IsDeltaOpt (indepPoly f) m c α δ x) ∧
    (rb + G * f univ ≤ δ → IsDeltaOpt (indepPoly f) m c α δ 0) ∧
    (∀ {σ : Type*} (Ell : EllMethod {e // e ∈ posElems f} σ) (cE : ℕ), Ell.Cited cE →
      (∀ y a, (sepC (restrictRank f) y).val = Sum.inl a → a ≠ 0 ∧
        ∀ y' ∈ scaledPoly (restrictRank f), ∑ e, a e * y' e ≤ ∑ e, a e * y e) ∧
      (∀ y x, (sepC (restrictRank f) y).val = Sum.inr x →
        x = (fun e => restrictRank f {e} * y e) ∧ y ∈ scaledPoly (restrictRank f) ∧
        ∀ y' ∈ scaledPoly (restrictRank f),
          (objC (restrictRank f) (fun e => m e.1) (fun y => c (pad f y))
              (fun y e => g (pad f y) e.1) α x).val.1 +
            ∑ e, (objC (restrictRank f) (fun e => m e.1) (fun y => c (pad f y))
              (fun y e => g (pad f y) e.1) α x).val.2.2 e * (y' e - y e) ≤
          c (pad f fun e => restrictRank f {e} * y' e) -
            α * reward (fun e => m e.1) (fun e => restrictRank f {e} * y' e)) ∧
      (∀ s b,
        let it := ellIterC (restrictRank f) (fun e => m e.1) (fun y => c (pad f y))
          (fun y e => g (pad f y) e.1) α Ell s b
        it.cost.1 ≤ cE * Fintype.card E ^ 2 + 9 * Fintype.card E + 4 ∧ it.cost.2.1 ≤ 1 ∧
          it.cost.2.2 ≤ 1 ∧ it.queries ≤ 1) ∧
      (0 < δ → δ < rb + G * f univ → (posElems f).Nonempty →
        EllConverges f m c g Ell α (rb + G * f univ)
          (ellipsoidIters (Fintype.card E) (rb + G * f univ) δ) →
        IsDeltaOpt (indepPoly f) m c α δ (ellipsoidC f m c g G rb Ell α δ).val.1) ∧
      let R := ellipsoidC f m c g G rb Ell α δ
      let t := ellipsoidIters (Fintype.card E) (rb + G * f univ) δ
      R.val.1 ∈ indepPoly f ∧ R.val.2 = c R.val.1 ∧
      (δ < rb + G * f univ → (posElems f).Nonempty → IsBestCenter f m c g Ell α t R.val.1) ∧
      R.cost.2.1 ≤ t ∧ R.queries ≤ t ∧ R.cost.2.2 ≤ Fintype.card E + 1 + t ∧
      R.cost.1 ≤ t * (cE * Fintype.card E ^ 2 + 9 * Fintype.card E + 4) +
        cE * Fintype.card E ^ 2 + Fintype.card E + 4) := by
  -- (1) "We first reduce to the case that `f({e}) > 0` for all `e`. … So `P₊(f)` is `P₊(f|E')`,
  -- padded with zeros, and we may assume that `f({e}) > 0` for all `e ∈ E`. If `E' = ∅`, then
  -- `P₊(f) = {0}` and there is nothing to compute."
  refine ⟨⟨h.restrict, restrictRank_singleton_pos, restrictRank_univ h.rank, card_posElems_le,
    isDeltaOpt_pad_iff h.rank m c α δ, indepPoly_eq_zero h.rank⟩, fun hδ hδM => ?_,
    zero_isDeltaOpt h hα, ?_⟩
  -- `n ≥ 1`, as the ground set is nonempty (02-preliminaries.tex:4)
  have hn : 1 ≤ Fintype.card E := Fintype.card_pos
  -- (5) "Finally, we apply the ellipsoid method. … For `t := ⌈2n² ln(2n^{3/2} M/δ)⌉`, which is
  -- positive and exceeds `2n² ln(n^{3/2})` since `δ < M`,"
  obtain ⟨h1, h2⟩ := ellipsoidIters_ge hn hδ hδM
  refine ⟨h1, h2, fun x hx hbound => ⟨hx, ?_⟩⟩
  -- "this gives `U_A(x_t | α) ≥ V(α) − δ`, so `x_t` is a `δ`-optimal response."
  have := ellipsoid_bound_le hn hδ hδM
  linarith
  -- (3) "A separation oracle needs one submodular minimization." (5) "The values of `c` at the
  -- centers in `P₊(f)` select `x_t`, and each iteration updates the ellipsoid with `O(n²)`
  -- operations." The counted method, with the method as a parameter and the paper's count of an
  -- update as a hypothesis (not in the paper: the paper counts in prose).
  intro σ Ell cE hU
  refine ⟨fun y a ha => sepC_inl (isRankFunction_restrictRank h.rank)
    restrictRank_singleton_pos ha, fun y x hx => ?_, fun s b => ?_,
    fun hδ hδM hE hC => ellipsoidC_isDeltaOpt h Ell hU hδ hδM hE hC, ellipsoidC_spec h Ell hU α δ⟩
  · -- (3) "or it shows `z ∈ P₊(f)`", and then the subgradient of (4) in the coordinates of (5)
    obtain ⟨rfl, hK⟩ := sepC_inr hx
    exact ⟨rfl, hK, objC_subgrad h.restrict α hK⟩
  · -- an iteration, with `|E'| ≤ |E| = n`
    obtain ⟨k1, k2, k3, k4⟩ := ellIterC_cost (φ := restrictRank f) (μ := fun e => m e.1)
      (κ := fun y => c (pad f y)) (γ := fun y e => g (pad f y) e.1) (α := α) hU s b
    have hn : Fintype.card {e // e ∈ posElems f} ≤ Fintype.card E := card_posElems_le
    have hn2 : cE * Fintype.card {e // e ∈ posElems f} ^ 2 ≤ cE * Fintype.card E ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn 2)
    exact ⟨by omega, k2, k3, k4⟩

end Method

end Stoc.Convex
