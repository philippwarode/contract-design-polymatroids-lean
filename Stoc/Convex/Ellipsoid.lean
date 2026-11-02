-- stamp r7 2026-11-02
import Stoc.Convex.Model

/-!
# Convex costs: computing `δ`-optimal responses (`lem:ellipsoid`)

The STOC version's `lem:ellipsoid` (`sec:F-ellipsoid`, `stoc-sections/appF-convex.tex`:120-142),
in the exact real-arithmetic model of `sec:convex` (08c-convex.tex:13, appF-convex.tex:124):
submodular minimizations, exact calls of the oracle for `c` at feasible real ellipsoid centers,
exact separating cuts, subgradients and objective values; "its proof does not establish a
finite-precision implementation" (appF-convex.tex:142).

What is formalised, paragraph by paragraph of the proof (appF-convex.tex:130-140), which we number
(1) to (5):
* (1) "We first reduce to the case that `f({e}) > 0` for all `e`" (appF:131):
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
* (2) "Next we place `P₊(f)` between two cubes" (appF:133): in the coordinates `y_e = x_e/f({e})`
  (`scaledPoly`), `[0, 1/n]^E ⊆ K ⊆ [0, 1]^E` (`box_subset_scaledPoly`, `scaledPoly_subset_box`),
  so `K` contains the ball of radius `1/(2n)` about `(1/(2n)) 𝟙` (`ball_subset_scaledPoly`) and
  lies in the ball of radius `√n/2` about `(1/2) 𝟙` (`scaledPoly_subset_ball`), and the ratio of
  the radii is `n^{3/2}` (`radii_ratio`).
* (3) "A separation oracle needs one submodular minimization" (appF:135): `separation`.
* (4) "Next we bound the objective" (appF:137): `c − α r` is convex on `P₊(f)` with the subgradient
  `g(x) − α m` (`convexOn_cost_sub`, `subgrad_cost_sub`); `0 ≤ c(x) ≤ G x(E) ≤ G f(E)` (`cost_le`,
  with `PolySetting.G_mul_le`), and `|U_A(· | α)| ≤ M = r̄ + G f(E)` on `P₊(f)` (`abs_util_le`).
* (5) "Finally, we apply the ellipsoid method" (appF:139): the subgradients in the coordinates `y`
  are scaled by `f({e})` (`subgrad_scaled`); `t = ⌈2n² ln(2n^{3/2} M/δ)⌉` (`ellipsoidIters`) is at
  least `2n² ln(2n^{3/2}) ≥ 1` and at least `2n² ln(R_out/R_in)` (`ellipsoidIters_ge`); the bound
  `(2M R_out/R_in) exp(−t/(2n²))` is at most `δ` (`ellipsoid_bound_le`), which makes a point within
  this bound of the optimum `δ`-optimal; for `δ ≥ M` the response `0` is `δ`-optimal
  (`zero_isDeltaOpt`, with `G f(E) ≥ 0`, `PolySetting.G_mul_nonneg`). `ellipsoid` collects (1)
  and (5).

Not formalised: the central-cut ellipsoid method and the bound it attains (Bubeck, Thm. 2.4, which
the STOC version cites for a convex body in a ball of radius `R_out` that contains a ball of radius
`R_in`, and a continuous convex function with absolute values at most `M` on it: after
`t ≥ 2n² ln(R_out/R_in)` iterations, some center lies in the body, and the best such center is
within `(2M R_out/R_in) exp(−t/(2n²))` of the minimum), bisection in dimension one, how the values
of `c` select the best center, and the counts per iteration (at most one submodular minimization, at
most one call of the oracle for `c`, `O(n²)` further arithmetic operations). In `ellipsoid` the
cited bound enters as a hypothesis on the returned point. So the lemma's claim that the method
computes a `δ`-optimal response within `t` iterations is not proved here: what is proved is that a
point satisfying the cited bound for `t` iterations is `δ`-optimal,
and that `t` meets the bound's requirement `t ≥ 2n² ln(R_out/R_in)`. Hence the lemmas of the
paragraphs (2), (3) and (4) and of the scaling of the subgradients in (5)
(`box_subset_scaledPoly`, `scaledPoly_subset_box`, `ball_subset_scaledPoly`,
`scaledPoly_subset_ball`, `radii_ratio`, `separation`, `convexOn_cost_sub`, `subgrad_cost_sub`,
`cost_le`, `abs_util_le`, `subgrad_scaled`) are not used by `ellipsoid`: they state the facts on
which the method is run.

The lemmas of (2) were taken over on 2026-10-20 from `Research/S14/Inner.lean` (series 14,
`lem:cvxround`) for the STOC version (`stoc.tex`); from then on this copy follows the STOC version.
-/

namespace Stoc.Convex

open Finset

variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ### (1) The reduction to `f({e}) > 0` -/

section Reduction

variable {f : Finset E → ℝ}

/-- `E' = {e ∈ E : f({e}) > 0}` (appF-convex.tex:131). -/
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

/-- (1) of the proof of `lem:ellipsoid` (appF-convex.tex:131): `f(S) = f(S ∩ E')` for all `S ⊆ E`,
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
/-- (1) of the proof of `lem:ellipsoid` (appF-convex.tex:131): "For `e ∉ E'`, every `x ∈ P₊(f)` has
`x_e = 0`." -/
lemma eq_zero_of_not_mem_posElems {x : E → ℝ} (hx : x ∈ indepPoly f) {e : E}
    (he : e ∉ posElems f) : x e = 0 := by
  have h1 : ¬ 0 < f {e} := by simpa [posElems] using he
  have h2 : x e ≤ f {e} := by simpa using hx.2 {e}
  exact le_antisymm (by linarith [not_lt.1 h1]) (hx.1 e)

/-- The restriction `f|E'` of `f` to the subsets of `E'` (appF-convex.tex:131). -/
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

/-- (1) of the proof of `lem:ellipsoid` (appF-convex.tex:131): "So `P₊(f)` is `P₊(f|E')`, padded
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

/-- (1) of the proof of `lem:ellipsoid` (appF-convex.tex:131): "If `E' = ∅`, then `P₊(f) = {0}`." -/
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

/-- The image `K` of `P₊(f)` in the coordinates `y_e = x_e/f({e})` (appF-convex.tex:133): `y ∈ K` if
and only if `x = (f({e}) y_e)_e ∈ P₊(f)`. -/
def scaledPoly (f : Finset E → ℝ) : Set (E → ℝ) :=
  {y | (fun e => f {e} * y e) ∈ indepPoly f}

/-- (2) of the proof of `lem:ellipsoid` (appF-convex.tex:133): `[0, 1/n]^E ⊆ K`. "Indeed, if
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
/-- (2) of the proof of `lem:ellipsoid` (appF-convex.tex:133): `K ⊆ [0, 1]^E`, as "every `x ∈ P₊(f)`
has `x_e ≤ f({e})`". -/
theorem scaledPoly_subset_box (hu : ∀ e, 0 < f {e}) {y : E → ℝ}
    (hy : y ∈ scaledPoly f) (e : E) : 0 ≤ y e ∧ y e ≤ 1 := by
  have h0 := hy.1 e
  have h1 : f {e} * y e ≤ f {e} := by simpa using hy.2 {e}
  constructor
  · exact nonneg_of_mul_nonneg_right (by simpa [mul_comm] using h0) (hu e)
  · nlinarith [hu e]

/-- (2) of the proof of `lem:ellipsoid` (appF-convex.tex:133): "So `K` contains a ball of radius
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
/-- (2) of the proof of `lem:ellipsoid` (appF-convex.tex:133): "and lies in a ball of radius
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
/-- (2) of the proof of `lem:ellipsoid` (appF-convex.tex:133): "the ratio of the radii is
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
/-- (3) of the proof of `lem:ellipsoid` (appF-convex.tex:135): "For a point `z ∈ ℝ^E`, either
`z_e < 0` for some `e`, which gives the cut `x_e ≥ 0`, or one submodular minimization of
`T ↦ f(T) − z(T)` returns a set `T` with `z(T) > f(T) ≥ x(T)` for all `x ∈ P₊(f)`, or it shows
`z ∈ P₊(f)`." Here `T` is a minimizer of `f(T) − z(T)` (one exists, as `E` is finite). -/
theorem separation {f : Finset E → ℝ} (z : E → ℝ) {T : Finset E}
    (hT : ∀ T', f T - ∑ e ∈ T, z e ≤ f T' - ∑ e ∈ T', z e) :
    (∃ e, z e < 0 ∧ ∀ x ∈ indepPoly f, z e < x e) ∨
      (f T < ∑ e ∈ T, z e ∧ ∀ x ∈ indepPoly f, ∑ e ∈ T, x e ≤ f T) ∨ z ∈ indepPoly f := by
  by_cases hneg : ∃ e, z e < 0
  · obtain ⟨e, he⟩ := hneg
    exact Or.inl ⟨e, he, fun x hx => he.trans_le (hx.1 e)⟩
  push Not at hneg
  by_cases hT0 : f T - ∑ e ∈ T, z e < 0
  · exact Or.inr (Or.inl ⟨by linarith, fun x hx => hx.2 T⟩)
  · refine Or.inr (Or.inr ⟨hneg, fun S => ?_⟩)
    have := hT S
    linarith

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

/-- (4) of the proof of `lem:ellipsoid` (appF-convex.tex:137): "We minimize `−U_A(· | α) = c − α r`,
which is convex on `P₊(f)`". -/
lemma convexOn_cost_sub (h : PolySetting f m c g G rb) (α : ℝ) :
    ConvexOn ℝ (indepPoly f) (fun x => c x - α * reward m x) := by
  refine ⟨h.convexOn.1, fun x hx y hy a b ha hb hab => ?_⟩
  have h1 := h.convexOn.2 hx hy ha hb hab
  simp only [smul_eq_mul] at h1 ⊢
  rw [reward_add_smul]
  nlinarith

/-- (4) of the proof of `lem:ellipsoid` (appF-convex.tex:137): `c − α r` has "the subgradient
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

/-- (4) of the proof of `lem:ellipsoid` (appF-convex.tex:137), the last inequality of
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
last sentence of `lem:ellipsoid`, where `δ ≥ M = r̄ + G f(E)` gives `r̄ ≤ δ` (appF-convex.tex:139),
and in (T5) of the proof of `thm:convexfptas`, where it gives `M ≥ r̄ ≥ w` (appF-convex.tex:147)).
-/
lemma PolySetting.G_mul_nonneg (h : PolySetting f m c g G rb) : 0 ≤ G * f univ := by
  simpa using h.G_mul_le (zero_mem_indepPoly h.rank)

/-- (4) of the proof of `lem:ellipsoid` (appF-convex.tex:137): "For `x ∈ P₊(f)`, the subgradient
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

/-- (4) of the proof of `lem:ellipsoid` (appF-convex.tex:137): "and `0 ≤ α r(x) ≤ r̄`. Hence
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

/-- The iteration number `t = ⌈2n² ln(2n^{3/2} M/δ)⌉` of `lem:ellipsoid` (appF-convex.tex:127, 139).
This is a formula; that the ellipsoid method attains it is not formalised (see the module
docstring). -/
noncomputable def ellipsoidIters (n : ℕ) (M δ : ℝ) : ℕ :=
  ⌈2 * (n : ℝ) ^ 2 * Real.log (2 * (n : ℝ) ^ (3 / 2 : ℝ) * M / δ)⌉₊

/-- (5) of the proof of `lem:ellipsoid` (appF-convex.tex:139): for `n ≥ 1` and `0 < δ < M`,
`t = ⌈2n² ln(2n^{3/2} M/δ)⌉` "is at least `2n² ln(2n^{3/2}) ≥ 1` as `δ < M`", and so at least
`2n² ln(R_out/R_in) = 2n² ln(n^{3/2})`, the number of iterations after which the cited bound
holds. -/
theorem ellipsoidIters_ge {n : ℕ} (hn : 1 ≤ n) {M δ : ℝ} (hδ : 0 < δ) (hδM : δ < M) :
    2 * (n : ℝ) ^ 2 * Real.log (2 * (n : ℝ) ^ (3 / 2 : ℝ)) ≤ ellipsoidIters n M δ ∧
      1 ≤ 2 * (n : ℝ) ^ 2 * Real.log (2 * (n : ℝ) ^ (3 / 2 : ℝ)) ∧
      2 * (n : ℝ) ^ 2 * Real.log ((n : ℝ) ^ (3 / 2 : ℝ)) ≤ ellipsoidIters n M δ := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (1 : ℝ) ≤ (n : ℝ) ^ (3 / 2 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
  have hM : 0 < M := hδ.trans hδM
  have hMδ : 1 < M / δ := by rw [lt_div_iff₀ hδ]; linarith
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn1
  -- `ln(2n^{3/2} M/δ) ≥ ln(2n^{3/2})`, as `M/δ > 1`
  have hlog1 : Real.log (2 * (n : ℝ) ^ (3 / 2 : ℝ)) ≤
      Real.log (2 * (n : ℝ) ^ (3 / 2 : ℝ) * M / δ) := by
    apply Real.log_le_log (by positivity)
    rw [mul_div_assoc]
    nlinarith
  have ht := Nat.le_ceil (2 * (n : ℝ) ^ 2 * Real.log (2 * (n : ℝ) ^ (3 / 2 : ℝ) * M / δ))
  have h1 : 2 * (n : ℝ) ^ 2 * Real.log (2 * (n : ℝ) ^ (3 / 2 : ℝ)) ≤ ellipsoidIters n M δ :=
    (mul_le_mul_of_nonneg_left hlog1 (by positivity)).trans ht
  -- `2n² ln(2n^{3/2}) ≥ 2 ln 2 ≥ 1`
  have hlog2 : Real.log 2 ≤ Real.log (2 * (n : ℝ) ^ (3 / 2 : ℝ)) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hl2 := Real.log_two_gt_d9
  have h2 : 1 ≤ 2 * (n : ℝ) ^ 2 * Real.log (2 * (n : ℝ) ^ (3 / 2 : ℝ)) := by nlinarith
  refine ⟨h1, h2, le_trans ?_ h1⟩
  exact mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by linarith)) (by positivity)

/-- (5) of the proof of `lem:ellipsoid` (appF-convex.tex:139): with `R_out/R_in = n^{3/2}` and
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
/-- (5) of the proof of `lem:ellipsoid` (appF-convex.tex:139): "We apply this to `K` and to
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

/-- `lem:ellipsoid`, its last sentence (appF-convex.tex:127, 139): "For `δ ≥ r̄ + G f(E)`, the
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

/-- **`lem:ellipsoid`** (Lemma D.8, appF-convex.tex:126-128, proof 130-140), as far as it is
formalised (see the module docstring): let `α ∈ [0, 1]`, `M = r̄ + G f(E)` and `n = |E| ≥ 1` (the
ground set is nonempty: "Let `E` be a finite nonempty ground set", 02-preliminaries.tex:4).
(i) The reduction of (1), "we may assume that `f({e}) > 0` for all `e ∈ E`": the reduced instance on
`E' = {e : f({e}) > 0}` (the rank function `f|E'`, the rewards `m|E'`, the cost `c ∘ pad` and the
subgradients `g ∘ pad` on `E'`, where `pad` pads with zeros) lies in the setting of `sec:convex`
with the same `G` and `r̄`, has `f|E'({e}) > 0` for all `e ∈ E'`, the same `f(E)` (so the same `M`)
and at most `n` elements, and `y` is a `δ`-optimal response at `α` of it if and only if `pad(y)` is
one of the original instance; "If `E' = ∅`, then `P₊(f) = {0}`".
(ii) If `0 < δ < M`, the number `t = ⌈2n² ln(2n^{3/2} M/δ)⌉` satisfies `t ≥ 1` and
`t ≥ 2n² ln(R_out/R_in)` for `R_out/R_in = n^{3/2}` (the radii of (2), which needs
`f({e}) > 0`: `ball_subset_scaledPoly`, `scaledPoly_subset_ball`, `radii_ratio`), and every
`x ∈ P₊(f)` within the bound `(2M R_out/R_in) exp(−t/(2n²))` of the ellipsoid method of the optimum,
that is, `V(α) − U_A(x | α) ≤ 2M n^{3/2} exp(−t/(2n²))` (the cited bound for the best center after
`t` iterations, Bubeck, Thm. 2.4, here a hypothesis on `x`), is a `δ`-optimal response at `α`: "this
gives `U_A(x_t | α) ≥ V(α) − δ`, so `x_t` is a `δ`-optimal response".
(iii) "For `δ ≥ r̄ + G f(E)`, the response `0` is `δ`-optimal" (`zero_isDeltaOpt`).

The proof follows the paragraphs (1) to (5) of the STOC version's (see the module docstring): (1)
"We first reduce to the case that `f({e}) > 0` for all `e`" (`PolySetting.restrict`,
`restrictRank_singleton_pos`, `restrictRank_univ`, `card_posElems_le`,
`isDeltaOpt_pad_iff`, `indepPoly_eq_zero`); (5) "Finally, we apply the ellipsoid method": "For
`t := ⌈2n² ln(2n^{3/2} M/δ)⌉`, which is at least `2n² ln(2n^{3/2}) ≥ 1` as `δ < M`, this gives
`U_A(x_t | α) ≥ V(α) − δ`" (`ellipsoidIters_ge`, `ellipsoid_bound_le`), and "If `δ ≥ M`, then
`V(α) − U_A(0 | α) = V(α) ≤ r̄ ≤ δ`" (`zero_isDeltaOpt`). The paper takes `n` after the reduction,
where `E' ≠ ∅`, as otherwise "there is nothing to compute"; the Lean states (ii) with `n = |E|`,
which is at least `|E'|`. The paragraphs (2) "Next we place `P₊(f)` between two cubes", (3) "A
separation oracle needs one submodular minimization" and (4) "Next we bound the objective", and
the scaling of the subgradients in (5), state the facts on which the method is run
(`ball_subset_scaledPoly`, `scaledPoly_subset_ball`, `radii_ratio`, `separation`,
`convexOn_cost_sub`, `subgrad_cost_sub`, `cost_le`, `abs_util_le`, `subgrad_scaled`). As the
method is not formalised, `ellipsoid` does not use them. Not formalised: the method, the cited
bound and the counts per iteration. -/
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
      1 ≤ ellipsoidIters (Fintype.card E) (rb + G * f univ) δ ∧
      2 * (Fintype.card E : ℝ) ^ 2 * Real.log ((Fintype.card E : ℝ) ^ (3 / 2 : ℝ)) ≤
        ellipsoidIters (Fintype.card E) (rb + G * f univ) δ ∧
      ∀ x ∈ indepPoly f, V (indepPoly f) m c α - util m c α x ≤
          2 * (rb + G * f univ) * (Fintype.card E : ℝ) ^ (3 / 2 : ℝ) *
            Real.exp (-(ellipsoidIters (Fintype.card E) (rb + G * f univ) δ : ℝ) /
              (2 * (Fintype.card E : ℝ) ^ 2)) →
        IsDeltaOpt (indepPoly f) m c α δ x) ∧
    (rb + G * f univ ≤ δ → IsDeltaOpt (indepPoly f) m c α δ 0) := by
  -- (1) "We first reduce to the case that `f({e}) > 0` for all `e`. … So `P₊(f)` is `P₊(f|E')`,
  -- padded with zeros, and we may assume that `f({e}) > 0` for all `e ∈ E`. If `E' = ∅`, then
  -- `P₊(f) = {0}` and there is nothing to compute."
  refine ⟨⟨h.restrict, restrictRank_singleton_pos, restrictRank_univ h.rank, card_posElems_le,
    isDeltaOpt_pad_iff h.rank m c α δ, indepPoly_eq_zero h.rank⟩, fun hδ hδM => ?_,
    zero_isDeltaOpt h hα⟩
  -- `n ≥ 1`, as the ground set is nonempty (02-preliminaries.tex:4)
  have hn : 1 ≤ Fintype.card E := Fintype.card_pos
  -- (5) "Finally, we apply the ellipsoid method. … For `t := ⌈2n² ln(2n^{3/2} M/δ)⌉`, which is
  -- at least `2n² ln(2n^{3/2}) ≥ 1` as `δ < M`,"
  obtain ⟨h1, h2, h3⟩ := ellipsoidIters_ge hn hδ hδM
  refine ⟨by exact_mod_cast h2.trans h1, h3, fun x hx hbound => ⟨hx, ?_⟩⟩
  -- "this gives `U_A(x_t | α) ≥ V(α) − δ`, so `x_t` is a `δ`-optimal response."
  have := ellipsoid_bound_le hn hδ hδM
  linarith

end Method

end Stoc.Convex
