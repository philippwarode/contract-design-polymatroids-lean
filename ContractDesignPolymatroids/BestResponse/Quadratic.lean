-- stamp r7 2026-11-02
import ContractDesignPolymatroids.Preliminaries.Polymatroid

/-!
# Quadratic costs: the agent's problem and its best response

The STOC version, Section 3, Exact computation for quadratic costs, its best-response part
(`stoc-sections/05-best-response.tex`, with the proofs in Appendix B.1, `sec:A-bestresponse`):
costs `c_e(x_e) = β_e x_e²/2` with `β_e > 0`, the agent's utility
`U_A(x | α) = ∑_e (α m_e x_e − β_e/2 x_e²)` and its best response `x*(α)`.

The best response is defined directly, as the maximizer of `U_A(· | α)` over the action set; the
water-filling algorithm of `thm:waterfilling`, which computes it, is in
`ContractDesignPolymatroids/BestResponse/WaterFilling.lean`. `IsBestResponse C` is defined for any action set `C`; the
STOC version's is the polymatroid `P₊(f)`.

* `marg` and `zmax`: the marginals `ρ_e(x)` and the unconstrained maximizers `z_e(α)` (`eq:marg`).
* `IsBestResponse.foc`, `utility_sub_le`, `isBestResponse_of_foc`: step (2) of the proof of
  `prop:optchar`, the first-order condition `∑_e ρ_e (z_e − x_e) ≤ 0` for all `z ∈ C`, necessary on
  a convex set (by the directional derivatives) and sufficient for `β ≥ 0` (by the concavity
  inequality `U_A(y | α) − U_A(x | α) ≤ ρ(x)ᵀ(y − x)`).
* `strictConcaveOn_utility`, `IsBestResponse.unique`: for `β > 0` the utility is strictly
  concave, so the best response is unique (`stoc-sections/05-best-response.tex:10`).
* `exists_isBestResponse`, `bestResponse`: on `P₊(f)` a best response exists, as `P₊(f)` is
  compact (Section 2 assumes this and notes when it holds), and `bestResponse f m β α` is `x*(α)`.
* `IsBestResponse.le_z`, `IsBestResponse.marg_nonneg`: step (1) and the last sentence of
  `prop:optchar`, `0 ≤ x*_e(α) ≤ z_e(α) = α t_e` and `ρ ≥ 0`.
* `breakpoints`: the breakpoints of `x*` (Section 3).

The facts the STOC version uses without proof are marked "not in the paper" in their docstrings.

Shares are real numbers; `α ≥ 0` (Section 3 fixes `α ≥ 0`) is assumed where it is needed. The
contract model of Section 2 has a reward bound `r̄ > 0` (`stoc-sections/02-preliminaries.tex:12`);
the results of Section 3 (here, in `LevelSets.lean` and in `WaterFilling.lean`) do not use it and
are stated without it.

Taken over on 2026-10-20 from `Paper/FixedShare/Quadratic.lean` (the paper at Overleaf f035b19) for
the STOC version (`stoc.tex`); from then on this copy follows the STOC version.
-/

namespace Stoc

open Finset

variable {E : Type*} [Fintype E]

/-! ### Utility, marginals and best responses on a general action set -/

/-- The agent's utility `U_A(x | α) = α r(x) − c(x)` (`stoc-sections/02-preliminaries.tex:14-16`),
with the quadratic costs `c(x) = ∑_e β_e x_e²/2` of `stoc-sections/05-best-response.tex:4`. -/
noncomputable def utility (m β : E → ℝ) (α : ℝ) (x : E → ℝ) : ℝ :=
  α * reward m x - ∑ e, β e / 2 * x e ^ 2

/-- The utility as one sum over the elements, `U_A(x | α) = ∑_e (α m_e x_e − β_e/2 x_e²)`. -/
lemma utility_eq_sum (m β : E → ℝ) (α : ℝ) (x : E → ℝ) :
    utility m β α x = ∑ e, (α * m e * x e - β e / 2 * x e ^ 2) := by
  rw [utility, reward, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun e _ => by ring

/-- The marginal `ρ_e(x) = α m_e − β_e x_e` of `e` at `x` (`eq:marg`,
`stoc-sections/05-best-response.tex:13-15`). -/
def marg (m β : E → ℝ) (α : ℝ) (x : E → ℝ) (e : E) : ℝ :=
  α * m e - β e * x e

/-- The unconstrained maximizer `z_e(α) = α t_e = α m_e/β_e` of `e` (`eq:marg`,
`stoc-sections/05-best-response.tex:13-15`). -/
noncomputable def zmax (m β : E → ℝ) (α : ℝ) (e : E) : ℝ :=
  α * (m e / β e)

/-- `x` is a best response to the share `α` on the action set `C`: it maximizes the agent's
utility over `C` (`stoc-sections/02-preliminaries.tex:17`; the STOC version's action set is
`P₊(f)`). -/
def IsBestResponse (C : Set (E → ℝ)) (m β : E → ℝ) (α : ℝ) (x : E → ℝ) : Prop :=
  x ∈ C ∧ ∀ z ∈ C, utility m β α z ≤ utility m β α x

/-- The utility along the segment from `x` towards `z` is a quadratic in the step `t`. -/
lemma utility_add_smul (m β : E → ℝ) (α t : ℝ) (x z : E → ℝ) :
    utility m β α (x + t • (z - x)) =
      utility m β α x + t * ∑ e, marg m β α x e * (z e - x e)
        - t ^ 2 / 2 * ∑ e, β e * (z e - x e) ^ 2 := by
  simp only [utility_eq_sum, marg, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- First-order optimality: at a best response `x` on a convex set `C`,
`∑ ρ_e (z_e - x_e) ≤ 0` for every `z ∈ C`. This is the necessity in step (2) of the proof of
`prop:optchar` ("necessity follows by taking directional derivatives towards feasible points"):
the directional derivative of `U_A` at `x` towards `z` is the limit of the difference quotients
`(U_A(x + t (z − x)) − U_A(x)) / t = ρᵀ(z − x) − t/2 ∑ β_e (z_e − x_e)²` as `t → 0⁺`, and these
are `≤ 0` as `x` is optimal (`stoc-sections/appB-quadratic.tex:16-18`). -/
theorem IsBestResponse.foc {C : Set (E → ℝ)} (hC : Convex ℝ C) {m β : E → ℝ} {α : ℝ}
    {x : E → ℝ} (hx : IsBestResponse C m β α x) {z : E → ℝ} (hz : z ∈ C) :
    ∑ e, marg m β α x e * (z e - x e) ≤ 0 := by
  set L := ∑ e, marg m β α x e * (z e - x e)
  set Q := ∑ e, β e * (z e - x e) ^ 2
  -- The difference quotients for `t ∈ (0, 1)` are `≤ 0`.
  have hq : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), L - t * Q / 2 ≤ 0 := by
    filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
    have hmem : x + t • (z - x) ∈ C := hC.add_smul_sub_mem hx.1 hz ⟨ht.1.le, ht.2.le⟩
    have h := hx.2 _ hmem
    rw [utility_add_smul] at h
    have h' : t * (L - t * Q / 2) ≤ 0 := by linarith
    by_contra hpos
    exact absurd h' (not_le.2 (mul_pos ht.1 (not_le.1 hpos)))
  -- Their limit as `t → 0⁺` is the directional derivative `L`.
  have hlim : Filter.Tendsto (fun t : ℝ => L - t * Q / 2) (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
    have h : Filter.Tendsto (fun t : ℝ => L - t * Q / 2) (nhds 0) (nhds (L - 0 * Q / 2)) :=
      (by fun_prop : Continuous fun t : ℝ => L - t * Q / 2).tendsto 0
    rw [zero_mul, zero_div, sub_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto hlim hq

/-- The concavity inequality of step (2) of the proof of `prop:optchar`
(`stoc-sections/appB-quadratic.tex:18-22`): for `β ≥ 0`,
`U_A(y | α) − U_A(x | α) ≤ ρ(x)ᵀ(y − x)`. -/
lemma utility_sub_le {m β : E → ℝ} (hβ : ∀ e, 0 ≤ β e) (α : ℝ) (x y : E → ℝ) :
    utility m β α y - utility m β α x ≤ ∑ e, marg m β α x e * (y e - x e) := by
  have hu := utility_add_smul m β α 1 x y
  rw [one_smul, add_sub_cancel] at hu
  rw [hu]
  have hq : 0 ≤ ∑ e, β e * (y e - x e) ^ 2 :=
    Finset.sum_nonneg fun e _ => mul_nonneg (hβ e) (sq_nonneg _)
  linarith

/-- Sufficiency in step (2) of the proof of `prop:optchar`
(`stoc-sections/appB-quadratic.tex:16-22`): for `β ≥ 0`, a point of `C` with
`∑ ρ_e (z_e − x_e) ≤ 0` for every `z ∈ C` is a best response, by the concavity inequality
`utility_sub_le`. -/
theorem isBestResponse_of_foc {C : Set (E → ℝ)} {m β : E → ℝ} (hβ : ∀ e, 0 ≤ β e) {α : ℝ}
    {x : E → ℝ} (hx : x ∈ C) (h : ∀ z ∈ C, ∑ e, marg m β α x e * (z e - x e) ≤ 0) :
    IsBestResponse C m β α x := by
  refine ⟨hx, fun z hz => ?_⟩
  have := utility_sub_le (m := m) hβ α x z
  linarith [h z hz]

/-- For `β > 0` the agent's utility is strictly concave (not in the paper: the STOC version
asserts this without proof, `stoc-sections/05-best-response.tex:10`): for `x ≠ y`, `a, b > 0` and
`a + b = 1`, `U_A(a x + b y | α) − a U_A(x | α) − b U_A(y | α) = a b / 2 ∑ β_e (x_e − y_e)² > 0`. -/
theorem strictConcaveOn_utility {C : Set (E → ℝ)} (hC : Convex ℝ C) (m : E → ℝ) {β : E → ℝ}
    (hβ : ∀ e, 0 < β e) (α : ℝ) : StrictConcaveOn ℝ C (utility m β α) := by
  refine ⟨hC, fun x _ y _ hxy a b ha hb hab => ?_⟩
  have hgap : utility m β α (a • x + b • y) - (a • utility m β α x + b • utility m β α y) =
      a * b / 2 * ∑ e, β e * (x e - y e) ^ 2 := by
    simp only [utility_eq_sum, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    obtain rfl : b = 1 - a := by linarith
    ring
  obtain ⟨e, he⟩ := Function.ne_iff.1 hxy
  have hpos : 0 < ∑ e, β e * (x e - y e) ^ 2 :=
    Finset.sum_pos' (fun e _ => mul_nonneg (hβ e).le (sq_nonneg _))
      ⟨e, Finset.mem_univ e, mul_pos (hβ e) (sq_pos_iff.2 (sub_ne_zero.2 he))⟩
  have h2 := mul_pos (mul_pos ha hb) hpos
  simp only [smul_eq_mul] at hgap ⊢
  linarith

/-- Uniqueness of the best response for `β > 0` (`stoc-sections/05-best-response.tex:10`: "This
objective is strictly concave, so the best response `x*(α)` is unique"): the utility is strictly
concave (`strictConcaveOn_utility`), so it has at most one maximizer on `C`. -/
theorem IsBestResponse.unique {C : Set (E → ℝ)} (hC : Convex ℝ C) {m β : E → ℝ}
    (hβ : ∀ e, 0 < β e) {α : ℝ} {a b : E → ℝ} (ha : IsBestResponse C m β α a)
    (hb : IsBestResponse C m β α b) : a = b :=
  (strictConcaveOn_utility hC m hβ α).eq_of_isMaxOn (isMaxOn_iff.2 ha.2) (isMaxOn_iff.2 hb.2)
    ha.1 hb.1

/-! ### The polymatroid `P₊(f)` (`Stoc.indepPoly`, from `ContractDesignPolymatroids/Preliminaries/Polymatroid.lean`) -/

omit [Fintype E] in
/-- `P₊(f)` is convex (not in the paper: used without proof in step (2) of the proof of
`prop:optchar` and for the uniqueness of the best response). -/
lemma convex_indepPoly (f : Finset E → ℝ) : Convex ℝ (indepPoly f) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun e => ?_, fun A => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 e)) (mul_nonneg hb (hy.1 e))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    calc a * ∑ e ∈ A, x e + b * ∑ e ∈ A, y e ≤ a * f A + b * f A :=
          add_le_add (mul_le_mul_of_nonneg_left (hx.2 A) ha)
            (mul_le_mul_of_nonneg_left (hy.2 A) hb)
      _ = f A := by rw [← add_mul, hab, one_mul]

omit [Fintype E] in
/-- `P₊(f)` is closed (not in the paper: for the existence of best responses, which Section 2
assumes). -/
lemma isClosed_indepPoly (f : Finset E → ℝ) : IsClosed (indepPoly f) := by
  have h1 : IsClosed {x : E → ℝ | ∀ e, 0 ≤ x e} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun e => isClosed_le continuous_const (continuous_apply e)
  have h2 : IsClosed {x : E → ℝ | ∀ A : Finset E, ∑ e ∈ A, x e ≤ f A} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun A =>
      isClosed_le (continuous_finsetSum _ fun e _ => continuous_apply e) continuous_const
  exact h1.inter h2

omit [Fintype E] in
/-- `P₊(f)` lies in the box `0 ≤ x_e ≤ f({e})` (not in the paper: as for `isClosed_indepPoly`). -/
lemma indepPoly_subset_Icc (f : Finset E → ℝ) : indepPoly f ⊆ Set.Icc 0 (fun e => f {e}) :=
  fun x hx => ⟨fun e => hx.1 e, fun e => by simpa using hx.2 {e}⟩

omit [Fintype E] in
/-- `P₊(f)` is compact (not in the paper: the STOC version calls it compact without proof,
`stoc-sections/02-preliminaries.tex:17`). -/
lemma isCompact_indepPoly (f : Finset E → ℝ) : IsCompact (indepPoly f) :=
  isCompact_Icc.of_isClosed_subset (isClosed_indepPoly f) (indepPoly_subset_Icc f)

/-! ### The best response `x*(α)` -/

/-- The utility is continuous (not in the paper: as for `isClosed_indepPoly`). -/
lemma continuous_utility (m β : E → ℝ) (α : ℝ) : Continuous (utility m β α) := by
  unfold utility reward
  fun_prop

/-- A best response exists for every share (not in the paper: Section 2,
`stoc-sections/02-preliminaries.tex:17`, assumes that the agent's maximum is attained and notes that
this holds when `c` is continuous on the compact set `P₊(f)`; this is that note for quadratic
costs). -/
theorem exists_isBestResponse [DecidableEq E] {f : Finset E → ℝ} (hf : IsRankFunction f)
    (m β : E → ℝ) (α : ℝ) : ∃ x, IsBestResponse (indepPoly f) m β α x := by
  obtain ⟨x, hx, hmax⟩ := (isCompact_indepPoly f).exists_isMaxOn ⟨0, zero_mem_indepPoly hf⟩
    (continuous_utility m β α).continuousOn
  exact ⟨x, hx, isMaxOn_iff.1 hmax⟩

/-- The best response `x*(α)` on `P₊(f)`; for a rank function `f` it is one
(`Stoc.isBestResponse_bestResponse`), and for `β > 0` the only one (`IsBestResponse.unique`). -/
noncomputable def bestResponse (f : Finset E → ℝ) (m β : E → ℝ) (α : ℝ) : E → ℝ :=
  Classical.epsilon fun x => IsBestResponse (indepPoly f) m β α x

lemma isBestResponse_bestResponse [DecidableEq E] {f : Finset E → ℝ} (hf : IsRankFunction f)
    (m β : E → ℝ) (α : ℝ) : IsBestResponse (indepPoly f) m β α (bestResponse f m β α) :=
  Classical.epsilon_spec (exists_isBestResponse hf m β α)

section BestResponse

variable [DecidableEq E] {f : Finset E → ℝ} {m β : E → ℝ} {α : ℝ} {x : E → ℝ}

/-- For `β > 0`, every best response on `P₊(f)` is `x*(α)`. -/
theorem IsBestResponse.eq_bestResponse (hβ : ∀ e, 0 < β e) (hf : IsRankFunction f)
    (hx : IsBestResponse (indepPoly f) m β α x) : x = bestResponse f m β α :=
  hx.unique (convex_indepPoly f) hβ (isBestResponse_bestResponse hf m β α)

/-- `prop:optchar`, step (1) (`stoc-sections/appB-quadratic.tex:14-15`) and its last sentence
(`stoc-sections/05-best-response.tex:20`): at an optimum `x_e ≤ z_e(α)`, as otherwise lowering
`x_e` to `z_e(α)` preserves feasibility and increases the utility, by `β_e/2 (x_e − z_e(α))²`; so
`0 ≤ x_e ≤ z_e(α) = α t_e`, provided `α m_e ≥ 0`. -/
theorem IsBestResponse.le_z (hβ : ∀ e, 0 < β e) (hx : IsBestResponse (indepPoly f) m β α x)
    (hm : ∀ e, 0 ≤ α * m e) (e : E) : 0 ≤ x e ∧ x e ≤ zmax m β α e := by
  refine ⟨hx.1.1 e, ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  set z := zmax m β α e with hz
  have hz0 : 0 ≤ z := by
    rw [hz, zmax, ← mul_div_assoc]
    exact div_nonneg (hm e) (hβ e).le
  set y := Function.update x e z
  have hy : y ∈ indepPoly f := by
    refine mem_indepPoly_of_le hx.1 (fun e' => ?_) (fun e' => ?_)
    · by_cases h : e' = e
      · simp [y, h, hz0]
      · simp [y, h, hx.1.1 e']
    · by_cases h : e' = e
      · simp [y, h, hlt.le]
      · simp [y, h]
  have hdiff : utility m β α y - utility m β α x = β e / 2 * (x e - z) ^ 2 := by
    simp only [utility_eq_sum]
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single e]
    · simp only [y, Function.update_self]
      have hbz : β e * z = α * m e := by rw [hz, zmax]; field_simp [(hβ e).ne']
      linear_combination (x e - z) * hbz
    · intro e' _ he'
      simp [y, he']
    · simp
  have hpos : 0 < β e / 2 * (x e - z) ^ 2 := by
    have := hβ e
    have : 0 < x e - z := by linarith
    positivity
  have := hx.2 y hy
  linarith

/-- `prop:optchar`, step (1), "Hence `ρ(x) ≥ 0`": every marginal is nonnegative at the best
response, `ρ_e = β_e (z_e(α) − x_e) ≥ 0`, provided `α m_e ≥ 0`. -/
theorem IsBestResponse.marg_nonneg (hβ : ∀ e, 0 < β e)
    (hx : IsBestResponse (indepPoly f) m β α x) (hm : ∀ e, 0 ≤ α * m e) (e : E) :
    0 ≤ marg m β α x e := by
  have h := (hx.le_z hβ hm e).2
  rw [zmax, ← mul_div_assoc, le_div_iff₀ (hβ e)] at h
  unfold marg
  linarith

/-- The sentence of Section 3 after (`eq:marg`) (`stoc-sections/05-best-response.tex:16`): "The
vector `z(α)` is nonnegative but may violate the constraints defining `P₊(f)`. If it is feasible,
it equals `x*(α)`" (not in the paper: the STOC version gives no proof). For `β > 0` and `α m ≥ 0`,
`z(α) ≥ 0`; and if `z(α) ∈ P₊(f)`, it is the best response, as
`U_A(z(α) | α) − U_A(y | α) = ∑_e β_e/2 (y_e − z_e(α))² ≥ 0` for every `y`, so `x*(α) = z(α)`. -/
theorem bestResponse_eq_zmax (hf : IsRankFunction f) (hβ : ∀ e, 0 < β e)
    (hm : ∀ e, 0 ≤ α * m e) :
    (∀ e, 0 ≤ zmax m β α e) ∧
      (zmax m β α ∈ indepPoly f → bestResponse f m β α = zmax m β α) := by
  refine ⟨fun e => ?_, fun hz => ?_⟩
  · rw [zmax, ← mul_div_assoc]
    exact div_nonneg (hm e) (hβ e).le
  · -- `z(α)` maximizes the utility over all of `ℝ^E`
    have hgap : ∀ y : E → ℝ, utility m β α (zmax m β α) - utility m β α y =
        ∑ e, β e / 2 * (y e - zmax m β α e) ^ 2 := by
      intro y
      simp only [utility_eq_sum]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      have hbz : β e * zmax m β α e = α * m e := by
        rw [zmax]
        field_simp [(hβ e).ne']
      linear_combination (y e - zmax m β α e) * hbz
    have hbr : IsBestResponse (indepPoly f) m β α (zmax m β α) := by
      refine ⟨hz, fun y _ => ?_⟩
      have h0 : 0 ≤ ∑ e, β e / 2 * (y e - zmax m β α e) ^ 2 :=
        Finset.sum_nonneg fun e _ => mul_nonneg (div_nonneg (hβ e).le two_pos.le) (sq_nonneg _)
      linarith [hgap y]
    exact (hbr.eq_bestResponse hβ hf).symm

end BestResponse

/-! ### Breakpoints -/

/-- `g` is affine on a neighborhood of `α`. -/
def AffineNear (g : ℝ → E → ℝ) (α : ℝ) : Prop :=
  ∃ ε > 0, ∃ a b : E → ℝ, ∀ α' ∈ Set.Ioo (α - ε) (α + ε), g α' = fun e => a e + α' * b e

/-- The breakpoints of `g`: the shares `α > 0` near which `g` is not affine (Section 3).
The number `B` of the STOC version is the number of breakpoints of `bestResponse f m β` in
`(0, 1)`. -/
def breakpoints (g : ℝ → E → ℝ) : Set ℝ :=
  {α | 0 < α ∧ ¬ AffineNear g α}

end Stoc
