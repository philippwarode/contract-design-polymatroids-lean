-- stamp r8 2026-11-02
import Stoc.BestResponse.Quadratic

/-!
# The best response is continuous and piecewise affine

The STOC version, Section 3, Lemma `lem:pwaffine` (statement
`stoc-sections/06-optimal-share.tex:20-22`, proof `stoc-sections/appB-quadratic.tex:254-273`): the
map `α ↦ x*(α)` is continuous and piecewise affine on `[0, ∞)` with finitely many breakpoints, and
`x*(α)` is the projection of `z(α) = αt` onto `P₊(f)` in the inner product `uᵀ diag(β) v`
(`= ∑_e β_e u_e v_e`). The exact statement is `Stoc.pwaffine`. Section 3 derives the projection
before the lemma as well, by completing the square (`stoc-sections/06-optimal-share.tex:5-13`;
`utility_eq_normβ`, `bestResponse_isProjβ`). Its proof is
`Stoc.pwaffine_aux`, a stronger statement: it holds for every `m` (the proof does not use `m ≥ 0`),
`x*` is continuous on all of `ℝ`, and `x*(α)` is the projection of `αt` for every real `α`.
`piecewise_affine` reads the cover of `[0, ∞)` off `pwaffine_aux`, and `exists_affine_right`, which
`Stoc/Subclasses/SupportShrinks.lean` uses, is derived from it; `continuous_bestResponse`, step 2,
is also used by other files.

The proof of `pwaffine_aux` follows the STOC version's, step by step:

1. For the inner product `yᵀDz` with `D = diag(β)` (`innerβ`) and its norm
   `‖y‖_β = (yᵀDy)^{1/2}` (`normβ`), completing the square gives
   `U_A(x | α) = α²/2 ‖t‖_β² − 1/2 ‖x − αt‖_β²` (`utility_eq_normβ`), so `x*(α)` is the
   projection of `αt` onto `P₊(f)` (`isBestResponse_iff_isProjβ`, `bestResponse_isProjβ`).
2. Nonexpansiveness of projections gives `‖x*(α) − x*(α')‖_β ≤ |α − α'| ‖t‖_β`
   (`normβ_bestResponse_sub_le`), so `x*` is continuous (`continuous_bestResponse`).
3. The normal cone `N(x) = {u | uᵀD(y − x) ≤ 0 for all y ∈ P₊(f)}` (`normalCone`); `x` is the
   projection of `z` exactly when `z − x ∈ N(x)` [BC17, Prop. 6.47] (`isProjβ_iff_mem_normalCone`).
4. For a face `F`, a normal at `x ∈ relint F` is orthogonal to every direction parallel to `F`
   (`innerβ_eq_zero_of_mem_relint`), hence normal at every other point of `relint F`
   (`mem_normalCone_of_mem_relint`); the common cone is `N(F)` (`faceNormal`,
   `normalCone_eq_faceNormal`).
5. The shares with `x*(α) ∈ relint F` (`relintShares`) are those with `αt ∈ relint F + N(F)`, and
   they form an interval, as this set is convex (in the proof of `pwaffine_aux`, with
   `convex_intrinsicInterior`, `convex_of_mem_indepFaces` and `convex_faceNormal`).
6. On this interval, `x*(α)` is the projection of `αt` onto `aff F`, hence affine in `α` (in the
   proof of `pwaffine_aux`).
7. There are finitely many faces (`indepFaces_finite`).

The faces of the polyhedron `P₊(f) = {x ≥ 0 | x(S) ≤ f(S) for all S}` are the nonempty sets on
which some of its defining inequalities hold with equality (`indepFace`, `indepFaces`; the
definition of a face of a polyhedron in Schrijver's *Theory of Linear and Integer Programming*,
§5.2). The relative interior `relint F` is Mathlib's `intrinsicInterior ℝ F`, the interior of `F`
within its affine hull `aff F = affineSpan ℝ F`, and the directions parallel to `F` are
`vectorSpan ℝ F`. Vectors are functions `E → ℝ`, with `t = (m_e/β_e)_e` written out.

Steps that the STOC version cites, uses without proof or leaves implicit are proved in lemmas of
their own, marked "not in the paper" in their docstrings: the nonexpansiveness of projections
(`IsProjβ.normβ_sub_le`, cited as [BC17, Prop. 4.16]); the characterisation of projections by the
normal cone (`isProjβ_iff_mem_normalCone`, cited as [BC17, Prop. 6.47]) and their uniqueness
(`IsProjβ.unique`); that a face of `P₊(f)` is convex (`convex_of_mem_indepFaces`), that the
relative interior of a convex set is convex (`convex_intrinsicInterior`) and that `N(F)` is convex
(`convex_faceNormal`), the three facts behind "since this set is convex" in step 5; that the
projection onto an affine subspace maps affine combinations to affine combinations
(`IsProjβ.lineMap`); that every point of `P₊(f)` lies in the relative interior of a face
(`exists_face_mem_relint`), so that the intervals of step 5 cover `[0, ∞)`; and that finitely many
intervals of affinity leave finitely many breakpoints (`breakpoints_finite_of_cover`). Passing from
the `β`-norm to the coordinates (`continuous_of_normβ_le`, `sq_le_normβ_sq`) and unfolding
Mathlib's relative interior (`mem_intrinsicInterior_iff`) are plumbing.

The standing assumptions of Sections 3 to 4 are collected in `Stoc.Tracing.Hyp`.

Taken over on 2026-10-20 from `Paper/OptimalShare/PiecewiseAffine.lean` (the paper at Overleaf
f035b19) for the STOC version (`stoc.tex`); from then on this copy follows the STOC version.
Reworked on 2026-10-25 to follow the STOC version's proof step by step: faces, relative interiors,
normal cones and the projection onto `aff F` replace the sets of tight constraints, and continuity
comes from the nonexpansiveness of the projection. Checked on 2026-10-27 against the STOC version
after PR #88, whose proof now cites [BC17, Prop. 6.47] for the characterisation by the normal cone
(step 3); nothing else in `lem:pwaffine` changed.
-/

namespace Stoc

open Finset Filter Topology
open scoped Pointwise

noncomputable section

variable {E : Type*} [Fintype E] [DecidableEq E]

namespace Tracing

/-- The standing assumptions of Sections 3 to 4 of the STOC version (and of `alg:pieces`): `f` is a
rank function, the curvatures are positive, `β > 0`, and the rewards are nonnegative, `m ≥ 0`
(`stoc-sections/02-preliminaries.tex:4, 12`, `05-best-response.tex:4`). The contract model's
reward bound (`02-preliminaries.tex:12`, "success with a given reward `r̄ > 0`, where `r(x) ≤ r̄`
for every `x ∈ P₊(f)`") is not included: it makes the success probability `r(x)/r̄` well defined,
and no result of Sections 3 to 4 uses it (`Stoc/Approximation/Agent.lean`). -/
structure Hyp (f : Finset E → ℝ) (m β : E → ℝ) : Prop where
  rank : IsRankFunction f
  beta : ∀ e, 0 < β e
  reward : ∀ e, 0 ≤ m e

end Tracing

variable {f : Finset E → ℝ} {m β : E → ℝ}

/-! ### The inner product `yᵀDz`, projections and normal cones -/

/-- The inner product `yᵀDz = ∑_e β_e y_e z_e` with `D = diag(β)`. -/
def innerβ (β y z : E → ℝ) : ℝ := ∑ e, β e * y e * z e

/-- Its norm `‖y‖_β = (yᵀDy)^{1/2}`. -/
def normβ (β y : E → ℝ) : ℝ := Real.sqrt (innerβ β y y)

/-- `x` is the projection of `z` onto `C` in the inner product `yᵀDz`: a point of `C` nearest to
`z` in the norm `‖·‖_β`. -/
def IsProjβ (β : E → ℝ) (C : Set (E → ℝ)) (z x : E → ℝ) : Prop :=
  x ∈ C ∧ ∀ y ∈ C, normβ β (z - x) ≤ normβ β (z - y)

/-- The normal cone `N(x) = {u | uᵀD(y − x) ≤ 0 for all y ∈ C}` of `C` at `x`; the STOC
version's `N(x)` is the one of `C = P₊(f)`. -/
def normalCone (β : E → ℝ) (C : Set (E → ℝ)) (x : E → ℝ) : Set (E → ℝ) :=
  {u | ∀ y ∈ C, innerβ β u (y - x) ≤ 0}

section Inner

omit [DecidableEq E]

lemma innerβ_add_left (y y' z : E → ℝ) : innerβ β (y + y') z = innerβ β y z + innerβ β y' z := by
  simp only [innerβ, ← Finset.sum_add_distrib, Pi.add_apply]
  exact Finset.sum_congr rfl fun e _ => by ring

lemma innerβ_add_right (y z z' : E → ℝ) : innerβ β y (z + z') = innerβ β y z + innerβ β y z' := by
  simp only [innerβ, ← Finset.sum_add_distrib, Pi.add_apply]
  exact Finset.sum_congr rfl fun e _ => by ring

lemma innerβ_neg_right (y z : E → ℝ) : innerβ β y (-z) = -innerβ β y z := by
  simp only [innerβ, ← Finset.sum_neg_distrib, Pi.neg_apply]
  exact Finset.sum_congr rfl fun e _ => by ring

lemma innerβ_smul_left (c : ℝ) (y z : E → ℝ) : innerβ β (c • y) z = c * innerβ β y z := by
  simp only [innerβ, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun e _ => by ring

lemma innerβ_smul_right (c : ℝ) (y z : E → ℝ) : innerβ β y (c • z) = c * innerβ β y z := by
  simp only [innerβ, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun e _ => by ring

lemma innerβ_self_nonneg (hβ : ∀ e, 0 < β e) (y : E → ℝ) : 0 ≤ innerβ β y y :=
  Finset.sum_nonneg fun e _ => by
    have := (hβ e).le
    rw [mul_assoc]
    exact mul_nonneg this (mul_self_nonneg _)

/-- A vector of `β`-length `0` is `0`. -/
lemma eq_of_innerβ_self_nonpos (hβ : ∀ e, 0 < β e) {y : E → ℝ} (h : innerβ β y y ≤ 0) :
    y = 0 := by
  have hz : innerβ β y y = 0 := le_antisymm h (innerβ_self_nonneg hβ y)
  funext e
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun e _ => by
    have := (hβ e).le
    rw [mul_assoc]
    exact mul_nonneg this (mul_self_nonneg (y e))).1 hz e (Finset.mem_univ e)
  have : β e * (y e * y e) = 0 := by rw [← mul_assoc]; exact h0
  rcases mul_eq_zero.1 this with h1 | h1
  · exact absurd h1 (hβ e).ne'
  · simpa using mul_self_eq_zero.1 h1

lemma normβ_sq (hβ : ∀ e, 0 < β e) (y : E → ℝ) : normβ β y ^ 2 = innerβ β y y :=
  Real.sq_sqrt (innerβ_self_nonneg hβ y)

lemma normβ_nonneg (y : E → ℝ) : 0 ≤ normβ β y := Real.sqrt_nonneg _

lemma normβ_le_normβ_iff (hβ : ∀ e, 0 < β e) {y z : E → ℝ} :
    normβ β y ≤ normβ β z ↔ innerβ β y y ≤ innerβ β z z :=
  Real.sqrt_le_sqrt_iff (innerβ_self_nonneg hβ z)

lemma normβ_sub_comm (y z : E → ℝ) : normβ β (y - z) = normβ β (z - y) := by
  have : z - y = (-1 : ℝ) • (y - z) := by funext e; simp
  rw [this, normβ, normβ, innerβ_smul_left, innerβ_smul_right]
  ring_nf

lemma normβ_smul (c : ℝ) (y : E → ℝ) : normβ β (c • y) = |c| * normβ β y := by
  rw [normβ, normβ, innerβ_smul_left, innerβ_smul_right, ← mul_assoc,
    Real.sqrt_mul (mul_self_nonneg c), Real.sqrt_mul_self_eq_abs]

/-- The `β`-norm bounds every coordinate: `β_e y_e² ≤ ‖y‖_β²` (plumbing, from the `β`-norm to the
coordinates). -/
lemma sq_le_normβ_sq (hβ : ∀ e, 0 < β e) (y : E → ℝ) (e : E) : β e * y e ^ 2 ≤ normβ β y ^ 2 := by
  rw [normβ_sq hβ]
  have := Finset.single_le_sum (f := fun g => β g * y g * y g)
    (fun g _ => by have := (hβ g).le; rw [mul_assoc]; exact mul_nonneg this (mul_self_nonneg _))
    (Finset.mem_univ e)
  calc β e * y e ^ 2 = β e * y e * y e := by ring
    _ ≤ _ := this

end Inner

/-! ### Step (1): completing the square -/

omit [DecidableEq E] in
/-- Step (1) of the proof of `lem:pwaffine`, completing the square: with `t_e = m_e/β_e`,
`U_A(x | α) = α²/2 ‖t‖_β² − 1/2 ‖x − αt‖_β²`. Section 3 states it before the lemma
(`stoc-sections/06-optimal-share.tex:5-12`), as
`U_A(x | α) = α²/2 ∑_e m_e²/β_e − 1/2 ∑_e β_e (x_e − α m_e/β_e)²`. -/
lemma utility_eq_normβ (hβ : ∀ e, 0 < β e) (α : ℝ) (x : E → ℝ) :
    utility m β α x = α ^ 2 / 2 * normβ β (fun e => m e / β e) ^ 2 -
      1 / 2 * normβ β (x - α • fun e => m e / β e) ^ 2 := by
  rw [normβ_sq hβ, normβ_sq hβ]
  simp only [utility_eq_sum, innerβ, Finset.mul_sum, ← Finset.sum_sub_distrib, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  have := (hβ e).ne'
  field_simp
  ring

omit [DecidableEq E] in
/-- Step (1): on any action set `C`, the best responses to `α` are the projections of `αt` onto
`C`, as `U_A(· | α)` is `α²/2 ‖t‖_β²` minus half the squared distance to `αt`. -/
theorem isBestResponse_iff_isProjβ (hβ : ∀ e, 0 < β e) {C : Set (E → ℝ)} {α : ℝ}
    {x : E → ℝ} : IsBestResponse C m β α x ↔ IsProjβ β C (α • fun e => m e / β e) x := by
  unfold IsBestResponse IsProjβ
  refine and_congr_right fun _ => forall₂_congr fun z _ => ?_
  rw [utility_eq_normβ hβ, utility_eq_normβ hβ, normβ_sub_comm _ x, normβ_sub_comm _ z]
  rw [← pow_le_pow_iff_left₀ (normβ_nonneg _) (normβ_nonneg _) two_ne_zero]
  constructor <;> intro h <;> linarith

/-- Step (1): `x*(α)` is the projection of `αt` onto `P₊(f)`; the sentence of Section 3 before the
lemma, "In other words, `x*(α)` is the projection of the preferred allocation `z(α) = αt` onto
`P₊(f)` in the inner product `uᵀ diag(β) v`" (`stoc-sections/06-optimal-share.tex:13`). -/
theorem bestResponse_isProjβ (hf : IsRankFunction f) (hβ : ∀ e, 0 < β e) (α : ℝ) :
    IsProjβ β (indepPoly f) (α • fun e => m e / β e) (bestResponse f m β α) :=
  (isBestResponse_iff_isProjβ hβ).1 (isBestResponse_bestResponse hf m β α)

/-! ### Step (3): projections and normal cones -/

omit [DecidableEq E] in
/-- Step (3) of the proof of `lem:pwaffine` (not in the paper: the STOC version cites it, [BC17,
Prop. 6.47]): `x` is the projection of `z` onto a convex set `C` exactly when `z − x ∈ N(x)`. The
projections of `z` are the best responses to the share `1` for the rewards `β_e z_e`
(`isBestResponse_iff_isProjβ`), whose marginals at `x` are `β_e (z_e − x_e)`, so this is their
first-order condition (`IsBestResponse.foc`, `isBestResponse_of_foc`). -/
theorem isProjβ_iff_mem_normalCone (hβ : ∀ e, 0 < β e) {C : Set (E → ℝ)} (hC : Convex ℝ C)
    {z x : E → ℝ} : IsProjβ β C z x ↔ x ∈ C ∧ z - x ∈ normalCone β C x := by
  have hz : ((1 : ℝ) • fun e => (fun e => β e * z e) e / β e) = z := by
    funext e
    simp [(hβ e).ne']
  have key : IsProjβ β C z x ↔ IsBestResponse C (fun e => β e * z e) β 1 x := by
    rw [isBestResponse_iff_isProjβ hβ, hz]
  have hmarg : ∀ y, ∑ e, marg (fun e => β e * z e) β 1 x e * (y e - x e) =
      innerβ β (z - x) (y - x) := by
    intro y
    simp only [marg, innerβ, Pi.sub_apply]
    exact Finset.sum_congr rfl fun e _ => by ring
  rw [key]
  constructor
  · intro h
    exact ⟨h.1, fun y hy => (hmarg y) ▸ h.foc hC hy⟩
  · rintro ⟨hx, hu⟩
    exact isBestResponse_of_foc (fun e => (hβ e).le) hx fun y hy => (hmarg y).symm ▸ hu y hy

omit [DecidableEq E] in
/-- Uniqueness of the projection onto a convex set (not in the paper: the STOC version presupposes
it by writing "the projection"). By step (3), `(z − x)ᵀD(x' − x) ≤ 0` and `(z − x')ᵀD(x − x') ≤ 0`,
which add up to `‖x' − x‖_β² ≤ 0`. -/
theorem IsProjβ.unique (hβ : ∀ e, 0 < β e) {C : Set (E → ℝ)} (hC : Convex ℝ C) {z x x' : E → ℝ}
    (h : IsProjβ β C z x) (h' : IsProjβ β C z x') : x = x' := by
  have h1 := ((isProjβ_iff_mem_normalCone hβ hC).1 h).2 x' h'.1
  have h2 := ((isProjβ_iff_mem_normalCone hβ hC).1 h').2 x h.1
  have hsum : innerβ β (z - x) (x' - x) + innerβ β (z - x') (x - x') =
      innerβ β (x' - x) (x' - x) := by
    simp only [innerβ, ← Finset.sum_add_distrib, Pi.sub_apply]
    exact Finset.sum_congr rfl fun e _ => by ring
  have h0 : innerβ β (x' - x) (x' - x) ≤ 0 := by linarith
  exact (sub_eq_zero.1 (eq_of_innerβ_self_nonpos hβ h0)).symm

/-! ### Step (2): continuity -/

omit [DecidableEq E] in
/-- Nonexpansiveness of projections (not in the paper: the STOC version cites it, [BC17,
Prop. 4.16]): for projections `p` of `z` and `p'` of `z'` onto a convex set,
`‖p − p'‖_β ≤ ‖z − z'‖_β`. By step (3), `(z − p)ᵀD(p' − p) ≤ 0` and `(z' − p')ᵀD(p − p') ≤ 0`;
adding them gives `‖p − p'‖_β² ≤ (z − z')ᵀD(p − p') ≤ (‖z − z'‖_β² + ‖p − p'‖_β²)/2`. -/
theorem IsProjβ.normβ_sub_le (hβ : ∀ e, 0 < β e) {C : Set (E → ℝ)} (hC : Convex ℝ C)
    {z z' p p' : E → ℝ} (hp : IsProjβ β C z p) (hp' : IsProjβ β C z' p') :
    normβ β (p - p') ≤ normβ β (z - z') := by
  have h1 := ((isProjβ_iff_mem_normalCone hβ hC).1 hp).2 p' hp'.1
  have h2 := ((isProjβ_iff_mem_normalCone hβ hC).1 hp').2 p hp.1
  rw [normβ_le_normβ_iff hβ]
  have hsum : innerβ β (z - p) (p' - p) + innerβ β (z' - p') (p - p') =
      innerβ β (p - p') (p - p') - innerβ β (z - z') (p - p') := by
    simp only [innerβ, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Pi.sub_apply]
    exact Finset.sum_congr rfl fun e _ => by ring
  have hsq : innerβ β ((z - z') - (p - p')) ((z - z') - (p - p')) =
      innerβ β (z - z') (z - z') - 2 * innerβ β (z - z') (p - p') +
        innerβ β (p - p') (p - p') := by
    simp only [innerβ, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      Pi.sub_apply]
    exact Finset.sum_congr rfl fun e _ => by ring
  have h0 := innerβ_self_nonneg hβ ((z - z') - (p - p'))
  linarith

/-- Step (2): nonexpansiveness of projections gives `‖x*(α) − x*(α')‖_β ≤ |α − α'| ‖t‖_β`. -/
theorem normβ_bestResponse_sub_le (hf : IsRankFunction f) (hβ : ∀ e, 0 < β e) (α α' : ℝ) :
    normβ β (bestResponse f m β α - bestResponse f m β α') ≤
      |α - α'| * normβ β (fun e => m e / β e) := by
  have h := (bestResponse_isProjβ (m := m) hf hβ α).normβ_sub_le hβ (convex_indepPoly f)
    (bestResponse_isProjβ (m := m) hf hβ α')
  rwa [← sub_smul, normβ_smul] at h

omit [DecidableEq E] in
/-- From the `β`-norm to continuity (plumbing): if `‖g(α) − g(α')‖_β ≤ |α − α'| C` for all
shares, then every coordinate of `g` is Lipschitz, as `√β_e |g_e(α) − g_e(α')| ≤ ‖g(α) − g(α')‖_β`,
and `g` is continuous. -/
theorem continuous_of_normβ_le (hβ : ∀ e, 0 < β e) {g : ℝ → E → ℝ} {C : ℝ}
    (h : ∀ α α', normβ β (g α - g α') ≤ |α - α'| * C) : Continuous g := by
  refine continuous_pi fun e => ?_
  have hs : 0 < Real.sqrt (β e) := Real.sqrt_pos.2 (hβ e)
  have hC : 0 ≤ C := by
    have h01 := h 0 1
    have := normβ_nonneg (β := β) (g 0 - g 1)
    norm_num at h01
    linarith
  set K := C / Real.sqrt (β e)
  have hK : 0 ≤ K := div_nonneg hC hs.le
  refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal K) fun α α' => ?_).continuous
  rw [Real.coe_toNNReal _ hK, Real.dist_eq, Real.dist_eq]
  set d := g α - g α'
  have h1 : Real.sqrt (β e) * |d e| ≤ normβ β d := by
    rw [← Real.sqrt_sq (abs_nonneg (d e)), ← Real.sqrt_mul (hβ e).le]
    rw [← Real.sqrt_sq (normβ_nonneg d)]
    exact Real.sqrt_le_sqrt (by rw [sq_abs]; exact sq_le_normβ_sq hβ d e)
  have h2 := h α α'
  have hde : d e = g α e - g α' e := rfl
  rw [← hde, div_mul_eq_mul_div, le_div_iff₀ hs]
  nlinarith [abs_nonneg (d e)]

/-- Step (2), continuity: `x*` is continuous, by `normβ_bestResponse_sub_le`. -/
theorem continuous_bestResponse (hf : IsRankFunction f) (hβ : ∀ e, 0 < β e) :
    Continuous (bestResponse f m β) :=
  continuous_of_normβ_le hβ (normβ_bestResponse_sub_le hf hβ)

/-! ### Step (4): the normal cone is constant on the relative interior of a face -/

omit [DecidableEq E] in
/-- Membership in the relative interior (plumbing: Mathlib's `intrinsicInterior`, the interior of
`F` within its affine hull, unfolded): `x ∈ relint F` if and only if `x ∈ F` and some ball about
`x` meets `aff F` only in points of `F`. -/
theorem mem_intrinsicInterior_iff {F : Set (E → ℝ)} {x : E → ℝ} :
    x ∈ intrinsicInterior ℝ F ↔
      x ∈ F ∧ ∃ ε > 0, ∀ y ∈ affineSpan ℝ F, dist y x < ε → y ∈ F := by
  constructor
  · rintro ⟨⟨y, hyA⟩, hy, rfl⟩
    rw [mem_interior_iff_mem_nhds, mem_nhds_subtype] at hy
    obtain ⟨u, hu, hus⟩ := hy
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hu
    refine ⟨hus (show (⟨y, hyA⟩ : affineSpan ℝ F) ∈ Subtype.val ⁻¹' u from
      hball (Metric.mem_ball_self hε)), ε, hε, fun z hz hzd => ?_⟩
    exact hus (show (⟨z, hz⟩ : affineSpan ℝ F) ∈ Subtype.val ⁻¹' u from hball hzd)
  · rintro ⟨hx, ε, hε, h⟩
    refine ⟨⟨x, subset_affineSpan ℝ F hx⟩, ?_, rfl⟩
    rw [mem_interior_iff_mem_nhds, mem_nhds_subtype]
    exact ⟨Metric.ball x ε, Metric.ball_mem_nhds x hε, fun z hz => h z z.2 hz⟩

omit [DecidableEq E] in
/-- Step (4): a normal at a point `x` of `relint F`, for `F ⊆ P₊(f)`, is orthogonal to every
direction `d` parallel to `F`: for small `s`, both `x + s d` and `x − s d` lie in `F`. -/
theorem innerβ_eq_zero_of_mem_relint {F : Set (E → ℝ)} (hFP : F ⊆ indepPoly f)
    {x u d : E → ℝ} (hx : x ∈ intrinsicInterior ℝ F) (hu : u ∈ normalCone β (indepPoly f) x)
    (hd : d ∈ vectorSpan ℝ F) : innerβ β u d = 0 := by
  obtain ⟨hxF, ε, hε, hball⟩ := mem_intrinsicInterior_iff.1 hx
  set δ := ε / (2 * (‖d‖ + 1))
  have hδ : 0 < δ := by positivity
  have hδd : δ * ‖d‖ < ε := by
    have h1 : δ * (2 * (‖d‖ + 1)) = ε := div_mul_cancel₀ _ (by positivity)
    nlinarith [norm_nonneg d]
  have hmem : ∀ s : ℝ, |s| ≤ δ → x + s • d ∈ F := by
    intro s hs
    refine hball _ ?_ ?_
    · have hdir : s • d ∈ (affineSpan ℝ F).direction := by
        rw [direction_affineSpan]
        exact Submodule.smul_mem _ s hd
      have := AffineSubspace.vadd_mem_of_mem_direction hdir (subset_affineSpan ℝ F hxF)
      rwa [vadd_eq_add, add_comm] at this
    · rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hs (norm_nonneg _)) hδd
  have h1 := hu _ (hFP (hmem δ (by rw [abs_of_pos hδ])))
  have h2 := hu _ (hFP (hmem (-δ) (by rw [abs_neg, abs_of_pos hδ])))
  rw [add_sub_cancel_left, innerβ_smul_right] at h1 h2
  nlinarith

omit [DecidableEq E] in
/-- Step (4): "… and hence is normal at every other point of `relint F`": a normal at `x` is normal
at every other point `x'` of `relint F`, as `x − x'` is parallel to `F`. -/
theorem mem_normalCone_of_mem_relint {F : Set (E → ℝ)} (hFP : F ⊆ indepPoly f)
    {x x' u : E → ℝ} (hx : x ∈ intrinsicInterior ℝ F) (hx' : x' ∈ intrinsicInterior ℝ F)
    (hu : u ∈ normalCone β (indepPoly f) x) : u ∈ normalCone β (indepPoly f) x' := by
  intro y hy
  have hd : x - x' ∈ vectorSpan ℝ F :=
    vsub_mem_vectorSpan ℝ (intrinsicInterior_subset hx) (intrinsicInterior_subset hx')
  have h0 := innerβ_eq_zero_of_mem_relint hFP hx hu hd
  have : y - x' = (y - x) + (x - x') := by abel
  rw [this, innerβ_add_right]
  linarith [hu y hy]

/-- `N(F)`: the normal cone of `P₊(f)` at the points of `relint F`, the same at all of them
(`normalCone_eq_faceNormal`). -/
def faceNormal (β : E → ℝ) (f : Finset E → ℝ) (F : Set (E → ℝ)) : Set (E → ℝ) :=
  {u | ∀ x ∈ intrinsicInterior ℝ F, u ∈ normalCone β (indepPoly f) x}

omit [DecidableEq E] in
/-- Step (4): the normal cone is constant on `relint F`; it is `N(F)`. -/
theorem normalCone_eq_faceNormal {F : Set (E → ℝ)} (hFP : F ⊆ indepPoly f) {x : E → ℝ}
    (hx : x ∈ intrinsicInterior ℝ F) : normalCone β (indepPoly f) x = faceNormal β f F := by
  ext u
  exact ⟨fun hu x' hx' => mem_normalCone_of_mem_relint hFP hx hx' hu, fun hu => hu x hx⟩

/-! ### Faces of `P₊(f)` -/

/-- The face of `P₊(f)` on which the inequalities `x_e ≥ 0`, `e ∈ Z`, and `x(S) ≤ f(S)`,
`S ∈ 𝒯`, hold with equality. -/
def indepFace (f : Finset E → ℝ) (Z : Finset E) (𝒯 : Finset (Finset E)) : Set (E → ℝ) :=
  {x | x ∈ indepPoly f ∧ (∀ e ∈ Z, x e = 0) ∧ ∀ S ∈ 𝒯, ∑ e ∈ S, x e = f S}

/-- The faces of the polyhedron `P₊(f)`: the nonempty sets `indepFace f Z 𝒯`. -/
def indepFaces (f : Finset E → ℝ) : Set (Set (E → ℝ)) :=
  {F | F.Nonempty ∧ ∃ Z 𝒯, F = indepFace f Z 𝒯}

omit [Fintype E] [DecidableEq E] in
lemma subset_indepPoly_of_mem_indepFaces {F : Set (E → ℝ)} (hF : F ∈ indepFaces f) :
    F ⊆ indepPoly f := by
  obtain ⟨-, Z, 𝒯, rfl⟩ := hF
  exact fun x hx => hx.1

omit [Fintype E] [DecidableEq E] in
/-- A face of `P₊(f)` is convex (not in the paper: the STOC version uses it without proof, in
"since this set is convex" of step (5)): it is `P₊(f)` intersected with hyperplanes. -/
lemma convex_of_mem_indepFaces {F : Set (E → ℝ)} (hF : F ∈ indepFaces f) : Convex ℝ F := by
  obtain ⟨-, Z, 𝒯, rfl⟩ := hF
  intro x hx y hy a b ha hb hab
  refine ⟨convex_indepPoly f hx.1 hy.1 ha hb hab, fun e he => ?_, fun S hS => ?_⟩
  · simp [hx.2.1 e he, hy.2.1 e he]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hx.2.2 S hS, hy.2.2 S hS]
    rw [← add_mul, hab, one_mul]

/-! ### Steps (5) and (6): convexity, and projections onto affine subspaces -/

omit [DecidableEq E] in
/-- The relative interior of a convex set is convex (not in the paper: the STOC version uses it
without proof, in "since this set is convex"). For `z = a x + b y` with `a > 0`, the ball of
radius `a ε` about `z` in `aff F` is `a` times the ball of radius `ε` about `x` plus `b y`. -/
theorem convex_intrinsicInterior {F : Set (E → ℝ)} (hF : Convex ℝ F) :
    Convex ℝ (intrinsicInterior ℝ F) := by
  intro x hx y hy a b ha hb hab
  rw [mem_intrinsicInterior_iff] at hx hy ⊢
  obtain ⟨hxF, ε, hε, hball⟩ := hx
  refine ⟨hF hxF hy.1 ha hb hab, ?_⟩
  rcases ha.lt_or_eq with ha' | ha'
  · refine ⟨a * ε, mul_pos ha' hε, fun w hw hwd => ?_⟩
    set z := a • x + b • y
    set w' := x + a⁻¹ • (w - z)
    have hxA := subset_affineSpan ℝ F hxF
    have hyA := subset_affineSpan ℝ F hy.1
    have hzA : z ∈ affineSpan ℝ F := by
      have := AffineSubspace.smul_vsub_vadd_mem (affineSpan ℝ F) b hyA hxA hxA
      have hz : b • (y -ᵥ x) +ᵥ x = z := by
        simp only [vsub_eq_sub, vadd_eq_add, z]
        rw [show a = 1 - b by linarith]
        module
      rwa [hz] at this
    have hw'A : w' ∈ affineSpan ℝ F := by
      have := AffineSubspace.smul_vsub_vadd_mem (affineSpan ℝ F) a⁻¹ hw hzA hxA
      simpa [vsub_eq_sub, vadd_eq_add, w', add_comm] using this
    have hw'd : dist w' x < ε := by
      rw [dist_eq_norm, show w' - x = a⁻¹ • (w - z) by simp [w'], norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 ha'), ← dist_eq_norm]
      rw [inv_mul_lt_iff₀ ha']
      exact hwd
    have hw : w = a • w' + b • y := by
      simp only [w', z]
      rw [smul_add, smul_smul, mul_inv_cancel₀ ha'.ne', one_smul]
      abel
    rw [hw]
    exact hF (hball w' hw'A hw'd) hy.1 ha hb hab
  · obtain ⟨hyF, ε, hε, hball'⟩ := hy
    have hb1 : b = 1 := by linarith
    exact ⟨ε, hε, fun w hw hwd => hball' w hw (by simpa [← ha', hb1] using hwd)⟩

omit [DecidableEq E] in
/-- `N(F)` is convex, as an intersection of half-spaces (not in the paper: the STOC version uses it
without proof, in "since this set is convex" of step (5)). -/
lemma convex_faceNormal {F : Set (E → ℝ)} : Convex ℝ (faceNormal β f F) := by
  intro u hu v hv a b ha hb _ x hx y hy
  have h1 := hu x hx y hy
  have h2 := hv x hx y hy
  show innerβ β (a • u + b • v) (y - x) ≤ 0
  rw [innerβ_add_left, innerβ_smul_left, innerβ_smul_left]
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha h1) (mul_nonpos_of_nonneg_of_nonpos hb h2)

omit [DecidableEq E] in
/-- The projection onto an affine subspace is affine (not in the paper: the STOC version uses it
without proof, in "the projection onto `aff F`, hence affine in `α`"): if `x₁` and `x₂` are the
projections of `z₁` and `z₂` onto an affine subspace `A`, then `x₁ + c (x₂ − x₁)` is the projection
of `z₁ + c (z₂ − z₁)`, for every real `c`. The normals `z_i − x_i` are orthogonal to the direction
of `A`, by step (3) applied at `x_i ± d`. -/
theorem IsProjβ.lineMap (hβ : ∀ e, 0 < β e) {A : AffineSubspace ℝ (E → ℝ)}
    {z₁ z₂ x₁ x₂ : E → ℝ} (h₁ : IsProjβ β A z₁ x₁) (h₂ : IsProjβ β A z₂ x₂) (c : ℝ) :
    IsProjβ β A (z₁ + c • (z₂ - z₁)) (x₁ + c • (x₂ - x₁)) := by
  rw [isProjβ_iff_mem_normalCone hβ A.convex] at h₁ h₂ ⊢
  have horth : ∀ {x z : E → ℝ}, x ∈ A → z - x ∈ normalCone β A x →
      ∀ d ∈ A.direction, innerβ β (z - x) d = 0 := by
    intro x z hx hu d hd
    have h1 := hu (d + x) (AffineSubspace.vadd_mem_of_mem_direction hd hx)
    have h2 := hu (-d + x) (AffineSubspace.vadd_mem_of_mem_direction (A.direction.neg_mem hd) hx)
    rw [add_sub_cancel_right] at h1 h2
    rw [innerβ_neg_right] at h2
    linarith
  have hx : x₁ + c • (x₂ - x₁) ∈ A := by
    have := AffineMap.lineMap_mem (Q := A) c h₁.1 h₂.1
    rwa [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm] at this
  refine ⟨hx, fun y hy => ?_⟩
  have hd : y - (x₁ + c • (x₂ - x₁)) ∈ A.direction := AffineSubspace.vsub_mem_direction hy hx
  have hsplit : (z₁ + c • (z₂ - z₁)) - (x₁ + c • (x₂ - x₁)) =
      (1 - c) • (z₁ - x₁) + c • (z₂ - x₂) := by
    module
  rw [hsplit, innerβ_add_left, innerβ_smul_left, innerβ_smul_left, horth h₁.1 h₁.2 _ hd,
    horth h₂.1 h₂.2 _ hd]
  simp

/-! ### Step (7): finitely many faces -/

omit [DecidableEq E] in
/-- Step (7): `P₊(f)` has finitely many faces. -/
theorem indepFaces_finite : (indepFaces f).Finite :=
  (Set.finite_range fun p : Finset E × Finset (Finset E) => indepFace f p.1 p.2).subset
    fun _ ⟨_, Z, 𝒯, hF⟩ => ⟨(Z, 𝒯), hF.symm⟩

/-! ### The steps the STOC version leaves implicit -/

omit [DecidableEq E] in
/-- Every point of `P₊(f)` lies in the relative interior of a face (not in the paper: the STOC
version leaves implicit that the intervals of step (5) cover `[0, ∞)`). The point `x` lies in
the relative interior of the face on which exactly its tight inequalities hold with equality:
near `x`, a point of its affine hull satisfies these with equality and the others strictly. -/
theorem exists_face_mem_relint {x : E → ℝ} (hx : x ∈ indepPoly f) :
    ∃ F ∈ indepFaces f, x ∈ intrinsicInterior ℝ F := by
  classical
  set Z := Finset.univ.filter fun e => x e = 0
  set 𝒯 := Finset.univ.filter fun S : Finset E => ∑ e ∈ S, x e = f S
  have hxF : x ∈ indepFace f Z 𝒯 :=
    ⟨hx, fun e he => (Finset.mem_filter.1 he).2, fun S hS => (Finset.mem_filter.1 hS).2⟩
  refine ⟨indepFace f Z 𝒯, ⟨⟨x, hxF⟩, Z, 𝒯, rfl⟩, mem_intrinsicInterior_iff.2 ⟨hxF, ?_⟩⟩
  -- The affine subspace on which the inequalities of `Z` and `𝒯` hold with equality.
  let L : AffineSubspace ℝ (E → ℝ) :=
    { carrier := {y | (∀ e ∈ Z, y e = 0) ∧ ∀ S ∈ 𝒯, ∑ e ∈ S, y e = f S}
      smul_vsub_vadd_mem' := by
        intro c p₁ p₂ p₃ h₁ h₂ h₃
        refine ⟨fun e he => ?_, fun S hS => ?_⟩
        · simp [h₁.1 e he, h₂.1 e he, h₃.1 e he]
        · simp only [vsub_eq_sub, vadd_eq_add, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
            smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
            h₁.2 S hS, h₂.2 S hS, h₃.2 S hS]
          ring }
  have hFL : affineSpan ℝ (indepFace f Z 𝒯) ≤ L :=
    affineSpan_le.2 fun y hy => ⟨hy.2.1, hy.2.2⟩
  -- `ε` below every positive coordinate of `x` and every slack divided by `n + 1`
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (∀ e, e ∉ Z → ε ≤ x e) ∧
      ∀ S : Finset E, S ∉ 𝒯 → (Fintype.card E + 1) * ε ≤ f S - ∑ e ∈ S, x e := by
    refine (Filter.eventually_all.2 fun e => ?_).and (Filter.eventually_all.2 fun S => ?_)
    · by_cases he : e ∈ Z
      · exact Filter.Eventually.of_forall fun _ h => absurd he h
      · have hpos : 0 < x e := lt_of_le_of_ne (hx.1 e) fun h =>
          he (Finset.mem_filter.2 ⟨Finset.mem_univ e, h.symm⟩)
        filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds hpos)] with ε hε _ using hε.le
    · by_cases hS : S ∈ 𝒯
      · exact Filter.Eventually.of_forall fun _ h => absurd hS h
      · have hpos : 0 < f S - ∑ e ∈ S, x e := sub_pos.2 (lt_of_le_of_ne (hx.2 S) fun h =>
          hS (Finset.mem_filter.2 ⟨Finset.mem_univ S, h⟩))
        have hc : Continuous fun ε : ℝ => (Fintype.card E + 1) * ε := by fun_prop
        have := hc.tendsto 0
        rw [mul_zero] at this
        filter_upwards [nhdsWithin_le_nhds (this.eventually_lt_const hpos)] with ε hε _
          using hε.le
  obtain ⟨ε, hε, hεpos⟩ := (hev.and self_mem_nhdsWithin).exists
  refine ⟨ε, hεpos, fun y hy hyx => ?_⟩
  have hyL := hFL hy
  have hcoord : ∀ e, |y e - x e| < ε := fun e => by
    have := (dist_pi_lt_iff hεpos).1 hyx e
    rwa [Real.dist_eq] at this
  refine ⟨⟨fun e => ?_, fun S => ?_⟩, hyL.1, hyL.2⟩
  · by_cases he : e ∈ Z
    · rw [hyL.1 e he]
    · have h1 := hε.1 e he
      have h2 := hcoord e
      rw [abs_lt] at h2
      linarith
  · by_cases hS : S ∈ 𝒯
    · rw [hyL.2 S hS]
    · have h1 := hε.2 S hS
      have h2 : ∑ e ∈ S, y e - ∑ e ∈ S, x e ≤ S.card * ε := by
        rw [← Finset.sum_sub_distrib]
        calc ∑ e ∈ S, (y e - x e) ≤ ∑ _e ∈ S, ε :=
              Finset.sum_le_sum fun e _ => (le_abs_self _).trans (hcoord e).le
          _ = S.card * ε := by rw [Finset.sum_const, nsmul_eq_mul]
      have h3 : (S.card : ℝ) ≤ Fintype.card E + 1 := by
        have := Finset.card_le_univ S
        have : (S.card : ℝ) ≤ Fintype.card E := by exact_mod_cast this
        linarith
      nlinarith

omit [Fintype E] [DecidableEq E] in
/-- Finitely many intervals of affinity leave finitely many breakpoints (not in the paper: the
STOC version leaves this implicit). If finitely many intervals cover `[0, ∞)` and `g` is affine
on each of them, then every breakpoint of `g` is an end of one of them. -/
theorem breakpoints_finite_of_cover {g : ℝ → E → ℝ} (𝓙 : Finset (Set ℝ))
    (hcov : (⋃ J ∈ 𝓙, J) = Set.Ici 0)
    (hJ : ∀ J ∈ 𝓙, J.OrdConnected ∧ ∃ a b : E → ℝ, ∀ α ∈ J, g α = fun e => a e + α * b e) :
    (breakpoints g).Finite := by
  classical
  set T : Finset ℝ := 𝓙.image sInf ∪ 𝓙.image sSup
  refine T.finite_toSet.subset fun α ⟨hα, hnot⟩ => ?_
  by_contra hT
  apply hnot
  have hαcov : α ∈ ⋃ J ∈ 𝓙, J := by rw [hcov]; exact hα.le
  obtain ⟨J, hJ𝓙, hαJ⟩ := Set.mem_iUnion₂.1 hαcov
  obtain ⟨hJo, a, b, hab⟩ := hJ J hJ𝓙
  have hJ0 : ∀ γ ∈ J, (0 : ℝ) ≤ γ := fun γ hγ => by
    have : γ ∈ ⋃ J ∈ 𝓙, J := Set.mem_biUnion hJ𝓙 hγ
    rw [hcov] at this
    exact this
  have hinf : sInf J ≠ α := fun h =>
    hT (Finset.mem_union_left _ (Finset.mem_image.2 ⟨J, hJ𝓙, h⟩))
  have hsup : sSup J ≠ α := fun h =>
    hT (Finset.mem_union_right _ (Finset.mem_image.2 ⟨J, hJ𝓙, h⟩))
  have hbdd : BddBelow J := ⟨0, hJ0⟩
  obtain ⟨α₁, h₁, hlt₁⟩ : ∃ α₁ ∈ J, α₁ < α :=
    exists_lt_of_csInf_lt ⟨α, hαJ⟩ (lt_of_le_of_ne (csInf_le hbdd hαJ) hinf)
  obtain ⟨α₂, h₂, hlt₂⟩ : ∃ α₂ ∈ J, α < α₂ := by
    by_cases hb : BddAbove J
    · exact exists_lt_of_lt_csSup ⟨α, hαJ⟩ (lt_of_le_of_ne (le_csSup hb hαJ) hsup.symm)
    · rw [not_bddAbove_iff] at hb
      exact hb α
  refine ⟨min (α - α₁) (α₂ - α), lt_min (by linarith) (by linarith), a, b,
    fun α' hα' => hab α' (hJo.out h₁ h₂ ⟨?_, ?_⟩)⟩
  · have := hα'.1
    have := min_le_left (α - α₁) (α₂ - α)
    linarith
  · have := hα'.2
    have := min_le_right (α - α₁) (α₂ - α)
    linarith

/-! ### `lem:pwaffine` -/

/-- The shares `α ≥ 0` with `x*(α) ∈ relint F`. -/
def relintShares (f : Finset E → ℝ) (m β : E → ℝ) (F : Set (E → ℝ)) : Set ℝ :=
  {α | 0 ≤ α ∧ bestResponse f m β α ∈ intrinsicInterior ℝ F}

/-- The proof of `lem:pwaffine` (`stoc-sections/appB-quadratic.tex:254-273`), step by step, for
every `m` (it does not use `m ≥ 0`): `x*` is continuous, finitely many intervals cover `[0, ∞)` with
`x*` affine on each, so `x*` has finitely many breakpoints, and `x*(α)` is the projection of `αt`
onto `P₊(f)`. The intervals are the sets `relintShares f m β F` of shares `α ≥ 0` with
`x*(α) ∈ relint F`, one for each face `F` of `P₊(f)`. -/
theorem pwaffine_aux (hf : IsRankFunction f) (hβ : ∀ e, 0 < β e) :
    Continuous (bestResponse f m β) ∧
      (∃ 𝓙 : Finset (Set ℝ), (⋃ J ∈ 𝓙, J) = Set.Ici 0 ∧ ∀ J ∈ 𝓙, J.OrdConnected ∧
        ∃ a b : E → ℝ, ∀ α ∈ J, bestResponse f m β α = fun e => a e + α * b e) ∧
      (breakpoints (bestResponse f m β)).Finite ∧
      ∀ α, IsProjβ β (indepPoly f) (α • fun e => m e / β e) (bestResponse f m β α) := by
  classical
  set t : E → ℝ := fun e => m e / β e with ht
  have hP : Convex ℝ (indepPoly f) := convex_indepPoly f
  -- (1) "For the inner product `yᵀDz` with `D := diag(β)` and its norm `‖y‖_β := (yᵀDy)^{1/2}`,
  -- completing the square gives `U_A(x | α) = α²/2 ‖t‖_β² − 1/2 ‖x − αt‖_β²`. Thus `x*(α)` is
  -- the projection of `αt` onto `P₊(f)`."
  have h1 : ∀ α, IsProjβ β (indepPoly f) (α • t) (bestResponse f m β α) :=
    bestResponse_isProjβ hf hβ
  -- (2) "Nonexpansiveness of projections [BC17, Prop. 4.16] gives
  -- `‖x*(α) − x*(α')‖_β ≤ |α − α'| ‖t‖_β`."
  -- So `x*` is continuous.
  have h2 : ∀ α α', normβ β (bestResponse f m β α - bestResponse f m β α') ≤
      |α - α'| * normβ β t := normβ_bestResponse_sub_le hf hβ
  have hcont : Continuous (bestResponse f m β) := continuous_of_normβ_le hβ h2
  -- (3) "For `x ∈ P₊(f)`, define `N(x) := {u : uᵀD(y − x) ≤ 0 for all y ∈ P₊(f)}`. Then `x` is
  -- the projection of `z` exactly when `z − x ∈ N(x)` [BC17, Prop. 6.47]."
  have h3 : ∀ z x, IsProjβ β (indepPoly f) z x ↔
      x ∈ indepPoly f ∧ z - x ∈ normalCone β (indepPoly f) x :=
    fun _ _ => isProjβ_iff_mem_normalCone hβ hP
  -- (4) "For a face `F`, this cone is constant on `relint F`: a normal at `x ∈ relint F` is
  -- orthogonal to every direction parallel to `F`, and hence is normal at every other point of
  -- `relint F`. Denote it by `N(F)`."
  have h4o : ∀ F ∈ indepFaces f, ∀ x ∈ intrinsicInterior ℝ F,
      ∀ u ∈ normalCone β (indepPoly f) x, ∀ d ∈ vectorSpan ℝ F, innerβ β u d = 0 :=
    fun F hF _ hx _ hu _ hd =>
      innerβ_eq_zero_of_mem_relint (subset_indepPoly_of_mem_indepFaces hF) hx hu hd
  have h4 : ∀ F ∈ indepFaces f, ∀ x ∈ intrinsicInterior ℝ F,
      normalCone β (indepPoly f) x = faceNormal β f F :=
    fun F hF _ hx => normalCone_eq_faceNormal (subset_indepPoly_of_mem_indepFaces hF) hx
  -- (5) "The shares for which `x*(α) ∈ relint F` are exactly those with `αt ∈ relint F + N(F)`, …"
  have h5a : ∀ F ∈ indepFaces f, ∀ α, bestResponse f m β α ∈ intrinsicInterior ℝ F ↔
      α • t ∈ intrinsicInterior ℝ F + faceNormal β f F := by
    intro F hF α
    constructor
    · intro hx
      have hu := ((h3 _ _).1 (h1 α)).2
      rw [h4 F hF _ hx] at hu
      exact ⟨_, hx, _, hu, add_sub_cancel _ _⟩
    · rintro ⟨x, hx, u, hu, hxu⟩
      rw [← h4 F hF x hx] at hu
      have hproj : IsProjβ β (indepPoly f) (α • t) x :=
        (h3 _ _).2 ⟨subset_indepPoly_of_mem_indepFaces hF (intrinsicInterior_subset hx),
          by rw [← hxu, add_sub_cancel_left]; exact hu⟩
      rwa [(h1 α).unique hβ hP hproj]
  -- "… and they form an interval, since this set is convex."
  have h5 : ∀ F ∈ indepFaces f, (relintShares f m β F).OrdConnected := by
    intro F hF
    have hconv : Convex ℝ (intrinsicInterior ℝ F + faceNormal β f F) :=
      (convex_intrinsicInterior (convex_of_mem_indepFaces hF)).add convex_faceNormal
    have heq : relintShares f m β F = Set.Ici 0 ∩
        (fun α : ℝ => α • t) ⁻¹' (intrinsicInterior ℝ F + faceNormal β f F) := by
      ext α
      simp only [relintShares, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Ici,
        Set.mem_preimage, h5a F hF α]
    rw [heq]
    exact ((convex_Ici 0).inter
      (hconv.linear_preimage (LinearMap.smulRight LinearMap.id t))).ordConnected
  -- (6) "On this interval, `x*(α)` is the projection onto `aff F`, …" as the normal
  -- `αt − x*(α)` is orthogonal to every direction parallel to `F` (this argument is not in the
  -- paper, which states the projection without proof),
  have h6a : ∀ F ∈ indepFaces f, ∀ α ∈ relintShares f m β F,
      IsProjβ β (affineSpan ℝ F) (α • t) (bestResponse f m β α) := by
    intro F hF α hα
    have hu := ((h3 _ _).1 (h1 α)).2
    have hxA := subset_affineSpan ℝ F (intrinsicInterior_subset hα.2)
    refine (isProjβ_iff_mem_normalCone hβ (affineSpan ℝ F).convex).2 ⟨hxA, fun y hy => ?_⟩
    have hd : y - bestResponse f m β α ∈ vectorSpan ℝ F := by
      rw [← direction_affineSpan]
      exact AffineSubspace.vsub_mem_direction hy hxA
    exact (h4o F hF _ hα.2 _ hu _ hd).le
  -- "… hence affine in `α`": for shares `α₁ ≠ α₂` of the interval and `α = α₁ + c (α₂ − α₁)`
  -- in it, `x*(α)` and `x*(α₁) + c (x*(α₂) − x*(α₁))` are both the projection of `αt` onto
  -- `aff F` (`IsProjβ.lineMap`, `IsProjβ.unique`).
  have h6 : ∀ F ∈ indepFaces f, ∃ a b : E → ℝ, ∀ α ∈ relintShares f m β F,
      bestResponse f m β α = fun e => a e + α * b e := by
    intro F hF
    set J := relintShares f m β F
    by_cases hJ : ∃ α₁ ∈ J, ∃ α₂ ∈ J, α₁ ≠ α₂
    · obtain ⟨α₁, h₁, α₂, h₂, hne⟩ := hJ
      set x₁ := bestResponse f m β α₁
      set x₂ := bestResponse f m β α₂
      have hd : α₂ - α₁ ≠ 0 := sub_ne_zero.2 hne.symm
      refine ⟨fun e => x₁ e - α₁ * ((x₂ e - x₁ e) / (α₂ - α₁)),
        fun e => (x₂ e - x₁ e) / (α₂ - α₁), fun α hα => ?_⟩
      set c := (α - α₁) / (α₂ - α₁)
      have hc : α • t = α₁ • t + c • (α₂ • t - α₁ • t) := by
        funext e
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, c]
        field_simp
        ring
      have hp := (h6a F hF α₁ h₁).lineMap hβ (h6a F hF α₂ h₂) c
      rw [← hc] at hp
      rw [(h6a F hF α hα).unique hβ (affineSpan ℝ F).convex hp]
      funext e
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, c]
      field_simp
      ring
    · push Not at hJ
      by_cases hne : J.Nonempty
      · obtain ⟨α₀, h₀⟩ := hne
        exact ⟨bestResponse f m β α₀, 0, fun α hα => by rw [hJ α hα α₀ h₀]; simp⟩
      · exact ⟨0, 0, fun α hα => absurd ⟨α, hα⟩ hne⟩
  -- (7) "There are finitely many faces."
  have h7 : (indepFaces f).Finite := indepFaces_finite
  -- The intervals of the faces cover `[0, ∞)`, as every point of `P₊(f)` lies in the relative
  -- interior of a face (`exists_face_mem_relint`), so `x*` has finitely many breakpoints
  -- (`breakpoints_finite_of_cover`).
  set 𝓙 := h7.toFinset.image (relintShares f m β)
  have hcov : (⋃ J ∈ 𝓙, J) = Set.Ici 0 := by
    ext α
    simp only [𝓙, Set.mem_iUnion, Finset.mem_image, Set.Finite.mem_toFinset, exists_prop,
      Set.mem_Ici]
    constructor
    · rintro ⟨_, ⟨F, -, rfl⟩, hα⟩
      exact hα.1
    · intro hα
      obtain ⟨F, hF, hx⟩ := exists_face_mem_relint (isBestResponse_bestResponse hf m β α).1
      exact ⟨_, ⟨F, hF, rfl⟩, hα, hx⟩
  have hJ : ∀ J ∈ 𝓙, J.OrdConnected ∧ ∃ a b : E → ℝ, ∀ α ∈ J,
      bestResponse f m β α = fun e => a e + α * b e := by
    intro J hJ
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.1 hJ
    rw [Set.Finite.mem_toFinset] at hF
    exact ⟨h5 F hF, h6 F hF⟩
  exact ⟨hcont, ⟨𝓙, hcov, hJ⟩, breakpoints_finite_of_cover 𝓙 hcov hJ, h1⟩

/-- **`lem:pwaffine`** (Lemma 3.4, statement `stoc-sections/06-optimal-share.tex:20-22`, proof
`stoc-sections/appB-quadratic.tex:254-273`), under the standing assumptions of Section 3
(`Tracing.Hyp`): the map `α ↦ x*(α)` is continuous and piecewise affine on `[0, ∞)` (finitely many
intervals cover `[0, ∞)`, and `x*` is affine on each) with finitely many breakpoints. Indeed,
`x*(α)` is the projection of `z(α) = αt` onto `P₊(f)` in the inner product
`uᵀ diag(β) v = ∑_e β_e u_e v_e`.
The proof, step by step, is `pwaffine_aux`. -/
theorem pwaffine (H : Tracing.Hyp f m β) :
    ContinuousOn (bestResponse f m β) (Set.Ici 0) ∧
      (∃ 𝓙 : Finset (Set ℝ), (⋃ J ∈ 𝓙, J) = Set.Ici 0 ∧ ∀ J ∈ 𝓙, J.OrdConnected ∧
        ∃ a b : E → ℝ, ∀ α ∈ J, bestResponse f m β α = fun e => a e + α * b e) ∧
      (breakpoints (bestResponse f m β)).Finite ∧
      ∀ α, 0 ≤ α → IsProjβ β (indepPoly f) (α • fun e => m e / β e) (bestResponse f m β α) := by
  obtain ⟨h1, h2, h3, h4⟩ := pwaffine_aux (m := m) H.rank H.beta
  exact ⟨h1.continuousOn, h2, h3, fun α _ => h4 α⟩

/-- `lem:pwaffine`, piecewise affine (from `pwaffine_aux`): `[0, ∞)` is the union of finitely many
intervals on each of which `x*` is affine. -/
theorem piecewise_affine (hf : IsRankFunction f) (hβ : ∀ e, 0 < β e) :
    ∃ 𝓙 : Finset (Set ℝ), (⋃ J ∈ 𝓙, J) = Set.Ici 0 ∧ ∀ J ∈ 𝓙, J.OrdConnected ∧
      ∃ a b : E → ℝ, ∀ α ∈ J, bestResponse f m β α = fun e => a e + α * b e :=
  (pwaffine_aux hf hβ).2.1

/-- `x*` is affine on a right neighborhood `[α, α₂]` of every share `α ≥ 0` (used for
`lem:supportmon`, `Stoc/Subclasses/SupportShrinks.lean`): one of the finitely many intervals of
`piecewise_affine` contains shares arbitrarily close to `α` on the right, hence an interval
`(α, α₂]`, and continuity adds `α` (not in the paper: step (4) of the proof of `lem:supportmon`
uses it without proof). -/
theorem exists_affine_right (hf : IsRankFunction f) (hβ : ∀ e, 0 < β e) {α b : ℝ}
    (hα : 0 ≤ α) (hb : α < b) :
    ∃ α₂, α < α₂ ∧ α₂ < b ∧ ∃ p w : E → ℝ,
      ∀ γ ∈ Set.Icc α α₂, bestResponse f m β γ = fun e => p e + γ * w e := by
  classical
  obtain ⟨𝓙, hcov, hJ⟩ := piecewise_affine (m := m) hf hβ
  -- some interval of `𝓙` has shares arbitrarily close to `α` on the right
  obtain ⟨J, hJ𝓙, hJr⟩ : ∃ J ∈ 𝓙, ∃ᶠ α' in 𝓝[>] α, α' ∈ J := by
    by_contra h
    push Not at h
    have hall : ∀ᶠ α' in 𝓝[>] α, ∀ J ∈ 𝓙, α' ∉ J :=
      (Filter.eventually_all_finset 𝓙).2 fun J hJ => h J hJ
    obtain ⟨α', hα', hα'pos⟩ := (hall.and self_mem_nhdsWithin).exists
    have : α' ∈ ⋃ J ∈ 𝓙, J := by
      rw [hcov]
      exact le_of_lt (lt_of_le_of_lt hα hα'pos)
    obtain ⟨J, hJ, hα'J⟩ := Set.mem_iUnion₂.1 this
    exact hα' J hJ hα'J
  obtain ⟨hJo, p, w, haff⟩ := hJ J hJ𝓙
  have hb' : ∀ᶠ α' in 𝓝[>] α, α' < b := nhdsWithin_le_nhds (eventually_lt_nhds hb)
  obtain ⟨α₂, ⟨h₂J, hα₂b⟩, hα₂⟩ :=
    ((hJr.and_eventually hb').and_eventually self_mem_nhdsWithin).exists
  -- `(α, α₂] ⊆ J`
  have hsub : Set.Ioc α α₂ ⊆ J := by
    intro α'' hα''
    have hlt : ∀ᶠ α' in 𝓝[>] α, α' < α'' := nhdsWithin_le_nhds (eventually_lt_nhds hα''.1)
    obtain ⟨α', ⟨h'J, hα'α''⟩, hα'⟩ := ((hJr.and_eventually hlt).and_eventually
      self_mem_nhdsWithin).exists
    exact hJo.out h'J h₂J ⟨hα'α''.le, hα''.2⟩
  -- at `α` itself, by continuity
  have hαeq : bestResponse f m β α = fun e => p e + α * w e := by
    have hcl : IsClosed {α' : ℝ | bestResponse f m β α' = fun e => p e + α' * w e} :=
      isClosed_eq (continuous_bestResponse hf hβ) (by fun_prop)
    have hsub' : Set.Ioo α α₂ ⊆ {α' : ℝ | bestResponse f m β α' = fun e => p e + α' * w e} :=
      fun α' hα' => haff α' (hsub ⟨hα'.1, hα'.2.le⟩)
    have := hcl.closure_subset_iff.2 hsub'
    rw [closure_Ioo (ne_of_lt hα₂)] at this
    exact this ⟨le_rfl, (le_of_lt hα₂)⟩
  refine ⟨α₂, hα₂, hα₂b, p, w, fun γ hγ => ?_⟩
  rcases hγ.1.lt_or_eq with hlt | heq
  · exact haff γ (hsub ⟨hlt, hγ.2⟩)
  · rw [← heq]
    exact hαeq

end

end Stoc
