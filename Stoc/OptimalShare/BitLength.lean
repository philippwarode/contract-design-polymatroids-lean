-- stamp r8 2026-11-02
import Mathlib
import Stoc.OptimalShare.Tracing

/-!
# Bit lengths

The STOC version, Section 3 (`stoc-sections/06-optimal-share.tex:37-39`),
Theorem `thm:bitlength`, with its proof in Appendix B.3 (`sec:C-bitlength`,
`stoc-sections/appB-bitlength.tex:1-112`): if every `m_e`, every `β_e` and every value of `f` is a
quotient of two integers of absolute value less than `2^ν` (`IsSmall`), and `n ≤ ν`, then every
breakpoint of `x*` is a quotient of two integers of absolute value at most
`Q = (2n + 1)^{n+1} 4^{(2n+1)ν}` (`bigQ`), and some optimal contract a quotient of two integers of
absolute value at most `2nQ2^{nν}` (`bigQ'`); both have `O(nν)` bits (`logb_bigQ`,
`bigQ_le_two_pow`). The
theorem is `Stoc.BitLength.bitlength`. Its proof follows the paper's, which has four parts, each
opened by a sentence and without a label; here they are numbered (1) to (4), and their sub-steps
(a) to (d):

* (1) "We first write down the linear equations of a state." (a) Finitely many event points:
  `events_finite`, from the intervals of `lem:pwaffine` (`Stoc.pwaffine`) and the argument of
  `lem:eventcount` on each of them, at most `C(n, 2)` changes of the state (`events_in_affine`).
  For an open interval `J ∋ α₁` with constant state, the free set `Φ` and the zero set `Z` are
  `freeSet` and `zeroSet` of `Stoc/OptimalShare/Velocity.lean`, the blocks are
  `D_j = {e | ρ_e(α₁) = θ_j}` for the distinct positive marginals `θ_0 > ⋯ > θ_{k−1}` at `α₁`
  (`theta` of `Stoc/BestResponse/LayerCake.lean`; the paper's `D_1, …, D_k`, indices from 0),
  `S_j = D_0 ∪ ⋯ ∪ D_j` (`cumS`), and the equations are the paper's (`eqG`, `eqH`, with the
  unknowns `Col = (α, x, ρ_0, …, ρ_{k−1})` and the rows `Row`: one equation for each element, the
  second equation `ρ_j − m_e α = 0` of each `e ∈ D_j ∩ Z`, and `x(S_j) = f(S_j)`). Then:
  (b) `solJ_solves` (the vector `(α, x*(α), ρ(α))` solves them on `J`), (c) `determined` (for
  fixed `α` they determine `x` and `ρ`), (d) `lineJ_eq_solJ` and `solves_iff_line` (by
  `lem:velocity`, the solutions form exactly the line `lineJ`).
* (2) "Next we single out a breakpoint by one more equation": `step2_equation` ((a) `J_−`, `J_+`
  by `exists_sides`; (b) the states differ; (c) the cases of the free sets, the zero sets and the
  blocks, `eq_of_free`, `eq_of_zero`, `eq_of_block`) and `step2_cramer` ((d) the enlarged system
  `bigG`, `bigH` has the only solution `(b, x*(b), ρ^J(b))`; a nonsingular square subsystem;
  Cramer's rule `cramer_coord`).
* (3) "Next we bound the size of `b`": `rows_integral`, `rows_integral_big`,
  `ratio_of_integral_rows` (the same factor for `det G` and `det G_α`, `det_diagonal_mul`;
  Hadamard's inequality, `abs_det_le`), `hadamard_le_bigQ`, and `breakpoint_ratio`.
* (4) "Finally, we turn to an optimal contract": `exists_J_in_piece`, `xJ_eq_on_piece`,
  `step4_cramer` (with `affine_ratio_of_integral_rows`), `reward_ratio` (the reward `r⁰_I + r¹_I α`
  on the piece `I`, in the notation after `lem:pwaffine`), and the maximum on the piece
  (`Stoc.Tracing.quad_max`).

Not in the paper (D3, marked in the docstrings): the argument of `lem:eventcount` on the intervals
of `lem:pwaffine`, which the paper refers to (`events_in_affine`), Hadamard's inequality
(`det_sq_le_prod`, through the Gram–Schmidt orthogonalisation; Mathlib has none), Cramer's rule in
coordinates (`cramer_coord`, Mathlib's `Matrix.cramer` restated), the choice of `N` equations with a
nonsingular matrix (`exists_square_subsystem`), the constant state on an interval without event
points (`state_eq_of_no_event`), the existence of `J` inside a piece (`exists_J_in_piece`), the
transfer of `x^J` to the piece (`xJ_eq_on_piece`) and the existence of an optimal contract
(`exists_optimal_share`).

Taken over on 2026-10-20 from `Paper/FPTAS/BitLength.lean` (the paper at Overleaf f035b19) for the
STOC version (`stoc.tex`); from then on this copy follows the STOC version. Reworked on 2026-10-25
to follow the STOC version's proof step by step. Adapted on 2026-10-27 to the STOC version after
PR #88: the state changes at most `C(n, 2)` times on each interval of `lem:pwaffine` (it was
`2n + C(n, 2)`), by the new argument of `lem:eventcount`; the proof's labels "Step 1" to "Step 4"
became sentences, so the parts are numbered (1) to (4) here; the reward on a piece `I` is
`r⁰_I + r¹_I α` with `r⁰_I = P/(ζ ∏_e ā_e)`, `r¹_I = P'/(ζ ∏_e ā_e)` (it was `p_J + d_J α` with
`K := ζ ∏_e ā_e`), and the vertex is taken only if `r¹_I > 0` and it lies in `I`.
-/

namespace Stoc

namespace BitLength

open Finset Matrix

/-- `q` is a quotient of two integers of absolute value less than `2^ν`. -/
def IsSmall (ν : ℕ) (q : ℝ) : Prop :=
  ∃ a b : ℤ, b ≠ 0 ∧ |(a : ℝ)| < 2 ^ ν ∧ |(b : ℝ)| < 2 ^ ν ∧ q = a / b

/-- `Q = (2n + 1)^{n+1} 4^{(2n+1)ν}`, the bound of `sec:C-bitlength` on the numerators and
denominators of the breakpoints. -/
def bigQ (n ν : ℕ) : ℕ := (2 * n + 1) ^ (n + 1) * 4 ^ ((2 * n + 1) * ν)

/-! ### Linear algebra: Hadamard's inequality, square subsystems and Cramer's rule -/

section LinearAlgebra

/-- Hadamard's inequality on `Fin N`, through the Gram–Schmidt orthogonalisation of the rows (part
of the proof of `det_sq_le_prod`). -/
theorem det_sq_le_prod_fin (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) :
    A.det ^ 2 ≤ ∏ i, ∑ j, A i j ^ 2 := by
  set v : Fin N → EuclideanSpace ℝ (Fin N) := fun i => WithLp.toLp 2 (A i)
  set u := InnerProductSpace.gramSchmidt ℝ v
  set c : Fin N → Fin N → ℝ := fun i j => inner ℝ (u j) (v i) / ‖u j‖ ^ 2
  have hdef : ∀ i, v i = u i + ∑ j ∈ Finset.Iio i, c i j • u j := fun i => by
    have := InnerProductSpace.gramSchmidt_def'' ℝ v i
    simpa using this
  set U : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun i k => u i k
  set T : Matrix (Fin N) (Fin N) ℝ :=
    Matrix.of fun i j => if j = i then 1 else if j < i then c i j else 0
  have hA : A = T * U := by
    ext i k
    have h := congrArg (fun x : EuclideanSpace ℝ (Fin N) => x k) (hdef i)
    simp only [v, PiLp.add_apply, WithLp.ofLp_sum, Finset.sum_apply,
      PiLp.smul_apply, smul_eq_mul] at h
    rw [h, Matrix.mul_apply]
    have hsplit : ∀ j, T i j * U j k =
        (if j = i then u j k else 0) + (if j < i then c i j * u j k else 0) := by
      intro j
      simp only [T, U, Matrix.of_apply]
      split_ifs with h1 h2 h2
      · subst h1; exact absurd h2 (lt_irrefl _)
      · ring
      · ring
      · ring
    rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ i, ite_eq_left (Finset.mem_univ _), ← Finset.sum_filter]
    congr 2
    ext j
    simp
  have hT : T.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular T]
    · simp [T]
    · intro i j hij
      simp only [T, Matrix.of_apply]
      have hij' : i < j := by simpa using hij
      rw [ite_eq_right (ne_of_gt hij'), ite_eq_right (not_lt.2 hij'.le)]
  have hUU : U * Uᵀ = Matrix.diagonal fun i => ‖u i‖ ^ 2 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.diagonal_apply]
    simp only [U, Matrix.transpose_apply, Matrix.of_apply]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, EuclideanSpace.real_norm_sq_eq]
      exact Finset.sum_congr rfl fun k _ => by ring
    · rw [ite_eq_right hij]
      have h0 : inner ℝ (u i) (u j) = 0 := InnerProductSpace.gramSchmidt_orthogonal ℝ v hij
      simp only [PiLp.inner_apply, RCLike.inner_apply', conj_trivial] at h0
      exact h0
  have hdetU : U.det ^ 2 = ∏ i, ‖u i‖ ^ 2 := by
    have := congrArg Matrix.det hUU
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at this
    rw [← this]; ring
  have hnorm : ∀ i, ‖u i‖ ^ 2 ≤ ∑ j, A i j ^ 2 := by
    intro i
    have horth : inner ℝ (u i) (∑ j ∈ Finset.Iio i, c i j • u j) = 0 := by
      rw [inner_sum]
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [real_inner_smul_right, InnerProductSpace.gramSchmidt_orthogonal ℝ v
        (ne_of_gt (Finset.mem_Iio.1 hj)), mul_zero]
    have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
    rw [← hdef i] at hpy
    have hv : ‖v i‖ ^ 2 = ∑ j, A i j ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
    nlinarith [mul_self_nonneg ‖∑ j ∈ Finset.Iio i, c i j • u j‖]
  calc A.det ^ 2 = U.det ^ 2 := by rw [hA, Matrix.det_mul, hT, one_mul]
    _ = ∏ i, ‖u i‖ ^ 2 := hdetU
    _ ≤ ∏ i, ∑ j, A i j ^ 2 :=
        Finset.prod_le_prod₀ (fun i _ => sq_nonneg _) fun i _ => hnorm i

/-- Hadamard's inequality, `(det A)² ≤ ∏ᵢ ∑ⱼ A_ij²` (not in the paper: the proof of
`thm:bitlength` cites it in (3), "By Hadamard's inequality, both determinants then have absolute
value at most `(√N 4^ν)^N ≤ Q`"). -/
theorem det_sq_le_prod {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) :
    A.det ^ 2 ≤ ∏ i, ∑ j, A i j ^ 2 := by
  set e := Fintype.equivFin n
  have h := det_sq_le_prod_fin _ (Matrix.reindex e e A)
  rw [Matrix.det_reindex_self] at h
  have h2 : ∏ i, ∑ j, (Matrix.reindex e e A) i j ^ 2 = ∏ i, ∑ j, A i j ^ 2 := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [Equiv.prod_comp e.symm (fun i => ∑ j : Fin _, A i (e.symm j) ^ 2)]
    exact Finset.prod_congr rfl fun i _ => Equiv.sum_comp e.symm (fun j => A i j ^ 2)
  rwa [h2] at h

/-- Hadamard's inequality for an `N × N` matrix with entries of absolute value at most `X`:
`|det A| ≤ (√N X)^N` (part of the D3 lemma `det_sq_le_prod`). -/
theorem abs_det_le {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) {X : ℝ}
    (hX0 : 0 ≤ X) (hX : ∀ i j, |A i j| ≤ X) :
    |A.det| ≤ (Real.sqrt (Fintype.card n) * X) ^ Fintype.card n := by
  have h1 : A.det ^ 2 ≤ ((Real.sqrt (Fintype.card n) * X) ^ Fintype.card n) ^ 2 := by
    refine (det_sq_le_prod A).trans ?_
    calc ∏ i, ∑ j, A i j ^ 2 ≤ ∏ _i : n, ∑ _j : n, X ^ 2 :=
          Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
            fun i _ => Finset.sum_le_sum fun j _ => by
              nlinarith [sq_abs (A i j), abs_nonneg (A i j), hX i j]
      _ = ((Real.sqrt (Fintype.card n) * X) ^ Fintype.card n) ^ 2 := by
          rw [Finset.prod_const, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← pow_mul,
            mul_comm (Fintype.card n) 2, pow_mul]
          congr 1
          rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have h2 : 0 ≤ (Real.sqrt (Fintype.card n) * X) ^ Fintype.card n := by positivity
  exact abs_le_of_sq_le_sq' h1 h2 |> fun h => abs_le.2 h

/-- Some `N` of the equations of a system in `N` unknowns whose homogeneous part has only the zero
solution form a square system with a nonsingular matrix (not in the paper: the proof of
`thm:bitlength` uses this without proof). The rows of the matrix span the whole space, so some `N`
of them form a basis. -/
theorem exists_square_subsystem {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℝ) (hA : ∀ w, A *ᵥ w = 0 → w = 0) :
    ∃ σ : κ → ι, Function.Injective σ ∧ (A.submatrix σ id).det ≠ 0 := by
  classical
  have hker : LinearMap.ker A.mulVecLin = ⊥ := LinearMap.ker_eq_bot'.2 fun w hw => hA w hw
  have hrank : A.rank = Fintype.card κ := by
    have := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    rw [hker, finrank_bot, add_zero, Module.finrank_fintype_fun_eq_card] at this
    exact this
  have hspan : Submodule.span ℝ (Set.range A.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← rank_eq_finrank_span_row, hrank, Module.finrank_fintype_fun_eq_card]
  obtain ⟨κ', a, ha, hsp, hli⟩ := exists_linearIndependent' ℝ A.row
  have : Finite κ' := Finite.of_injective a ha
  let _ : Fintype κ' := Fintype.ofFinite κ'
  have hcard : Fintype.card κ' = Fintype.card κ := by
    have h1 := linearIndependent_iff_card_eq_finrank_span.1 hli
    rw [Set.finrank, hsp, hspan, finrank_top, Module.finrank_fintype_fun_eq_card] at h1
    exact h1
  set e : κ ≃ κ' := Fintype.equivOfCardEq hcard.symm
  refine ⟨a ∘ e, ha.comp e.injective, ?_⟩
  have hrows : LinearIndependent ℝ (A.submatrix (a ∘ e) id).row := by
    have : (A.submatrix (a ∘ e) id).row = (A.row ∘ a) ∘ e := rfl
    rw [this]
    exact hli.comp e e.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (linearIndependent_rows_iff_isUnit.1 hrows)).ne_zero

/-- Cramer's rule: if `G z = h` and `det G ≠ 0`, then `z_c = det G_c / det G`, where `G_c` arises
from `G` by replacing the column `c` with `h` (not in the paper: the proof of `thm:bitlength`
cites Cramer's rule in (2) and (4); this is Mathlib's Cramer's rule, `Matrix.mulVec_cramer` and
`Matrix.cramer_apply`, restated in coordinates). -/
theorem cramer_coord {n : Type*} [Fintype n] [DecidableEq n] {G : Matrix n n ℝ} {h z : n → ℝ}
    (hdet : G.det ≠ 0) (hz : G *ᵥ z = h) (c : n) : z c = (G.updateCol c h).det / G.det := by
  have hcr : G.det • z = G.cramer h := by
    have h1 : G *ᵥ (G.cramer h) = G *ᵥ (G.det • z) := by
      rw [Matrix.mulVec_cramer, Matrix.mulVec_smul, hz]
    by_contra hne
    exact hdet ((Matrix.exists_mulVec_eq_zero_iff (M := G)).1
      ⟨G.det • z - G.cramer h, sub_ne_zero.2 hne, by rw [Matrix.mulVec_sub, ← h1, sub_self]⟩)
  have := congrFun hcr c
  rw [Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply] at this
  rw [← this]
  field_simp

/-- Scaling the rows of a square system by nonzero factors `s_i` multiplies its determinant and
the determinants of the systems with a column replaced by the right-hand side by the same factor
`∏ s_i` (the step "multiplies `det G` and `det G_α` by the same nonzero factor" of (3)). -/
theorem det_diagonal_mul {n : Type*} [Fintype n] [DecidableEq n] (s : n → ℝ) (G : Matrix n n ℝ)
    (h : n → ℝ) (c : n) :
    (Matrix.diagonal s * G).det = (∏ i, s i) * G.det ∧
      ((Matrix.diagonal s * G).updateCol c (fun i => s i * h i)).det =
        (∏ i, s i) * (G.updateCol c h).det := by
  refine ⟨by rw [Matrix.det_mul, Matrix.det_diagonal], ?_⟩
  have : (Matrix.diagonal s * G).updateCol c (fun i => s i * h i) =
      Matrix.diagonal s * G.updateCol c h := by
    ext i j
    by_cases hj : j = c
    · subst hj
      simp [Matrix.diagonal_mul]
    · simp [Matrix.diagonal_mul, Matrix.updateCol_ne hj]
  rw [this, Matrix.det_mul, Matrix.det_diagonal]

end LinearAlgebra

/-! ### (1) The linear equations of a state -/

section Events

variable {E : Type*} [Fintype E] [DecidableEq E] {f : Finset E → ℝ} {m β : E → ℝ}

/-- (1), (a), "On each of them, the state changes at most `C(n, 2)` times, by the argument of
`lem:eventcount`" (not in the paper: the STOC version refers to the argument of the steps (2) to
(4) of the proof of `lem:eventcount`, which it gives for a piece, `Stoc.Tracing.events_in_piece`,
and leaves it to the reader for the intervals of `lem:pwaffine`; here it is repeated for them). On
a set `J ⊆ [0, ∞)` on which `x*` is affine, `x*_e(α) = p_e + w_e α` (one of the intervals of
`lem:pwaffine`): (2) every `x*_e` and every `ρ_e` is nonnegative and affine, so each vanishes either
identically or nowhere in the interior of `J` (`Stoc.Tracing.zero_or_ne_of_nonneg`); (3) hence the
free elements and the zero set are constant there; (4) the blocks change only at an isolated zero
of some `ρ_e − ρ_g`, the root of a nonconstant one (`Stoc.Tracing.affine_zero_iff`), one for each
pair `{e, g}`: a set `K` of at most `C(n, 2)` shares contains every event point in the interior of
`J`. -/
theorem events_in_affine (H : Tracing.Hyp f m β) {J : Set ℝ} (hJ : J ⊆ Set.Ici 0) {p w : E → ℝ}
    (haff : ∀ α ∈ J, bestResponse f m β α = fun e => p e + α * w e) :
    ∃ K : Finset ℝ, K.card ≤ (Fintype.card E).choose 2 ∧
      ∀ α ∈ interior J, Tracing.IsEvent f m β α → α ∈ K := by
  classical
  -- On `J`, `x*_e(α) = p_e + w_e α` and `ρ_e(α) = α m_e − β_e x*_e(α) = cρ_e + dρ_e α`.
  set cρ : E → ℝ := fun e => -(β e * p e)
  set dρ : E → ℝ := fun e => m e - β e * w e
  have hrho : ∀ α ∈ J, ∀ e, rho f m β α e = cρ e + dρ e * α := by
    intro α hα e
    simp only [rho, marg, haff α hα, cρ, dρ]
    ring
  have hx : ∀ α ∈ J, ∀ e, bestResponse f m β α e = p e + w e * α := by
    intro α hα e
    rw [haff α hα]
    ring
  -- The argument of step (2) of the proof of `lem:eventcount` on `J`: "every `x*_e` and every
  -- `ρ_e` is nonnegative and affine, so each vanishes either identically or nowhere in its
  -- interior": `x*(α) ∈ P₊(f)`, and `ρ(α) ≥ 0` (`prop:optchar`).
  have h2x : ∀ e, (∀ α ∈ interior J, p e + w e * α = 0) ∨
      ∀ α ∈ interior J, p e + w e * α ≠ 0 := fun e =>
    Tracing.zero_or_ne_of_nonneg fun α hα => by
      rw [← hx α hα e]
      exact (isBestResponse_bestResponse H.rank m β α).1.1 e
  have h2ρ : ∀ e, (∀ α ∈ interior J, cρ e + dρ e * α = 0) ∨
      ∀ α ∈ interior J, cρ e + dρ e * α ≠ 0 := fun e =>
    Tracing.zero_or_ne_of_nonneg fun α hα => by
      rw [← hrho α hα e]
      exact (isBestResponse_bestResponse H.rank m β α).marg_nonneg H.beta
        (fun g => mul_nonneg (hJ hα) (H.reward g)) e
  -- The argument of step (3): "Hence the free elements and the zero set are constant there"
  have h3 : ∀ {c d : ℝ}, ((∀ α ∈ interior J, c + d * α = 0) ∨
      ∀ α ∈ interior J, c + d * α ≠ 0) →
      ∀ α ∈ interior J, ∀ α' ∈ interior J, (c + d * α = 0 ↔ c + d * α' = 0) := by
    rintro c d (h | h) α hα α' hα'
    · exact ⟨fun _ => h α' hα', fun _ => h α hα⟩
    · exact ⟨fun h0 => absurd h0 (h α hα), fun h0 => absurd h0 (h α' hα')⟩
  have h3free : ∀ α ∈ interior J, ∀ α' ∈ interior J, ∀ e,
      rho f m β α e = 0 ↔ rho f m β α' e = 0 := fun α hα α' hα' e => by
    rw [hrho α (interior_subset hα), hrho α' (interior_subset hα')]
    exact h3 (h2ρ e) α hα α' hα'
  have h3zero : ∀ α ∈ interior J, ∀ α' ∈ interior J, ∀ e,
      bestResponse f m β α e = 0 ↔ bestResponse f m β α' e = 0 := fun α hα α' hα' e => by
    rw [hx α (interior_subset hα), hx α' (interior_subset hα')]
    exact h3 (h2x e) α hα α' hα'
  -- The argument of step (4): "and the blocks change only at an isolated zero of some
  -- `ρ_e − ρ_g`, at most `C(n, 2)` points": an isolated zero of the affine function `ρ_e − ρ_g` is
  -- the root of a nonconstant one, `dρ_e ≠ dρ_g` (`Tracing.affine_zero_iff`), one for each
  -- unordered pair `{e, g}` (the set `K`).
  set rpair : E → E → ℝ := fun e g => Tracing.root (cρ e - cρ g) (dρ e - dρ g)
  have hsymm : ∀ e g, rpair e g = rpair g e := by
    intro e g
    simp only [rpair, Tracing.root]
    rw [show cρ g - cρ e = -(cρ e - cρ g) by ring, show dρ g - dρ e = -(dρ e - dρ g) by ring,
      neg_div_neg_eq]
  set K := (((univ : Finset E).offDiag.filter fun q => dρ q.1 ≠ dρ q.2).image
    (Function.uncurry Sym2.mk)).image (Sym2.lift ⟨rpair, hsymm⟩)
  refine ⟨K, ?_, ?_⟩
  · -- "at most `C(n, 2)` points"
    refine card_image_le.trans ((Finset.card_le_card
      (Finset.image_subset_image (filter_subset _ _))).trans ?_)
    rw [Sym2.card_image_offDiag]
    simp
  · -- Away from `K`, the state is constant near `α`, so `α` is no event point.
    intro α hα hev
    by_contra hK
    -- A neighborhood of `α` in the interior of `J` that avoids `K`.
    obtain ⟨ε, hε, hball⟩ :=
      Metric.isOpen_iff.1 (Finset.finite_toSet K).isClosed.isOpen_compl α hK
    obtain ⟨ε₀, hε₀, hball₀⟩ := Metric.isOpen_iff.1 isOpen_interior α hα
    set δ := min ε ε₀
    have hδ : 0 < δ := lt_min hε hε₀
    have hI : ∀ γ ∈ Set.Ioo (α - δ) (α + δ), γ ∈ interior J ∧ γ ∉ K := by
      intro γ hγ
      have hd : dist γ α < δ := by
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [hγ.1, hγ.2]
      exact ⟨hball₀ (lt_of_lt_of_le hd (min_le_right _ _)),
        hball (lt_of_lt_of_le hd (min_le_left _ _))⟩
    have hconst : StateConstOn f m β (Set.Ioo (α - δ) (α + δ)) := by
      -- the free set and the zero set, by (3)
      refine ⟨fun α₁ h₁ α₂ h₂ e => h3free α₁ (hI α₁ h₁).1 α₂ (hI α₂ h₂).1 e,
        fun α₁ h₁ α₂ h₂ e => h3zero α₁ (hI α₁ h₁).1 α₂ (hI α₂ h₂).1 e,
        fun α₁ h₁ α₂ h₂ e g => ?_⟩
      -- the blocks: `ρ_e − ρ_g` is zero at all shares of the neighborhood or at none, as it is
      -- constant, or nonconstant with its only zero in `K`
      by_cases heg : e = g
      · subst heg
        simp
      have hJ₁ := interior_subset (hI α₁ h₁).1
      have hJ₂ := interior_subset (hI α₂ h₂).1
      rw [hrho α₁ hJ₁, hrho α₂ hJ₂, hrho α₁ hJ₁, hrho α₂ hJ₂]
      have key : cρ e - cρ g + (dρ e - dρ g) * α₁ = 0 ↔
          cρ e - cρ g + (dρ e - dρ g) * α₂ = 0 := by
        by_cases hd : dρ e - dρ g = 0
        · simp [hd]
        · have hroot : Tracing.root (cρ e - cρ g) (dρ e - dρ g) ∈ K := by
            refine Finset.mem_image.2 ⟨s(e, g), Finset.mem_image.2 ⟨(e, g), Finset.mem_filter.2
              ⟨Finset.mem_offDiag.2 ⟨Finset.mem_univ e, Finset.mem_univ g, heg⟩,
                sub_ne_zero.1 hd⟩, rfl⟩, rfl⟩
          exact Tracing.affine_zero_iff (fun h => (hI α₁ h₁).2 (h ▸ hroot))
            (fun h => (hI α₂ h₂).2 (h ▸ hroot))
      constructor <;> intro h
      · have := key.1 (by linarith)
        linarith
      · have := key.2 (by linarith)
        linarith
    exact hev.2 _ _ (by linarith) (by linarith) (stateConstOn_iff.1 hconst)

/-- A share of an interval `J` of reals that is not in its interior is its infimum or its supremum
(part of the proof of `events_finite`, plumbing). -/
lemma eq_sInf_or_eq_sSup {J : Set ℝ} (hJ : J.OrdConnected) {α : ℝ} (hα : α ∈ J)
    (hint : α ∉ interior J) : α = sInf J ∨ α = sSup J := by
  by_cases hlow : ∃ a ∈ J, a < α
  · by_cases hup : ∃ c ∈ J, α < c
    · obtain ⟨a, ha, haα⟩ := hlow
      obtain ⟨c, hc, hαc⟩ := hup
      exact absurd (mem_interior.2 ⟨Set.Ioo a c, fun γ hγ => hJ.out ha hc ⟨hγ.1.le, hγ.2.le⟩,
        isOpen_Ioo, ⟨haα, hαc⟩⟩) hint
    · push Not at hup
      exact Or.inr (IsGreatest.csSup_eq ⟨hα, hup⟩).symm
  · push Not at hlow
    exact Or.inl (IsLeast.csInf_eq ⟨hα, hlow⟩).symm

/-- **(1)**, (a) (`appB-bitlength.tex:15-19`): "By `lem:pwaffine`, `[0, ∞)` is the union of finitely
many intervals on each of which `x*`, and hence every `ρ_e`, is affine. On each of them, the state
changes at most `C(n, 2)` times, by the argument of `lem:eventcount`, so there are finitely many
event points." An event point lies in the interior of one of the intervals, where
`events_in_affine` applies, or is an end of one of them. -/
theorem events_finite (H : Tracing.Hyp f m β) : {α | Tracing.IsEvent f m β α}.Finite := by
  classical
  -- "By `lem:pwaffine`, `[0, ∞)` is the union of finitely many intervals on each of which `x*`
  -- … is affine."
  obtain ⟨𝓙, hcov, h𝓙⟩ := (pwaffine H).2.1
  -- "On each of them, the state changes at most `C(n, 2)` times, by the argument of
  -- `lem:eventcount`,"
  have hK : ∀ J ∈ 𝓙, ∃ K : Finset ℝ, K.card ≤ (Fintype.card E).choose 2 ∧
      ∀ α ∈ interior J, Tracing.IsEvent f m β α → α ∈ K := fun J hJ => by
    obtain ⟨-, p, w, hpw⟩ := h𝓙 J hJ
    have hJ0 : J ⊆ Set.Ici 0 := fun α hα => by
      rw [← hcov]
      exact Set.mem_iUnion₂.2 ⟨J, hJ, hα⟩
    exact events_in_affine H hJ0 hpw
  choose! K hKcard hKev using hK
  -- "so there are finitely many event points."
  refine ((𝓙.biUnion fun J => K J ∪ {sInf J, sSup J}).finite_toSet).subset fun α hα => ?_
  have hα0 : α ∈ ⋃ J ∈ 𝓙, J := by
    rw [hcov]
    exact Set.mem_Ici.2 hα.1.le
  obtain ⟨J, hJ, hαJ⟩ := Set.mem_iUnion₂.1 hα0
  refine Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨J, hJ, ?_⟩)
  by_cases hint : α ∈ interior J
  · exact Finset.mem_union_left _ (hKev J hJ α hint hα)
  · rcases eq_sInf_or_eq_sSup (h𝓙 J hJ).1 hαJ hint with h | h
    · exact Finset.mem_union_right _ (by simp [h])
    · exact Finset.mem_union_right _ (by simp [h])

end Events

/-! #### The equations of a state

The state at a share `α₁` (`Stoc.state` of `Stoc/OptimalShare/Velocity.lean`): the free elements
`Φ = {e | ρ_e(α₁) = 0}` (`freeSet f m β α₁`), the zero set `Z = {e | x*_e(α₁) = 0}`
(`zeroSet f m β α₁`) and the blocks `D_j = {e | ρ_e(α₁) = θ_j}` of the distinct positive marginals
`θ_0 > θ_1 > ⋯ > θ_{k−1}` (`theta` of `Stoc/BestResponse/LayerCake.lean`; the paper's blocks
`D_1, …, D_k`, indices from 0). -/

section System

variable {E : Type*} [Fintype E] [DecidableEq E]
variable (f : Finset E → ℝ) (m β : E → ℝ) (α₁ : ℝ)

/-- The number `k` of blocks of the state at `α₁`. -/
noncomputable abbrev nb : ℕ := numVals (rho f m β α₁) 0

/-- The values `θ_j = ρ_j(α₁)` of the blocks at `α₁`, decreasing in `j`. -/
noncomputable abbrev val (j : ℕ) : ℝ := theta (rho f m β α₁) 0 j

/-- The block `D_j = {e | ρ_e(α₁) = θ_j}`. -/
noncomputable def blockD (j : ℕ) : Finset E :=
  univ.filter fun e => rho f m β α₁ e = val f m β α₁ j

/-- `S_j = D_0 ∪ ⋯ ∪ D_j`, the union of the blocks up to `D_j` (the paper's
`S_j := D_1 ∪ ⋯ ∪ D_j`, `appB-bitlength.tex:25`, with the blocks indexed from 0; the paper's
`S_0 := ∅` is the union of no blocks, before `D_0`). -/
noncomputable def cumS (j : ℕ) : Finset E :=
  (range (j + 1)).biUnion (blockD f m β α₁)

/-- The elements `e ∈ D_j ∩ Z` of the blocks (`j = 0, …, k − 1`): `e ∉ Φ`, so that `e` lies in a
block, and `e ∈ Z`. -/
noncomputable def zb : Finset E :=
  univ.filter fun e => e ∉ freeSet f m β α₁ ∧ e ∈ zeroSet f m β α₁

/-- The unknowns `(α, x, ρ_0, …, ρ_{k−1})`. -/
abbrev Col := Unit ⊕ E ⊕ Fin (nb f m β α₁)

/-- The equations: one for each element `e`, a second one for each `e ∈ D_j ∩ Z`, and one for each
block. -/
abbrev Row := E ⊕ zb f m β α₁ ⊕ Fin (nb f m β α₁)

/-- The vector of unknowns with `α = a`, `x` and `ρ = r`. -/
def vec (a : ℝ) (x : E → ℝ) (r : Fin (nb f m β α₁) → ℝ) : Col f m β α₁ → ℝ :=
  Sum.elim (fun _ => a) (Sum.elim x r)

/-- The equation of the element `e`: `β_e x_e − m_e α = 0` for `e ∈ Φ`, `x_e = 0` for
`e ∈ D_j ∩ Z`, and `β_e x_e + ρ_j − m_e α = 0` for `e ∈ D_j ∖ Z`. -/
noncomputable def rowE (e : E) : Col f m β α₁ → ℝ :=
  if e ∈ freeSet f m β α₁ then
    vec f m β α₁ (-m e) (fun e' => if e' = e then β e else 0) 0
  else if e ∈ zeroSet f m β α₁ then
    vec f m β α₁ 0 (fun e' => if e' = e then 1 else 0) 0
  else
    vec f m β α₁ (-m e) (fun e' => if e' = e then β e else 0)
      fun j => if val f m β α₁ j = rho f m β α₁ e then 1 else 0

/-- The second equation `ρ_j − m_e α = 0` of an element `e ∈ D_j ∩ Z`. -/
noncomputable def rowZ (e : zb f m β α₁) : Col f m β α₁ → ℝ :=
  vec f m β α₁ (-m e) 0 fun j => if val f m β α₁ j = rho f m β α₁ e then 1 else 0

/-- The equation `x(S_j) = f(S_j)` of the block `D_j`. -/
noncomputable def rowS (j : Fin (nb f m β α₁)) : Col f m β α₁ → ℝ :=
  vec f m β α₁ 0 (fun e => if e ∈ cumS f m β α₁ j then 1 else 0) 0

/-- The matrix of the equations of the state at `α₁`. -/
noncomputable def eqG : Matrix (Row f m β α₁) (Col f m β α₁) ℝ :=
  Matrix.of (Sum.elim (rowE f m β α₁) (Sum.elim (rowZ f m β α₁) (rowS f m β α₁)))

/-- The right-hand sides of the equations: `0`, `0` and `f(S_j)`. -/
noncomputable def eqH : Row f m β α₁ → ℝ :=
  Sum.elim 0 (Sum.elim 0 fun j => f (cumS f m β α₁ j))

/-- A representative `rep j ∈ D_j` of the block `D_j`. -/
noncomputable def rep (j : Fin (nb f m β α₁)) : E :=
  (mem_image.1 (mem_filter.1 (theta_mem j.2)).1).choose

/-- The vector `(α, x*(α), ρ_0(α), …, ρ_{k−1}(α))` of a share `α`, where `ρ_j(α)` is the marginal
`ρ_e(α)` of the elements `e ∈ D_j`, here of the representative. -/
noncomputable def solJ (α : ℝ) : Col f m β α₁ → ℝ :=
  vec f m β α₁ α (bestResponse f m β α) fun j => rho f m β α (rep f m β α₁ j)

/-- The affine extension `x^J(α) = x*(α₁) + (α − α₁) v` of `x*` from an interval with constant
state around `α₁` (`lem:velocity`). -/
noncomputable def xJ (α : ℝ) (e : E) : ℝ :=
  bestResponse f m β α₁ e + (α - α₁) * velocity f m β α₁ e

/-- The line `(α, x^J(α), ρ^J(α))` of the state at `α₁`, with the affine extensions
`ρ^J_j(α) = α m_e − β_e x^J_e(α)` (`e = rep j`) of the marginals of the blocks. -/
noncomputable def lineJ (α : ℝ) : Col f m β α₁ → ℝ :=
  vec f m β α₁ α (xJ f m β α₁ α) fun j =>
    α * m (rep f m β α₁ j) - β (rep f m β α₁ j) * xJ f m β α₁ α (rep f m β α₁ j)

variable {f m β α₁}

omit [DecidableEq E] in
/-- `e ∈ Φ` means `ρ_e = 0` (plumbing). -/
lemma mem_freeSet {α : ℝ} {e : E} : e ∈ freeSet f m β α ↔ rho f m β α e = 0 := by
  simp [freeSet]

omit [DecidableEq E] in
/-- `e ∈ Z` means `x*_e = 0` (plumbing). -/
lemma mem_zeroSet {α : ℝ} {e : E} : e ∈ zeroSet f m β α ↔ bestResponse f m β α e = 0 := by
  simp [zeroSet]

omit [DecidableEq E] in
lemma rho_rep (j : Fin (nb f m β α₁)) : rho f m β α₁ (rep f m β α₁ j) = val f m β α₁ j :=
  (mem_image.1 (mem_filter.1 (theta_mem j.2)).1).choose_spec.2

omit [DecidableEq E] in
lemma val_pos (j : Fin (nb f m β α₁)) : 0 < val f m β α₁ j := c_lt_theta j.2

omit [DecidableEq E] in
lemma val_inj {i j : Fin (nb f m β α₁)} (h : val f m β α₁ i = val f m β α₁ j) : i = j := by
  rcases lt_trichotomy (i : ℕ) j with hij | hij | hij
  · exact absurd h (theta_lt_theta hij j.2.le).ne'
  · exact Fin.ext hij
  · exact absurd h (theta_lt_theta hij i.2.le).ne

omit [DecidableEq E] in
/-- Every positive marginal at `α₁` is the value of a block. -/
lemma exists_val_eq {e : E} (he : 0 < rho f m β α₁ e) :
    ∃ j : Fin (nb f m β α₁), val f m β α₁ j = rho f m β α₁ e := by
  obtain ⟨j, hj, hje⟩ := exists_theta_eq he
  exact ⟨⟨j, hj⟩, hje⟩

omit [DecidableEq E] in
lemma dotProduct_vec (a : ℝ) (x : E → ℝ) (r : Fin (nb f m β α₁) → ℝ)
    (z : Col f m β α₁ → ℝ) :
    vec f m β α₁ a x r ⬝ᵥ z = a * z (Sum.inl ()) + ∑ e, x e * z (Sum.inr (Sum.inl e)) +
      ∑ j, r j * z (Sum.inr (Sum.inr j)) := by
  simp only [dotProduct, Fintype.sum_sum_type, vec, Sum.elim_inl, Sum.elim_inr,
    Finset.univ_unique, Finset.sum_singleton]
  ring

omit [DecidableEq E] in
/-- `∑_j [θ_j = ρ_e(α₁)] ρ_j = ρ_{j₀}` for the block `D_{j₀}` of `e`. -/
lemma sum_ind_val {e : E} {j₀ : Fin (nb f m β α₁)} (hj₀ : val f m β α₁ j₀ = rho f m β α₁ e)
    (r : Fin (nb f m β α₁) → ℝ) :
    ∑ j : Fin (nb f m β α₁), (if val f m β α₁ j = rho f m β α₁ e then (1 : ℝ) else 0) * r j =
      r j₀ := by
  rw [Finset.sum_eq_single j₀]
  · rw [ite_eq_left hj₀, one_mul]
  · intro j _ hj
    rw [ite_eq_right fun h => hj (val_inj (h.trans hj₀.symm)), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j₀) h

lemma sum_ind_eq (e : E) (c : ℝ) (y : E → ℝ) :
    ∑ e', (if e' = e then c else 0) * y e' = c * y e := by
  rw [Finset.sum_eq_single e]
  · rw [ite_eq_left rfl]
  · intro e' _ he'
    rw [ite_eq_right he', zero_mul]
  · intro h
    exact absurd (Finset.mem_univ e) h

/-- The equation of a free element `e ∈ Φ`: `β_e x_e − m_e α`. -/
lemma mulVec_free (z : Col f m β α₁ → ℝ) {e : E} (he : e ∈ freeSet f m β α₁) :
    (eqG f m β α₁ *ᵥ z) (Sum.inl e) =
      β e * z (Sum.inr (Sum.inl e)) - m e * z (Sum.inl ()) := by
  show rowE f m β α₁ e ⬝ᵥ z = _
  rw [rowE, ite_eq_left he, dotProduct_vec, sum_ind_eq]
  simp
  ring

/-- The first equation of an element `e ∈ D_j ∩ Z`: `x_e`. -/
lemma mulVec_zero (z : Col f m β α₁ → ℝ) {e : E} (he : e ∉ freeSet f m β α₁)
    (hz : e ∈ zeroSet f m β α₁) :
    (eqG f m β α₁ *ᵥ z) (Sum.inl e) = z (Sum.inr (Sum.inl e)) := by
  show rowE f m β α₁ e ⬝ᵥ z = _
  rw [rowE, ite_eq_right he, ite_eq_left hz, dotProduct_vec, sum_ind_eq]
  simp

/-- The equation of an element `e ∈ D_j ∖ Z`: `β_e x_e + ρ_j − m_e α`. -/
lemma mulVec_block (z : Col f m β α₁ → ℝ) {e : E} (he : e ∉ freeSet f m β α₁)
    (hz : e ∉ zeroSet f m β α₁) {j : Fin (nb f m β α₁)}
    (hj : val f m β α₁ j = rho f m β α₁ e) :
    (eqG f m β α₁ *ᵥ z) (Sum.inl e) =
      β e * z (Sum.inr (Sum.inl e)) + z (Sum.inr (Sum.inr j)) - m e * z (Sum.inl ()) := by
  show rowE f m β α₁ e ⬝ᵥ z = _
  rw [rowE, ite_eq_right he, ite_eq_right hz, dotProduct_vec, sum_ind_eq, sum_ind_val hj]
  ring

/-- The second equation of an element `e ∈ D_j ∩ Z`: `ρ_j − m_e α`. -/
lemma mulVec_zb (z : Col f m β α₁ → ℝ) (e : zb f m β α₁) {j : Fin (nb f m β α₁)}
    (hj : val f m β α₁ j = rho f m β α₁ e) :
    (eqG f m β α₁ *ᵥ z) (Sum.inr (Sum.inl e)) = z (Sum.inr (Sum.inr j)) - m e * z (Sum.inl ()) := by
  show rowZ f m β α₁ e ⬝ᵥ z = _
  rw [rowZ, dotProduct_vec, sum_ind_val hj]
  simp
  ring

/-- The equation of the block `D_j`: `x(S_j)`. -/
lemma mulVec_cum (z : Col f m β α₁ → ℝ) (j : Fin (nb f m β α₁)) :
    (eqG f m β α₁ *ᵥ z) (Sum.inr (Sum.inr j)) = ∑ e ∈ cumS f m β α₁ j, z (Sum.inr (Sum.inl e)) := by
  show rowS f m β α₁ j ⬝ᵥ z = _
  rw [rowS, dotProduct_vec]
  simp [Finset.sum_ite_mem]

end System

/-! #### (1), (b) to (d): the solutions of the equations -/

section Solutions

variable {E : Type*} [Fintype E] [DecidableEq E] {f : Finset E → ℝ} {m β : E → ℝ} {α₁ : ℝ}

/-- The marginals are nonnegative at nonnegative shares (`prop:optchar`). -/
lemma rho_nonneg (H : Tracing.Hyp f m β) {α : ℝ} (hα : 0 ≤ α) (e : E) : 0 ≤ rho f m β α e :=
  (isBestResponse_bestResponse H.rank m β α).marg_nonneg H.beta
    (fun g => mul_nonneg hα (H.reward g)) e

/-- `S_0 = D_0`: the first union is the first block (the paper's `S_1 = S_0 ∪ D_1 = D_1` with
`S_0 := ∅`; here the blocks are indexed from 0). -/
lemma cumS_zero : cumS f m β α₁ 0 = blockD f m β α₁ 0 := by
  simp [cumS]

/-- `S_j = S_{j−1} ∪ D_j` (here for `j + 1 ≥ 1`). -/
lemma cumS_succ (j : ℕ) :
    cumS f m β α₁ (j + 1) = cumS f m β α₁ j ∪ blockD f m β α₁ (j + 1) := by
  rw [cumS, range_add_one, biUnion_insert, union_comm]
  rfl

/-- `S_{j−1}` and `D_j` are disjoint, as blocks of different values are (here for `j + 1 < k`). -/
lemma disjoint_cumS_blockD {j : ℕ} (hj : j + 1 < nb f m β α₁) :
    Disjoint (cumS f m β α₁ j) (blockD f m β α₁ (j + 1)) := by
  rw [cumS, disjoint_biUnion_left]
  intro i hi
  rw [Finset.disjoint_left]
  intro e h1 h2
  simp only [blockD, mem_filter, mem_univ, true_and] at h1 h2
  exact (theta_lt_theta (show i < j + 1 from mem_range.1 hi) hj.le).ne' (h1.symm.trans h2)

/-- `e ∈ S_j` if and only if `θ_j ≤ ρ_e(α₁)`, as the blocks are numbered by their values, the
distinct positive marginals `θ_0 > θ_1 > ⋯` at `α₁` (part of the step "`S_j` is the level set
`A_{ρ_j(α)}(α)`" of (1), `solJ_solves`). -/
lemma mem_cumS_iff {j : ℕ} (hj : j < nb f m β α₁) (e : E) :
    e ∈ cumS f m β α₁ j ↔ val f m β α₁ j ≤ rho f m β α₁ e := by
  simp only [cumS, mem_biUnion, mem_range, blockD, mem_filter, mem_univ, true_and]
  constructor
  · -- `ρ_e(α₁) = θ_i` for some `i ≤ j`, and `θ_i ≥ θ_j`
    rintro ⟨i, hi, he⟩
    rw [he]
    exact (theta_le_theta_iff hj (show i < nb f m β α₁ by omega)).2 (by omega)
  · -- `ρ_e(α₁) ≥ θ_j > 0` is a value `θ_i`, and `θ_i ≥ θ_j` means `i ≤ j`
    intro h
    obtain ⟨i, hi, hie⟩ := exists_theta_eq ((c_lt_theta hj).trans_le h)
    refine ⟨i, ?_, hie.symm⟩
    rw [← hie] at h
    have := (theta_le_theta_iff hj hi).1 h
    omega

/-- **(1)**, (b) (`appB-bitlength.tex:19-38`): on an open interval `J = (lo, hi) ∋ α₁` with
`lo ≥ 0` on which the state is constant, the vector `(α, x*(α), ρ_1(α), …, ρ_k(α))` solves the
equations for every `α ∈ J`. -/
theorem solJ_solves (H : Tracing.Hyp f m β) {lo hi : ℝ} (hlo : 0 ≤ lo)
    (hS : ∀ α ∈ Set.Ioo lo hi, ∀ α' ∈ Set.Ioo lo hi, state f m β α = state f m β α')
    (hα₁ : α₁ ∈ Set.Ioo lo hi) {α : ℝ} (hα : α ∈ Set.Ioo lo hi) :
    eqG f m β α₁ *ᵥ solJ f m β α₁ α = eqH f m β α₁ := by
  have hS' : StateConstOn f m β (Set.Ioo lo hi) := stateConstOn_iff.2 hS
  have hα0 : 0 ≤ α := hlo.trans hα.1.le
  -- "The values `ρ_e(α)` of different blocks differ for every `α ∈ J` and depend continuously on
  -- `α`, so the blocks are in the same order on all of `J`, and we number them such that their
  -- values satisfy `ρ_1(α) > ⋯ > ρ_k(α) > 0`."
  have hord : ∀ e e', rho f m β α₁ e ≤ rho f m β α₁ e' ↔ rho f m β α e ≤ rho f m β α e' :=
    fun e e' => hS'.rho_le_iff H.rank H.beta hα₁ hα e e'
  have hpos : ∀ j : Fin (nb f m β α₁), 0 < rho f m β α (rep f m β α₁ j) := fun j => by
    have h1 : rho f m β α₁ (rep f m β α₁ j) ≠ 0 := by rw [rho_rep]; exact (val_pos j).ne'
    exact lt_of_le_of_ne (rho_nonneg H hα0 _)
      (Ne.symm fun h => h1 ((hS'.free α₁ hα₁ α hα _).2 h))
  -- "Then `S_j := D_1 ∪ ⋯ ∪ D_j` is the level set `A_{ρ_j(α)}(α)`, so it is tight with respect to
  -- `x*(α)`." An element lies in `S_j` if and only if `θ_j ≤ ρ_e(α₁)` (the blocks are numbered by
  -- their values, `mem_cumS_iff`), that is, `ρ_j(α) ≤ ρ_e(α)` (the order on `J`, `hord`).
  have hlev : ∀ j : Fin (nb f m β α₁), cumS f m β α₁ j =
      levelSet m β α (bestResponse f m β α) (rho f m β α (rep f m β α₁ j)) := fun j => by
    ext e
    rw [mem_cumS_iff j.2]
    simp only [levelSet, mem_filter, mem_univ, true_and]
    rw [← rho_rep j]
    exact hord _ e
  have htight : ∀ j : Fin (nb f m β α₁), ∑ e ∈ cumS f m β α₁ j, bestResponse f m β α e =
      f (cumS f m β α₁ j) := fun j => by
    have h := ((isBestResponse_iff_levelSets H.rank H.beta
      (fun e => mul_nonneg hα0 (H.reward e))).1
      (isBestResponse_bestResponse H.rank m β α)).2.2 _ (hpos j)
    rw [← hlev j] at h
    exact h
  -- "Hence, for every `α ∈ J`, the vector `(α, x*(α), ρ_1(α), …, ρ_k(α))` solves the linear
  -- equations."
  have hx : ∀ e, β e * bestResponse f m β α e = α * m e - rho f m β α e := fun e => by
    simp only [rho, marg]
    ring
  funext r
  rcases r with e | e | j
  · by_cases hfree : e ∈ freeSet f m β α₁
    · -- `β_e x_e − m_e α = 0` for `e ∈ Φ`
      rw [mulVec_free _ hfree]
      have := (hS'.free α₁ hα₁ α hα e).1 (mem_freeSet.1 hfree)
      simp only [solJ, vec, Sum.elim_inl, Sum.elim_inr, eqH, Pi.zero_apply]
      rw [hx, this]
      ring
    · by_cases hzero : e ∈ zeroSet f m β α₁
      · -- `x_e = 0` for `e ∈ D_j ∩ Z`
        rw [mulVec_zero _ hfree hzero]
        simp only [solJ, vec, Sum.elim_inl, Sum.elim_inr, eqH, Pi.zero_apply]
        exact (hS'.zero α₁ hα₁ α hα e).1 (mem_zeroSet.1 hzero)
      · -- `β_e x_e + ρ_j − m_e α = 0` for `e ∈ D_j ∖ Z`
        obtain ⟨j, hj⟩ := exists_val_eq (lt_of_le_of_ne
          (rho_nonneg H (hlo.trans hα₁.1.le) e) (Ne.symm (mem_freeSet.not.1 hfree)))
        rw [mulVec_block _ hfree hzero hj]
        have hblk : rho f m β α (rep f m β α₁ j) = rho f m β α e :=
          (hS'.block α₁ hα₁ α hα _ e).1 (by rw [rho_rep, hj])
        simp only [solJ, vec, Sum.elim_inl, Sum.elim_inr, eqH, Pi.zero_apply]
        rw [hx, hblk]
        ring
  · -- `ρ_j − m_e α = 0` for `e ∈ D_j ∩ Z`
    obtain ⟨he, hzero⟩ := (mem_filter.1 e.2).2
    obtain ⟨j, hj⟩ := exists_val_eq (lt_of_le_of_ne
      (rho_nonneg H (hlo.trans hα₁.1.le) e) (Ne.symm (mem_freeSet.not.1 he)))
    rw [mulVec_zb _ e hj]
    have hblk : rho f m β α (rep f m β α₁ j) = rho f m β α e :=
      (hS'.block α₁ hα₁ α hα _ e).1 (by rw [rho_rep, hj])
    have hz0 : bestResponse f m β α e = 0 :=
      (hS'.zero α₁ hα₁ α hα e).1 (mem_zeroSet.1 hzero)
    simp only [solJ, vec, Sum.elim_inl, Sum.elim_inr, eqH, Pi.zero_apply]
    rw [hblk]
    simp only [rho, marg, hz0]
    ring
  · -- `x(S_j) = f(S_j)`
    rw [mulVec_cum]
    simp only [solJ, vec, Sum.elim_inl, Sum.elim_inr, eqH]
    exact htight j

/-- **(1)**, (c) (`appB-bitlength.tex:39-44`): "For fixed `α`, these equations determine `x` and
`ρ_1, …, ρ_k`." Two solutions with the same `α` are equal. -/
theorem determined (H : Tracing.Hyp f m β) (hρ : ∀ e, 0 ≤ rho f m β α₁ e)
    {z z' : Col f m β α₁ → ℝ} (hz : eqG f m β α₁ *ᵥ z = eqH f m β α₁)
    (hz' : eqG f m β α₁ *ᵥ z' = eqH f m β α₁) (hα : z (Sum.inl ()) = z' (Sum.inl ())) :
    z = z' := by
  have hβ := H.beta
  -- "Indeed, the first line fixes `x_e` for `e ∈ Φ`."
  have hΦ : ∀ e ∈ freeSet f m β α₁, z (Sum.inr (Sum.inl e)) = z' (Sum.inr (Sum.inl e)) := by
    intro e he
    have h1 := congrFun hz (Sum.inl e)
    have h2 := congrFun hz' (Sum.inl e)
    rw [mulVec_free _ he] at h1 h2
    simp only [eqH, Sum.elim_inl, Pi.zero_apply] at h1 h2
    rw [hα] at h1
    exact mul_left_cancel₀ (hβ e).ne' (by linarith)
  -- the equation `β_e x_e + ρ_j − m_e α = 0` of `e ∈ D_j ∖ Z`, solved for `x_e`
  have hblock : ∀ y : Col f m β α₁ → ℝ, eqG f m β α₁ *ᵥ y = eqH f m β α₁ → ∀ e,
      e ∉ freeSet f m β α₁ → e ∉ zeroSet f m β α₁ → ∀ j : Fin (nb f m β α₁),
      val f m β α₁ j = rho f m β α₁ e →
        y (Sum.inr (Sum.inl e)) = (m e * y (Sum.inl ()) - y (Sum.inr (Sum.inr j))) / β e := by
    intro y hy e he hz j hj
    have h1 := congrFun hy (Sum.inl e)
    rw [mulVec_block _ he hz hj] at h1
    simp only [eqH, Sum.elim_inl, Pi.zero_apply] at h1
    field_simp [(hβ e).ne']
    linarith
  -- "If `D_j ∩ Z ≠ ∅`, the third line fixes `ρ_j`. Otherwise, subtracting the equations for
  -- `S_{j−1}` and `S_j`, with `S_0 := ∅`, gives
  -- `∑_{e∈D_j} (m_e α − ρ_j)/β_e = f(S_j) − f(S_{j−1})`, which fixes `ρ_j`."
  have hρj : ∀ j : Fin (nb f m β α₁), z (Sum.inr (Sum.inr j)) = z' (Sum.inr (Sum.inr j)) := by
    intro j
    by_cases hZ : (blockD f m β α₁ j ∩ zeroSet f m β α₁).Nonempty
    · obtain ⟨e, heDZ⟩ := hZ
      obtain ⟨heD, hze⟩ := mem_inter.1 heDZ
      have hje : val f m β α₁ j = rho f m β α₁ e := ((mem_filter.1 heD).2).symm
      have he : e ∉ freeSet f m β α₁ :=
        mem_freeSet.not.2 (by rw [← hje]; exact (val_pos j).ne')
      have hezb : e ∈ zb f m β α₁ := mem_filter.2 ⟨mem_univ e, he, hze⟩
      have h1 := congrFun hz (Sum.inr (Sum.inl ⟨e, hezb⟩))
      have h2 := congrFun hz' (Sum.inr (Sum.inl ⟨e, hezb⟩))
      rw [mulVec_zb _ _ hje] at h1 h2
      simp only [eqH, Sum.elim_inr, Sum.elim_inl, Pi.zero_apply] at h1 h2
      rw [hα] at h1
      linarith
    · -- otherwise `D_j ∩ Z = ∅`
      have hZ' : ∀ e ∈ blockD f m β α₁ j, e ∉ zeroSet f m β α₁ := fun e he hz =>
        hZ ⟨e, mem_inter.2 ⟨he, hz⟩⟩
      -- `S_{j−1}`, with `S_0 := ∅` (with the blocks indexed from 0: `∅` for the first block `D_0`)
      set Sprev : Finset E := if (j : ℕ) = 0 then ∅ else cumS f m β α₁ ((j : ℕ) - 1) with hSprev
      -- `S_j` is the disjoint union of `S_{j−1}` and `D_j`
      have hSj : cumS f m β α₁ j = Sprev ∪ blockD f m β α₁ j ∧
          Disjoint Sprev (blockD f m β α₁ j) := by
        by_cases hj0 : (j : ℕ) = 0
        · rw [hSprev, ite_eq_left hj0, hj0, cumS_zero, empty_union]
          exact ⟨rfl, disjoint_empty_left _⟩
        · obtain ⟨i, hi⟩ := Nat.exists_eq_add_one_of_ne_zero hj0
          rw [hSprev, ite_eq_right hj0, hi, Nat.add_sub_cancel]
          exact ⟨cumS_succ i, disjoint_cumS_blockD (by have := j.2; omega)⟩
      -- the equation `x(S_{j−1}) = f(S_{j−1})` of a solution (for `S_0 = ∅`, as `f(∅) = 0`)
      have hprev : ∀ y : Col f m β α₁ → ℝ, eqG f m β α₁ *ᵥ y = eqH f m β α₁ →
          ∑ e ∈ Sprev, y (Sum.inr (Sum.inl e)) = f Sprev := by
        intro y hy
        by_cases hj0 : (j : ℕ) = 0
        · rw [hSprev, ite_eq_left hj0, sum_empty, H.rank.empty]
        · have h := congrFun hy (Sum.inr (Sum.inr ⟨(j : ℕ) - 1, by omega⟩))
          rw [mulVec_cum] at h
          rw [hSprev, ite_eq_right hj0]
          exact h
      -- subtracting the equations for `S_{j−1}` and `S_j`
      have hsub : ∀ y : Col f m β α₁ → ℝ, eqG f m β α₁ *ᵥ y = eqH f m β α₁ →
          ∑ e ∈ blockD f m β α₁ j, (m e * y (Sum.inl ()) - y (Sum.inr (Sum.inr j))) / β e =
            f (cumS f m β α₁ j) - f Sprev := by
        intro y hy
        have hS := congrFun hy (Sum.inr (Sum.inr j))
        rw [mulVec_cum] at hS
        simp only [eqH, Sum.elim_inr] at hS
        rw [hSj.1, Finset.sum_union hSj.2] at hS
        rw [← Finset.sum_congr rfl fun e he => hblock y hy e
          (mem_freeSet.not.2 (by rw [(mem_filter.1 he).2]; exact (val_pos j).ne')) (hZ' e he) j
          ((mem_filter.1 he).2).symm, hSj.1]
        linarith [hprev y hy]
      have h1 := hsub z hz
      have h2 := hsub z' hz'
      have hD : 0 < ∑ e ∈ blockD f m β α₁ j, 1 / β e :=
        Finset.sum_pos (fun e _ => one_div_pos.2 (hβ e))
          ⟨rep f m β α₁ j, mem_filter.2 ⟨mem_univ _, rho_rep j⟩⟩
      have e1 : ∀ y : Col f m β α₁ → ℝ,
          ∑ e ∈ blockD f m β α₁ j, (m e * y (Sum.inl ()) - y (Sum.inr (Sum.inr j))) / β e =
            ∑ e ∈ blockD f m β α₁ j, m e * y (Sum.inl ()) / β e -
              y (Sum.inr (Sum.inr j)) * ∑ e ∈ blockD f m β α₁ j, 1 / β e := fun y => by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun e _ => by ring
      rw [e1] at h1 h2
      rw [hα] at h1
      have := mul_right_cancel₀ hD.ne' (show z (Sum.inr (Sum.inr j)) *
        ∑ e ∈ blockD f m β α₁ j, 1 / β e =
          z' (Sum.inr (Sum.inr j)) * ∑ e ∈ blockD f m β α₁ j, 1 / β e by linarith)
      exact this
  -- "Then every `x_e` is fixed."
  have hx : ∀ e, z (Sum.inr (Sum.inl e)) = z' (Sum.inr (Sum.inl e)) := by
    intro e
    by_cases hfree : e ∈ freeSet f m β α₁
    · exact hΦ e hfree
    · by_cases hzero : e ∈ zeroSet f m β α₁
      · have h1 := congrFun hz (Sum.inl e)
        have h2 := congrFun hz' (Sum.inl e)
        rw [mulVec_zero _ hfree hzero] at h1 h2
        simp only [eqH, Sum.elim_inl, Pi.zero_apply] at h1 h2
        rw [h1, h2]
      · obtain ⟨j, hj⟩ := exists_val_eq (lt_of_le_of_ne (hρ e)
          (Ne.symm (mem_freeSet.not.1 hfree)))
        rw [hblock z hz e hfree hzero j hj, hblock z' hz' e hfree hzero j hj, hα, hρj j]
  funext c
  rcases c with ⟨⟩ | e | j
  · exact hα
  · exact hx e
  · exact hρj j

omit [DecidableEq E] in
/-- The line is affine in the share. -/
lemma lineJ_affine (α : ℝ) :
    lineJ f m β α₁ α = lineJ f m β α₁ 0 + α • (lineJ f m β α₁ 1 - lineJ f m β α₁ 0) := by
  funext c
  rcases c with ⟨⟩ | e | j <;>
    simp only [lineJ, vec, xJ, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul] <;> ring

omit [DecidableEq E] in
lemma lineJ_alpha (α : ℝ) : lineJ f m β α₁ α (Sum.inl ()) = α := rfl

/-- **(1)**, (d) (`appB-bitlength.tex:44-46`): "By `lem:velocity`, `x*` and `ρ_1, …, ρ_k` are
affine on `J`": the line `(α, x^J(α), ρ^J(α))` is the vector `(α, x*(α), ρ(α))` for `α ∈ J`. -/
theorem lineJ_eq_solJ (H : Tracing.Hyp f m β) {lo hi : ℝ} (hlo : 0 ≤ lo)
    (hS : ∀ α ∈ Set.Ioo lo hi, ∀ α' ∈ Set.Ioo lo hi, state f m β α = state f m β α')
    (hα₁ : α₁ ∈ Set.Ioo lo hi) {α : ℝ} (hα : α ∈ Set.Ioo lo hi) :
    lineJ f m β α₁ α = solJ f m β α₁ α := by
  have hvel := (velocity_lemma H hlo hS hα₁).1 α hα
  have hxJ : xJ f m β α₁ α = bestResponse f m β α := by
    rw [hvel]
    rfl
  funext c
  rcases c with ⟨⟩ | e | j
  · rfl
  · simp only [lineJ, solJ, vec, Sum.elim_inr, Sum.elim_inl, hxJ]
  · simp only [lineJ, solJ, vec, Sum.elim_inr, hxJ, rho, marg]

/-- **(1)**, (d), continued (`appB-bitlength.tex:47-51`): "The solutions of the equations form an
affine subspace that contains `(α, x^J(α), ρ^J(α))` for all `α ∈ J`, hence for all `α ∈ ℝ`, and
that contains at most one point for each `α`. So the solutions form exactly the line
`{(α, x^J(α), ρ^J(α)) | α ∈ ℝ}`." -/
theorem solves_iff_line (H : Tracing.Hyp f m β) {lo hi : ℝ} (hlo : 0 ≤ lo)
    (hS : ∀ α ∈ Set.Ioo lo hi, ∀ α' ∈ Set.Ioo lo hi, state f m β α = state f m β α')
    (hα₁ : α₁ ∈ Set.Ioo lo hi) (z : Col f m β α₁ → ℝ) :
    eqG f m β α₁ *ᵥ z = eqH f m β α₁ ↔ ∃ α, z = lineJ f m β α₁ α := by
  -- contains the line on `J`
  have hJ : ∀ α ∈ Set.Ioo lo hi, eqG f m β α₁ *ᵥ lineJ f m β α₁ α = eqH f m β α₁ :=
    fun α hα => by
      rw [lineJ_eq_solJ H hlo hS hα₁ hα]
      exact solJ_solves H hlo hS hα₁ hα
  -- hence on all of `ℝ`
  set α₂ := (α₁ + hi) / 2
  have hα₂ : α₂ ∈ Set.Ioo lo hi := ⟨by simp only [α₂]; linarith [hα₁.1, hα₁.2],
    by simp only [α₂]; linarith [hα₁.2]⟩
  have hne : α₁ ≠ α₂ := by simp only [α₂]; intro h; linarith [hα₁.2]
  set d := lineJ f m β α₁ 1 - lineJ f m β α₁ 0
  have hall : ∀ α, eqG f m β α₁ *ᵥ lineJ f m β α₁ α = eqH f m β α₁ := by
    have e1 := hJ α₁ hα₁
    have e2 := hJ α₂ hα₂
    rw [lineJ_affine, Matrix.mulVec_add, Matrix.mulVec_smul] at e1 e2
    have hd : eqG f m β α₁ *ᵥ d = 0 := by
      have : (α₁ - α₂) • (eqG f m β α₁ *ᵥ d) = 0 := by
        rw [sub_smul, sub_eq_zero]
        exact add_left_cancel (e1.trans e2.symm)
      exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
    intro α
    rw [lineJ_affine, Matrix.mulVec_add, Matrix.mulVec_smul, hd, smul_zero, add_zero]
    rw [hd, smul_zero, add_zero] at e1
    exact e1
  constructor
  · -- "and that contains at most one point for each `α`"
    intro hz
    refine ⟨z (Sum.inl ()), determined H (rho_nonneg H (hlo.trans hα₁.1.le)) hz
      (hall _) (lineJ_alpha _).symm⟩
  · rintro ⟨α, rfl⟩
    exact hall α

omit [DecidableEq E] in
/-- The number `N = 1 + n + k ≤ 2n + 1` of unknowns. -/
lemma card_col_le : Fintype.card (Col f m β α₁) ≤ 2 * Fintype.card E + 1 := by
  simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
  have : nb f m β α₁ ≤ Fintype.card E := by
    unfold nb numVals valsAbove
    exact (card_filter_le _ _).trans (card_image_le.trans (by simp))
  omega

end Solutions

/-! ### (2) A breakpoint singled out by one more equation -/

section Breakpoint

variable {E : Type*} [Fintype E] [DecidableEq E] {f : Finset E → ℝ} {m β : E → ℝ}

/-- An open interval of positive shares without event points has constant state (not in the
paper: the proof of `thm:bitlength` uses this without proof, in (2), "As there are finitely many
event points, there are open intervals `J_−` … and `J_+` … on each of which the state is
constant", and in (4)). The state is locally constant there, and the interval is connected. -/
lemma state_eq_of_no_event {lo hi : ℝ} (hlo : 0 ≤ lo)
    (hno : ∀ α ∈ Set.Ioo lo hi, ¬ Tracing.IsEvent f m β α) :
    ∀ α ∈ Set.Ioo lo hi, ∀ α' ∈ Set.Ioo lo hi, state f m β α = state f m β α' := by
  let _ : TopologicalSpace (Finset E × Finset E × Finset (Finset E)) := ⊥
  have : DiscreteTopology (Finset E × Finset E × Finset (Finset E)) := ⟨rfl⟩
  have hloc : ∀ α ∈ Set.Ioo lo hi, ∀ᶠ γ in nhds α, state f m β γ = state f m β α := by
    intro α hα
    have hα0 : 0 < α := lt_of_le_of_lt hlo hα.1
    have h := hno α hα
    rw [Tracing.isEvent_iff] at h
    push Not at h
    obtain ⟨a, c, ha, hc, hS⟩ := h hα0
    filter_upwards [Ioo_mem_nhds ha hc] with γ hγ
    exact hS γ hγ α ⟨ha, hc⟩
  have hcont : ContinuousOn (state f m β) (Set.Ioo lo hi) := fun α hα =>
    ((continuousAt_const (y := state f m β α)).congr
      ((hloc α hα).mono fun γ hγ => hγ.symm)).continuousWithinAt
  intro α hα α' hα'
  exact isPreconnected_Ioo.constant hcont hα hα'

/-- (2), (a): "As there are finitely many event points, there are open intervals `J_−` with
right endpoint `b` and `J_+` with left endpoint `b` on each of which the state is constant", here
`J_− = (b − ε, b)` and `J_+ = (b, b + ε)` with `0 < ε ≤ b`. -/
lemma exists_sides (H : Tracing.Hyp f m β) {b : ℝ} (hb : 0 < b) :
    ∃ ε > 0, ε ≤ b ∧
      (∀ α ∈ Set.Ioo (b - ε) b, ∀ α' ∈ Set.Ioo (b - ε) b, state f m β α = state f m β α') ∧
      ∀ α ∈ Set.Ioo b (b + ε), ∀ α' ∈ Set.Ioo b (b + ε), state f m β α = state f m β α' := by
  classical
  set T := (events_finite H).toFinset.erase b
  have hopen : IsOpen ((↑T : Set ℝ)ᶜ) := (Finset.finite_toSet _).isClosed.isOpen_compl
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.1 hopen b (by simp [T])
  set ε := min ε₀ b
  have hε : 0 < ε := lt_min hε₀ hb
  have hno : ∀ α, α ≠ b → b - ε < α → α < b + ε → ¬ Tracing.IsEvent f m β α := by
    intro α hne h1 h2 hev
    have hball' : α ∈ Metric.ball b ε₀ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [min_le_left ε₀ b]
    exact hball hball' (Finset.mem_coe.2 (Finset.mem_erase.2
      ⟨hne, (Set.Finite.mem_toFinset _).2 hev⟩))
  refine ⟨ε, hε, min_le_right _ _, ?_, ?_⟩
  · exact state_eq_of_no_event (by linarith [min_le_right ε₀ b])
      fun α hα => hno α hα.2.ne hα.1 (by linarith [hα.2])
  · exact state_eq_of_no_event hb.le fun α hα => hno α hα.1.ne' (by linarith [hα.1]) hα.2

/-- The vector `v` that (`eq:velocity`) assigns to a state depends only on the state (plumbing for
the step "`lem:velocity` gives `x*` the same slope on `J_−` and on `J_+`" of (2), (b)). -/
lemma velocity_eq_of_state_eq {α α' : ℝ} (h : state f m β α = state f m β α') :
    velocity f m β α = velocity f m β α' := by
  classical
  have hS : StateConstOn f m β {α, α'} := stateConstOn_iff.2 fun γ hγ γ' hγ' => by
    rcases hγ with rfl | rfl <;> rcases hγ' with rfl | rfl
    · rfl
    · exact h
    · exact h.symm
    · rfl
  have hα : α ∈ ({α, α'} : Set ℝ) := Or.inl rfl
  have hα' : α' ∈ ({α, α'} : Set ℝ) := Or.inr rfl
  funext e
  have hB : blockNZ f m β α e = blockNZ f m β α' e := by
    ext g
    simp only [blockNZ, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hS.block α hα α' hα' g e, ne_eq, ne_eq, hS.zero α hα α' hα' g]
  unfold velocity
  rw [hB]
  by_cases h1 : rho f m β α e = 0
  · rw [ite_eq_left h1, ite_eq_left ((hS.free α hα α' hα' e).1 h1)]
  · rw [ite_eq_right h1, ite_eq_right (fun h => h1 ((hS.free α hα α' hα' e).2 h))]
    by_cases h2 : bestResponse f m β α e = 0
    · rw [ite_eq_left h2, ite_eq_left ((hS.zero α hα α' hα' e).1 h2)]
    · rw [ite_eq_right h2, ite_eq_right (fun h => h2 ((hS.zero α hα α' hα' e).2 h))]

/-- A function continuous on `[0, ∞)` that vanishes on an interval `(lo, hi)` with `0 ≤ lo < hi`
vanishes at its ends (the steps "hence at `b`" and "by continuity" of (2), (c); plumbing). -/
lemma eq_zero_at_end {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Set.Ici 0)) {lo hi b : ℝ} (hlo : 0 ≤ lo)
    (hlohi : lo < hi) (hb : b = lo ∨ b = hi) (h0 : ∀ α ∈ Set.Ioo lo hi, φ α = 0) : φ b = 0 := by
  have hcl : IsClosed (Set.Ici (0 : ℝ) ∩ φ ⁻¹' {0}) :=
    hφ.preimage_isClosed_of_isClosed isClosed_Ici isClosed_singleton
  have hsub : Set.Ioo lo hi ⊆ Set.Ici (0 : ℝ) ∩ φ ⁻¹' {0} := fun α hα =>
    ⟨Set.mem_Ici.2 (hlo.trans hα.1.le), h0 α hα⟩
  have hbcl : b ∈ closure (Set.Ioo lo hi) := by
    rw [closure_Ioo hlohi.ne]
    rcases hb with rfl | rfl
    · exact ⟨le_rfl, hlohi.le⟩
    · exact ⟨hlohi.le, le_rfl⟩
  exact (hcl.closure_subset_iff.2 hsub hbcl).2

omit [DecidableEq E] in
/-- The step "so `φ` is a nonconstant affine function that vanishes at `b`, and the equation
works" of (2), (c): if along the line of an interval `J = (lo, hi)` with end `b` the equation `ex`
is a function `φ` continuous on `[0, ∞)` with `φ(b) = 0` and `φ(α₁) ≠ 0`, then along the line `ex`
holds at `α = b` and nowhere else. -/
lemma holds_only_at {lo hi α₁ b : ℝ} (hlo : 0 ≤ lo) (hα₁ : α₁ ∈ Set.Ioo lo hi)
    (hb : b = lo ∨ b = hi) (ex : Col f m β α₁ → ℝ) {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Set.Ici 0))
    (hline : ∀ α ∈ Set.Ioo lo hi, ex ⬝ᵥ lineJ f m β α₁ α = φ α) (hφb : φ b = 0)
    (hφ₁ : φ α₁ ≠ 0) :
    ∀ α, ex ⬝ᵥ lineJ f m β α₁ α = 0 ↔ α = b := by
  set A := ex ⬝ᵥ lineJ f m β α₁ 0
  set B := ex ⬝ᵥ (lineJ f m β α₁ 1 - lineJ f m β α₁ 0)
  have hψ : ∀ α, ex ⬝ᵥ lineJ f m β α₁ α = A + α * B := fun α => by
    rw [lineJ_affine, dotProduct_add, dotProduct_smul, smul_eq_mul]
  have hlohi : lo < hi := hα₁.1.trans hα₁.2
  -- `A + α B − φ(α)` vanishes on `J`, hence at `b`
  have hb0 : A + b * B = 0 := by
    have h : A + b * B - φ b = 0 := eq_zero_at_end (φ := fun α => A + α * B - φ α)
      ((continuousOn_const.add (continuousOn_id.mul continuousOn_const)).sub hφ) hlo hlohi hb
      fun α hα => by rw [← hψ, hline α hα, sub_self]
    linarith
  -- and it does not vanish at `α₁`, so it is nonconstant
  have hB : B ≠ 0 := by
    intro hB0
    apply hφ₁
    rw [← hline α₁ hα₁, hψ, hB0]
    rw [hB0] at hb0
    linarith
  intro α
  rw [hψ]
  constructor
  · intro h
    have : (α - b) * B = 0 := by linarith
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hB)
  · rintro rfl
    exact hb0

/-- The equation `ρ_j = 0` of (2), (c), in the case that the sets of free elements differ: `e` is
free on one of the two intervals, `(lo', hi')`, and not on the other one, `J = (lo, hi)`, where it
lies in the block `D_j`. -/
lemma eq_of_free (H : Tracing.Hyp f m β) {lo hi lo' hi' α₁ α₂ b : ℝ} (hlo : 0 ≤ lo)
    (hS : ∀ α ∈ Set.Ioo lo hi, ∀ α' ∈ Set.Ioo lo hi, state f m β α = state f m β α')
    (hα₁ : α₁ ∈ Set.Ioo lo hi) (hb : b = lo ∨ b = hi) (hlo' : 0 ≤ lo')
    (hS' : ∀ α ∈ Set.Ioo lo' hi', ∀ α' ∈ Set.Ioo lo' hi', state f m β α = state f m β α')
    (hα₂ : α₂ ∈ Set.Ioo lo' hi') (hb' : b = lo' ∨ b = hi') {e : E}
    (h₂ : e ∈ freeSet f m β α₂) (h₁ : e ∉ freeSet f m β α₁) :
    ∃ ex : Col f m β α₁ → ℝ, (∀ c, ∃ k : ℤ, ex c = k ∧ |k| ≤ 1) ∧
      ∀ α, ex ⬝ᵥ lineJ f m β α₁ α = 0 ↔ α = b := by
  have hc : ContinuousOn (fun α => rho f m β α e) (Set.Ici 0) := by
    have := (continuous_apply e).comp_continuousOn (pwaffine H).1
    unfold rho marg
    exact (continuousOn_id.mul continuousOn_const).sub (continuousOn_const.mul this)
  have hT : StateConstOn f m β (Set.Ioo lo hi) := stateConstOn_iff.2 hS
  have hT' : StateConstOn f m β (Set.Ioo lo' hi') := stateConstOn_iff.2 hS'
  -- "where it lies in a block `D_j`"
  obtain ⟨j, hj⟩ := exists_val_eq (lt_of_le_of_ne (rho_nonneg H (hlo.trans hα₁.1.le) e)
    (Ne.symm (mem_freeSet.not.1 h₁)))
  -- "Then `ρ_e` vanishes on the first interval, hence at `b`,"
  have hρb : rho f m β b e = 0 := eq_zero_at_end hc hlo' (hα₂.1.trans hα₂.2) hb'
    fun α hα => (hT'.free α₂ hα₂ α hα e).1 (mem_freeSet.1 h₂)
  -- "and `ρ^J_j = ρ_e` is positive on `J`,": along the line, the left-hand side of `ρ_j = 0` is
  -- `ρ_e` on `J`, and `ρ_e(α₁) ≠ 0`
  set ex : Col f m β α₁ → ℝ := fun c => if c = Sum.inr (Sum.inr j) then 1 else 0
  have hline : ∀ α ∈ Set.Ioo lo hi, ex ⬝ᵥ lineJ f m β α₁ α = rho f m β α e := fun α hα => by
    have hdot : ex ⬝ᵥ lineJ f m β α₁ α = lineJ f m β α₁ α (Sum.inr (Sum.inr j)) := by
      simp [ex, dotProduct]
    rw [hdot, lineJ_eq_solJ H hlo hS hα₁ hα]
    exact (hT.block α₁ hα₁ α hα _ e).1 (by rw [rho_rep, hj])
  have hpos : rho f m β α₁ e ≠ 0 := mem_freeSet.not.1 h₁
  -- "so `ρ^J_j` is a nonconstant affine function that vanishes at `b`, and the equation `ρ_j = 0`
  -- works."
  refine ⟨ex, fun c => ?_, holds_only_at hlo hα₁ hb ex hc hline hρb hpos⟩
  by_cases hcj : c = Sum.inr (Sum.inr j)
  · exact ⟨1, by simp [ex, hcj], by simp⟩
  · exact ⟨0, by simp [ex, hcj], by simp⟩

/-- The equation `x_e = 0` of (2), (c), in the case that the zero sets differ: `x*_e = 0` on one
interval, `(lo', hi')` (`e ∈ Z` there), and `x*_e > 0` on the other one, `J = (lo, hi)` (`e ∉ Z`
there). -/
lemma eq_of_zero (H : Tracing.Hyp f m β) {lo hi lo' hi' α₁ α₂ b : ℝ} (hlo : 0 ≤ lo)
    (hS : ∀ α ∈ Set.Ioo lo hi, ∀ α' ∈ Set.Ioo lo hi, state f m β α = state f m β α')
    (hα₁ : α₁ ∈ Set.Ioo lo hi) (hb : b = lo ∨ b = hi) (hlo' : 0 ≤ lo')
    (hS' : ∀ α ∈ Set.Ioo lo' hi', ∀ α' ∈ Set.Ioo lo' hi', state f m β α = state f m β α')
    (hα₂ : α₂ ∈ Set.Ioo lo' hi') (hb' : b = lo' ∨ b = hi') {e : E}
    (h₂ : e ∈ zeroSet f m β α₂) (h₁ : e ∉ zeroSet f m β α₁) :
    ∃ ex : Col f m β α₁ → ℝ, (∀ c, ∃ k : ℤ, ex c = k ∧ |k| ≤ 1) ∧
      ∀ α, ex ⬝ᵥ lineJ f m β α₁ α = 0 ↔ α = b := by
  have hc : ContinuousOn (fun α => bestResponse f m β α e) (Set.Ici 0) :=
    (continuous_apply e).comp_continuousOn (pwaffine H).1
  have hT' : StateConstOn f m β (Set.Ioo lo' hi') := stateConstOn_iff.2 hS'
  -- "in the same way": `x*_e` vanishes on the first interval, hence at `b`,
  have hxb : bestResponse f m β b e = 0 := eq_zero_at_end hc hlo' (hα₂.1.trans hα₂.2) hb'
    fun α hα => (hT'.zero α₂ hα₂ α hα e).1 (mem_zeroSet.1 h₂)
  -- and `x^J_e = x*_e` is positive on `J`: along the line, the left-hand side of `x_e = 0` is
  -- `x*_e` on `J`, and `x*_e(α₁) ≠ 0`,
  set ex : Col f m β α₁ → ℝ := fun c => if c = Sum.inr (Sum.inl e) then 1 else 0
  have hline : ∀ α ∈ Set.Ioo lo hi, ex ⬝ᵥ lineJ f m β α₁ α = bestResponse f m β α e :=
    fun α hα => by
      have hdot : ex ⬝ᵥ lineJ f m β α₁ α = lineJ f m β α₁ α (Sum.inr (Sum.inl e)) := by
        simp [ex, dotProduct]
      rw [hdot, lineJ_eq_solJ H hlo hS hα₁ hα]
      rfl
  have hpos : bestResponse f m β α₁ e ≠ 0 := mem_zeroSet.not.1 h₁
  -- so `x^J_e` is a nonconstant affine function that vanishes at `b`, and the equation `x_e = 0`
  -- works.
  refine ⟨ex, fun c => ?_, holds_only_at hlo hα₁ hb ex hc hline hxb hpos⟩
  by_cases hce : c = Sum.inr (Sum.inl e)
  · exact ⟨1, by simp [ex, hce], by simp⟩
  · exact ⟨0, by simp [ex, hce], by simp⟩

/-- The equation `ρ_j − ρ_{j'} = 0` of (2), (c), in the case that the partitions into blocks
differ: `e` and `e'` lie in a common block on one interval, `(lo', hi')`, and in different blocks
`D_j ≠ D_{j'}` on the other one, `J = (lo, hi)`. -/
lemma eq_of_block (H : Tracing.Hyp f m β) {lo hi lo' hi' α₁ α₂ b : ℝ} (hlo : 0 ≤ lo)
    (hS : ∀ α ∈ Set.Ioo lo hi, ∀ α' ∈ Set.Ioo lo hi, state f m β α = state f m β α')
    (hα₁ : α₁ ∈ Set.Ioo lo hi) (hb : b = lo ∨ b = hi) (hlo' : 0 ≤ lo')
    (hS' : ∀ α ∈ Set.Ioo lo' hi', ∀ α' ∈ Set.Ioo lo' hi', state f m β α = state f m β α')
    (hα₂ : α₂ ∈ Set.Ioo lo' hi') (hb' : b = lo' ∨ b = hi') {e e' : E}
    (h₂ : rho f m β α₂ e = rho f m β α₂ e') (h₁ : rho f m β α₁ e ≠ rho f m β α₁ e')
    (he : e ∉ freeSet f m β α₁) (he' : e' ∉ freeSet f m β α₁) :
    ∃ ex : Col f m β α₁ → ℝ, (∀ c, ∃ k : ℤ, ex c = k ∧ |k| ≤ 1) ∧
      ∀ α, ex ⬝ᵥ lineJ f m β α₁ α = 0 ↔ α = b := by
  have hc : ∀ g, ContinuousOn (fun α => rho f m β α g) (Set.Ici 0) := fun g => by
    have := (continuous_apply g).comp_continuousOn (pwaffine H).1
    unfold rho marg
    exact (continuousOn_id.mul continuousOn_const).sub (continuousOn_const.mul this)
  have hT : StateConstOn f m β (Set.Ioo lo hi) := stateConstOn_iff.2 hS
  have hT' : StateConstOn f m β (Set.Ioo lo' hi') := stateConstOn_iff.2 hS'
  have hρ := rho_nonneg H (hlo.trans hα₁.1.le)
  -- the blocks `D_j ≠ D_{j'}` of `e` and `e'` on `J`
  obtain ⟨j, hj⟩ := exists_val_eq (lt_of_le_of_ne (hρ e) (Ne.symm (mem_freeSet.not.1 he)))
  obtain ⟨j', hj'⟩ := exists_val_eq (lt_of_le_of_ne (hρ e') (Ne.symm (mem_freeSet.not.1 he')))
  have hjj' : j ≠ j' := fun h => h₁ (by rw [← hj, ← hj', h])
  -- "Then `ρ_e = ρ_{e'}` at `b` by continuity"
  have hρb : rho f m β b e - rho f m β b e' = 0 :=
    eq_zero_at_end ((hc e).sub (hc e')) hlo' (hα₂.1.trans hα₂.2) hb'
      fun α hα => sub_eq_zero.2 ((hT'.block α₂ hα₂ α hα e e').1 h₂)
  -- "and `ρ_e ≠ ρ_{e'}` on `J`,": along the line, the left-hand side of `ρ_j − ρ_{j'} = 0` is
  -- `ρ_e − ρ_{e'}` on `J`, and `ρ_e(α₁) ≠ ρ_{e'}(α₁)`
  set ex : Col f m β α₁ → ℝ := fun c =>
    (if c = Sum.inr (Sum.inr j) then 1 else 0) - if c = Sum.inr (Sum.inr j') then 1 else 0
  have hline : ∀ α ∈ Set.Ioo lo hi,
      ex ⬝ᵥ lineJ f m β α₁ α = rho f m β α e - rho f m β α e' := fun α hα => by
    have hdot : ex ⬝ᵥ lineJ f m β α₁ α = lineJ f m β α₁ α (Sum.inr (Sum.inr j)) -
        lineJ f m β α₁ α (Sum.inr (Sum.inr j')) := by
      simp [ex, dotProduct, sub_mul, Finset.sum_sub_distrib]
    rw [hdot, lineJ_eq_solJ H hlo hS hα₁ hα]
    simp only [solJ, vec, Sum.elim_inr]
    rw [(hT.block α₁ hα₁ α hα (rep f m β α₁ j) e).1 (by rw [rho_rep, hj]),
      (hT.block α₁ hα₁ α hα (rep f m β α₁ j') e').1 (by rw [rho_rep, hj'])]
  -- "so `ρ^J_j − ρ^J_{j'}` is a nonconstant affine function that vanishes at `b`, and the equation
  -- `ρ_j − ρ_{j'} = 0` works."
  refine ⟨ex, fun c => ?_, holds_only_at hlo hα₁ hb ex
    (φ := fun α => rho f m β α e - rho f m β α e') ((hc e).sub (hc e')) hline hρb
    (sub_ne_zero.2 h₁)⟩
  by_cases hcj : c = Sum.inr (Sum.inr j)
  · have : c ≠ Sum.inr (Sum.inr j') := by rw [hcj]; simpa using hjj'
    refine ⟨1, ?_, by norm_num⟩
    simp only [ex]
    rw [ite_eq_left hcj, ite_eq_right this]
    norm_num
  · by_cases hcj' : c = Sum.inr (Sum.inr j')
    · refine ⟨-1, ?_, by norm_num⟩
      simp only [ex]
      rw [ite_eq_right hcj, ite_eq_left hcj']
      norm_num
    · refine ⟨0, ?_, by norm_num⟩
      simp only [ex]
      rw [ite_eq_right hcj, ite_eq_right hcj']
      norm_num

/-- **(2)** of the proof of `thm:bitlength` (`stoc-sections/appB-bitlength.tex:53-78`, "Next we
single out a breakpoint by one more equation"), its first part: for a breakpoint `b`, there are an
open interval `J = (lo, hi)`, `0 ≤ lo`, with constant state, a share `α₁ ∈ J`, and an equation with
coefficients in `{0, ±1}` and right-hand side `0` in the unknowns of `J` that, along the line of
solutions of (1), holds at `α = b` and nowhere else. Steps: (a)
`J_−` and `J_+` (`exists_sides`); (b) the two states differ; (c) the three cases in the paper's
order: the sets of free elements differ (`eq_of_free`), the zero sets differ (`eq_of_zero`),
otherwise the partitions into blocks differ (`eq_of_block`). -/
theorem step2_equation (H : Tracing.Hyp f m β) {b : ℝ}
    (hb : b ∈ breakpoints (bestResponse f m β)) :
    ∃ lo hi α₁ : ℝ, 0 ≤ lo ∧
      (∀ α ∈ Set.Ioo lo hi, ∀ α' ∈ Set.Ioo lo hi, state f m β α = state f m β α') ∧
      α₁ ∈ Set.Ioo lo hi ∧ (b = lo ∨ b = hi) ∧
      ∃ ex : Col f m β α₁ → ℝ, (∀ c, ∃ k : ℤ, ex c = k ∧ |k| ≤ 1) ∧
        ∀ α, ex ⬝ᵥ lineJ f m β α₁ α = 0 ↔ α = b := by
  classical
  have hb0 : 0 < b := hb.1
  -- (a) "As there are finitely many event points, there are open intervals `J_−` with right
  -- endpoint `b` and `J_+` with left endpoint `b` on each of which the state is constant."
  obtain ⟨ε, hε, hεb, hSm, hSp⟩ := exists_sides H hb0
  have hlom : 0 ≤ b - ε := by linarith
  set αm := b - ε / 2
  set αp := b + ε / 2
  have hαm : αm ∈ Set.Ioo (b - ε) b := ⟨by simp only [αm]; linarith, by simp only [αm]; linarith⟩
  have hαp : αp ∈ Set.Ioo b (b + ε) := ⟨by simp only [αp]; linarith, by simp only [αp]; linarith⟩
  -- (b) "The two states differ: otherwise, `lem:velocity` gives `x*` the same slope on `J_−` and on
  -- `J_+`, and as `x*` is continuous, it would be affine on `J_− ∪ {b} ∪ J_+`."
  have hdiff : state f m β αm ≠ state f m β αp := by
    intro hsame
    have hv := velocity_eq_of_state_eq hsame
    have hL : ∀ α ∈ Set.Ioo (b - ε) b, bestResponse f m β α =
        fun e => bestResponse f m β αm e + (α - αm) * velocity f m β αp e := fun α hα => by
      rw [(velocity_lemma H hlom hSm hαm).1 α hα, hv]
    have hR := (velocity_lemma H hb0.le hSp hαp).1
    have hc : ∀ e, ContinuousOn (fun α => bestResponse f m β α e) (Set.Ici 0) := fun e =>
      (continuous_apply e).comp_continuousOn (pwaffine H).1
    have hbL : ∀ e, bestResponse f m β b e =
        bestResponse f m β αm e + (b - αm) * velocity f m β αp e := by
      intro e
      have h : bestResponse f m β b e -
          (bestResponse f m β αm e + (b - αm) * velocity f m β αp e) = 0 :=
        eq_zero_at_end (φ := fun α => bestResponse f m β α e -
          (bestResponse f m β αm e + (α - αm) * velocity f m β αp e))
          ((hc e).sub (by fun_prop)) (lo := b - ε) (hi := b) hlom (by linarith) (Or.inr rfl)
          fun α hα => by rw [hL α hα]; simp
      linarith
    have hbR : ∀ e, bestResponse f m β b e =
        bestResponse f m β αp e + (b - αp) * velocity f m β αp e := by
      intro e
      have h : bestResponse f m β b e -
          (bestResponse f m β αp e + (b - αp) * velocity f m β αp e) = 0 :=
        eq_zero_at_end (φ := fun α => bestResponse f m β α e -
          (bestResponse f m β αp e + (α - αp) * velocity f m β αp e))
          ((hc e).sub (by fun_prop)) (lo := b) (hi := b + ε) hb0.le (by linarith) (Or.inl rfl)
          fun α hα => by rw [hR α hα]; simp
      linarith
    apply hb.2
    refine ⟨ε, hε, fun e => bestResponse f m β b e - b * velocity f m β αp e,
      velocity f m β αp, fun α hα => ?_⟩
    rcases lt_trichotomy α b with hαb | rfl | hαb
    · rw [hL α ⟨hα.1, hαb⟩]
      funext e
      beta_reduce
      rw [hbL e]
      ring
    · funext e
      ring
    · rw [hR α ⟨hαb, hα.2⟩]
      funext e
      beta_reduce
      rw [hbR e]
      ring
  -- (c) "We find an interval `J ∈ {J_−, J_+}` and an equation with coefficients in `{0, ±1}` and
  -- right-hand side `0` in the unknowns of `J` that, along the line of solutions above, holds at
  -- `α = b` and nowhere else."
  by_cases hfree : freeSet f m β αm ≠ freeSet f m β αp
  · -- "If the sets of free elements differ, some element `e` is free on one of the two intervals
    -- and not on the other one, `J`, where it lies in a block `D_j`. … the equation `ρ_j = 0`
    -- works."
    obtain ⟨e, he⟩ : ∃ e, ¬(e ∈ freeSet f m β αm ↔ e ∈ freeSet f m β αp) := by
      by_contra h
      push Not at h
      exact hfree (Finset.ext h)
    push Not at he
    rcases he with ⟨hm, hp⟩ | ⟨hm, hp⟩
    · -- free on `J_−`, not on `J = J_+`
      exact ⟨b, b + ε, αp, hb0.le, hSp, hαp, Or.inl rfl,
        eq_of_free H hb0.le hSp hαp (Or.inl rfl) hlom hSm hαm (Or.inr rfl) hm hp⟩
    · -- free on `J_+`, not on `J = J_−`
      exact ⟨b - ε, b, αm, hlom, hSm, hαm, Or.inr rfl,
        eq_of_free H hlom hSm hαm (Or.inr rfl) hb0.le hSp hαp (Or.inl rfl) hp hm⟩
  push Not at hfree
  by_cases hzero : zeroSet f m β αm ≠ zeroSet f m β αp
  · -- "If the zero sets differ, some element `e` has `x*_e = 0` on one interval and `x*_e > 0`
    -- on the other one, `J`, and the equation `x_e = 0` works in the same way."
    obtain ⟨e, he⟩ : ∃ e, ¬(e ∈ zeroSet f m β αm ↔ e ∈ zeroSet f m β αp) := by
      by_contra h
      push Not at h
      exact hzero (Finset.ext h)
    push Not at he
    rcases he with ⟨hm, hp⟩ | ⟨hm, hp⟩
    · -- `x*_e = 0` on `J_−`, `x*_e > 0` on `J = J_+`
      exact ⟨b, b + ε, αp, hb0.le, hSp, hαp, Or.inl rfl,
        eq_of_zero H hb0.le hSp hαp (Or.inl rfl) hlom hSm hαm (Or.inr rfl) hm hp⟩
    · -- `x*_e = 0` on `J_+`, `x*_e > 0` on `J = J_−`
      exact ⟨b - ε, b, αm, hlom, hSm, hαm, Or.inr rfl,
        eq_of_zero H hlom hSm hαm (Or.inr rfl) hb0.le hSp hαp (Or.inl rfl) hp hm⟩
  push Not at hzero
  -- "Otherwise, the partitions into blocks differ,"
  have hpart : blockPartition f m β αm ≠ blockPartition f m β αp := fun h =>
    hdiff (by simp only [state, hfree, hzero, h])
  -- "so there are elements `e, e'` that lie in a common block on one interval and in different
  -- blocks `D_j ≠ D_{j'}` on the other one, `J`." Otherwise the relation "equal marginal", which
  -- determines the blocks, would be the same on both intervals, and so would the partitions.
  have hfr : ∀ g, rho f m β αm g = 0 ↔ rho f m β αp g = 0 := fun g => by
    simpa only [mem_freeSet] using Finset.ext_iff.1 hfree g
  have hzr : ∀ g, bestResponse f m β αm g = 0 ↔ bestResponse f m β αp g = 0 := fun g => by
    simpa only [mem_zeroSet] using Finset.ext_iff.1 hzero g
  have hblock : ∃ e e', ¬(rho f m β αm e = rho f m β αm e' ↔
      rho f m β αp e = rho f m β αp e') := by
    by_contra hbl
    push Not at hbl
    apply hpart
    have hS2 : StateConstOn f m β {αm, αp} := by
      refine ⟨fun γ hγ γ' hγ' e => ?_, fun γ hγ γ' hγ' e => ?_, fun γ hγ γ' hγ' e e' => ?_⟩ <;>
        rcases hγ with rfl | rfl <;> rcases hγ' with rfl | rfl
      all_goals first
        | exact Iff.rfl
        | exact hfr e
        | exact (hfr e).symm
        | exact hzr e
        | exact (hzr e).symm
        | exact hbl e e'
        | exact (hbl e e').symm
    exact congrArg (fun s => s.2.2) (stateConstOn_iff.1 hS2 αm (Or.inl rfl) αp (Or.inr rfl))
  obtain ⟨e, e', hee'⟩ := hblock
  push Not at hee'
  -- the two elements lie in blocks on `J`: they are not free there, as the free sets agree
  have hnf : ∀ γ γ', (γ = αm ∧ γ' = αp ∨ γ = αp ∧ γ' = αm) →
      rho f m β γ e = rho f m β γ e' → rho f m β γ' e ≠ rho f m β γ' e' →
        e ∉ freeSet f m β γ' ∧ e' ∉ freeSet f m β γ' := by
    rintro γ γ' hγγ' heq hne
    have hfr' : ∀ g, rho f m β γ g = 0 ↔ rho f m β γ' g = 0 := fun g => by
      rcases hγγ' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hfr g
      · exact (hfr g).symm
    rw [mem_freeSet, mem_freeSet]
    constructor
    · intro h0
      apply hne
      rw [h0, eq_comm, ← hfr' e', ← heq, hfr' e]
      exact h0
    · intro h0
      apply hne
      rw [h0, ← hfr' e, heq, hfr' e']
      exact h0
  rcases hee' with ⟨hm, hp⟩ | ⟨hm, hp⟩
  · -- a common block on `J_−`, different blocks on `J = J_+`
    obtain ⟨h1, h2⟩ := hnf αm αp (Or.inl ⟨rfl, rfl⟩) hm hp
    exact ⟨b, b + ε, αp, hb0.le, hSp, hαp, Or.inl rfl,
      eq_of_block H hb0.le hSp hαp (Or.inl rfl) hlom hSm hαm (Or.inr rfl) hm hp h1 h2⟩
  · -- a common block on `J_+`, different blocks on `J = J_−`
    obtain ⟨h1, h2⟩ := hnf αp αm (Or.inr ⟨rfl, rfl⟩) hp hm
    exact ⟨b - ε, b, αm, hlom, hSm, hαm, Or.inr rfl,
      eq_of_block H hlom hSm hαm (Or.inr rfl) hb0.le hSp hαp (Or.inl rfl) hp hm h1 h2⟩

end Breakpoint

/-! ### (2), (d), and (3): Cramer's rule and the size of a breakpoint -/

section Size

variable {E : Type*} [Fintype E] [DecidableEq E] {f : Finset E → ℝ} {m β : E → ℝ} {α₁ : ℝ}

variable (f m β α₁) in
/-- The equations of the state at `α₁` with the extra equation `ex` of (2) (the row `none`). -/
noncomputable def bigG (ex : Col f m β α₁ → ℝ) :
    Matrix (Option (Row f m β α₁)) (Col f m β α₁) ℝ :=
  Matrix.of fun r => Option.elim r ex (eqG f m β α₁)

variable (f m β α₁) in
/-- Their right-hand sides. -/
noncomputable def bigH : Option (Row f m β α₁) → ℝ := fun r => Option.elim r 0 (eqH f m β α₁)

lemma bigG_mulVec_none (ex z : Col f m β α₁ → ℝ) :
    (bigG f m β α₁ ex *ᵥ z) none = ex ⬝ᵥ z := rfl

lemma bigG_mulVec_some (ex z : Col f m β α₁ → ℝ) (r : Row f m β α₁) :
    (bigG f m β α₁ ex *ᵥ z) (some r) = (eqG f m β α₁ *ᵥ z) r := rfl

/-- **(2)**, (d) (`appB-bitlength.tex:74-78`): "Adding this equation to the equations of `J` gives
a system whose only solution is `(b, x*(b), ρ^J(b))`. So some `N` of its equations form a square
system `Gz = h` with a nonsingular matrix `G` and the same solution, and by Cramer's rule
`b = det G_α / det G`, where `G_α` arises from `G` by replacing the column of `α` with `h`." -/
theorem step2_cramer (H : Tracing.Hyp f m β) {lo hi b : ℝ} (hlo : 0 ≤ lo)
    (hS : ∀ α ∈ Set.Ioo lo hi, ∀ α' ∈ Set.Ioo lo hi, state f m β α = state f m β α')
    (hα₁ : α₁ ∈ Set.Ioo lo hi) (hb : b = lo ∨ b = hi) (ex : Col f m β α₁ → ℝ)
    (hex : ∀ α, ex ⬝ᵥ lineJ f m β α₁ α = 0 ↔ α = b) :
    (∀ z, bigG f m β α₁ ex *ᵥ z = bigH f m β α₁ ↔ z = lineJ f m β α₁ b) ∧
    (∀ e, lineJ f m β α₁ b (Sum.inr (Sum.inl e)) = bestResponse f m β b e) ∧
    ∃ σ : Col f m β α₁ → Option (Row f m β α₁), Function.Injective σ ∧
      ((bigG f m β α₁ ex).submatrix σ id).det ≠ 0 ∧
      b = (((bigG f m β α₁ ex).submatrix σ id).updateCol (Sum.inl ())
        (bigH f m β α₁ ∘ σ)).det / ((bigG f m β α₁ ex).submatrix σ id).det := by
  -- "Adding this equation to the equations of `J` gives a system whose only solution is
  -- `(b, x*(b), ρ^J(b))`."
  have huniq : ∀ z, bigG f m β α₁ ex *ᵥ z = bigH f m β α₁ ↔ z = lineJ f m β α₁ b := by
    intro z
    constructor
    · intro hz
      have hJ : eqG f m β α₁ *ᵥ z = eqH f m β α₁ := funext fun r => congrFun hz (some r)
      obtain ⟨α, rfl⟩ := (solves_iff_line H hlo hS hα₁ z).1 hJ
      have hα := congrFun hz none
      rw [bigG_mulVec_none] at hα
      rw [(hex α).1 hα]
    · rintro rfl
      funext r
      rcases r with _ | r
      · rw [bigG_mulVec_none]
        exact (hex b).2 rfl
      · rw [bigG_mulVec_some]
        exact congrFun (((solves_iff_line H hlo hS hα₁ _).2 ⟨b, rfl⟩)) r
  have hxb : ∀ e, lineJ f m β α₁ b (Sum.inr (Sum.inl e)) = bestResponse f m β b e := by
    intro e
    have hc : ContinuousOn (fun α => bestResponse f m β α e) (Set.Ici 0) :=
      (continuous_apply e).comp_continuousOn (pwaffine H).1
    have h : bestResponse f m β b e - lineJ f m β α₁ b (Sum.inr (Sum.inl e)) = 0 :=
      eq_zero_at_end (φ := fun α => bestResponse f m β α e - xJ f m β α₁ α e)
        (hc.sub (by unfold xJ; fun_prop)) hlo (hα₁.1.trans hα₁.2) hb fun α hα => by
          have := congrFun (lineJ_eq_solJ H hlo hS hα₁ hα) (Sum.inr (Sum.inl e))
          simp only [lineJ, solJ, vec, Sum.elim_inr, Sum.elim_inl] at this
          simp only [this, sub_self]
    linarith
  refine ⟨huniq, hxb, ?_⟩
  -- "So some `N` of its equations form a square system `Gz = h` with a nonsingular matrix `G` and
  -- the same solution,"
  have hker : ∀ w, bigG f m β α₁ ex *ᵥ w = 0 → w = 0 := by
    intro w hw
    have h1 : bigG f m β α₁ ex *ᵥ (lineJ f m β α₁ b + w) = bigH f m β α₁ := by
      rw [Matrix.mulVec_add, hw, add_zero]
      exact (huniq _).2 rfl
    have := (huniq _).1 h1
    simpa using this
  obtain ⟨σ, hσ, hdet⟩ := exists_square_subsystem _ hker
  have hsol : (bigG f m β α₁ ex).submatrix σ id *ᵥ lineJ f m β α₁ b = bigH f m β α₁ ∘ σ := by
    funext i
    have := congrFun ((huniq _).2 rfl) (σ i)
    simpa [Matrix.mulVec, dotProduct, Matrix.submatrix_apply] using this
  -- "and by Cramer's rule `b = det G_α / det G`"
  refine ⟨σ, hσ, hdet, ?_⟩
  have := cramer_coord hdet hsol (Sum.inl ())
  rw [lineJ_alpha] at this
  exact this

/-- `s y` is an integer of absolute value at most `X`. -/
def IntLe (s X y : ℝ) : Prop := ∃ k : ℤ, s * y = k ∧ |(k : ℝ)| ≤ X

/-- `s y` is an integer of absolute value less than `X`. -/
def IntLt (s X y : ℝ) : Prop := ∃ k : ℤ, s * y = k ∧ |(k : ℝ)| < X

lemma IntLt.intLe {s X y : ℝ} (h : IntLt s X y) : IntLe s X y :=
  let ⟨k, hk, hkX⟩ := h
  ⟨k, hk, hkX.le⟩

lemma intLt_zero {s X : ℝ} (hX : 0 < X) : IntLt s X 0 := ⟨0, by simp, by simpa using hX⟩

lemma intLt_ite {s X y : ℝ} {p : Prop} [Decidable p] (hX : 0 < X) (h : IntLt s X y) :
    IntLt s X (if p then y else 0) := by
  split_ifs
  · exact h
  · exact intLt_zero hX

omit [DecidableEq E] in
lemma intLt_vec {s X : ℝ} {a : ℝ} {x : E → ℝ} {r : Fin (nb f m β α₁) → ℝ} (ha : IntLt s X a)
    (hx : ∀ e, IntLt s X (x e)) (hr : ∀ j, IntLt s X (r j)) (c : Col f m β α₁) :
    IntLt s X (vec f m β α₁ a x r c) := by
  rcases c with ⟨⟩ | e | j
  · exact ha
  · exact hx e
  · exact hr j

lemma abs_mul_lt_four_pow {ν : ℕ} {x y : ℝ} (hx : |x| < 2 ^ ν) (hy : |y| < 2 ^ ν) :
    |x * y| < 4 ^ ν := by
  rw [abs_mul, show (4 : ℝ) ^ ν = 2 ^ ν * 2 ^ ν by rw [← mul_pow]; norm_num]
  exact mul_lt_mul'' hx hy (abs_nonneg _) (abs_nonneg _)

/-- **(3)**, the rows of the equations of a state (`appB-bitlength.tex:80-85`): "Every equation
contains at most two of the numbers `m_e`, `β_e`, or one value of `f` on its right-hand side, and
its other coefficients lie in `{0, ±1}`." Multiplying it by the product `s` of the denominators of
these numbers turns its coefficients and its right-hand side into integers of absolute value less
than `4^ν` (here `ν ≥ 1`, as `1 ≤ n ≤ ν`). -/
lemma rows_integral {ν : ℕ} (hν : 1 ≤ ν) (hm : ∀ e, IsSmall ν (m e))
    (hβs : ∀ e, IsSmall ν (β e)) (hfs : ∀ S, IsSmall ν (f S)) (r : Row f m β α₁) :
    ∃ s : ℝ, s ≠ 0 ∧ (∀ c, IntLt s (4 ^ ν) (eqG f m β α₁ r c)) ∧
      IntLt s (4 ^ ν) (eqH f m β α₁ r) := by
  have h1 : (1 : ℝ) < 4 ^ ν := one_lt_pow₀ (by norm_num) (by omega)
  have h0 : (0 : ℝ) < 4 ^ ν := by positivity
  have h24 : (2 : ℝ) ^ ν ≤ 4 ^ ν := pow_le_pow_left₀ (by norm_num) (by norm_num) ν
  have hone : IntLt 1 (4 ^ ν) 1 := ⟨1, by simp, by simpa using h1⟩
  rcases r with e | e | j
  · obtain ⟨a, d, hd, ha, hd', hme⟩ := hm e
    obtain ⟨a', d', hd2, ha', hd2', hβe⟩ := hβs e
    have hdr : (d : ℝ) ≠ 0 := Int.cast_ne_zero.2 hd
    have hdr' : (d' : ℝ) ≠ 0 := Int.cast_ne_zero.2 hd2
    -- `-m_e`, `β_e` and `1` times `d d'`
    have hmI : IntLt (d * d') (4 ^ ν) (-m e) := ⟨-(a * d'), by rw [hme]; push_cast; field_simp,
      by push_cast; rw [abs_neg]; exact abs_mul_lt_four_pow ha hd2'⟩
    have hβI : IntLt (d * d') (4 ^ ν) (β e) := ⟨a' * d, by rw [hβe]; push_cast; field_simp,
      by push_cast; exact abs_mul_lt_four_pow ha' hd'⟩
    have hoI : IntLt (d * d') (4 ^ ν) 1 := ⟨d * d', by push_cast; ring,
      by push_cast; exact abs_mul_lt_four_pow hd' hd2'⟩
    by_cases hfree : e ∈ freeSet f m β α₁
    · -- `β_e x_e − m_e α = 0`
      refine ⟨d * d', mul_ne_zero hdr hdr', fun c => ?_, intLt_zero h0⟩
      show IntLt _ _ (rowE f m β α₁ e c)
      rw [rowE, ite_eq_left hfree]
      exact intLt_vec hmI (fun e' => intLt_ite h0 hβI) (fun _ => intLt_zero h0) c
    · by_cases hzero : e ∈ zeroSet f m β α₁
      · -- `x_e = 0`
        refine ⟨1, one_ne_zero, fun c => ?_, intLt_zero h0⟩
        show IntLt _ _ (rowE f m β α₁ e c)
        rw [rowE, ite_eq_right hfree, ite_eq_left hzero]
        exact intLt_vec (intLt_zero h0) (fun e' => intLt_ite h0 hone) (fun _ => intLt_zero h0) c
      · -- `β_e x_e + ρ_j − m_e α = 0`
        refine ⟨d * d', mul_ne_zero hdr hdr', fun c => ?_, intLt_zero h0⟩
        show IntLt _ _ (rowE f m β α₁ e c)
        rw [rowE, ite_eq_right hfree, ite_eq_right hzero]
        exact intLt_vec hmI (fun e' => intLt_ite h0 hβI) (fun _ => intLt_ite h0 hoI) c
  · -- `ρ_j − m_e α = 0`
    obtain ⟨a, d, hd, ha, hd', hme⟩ := hm e
    have hdr : (d : ℝ) ≠ 0 := Int.cast_ne_zero.2 hd
    refine ⟨d, hdr, fun c => ?_, intLt_zero h0⟩
    show IntLt _ _ (rowZ f m β α₁ e c)
    have hmI : IntLt d (4 ^ ν) (-m e) := ⟨-a, by rw [hme]; push_cast; field_simp,
      by push_cast; rw [abs_neg]; exact ha.trans_le h24⟩
    have hoI : IntLt d (4 ^ ν) 1 := ⟨d, by ring, hd'.trans_le h24⟩
    exact intLt_vec hmI (fun _ => intLt_zero h0) (fun _ => intLt_ite h0 hoI) c
  · -- `x(S_j) = f(S_j)`
    obtain ⟨a, d, hd, ha, hd', hfe⟩ := hfs (cumS f m β α₁ j)
    have hdr : (d : ℝ) ≠ 0 := Int.cast_ne_zero.2 hd
    have hoI : IntLt d (4 ^ ν) 1 := ⟨d, by ring, hd'.trans_le h24⟩
    refine ⟨d, hdr, fun c => ?_, ⟨a, ?_, ha.trans_le h24⟩⟩
    · show IntLt _ _ (rowS f m β α₁ j c)
      exact intLt_vec (intLt_zero h0) (fun _ => intLt_ite h0 hoI) (fun _ => intLt_zero h0) c
    · show (d : ℝ) * f (cumS f m β α₁ j) = a
      rw [hfe]
      field_simp

/-- **(3)**, the rows of the system of (2) (`rows_integral`, and the extra equation, with
coefficients in `{0, ±1}` and right-hand side `0`, needs no factor). -/
lemma rows_integral_big {ν : ℕ} (hν : 1 ≤ ν) (hm : ∀ e, IsSmall ν (m e))
    (hβs : ∀ e, IsSmall ν (β e)) (hfs : ∀ S, IsSmall ν (f S)) (ex : Col f m β α₁ → ℝ)
    (hex : ∀ c, ∃ k : ℤ, ex c = k ∧ |k| ≤ 1) (r : Option (Row f m β α₁)) :
    ∃ s : ℝ, s ≠ 0 ∧ (∀ c, IntLt s (4 ^ ν) (bigG f m β α₁ ex r c)) ∧
      IntLt s (4 ^ ν) (bigH f m β α₁ r) := by
  have h1 : (1 : ℝ) < 4 ^ ν := one_lt_pow₀ (by norm_num) (by omega)
  rcases r with _ | r
  · refine ⟨1, one_ne_zero, fun c => ?_, intLt_zero (by positivity)⟩
    obtain ⟨k, hk, hk1⟩ := hex c
    refine ⟨k, ?_, ?_⟩
    · show 1 * ex c = k
      rw [hk, one_mul]
    · have : |(k : ℝ)| ≤ 1 := by exact_mod_cast hk1
      linarith
  · exact rows_integral hν hm hβs hfs r

/-- **(3)**, the determinants (`appB-bitlength.tex:82-88`): "Multiplying each equation by the
product of the denominators of these numbers multiplies `det G` and `det G_α` by the same nonzero
factor, and turns `G` and `G_α` into integer matrices whose entries have absolute value less than
`4^ν`. By Hadamard's inequality, both determinants then have absolute value at most
`(√N 4^ν)^N`." Here for a square system `G z = h` whose rows become integral with entries of
absolute value at most `X` after multiplication with `s_i ≠ 0`. -/
theorem ratio_of_integral_rows {n : Type*} [Fintype n] [DecidableEq n] {G : Matrix n n ℝ}
    {h : n → ℝ} (hdet : G.det ≠ 0) {s : n → ℝ} (hs : ∀ i, s i ≠ 0) {X : ℝ} (hX : 0 ≤ X)
    (hG : ∀ i j, IntLe (s i) X (G i j)) (hh : ∀ i, IntLe (s i) X (h i)) (c : n) :
    ∃ p q : ℤ, q ≠ 0 ∧ (G.updateCol c h).det / G.det = p / q ∧
      |(p : ℝ)| ≤ (Real.sqrt (Fintype.card n) * X) ^ Fintype.card n ∧
      |(q : ℝ)| ≤ (Real.sqrt (Fintype.card n) * X) ^ Fintype.card n := by
  choose Gk hGk hGkX using hG
  choose hk hhk hhkX using hh
  -- the integer matrices
  set Gi : Matrix n n ℤ := Matrix.of fun i j => Gk i j
  set Hi : Matrix n n ℤ := Gi.updateCol c hk
  have hGi : Gi.map (Int.cast : ℤ → ℝ) = Matrix.diagonal s * G := by
    ext i j
    simp [Gi, Matrix.diagonal_mul, hGk]
  have hHi : Hi.map (Int.cast : ℤ → ℝ) =
      (Matrix.diagonal s * G).updateCol c (fun i => s i * h i) := by
    ext i j
    by_cases hj : j = c
    · subst hj
      simp [Hi, hhk]
    · simp [Hi, Gi, Matrix.updateCol_ne hj, Matrix.diagonal_mul, hGk]
  have hcast : ∀ A : Matrix n n ℤ, (A.det : ℝ) = (A.map (Int.cast : ℤ → ℝ)).det := fun A => by
    have := (Int.castRingHom ℝ).map_det A
    simpa using this
  obtain ⟨hdG, hdH⟩ := det_diagonal_mul s G h c
  have hprod : (∏ i, s i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hs i
  refine ⟨Hi.det, Gi.det, ?_, ?_, ?_, ?_⟩
  · intro h0
    have : ((Gi.det : ℤ) : ℝ) = 0 := by rw [h0, Int.cast_zero]
    rw [hcast, hGi, hdG] at this
    exact mul_ne_zero hprod hdet this
  · rw [hcast Hi, hcast Gi, hHi, hGi, hdG, hdH]
    field_simp
  · rw [hcast]
    refine abs_det_le _ hX fun i j => ?_
    by_cases hj : j = c
    · subst hj
      simpa [Hi] using hhkX i
    · simpa [Hi, Gi, Matrix.updateCol_ne hj] using hGkX i j
  · rw [hcast]
    exact abs_det_le _ hX fun i j => by simpa [Gi] using hGkX i j

/-- (3): "`(√N 4^ν)^N ≤ Q`" for `N ≤ 2n + 1`. -/
lemma hadamard_le_bigQ {n N ν : ℕ} (hN : N ≤ 2 * n + 1) :
    (Real.sqrt N * 4 ^ ν) ^ N ≤ bigQ n ν := by
  have h4 : (1 : ℝ) ≤ ((4 : ℝ) ^ ν) ^ 2 := one_le_pow₀ (one_le_pow₀ (by norm_num))
  have hn : (1 : ℝ) ≤ 2 * n + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hb : (1 : ℝ) ≤ (2 * n + 1 : ℝ) * ((4 : ℝ) ^ ν) ^ 2 := by nlinarith
  have hsq : ((Real.sqrt N * 4 ^ ν) ^ N) ^ 2 = ((N : ℝ) * ((4 : ℝ) ^ ν) ^ 2) ^ N := by
    rw [← pow_mul, mul_comm N 2, pow_mul, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hle : ((N : ℝ) * ((4 : ℝ) ^ ν) ^ 2) ^ N ≤ (bigQ n ν : ℝ) ^ 2 := by
    calc ((N : ℝ) * ((4 : ℝ) ^ ν) ^ 2) ^ N ≤ ((2 * n + 1 : ℝ) * ((4 : ℝ) ^ ν) ^ 2) ^ N := by
          gcongr
          exact_mod_cast hN
      _ ≤ ((2 * n + 1 : ℝ) * ((4 : ℝ) ^ ν) ^ 2) ^ (2 * n + 1) := pow_le_pow_right₀ hb hN
      _ = (2 * n + 1 : ℝ) ^ (2 * n + 1) * ((4 : ℝ) ^ ((2 * n + 1) * ν)) ^ 2 := by
          rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
          ring_nf
      _ ≤ (2 * n + 1 : ℝ) ^ (2 * n + 2) * ((4 : ℝ) ^ ((2 * n + 1) * ν)) ^ 2 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hn (by omega)) (by positivity)
      _ = (bigQ n ν : ℝ) ^ 2 := by
          simp only [bigQ]
          push_cast
          ring
  rw [← hsq] at hle
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hle

omit [DecidableEq E] in
/-- A breakpoint needs an element: with no elements, `x*` is constant (plumbing). -/
lemma card_pos_of_mem_breakpoints {b : ℝ} (hb : b ∈ breakpoints (bestResponse f m β)) :
    0 < Fintype.card E := by
  by_contra h
  have : IsEmpty E := Fintype.card_eq_zero_iff.1 (by omega)
  exact hb.2 ⟨1, one_pos, 0, 0, fun α _ => funext fun e => isEmptyElim e⟩

/-- **(2) and (3)** of the proof of `thm:bitlength` (`stoc-sections/appB-bitlength.tex:53-90`):
every breakpoint `b` is a quotient of two integers of absolute value at most `Q` (with the
hypothesis `n ≤ ν` of the theorem, which gives `ν ≥ 1`). "The equations
depend only on the state on `J` and on the data, not on the breakpoints before `b`, so this bound
holds for every breakpoint." -/
theorem breakpoint_ratio (H : Tracing.Hyp f m β) {ν : ℕ} (hm : ∀ e, IsSmall ν (m e))
    (hβs : ∀ e, IsSmall ν (β e)) (hfs : ∀ S, IsSmall ν (f S)) (hnν : Fintype.card E ≤ ν)
    {b : ℝ} (hb : b ∈ breakpoints (bestResponse f m β)) :
    ∃ p q : ℤ, q ≠ 0 ∧ b = p / q ∧ |p| ≤ bigQ (Fintype.card E) ν ∧
      |q| ≤ bigQ (Fintype.card E) ν := by
  have hν : 1 ≤ ν := (card_pos_of_mem_breakpoints hb).trans_le hnν
  -- (2) "Next we single out a breakpoint by one more equation": the interval `J`, the equation
  -- of `b`, the square system and Cramer's rule
  obtain ⟨lo, hi, α₁, hlo, hS, hα₁, hbJ, ex, hexint, hex⟩ := step2_equation H hb
  obtain ⟨-, -, σ, -, hdet, hbG⟩ := step2_cramer H hlo hS hα₁ hbJ ex hex
  -- (3) "Next we bound the size of `b`": the rows become integral, and Hadamard's inequality
  choose s hs hG hh using rows_integral_big hν hm hβs hfs ex hexint
  obtain ⟨p, q, hq, hpq, hp, hqb⟩ := ratio_of_integral_rows (s := fun i => s (σ i)) hdet
    (fun i => hs (σ i)) (by positivity) (fun i j => (hG (σ i) j).intLe) (fun i => (hh (σ i)).intLe)
    (Sum.inl ())
  have hQ := hadamard_le_bigQ (ν := ν) (card_col_le (f := f) (m := m) (β := β) (α₁ := α₁))
  refine ⟨p, q, hq, hbG.trans hpq, ?_, ?_⟩
  · have : |(p : ℝ)| ≤ (bigQ (Fintype.card E) ν : ℝ) := hp.trans hQ
    exact_mod_cast this
  · have : |(q : ℝ)| ≤ (bigQ (Fintype.card E) ν : ℝ) := hqb.trans hQ
    exact_mod_cast this

end Size

/-! ### (4) An optimal contract -/

section Share

variable {E : Type*} [Fintype E] [DecidableEq E] {f : Finset E → ℝ} {m β : E → ℝ}

/-- (4): "Let `J` be an open interval with constant state in the interior of a piece `I`" (not in
the paper: the STOC version does not say why such an interval exists). It exists, as there are
finitely many event points ((1), (a)): below the first event point in the interior of the piece,
the state is constant (`state_eq_of_no_event`). Here the piece is `I = [a, c]`. -/
lemma exists_J_in_piece (H : Tracing.Hyp f m β) {a c : ℝ} (hp : Tracing.IsPiece f m β a c) :
    ∃ lo hi α₁ : ℝ, a ≤ lo ∧ hi ≤ c ∧ 0 ≤ lo ∧
      (∀ α ∈ Set.Ioo lo hi, ∀ α' ∈ Set.Ioo lo hi, state f m β α = state f m β α') ∧
      α₁ ∈ Set.Ioo lo hi := by
  classical
  set T := (events_finite H).toFinset.filter fun x => a < x ∧ x < c
  set hi := (insert c T).min' (Finset.insert_nonempty _ _)
  have hhic : hi ≤ c := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  have hahi : a < hi := (Finset.lt_min'_iff _ _).2 fun y hy => by
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hp.2.1
    · exact (Finset.mem_filter.1 hy).2.1
  have hno : ∀ α ∈ Set.Ioo a hi, ¬ Tracing.IsEvent f m β α := fun α hα hev => by
    have hαT : α ∈ insert c T := Finset.mem_insert_of_mem (Finset.mem_filter.2
      ⟨(Set.Finite.mem_toFinset _).2 hev, hα.1, hα.2.trans_le hhic⟩)
    exact absurd (Finset.min'_le _ _ hαT) (not_le.2 hα.2)
  exact ⟨a, hi, (a + hi) / 2, le_rfl, hhic, hp.1, state_eq_of_no_event hp.1 hno,
    ⟨by linarith, by linarith⟩⟩

/-- (4): "Then the affine extension `x^J` above is the affine form of `x*` on `I`" (not in the
paper: the STOC version states this without proof). `x*` is affine on the piece `I = [a, c]`
(`Stoc.Tracing.affine_on_piece`), and the two affine maps agree on `J`. -/
lemma xJ_eq_on_piece (H : Tracing.Hyp f m β) {a c lo hi α₁ : ℝ} (hp : Tracing.IsPiece f m β a c)
    (hal : a ≤ lo) (hhc : hi ≤ c) (hlo : 0 ≤ lo)
    (hS : ∀ α ∈ Set.Ioo lo hi, ∀ α' ∈ Set.Ioo lo hi, state f m β α = state f m β α')
    (hα₁ : α₁ ∈ Set.Ioo lo hi) :
    ∀ α ∈ Set.Icc a c, bestResponse f m β α = xJ f m β α₁ α := by
  obtain ⟨p, w, hpw⟩ := Tracing.affine_on_piece H hp
  have hJ : ∀ α ∈ Set.Ioo lo hi, bestResponse f m β α = xJ f m β α₁ α := fun α hα => by
    have := congrArg (fun z => fun e => z (Sum.inr (Sum.inl e)))
      (lineJ_eq_solJ H hlo hS hα₁ hα)
    simpa [lineJ, solJ, vec] using this.symm
  set α₂ := (α₁ + hi) / 2
  have hα₂ : α₂ ∈ Set.Ioo lo hi := ⟨by simp only [α₂]; linarith [hα₁.1, hα₁.2],
    by simp only [α₂]; linarith [hα₁.2]⟩
  have hne : α₁ ≠ α₂ := by simp only [α₂]; intro h; linarith [hα₁.2]
  have hsub : ∀ γ ∈ Set.Ioo lo hi, γ ∈ Set.Icc a c := fun γ hγ =>
    ⟨hal.trans hγ.1.le, hγ.2.le.trans hhc⟩
  intro α hα
  funext e
  have e1 := congrFun ((hpw α₁ (hsub α₁ hα₁)).symm.trans (hJ α₁ hα₁)) e
  have e2 := congrFun ((hpw α₂ (hsub α₂ hα₂)).symm.trans (hJ α₂ hα₂)) e
  simp only [xJ] at e1 e2 ⊢
  have hw : w e = velocity f m β α₁ e := by
    have : (α₁ - α₂) * (w e - velocity f m β α₁ e) = 0 := by linarith
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne))
  rw [hpw α hα]
  simp only
  rw [hw] at e1 ⊢
  linarith

/-- (4), the linear algebra: "We scale them as above, move the terms with `α` to the right-hand
side and apply Cramer's rule." For a square system `G y = h − α g` whose rows become
integral, with entries of absolute value at most `X`, after multiplication with `s_i ≠ 0`, the
solution is `y_c = (u_c + α v_c)/ζ` with integers `u_c`, `v_c` and `ζ ≠ 0` of absolute value at
most `(√N X)^N` (Hadamard's inequality, `abs_det_le`). -/
theorem affine_ratio_of_integral_rows {n : Type*} [Fintype n] [DecidableEq n] {G : Matrix n n ℝ}
    {h g : n → ℝ} (hdet : G.det ≠ 0) {s : n → ℝ} (hs : ∀ i, s i ≠ 0) {X : ℝ} (hX : 0 ≤ X)
    (hG : ∀ i j, IntLe (s i) X (G i j)) (hh : ∀ i, IntLe (s i) X (h i))
    (hg : ∀ i, IntLe (s i) X (g i)) :
    ∃ ζ : ℤ, ζ ≠ 0 ∧ |(ζ : ℝ)| ≤ (Real.sqrt (Fintype.card n) * X) ^ Fintype.card n ∧
      ∀ c, ∃ u v : ℤ, |(u : ℝ)| ≤ (Real.sqrt (Fintype.card n) * X) ^ Fintype.card n ∧
        |(v : ℝ)| ≤ (Real.sqrt (Fintype.card n) * X) ^ Fintype.card n ∧
        ∀ (α : ℝ) (y : n → ℝ), G *ᵥ y = h - α • g → y c = (u + α * v) / ζ := by
  choose Gk hGk hGkX using hG
  choose hk hhk hhkX using hh
  choose gk hgk hgkX using hg
  set Gi : Matrix n n ℤ := Matrix.of fun i j => Gk i j
  have hGi : Gi.map (Int.cast : ℤ → ℝ) = Matrix.diagonal s * G := by
    ext i j
    simp [Gi, Matrix.diagonal_mul, hGk]
  have hcol : ∀ (c : n) (r : n → ℤ) (t : n → ℝ), (∀ i, s i * t i = r i) →
      (Gi.updateCol c r).map (Int.cast : ℤ → ℝ) =
        (Matrix.diagonal s * G).updateCol c (fun i => s i * t i) := by
    intro c r t hrt
    ext i j
    by_cases hj : j = c
    · subst hj
      simp [hrt]
    · simp [Gi, Matrix.updateCol_ne hj, Matrix.diagonal_mul, hGk]
  have hcast : ∀ A : Matrix n n ℤ, (A.det : ℝ) = (A.map (Int.cast : ℤ → ℝ)).det := fun A => by
    have := (Int.castRingHom ℝ).map_det A
    simpa using this
  have hprod : (∏ i, s i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hs i
  have hζ : (Gi.det : ℝ) = (∏ i, s i) * G.det := by
    rw [hcast, hGi, Matrix.det_mul, Matrix.det_diagonal]
  have hbound : ∀ c (r : n → ℤ), (∀ i, |(r i : ℝ)| ≤ X) →
      |((Gi.updateCol c r).det : ℝ)| ≤ (Real.sqrt (Fintype.card n) * X) ^ Fintype.card n := by
    intro c r hr
    rw [hcast]
    refine abs_det_le _ hX fun i j => ?_
    by_cases hj : j = c
    · subst hj
      simpa using hr i
    · simpa [Gi, Matrix.updateCol_ne hj] using hGkX i j
  refine ⟨Gi.det, fun h0 => ?_, ?_, fun c => ?_⟩
  · have : ((Gi.det : ℤ) : ℝ) = 0 := by rw [h0, Int.cast_zero]
    rw [hζ] at this
    exact mul_ne_zero hprod hdet this
  · rw [hcast]
    exact abs_det_le _ hX fun i j => by simpa [Gi] using hGkX i j
  · refine ⟨(Gi.updateCol c hk).det, -(Gi.updateCol c gk).det, hbound c hk hhkX, ?_,
      fun α y hy => ?_⟩
    · rw [Int.cast_neg, abs_neg]
      exact hbound c gk hgkX
    · -- Cramer's rule, with the right-hand side `h − α g`, linear in `α`
      have hu : ((Gi.updateCol c hk).det : ℝ) = (∏ i, s i) * (G.updateCol c h).det := by
        rw [hcast, hcol c hk h hhk, (det_diagonal_mul s G h c).2]
      have hv : ((Gi.updateCol c gk).det : ℝ) = (∏ i, s i) * (G.updateCol c g).det := by
        rw [hcast, hcol c gk g hgk, (det_diagonal_mul s G g c).2]
      have hlin : (G.updateCol c (h - α • g)).det =
          (G.updateCol c h).det - α * (G.updateCol c g).det := by
        rw [sub_eq_add_neg, Matrix.det_updateCol_add, ← neg_smul, Matrix.det_updateCol_smul]
        ring
      rw [cramer_coord hdet hy c, hlin, Int.cast_neg, hu, hv, hζ]
      field_simp
      ring

/-- **(4)** (`appB-bitlength.tex:94-98`), for an open interval `J = (lo, hi) ∋ α₁` with constant
state: "As the equations of `J` determine `x` and `ρ` for fixed `α`, some `n + k` of them have a
nonsingular matrix in the columns of `(x, ρ)`. We scale them as above, move the terms with `α` to
the right-hand side and apply Cramer's rule. This gives `x*_e(α) = (u_e + α v_e)/ζ` on the piece,
with integers `u_e`, `v_e` and `ζ ≠ 0` of absolute value at most `Q`", here for the affine
extension `x^J` of `x*` from `J`. -/
theorem step4_cramer (H : Tracing.Hyp f m β) {ν : ℕ} (hν : 1 ≤ ν) (hm : ∀ e, IsSmall ν (m e))
    (hβs : ∀ e, IsSmall ν (β e)) (hfs : ∀ S, IsSmall ν (f S)) {lo hi α₁ : ℝ} (hlo : 0 ≤ lo)
    (hS : ∀ α ∈ Set.Ioo lo hi, ∀ α' ∈ Set.Ioo lo hi, state f m β α = state f m β α')
    (hα₁ : α₁ ∈ Set.Ioo lo hi) :
    ∃ ζ : ℤ, ζ ≠ 0 ∧ |ζ| ≤ bigQ (Fintype.card E) ν ∧ ∀ e, ∃ u v : ℤ,
      |u| ≤ bigQ (Fintype.card E) ν ∧ |v| ≤ bigQ (Fintype.card E) ν ∧
      ∀ α, xJ f m β α₁ α e = (u + α * v) / ζ := by
  -- the columns of `(x, ρ)` and the column of `α`
  set G₀ : Matrix (Row f m β α₁) (E ⊕ Fin (nb f m β α₁)) ℝ :=
    Matrix.of fun r c => eqG f m β α₁ r (Sum.inr c)
  have hsplit : ∀ (z : Col f m β α₁ → ℝ) (r : Row f m β α₁), (eqG f m β α₁ *ᵥ z) r =
      eqG f m β α₁ r (Sum.inl ()) * z (Sum.inl ()) + (G₀ *ᵥ fun c => z (Sum.inr c)) r := by
    intro z r
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Finset.univ_unique,
      Finset.sum_singleton, G₀, Matrix.of_apply]
  -- "As the equations of `J` determine `x` and `ρ` for fixed `α` (`determined`), some `n + k` of
  -- them have a nonsingular matrix in the columns of `(x, ρ)`": the homogeneous system in these
  -- columns has only the zero solution.
  have hker : ∀ y, G₀ *ᵥ y = 0 → y = 0 := by
    intro y hy
    set z : Col f m β α₁ → ℝ := lineJ f m β α₁ α₁ + Sum.elim (fun _ => 0) y
    have hz : eqG f m β α₁ *ᵥ z = eqH f m β α₁ := by
      have h1 := (solves_iff_line H hlo hS hα₁ (lineJ f m β α₁ α₁)).2 ⟨α₁, rfl⟩
      rw [Matrix.mulVec_add, h1]
      funext r
      rw [Pi.add_apply, hsplit]
      have : (fun c => (Sum.elim (fun _ => 0) y : Col f m β α₁ → ℝ) (Sum.inr c)) = y := rfl
      rw [this, hy]
      simp
    have := determined H (rho_nonneg H (hlo.trans hα₁.1.le)) hz
      ((solves_iff_line H hlo hS hα₁ (lineJ f m β α₁ α₁)).2 ⟨α₁, rfl⟩) (by simp [z, lineJ_alpha])
    funext c
    have hc := congrFun this (Sum.inr c)
    simp only [z, Pi.add_apply, Sum.elim_inr, add_eq_left] at hc
    exact hc
  obtain ⟨σ, -, hdet⟩ := exists_square_subsystem G₀ hker
  -- the square system `G y = h − α g` along the line
  set G := G₀.submatrix σ id
  set h₀ : E ⊕ Fin (nb f m β α₁) → ℝ := fun i => eqH f m β α₁ (σ i)
  set g₀ : E ⊕ Fin (nb f m β α₁) → ℝ := fun i => eqG f m β α₁ (σ i) (Sum.inl ())
  have hsys : ∀ α, G *ᵥ (fun c => lineJ f m β α₁ α (Sum.inr c)) = h₀ - α • g₀ := by
    intro α
    funext i
    have h1 := congrFun ((solves_iff_line H hlo hS hα₁ (lineJ f m β α₁ α)).2 ⟨α, rfl⟩) (σ i)
    rw [hsplit, lineJ_alpha] at h1
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h₀, g₀]
    have : (G *ᵥ fun c => lineJ f m β α₁ α (Sum.inr c)) i =
        (G₀ *ᵥ fun c => lineJ f m β α₁ α (Sum.inr c)) (σ i) := rfl
    rw [this]
    linarith
  -- "We scale them as above"
  choose s hs hG hh using rows_integral (α₁ := α₁) hν hm hβs hfs
  obtain ⟨ζ, hζ, hζb, huv⟩ := affine_ratio_of_integral_rows (s := fun i => s (σ i)) hdet
    (fun i => hs (σ i)) (by positivity) (fun i j => (hG (σ i) (Sum.inr j)).intLe)
    (fun i => (hh (σ i)).intLe) (fun i => (hG (σ i) (Sum.inl ())).intLe)
  have hcard : Fintype.card (E ⊕ Fin (nb f m β α₁)) ≤ 2 * Fintype.card E + 1 := by
    have := card_col_le (f := f) (m := m) (β := β) (α₁ := α₁)
    simp only [Fintype.card_sum, Fintype.card_unit] at this ⊢
    omega
  have hQ := hadamard_le_bigQ (ν := ν) hcard
  have hint : ∀ k : ℤ, |(k : ℝ)| ≤ (Real.sqrt (Fintype.card (E ⊕ Fin (nb f m β α₁))) * 4 ^ ν) ^
      Fintype.card (E ⊕ Fin (nb f m β α₁)) → |k| ≤ bigQ (Fintype.card E) ν := fun k hk => by
    have : |(k : ℝ)| ≤ (bigQ (Fintype.card E) ν : ℝ) := hk.trans hQ
    exact_mod_cast this
  refine ⟨ζ, hζ, hint ζ hζb, fun e => ?_⟩
  obtain ⟨u, v, hu, hv, hy⟩ := huv (Sum.inl e)
  exact ⟨u, v, hint u hu, hint v hv, fun α => hy α _ (hsys α)⟩

lemma abs_prod_erase_le {ν : ℕ} {q : E → ℤ} (hq : ∀ e, |(q e : ℝ)| < 2 ^ ν) (e : E) :
    |∏ g ∈ Finset.univ.erase e, (q g : ℝ)| ≤ (2 ^ ν) ^ (Fintype.card E - 1) := by
  rw [Finset.abs_prod]
  calc ∏ g ∈ Finset.univ.erase e, |(q g : ℝ)| ≤ ∏ _g ∈ Finset.univ.erase e, (2 : ℝ) ^ ν :=
        Finset.prod_le_prod₀ (fun g _ => abs_nonneg _) fun g _ => (hq g).le
    _ = (2 ^ ν) ^ (Fintype.card E - 1) := by
        rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ e), Finset.card_univ]

/-- (4) (`appB-bitlength.tex:98-104`): "Writing `m_e = a_e/ā_e` with integers `a_e` and `ā_e > 0`,
`|a_e|, ā_e < 2^ν`, the reward on `I` is `r⁰_I + r¹_I α`, in the notation after `lem:pwaffine`,
where `r⁰_I = P/(ζ ∏_{e∈E} ā_e)` and `r¹_I = P'/(ζ ∏_{e∈E} ā_e)` with
`P := ∑_{e∈E} a_e u_e ∏_{e'≠e} ā_{e'}` and `P' := ∑_{e∈E} a_e v_e ∏_{e'≠e} ā_{e'}`, and the
integers `P`, `P'` and `ζ ∏_{e∈E} ā_e` have absolute value at most `nQ2^{nν}`." Here for
`x(α)_e = (u_e + α v_e)/ζ` with `|u_e|, |v_e|, |ζ| ≤ Q` (the affine form `x^J` of `x*` on `I`, by
`step4_cramer`): `|ζ ∏_e ā_e| ≤ |ζ| (2^ν)^n ≤ nQ2^{nν}`, and `P`, `P'` are bounded termwise. -/
lemma reward_ratio {ν : ℕ} (hm : ∀ e, IsSmall ν (m e)) (hn : 0 < Fintype.card E) {Q : ℕ}
    {ζ : ℤ} (hζ : ζ ≠ 0) (hζQ : |ζ| ≤ Q) {u v : E → ℤ} (hu : ∀ e, |u e| ≤ Q)
    (hv : ∀ e, |v e| ≤ Q) {x : ℝ → E → ℝ} (hx : ∀ α e, x α e = (u e + α * v e) / ζ) :
    ∃ a ab : E → ℤ, (∀ e, 0 < ab e ∧ |(a e : ℝ)| < 2 ^ ν ∧ |(ab e : ℝ)| < 2 ^ ν ∧
        m e = a e / ab e) ∧
      ∃ P P' : ℤ, P = ∑ e, a e * u e * ∏ e' ∈ univ.erase e, ab e' ∧
        P' = ∑ e, a e * v e * ∏ e' ∈ univ.erase e, ab e' ∧ ζ * ∏ e, ab e ≠ 0 ∧
        (∀ α, reward m (x α) =
          P / ((ζ * ∏ e, ab e : ℤ) : ℝ) + (P' / ((ζ * ∏ e, ab e : ℤ) : ℝ)) * α) ∧
        |ζ * ∏ e, ab e| ≤ Fintype.card E * Q * 2 ^ (Fintype.card E * ν) ∧
        |P| ≤ Fintype.card E * Q * 2 ^ (Fintype.card E * ν) ∧
        |P'| ≤ Fintype.card E * Q * 2 ^ (Fintype.card E * ν) := by
  classical
  -- "Writing `m_e = a_e/ā_e` with integers `a_e` and `ā_e > 0`, `|a_e|, ā_e < 2^ν`"
  have hfrac : ∀ e, ∃ a ab : ℤ, 0 < ab ∧ |(a : ℝ)| < 2 ^ ν ∧ |(ab : ℝ)| < 2 ^ ν ∧
      m e = a / ab := fun e => by
    obtain ⟨a, d, hd, ha, hd', hme⟩ := hm e
    rcases lt_or_gt_of_ne hd with hneg | hpos
    · refine ⟨-a, -d, by omega, by push_cast; rwa [abs_neg], by push_cast; rwa [abs_neg], ?_⟩
      rw [hme]
      push_cast
      rw [neg_div_neg_eq]
    · exact ⟨a, d, hpos, ha, hd', hme⟩
  choose a ab hab ha hab' hma using hfrac
  set n := Fintype.card E
  -- "`P := ∑_{e∈E} a_e u_e ∏_{e'≠e} ā_{e'}` and `P' := ∑_{e∈E} a_e v_e ∏_{e'≠e} ā_{e'}`", with
  -- `R_e = ∏_{e'≠e} ā_{e'}`
  set R : E → ℤ := fun e => ∏ g ∈ Finset.univ.erase e, ab g
  refine ⟨a, ab, fun e => ⟨hab e, ha e, hab' e, hma e⟩, ∑ e, a e * u e * R e,
    ∑ e, a e * v e * R e, rfl, rfl,
    mul_ne_zero hζ (Finset.prod_ne_zero_iff.2 fun g _ => (hab g).ne'), fun α => ?_, ?_, ?_⟩
  · -- "the reward on `I` is `r⁰_I + r¹_I α`, …, where `r⁰_I = P/(ζ ∏_{e∈E} ā_e)` and
    -- `r¹_I = P'/(ζ ∏_{e∈E} ā_e)`"
    have hK : (ζ : ℝ) * ∏ g, (ab g : ℝ) ≠ 0 :=
      mul_ne_zero (Int.cast_ne_zero.2 hζ) (Finset.prod_ne_zero_iff.2 fun g _ =>
        Int.cast_ne_zero.2 (hab g).ne')
    simp only [reward]
    push_cast
    rw [eq_comm, div_mul_eq_mul_div, ← add_div, div_eq_iff hK, Finset.sum_mul,
      Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hx α e, hma e,
      ← Finset.mul_prod_erase Finset.univ (fun g => (ab g : ℝ)) (Finset.mem_univ e)]
    have hq : (ab e : ℝ) ≠ 0 := Int.cast_ne_zero.2 (hab e).ne'
    have hζ' : (ζ : ℝ) ≠ 0 := Int.cast_ne_zero.2 hζ
    have hRe : (R e : ℝ) = ∏ x ∈ Finset.univ.erase e, (ab x : ℝ) := by simp [R]
    rw [hRe]
    field_simp
  · -- "and the integers `P`, `P'` and `ζ ∏_{e∈E} ā_e` have absolute value at most `nQ2^{nν}`":
    -- `|ζ ∏_e ā_e| ≤ |ζ| (2^ν)^n ≤ Q 2^{nν} ≤ nQ2^{nν}`
    have hreal : |(ζ : ℝ) * ∏ g, (ab g : ℝ)| ≤ n * Q * 2 ^ (n * ν) := by
      have hζ' : |(ζ : ℝ)| ≤ Q := by exact_mod_cast hζQ
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      rw [abs_mul, Finset.abs_prod]
      calc |(ζ : ℝ)| * ∏ g, |(ab g : ℝ)| ≤ Q * ∏ _g : E, (2 : ℝ) ^ ν := by
            gcongr with g
            exact (hab' g).le
        _ = Q * 2 ^ (n * ν) := by
            rw [Finset.prod_const, Finset.card_univ, ← pow_mul, mul_comm ν]
        _ ≤ n * Q * 2 ^ (n * ν) := by
            nlinarith [show (0 : ℝ) ≤ Q * 2 ^ (n * ν) by positivity]
    have : ((|ζ * ∏ g, ab g| : ℤ) : ℝ) ≤ ((n * Q * 2 ^ (n * ν) : ℕ) : ℝ) := by
      push_cast
      exact hreal
    exact_mod_cast this
  -- and `P`, `P'`, termwise: `|a_e u_e R_e| ≤ 2^ν Q (2^ν)^{n−1}`
  have hR : ∀ e, |(R e : ℝ)| ≤ (2 ^ ν) ^ (n - 1) := fun e => by
    simpa [R] using abs_prod_erase_le hab' e
  have hterm : ∀ (W : E → ℤ), (∀ e, |W e| ≤ Q) →
      |∑ e, a e * W e * R e| ≤ n * Q * 2 ^ (n * ν) := by
    intro W hW
    have hreal : |(∑ e, a e * W e * R e : ℝ)| ≤ n * Q * 2 ^ (n * ν) := by
      calc |(∑ e, (a e : ℝ) * W e * R e)| ≤ ∑ e, |(a e : ℝ) * W e * R e| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _e : E, (2 : ℝ) ^ ν * Q * (2 ^ ν) ^ (n - 1) := by
            refine Finset.sum_le_sum fun e _ => ?_
            rw [abs_mul, abs_mul]
            have hWe : |(W e : ℝ)| ≤ Q := by exact_mod_cast hW e
            gcongr
            · exact (ha e).le
            · exact hR e
        _ = n * Q * 2 ^ (n * ν) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            have : (2 : ℝ) ^ ν * (2 ^ ν) ^ (n - 1) = 2 ^ (n * ν) := by
              rw [← pow_succ', ← pow_mul, Nat.sub_add_cancel hn, mul_comm]
            rw [show (2 : ℝ) ^ ν * Q * (2 ^ ν) ^ (n - 1) =
              Q * ((2 : ℝ) ^ ν * (2 ^ ν) ^ (n - 1)) by ring, this]
            ring
    have : ((|∑ e, a e * W e * R e| : ℤ) : ℝ) ≤ ((n * Q * 2 ^ (n * ν) : ℕ) : ℝ) := by
      push_cast
      exact hreal
    exact_mod_cast this
  exact ⟨hterm u hu, hterm v hv⟩

/-- An optimal contract exists (not in the paper: the proof of `thm:bitlength` takes it for granted
in (4)): `U_P(α) = (1 − α) r(x*(α))` is continuous on `[0, 1]`, as `x*` is (`lem:pwaffine`), and
`[0, 1]` is compact. -/
lemma exists_optimal_share (H : Tracing.Hyp f m β) :
    ∃ αs ∈ Set.Icc (0 : ℝ) 1, ∀ α ∈ Set.Icc (0 : ℝ) 1,
      profit (grossValue f m β) α ≤ profit (grossValue f m β) αs := by
  have hx : ContinuousOn (bestResponse f m β) (Set.Icc 0 1) :=
    (pwaffine H).1.mono fun α hα => hα.1
  have hc : ContinuousOn (profit (grossValue f m β)) (Set.Icc 0 1) := by
    unfold profit grossValue reward
    have : ∀ e, ContinuousOn (fun α => bestResponse f m β α e) (Set.Icc 0 1) := fun e =>
      (continuous_apply e).comp_continuousOn hx
    exact (continuousOn_const.sub continuousOn_id).mul
      (continuousOn_finsetSum _ fun e _ => continuousOn_const.mul (this e))
  obtain ⟨αs, hαs, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 zero_le_one) hc
  exact ⟨αs, hαs, isMaxOn_iff.1 hmax⟩

end Share

/-! ### The bounds and the theorem -/

/-- `2 n Q 2^{nν}`, the bound of (4) on the numerator and the denominator of an optimal contract. -/
def bigQ' (n ν : ℕ) : ℕ := 2 * n * bigQ n ν * 2 ^ (n * ν)

lemma bigQ_pos (n ν : ℕ) : 0 < bigQ n ν := by
  unfold bigQ
  positivity

lemma bigQ_le_bigQ' {n ν : ℕ} (hn : 0 < n) : bigQ n ν ≤ bigQ' n ν := by
  unfold bigQ'
  calc bigQ n ν ≤ bigQ n ν * (2 * n * 2 ^ (n * ν)) := Nat.le_mul_of_pos_right _ (by positivity)
    _ = 2 * n * bigQ n ν * 2 ^ (n * ν) := by ring

/-- "`log₂ Q = (n + 1) log₂(2n + 1) + 2(2n + 1)ν`" (`appB-bitlength.tex:11`). -/
lemma logb_bigQ (n ν : ℕ) :
    Real.logb 2 (bigQ n ν) = (n + 1) * Real.logb 2 (2 * n + 1) + 2 * (2 * n + 1) * ν := by
  have h4 : Real.logb 2 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    ring
  unfold bigQ
  push_cast
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow, h4]
  push_cast
  ring

/-- "`log₂ Q = (n + 1) log₂(2n + 1) + 2(2n + 1)ν = O(nν)`" (`appB-bitlength.tex:11`) and "its bit
length is `O(nν)`" ((4)), with explicit constants: for `1 ≤ n ≤ ν`, `log₂ Q ≤ 10nν`, that is,
`Q ≤ 2^{10nν}`, and `2nQ2^{nν} ≤ 2^{12nν}`. -/
lemma bigQ_le_two_pow {n ν : ℕ} (hn : 1 ≤ n) (hnν : n ≤ ν) :
    bigQ n ν ≤ 2 ^ (10 * n * ν) ∧ bigQ' n ν ≤ 2 ^ (12 * n * ν) := by
  have hν : 1 ≤ ν := hn.trans hnν
  -- `log₂(2n + 1) ≤ 2n`, as `2n + 1 ≤ 4^n`
  have h4 : (2 * n + 1 : ℝ) ≤ 4 ^ n := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ 3 by norm_num) n
    norm_num at this
    linarith
  have hlog21 : Real.logb 2 (2 * n + 1) ≤ 2 * n := by
    have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h4
    rw [show (4 : ℝ) ^ n = 2 ^ (2 * n) by rw [pow_mul]; norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num), mul_one] at h
    exact_mod_cast h
  -- `log₂ Q = (n + 1) log₂(2n + 1) + 2(2n + 1)ν ≤ 10nν`
  have hlog : Real.logb 2 (bigQ n ν) ≤ ((10 * n * ν : ℕ) : ℝ) := by
    rw [logb_bigQ]
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hnν' : (n : ℝ) ≤ ν := by exact_mod_cast hnν
    have h1 : (n + 1 : ℝ) * Real.logb 2 (2 * n + 1) ≤ (n + 1) * (2 * n) :=
      mul_le_mul_of_nonneg_left hlog21 (by positivity)
    push_cast
    nlinarith
  have hQ : bigQ n ν ≤ 2 ^ (10 * n * ν) := by
    have hQpos : (0 : ℝ) < bigQ n ν := by exact_mod_cast bigQ_pos n ν
    have h := (Real.logb_le_iff_le_rpow (by norm_num) hQpos).1 hlog
    rw [Real.rpow_natCast] at h
    exact_mod_cast h
  refine ⟨hQ, ?_⟩
  have h2n : 2 * n ≤ 2 ^ (n * ν) := by
    have h1 : n - 1 < 2 ^ (n - 1) := Nat.lt_two_pow_self
    have h2 : 2 * n ≤ 2 ^ n := by
      have : 2 ^ n = 2 * 2 ^ (n - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hn]
      omega
    exact h2.trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right n hν))
  unfold bigQ'
  calc 2 * n * bigQ n ν * 2 ^ (n * ν) ≤ 2 ^ (n * ν) * 2 ^ (10 * n * ν) * 2 ^ (n * ν) := by
        gcongr
    _ = 2 ^ (12 * n * ν) := by rw [← pow_add, ← pow_add]; ring_nf

section Theorem

variable {E : Type*} [Fintype E] [DecidableEq E] {f : Finset E → ℝ} {m β : E → ℝ}

/-- **`thm:bitlength`** (Theorem 3.6, statement `stoc-sections/06-optimal-share.tex:37-39`, proof
`stoc-sections/appB-bitlength.tex:14-112`, with `Q` at :3-11), under the standing assumptions of
Section 3 (`Tracing.Hyp`). Suppose that every `m_e`, every `β_e` and every value `f(S)` is a
quotient of two integers of absolute value less than `2^ν` (`IsSmall ν`), and `n ≤ ν`. Then every
breakpoint of `x*` and some optimal contract are rationals whose numerators and denominators have
bit length `O(nν)`: every breakpoint is a quotient of two integers of absolute value at most
`Q = (2n + 1)^{n+1} 4^{(2n+1)ν}` (the first part), some optimal contract (that is, a maximizer of
`U_P(α) = (1 − α) r(x*(α))` over `[0, 1]`) is a quotient of two integers of absolute value at most
`2nQ2^{nν}` (the second part), and `log₂ Q = (n + 1) log₂(2n + 1) + 2(2n + 1)ν ≤ 10nν`, that is,
`Q ≤ 2^{10nν}`, and `2nQ2^{nν} ≤ 2^{12nν}` (the third part; `logb_bigQ`, `bigQ_le_two_pow`). The
second and the third part assume `n ≥ 1`, as Section 2 does ("a finite nonempty ground set",
`02-preliminaries.tex:4`) and as the paper's bounds need: for `n = 0`, the bound `2nQ2^{nν}` is
`0`, and `Q = 4^ν` exceeds `2^{10nν} = 1` when `ν ≥ 1`.

The paper's proof has four parts, each opened by a sentence and without a label; the docstrings
and comments number them (1) to (4):
(1) "We first write down the linear equations of a state": (a) finitely many event points
(`events_finite`, by `lem:pwaffine` and the argument of `lem:eventcount`, at most `C(n, 2)`
changes of the state on each interval of `lem:pwaffine`, `events_in_affine`); (b) on an open
interval `J` with constant state, the blocks keep their order and `S_j = D_0 ∪ ⋯ ∪ D_j` is a tight
level set, so `(α, x*(α), ρ(α))` solves the equations (`eqG`, `eqH`; `solJ_solves`); (c) for fixed
`α` the equations determine `x` and `ρ` (`determined`, with the paper's elimination: `Φ`, the
blocks with `D_j ∩ Z ≠ ∅`, the other blocks through `S_{j−1}` and `S_j` with `S_0 := ∅`, then all
`x_e`); (d) by `lem:velocity` the solutions form exactly the line (`lineJ_eq_solJ`,
`solves_iff_line`);
(2) "Next we single out a breakpoint by one more equation" (`step2_equation`): (a) `J_−`, `J_+`
(`exists_sides`); (b) the states differ (by `lem:velocity`); (c) the three cases in the paper's
order, the free sets differ, the zero sets differ, otherwise the blocks (`eq_of_free`,
`eq_of_zero`, `eq_of_block`, with `holds_only_at`); (d) the enlarged system has the only solution
`(b, x*(b), ρ^J(b))`, some `N` of its equations form a nonsingular square system, and Cramer's rule
gives `b = det G_α / det G` (`step2_cramer`);
(3) "Next we bound the size of `b`": the rows become integral (`rows_integral`,
`rows_integral_big`), the factor is the same for `det G` and `det G_α`, and Hadamard's inequality
bounds both by `(√N 4^ν)^N ≤ Q` (`ratio_of_integral_rows`, `hadamard_le_bigQ`; together
`breakpoint_ratio`);
(4) "Finally, we turn to an optimal contract": an interval `J` with constant state in the interior
of the piece `I` of an optimal contract (`exists_J_in_piece`), `x^J` is the affine form of `x*` on
`I` (`xJ_eq_on_piece`), Cramer's rule for `n + k` of the equations gives
`x*_e = (u_e + α v_e)/ζ` with `|u_e|, |v_e|, |ζ| ≤ Q` (`step4_cramer`), the reward on `I` is
`r⁰_I + r¹_I α` with `r⁰_I = P/(ζ ∏_e ā_e)`, `r¹_I = P'/(ζ ∏_e ā_e)` and
`|P|, |P'|, |ζ ∏_e ā_e| ≤ nQ2^{nν}` (`reward_ratio`), and the maximum of `U_P` over `I` is attained
at an end, `0`, `1` or a breakpoint, or, if `r¹_I > 0` and it lies in `I`, at the vertex
`(r¹_I − r⁰_I)/(2r¹_I) = (P' − P)/(2P')` of the parabola `(1 − α)(r⁰_I + r¹_I α)`
(`Stoc.Tracing.quad_max`, the remark after `lem:pwaffine`).

Not in the paper (D3): Hadamard's inequality (`det_sq_le_prod`), Cramer's rule in coordinates
(`cramer_coord`), the choice of a nonsingular square subsystem (`exists_square_subsystem`), the
constant state on an interval without event points (`state_eq_of_no_event`), the existence of `J`
inside a piece (`exists_J_in_piece`), `x^J` on the piece (`xJ_eq_on_piece`) and the existence of an
optimal contract (`exists_optimal_share`). -/
theorem bitlength (H : Tracing.Hyp f m β) {ν : ℕ} (hm : ∀ e, IsSmall ν (m e))
    (hβs : ∀ e, IsSmall ν (β e)) (hfs : ∀ S, IsSmall ν (f S)) (hnν : Fintype.card E ≤ ν) :
    (∀ b ∈ breakpoints (bestResponse f m β), ∃ p q : ℤ, q ≠ 0 ∧ b = p / q ∧
      |p| ≤ bigQ (Fintype.card E) ν ∧ |q| ≤ bigQ (Fintype.card E) ν) ∧
    (0 < Fintype.card E → ∃ αs ∈ Set.Icc (0 : ℝ) 1,
      (∀ α ∈ Set.Icc (0 : ℝ) 1, profit (grossValue f m β) α ≤ profit (grossValue f m β) αs) ∧
      ∃ p q : ℤ, q ≠ 0 ∧ αs = p / q ∧ |p| ≤ bigQ' (Fintype.card E) ν ∧
        |q| ≤ bigQ' (Fintype.card E) ν) ∧
    (0 < Fintype.card E → bigQ (Fintype.card E) ν ≤ 2 ^ (10 * Fintype.card E * ν) ∧
      bigQ' (Fintype.card E) ν ≤ 2 ^ (12 * Fintype.card E * ν)) := by
  -- (1) to (3): every breakpoint (`breakpoint_ratio`).
  refine ⟨fun b hb => breakpoint_ratio H hm hβs hfs hnν hb, fun hn => ?_,
    fun hn => bigQ_le_two_pow hn hnν⟩
  -- (4) "Finally, we turn to an optimal contract": an optimal contract `α⋆` and its piece
  -- `I = [a, c]`
  set n := Fintype.card E
  obtain ⟨αs, hαs, hopt⟩ := exists_optimal_share H
  obtain ⟨a, c, hp, hαac⟩ := Tracing.exists_piece H hαs
  -- "Let `J` be an open interval with constant state in the interior of a piece `I`. Then the
  -- affine extension `x^J` above is the affine form of `x*` on `I`."
  obtain ⟨lo, hi, α₁, hal, hhc, hlo, hS, hα₁⟩ := exists_J_in_piece H hp
  have hxJ := xJ_eq_on_piece H hp hal hhc hlo hS hα₁
  -- "As the equations of `J` determine `x` and `ρ` for fixed `α`, some `n + k` of them have a
  -- nonsingular matrix in the columns of `(x, ρ)`. We scale them as above, move the terms with `α`
  -- to the right-hand side and apply Cramer's rule. This gives `x*_e(α) = (u_e + α v_e)/ζ` on the
  -- piece, with integers `u_e`, `v_e` and `ζ ≠ 0` of absolute value at most `Q`."
  obtain ⟨ζ, hζ, hζQ, huv⟩ := step4_cramer H (hn.trans_le hnν) hm hβs hfs hlo hS hα₁
  choose u v hu hv hxuv using huv
  -- "Writing `m_e = a_e/ā_e` with integers `a_e` and `ā_e > 0`, `|a_e|, ā_e < 2^ν`, the reward on
  -- `I` is `r⁰_I + r¹_I α`, in the notation after `lem:pwaffine`, where `r⁰_I = P/(ζ ∏_e ā_e)` and
  -- `r¹_I = P'/(ζ ∏_e ā_e)` with `P := ∑_e a_e u_e ∏_{e'≠e} ā_{e'}` and
  -- `P' := ∑_e a_e v_e ∏_{e'≠e} ā_{e'}`, and the integers `P`, `P'` and `ζ ∏_e ā_e` have absolute
  -- value at most `nQ2^{nν}`." (The numerators `a_e` are not needed below; `ab` are the `ā_e`.)
  obtain ⟨_, ab, -, P, P', -, -, hden, hrew, -, hP, hP'⟩ :=
    reward_ratio (x := xJ f m β α₁) hm hn hζ hζQ hu hv fun α e => hxuv e α
  set r0 : ℝ := (P : ℝ) / ((ζ * ∏ e, ab e : ℤ) : ℝ) with hr0
  set r1 : ℝ := (P' : ℝ) / ((ζ * ∏ e, ab e : ℤ) : ℝ) with hr1
  have hUP : ∀ α ∈ Set.Icc a c, profit (grossValue f m β) α = (1 - α) * (r0 + r1 * α) := by
    intro α hα
    rw [profit, grossValue, hxJ α hα, hrew α]
  -- "The maximum of `U_P` over `I` is attained at an endpoint, which is `0`, `1` or a breakpoint,
  -- or, if `r¹_I > 0` and it lies in `I`, at the vertex `(r¹_I − r⁰_I)/(2r¹_I) = (P' − P)/(2P')`
  -- of the parabola `(1 − α)(r⁰_I + r¹_I α)`" (`quad_max`, the remark after `lem:pwaffine`).
  obtain ⟨α', hα', hcand, hmax⟩ := Tracing.quad_max hp.2.1.le r0 r1
  have hα'01 : α' ∈ Set.Icc (0 : ℝ) 1 := ⟨hp.1.trans hα'.1, hα'.2.trans hp.2.2.1⟩
  refine ⟨α', hα'01, fun α hα => (hopt α hα).trans ?_, ?_⟩
  · rw [hUP αs hαac, hUP α' hα']
    exact hmax αs hαac
  -- "So some optimal contract is a quotient of two integers of absolute value at most `2nQ2^{nν}`."
  have hQ' : (bigQ n ν : ℤ) ≤ bigQ' n ν := by exact_mod_cast bigQ_le_bigQ' hn
  have h1 : (1 : ℤ) ≤ bigQ' n ν := by
    have := bigQ_le_bigQ' (ν := ν) hn
    have := bigQ_pos n ν
    exact_mod_cast (show 1 ≤ bigQ' n ν by omega)
  rcases hcand with rfl | rfl | ⟨hd, rfl⟩
  · -- the left end, `0` or a breakpoint
    rcases hp.2.2.2.2.1 with ha | hbp
    · exact ⟨0, 1, one_ne_zero, by rw [ha]; simp, by simp, by simpa using h1⟩
    · obtain ⟨p, q, hq, hb, hpQ, hqQ⟩ := breakpoint_ratio H hm hβs hfs hnν hbp
      exact ⟨p, q, hq, hb, hpQ.trans hQ', hqQ.trans hQ'⟩
  · -- the right end, `1` or a breakpoint
    rcases hp.2.2.2.2.2 with hc | hbp
    · exact ⟨1, 1, one_ne_zero, by rw [hc]; simp, by simpa using h1, by simpa using h1⟩
    · obtain ⟨p, q, hq, hb, hpQ, hqQ⟩ := breakpoint_ratio H hm hβs hfs hnν hbp
      exact ⟨p, q, hq, hb, hpQ.trans hQ', hqQ.trans hQ'⟩
  · -- the vertex, if `r¹_I > 0`: `(r¹_I − r⁰_I)/(2r¹_I) = (P' − P)/(2P')`
    have hden' : (ζ : ℝ) * ∏ e, (ab e : ℝ) ≠ 0 := by exact_mod_cast hden
    have hζ' : (ζ : ℝ) ≠ 0 := left_ne_zero_of_mul hden'
    have hprod : ∏ e, (ab e : ℝ) ≠ 0 := right_ne_zero_of_mul hden'
    have hP'ne : P' ≠ 0 := by
      intro h0
      rw [hr1, h0, Int.cast_zero, zero_div] at hd
      exact lt_irrefl 0 hd
    have hP'ne' : (P' : ℝ) ≠ 0 := Int.cast_ne_zero.2 hP'ne
    refine ⟨P' - P, 2 * P', mul_ne_zero two_ne_zero hP'ne, ?_, ?_, ?_⟩
    · rw [hr0, hr1]
      push_cast
      field_simp
    · have := abs_sub P' P
      unfold bigQ'
      push_cast
      linarith
    · rw [abs_mul]
      unfold bigQ'
      push_cast
      norm_num
      linarith

end Theorem

end BitLength

end Stoc
