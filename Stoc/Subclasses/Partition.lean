-- stamp r8 2026-11-02
import Stoc.BestResponse.Quadratic

/-!
# Partition polymatroids

The STOC version, Appendix B.8 (`sec:A-subclasses`), Proposition `prop:partition`
(`stoc-sections/appB-quadratic.tex:649-712`): for every partition polymatroid, `B ≤ n`
(`partition_breakpoints`).

A polymatroid is a partition polymatroid if `P₊(f) = {x ≥ 0 | x(L) ≤ f(L) for L ∈ 𝓛}` for a family
`𝓛` of nonempty sets, the constraint sets, that are pairwise disjoint
(`stoc-sections/06-optimal-share.tex:80`, recalled at `appB-quadratic.tex:602-605`).

The proof follows the STOC version. With the constraint sets `E_1, …, E_k` (a part `E_i` is `Ei`
here, `f(E_i)` is `F`, `t(S) = ∑_{e ∈ S} m_e/β_e` is `tA m β S` and `α_i = f(E_i)/t(E_i)` is
`F / tA m β Ei`):

1. the sets `E_i` cover `E` since `P₊(f)` is bounded (`exists_mem_of_indepPoly_eq`), so they
   partition `E`, and the response decomposes over these parts (`isBestResponse_of_optimalOn`,
   `bestResponse_eq_partResp`);
2. fix a part `E_i`; if `f(E_i) = 0` or `t(E_i) = 0`, the response is zero on `E_i`
   (`optimalOn_zero`), and otherwise `α_i := f(E_i)/t(E_i)`;
3. for `α ≤ α_i`, the unconstrained response `x*_e = α t_e`, `e ∈ E_i`, is feasible, as
   `α t(E_i) ≤ f(E_i)` (`feasible_unconstrained`), and hence optimal (`optimalOn_unconstrained`);
4. now let `α > α_i`; each `x_e(λ) := (α m_e − λ)⁺/β_e` (`xLam`) is continuous and nonincreasing
   in `λ`, and strictly decreasing while it is positive, that is, for `λ < α m_e`
   (`continuous_xLam`, `antitone_xLam`, `strictAntiOn_xLam`); hence the sum
   `s_i(λ) := ∑_{e ∈ E_i} x_e(λ)` (`sA`) is continuous, equals `α t(E_i)` at `λ = 0` as `m ≥ 0`,
   decreases strictly until `λ = α max_{e ∈ E_i} m_e`, and is zero from there on (`continuous_sA`,
   `sA_zero`, `strictAntiOn_sA`, `sA_eq_zero`);
5. as `α > α_i`, `α t(E_i) > f(E_i) > 0`, so there is exactly one `λ ≥ 0` with
   `s_i(λ) = f(E_i)` (`existsUnique_lam`); it is `λ_i(α)` (`lamA`), positive since
   `s_i(0) > f(E_i)` (`lamA_pos`); `x_e := x_e(λ_i(α))` has `x(E_i) = f(E_i)`;
6. this `x` is optimal on `E_i`: its marginals `α m_e − β_e x_e` are at most `λ_i(α)`, with
   equality whenever `x_e > 0`; for every feasible `y` on `E_i`, as `y ≥ 0`, this gives
   `(α m_e − β_e x_e)(y_e − x_e) ≤ λ_i(α)(y_e − x_e)` for every `e ∈ E_i`; hence, by concavity of
   the per-element utility, `∑_{e ∈ E_i} (α m_e (y_e − x_e) − β_e/2 (y_e² − x_e²)) ≤
   ∑_{e ∈ E_i} (α m_e − β_e x_e)(y_e − x_e) ≤ λ_i(α)(y(E_i) − f(E_i)) ≤ 0` (`optimalOn_lam`);
7. dividing `s_i(λ_i(α)) = f(E_i)` by `α` shows that `μ_i(α) := λ_i(α)/α` (`muA`) satisfies
   `q_i(μ_i(α)) = f(E_i)/α`, where `q_i(μ) := ∑_{e ∈ E_i} (m_e − μ)⁺/β_e` (`qA`, `sA_eq`,
   `qA_muA`);
8. the left-hand side depends only on `μ_i(α)`, and the right-hand side only on `α`; as
   `f(E_i) > 0`, the right-hand side strictly decreases as `α` increases; `q_i` is continuous and
   strictly decreasing on `[0, max_{e ∈ E_i} m_e]` (`continuous_qA`, `strictAntiOn_qA`), which
   contains `μ_i(α)` because `0 < λ_i(α) < α max_{e ∈ E_i} m_e` (`lamA_lt`, `muA_mem`); so when `α`
   increases, `q_i(μ_i(α))` decreases, and this forces `μ_i(α)` to increase (`strictMonoOn_muA`);
9. as `q_i` has a continuous inverse on this interval, `μ_i(α) = q_i⁻¹(f(E_i)/α)` is moreover
   continuous in `α` (`continuousAt_muA`);
10. as `μ_i(α)` increases and stays below `max_{e ∈ E_i} m_e`, the support
   `W_i := {e ∈ E_i | m_e > μ_i(α)}` (`WA`) only loses elements, never those with the largest
   reward, so it changes at most `|E_i| − 1` times (`Wchanges`, `ncard_Wchanges_le`); between these
   changes, `W_i` is constant (`eventually_WA_eq`);
11. as `x_e = (α m_e − λ_i(α))/β_e` for `e ∈ W_i` and `x_e = 0` for the other elements of `E_i`,
   the equation `x(E_i) = f(E_i)` reads `α t(W_i) − λ_i(α) β⁻¹(W_i) = f(E_i)`; hence
   `λ_i(α) = (α t(W_i) − f(E_i))/β⁻¹(W_i)` is affine in `α` (`lamA_eq_of_WA`), and so is the
   response (`affineNear_partResp`);
12. including `α_i` gives at most `|E_i|` breakpoints on `E_i` (`partBreaks`,
   `ncard_partBreaks_le`), hence at most `|E_1| + ⋯ + |E_k| = n` overall (`partition_breakpoints`).

Not in the paper (D3), each in its own lemma: that the parts cover `E` (step (1),
`exists_mem_of_indepPoly_eq`, which the STOC version states with the reason "since `P₊(f)` is
bounded") and that the response decomposes over the parts (step (1), `isBestResponse_of_optimalOn`),
both stated without proof; that a degenerate part has zero response (step (2), `optimalOn_zero`),
stated without proof; that the unconstrained response is optimal on `E_i` (step (3),
`optimalOn_unconstrained`), which "and hence optimal" leaves to the reader; and that a continuous
strictly decreasing function on an interval has a continuous inverse (step (9),
`exists_continuousAt_inverse`), which the STOC version uses without proof.

As in Appendix B.8, `B` here counts the breakpoints in `(0, ∞)` (`Stoc.breakpoints`), which bound
the number in `(0, 1)` (`rem:subclasses`, `PolynomialClasses.lean`).

Taken over on 2026-10-21 from `Paper/Subclasses/Partition.lean` (the long paper's
`prop:partition-polymatroids`) for the STOC version (`stoc.tex`); from then on this copy follows the
STOC version.
-/

namespace Stoc

open Finset Filter Topology

noncomputable section

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {f : Finset E → ℝ} {m β : E → ℝ}

/-- `(E, f)` is a partition polymatroid: `P₊(f) = {x ≥ 0 | x(L) ≤ f(L) for L ∈ 𝓛}` for a family
`𝓛` of pairwise disjoint nonempty sets, the constraint sets
(`stoc-sections/06-optimal-share.tex:80`, `appB-quadratic.tex:602-605`). -/
def IsPartitionPolymatroid (f : Finset E → ℝ) : Prop :=
  ∃ L : Finset (Finset E), (∀ Ei ∈ L, Ei.Nonempty) ∧ (L : Set (Finset E)).PairwiseDisjoint id ∧
    indepPoly f = {x | (∀ e, 0 ≤ x e) ∧ ∀ Ei ∈ L, ∑ e ∈ Ei, x e ≤ f Ei}

omit [Fintype E] in
/-- (Not in the paper: step (1) of `prop:partition` states this with the reason "since `P₊(f)` is
bounded", and the setup of `thm:laminar` with the reason "since otherwise `x_e` would be unbounded
on `P₊(f)`".) Every element lies in some constraint set: if `e` lay in none of them,
`x({e}) ≤ f({e})` would fail on `P₊(f)` for a large `x_e`. -/
theorem exists_mem_of_indepPoly_eq (hf : IsRankFunction f) {L : Finset (Finset E)}
    (hP : indepPoly f = {x | (∀ e, 0 ≤ x e) ∧ ∀ A ∈ L, ∑ e ∈ A, x e ≤ f A}) (e : E) :
    ∃ A ∈ L, e ∈ A := by
  by_contra h
  simp only [not_exists, not_and] at h
  have hx : (Pi.single e (f {e} + 1) : E → ℝ) ∈ indepPoly f := by
    rw [hP]
    refine ⟨fun e' => ?_, fun A hA => ?_⟩
    · by_cases h' : e' = e
      · subst h'
        simp only [Pi.single_eq_same]
        linarith [hf.nonneg {e'}]
      · simp [h']
    · rw [sum_eq_zero fun e' he' => ?_]
      · exact hf.nonneg A
      · have : e' ≠ e := fun h'' => h A hA (h'' ▸ he')
        simp [this]
  have := hx.2 {e}
  norm_num at this

/-- A finite union of finite sets of reals, with a bound on the number of elements. -/
theorem finite_ncard_biUnion_le {ι : Type*} [DecidableEq ι] (I : Finset ι) (T : ι → Set ℝ)
    (c : ι → ℕ) (hT : ∀ i ∈ I, (T i).Finite ∧ (T i).ncard ≤ c i) :
    (⋃ i ∈ I, T i).Finite ∧ (⋃ i ∈ I, T i).ncard ≤ ∑ i ∈ I, c i := by
  induction I using Finset.induction_on with
  | empty => simp
  | insert i I hi ih =>
    have h' := ih fun j hj => hT j (mem_insert_of_mem hj)
    have hi' := hT i (mem_insert_self _ _)
    rw [Finset.set_biUnion_insert, sum_insert hi]
    exact ⟨hi'.1.union h'.1, (Set.ncard_union_le _ _).trans (add_le_add hi'.2 h'.2)⟩

/-! ### Step (1): the response decomposes over the parts -/

/-- The agent's utility on a part `E_i`: `∑_{e ∈ E_i} (α m_e y_e − β_e/2 y_e²)`. -/
def partUtil (m β : E → ℝ) (Ei : Finset E) (α : ℝ) (y : E → ℝ) : ℝ :=
  ∑ e ∈ Ei, (α * m e * y e - β e / 2 * y e ^ 2)

/-- `x` is optimal on the part `E_i` with `F = f(E_i)`: no `y` that is feasible on `E_i`
(`y ≥ 0` on `E_i`, `y(E_i) ≤ F`) has a larger utility on `E_i`. -/
def OptimalOn (m β : E → ℝ) (Ei : Finset E) (F α : ℝ) (x : E → ℝ) : Prop :=
  ∀ y : E → ℝ, (∀ e ∈ Ei, 0 ≤ y e) → ∑ e ∈ Ei, y e ≤ F →
    partUtil m β Ei α y ≤ partUtil m β Ei α x

omit [Fintype E] [DecidableEq E] in
/-- Only the values on `E_i` matter for the optimality on `E_i`. -/
theorem OptimalOn.congr {Ei : Finset E} {F α : ℝ} {x x' : E → ℝ} (h : OptimalOn m β Ei F α x)
    (hxx : ∀ e ∈ Ei, x e = x' e) : OptimalOn m β Ei F α x' := by
  intro y hy hyE
  have : partUtil m β Ei α x = partUtil m β Ei α x' :=
    sum_congr rfl fun e he => by rw [hxx e he]
  rw [← this]
  exact h y hy hyE

/-- (Not in the paper: step (1) of `prop:partition` says "… and the response decomposes over these
parts." without proof.) A point of `P₊(f)` that is optimal on every part is the best response, as
the utility is the sum of the utilities on the parts. -/
theorem isBestResponse_of_optimalOn {L : Finset (Finset E)}
    (hdisj : (L : Set (Finset E)).PairwiseDisjoint id) (hU : L.biUnion id = univ)
    (hP : indepPoly f = {x | (∀ e, 0 ≤ x e) ∧ ∀ A ∈ L, ∑ e ∈ A, x e ≤ f A}) {α : ℝ}
    {x : E → ℝ} (hx : x ∈ indepPoly f) (h : ∀ A ∈ L, OptimalOn m β A (f A) α x) :
    IsBestResponse (indepPoly f) m β α x := by
  have hsplit : ∀ y, utility m β α y = ∑ A ∈ L, partUtil m β A α y := by
    intro y
    rw [utility_eq_sum, ← hU, sum_biUnion hdisj]
    rfl
  refine ⟨hx, fun y hy => ?_⟩
  rw [hP] at hy
  rw [hsplit, hsplit]
  exact sum_le_sum fun A hA => h A hA y (fun e _ => hy.1 e) (hy.2 A hA)

/-! ### Steps (2)-(6): the response on one part -/

/-- `t(S) = ∑_{e ∈ S} m_e/β_e`. -/
def tA (m β : E → ℝ) (A : Finset E) : ℝ := ∑ e ∈ A, m e / β e

omit [Fintype E] [DecidableEq E] in
/-- (Not in the paper: step (2) of `prop:partition` states this without proof.) If `f(E_i) = 0` or
`t(E_i) = 0`, the response is zero on `E_i`. -/
theorem optimalOn_zero (hβ : ∀ e, 0 < β e) (hm : ∀ e, 0 ≤ m e) {Ei : Finset E} {F α : ℝ}
    (h : F = 0 ∨ tA m β Ei = 0) : OptimalOn m β Ei F α 0 := by
  intro y hy hyE
  have h0 : partUtil m β Ei α 0 = 0 := by simp [partUtil]
  rw [h0]
  rcases h with hF | ht
  · -- `f(E_i) = 0`: the only feasible point on `E_i` is `0`.
    have hy0 : ∀ e ∈ Ei, y e = 0 := fun e he =>
      (sum_eq_zero_iff_of_nonneg hy).1 (le_antisymm (hF ▸ hyE) (sum_nonneg hy)) e he
    exact le_of_eq (sum_eq_zero fun e he => by rw [hy0 e he]; ring)
  · -- `t(E_i) = 0`: all rewards on `E_i` vanish.
    have hm0 : ∀ e ∈ Ei, m e = 0 := by
      intro e he
      have := (sum_eq_zero_iff_of_nonneg fun e _ => div_nonneg (hm e) (hβ e).le).1 ht e he
      rcases div_eq_zero_iff.1 this with h' | h'
      · exact h'
      · exact absurd h' (hβ e).ne'
    refine sum_nonpos fun e he => ?_
    rw [hm0 e he]
    have := hβ e
    have := sq_nonneg (y e)
    nlinarith

omit [Fintype E] [DecidableEq E] in
/-- `prop:partition`, step (3): "For `α ≤ α_i`, the unconstrained response `x*_e = α t_e`,
`e ∈ E_i`, is feasible, as `α t(E_i) ≤ f(E_i)`, …" Here with `α_i = f(E_i)/t(E_i)`, feasible on
`E_i`. -/
theorem feasible_unconstrained (hβ : ∀ e, 0 < β e) (hm : ∀ e, 0 ≤ m e) {Ei : Finset E}
    {F α : ℝ} (ht : 0 < tA m β Ei) (hα : 0 ≤ α) (hαi : α ≤ F / tA m β Ei) :
    (∀ e ∈ Ei, 0 ≤ α * (m e / β e)) ∧ ∑ e ∈ Ei, α * (m e / β e) ≤ F := by
  refine ⟨fun e _ => mul_nonneg hα (div_nonneg (hm e) (hβ e).le), ?_⟩
  -- `α t(E_i) ≤ f(E_i)`
  rw [← mul_sum]
  exact (le_div_iff₀ ht).1 hαi

omit [Fintype E] [DecidableEq E] in
/-- (Not in the paper: step (3) of `prop:partition` says "… and hence optimal." of the feasible
unconstrained response, leaving to the reader that it maximizes the utility without constraints.)
The unconstrained response `x_e = α t_e` is optimal on `E_i`: it maximizes every term
`α m_e y_e − β_e/2 y_e²` (completing the square). -/
theorem optimalOn_unconstrained (hβ : ∀ e, 0 < β e) {Ei : Finset E} {F α : ℝ} :
    OptimalOn m β Ei F α fun e => α * (m e / β e) := by
  intro y _ _
  refine sum_le_sum fun e _ => ?_
  have hb := hβ e
  have key : α * m e * y e - β e / 2 * y e ^ 2 =
      α * m e * (α * (m e / β e)) - β e / 2 * (α * (m e / β e)) ^ 2 -
        β e / 2 * (y e - α * (m e / β e)) ^ 2 := by
    field_simp
    ring
  rw [key]
  have := sq_nonneg (y e - α * (m e / β e))
  nlinarith

/-- `x_e(λ) = (α m_e − λ)⁺/β_e` (`appB-quadratic.tex:663-664`). -/
def xLam (m β : E → ℝ) (α : ℝ) (e : E) (l : ℝ) : ℝ := max (α * m e - l) 0 / β e

omit [Fintype E] [DecidableEq E] in
/-- `prop:partition`, step (4): "Each `x_e(λ)` is continuous … in `λ`, …" -/
theorem continuous_xLam (α : ℝ) (e : E) : Continuous (xLam m β α e) := by
  unfold xLam
  fun_prop

omit [Fintype E] [DecidableEq E] in
/-- `prop:partition`, step (4): "Each `x_e(λ)` is … nonincreasing in `λ`, …" -/
theorem antitone_xLam (hβ : ∀ e, 0 < β e) (α : ℝ) (e : E) : Antitone (xLam m β α e) :=
  fun _ _ hll' => div_le_div_of_nonneg_right (max_le_max (by linarith) le_rfl) (hβ e).le

omit [Fintype E] [DecidableEq E] in
/-- `prop:partition`, step (4): "Each `x_e(λ)` is … strictly decreasing while it is positive, that
is, for `λ < α m_e`." Here on `(−∞, α m_e]`. -/
theorem strictAntiOn_xLam (hβ : ∀ e, 0 < β e) (α : ℝ) (e : E) :
    StrictAntiOn (xLam m β α e) (Set.Iic (α * m e)) := by
  intro l _ l' hl' hll'
  have hl'e : l' ≤ α * m e := hl'
  unfold xLam
  rw [max_eq_left (sub_nonneg.2 hl'e), max_eq_left (by linarith)]
  exact div_lt_div_of_pos_right (by linarith) (hβ e)

/-- The sum `s_i(λ) = ∑_{e ∈ E_i} x_e(λ)` (`appB-quadratic.tex:666-667`). -/
def sA (m β : E → ℝ) (Ei : Finset E) (α l : ℝ) : ℝ := ∑ e ∈ Ei, xLam m β α e l

omit [Fintype E] [DecidableEq E] in
/-- `prop:partition`, step (4): "Hence the sum `s_i(λ) := ∑_{e∈E_i} x_e(λ)` is continuous, …" -/
theorem continuous_sA (Ei : Finset E) (α : ℝ) : Continuous (sA m β Ei α) :=
  continuous_finsetSum _ fun e _ => continuous_xLam α e

omit [Fintype E] [DecidableEq E] in
/-- `prop:partition`, step (4): "… equals `α t(E_i)` at `λ = 0` as `m ≥ 0`, …" -/
theorem sA_zero (hm : ∀ e, 0 ≤ m e) (Ei : Finset E) {α : ℝ} (hα : 0 ≤ α) :
    sA m β Ei α 0 = α * tA m β Ei := by
  unfold sA tA xLam
  rw [mul_sum]
  refine sum_congr rfl fun e _ => ?_
  rw [sub_zero, max_eq_left (mul_nonneg hα (hm e)), mul_div_assoc]

omit [Fintype E] [DecidableEq E] in
/-- `prop:partition`, step (4): "… decreases strictly until `λ = α max_{e∈E_i} m_e`, …": every
`x_e(λ)` is nonincreasing, and that of an element with the largest reward decreases strictly, as
it is positive there. -/
theorem strictAntiOn_sA (hβ : ∀ e, 0 < β e) {Ei : Finset E} (hEi : Ei.Nonempty) (α : ℝ) :
    StrictAntiOn (sA m β Ei α) (Set.Icc 0 (α * Ei.sup' hEi m)) := by
  intro l _ l' hl' hll'
  obtain ⟨e₀, he₀, hmax⟩ := exists_mem_eq_sup' hEi m
  have h' : l' ≤ α * m e₀ := hmax ▸ hl'.2
  refine sum_lt_sum (fun e _ => antitone_xLam hβ α e hll'.le) ⟨e₀, he₀, ?_⟩
  exact strictAntiOn_xLam hβ α e₀ (show l ≤ α * m e₀ by linarith) h' hll'

omit [Fintype E] [DecidableEq E] in
/-- `prop:partition`, step (4): "… and is zero from there on." -/
theorem sA_eq_zero {Ei : Finset E} (hEi : Ei.Nonempty) {α l : ℝ} (hα : 0 ≤ α)
    (hl : α * Ei.sup' hEi m ≤ l) : sA m β Ei α l = 0 :=
  sum_eq_zero fun e he => by
    unfold xLam
    rw [max_eq_right (by linarith [mul_le_mul_of_nonneg_left (le_sup' m he) hα]), zero_div]

omit [Fintype E] [DecidableEq E] in
/-- `prop:partition`, step (5): "As `α > α_i`, we have `α t(E_i) > f(E_i) > 0`. So there is exactly
one `λ ≥ 0` with `s_i(λ) = f(E_i)`." By step (4): the intermediate value theorem on
`[0, α max_{e ∈ E_i} m_e]`, where `s_i` decreases strictly, and `s_i = 0` from there on. -/
theorem existsUnique_lam (hβ : ∀ e, 0 < β e) (hm : ∀ e, 0 ≤ m e) {Ei : Finset E}
    (hEi : Ei.Nonempty) {F : ℝ} (hF : 0 < F) (ht : 0 < tA m β Ei) {α : ℝ}
    (hαi : F / tA m β Ei < α) : ∃! l, 0 ≤ l ∧ sA m β Ei α l = F := by
  have hα : 0 < α := (div_pos hF ht).trans hαi
  set M := Ei.sup' hEi m
  -- "As `α > α_i`, we have `α t(E_i) > f(E_i) > 0`."
  have hFlt : F < α * tA m β Ei := (div_lt_iff₀ ht).1 hαi
  have hs0 : sA m β Ei α 0 = α * tA m β Ei := sA_zero hm Ei hα.le
  have hsM : sA m β Ei α (α * M) = 0 := sA_eq_zero hEi hα.le le_rfl
  have hM0 : 0 ≤ α * M := by
    obtain ⟨e₀, he₀⟩ := hEi
    exact mul_nonneg hα.le ((hm e₀).trans (le_sup' m he₀))
  obtain ⟨l, hl, hlF⟩ : F ∈ sA m β Ei α '' Set.Icc 0 (α * M) :=
    intermediate_value_Icc' hM0 (continuous_sA Ei α).continuousOn ⟨by rw [hsM]; exact hF.le, by
      rw [hs0]; exact hFlt.le⟩
  refine ⟨l, ⟨hl.1, hlF⟩, fun l' ⟨hl'0, hl'F⟩ => ?_⟩
  -- every solution lies below `α max_{e ∈ E_i} m_e`, from where on `s_i` is zero
  have hl'M : l' < α * M := by
    by_contra h
    rw [sA_eq_zero hEi hα.le (not_lt.1 h)] at hl'F
    linarith
  exact (strictAntiOn_sA hβ hEi α).injOn ⟨hl'0, hl'M.le⟩ hl (hl'F.trans hlF.symm)

open Classical in
/-- `λ_i(α)`: the unique `λ ≥ 0` with `s_i(λ) = f(E_i)` (for `α > α_i`,
`appB-quadratic.tex:670-671`). -/
def lamA (m β : E → ℝ) (Ei : Finset E) (F α : ℝ) : ℝ :=
  if h : ∃ l, 0 ≤ l ∧ sA m β Ei α l = F then h.choose else 0

omit [Fintype E] [DecidableEq E] in
theorem lamA_spec (hβ : ∀ e, 0 < β e) (hm : ∀ e, 0 ≤ m e) {Ei : Finset E}
    (hEi : Ei.Nonempty) {F : ℝ} (hF : 0 < F) (ht : 0 < tA m β Ei) {α : ℝ}
    (hαi : F / tA m β Ei < α) : 0 ≤ lamA m β Ei F α ∧ sA m β Ei α (lamA m β Ei F α) = F := by
  have h := (existsUnique_lam hβ hm hEi hF ht hαi).exists
  simp only [lamA, h, dite_true]
  exact h.choose_spec

omit [Fintype E] [DecidableEq E] in
/-- `prop:partition`, step (5): "We call it `λ_i(α)`, and it is positive since
`s_i(0) > f(E_i)`." -/
theorem lamA_pos (hβ : ∀ e, 0 < β e) (hm : ∀ e, 0 ≤ m e) {Ei : Finset E}
    (hEi : Ei.Nonempty) {F : ℝ} (hF : 0 < F) (ht : 0 < tA m β Ei) {α : ℝ}
    (hαi : F / tA m β Ei < α) : 0 < lamA m β Ei F α := by
  obtain ⟨h0, hs⟩ := lamA_spec hβ hm hEi hF ht hαi
  refine lt_of_le_of_ne h0 fun h => ?_
  have hα : 0 < α := (div_pos hF ht).trans hαi
  rw [← h, sA_zero hm Ei hα.le] at hs
  linarith [(div_lt_iff₀ ht).1 hαi]

omit [Fintype E] [DecidableEq E] in
/-- `prop:partition`, steps (5) and (6) (`appB-quadratic.tex:672-688`): "Let `x_e := x_e(λ_i(α))`
for `e ∈ E_i`, so that `x_e = (α m_e − λ_i(α))⁺/β_e`, `x(E_i) = f(E_i)`. This `x` is optimal on
`E_i`." The lemma takes any `λ ≥ 0` with `s_i(λ) = f(E_i)` in place of `λ_i(α)`, and shows that
`x_e = x_e(λ)` is feasible and optimal on `E_i`, by the three sentences of step (6) quoted in the
proof. -/
theorem optimalOn_lam (hβ : ∀ e, 0 < β e) {Ei : Finset E} {F α l : ℝ} (hl : 0 ≤ l)
    (hs : sA m β Ei α l = F) :
    ((∀ e ∈ Ei, 0 ≤ xLam m β α e l) ∧ ∑ e ∈ Ei, xLam m β α e l ≤ F) ∧
      OptimalOn m β Ei F α fun e => xLam m β α e l := by
  set x : E → ℝ := fun e => xLam m β α e l
  have hx0 : ∀ e, 0 ≤ x e := fun e => div_nonneg (le_max_right _ _) (hβ e).le
  refine ⟨⟨fun e _ => hx0 e, hs.le⟩, fun y hy hyE => ?_⟩
  -- (6) "Its marginals `α m_e − β_e x_e` are at most `λ_i(α)`, with equality whenever `x_e > 0`."
  -- Here with `λ` (`l`) for `λ_i(α)`.
  have hmarg : ∀ e, α * m e - β e * x e ≤ l ∧ (0 < x e → α * m e - β e * x e = l) := by
    intro e
    have hb := (hβ e).ne'
    have hx : β e * x e = max (α * m e - l) 0 := by simp only [x, xLam]; field_simp
    rw [hx]
    constructor
    · rcases le_total (α * m e - l) 0 with h | h
      · rw [max_eq_right h]
        linarith
      · rw [max_eq_left h]
        linarith
    · intro hpos
      have : 0 < max (α * m e - l) 0 := by
        have := mul_pos (hβ e) hpos
        rwa [hx] at this
      rw [max_eq_left (by
        by_contra h'
        rw [not_le] at h'
        rw [max_eq_right h'.le] at this
        exact lt_irrefl 0 this)]
      ring
  -- (6) "For every feasible `y` on `E_i`, as `y ≥ 0`, this gives
  -- `(α m_e − β_e x_e)(y_e − x_e) ≤ λ_i(α)(y_e − x_e)` for every `e ∈ E_i`."
  have hterm : ∀ e ∈ Ei, (α * m e - β e * x e) * (y e - x e) ≤ l * (y e - x e) := by
    intro e he
    rcases (hx0 e).lt_or_eq with hpos | hzero
    · rw [(hmarg e).2 hpos]
    · have h2 : 0 ≤ y e - x e := by
        rw [← hzero, sub_zero]
        exact hy e he
      exact mul_le_mul_of_nonneg_right (hmarg e).1 h2
  -- (6) "Hence, by concavity of the per-element utility `x_e ↦ α m_e x_e − β_e/2 x_e²`, every
  -- feasible `y` on `E_i` satisfies
  -- `∑_{e∈E_i} (α m_e (y_e − x_e) − β_e/2 (y_e² − x_e²)) ≤ ∑_{e∈E_i} (α m_e − β_e x_e)(y_e − x_e)
  -- ≤ λ_i(α)(y(E_i) − f(E_i)) ≤ 0`."
  have key : partUtil m β Ei α y - partUtil m β Ei α x ≤ 0 := by
    calc partUtil m β Ei α y - partUtil m β Ei α x
        = ∑ e ∈ Ei, (α * m e * (y e - x e) - β e / 2 * (y e ^ 2 - x e ^ 2)) := by
          rw [partUtil, partUtil, ← sum_sub_distrib]
          exact sum_congr rfl fun e _ => by ring
      _ ≤ ∑ e ∈ Ei, (α * m e - β e * x e) * (y e - x e) := by
          -- concavity of the per-element utility
          refine sum_le_sum fun e _ => ?_
          have := mul_nonneg (hβ e).le (sq_nonneg (y e - x e))
          nlinarith
      _ ≤ l * (∑ e ∈ Ei, y e - F) := by
          rw [← hs]
          calc ∑ e ∈ Ei, (α * m e - β e * x e) * (y e - x e) ≤ ∑ e ∈ Ei, l * (y e - x e) :=
                sum_le_sum hterm
            _ = l * (∑ e ∈ Ei, y e - sA m β Ei α l) := by
                rw [← mul_sum, sum_sub_distrib]
                rfl
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hl (by linarith)
  linarith

/-- The response on a part `E_i` with `F = f(E_i)`: `0` if `f(E_i) = 0` or `t(E_i) = 0`; `α t_e` for
`α ≤ α_i`; and `x_e(λ_i(α)) = (α m_e − λ_i(α))⁺/β_e` for `α > α_i`. -/
def partResp (m β : E → ℝ) (Ei : Finset E) (F α : ℝ) : E → ℝ :=
  if F = 0 ∨ tA m β Ei = 0 then 0
  else if α ≤ F / tA m β Ei then fun e => α * (m e / β e)
  else fun e => xLam m β α e (lamA m β Ei F α)

omit [Fintype E] [DecidableEq E] in
/-- Steps (2)-(6): the response on the part `E_i` is feasible and optimal on `E_i`. -/
theorem partResp_optimal (hβ : ∀ e, 0 < β e) (hm : ∀ e, 0 ≤ m e) {Ei : Finset E}
    (hEi : Ei.Nonempty) {F : ℝ} (hF : 0 ≤ F) {α : ℝ} (hα : 0 ≤ α) :
    ((∀ e ∈ Ei, 0 ≤ partResp m β Ei F α e) ∧ ∑ e ∈ Ei, partResp m β Ei F α e ≤ F) ∧
      OptimalOn m β Ei F α (partResp m β Ei F α) := by
  unfold partResp
  by_cases hdeg : F = 0 ∨ tA m β Ei = 0
  · -- (2) "If `f(E_i) = 0` or `t(E_i) = 0`, the response is zero on `E_i`, …" (`optimalOn_zero`)
    simp only [hdeg, ite_true, Pi.zero_apply, sum_const_zero]
    exact ⟨⟨fun _ _ => le_rfl, hF⟩, optimalOn_zero hβ hm hdeg⟩
  simp only [hdeg, ite_false]
  push Not at hdeg
  have hF0 : 0 < F := lt_of_le_of_ne hF (Ne.symm hdeg.1)
  have ht : 0 < tA m β Ei :=
    lt_of_le_of_ne (sum_nonneg fun e _ => div_nonneg (hm e) (hβ e).le) (Ne.symm hdeg.2)
  by_cases hαi : α ≤ F / tA m β Ei
  · -- (3) "For `α ≤ α_i`, the unconstrained response `x*_e = α t_e`, `e ∈ E_i`, is feasible, as
    -- `α t(E_i) ≤ f(E_i)`, and hence optimal."
    simp only [hαi, ite_true]
    exact ⟨feasible_unconstrained hβ hm ht hα hαi, optimalOn_unconstrained hβ⟩
  · -- (4)-(6) "Now let `α > α_i`." …
    simp only [hαi, ite_false]
    obtain ⟨hl, hs⟩ := lamA_spec hβ hm hEi hF0 ht (not_le.1 hαi)
    exact optimalOn_lam hβ hl hs

/-- `prop:partition`, steps (1)-(6) on all parts: `x*` is, on every part `E_i`, the response on
`E_i`; the decomposition of step (1) (`isBestResponse_of_optimalOn`) with steps (2)-(6) on each part
(`partResp_optimal`). -/
theorem bestResponse_eq_partResp (hf : IsRankFunction f) (hβ : ∀ e, 0 < β e) (hm : ∀ e, 0 ≤ m e)
    {L : Finset (Finset E)} (hne : ∀ A ∈ L, A.Nonempty)
    (hdisj : (L : Set (Finset E)).PairwiseDisjoint id)
    (hP : indepPoly f = {x | (∀ e, 0 ≤ x e) ∧ ∀ A ∈ L, ∑ e ∈ A, x e ≤ f A})
    {part : E → Finset E} (hpartL : ∀ e, part e ∈ L) (hmem : ∀ e, e ∈ part e) {α : ℝ}
    (hα : 0 ≤ α) :
    bestResponse f m β α = fun e => partResp m β (part e) (f (part e)) α e := by
  have hpart : ∀ A ∈ L, ∀ e ∈ A, part e = A := fun A hA e he =>
    hdisj.elim_finset (hpartL e) hA e (hmem e) he
  have hU : L.biUnion id = univ :=
    eq_univ_iff_forall.2 fun e => mem_biUnion.2 ⟨part e, hpartL e, hmem e⟩
  set x : E → ℝ := fun e => partResp m β (part e) (f (part e)) α e
  have hxA : ∀ A ∈ L, ∀ e ∈ A, x e = partResp m β A (f A) α e := fun A hA e he => by
    simp only [x, hpart A hA e he]
  have hopt := fun A (hA : A ∈ L) => partResp_optimal (m := m) hβ hm (hne A hA) (hf.nonneg A) hα
  have hx : x ∈ indepPoly f := by
    rw [hP]
    refine ⟨fun e => ?_, fun A hA => ?_⟩
    · exact (hopt (part e) (hpartL e)).1.1 e (hmem e)
    · rw [sum_congr rfl (hxA A hA)]
      exact (hopt A hA).1.2
  refine (IsBestResponse.eq_bestResponse hβ hf (isBestResponse_of_optimalOn hdisj hU hP hx
    fun A hA => (hopt A hA).2.congr fun e he => (hxA A hA e he).symm)).symm

/-! ### Steps (7)-(10): the multiplier `μ_i(α) = λ_i(α)/α` and the support `W_i` -/

/-- `q_i(μ) = ∑_{e ∈ E_i} (m_e − μ)⁺/β_e` (`appB-quadratic.tex:693`). -/
def qA (m β : E → ℝ) (Ei : Finset E) (μ : ℝ) : ℝ := ∑ e ∈ Ei, max (m e - μ) 0 / β e

omit [Fintype E] [DecidableEq E] in
/-- `s_i(λ) = α q_i(λ/α)` for `α > 0`. -/
theorem sA_eq (Ei : Finset E) {α : ℝ} (hα : 0 < α) (l : ℝ) :
    sA m β Ei α l = α * qA m β Ei (l / α) := by
  unfold sA qA xLam
  rw [mul_sum]
  refine sum_congr rfl fun e _ => ?_
  have : α * m e - l = α * (m e - l / α) := by field_simp
  rw [this, mul_div_assoc']
  congr 1
  rcases le_total (m e - l / α) 0 with h | h
  · rw [max_eq_right h, max_eq_right (mul_nonpos_of_nonneg_of_nonpos hα.le h), mul_zero]
  · rw [max_eq_left h, max_eq_left (mul_nonneg hα.le h)]

omit [Fintype E] [DecidableEq E] in
/-- `prop:partition`, step (8): "The function `q_i` is continuous … on `[0, max_{e∈E_i} m_e]`, …"
Here on all of `ℝ`. -/
theorem continuous_qA (Ei : Finset E) : Continuous (qA m β Ei) := by
  unfold qA
  fun_prop

omit [Fintype E] [DecidableEq E] in
/-- `prop:partition`, step (8): "The function `q_i` is … strictly decreasing on
`[0, max_{e∈E_i} m_e]`, …": every term is nonincreasing, and that of an element with the largest
reward decreases strictly there. -/
theorem strictAntiOn_qA (hβ : ∀ e, 0 < β e) {Ei : Finset E} (hEi : Ei.Nonempty) :
    StrictAntiOn (qA m β Ei) (Set.Icc 0 (Ei.sup' hEi m)) := by
  intro μ _ μ' hμ' hlt
  obtain ⟨e₀, he₀, hmax⟩ := exists_mem_eq_sup' hEi m
  have h' : μ' ≤ m e₀ := hmax ▸ hμ'.2
  refine sum_lt_sum (fun e _ => div_le_div_of_nonneg_right
    (max_le_max (by linarith) le_rfl) (hβ e).le) ⟨e₀, he₀, ?_⟩
  rw [max_eq_left (by linarith), max_eq_left (by linarith)]
  exact div_lt_div_of_pos_right (by linarith) (hβ e₀)

omit [Fintype E] [DecidableEq E] in
/-- `q_i` vanishes from the largest reward on. -/
theorem qA_eq_zero {Ei : Finset E} (hEi : Ei.Nonempty) {μ : ℝ} (hμ : Ei.sup' hEi m ≤ μ) :
    qA m β Ei μ = 0 :=
  sum_eq_zero fun e he => by
    rw [max_eq_right (by linarith [le_sup' m he]), zero_div]

omit [Fintype E] [DecidableEq E] in
/-- `q_i(0) = t(E_i)`, as `m ≥ 0`. -/
theorem qA_zero (hm : ∀ e, 0 ≤ m e) (Ei : Finset E) : qA m β Ei 0 = tA m β Ei :=
  sum_congr rfl fun e _ => by rw [sub_zero, max_eq_left (hm e)]

/-- `μ_i(α) = λ_i(α)/α`. -/
def muA (m β : E → ℝ) (Ei : Finset E) (F α : ℝ) : ℝ := lamA m β Ei F α / α

/-- The support `W_i = {e ∈ E_i | m_e > μ_i(α)}` of the response on `E_i` for `α > α_i`
(`appB-quadratic.tex:704`). -/
def WA (m β : E → ℝ) (Ei : Finset E) (F α : ℝ) : Finset E :=
  Ei.filter fun e => muA m β Ei F α < m e

omit [Fintype E] [DecidableEq E] in
theorem mem_WA {Ei : Finset E} {F α : ℝ} {e : E} :
    e ∈ WA m β Ei F α ↔ e ∈ Ei ∧ muA m β Ei F α < m e :=
  mem_filter

omit [Fintype E] [DecidableEq E] in
/-- For `α > 0`: `μ_i(α) < m_e` iff `λ_i(α) < α m_e`. -/
theorem muA_lt_iff {Ei : Finset E} {F α : ℝ} (hα : 0 < α) (e : E) :
    muA m β Ei F α < m e ↔ lamA m β Ei F α < α * m e := by
  rw [muA, div_lt_iff₀ hα, mul_comm]

section NondegeneratePart

variable {Ei : Finset E} {F : ℝ}

omit [Fintype E] [DecidableEq E] in
/-- `prop:partition`, step (7): "Dividing `s_i(λ_i(α)) = f(E_i)` by `α` shows that
`μ_i(α) := λ_i(α)/α` satisfies `q_i(μ_i(α)) = f(E_i)/α`, where
`q_i(μ) := ∑_{e∈E_i} (m_e − μ)⁺/β_e`." -/
theorem qA_muA (hβ : ∀ e, 0 < β e) (hm : ∀ e, 0 ≤ m e) (hEi : Ei.Nonempty) (hF : 0 < F)
    (ht : 0 < tA m β Ei) {α : ℝ} (hαi : F / tA m β Ei < α) :
    qA m β Ei (muA m β Ei F α) = F / α := by
  have hα : 0 < α := (div_pos hF ht).trans hαi
  obtain ⟨-, hs⟩ := lamA_spec hβ hm hEi hF ht hαi
  rw [sA_eq Ei hα] at hs
  rw [muA, eq_div_iff hα.ne', mul_comm]
  exact hs

omit [Fintype E] [DecidableEq E] in
/-- `prop:partition`, step (8): "… because `0 < λ_i(α) < α max_{e∈E_i} m_e`.": the upper bound, as
`s_i` is zero from `α max_{e ∈ E_i} m_e` on and `s_i(λ_i(α)) = f(E_i) > 0`. -/
theorem lamA_lt (hβ : ∀ e, 0 < β e) (hm : ∀ e, 0 ≤ m e) (hEi : Ei.Nonempty) (hF : 0 < F)
    (ht : 0 < tA m β Ei) {α : ℝ} (hαi : F / tA m β Ei < α) :
    lamA m β Ei F α < α * Ei.sup' hEi m := by
  have hα : 0 < α := (div_pos hF ht).trans hαi
  obtain ⟨-, hs⟩ := lamA_spec hβ hm hEi hF ht hαi
  by_contra hge
  rw [sA_eq_zero hEi hα.le (not_lt.1 hge)] at hs
  exact hF.ne' hs.symm

omit [Fintype E] [DecidableEq E] in
/-- `prop:partition`, step (8): "… `[0, max_{e∈E_i} m_e]`, which contains `μ_i(α)` because
`0 < λ_i(α) < α max_{e∈E_i} m_e`.": `0 < μ_i(α) < max_{e ∈ E_i} m_e`. -/
theorem muA_mem (hβ : ∀ e, 0 < β e) (hm : ∀ e, 0 ≤ m e) (hEi : Ei.Nonempty) (hF : 0 < F)
    (ht : 0 < tA m β Ei) {α : ℝ} (hαi : F / tA m β Ei < α) :
    muA m β Ei F α ∈ Set.Ioo 0 (Ei.sup' hEi m) := by
  have hα : 0 < α := (div_pos hF ht).trans hαi
  refine ⟨div_pos (lamA_pos hβ hm hEi hF ht hαi) hα, ?_⟩
  rw [muA, div_lt_iff₀ hα, mul_comm]
  exact lamA_lt hβ hm hEi hF ht hαi

omit [Fintype E] [DecidableEq E] in
/-- `prop:partition`, step (8): "The left-hand side depends only on `μ_i(α)`, and the right-hand
side only on `α`. As `f(E_i) > 0`, the right-hand side strictly decreases as `α` increases. The
function `q_i` is continuous and strictly decreasing on `[0, max_{e∈E_i} m_e]`, which contains
`μ_i(α)` because `0 < λ_i(α) < α max_{e∈E_i} m_e`. So when `α` increases, `q_i(μ_i(α))`
decreases, and this forces `μ_i(α)` to increase." That is, `μ_i` increases on `(α_i, ∞)`; the
sides are those of `q_i(μ_i(α)) = f(E_i)/α` (step (7)). -/
theorem strictMonoOn_muA (hβ : ∀ e, 0 < β e) (hm : ∀ e, 0 ≤ m e) (hEi : Ei.Nonempty) (hF : 0 < F)
    (ht : 0 < tA m β Ei) : StrictMonoOn (muA m β Ei F) (Set.Ioi (F / tA m β Ei)) := by
  intro α hα α' hα' hlt
  have hα0 : 0 < α := (div_pos hF ht).trans hα
  -- (8) "As `f(E_i) > 0`, the right-hand side strictly decreases as `α` increases." … "So when
  -- `α` increases, `q_i(μ_i(α))` decreases, …"
  have hq : qA m β Ei (muA m β Ei F α') < qA m β Ei (muA m β Ei F α) := by
    rw [qA_muA hβ hm hEi hF ht hα, qA_muA hβ hm hEi hF ht hα']
    exact div_lt_div_of_pos_left hF hα0 hlt
  -- (8) "… and this forces `μ_i(α)` to increase.", as "The function `q_i` is continuous and
  -- strictly decreasing on `[0, max_{e∈E_i} m_e]`, which contains `μ_i(α)` …" (`strictAntiOn_qA`,
  -- `muA_mem`)
  by_contra hge
  rw [not_lt] at hge
  have h1 := Set.Ioo_subset_Icc_self (muA_mem hβ hm hEi hF ht hα)
  have h2 := Set.Ioo_subset_Icc_self (muA_mem hβ hm hEi hF ht hα')
  have := (strictAntiOn_qA hβ hEi).antitoneOn h2 h1 hge
  linarith

/-- (Not in the paper: step (9) of `prop:partition` uses without proof that `q_i` has a continuous
inverse on `[0, max_{e ∈ E_i} m_e]`.) A continuous strictly decreasing function `q` on `[a, b]` has
an inverse `g`, `g(q(μ)) = μ` for `μ ∈ [a, b]`, that is continuous at every point of
`(q(b), q(a))`: by the intermediate value theorem `q` maps `[a, b]` onto `[q(b), q(a)]`, so `g` is
decreasing on `(q(b), q(a))` and maps it onto `(a, b)`, an open interval. -/
theorem exists_continuousAt_inverse {q : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn q (Set.Icc a b)) (hq : StrictAntiOn q (Set.Icc a b)) :
    ∃ g : ℝ → ℝ, (∀ μ ∈ Set.Icc a b, g (q μ) = μ) ∧
      ∀ y ∈ Set.Ioo (q b) (q a), ContinuousAt g y := by
  classical
  set g := Function.invFunOn q (Set.Icc a b)
  have hleft : ∀ μ ∈ Set.Icc a b, g (q μ) = μ := fun μ hμ => hq.injOn.leftInvOn_invFunOn hμ
  refine ⟨g, hleft, fun y hy => ?_⟩
  -- every `y ∈ (q(b), q(a))` is `q(μ)` for a `μ ∈ (a, b)`, and `g(y) = μ`
  have hval : ∀ y ∈ Set.Ioo (q b) (q a), g y ∈ Set.Ioo a b ∧ q (g y) = y := by
    intro y hy
    obtain ⟨μ, hμ, rfl⟩ := intermediate_value_Icc' hab hc (Set.Ioo_subset_Icc_self hy)
    rw [hleft μ hμ]
    refine ⟨⟨lt_of_le_of_ne hμ.1 ?_, lt_of_le_of_ne hμ.2 ?_⟩, rfl⟩
    · rintro rfl
      exact lt_irrefl _ hy.2
    · rintro rfl
      exact lt_irrefl _ hy.1
  -- `−g` is nondecreasing on `(q(b), q(a))`
  have hmono : MonotoneOn (fun y => -g y) (Set.Ioo (q b) (q a)) := by
    intro y₁ h₁ y₂ h₂ hle
    simp only [neg_le_neg_iff]
    by_contra hlt
    rw [not_le] at hlt
    have := hq (Set.Ioo_subset_Icc_self (hval y₁ h₁).1) (Set.Ioo_subset_Icc_self (hval y₂ h₂).1)
      hlt
    rw [(hval y₁ h₁).2, (hval y₂ h₂).2] at this
    linarith
  -- and maps it onto `(−b, −a)`
  have himage : (fun y => -g y) '' Set.Ioo (q b) (q a) = Set.Ioo (-b) (-a) := by
    ext ν
    constructor
    · rintro ⟨y, hy, rfl⟩
      have := (hval y hy).1
      exact ⟨by linarith [this.2], by linarith [this.1]⟩
    · intro hν
      have hμ : -ν ∈ Set.Icc a b := ⟨by linarith [hν.2], by linarith [hν.1]⟩
      refine ⟨q (-ν), ⟨hq hμ (Set.right_mem_Icc.2 hab) (by linarith [hν.1]),
        hq (Set.left_mem_Icc.2 hab) hμ (by linarith [hν.2])⟩, ?_⟩
      simp only [hleft (-ν) hμ, neg_neg]
  have hmem : -g y ∈ Set.Ioo (-b) (-a) := by
    have := (hval y hy).1
    exact ⟨by linarith [this.2], by linarith [this.1]⟩
  have hcont : ContinuousAt (fun y => -g y) y :=
    continuousAt_of_monotoneOn_of_image_mem_nhds hmono (Ioo_mem_nhds hy.1 hy.2)
      (himage ▸ Ioo_mem_nhds hmem.1 hmem.2)
  have h2 : ContinuousAt (fun y => -(-g y)) y := hcont.neg
  simp only [neg_neg] at h2
  exact h2

omit [Fintype E] [DecidableEq E] in
/-- `prop:partition`, step (9): "As `q_i` has a continuous inverse on this interval,
`μ_i(α) = q_i⁻¹(f(E_i)/α)` is moreover continuous in `α`." The interval is
`[0, max_{e ∈ E_i} m_e]` (`exists_continuousAt_inverse`), and the continuity holds at every
`α > α_i`, where `f(E_i)/α` lies in `(0, t(E_i)) = (q_i(max_{e ∈ E_i} m_e), q_i(0))`. -/
theorem continuousAt_muA (hβ : ∀ e, 0 < β e) (hm : ∀ e, 0 ≤ m e) (hEi : Ei.Nonempty) (hF : 0 < F)
    (ht : 0 < tA m β Ei) {α₀ : ℝ} (hα₀ : F / tA m β Ei < α₀) : ContinuousAt (muA m β Ei F) α₀ := by
  set M := Ei.sup' hEi m
  have hα₀pos : 0 < α₀ := (div_pos hF ht).trans hα₀
  have hM : 0 ≤ M := (muA_mem hβ hm hEi hF ht hα₀).1.le.trans (muA_mem hβ hm hEi hF ht hα₀).2.le
  obtain ⟨g, hg, hgc⟩ := exists_continuousAt_inverse hM
    (continuous_qA (m := m) (β := β) Ei).continuousOn (strictAntiOn_qA hβ hEi)
  -- `μ_i(α) = q_i⁻¹(f(E_i)/α)` for `α > α_i`
  have heq : ∀ᶠ α in 𝓝 α₀, g (F / α) = muA m β Ei F α := by
    filter_upwards [eventually_gt_nhds hα₀] with α hα
    rw [← qA_muA hβ hm hEi hF ht hα, hg _ (Set.Ioo_subset_Icc_self (muA_mem hβ hm hEi hF ht hα))]
  -- `f(E_i)/α₀ ∈ (q_i(max m_e), q_i(0)) = (0, t(E_i))`
  have hy : F / α₀ ∈ Set.Ioo (qA m β Ei M) (qA m β Ei 0) := by
    rw [qA_eq_zero hEi le_rfl, qA_zero hm Ei]
    refine ⟨div_pos hF hα₀pos, (div_lt_iff₀ hα₀pos).2 ?_⟩
    rw [mul_comm]
    exact (div_lt_iff₀ ht).1 hα₀
  have hc : ContinuousAt (fun α => g (F / α)) α₀ :=
    (hgc _ hy).comp (f := fun α => F / α) (continuousAt_const.div continuousAt_id hα₀pos.ne')
  exact hc.congr heq

/-- The shares `α > α_i` at which `μ_i(α)` reaches the reward `m_e` of an element `e ∈ E_i`: the
element `e` lies in `W_i` before this share and not after it, so `W_i` loses `e` there. These are
the only shares at which `W_i` changes (`eventually_WA_eq`). -/
def Wchanges (m β : E → ℝ) (Ei : Finset E) (F : ℝ) : Set ℝ :=
  {α | F / tA m β Ei < α ∧ ∃ e ∈ Ei, muA m β Ei F α = m e}

omit [Fintype E] [DecidableEq E] in
/-- `prop:partition`, step (10) (`appB-quadratic.tex:702-706`): "As `μ_i(α)` increases and stays
below `max_{e∈E_i} m_e`, the support `W_i := {e ∈ E_i : m_e > μ_i(α)}` only loses elements, never
those with the largest reward, so it changes at most `|E_i| − 1` times." At a share of
`Wchanges`, `W_i` loses an element `e` with `m_e = μ_i(α)`; as `μ_i` increases, each element is
lost at one share at most, and as `μ_i` stays below `max_{e ∈ E_i} m_e`, the lost elements do not
have the largest reward. -/
theorem ncard_Wchanges_le (hβ : ∀ e, 0 < β e) (hm : ∀ e, 0 ≤ m e) (hEi : Ei.Nonempty)
    (hF : 0 < F) (ht : 0 < tA m β Ei) :
    (Wchanges m β Ei F).Finite ∧ (Wchanges m β Ei F).ncard ≤ Ei.card - 1 := by
  classical
  set M := Ei.sup' hEi m
  -- the element lost at a share of `Wchanges`
  have : Nonempty E := ⟨hEi.choose⟩
  choose! lost hlostE hlostm using fun α (hα : α ∈ Wchanges m β Ei F) => hα.2
  -- it does not have the largest reward, as `μ_i(α) < max_{e ∈ E_i} m_e`
  have hmaps : Set.MapsTo lost (Wchanges m β Ei F)
      ((Ei.filter fun e => m e < M : Finset E) : Set E) := by
    intro α hα
    refine mem_coe.2 (mem_filter.2 ⟨hlostE α hα, ?_⟩)
    rw [← hlostm α hα]
    exact (muA_mem hβ hm hEi hF ht hα.1).2
  -- each element is lost at one share at most, as `μ_i(α)` increases
  have hinj : Set.InjOn lost (Wchanges m β Ei F) := by
    intro α hα α' hα' heq
    have : muA m β Ei F α = muA m β Ei F α' := by
      rw [hlostm α hα, hlostm α' hα']
      exact congrArg m heq
    exact (strictMonoOn_muA hβ hm hEi hF ht).injOn hα.1 hα'.1 this
  -- the elements without the largest reward are at most `|E_i| − 1`
  have hcard : (Ei.filter fun e => m e < M).card ≤ Ei.card - 1 := by
    obtain ⟨e₀, he₀, hmax⟩ := exists_mem_eq_sup' hEi m
    have hsub : Ei.filter (fun e => m e < M) ⊆ Ei.erase e₀ := fun e he => by
      obtain ⟨heE, hlt⟩ := mem_filter.1 he
      refine mem_erase.2 ⟨fun h => ?_, heE⟩
      rw [h, ← hmax] at hlt
      exact lt_irrefl _ hlt
    exact (card_le_card hsub).trans_eq (card_erase_of_mem he₀)
  have hfin : (Wchanges m β Ei F).Finite :=
    Set.Finite.of_finite_image ((finite_toSet _).subset (Set.image_subset_iff.2 hmaps)) hinj
  refine ⟨hfin, (Set.ncard_le_ncard_of_injOn _ hmaps hinj (finite_toSet _)).trans ?_⟩
  rw [Set.ncard_coe_finset]
  exact hcard

omit [Fintype E] [DecidableEq E] in
/-- `prop:partition`, step (10): "Between these changes, `W_i` is constant.": away from the shares
of `Wchanges`, `W_i` is constant near `α₀`, as `μ_i` is continuous (step (9)). -/
theorem eventually_WA_eq (hβ : ∀ e, 0 < β e) (hm : ∀ e, 0 ≤ m e) (hEi : Ei.Nonempty) (hF : 0 < F)
    (ht : 0 < tA m β Ei) {α₀ : ℝ} (hα₀ : F / tA m β Ei < α₀) (hW : α₀ ∉ Wchanges m β Ei F) :
    ∀ᶠ α in 𝓝 α₀, WA m β Ei F α = WA m β Ei F α₀ := by
  have hne : ∀ e ∈ Ei, muA m β Ei F α₀ ≠ m e := fun e he h => hW ⟨hα₀, e, he, h⟩
  have hcont := continuousAt_muA hβ hm hEi hF ht hα₀
  have hev : ∀ᶠ α in 𝓝 α₀, ∀ e ∈ Ei, (muA m β Ei F α < m e ↔ muA m β Ei F α₀ < m e) := by
    refine (eventually_all_finset Ei).2 fun e he => ?_
    rcases lt_or_gt_of_ne (hne e he) with h | h
    · filter_upwards [hcont.eventually (gt_mem_nhds h)] with α hα
      exact ⟨fun _ => h, fun _ => hα⟩
    · filter_upwards [hcont.eventually (lt_mem_nhds h)] with α hα
      exact ⟨fun h' => absurd h' (not_lt.2 hα.le), fun h' => absurd h' (not_lt.2 h.le)⟩
  filter_upwards [hev] with α hα
  ext e
  simp only [WA, mem_filter]
  exact ⟨fun ⟨he, h⟩ => ⟨he, (hα e he).1 h⟩, fun ⟨he, h⟩ => ⟨he, (hα e he).2 h⟩⟩

/-! ### Step (11): the response between the changes of `W_i` -/

omit [Fintype E] [DecidableEq E] in
/-- `prop:partition`, step (11): "As `x_e = (α m_e − λ_i(α))/β_e` for `e ∈ W_i` and `x_e = 0` for
the other elements of `E_i`, the equation `x(E_i) = f(E_i)` reads
`α t(W_i) − λ_i(α) β⁻¹(W_i) = f(E_i)`. Hence `λ_i(α) = (α t(W_i) − f(E_i))/β⁻¹(W_i)` …", with
`W_i = W_i(α)`. -/
theorem lamA_eq_of_WA (hβ : ∀ e, 0 < β e) (hm : ∀ e, 0 ≤ m e) (hEi : Ei.Nonempty) (hF : 0 < F)
    (ht : 0 < tA m β Ei) {α : ℝ} (hαi : F / tA m β Ei < α) :
    lamA m β Ei F α = (α * ∑ e ∈ WA m β Ei F α, m e / β e - F) /
      ∑ e ∈ WA m β Ei F α, 1 / β e := by
  have hα : 0 < α := (div_pos hF ht).trans hαi
  obtain ⟨-, hs⟩ := lamA_spec hβ hm hEi hF ht hαi
  set l := lamA m β Ei F α
  set W := WA m β Ei F α
  -- On `W_i`, `α m_e > λ_i(α)`; off `W_i`, `α m_e ≤ λ_i(α)` and `x_e = 0`.
  have hmem : ∀ e, e ∈ W ↔ e ∈ Ei ∧ l < α * m e := by
    intro e
    rw [mem_WA, muA_lt_iff hα]
  have hsW : sA m β Ei α l = α * ∑ e ∈ W, m e / β e - l * ∑ e ∈ W, 1 / β e := by
    unfold sA xLam
    rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_filter_add_sum_filter_not Ei
      (fun e => l < α * m e)]
    rw [sum_eq_zero (s := Ei.filter fun e => ¬ l < α * m e) fun e he => by
      rw [max_eq_right (by linarith [not_lt.1 (mem_filter.1 he).2]), zero_div], add_zero]
    have hWeq : W = Ei.filter fun e => l < α * m e := by
      ext e
      rw [hmem, mem_filter]
    rw [hWeq]
    refine sum_congr rfl fun e he => ?_
    rw [max_eq_left (by linarith [(mem_filter.1 he).2])]
    field_simp [(hβ e).ne']
  have hWne : 0 < ∑ e ∈ W, 1 / β e := by
    obtain ⟨e₀, he₀, hmax⟩ := exists_mem_eq_sup' hEi m
    refine sum_pos (fun e _ => one_div_pos.2 (hβ e)) ⟨e₀, ?_⟩
    rw [mem_WA]
    exact ⟨he₀, hmax ▸ (muA_mem hβ hm hEi hF ht hαi).2⟩
  rw [eq_div_iff hWne.ne']
  linarith

end NondegeneratePart

omit [Fintype E] in
/-- `prop:partition`, steps (2)-(11) on one part: the response on `E_i` is affine near every share
`α₀ > 0` other than `α_i` and the shares of `Wchanges`: zero (step (2)), `α t_e` below `α_i`
(step (3)), and above `α_i`, with `W_i` constant near `α₀` (step (10)),
`x_e = (α m_e − λ_i(α))/β_e` on `W_i` and `x_e = 0` off `W_i` with the affine `λ_i(α)` of
step (11). -/
theorem affineNear_partResp (hβ : ∀ e, 0 < β e) (hm : ∀ e, 0 ≤ m e) {Ei : Finset E}
    (hEi : Ei.Nonempty) {F : ℝ} (hF : 0 ≤ F) {α₀ : ℝ}
    (hnot : ¬ (F = 0 ∨ tA m β Ei = 0) → α₀ ≠ F / tA m β Ei ∧ α₀ ∉ Wchanges m β Ei F) :
    ∃ ε > 0, ∃ a b : E → ℝ, ∀ α ∈ Set.Ioo (α₀ - ε) (α₀ + ε), ∀ e ∈ Ei,
      partResp m β Ei F α e = a e + α * b e := by
  by_cases hdeg : F = 0 ∨ tA m β Ei = 0
  · -- (2) "If `f(E_i) = 0` or `t(E_i) = 0`, the response is zero on `E_i`, …"
    refine ⟨1, one_pos, 0, 0, fun α _ e _ => ?_⟩
    simp only [partResp, hdeg, ite_true, Pi.zero_apply, mul_zero, add_zero]
  obtain ⟨hne, hW⟩ := hnot hdeg
  push Not at hdeg
  have hF0 : 0 < F := lt_of_le_of_ne hF (Ne.symm hdeg.1)
  have ht : 0 < tA m β Ei :=
    lt_of_le_of_ne (sum_nonneg fun e _ => div_nonneg (hm e) (hβ e).le) (Ne.symm hdeg.2)
  have hdeg' : ¬ (F = 0 ∨ tA m β Ei = 0) := by
    push Not
    exact hdeg
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- (3) "For `α ≤ α_i`, the unconstrained response `x*_e = α t_e`, `e ∈ E_i`, is feasible, …"
    -- Here near a share `α₀ < α_i`.
    refine ⟨F / tA m β Ei - α₀, sub_pos.2 hlt, 0, fun e => m e / β e, fun α hα e _ => ?_⟩
    have hαi : α ≤ F / tA m β Ei := by linarith [hα.2]
    simp only [partResp, hdeg', hαi, ite_true, ite_false, Pi.zero_apply, zero_add]
  · -- (10) "Between these changes, `W_i` is constant." (11) "Hence
    -- `λ_i(α) = (α t(W_i) − f(E_i))/β⁻¹(W_i)` is affine in `α`, and so is the response."
    -- Here near a share `α₀ > α_i` that is not in `Wchanges`.
    have hev := (eventually_WA_eq hβ hm hEi hF0 ht hgt hW).and (eventually_gt_nhds hgt)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
    set W := WA m β Ei F α₀
    set tW := ∑ e ∈ W, m e / β e
    set bW := ∑ e ∈ W, 1 / β e
    refine ⟨ε, hε, fun e => if e ∈ W then F / (bW * β e) else 0,
      fun e => if e ∈ W then (m e - tW / bW) / β e else 0, fun α hα e he => ?_⟩
    have hαd : dist α α₀ < ε := by
      rw [Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith [hα.1, hα.2]
    obtain ⟨hWα, hαi⟩ := hball hαd
    have hαi' : ¬ α ≤ F / tA m β Ei := not_le.2 hαi
    have hlam := lamA_eq_of_WA hβ hm hEi hF0 ht hαi
    rw [hWα] at hlam
    have hα0 : 0 < α := (div_pos hF0 ht).trans hαi
    have hbW : 0 < bW := by
      obtain ⟨e₀, he₀, hmax⟩ := exists_mem_eq_sup' hEi m
      refine sum_pos (fun e _ => one_div_pos.2 (hβ e)) ⟨e₀, ?_⟩
      rw [← hWα, mem_WA]
      exact ⟨he₀, hmax ▸ (muA_mem hβ hm hEi hF0 ht hαi).2⟩
    simp only [partResp, hdeg', hαi', ite_false]
    have hmemW : e ∈ W ↔ lamA m β Ei F α < α * m e := by
      rw [← hWα, mem_WA, muA_lt_iff hα0]
      exact and_iff_right he
    unfold xLam
    by_cases heW : e ∈ W
    · have h1 := hmemW.1 heW
      have hlam' : lamA m β Ei F α = (α * tW - F) / bW := hlam
      simp only [heW, ite_true]
      rw [max_eq_left (by linarith), hlam']
      field_simp
      ring
    · have h1 : α * m e ≤ lamA m β Ei F α := not_lt.1 fun h => heW (hmemW.2 h)
      simp only [heW, ite_false, mul_zero, add_zero]
      rw [max_eq_right (by linarith), zero_div]

/-! ### Step (12): the count -/

/-- The shares near which the response on `E_i` may fail to be affine: `α_i` and the shares of
`Wchanges`, for a part with `f(E_i), t(E_i) > 0`. -/
def partBreaks (m β : E → ℝ) (Ei : Finset E) (F : ℝ) : Set ℝ :=
  if F = 0 ∨ tA m β Ei = 0 then ∅ else insert (F / tA m β Ei) (Wchanges m β Ei F)

omit [Fintype E] [DecidableEq E] in
/-- `prop:partition`, step (12): "Including `α_i` gives at most `|E_i|` breakpoints on `E_i`, …"
Here the shares `α_i` and those of `Wchanges`, which contain these breakpoints. -/
theorem ncard_partBreaks_le (hβ : ∀ e, 0 < β e) (hm : ∀ e, 0 ≤ m e) {Ei : Finset E}
    (hEi : Ei.Nonempty) {F : ℝ} (hF : 0 ≤ F) :
    (partBreaks m β Ei F).Finite ∧ (partBreaks m β Ei F).ncard ≤ Ei.card := by
  unfold partBreaks
  by_cases hdeg : F = 0 ∨ tA m β Ei = 0
  · simp [hdeg]
  simp only [hdeg, ite_false]
  push Not at hdeg
  have hF0 : 0 < F := lt_of_le_of_ne hF (Ne.symm hdeg.1)
  have ht : 0 < tA m β Ei :=
    lt_of_le_of_ne (sum_nonneg fun e _ => div_nonneg (hm e) (hβ e).le) (Ne.symm hdeg.2)
  obtain ⟨hfin, hcard⟩ := ncard_Wchanges_le hβ hm hEi hF0 ht
  refine ⟨hfin.insert _, (Set.ncard_insert_le _ _).trans ?_⟩
  have := hEi.card_pos
  omega

/-- **`prop:partition`** (Proposition B.18, `stoc-sections/appB-quadratic.tex:649-712`): for every
partition polymatroid, `B ≤ n`. The STOC version's steps (see the module docstring): (1) the
constraint sets `E_i` cover `E`, and the response decomposes over these parts
(`exists_mem_of_indepPoly_eq`, `bestResponse_eq_partResp`); (2) a part with `f(E_i) = 0` or
`t(E_i) = 0` has zero response;
(3) for `α ≤ α_i` the unconstrained response `α t_e` is feasible and hence optimal; (4)-(6) for
`α > α_i`, `s_i` decreases strictly, there is exactly one `λ_i(α) ≥ 0` with `s_i(λ_i(α)) = f(E_i)`,
and `x_e = (α m_e − λ_i(α))⁺/β_e` is optimal on `E_i`; (7)-(9) `μ_i(α) = λ_i(α)/α` solves
`q_i(μ_i(α)) = f(E_i)/α`, increases and is continuous; (10) the support `W_i` changes at most
`|E_i| − 1` times; (11) between these changes the response is affine (`affineNear_partResp`);
(12) including `α_i`, at most `|E_i|` breakpoints on `E_i`, hence at most `|E_1| + ⋯ + |E_k| = n`
overall. -/
theorem partition_breakpoints (hf : IsRankFunction f) (hpart : IsPartitionPolymatroid f)
    (hm : ∀ e, 0 ≤ m e) (hβ : ∀ e, 0 < β e) :
    (breakpoints (bestResponse f m β)).Finite ∧
      (breakpoints (bestResponse f m β)).ncard ≤ Fintype.card E := by
  -- (1) "Let `E_1, …, E_k` be the constraint sets of the partition polymatroid, so that
  -- `P₊(f) = {x ≥ 0 : x(E_i) ≤ f(E_i) for i = 1, …, k}` with pairwise disjoint sets `E_i`."
  obtain ⟨L, hne, hdisj, hP⟩ := hpart
  -- (1) "They cover `E` since `P₊(f)` is bounded, so they partition `E`, …"
  have hcov : ∀ e, ∃ Ei ∈ L, e ∈ Ei := exists_mem_of_indepPoly_eq hf hP
  choose part hpartL hmem using hcov
  have hU : L.biUnion id = univ :=
    eq_univ_iff_forall.2 fun e => mem_biUnion.2 ⟨part e, hpartL e, hmem e⟩
  -- (12) "Including `α_i` gives at most `|E_i|` breakpoints on `E_i`, …"
  -- Every breakpoint is one of the shares `partBreaks` of some part `E_i`.
  have hsub : breakpoints (bestResponse f m β) ⊆ ⋃ Ei ∈ L, partBreaks m β Ei (f Ei) := by
    rintro α₀ ⟨hα₀, hnot⟩
    by_contra hout
    apply hnot
    have hnotE : ∀ Ei ∈ L, ¬ (f Ei = 0 ∨ tA m β Ei = 0) →
        α₀ ≠ f Ei / tA m β Ei ∧ α₀ ∉ Wchanges m β Ei (f Ei) := by
      intro Ei hEi hdeg
      have hα₀E : α₀ ∉ partBreaks m β Ei (f Ei) := fun h => hout (Set.mem_biUnion hEi h)
      simp only [partBreaks, hdeg, ite_false, Set.mem_insert_iff, not_or] at hα₀E
      exact hα₀E
    have key : ∀ Ei ∈ L, ∃ ε > 0, ∃ a b : E → ℝ, ∀ α ∈ Set.Ioo (α₀ - ε) (α₀ + ε), ∀ e ∈ Ei,
        partResp m β Ei (f Ei) α e = a e + α * b e := fun Ei hEi =>
      affineNear_partResp hβ hm (hne Ei hEi) (hf.nonneg Ei) (hnotE Ei hEi)
    choose! εE hεE a b hab using key
    -- A common neighborhood for all parts, inside `(0, ∞)`.
    set ε := (insert α₀ (L.image εE)).min' (insert_nonempty _ _)
    have hε : 0 < ε := by
      rw [Finset.lt_min'_iff]
      intro y hy
      rcases mem_insert.1 hy with rfl | hy
      · exact hα₀
      · obtain ⟨Ei, hEi, rfl⟩ := mem_image.1 hy
        exact hεE Ei hEi
    have hεα₀ : ε ≤ α₀ := min'_le _ _ (mem_insert_self _ _)
    have hεE' : ∀ Ei ∈ L, ε ≤ εE Ei := fun Ei hEi =>
      min'_le _ _ (mem_insert_of_mem (mem_image_of_mem _ hEi))
    refine ⟨ε, hε, fun e => a (part e) e, fun e => b (part e) e, fun α hα => ?_⟩
    have hα0 : 0 ≤ α := by linarith [hα.1]
    -- (1) "… and the response decomposes over these parts."
    -- On each part, the response is affine near `α₀` (steps (2)-(11)).
    rw [bestResponse_eq_partResp hf hβ hm hne hdisj hP hpartL hmem hα0]
    funext e
    have hεe := hεE' (part e) (hpartL e)
    exact hab (part e) (hpartL e) α ⟨by linarith [hα.1], by linarith [hα.2]⟩ e (hmem e)
  -- (12) "… hence at most `|E_1| + ⋯ + |E_k| = n` overall."
  obtain ⟨hfin, hcard⟩ := finite_ncard_biUnion_le L (fun Ei => partBreaks m β Ei (f Ei)) card
    fun Ei hEi => ncard_partBreaks_le hβ hm (hne Ei hEi) (hf.nonneg Ei)
  refine ⟨hfin.subset hsub, (Set.ncard_le_ncard hsub hfin).trans (hcard.trans ?_)⟩
  have := card_biUnion hdisj
  simp only [id] at this
  rw [← this, hU, card_univ]

end

end Stoc
