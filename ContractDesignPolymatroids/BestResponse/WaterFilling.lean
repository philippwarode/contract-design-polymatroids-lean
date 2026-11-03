-- stamp r10 2026-11-03
import Mathlib
import ContractDesignPolymatroids.BestResponse.LevelSets
import ContractDesignPolymatroids.Preliminaries.Counted
import ContractDesignPolymatroids.Preliminaries.CountedTime

/-!
# The water-filling algorithm for a fixed share

The STOC version, Section 3 (`stoc-sections/05-best-response.tex`), Theorem `thm:waterfilling`, with
the construction and its analysis in Appendix B.1 (`sec:A-bestresponse`,
`stoc-sections/appB-quadratic.tex:36-199`): for quadratic costs, water-filling computes the best
response `x*(α)`. The file follows the STOC version's construction and proofs step by step.

The construction (`appB-quadratic.tex:36-83`), in namespace `Stoc.WaterFilling`:
* `hatE` is `Ê`, `maxTight` is the maximal tight set `T(x)`, `vS β S` is `v^S`, and `dmax f β x S`
  is `d(x, S)`, defined as the maximum of (`eq:A-dmax`); its formula as a minimum is `dmax_spec`,
  and `maxTight_dmax_meets` is the sentence after (`eq:A-dmax`) that `T(x + d(x, S) v^S)` meets `S`;
* a state is the pair `(x, Y)` of the point and the saturated set (`State`); `level` is the water
  level `λ` and `active` the active set `S*` (`eq:A-level`), `admLevel` the admission level `λ'`,
  `stepSize` the step `Δ`, and `step` gives `(x⁺, Y⁺)` (`eq:A-step`); `run` repeats the step while
  `λ > 0`, `iters` is the number of steps, `waterFill` the terminal point `x̄`
  (`alg:waterfilling`), and `blockLevel` the blocking level `λ̄_e`;
* a submodular minimization returns the maximal minimizer (`sfmArg`), as in the counts of
  `thm:waterfilling` (`appB-quadratic.tex:181`). The algorithm runs on real numbers and is a
  mathematical function: `step` takes `d(x, S*)` and `T(x⁺)` as values, which the ray computation
  of line 3 returns (`alg_step`); counting minimizations means counting the rounds of one ray
  computation per step (`rayCalls`, summed in `oracleCalls`).

The results:
* `lem:ray`: `ray`, for the discrete Newton method `d0`, `tilde`, `dnext`, `dIter`, `rayRounds`,
  `rayStep`, `rayArg`, with the counts `rayCalls` and `rayEvals` and the counted ray computation
  `rayC` (`rayC_spec`);
* `alg:waterfilling`: `waterFill`, with `alg_step` for its lines 3-4;
* `lem:wfstructure`: `wfstructure`, with the induction `Inv`, `inv_init`, `Inv.active_waiting`,
  `inv_step`, `inv_run` and the count `steps_le`, `iters_spec`;
* `thm:waterfilling`: `waterfilling`, with `waterFill_levelSet_tight` for the steps (1)-(4) of the
  part of the proof that shows that water-filling ends at the best response, the counts
  `oracleCalls` and `fEvals`, and the counted water-filling `waterFillC` (`waterFillC_spec`).

The operation counts (not in the paper: the paper counts in prose). `rayCalls = K + 1` is the
number of calls of the ray computation, and `rayEvals = |S| + K + 1` and `fEvals`, its sum over the
steps, are the paper's accounting of the evaluations of `f` (one after each call and the `|S|`
singleton evaluations of the initialization, step (5) of the proof of `lem:ray`). The counted ray
computation `rayC` and the counted water-filling `waterFillC` perform the steps of `lem:ray` and
of `alg:waterfilling` in the cost model of `Stoc.Counted`, which counts minimizations, evaluations
of `f` and arithmetic operations (comparisons included). They return what `rayStep`, `rayArg` and
`waterFill` define, with exactly `rayCalls` and `oracleCalls` minimizations and `rayEvals` and
`fEvals` evaluations of `f`, and at most `4|S| + (|S| + 1)(3|Ê| + 5)` and `6n³ + 56n² + 29n + 2`
further arithmetic operations: the `𝒪(n|S|)` of `lem:ray` and the `𝒪(n³)` (with the `𝒪(n)` work
per step) of `thm:waterfilling`.

The running time of `thm:waterfilling` (`waterFillC_time`): its proof derives it from the counts
with the time of one minimization by the algorithm of Iwata and Orlin [IO09], which is cited; the
Lean takes that time bound as a hypothesis (`Counted.sfmTime`, in
`ContractDesignPolymatroids/Preliminaries/CountedTime.lean`) and proves the time
`(6 + 4C₁) n⁷ lg n · FO + (93 + 4C₁(C₂ + 1)) n⁸ lg n` of `waterFillC`, `lg n = ⌈log₂ n⌉ + 1`, from
its counts (`oracleCalls_fEvals_le`).

Added steps (not in the paper, each marked in its docstring): `sfmArg_min` (the minimizers are
closed under union, so the maximal minimizer is one), `dmax_spec` (the formula of `eq:A-dmax`),
`gd_submodular`, `gd_tilde_nonpos`, `run_x_eq_zero` and `marg_eq_zero_of_notMem` (the elements
outside `Ê`), and the inductions over the steps that the paper leaves implicit: `run_Y_subset`
(the saturated sets lie in `Ê`), `Y_subset_of_nested` and `Y_subset_final` (nested saturated sets
over several steps), `level_le_of_le` and `levelEnd_antitone` (the level does not increase over
several steps), and `x_eq_of_mem_Y` (the coordinates of a saturated set do not change over all
later steps).

Taken over on 2026-10-20 from `Paper/FixedShare/WaterFilling.lean` (the paper at Overleaf f035b19)
for the STOC version (`stoc.tex`); reworked on 2026-10-25 to follow the STOC version's construction
and proofs step by step. Adapted on 2026-11-02 to Max Klimm's final STOC version (repository
429ca68), whose `thm:waterfilling` states a running time: `waterfilling` keeps the counts of its
proof, and the paragraph on computational conventions of Section 2 is gone (`sfmArg`). Extended on
2026-11-03 with the counted programs `rayC` and `waterFillC`, which prove the arithmetic operations
of `lem:ray` and `thm:waterfilling` and leave their proofs as they were.
-/

namespace Stoc

namespace WaterFilling

open Finset

variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ### The minimization oracle

Section 3 (`05-best-response.tex:23`): "we use the algorithm of Iwata and Orlin [IO09], which
returns the maximal minimizer"; the proof of `thm:waterfilling` (`appB-quadratic.tex:181`):
"Throughout our operation counts, a submodular minimization returns the unique maximal minimizer"
(`sfmArg`). That the maximal minimizer, the union of all minimizers, is one, as the minimizers of a
submodular function are closed under union, is `sfmArg_min` (not in the paper). The algorithm of
Iwata and Orlin and its running time are not formalised. -/

/-- The minimum of `g` over the subsets of `D`. -/
noncomputable def sfmVal (g : Finset E → ℝ) (D : Finset E) : ℝ :=
  D.powerset.inf' ⟨∅, empty_mem_powerset D⟩ g

/-- The maximal minimizer of `g` over the subsets of `D`, the union of all minimizers: the set the
oracle returns. -/
noncomputable def sfmArg (g : Finset E → ℝ) (D : Finset E) : Finset E :=
  (D.powerset.filter fun S => g S = sfmVal g D).sup id

omit [Fintype E] [DecidableEq E] in
lemma sfmVal_le (g : Finset E → ℝ) {D S : Finset E} (hS : S ⊆ D) : sfmVal g D ≤ g S :=
  inf'_le g (mem_powerset.2 hS)

omit [Fintype E] [DecidableEq E] in
lemma exists_sfmVal (g : Finset E → ℝ) (D : Finset E) : ∃ S ⊆ D, g S = sfmVal g D := by
  obtain ⟨S, hS, h⟩ := exists_mem_eq_inf' (⟨∅, empty_mem_powerset D⟩ : D.powerset.Nonempty) g
  exact ⟨S, mem_powerset.1 hS, h.symm⟩

omit [Fintype E] in
lemma sfmArg_subset (g : Finset E → ℝ) (D : Finset E) : sfmArg g D ⊆ D := by
  unfold sfmArg
  refine Finset.sup_le fun S hS => ?_
  exact mem_powerset.1 (mem_filter.1 hS).1

omit [Fintype E] in
/-- Every minimizer is contained in the maximal minimizer. -/
lemma subset_sfmArg (g : Finset E → ℝ) {D S : Finset E} (hS : S ⊆ D)
    (hmin : g S = sfmVal g D) : S ⊆ sfmArg g D := by
  unfold sfmArg
  exact le_sup (f := id) (mem_filter.2 ⟨mem_powerset.2 hS, hmin⟩)

omit [Fintype E] in
/-- For a submodular `g`, the union of all minimizers is a minimizer. (Not in the paper: the STOC
version uses without proof that a submodular function has a unique maximal minimizer,
`stoc-sections/05-best-response.tex:23` and `appB-quadratic.tex:181`, as its minimizers are closed
under union.) -/
lemma sfmArg_min {g : Finset E → ℝ} (hg : Submodular g) (D : Finset E) :
    g (sfmArg g D) = sfmVal g D := by
  set μ := sfmVal g D
  -- A union of minimizers is a subset of `D`, and it is empty or a minimizer.
  have key : sfmArg g D ⊆ D ∧ (sfmArg g D = ∅ ∨ g (sfmArg g D) = μ) := by
    unfold sfmArg
    refine Finset.sup_induction (p := fun T => T ⊆ D ∧ (T = ∅ ∨ g T = μ))
      ⟨empty_subset D, Or.inl rfl⟩ ?_ ?_
    · rintro A ⟨hAD, hA⟩ B ⟨hBD, hB⟩
      refine ⟨union_subset hAD hBD, ?_⟩
      rcases hA with rfl | hA
      · simpa using hB
      rcases hB with rfl | hB
      · simpa using Or.inr hA
      right
      have h1 := hg A B
      have h2 := sfmVal_le g (inter_subset_left.trans hAD : A ∩ B ⊆ D)
      have h3 := sfmVal_le g (union_subset hAD hBD)
      show g (A ∪ B) = μ
      linarith
    · intro S hS
      obtain ⟨h1, h2⟩ := mem_filter.1 hS
      exact ⟨mem_powerset.1 h1, Or.inr h2⟩
  rcases key.2 with h | h
  · obtain ⟨S, hSD, hS⟩ := exists_sfmVal g D
    have hS0 : S = ∅ := subset_empty.1 (h ▸ subset_sfmArg g hSD hS)
    rw [h, ← hS0, hS]
  · exact h

/-! ### The construction (`appB-quadratic.tex:36-55`) -/

section Construction

variable (f : Finset E → ℝ) (m β : E → ℝ) (α : ℝ)

/-- The hypotheses of Appendix B.1 (`alg:waterfilling`, "Require"): `f` is a rank function,
`β > 0`, `m ≥ 0` and `α ≥ 0`. The algorithm's other inputs, "a value oracle for `f` and submodular
minimization returning the maximal minimizer", are `f` itself and `sfmArg`. -/
structure Hyp (f : Finset E → ℝ) (m β : E → ℝ) (α : ℝ) : Prop where
  rank : IsRankFunction f
  beta : ∀ e, 0 < β e
  reward : ∀ e, 0 ≤ m e
  share : 0 ≤ α

/-- `Ê := {e ∈ E : α m_e > 0}`, the elements with positive initial marginals
(`appB-quadratic.tex:37-38`). -/
noncomputable def hatE : Finset E := univ.filter fun e => 0 < α * m e

/-- `T(x) := ⋃_{S ⊆ Ê, x(S) = f(S)} S`, the maximal tight subset of `Ê`
(`appB-quadratic.tex:41-45`). -/
noncomputable def maxTight (x : E → ℝ) : Finset E :=
  ((hatE m α).powerset.filter fun S => ∑ e ∈ S, x e = f S).sup id

/-- `v^S_e := β_e⁻¹` for `e ∈ S` and `v^S_e := 0` otherwise (`appB-quadratic.tex:46-47`). -/
noncomputable def vS (S : Finset E) : E → ℝ := fun e => if e ∈ S then (β e)⁻¹ else 0

/-- `d(x, S) := max {d ≥ 0 : x + d v^S ∈ P₊(f)}`, the first expression of (`eq:A-dmax`). The
maximum exists for `x ∈ P₊(f)` vanishing outside `Ê` and `∅ ≠ S ⊆ Ê` (`dmax_spec`). -/
noncomputable def dmax (x : E → ℝ) (S : Finset E) : ℝ :=
  sSup {d : ℝ | 0 ≤ d ∧ x + d • vS β S ∈ indepPoly f}

variable {f m β α}

omit [Fintype E] in
lemma Hyp.am_nonneg (H : Hyp f m β α) (e : E) : 0 ≤ α * m e := mul_nonneg H.share (H.reward e)

omit [DecidableEq E] in
lemma mem_hatE {e : E} : e ∈ hatE m α ↔ 0 < α * m e := by simp [hatE]

lemma Hyp.am_eq_zero (H : Hyp f m β α) {e : E} (he : e ∉ hatE m α) : α * m e = 0 :=
  le_antisymm (not_lt.1 fun h => he (mem_hatE.2 h)) (H.am_nonneg e)

omit [Fintype E] in
lemma vS_of_mem {S : Finset E} {e : E} (he : e ∈ S) : vS β S e = (β e)⁻¹ := ite_eq_left he

omit [Fintype E] in
lemma vS_of_notMem {S : Finset E} {e : E} (he : e ∉ S) : vS β S e = 0 := ite_eq_right he

omit [Fintype E] in
lemma vS_nonneg (hβ : ∀ e, 0 < β e) (S : Finset E) (e : E) : 0 ≤ vS β S e := by
  unfold vS
  split_ifs
  · exact (inv_pos.2 (hβ e)).le
  · exact le_rfl

omit [Fintype E] in
lemma sum_vS_nonneg (hβ : ∀ e, 0 < β e) (S S' : Finset E) : 0 ≤ ∑ e ∈ S', vS β S e :=
  sum_nonneg fun e _ => vS_nonneg hβ S e

omit [Fintype E] in
/-- `v^S(S') = v^S(S' ∩ S)`. -/
lemma sum_vS_inter (S S' : Finset E) : ∑ e ∈ S', vS β S e = ∑ e ∈ S' ∩ S, vS β S e := by
  rw [← sum_filter_add_sum_filter_not S' (· ∈ S)]
  have h0 : ∑ e ∈ S'.filter (fun e => e ∉ S), vS β S e = 0 :=
    sum_eq_zero fun e he => vS_of_notMem (mem_filter.1 he).2
  rw [h0, add_zero, filter_mem_eq_inter]

omit [Fintype E] in
/-- `v^S(S') > 0` if `S'` meets `S`. -/
lemma sum_vS_pos (hβ : ∀ e, 0 < β e) {S S' : Finset E} (h : (S' ∩ S).Nonempty) :
    0 < ∑ e ∈ S', vS β S e := by
  rw [sum_vS_inter]
  obtain ⟨e, he⟩ := h
  refine sum_pos' (fun e _ => vS_nonneg hβ S e) ⟨e, he, ?_⟩
  rw [vS_of_mem (mem_inter.1 he).2]
  exact inv_pos.2 (hβ e)

omit [Fintype E] in
/-- `v^S(S') = 0` if `S'` does not meet `S`. -/
lemma sum_vS_eq_zero {S S' : Finset E} (h : ¬ (S' ∩ S).Nonempty) : ∑ e ∈ S', vS β S e = 0 := by
  rw [sum_vS_inter, not_nonempty_iff_eq_empty.1 h, sum_empty]

omit [Fintype E] [DecidableEq E] in
@[simp] lemma add_smul_apply (x v : E → ℝ) (d : ℝ) (e : E) : (x + d • v) e = x e + d * v e := rfl

omit [Fintype E] [DecidableEq E] in
/-- `(x + d v)(S') = x(S') + d v(S')`. -/
lemma sum_add_smul (x v : E → ℝ) (d : ℝ) (S' : Finset E) :
    ∑ e ∈ S', (x + d • v) e = ∑ e ∈ S', x e + d * ∑ e ∈ S', v e := by
  simp only [add_smul_apply, sum_add_distrib, mul_sum]

/-- (`appB-quadratic.tex:39-41`) "We keep `x_e = 0` for the unprofitable elements outside `Ê`. By
monotonicity of `f`, feasibility of such a nonnegative vector is determined by the constraints on
subsets of `Ê`." -/
theorem mem_indepPoly_iff (hf : IsRankFunction f) {y : E → ℝ} (h0 : ∀ e, 0 ≤ y e)
    (hy : ∀ e ∉ hatE m α, y e = 0) :
    y ∈ indepPoly f ↔ ∀ S ⊆ hatE m α, ∑ e ∈ S, y e ≤ f S := by
  refine ⟨fun h S _ => h.2 S, fun h => ⟨h0, fun S => ?_⟩⟩
  have hsplit : ∑ e ∈ S, y e = ∑ e ∈ S ∩ hatE m α, y e :=
    (sum_subset inter_subset_left fun e heS he =>
      hy e fun hE => he (mem_inter.2 ⟨heS, hE⟩)).symm
  rw [hsplit]
  exact (h _ inter_subset_right).trans (hf.mono inter_subset_left)

omit [Fintype E] in
/-- (`appB-quadratic.tex:47-49`) `ρ_e(x + d v^S) = ρ_e(x) − d` for `e ∈ S`, and the other
marginals do not change: the marginals of `S` decrease uniformly as `d` increases. -/
lemma marg_add_smul_vS (hβ : ∀ e, 0 < β e) (x : E → ℝ) (S : Finset E) (d : ℝ) (e : E) :
    marg m β α (x + d • vS β S) e = if e ∈ S then marg m β α x e - d else marg m β α x e := by
  have hb := (hβ e).ne'
  unfold marg
  split_ifs with he
  · rw [add_smul_apply, vS_of_mem he]
    field_simp
    ring
  · rw [add_smul_apply, vS_of_notMem he]
    ring

/-- `T(x) ⊆ Ê`. -/
lemma maxTight_subset (x : E → ℝ) : maxTight f m α x ⊆ hatE m α := by
  unfold maxTight
  exact Finset.sup_le fun S hS => mem_powerset.1 (mem_filter.1 hS).1

/-- Every tight subset of `Ê` lies in `T(x)`. -/
lemma subset_maxTight {x : E → ℝ} {S : Finset E} (hS : S ⊆ hatE m α) (ht : IsTight f x S) :
    S ⊆ maxTight f m α x := by
  unfold maxTight
  exact le_sup (f := id) (mem_filter.2 ⟨mem_powerset.2 hS, ht⟩)

/-- (`appB-quadratic.tex:45`) `T(x)` is tight, by `prop:tight`. -/
lemma maxTight_tight (hf : IsRankFunction f) {x : E → ℝ} (hx : x ∈ indepPoly f) :
    IsTight f x (maxTight f m α x) := by
  unfold maxTight
  refine Finset.sup_induction (p := fun T => IsTight f x T) ?_ ?_ ?_
  · show ∑ e ∈ (∅ : Finset E), x e = f ∅
    rw [sum_empty, hf.empty]
  · intro A hA B hB
    exact (Stoc.tight hf hx hA hB).1
  · intro S hS
    exact (mem_filter.1 hS).2

/-- (`eq:A-dmax`) For `x ∈ P₊(f)` vanishing outside `Ê` and `∅ ≠ S ⊆ Ê`, the maximum
`d(x, S) = max {d ≥ 0 : x + d v^S ∈ P₊(f)}` exists and equals
`min_{S' ⊆ Ê, S' ∩ S ≠ ∅} (f(S') − x(S')) / v^S(S')`, a minimum that is attained. (Not in the paper:
the paper states the formula without proof.) -/
theorem dmax_spec (hf : IsRankFunction f) (hβ : ∀ e, 0 < β e) {x : E → ℝ}
    (hx : x ∈ indepPoly f) (hxE : ∀ e ∉ hatE m α, x e = 0) {S : Finset E} (hS : S.Nonempty)
    (hSE : S ⊆ hatE m α) :
    IsGreatest {d : ℝ | 0 ≤ d ∧ x + d • vS β S ∈ indepPoly f} (dmax f β x S) ∧
      IsLeast {r : ℝ | ∃ S' ⊆ hatE m α, (S' ∩ S).Nonempty ∧
        r = (f S' - ∑ e ∈ S', x e) / ∑ e ∈ S', vS β S e} (dmax f β x S) := by
  set q : Finset E → ℝ := fun S' => (f S' - ∑ e ∈ S', x e) / ∑ e ∈ S', vS β S e
  set F := (hatE m α).powerset.filter fun S' => (S' ∩ S).Nonempty
  have hF : F.Nonempty := ⟨S, mem_filter.2 ⟨mem_powerset.2 hSE, by rwa [inter_self]⟩⟩
  -- The minimum of `q` over the sets `S' ⊆ Ê` that meet `S`.
  obtain ⟨S₀, hS₀, hmin⟩ := F.exists_min_image q hF
  have hS₀' := mem_filter.1 hS₀
  have hM0 : 0 ≤ q S₀ :=
    div_nonneg (sub_nonneg.2 (hx.2 S₀)) (sum_vS_nonneg hβ S S₀)
  -- The feasible steps form the interval `[0, q(S₀)]`.
  have hset : {d : ℝ | 0 ≤ d ∧ x + d • vS β S ∈ indepPoly f} = Set.Icc 0 (q S₀) := by
    ext d
    simp only [Set.mem_ofPred_eq, Set.mem_Icc]
    constructor
    · rintro ⟨hd, hfeas⟩
      refine ⟨hd, ?_⟩
      have h := hfeas.2 S₀
      rw [sum_add_smul] at h
      show d ≤ (f S₀ - ∑ e ∈ S₀, x e) / ∑ e ∈ S₀, vS β S e
      rw [le_div_iff₀ (sum_vS_pos hβ hS₀'.2)]
      linarith
    · rintro ⟨hd, hdM⟩
      refine ⟨hd, (mem_indepPoly_iff (m := m) (α := α) hf (fun e => ?_) (fun e he => ?_)).2
        fun S' hS' => ?_⟩
      · rw [add_smul_apply]
        exact add_nonneg (hx.1 e) (mul_nonneg hd (vS_nonneg hβ S e))
      · rw [add_smul_apply, hxE e he, vS_of_notMem fun h => he (hSE h), mul_zero, add_zero]
      · rw [sum_add_smul]
        by_cases hmeet : (S' ∩ S).Nonempty
        · have h1 : d ≤ q S' := hdM.trans (hmin S' (mem_filter.2 ⟨mem_powerset.2 hS', hmeet⟩))
          have h2 := sum_vS_pos hβ hmeet
          rw [le_div_iff₀ h2] at h1
          linarith
        · rw [sum_vS_eq_zero hmeet, mul_zero, add_zero]
          exact hx.2 S'
  have hd : dmax f β x S = q S₀ := by
    unfold dmax
    rw [hset, csSup_Icc hM0]
  refine ⟨?_, ?_⟩
  · rw [hd, hset]
    exact isGreatest_Icc hM0
  · rw [hd]
    refine ⟨⟨S₀, mem_powerset.1 hS₀'.1, hS₀'.2, rfl⟩, ?_⟩
    rintro r ⟨S', hS', hmeet, rfl⟩
    exact hmin S' (mem_filter.2 ⟨mem_powerset.2 hS', hmeet⟩)

/-- (`appB-quadratic.tex:54-55`) "The minimum is attained, so the maximal tight set
`T(x + d(x, S) v^S)` at `x + d(x, S) v^S` has a nonempty intersection with `S`." -/
theorem maxTight_dmax_meets (hf : IsRankFunction f) (hβ : ∀ e, 0 < β e) {x : E → ℝ}
    (hx : x ∈ indepPoly f) (hxE : ∀ e ∉ hatE m α, x e = 0) {S : Finset E} (hS : S.Nonempty)
    (hSE : S ⊆ hatE m α) :
    (maxTight f m α (x + dmax f β x S • vS β S) ∩ S).Nonempty := by
  -- The minimum of (`eq:A-dmax`) is attained at a set `S' ⊆ Ê` that meets `S`,
  obtain ⟨S', hS'E, hmeet, hS'eq⟩ := (dmax_spec hf hβ hx hxE hS hSE).2.1
  -- so `S'` is tight at the endpoint,
  have htight : IsTight f (x + dmax f β x S • vS β S) S' := by
    unfold IsTight
    rw [sum_add_smul, hS'eq, div_mul_cancel₀ _ (sum_vS_pos hβ hmeet).ne']
    ring
  -- and it lies in the maximal tight set there.
  obtain ⟨e, he⟩ := hmeet
  exact ⟨e, mem_inter.2 ⟨subset_maxTight hS'E htight (mem_inter.1 he).1, (mem_inter.1 he).2⟩⟩

end Construction

/-! ### The ray computation (`lem:ray`)

The discrete Newton method of the proof of `lem:ray` (`appB-quadratic.tex:130-158`) for a point `x`
and a set `S`. -/

section Ray

variable (f : Finset E → ℝ) (m β : E → ℝ) (α : ℝ) (x : E → ℝ) (S : Finset E)

/-- `g_d(S') := f(S') − x(S') − d v(S')` with `v = v^S`, minimized over the subsets of `Ê`. -/
noncomputable def gd (d : ℝ) (S' : Finset E) : ℝ :=
  f S' - ∑ e ∈ S', x e - d * ∑ e ∈ S', vS β S e

/-- The start `d = min_{e ∈ S} (f({e}) − x_e) / v_e`. -/
noncomputable def d0 : ℝ :=
  if h : S.Nonempty then S.inf' h fun e => (f {e} - x e) / vS β S e else 0

/-- The maximal minimizer `S̃` of `g_d` on `2^Ê`, returned by the oracle. -/
noncomputable def tilde (d : ℝ) : Finset E := sfmArg (gd f β x S d) (hatE m α)

/-- The update `d' := (f(S̃) − x(S̃)) / v(S̃)`. -/
noncomputable def dnext (d : ℝ) : ℝ :=
  (f (tilde f m β α x S d) - ∑ e ∈ tilde f m β α x S d, x e) /
    ∑ e ∈ tilde f m β α x S d, vS β S e

/-- The value of `d` in round `k` (rounds counted from `0`). -/
noncomputable def dIter : ℕ → ℝ
  | 0 => d0 f β x S
  | k + 1 => dnext f m β α x S (dIter k)

/-- The minimum `g_d(S̃)` in round `k`. -/
noncomputable def gIter (k : ℕ) : ℝ :=
  gd f β x S (dIter f m β α x S k) (tilde f m β α x S (dIter f m β α x S k))

open Classical in
/-- The round `K` in which the method returns: the first round with `g_d(S̃) = 0` (`0` if there is
none; by `exists_stop` there is one, with `K ≤ |S|`). -/
noncomputable def rayRounds : ℕ :=
  if h : ∃ k, gIter f m β α x S k = 0 then Nat.find h else 0

/-- The step `d` that the method returns. -/
noncomputable def rayStep : ℝ := dIter f m β α x S (rayRounds f m β α x S)

/-- The set `S̃` that the method returns. -/
noncomputable def rayArg : Finset E := tilde f m β α x S (rayStep f m β α x S)

/-- The number of submodular minimizations: one in each of the rounds `0, …, K`. -/
noncomputable def rayCalls : ℕ := rayRounds f m β α x S + 1

/-- The number of further evaluations of `f`, defined as the proof of `lem:ray` counts them
(step (5)): one after each of the `K + 1` calls (at `S̃`, for the test and the update) and the
`|S|` singletons of the initialization. The counted ray computation `rayC` makes exactly this many
(`rayC_spec`). -/
noncomputable def rayEvals : ℕ := S.card + rayCalls f m β α x S

variable {f m β α x S}

omit [Fintype E] in
lemma gd_eq (d : ℝ) (S' : Finset E) :
    gd f β x S d S' = f S' - ∑ e ∈ S', (x + d • vS β S) e := by
  rw [gd, sum_add_smul]
  ring

omit [Fintype E] in
/-- `g_d` is submodular. (Not in the paper: the proof of `lem:ray` calls `g_d` submodular without
proof.) -/
lemma gd_submodular (hf : Submodular f) (d : ℝ) : Submodular (gd f β x S d) := by
  intro A B
  unfold gd
  have h1 := hf A B
  have h2 := sum_union_inter (s₁ := A) (s₂ := B) (f := x)
  have h3 := sum_union_inter (s₁ := A) (s₂ := B) (f := vS β S)
  have h4 : d * ∑ e ∈ A ∪ B, vS β S e + d * ∑ e ∈ A ∩ B, vS β S e =
      d * ∑ e ∈ A, vS β S e + d * ∑ e ∈ B, vS β S e := by
    rw [← mul_add, ← mul_add, h3]
  linarith

lemma tilde_subset (d : ℝ) : tilde f m β α x S d ⊆ hatE m α := sfmArg_subset _ _

/-- `S̃` is a minimizer of `g_d` on `2^Ê`. -/
lemma gd_tilde (hf : IsRankFunction f) (d : ℝ) :
    gd f β x S d (tilde f m β α x S d) = sfmVal (gd f β x S d) (hatE m α) :=
  sfmArg_min (gd_submodular hf.submod d) _

lemma gd_tilde_le (hf : IsRankFunction f) (d : ℝ) {S' : Finset E} (hS' : S' ⊆ hatE m α) :
    gd f β x S d (tilde f m β α x S d) ≤ gd f β x S d S' :=
  (gd_tilde hf d).trans_le (sfmVal_le _ hS')

/-- The minimum is at most `g_d(∅) = 0`. (Not in the paper: the proof of `lem:ray` leaves implicit
that "otherwise" means `g_d(S̃) < 0`.) -/
lemma gd_tilde_nonpos (hf : IsRankFunction f) (d : ℝ) : gd f β x S d (tilde f m β α x S d) ≤ 0 := by
  have h := gd_tilde_le (x := x) (S := S) (m := m) (α := α) (β := β) hf d (empty_subset _)
  simpa [gd, hf.empty] using h

/-- `S̃` contains every minimizer of `g_d` on `2^Ê`. -/
lemma subset_tilde (hf : IsRankFunction f) (d : ℝ) {S' : Finset E} (hS' : S' ⊆ hatE m α)
    (h : gd f β x S d S' ≤ gd f β x S d (tilde f m β α x S d)) : S' ⊆ tilde f m β α x S d := by
  refine subset_sfmArg _ hS' (le_antisymm ?_ (sfmVal_le _ hS'))
  rw [← gd_tilde hf d]
  exact h

/-- `lem:ray`, step (3), first sentence: "Initially `d ≥ d(x, S)` by the singleton constraints." -/
lemma dmax_le_d0 (H : Hyp f m β α) (hx : x ∈ indepPoly f) (hxE : ∀ e ∉ hatE m α, x e = 0)
    (hS : S.Nonempty) (hSE : S ⊆ hatE m α) : dmax f β x S ≤ d0 f β x S := by
  have hfeas := (dmax_spec H.rank H.beta hx hxE hS hSE).1.1.2
  rw [d0, dite_eq_left hS]
  refine le_inf' hS _ fun e he => ?_
  have h := hfeas.2 {e}
  rw [sum_singleton, add_smul_apply] at h
  have hv : 0 < vS β S e := by rw [vS_of_mem he]; exact inv_pos.2 (H.beta e)
  rw [le_div_iff₀ hv]
  linarith

/-- `lem:ray`, step (3), second sentence: "If `g_d(S̃) < 0`, feasibility of `x` gives
`v(S̃) > 0` and `d(x, S) ≤ d' < d`." -/
lemma round_of_neg (H : Hyp f m β α) (hx : x ∈ indepPoly f) (hxE : ∀ e ∉ hatE m α, x e = 0)
    (hS : S.Nonempty) (hSE : S ⊆ hatE m α) {d : ℝ}
    (hneg : gd f β x S d (tilde f m β α x S d) < 0) :
    0 < ∑ e ∈ tilde f m β α x S d, vS β S e ∧ dmax f β x S ≤ dnext f m β α x S d ∧
      dnext f m β α x S d < d := by
  set T := tilde f m β α x S d
  have hfx : 0 ≤ f T - ∑ e ∈ T, x e := sub_nonneg.2 (hx.2 T)
  have hv0 := sum_vS_nonneg H.beta S T
  unfold gd at hneg
  -- `v(S̃) > 0`
  have hv : 0 < ∑ e ∈ T, vS β S e := by
    rcases hv0.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hneg
      linarith
  refine ⟨hv, ?_, ?_⟩
  · -- `d(x, S) ≤ d'`: the constraint of `S̃` at the largest feasible step
    have h := ((dmax_spec H.rank H.beta hx hxE hS hSE).1.1.2).2 T
    rw [sum_add_smul] at h
    show dmax f β x S ≤ (f T - ∑ e ∈ T, x e) / ∑ e ∈ T, vS β S e
    rw [le_div_iff₀ hv]
    linarith
  · -- `d' < d`
    show (f T - ∑ e ∈ T, x e) / ∑ e ∈ T, vS β S e < d
    rw [div_lt_iff₀ hv]
    linarith

/-- `lem:ray`, step (3), the rounds before the method returns: `d ≥ d(x, S)` in every round
reached through negative minima ("Initially `d ≥ d(x, S)` … `d(x, S) ≤ d'` …"). -/
lemma dmax_le_dIter (H : Hyp f m β α) (hx : x ∈ indepPoly f) (hxE : ∀ e ∉ hatE m α, x e = 0)
    (hS : S.Nonempty) (hSE : S ⊆ hatE m α) :
    ∀ k, (∀ j < k, gIter f m β α x S j < 0) → dmax f β x S ≤ dIter f m β α x S k := by
  intro k
  induction k with
  | zero => intro _; exact dmax_le_d0 H hx hxE hS hSE
  | succ k _ =>
    intro hneg
    exact (round_of_neg H hx hxE hS hSE (hneg k (Nat.lt_succ_self k))).2.1

/-- `lem:ray`, step (3), last sentence: "If the minimum is zero, the current step is feasible,
hence equals `d(x, S)`, and its maximal minimizer is exactly the maximal tight set at the
endpoint." -/
lemma stop_spec (H : Hyp f m β α) (hx : x ∈ indepPoly f) (hxE : ∀ e ∉ hatE m α, x e = 0)
    (hS : S.Nonempty) (hSE : S ⊆ hatE m α) {d : ℝ} (hd : dmax f β x S ≤ d)
    (h0 : gd f β x S d (tilde f m β α x S d) = 0) :
    d = dmax f β x S ∧ tilde f m β α x S d = maxTight f m α (x + d • vS β S) := by
  have hspec := dmax_spec H.rank H.beta hx hxE hS hSE
  have hd0 : 0 ≤ d := (hspec.1.1.1).trans hd
  -- The current step is feasible:
  have hfeas : x + d • vS β S ∈ indepPoly f := by
    refine (mem_indepPoly_iff (m := m) (α := α) H.rank (fun e => ?_) (fun e he => ?_)).2
      fun S' hS' => ?_
    · rw [add_smul_apply]
      exact add_nonneg (hx.1 e) (mul_nonneg hd0 (vS_nonneg H.beta S e))
    · rw [add_smul_apply, hxE e he, vS_of_notMem fun h => he (hSE h), mul_zero, add_zero]
    · have h1 := gd_tilde_le (m := m) (α := α) (x := x) (S := S) (β := β) H.rank d hS'
      rw [h0, gd_eq] at h1
      linarith
  -- hence it equals `d(x, S)`,
  have heq : d = dmax f β x S := le_antisymm (hspec.1.2 ⟨hd0, hfeas⟩) hd
  refine ⟨heq, ?_⟩
  -- and its maximal minimizer is the maximal tight set at the endpoint.
  have hval : sfmVal (gd f β x S d) (hatE m α) = 0 := (gd_tilde H.rank d).symm.trans h0
  unfold tilde sfmArg maxTight
  rw [hval]
  congr 1
  refine filter_congr fun S' _ => ?_
  rw [gd_eq]
  constructor <;> intro h <;> linarith

/-- `lem:ray`, step (4): for consecutive negative minima with maximal minimizers `S̃, S̃'` at
`d > d'`, `S̃' ∩ S` is a proper subset of `S̃ ∩ S`. -/
lemma tilde_inter_ssubset (H : Hyp f m β α) (hx : x ∈ indepPoly f)
    (hxE : ∀ e ∉ hatE m α, x e = 0) (hS : S.Nonempty) (hSE : S ⊆ hatE m α) {d : ℝ}
    (hneg : gd f β x S d (tilde f m β α x S d) < 0)
    (hneg' : gd f β x S (dnext f m β α x S d) (tilde f m β α x S (dnext f m β α x S d)) < 0) :
    tilde f m β α x S (dnext f m β α x S d) ∩ S ⊂ tilde f m β α x S d ∩ S := by
  set d' := dnext f m β α x S d
  set T := tilde f m β α x S d
  set T' := tilde f m β α x S d'
  obtain ⟨hv, -, hlt⟩ := round_of_neg H hx hxE hS hSE hneg
  have hTE : T ⊆ hatE m α := tilde_subset d
  have hT'E : T' ⊆ hatE m α := tilde_subset d'
  -- `g_{d'} = g_d + (d − d') v`
  have hshift : ∀ U, gd f β x S d' U = gd f β x S d U + (d - d') * ∑ e ∈ U, vS β S e := by
    intro U; unfold gd; ring
  -- "Since `S̃'` minimizes `g_{d'} = g_d + (d − d') v` and `v ≥ 0`,
  -- `g_d(S̃') − g_d(S̃ ∩ S̃') ≤ (d − d')(v(S̃ ∩ S̃') − v(S̃')) ≤ 0`."
  have h1 : gd f β x S d T' - gd f β x S d (T ∩ T') ≤ 0 := by
    have hmin := gd_tilde_le (m := m) (α := α) (x := x) (S := S) (β := β) H.rank d'
      (inter_subset_left.trans hTE : T ∩ T' ⊆ _)
    rw [hshift, hshift] at hmin
    have hmono : ∑ e ∈ T ∩ T', vS β S e ≤ ∑ e ∈ T', vS β S e :=
      sum_le_sum_of_subset_of_nonneg inter_subset_right fun e _ _ => vS_nonneg H.beta S e
    have : (d - d') * ∑ e ∈ T ∩ T', vS β S e ≤ (d - d') * ∑ e ∈ T', vS β S e :=
      mul_le_mul_of_nonneg_left hmono (by linarith)
    linarith
  -- "Submodularity gives `g_d(S̃ ∪ S̃') ≤ g_d(S̃)`, so maximality of `S̃` implies `S̃' ⊆ S̃`."
  have hsub : T' ⊆ T := by
    have h2 := gd_submodular (β := β) (x := x) (S := S) H.rank.submod d T T'
    have h3 : gd f β x S d (T ∪ T') ≤ gd f β x S d T := by linarith
    exact subset_union_right.trans (subset_tilde H.rank d (union_subset hTE hT'E) h3)
  -- "If `S̃' ∩ S = S̃ ∩ S`, then
  -- `g_{d'}(S̃') = g_d(S̃') + (d − d') v(S̃) ≥ g_d(S̃) + (d − d') v(S̃) = g_{d'}(S̃) = 0`,
  -- a contradiction."
  have hne : T' ∩ S ≠ T ∩ S := by
    intro heq
    have hvv : ∑ e ∈ T', vS β S e = ∑ e ∈ T, vS β S e := by
      rw [sum_vS_inter S T', sum_vS_inter S T, heq]
    have hzero : gd f β x S d' T = 0 := by
      have hd' : d' = (f T - ∑ e ∈ T, x e) / ∑ e ∈ T, vS β S e := rfl
      rw [gd, hd', div_mul_cancel₀ _ hv.ne']
      ring
    have h4 : gd f β x S d T ≤ gd f β x S d T' := gd_tilde_le H.rank d hT'E
    have h5 : 0 ≤ gd f β x S d' T' := by
      rw [hshift T', hvv, ← hzero, hshift T]
      linarith
    linarith
  -- "Thus the sets `S̃ ∩ S` at negative minima form a strictly decreasing chain of nonempty
  -- subsets of `S`."
  -- Here the strict decrease; the nonemptiness is shown in `exists_stop`.
  exact ssubset_of_subset_of_ne (inter_subset_inter_right hsub) hne

/-- `lem:ray`, step (4): the sets `S̃ ∩ S` at negative minima are nonempty subsets of `S` that
strictly decrease, so the method returns within `|S|` rounds of negative minimum: some round
`k ≤ |S|` has minimum zero. -/
lemma exists_stop (H : Hyp f m β α) (hx : x ∈ indepPoly f) (hxE : ∀ e ∉ hatE m α, x e = 0)
    (hS : S.Nonempty) (hSE : S ⊆ hatE m α) : ∃ k ≤ S.card, gIter f m β α x S k = 0 := by
  by_contra hcon
  push Not at hcon
  have hneg : ∀ k ≤ S.card, gIter f m β α x S k < 0 := fun k hk =>
    lt_of_le_of_ne (gd_tilde_nonpos H.rank _) (hcon k hk)
  -- the chain: `|S̃_k ∩ S| + k ≤ |S|`
  have key : ∀ k ≤ S.card,
      (tilde f m β α x S (dIter f m β α x S k) ∩ S).card + k ≤ S.card := by
    intro k
    induction k with
    | zero => intro _; simpa using card_le_card inter_subset_right
    | succ k ih =>
      intro hk
      have h := card_lt_card
        (tilde_inter_ssubset H hx hxE hS hSE (hneg k (Nat.le_of_succ_le hk)) (hneg (k + 1) hk))
      have := ih (Nat.le_of_succ_le hk)
      change (tilde f m β α x S (dnext f m β α x S (dIter f m β α x S k)) ∩ S).card + (k + 1) ≤ _
      omega
  -- and every `S̃_k ∩ S` at a negative minimum is nonempty, as `v(S̃_k) > 0`.
  have h1 := key S.card le_rfl
  have hv := (round_of_neg H hx hxE hS hSE (hneg S.card le_rfl)).1
  have hne : (tilde f m β α x S (dIter f m β α x S S.card) ∩ S).Nonempty := by
    by_contra h
    rw [sum_vS_eq_zero h] at hv
    exact lt_irrefl 0 hv
  have := hne.card_pos
  omega

/-! #### The ray computation with its operation counts

Step (5) of the proof of `lem:ray` counts the work: "Each call is followed by one evaluation of `f`,
at `S̃`, for the test and the update, and by `O(n)` arithmetic operations." The counted ray
computation `rayC` performs the method's steps in the cost model of `Stoc.Counted`: the start `d0C`
(step (1)), and in each round `roundC` the minimization, the evaluation of `f` at `S̃`, the sums
`x(S̃)` and `v(S̃)`, `g_d(S̃)` and the update `d'` (step (2)), with the test `g_d(S̃) = 0` in
`loopC`. `rayC_spec` shows that it returns `rayStep` and `rayArg`, makes `rayCalls` minimizations
and `rayEvals` further evaluations of `f`, and at most `4|S| + (|S| + 1)(3|Ê| + 5)` further
arithmetic operations. (Not in the paper: the paper counts in prose.) -/

open Counted

variable (f m β α x S)

/-- `v_e`: one operation, `β_e⁻¹` for `e ∈ S` and `0` otherwise. The test `e ∈ S` is counted with
the inversion, a modelling choice: counted on its own, it would add at most `|S̃|` operations to
each round of `roundC`, which changes no order. -/
noncomputable def vC (e : E) : Counted ℝ := ops 1 (vS β S e)

/-- Step (1) of `lem:ray`, counted: the start `d = min_{e ∈ S} (f({e}) − x_e)/v_e`, with one
evaluation of `f` and three operations for each `e ∈ S`, and the minimum. -/
noncomputable def d0C : Counted ℝ :=
  if h : S.Nonempty then
    Counted.inf' S h fun e =>
      evalF (f {e}) >>=ᶜ fun fe => vC β S e >>=ᶜ fun ve => ops 2 ((fe - x e) / ve)
  else ret 0

/-- One round of step (2) of `lem:ray` at `d`, counted: the minimization returns `S̃`; then one
evaluation of `f` at `S̃`, the sums `x(S̃)` and `v(S̃)`, `g_d(S̃) = (f(S̃) − x(S̃)) − d v(S̃)`, and
the update `d' = (f(S̃) − x(S̃))/v(S̃)`. It returns `S̃`, `g_d(S̃)` and `d'`. -/
noncomputable def roundC (d : ℝ) : Counted (Finset E × ℝ × ℝ) :=
  minimize (tilde f m β α x S d) >>=ᶜ fun T =>
  evalF (f T) >>=ᶜ fun fT =>
  Counted.sum T (fun e => ret (x e)) >>=ᶜ fun xT =>
  Counted.sum T (vC β S) >>=ᶜ fun vT =>
  ops 1 (fT - xT) >>=ᶜ fun num =>
  ops 2 (num - d * vT) >>=ᶜ fun g =>
  ops 1 (num / vT) >>=ᶜ fun d' =>
  ret (T, g, d')

open Classical in
/-- The rounds of step (2) from `d`, at most `k` of them, counted: each round tests `g_d(S̃) = 0`
(one comparison) and returns `d` and `S̃`, or continues at `d'`. -/
noncomputable def loopC : ℕ → ℝ → Counted (ℝ × Finset E)
  | 0, d => ret (d, ∅)
  | k + 1, d =>
      roundC f m β α x S d >>=ᶜ fun r =>
      ops 1 () >>=ᶜ fun _ =>
      if r.2.1 = 0 then ret (d, r.1) else loopC k r.2.2

/-- The ray computation of `lem:ray`, counted: the start and at most `|S| + 1` rounds. -/
noncomputable def rayC : Counted (ℝ × Finset E) :=
  d0C f β x S >>=ᶜ fun d => loopC f m β α x S (S.card + 1) d

variable {f m β α x S}

omit [Fintype E] in
lemma d0C_val : (d0C f β x S).val = d0 f β x S := by
  unfold d0C d0
  split_ifs with h
  · simp [vC]
  · rfl

omit [Fintype E] in
lemma d0C_cost (hS : S.Nonempty) : (d0C f β x S).cost = (4 * S.card, 0, S.card) := by
  simp only [d0C, hS, ↓reduceDIte]
  simp [vC, Prod.ext_iff]
  ring

lemma roundC_val (d : ℝ) :
    (roundC f m β α x S d).val =
      (tilde f m β α x S d, gd f β x S d (tilde f m β α x S d), dnext f m β α x S d) := by
  simp [roundC, vC, gd, dnext]

lemma roundC_cost (d : ℝ) :
    (roundC f m β α x S d).cost = (3 * (tilde f m β α x S d).card + 4, 1, 1) := by
  simp [roundC, vC, Prod.ext_iff]
  ring

/-- The rounds return the method's result: if round `K` is the first with `g_d(S̃) = 0`, then from
round `j ≤ K`, with more than `K − j` rounds left, `loopC` returns `(d_K, S̃_K)` after the rounds
`j, …, K`, each with its test. -/
lemma loopC_spec {K : ℕ} (hK : gIter f m β α x S K = 0)
    (hneg : ∀ i < K, gIter f m β α x S i ≠ 0) :
    ∀ k j, j ≤ K → K < j + k →
      (loopC f m β α x S k (dIter f m β α x S j)).val =
          (dIter f m β α x S K, tilde f m β α x S (dIter f m β α x S K)) ∧
      (loopC f m β α x S k (dIter f m β α x S j)).cost =
          ∑ i ∈ Finset.Ico j (K + 1),
            ((roundC f m β α x S (dIter f m β α x S i)).cost + (1, 0, 0)) := by
  intro k
  induction k with
  | zero => intro j hj hjk; omega
  | succ k ih =>
    intro j hj hjk
    have hr := roundC_val (f := f) (m := m) (β := β) (α := α) (x := x) (S := S)
      (dIter f m β α x S j)
    rcases hj.lt_or_eq with hlt | rfl
    · have hg : gd f β x S (dIter f m β α x S j) (tilde f m β α x S (dIter f m β α x S j)) ≠ 0 :=
        hneg j hlt
      have hd : dnext f m β α x S (dIter f m β α x S j) = dIter f m β α x S (j + 1) := rfl
      obtain ⟨h1, h2⟩ := ih (j + 1) hlt (by omega)
      simp only [loopC, val_bind, cost_bind, hr, cost_ops, hg, ite_false, hd, h1, h2, true_and]
      rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : j < K + 1), add_assoc]
    · have hg : gd f β x S (dIter f m β α x S j) (tilde f m β α x S (dIter f m β α x S j)) = 0 :=
        hK
      simp only [loopC, val_bind, cost_bind, hr, cost_ops, hg, ite_true, Nat.Ico_succ_singleton,
        Finset.sum_singleton]
      simp

/-- The counted ray computation (step (5) of `lem:ray`; not in the paper: the paper counts in
prose): `rayC` returns the step `rayStep` and the set `rayArg` of the method, with exactly
`rayCalls` minimizations and `rayEvals` further evaluations of `f`, and at most
`4|S| + (|S| + 1)(3|Ê| + 5)` further arithmetic operations (comparisons included). -/
lemma rayC_spec (H : Hyp f m β α) (hx : x ∈ indepPoly f) (hxE : ∀ e ∉ hatE m α, x e = 0)
    (hS : S.Nonempty) (hSE : S ⊆ hatE m α) :
    (rayC f m β α x S).val = (rayStep f m β α x S, rayArg f m β α x S) ∧
      (rayC f m β α x S).cost.2.1 = rayCalls f m β α x S ∧
      (rayC f m β α x S).cost.2.2 = rayEvals f m β α x S ∧
      (rayC f m β α x S).cost.1 ≤ 4 * S.card + (S.card + 1) * (3 * (hatE m α).card + 5) := by
  obtain ⟨k, hk, hk0⟩ := exists_stop H hx hxE hS hSE
  have hex : ∃ k, gIter f m β α x S k = 0 := ⟨k, hk0⟩
  have hR : rayRounds f m β α x S = Nat.find hex := by rw [rayRounds, dite_eq_left hex]
  have hK : gIter f m β α x S (rayRounds f m β α x S) = 0 := hR ▸ Nat.find_spec hex
  have hneg : ∀ i < rayRounds f m β α x S, gIter f m β α x S i ≠ 0 := fun i hi =>
    Nat.find_min hex (hR ▸ hi)
  have hKS : rayRounds f m β α x S ≤ S.card := (hR ▸ Nat.find_min' hex hk0).trans hk
  obtain ⟨h1, h2⟩ := loopC_spec hK hneg (S.card + 1) 0 (Nat.zero_le _) (by omega)
  have hd0 : (d0C f β x S).val = dIter f m β α x S 0 := d0C_val
  have hcost : (rayC f m β α x S).cost = (4 * S.card, 0, S.card) +
      ∑ i ∈ Finset.Ico 0 (rayRounds f m β α x S + 1),
        ((3 * (tilde f m β α x S (dIter f m β α x S i)).card + 4, 1, 1) + (1, 0, 0)) := by
    simp only [rayC, cost_bind, hd0, h2, d0C_cost hS, roundC_cost]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [rayC, val_bind, hd0, h1]
    rfl
  · rw [hcost]
    simp [Prod.snd_sum, rayCalls]
  · rw [hcost]
    simp [Prod.snd_sum, rayEvals, rayCalls]
  · rw [hcost]
    simp only [Prod.fst_add, Prod.fst_sum]
    have hle : ∀ i ∈ Finset.Ico 0 (rayRounds f m β α x S + 1),
        3 * (tilde f m β α x S (dIter f m β α x S i)).card + 4 + 1 ≤ 3 * (hatE m α).card + 5 :=
      fun i _ => by
        have := card_le_card (tilde_subset (f := f) (m := m) (β := β) (α := α) (x := x) (S := S)
          (dIter f m β α x S i))
        omega
    have := Finset.sum_le_sum hle
    simp only [Finset.sum_const, Nat.card_Ico, smul_eq_mul] at this
    have hmul : (rayRounds f m β α x S + 1 - 0) * (3 * (hatE m α).card + 5) ≤
        (S.card + 1) * (3 * (hatE m α).card + 5) :=
      Nat.mul_le_mul_right _ (by omega)
    omega

/-- **`lem:ray`** (Lemma B.3, statement `appB-quadratic.tex:122-128`, proof
`:130-158`). For `x ∈ P₊(f)` with `x_e = 0` for `e ∉ Ê` and `∅ ≠ S ⊆ Ê`, the discrete Newton method
stops: in round `K = rayRounds` the minimum `g_d(S̃)` is zero and in every earlier round it is
negative. It returns the step size `d(x, S)` and the maximal tight set `T(x + d(x, S) v^S)` at its
endpoint, with at most `|S| + 1` submodular minimizations (`rayCalls = K + 1`), at most
`2|S| + 1` further evaluations of `f` (`rayEvals = |S| + K + 1`, the paper's accounting of step
(5)), and `𝒪(n|S|)` further arithmetic operations: the counted ray computation `rayC`, which
performs the method's steps in the cost model of `Stoc.Counted`, returns `d(x, S)` and
`T(x + d(x, S) v^S)` with exactly `rayCalls` minimizations and `rayEvals` evaluations of `f`, and
at most `4|S| + (|S| + 1)(3|Ê| + 5)` further arithmetic operations, comparisons included
(`rayC_spec`; not in the paper: the paper counts in prose).

The paper's steps: (1) start at `d = min_{e ∈ S} (f({e}) − x_e)/v_e` (`d0`); (2) find the maximal
minimizer `S̃` of `g_d` on `2^Ê` (`tilde`); return `d, S̃` if `g_d(S̃) = 0` (`rayRounds`, `rayStep`,
`rayArg`), else replace `d` by `d'` (`dnext`); (3) `d ≥ d(x, S)` initially (`dmax_le_d0`), after
a negative minimum `v(S̃) > 0` and `d(x, S) ≤ d' < d` (`round_of_neg`), and at minimum zero the step
is `d(x, S)` and `S̃` the maximal tight set (`stop_spec`); (4) consecutive negative minima shrink
`S̃ ∩ S` strictly (`tilde_inter_ssubset`), so at most `|S|` negative calls and one final call
(`exists_stop`); (5) one evaluation of `f` and `𝒪(n)` arithmetic operations after each call, and
`|S|` evaluations for the initialization, at most `2|S| + 1` (`rayEvals`; counted by `rayC`). -/
theorem ray (H : Hyp f m β α) (hx : x ∈ indepPoly f) (hxE : ∀ e ∉ hatE m α, x e = 0)
    (hS : S.Nonempty) (hSE : S ⊆ hatE m α) :
    gIter f m β α x S (rayRounds f m β α x S) = 0 ∧
      (∀ j < rayRounds f m β α x S, gIter f m β α x S j < 0) ∧
      rayStep f m β α x S = dmax f β x S ∧
      rayArg f m β α x S = maxTight f m α (x + dmax f β x S • vS β S) ∧
      rayCalls f m β α x S ≤ S.card + 1 ∧ rayEvals f m β α x S ≤ 2 * S.card + 1 ∧
      ((rayC f m β α x S).val = (rayStep f m β α x S, rayArg f m β α x S) ∧
        (rayC f m β α x S).cost.2.1 = rayCalls f m β α x S ∧
        (rayC f m β α x S).cost.2.2 = rayEvals f m β α x S ∧
        (rayC f m β α x S).cost.1 ≤ 4 * S.card + (S.card + 1) * (3 * (hatE m α).card + 5)) := by
  -- (1) "Write `v = v^S` and start at `d = min_{e∈S}(f({e}) − x_e)/v_e`."
  -- (2) "For each `d`, find the maximal minimizer `S̃` of the submodular function
  -- `g_d(S') := f(S') − x(S') − d v(S')` on `2^Ê`. If `g_d(S̃) = 0`, return `d` and `S̃`.
  -- Otherwise replace `d` by `d' := (f(S̃) − x(S̃))/v(S̃)`."
  -- The method is defined before the lemma: the start `d0`, the oracle `tilde`, the update
  -- `dnext`, the rounds `dIter`, and the round `rayRounds` in which it returns.
  -- (3) "Initially `d ≥ d(x, S)` by the singleton constraints. If `g_d(S̃) < 0`, feasibility of `x`
  -- gives `v(S̃) > 0` and `d(x, S) ≤ d' < d`."
  have hge : ∀ k, (∀ j < k, gIter f m β α x S j < 0) → dmax f β x S ≤ dIter f m β α x S k :=
    dmax_le_dIter H hx hxE hS hSE
  -- "If the minimum is zero, the current step is feasible, hence equals `d(x, S)`, and its maximal
  -- minimizer is exactly the maximal tight set at the endpoint."
  have hret : ∀ k, (∀ j < k, gIter f m β α x S j < 0) → gIter f m β α x S k = 0 →
      dIter f m β α x S k = dmax f β x S ∧
        tilde f m β α x S (dIter f m β α x S k) =
          maxTight f m α (x + dIter f m β α x S k • vS β S) :=
    fun k hneg h0 => stop_spec H hx hxE hS hSE (hge k hneg) h0
  -- (4) "There are at most `|S|` such calls and one final call with minimum zero."
  obtain ⟨k, hk, hk0⟩ := exists_stop H hx hxE hS hSE
  have hex : ∃ k, gIter f m β α x S k = 0 := ⟨k, hk0⟩
  have hK : rayRounds f m β α x S = Nat.find hex := by rw [rayRounds, dite_eq_left hex]
  have hKk : rayRounds f m β α x S ≤ k := hK ▸ Nat.find_min' hex hk0
  -- so the method returns in round `K = rayRounds`, after negative minima in the rounds before
  have hneg : ∀ j < rayRounds f m β α x S, gIter f m β α x S j < 0 := by
    intro j hj
    rw [hK] at hj
    exact lt_of_le_of_ne (gd_tilde_nonpos H.rank _) (Nat.find_min hex hj)
  have h0 : gIter f m β α x S (rayRounds f m β α x S) = 0 := by
    rw [hK]
    exact Nat.find_spec hex
  obtain ⟨hd, hT⟩ := hret _ hneg h0
  refine ⟨h0, hneg, hd, ?_, ?_, ?_, ?_⟩
  · show tilde f m β α x S (rayStep f m β α x S) = _
    rw [rayStep, hT, hd]
  · -- one call in each of the rounds `0, …, K`, and `K ≤ |S|`
    unfold rayCalls
    omega
  · -- (5) "Each call is followed by one evaluation of `f`, at `S̃`, for the test and the update,
    -- and by `O(n)` arithmetic operations. With the `|S|` singleton evaluations of the
    -- initialization, this makes at most `2|S| + 1` further evaluations of `f`."
    -- `rayEvals = |S| + (K + 1)` is this accounting, so its bound is the bound `K ≤ |S|` on the
    -- rounds; the counted ray computation makes exactly `rayEvals` evaluations (below).
    unfold rayEvals rayCalls
    omega
  · -- (5), the count: the counted ray computation `rayC` returns the method's step and set, with
    -- `rayCalls` minimizations, `rayEvals` evaluations of `f` and `𝒪(n|S|)` further arithmetic
    -- operations (`rayC_spec`; not in the paper: the paper counts in prose).
    exact rayC_spec H hx hxE hS hSE

end Ray

/-! ### Water-filling (`eq:A-level`, `eq:A-step`, `alg:waterfilling`) -/

section Loop

variable (f : Finset E → ℝ) (m β : E → ℝ) (α : ℝ)

/-- The state `(x, Y)` of the construction: the point `x` and the saturated set `Y`. -/
structure State (E : Type*) where
  /-- The point `x`. -/
  x : E → ℝ
  /-- The saturated set `Y`. -/
  Y : Finset E

/-- The water level `λ := max({ρ_e(x) : e ∈ Ê \ Y} ∪ {0})` (`eq:A-level`). -/
noncomputable def level (s : State E) : ℝ :=
  (insert 0 ((hatE m α \ s.Y).image (marg m β α s.x))).max' (insert_nonempty _ _)

/-- The active set `S* := {e ∈ Ê \ Y : ρ_e(x) = λ}` (`eq:A-level`). -/
noncomputable def active (s : State E) : Finset E :=
  (hatE m α \ s.Y).filter fun e => marg m β α s.x e = level m β α s

/-- The admission level `λ' := max({α m_e : e ∈ Ê \ (Y ∪ S*)} ∪ {0})` (`eq:A-step`). -/
noncomputable def admLevel (s : State E) : ℝ :=
  (insert 0 ((hatE m α \ (s.Y ∪ active m β α s)).image fun e => α * m e)).max'
    (insert_nonempty _ _)

/-- The step `Δ := min{d(x, S*), λ − λ'}` (`eq:A-step`). -/
noncomputable def stepSize (s : State E) : ℝ :=
  min (dmax f β s.x (active m β α s)) (level m β α s - admLevel m β α s)

/-- One step (`eq:A-step`): `x⁺ := x + Δ v^{S*}`, and `Y⁺ := T(x⁺)` if `Δ = d(x, S*)`,
`Y⁺ := Y` otherwise. -/
noncomputable def step (s : State E) : State E where
  x := s.x + stepSize f m β α s • vS β (active m β α s)
  Y := if stepSize f m β α s = dmax f β s.x (active m β α s) then
      maxTight f m α (s.x + stepSize f m β α s • vS β (active m β α s))
    else s.Y

/-- The start: `x = 0` and `Y = ∅`. -/
def init : State E := ⟨0, ∅⟩

/-- The state after `k` passes of the while loop of `alg:waterfilling`: a step (`eq:A-step`) while
`λ > 0`, and no change once `λ = 0`. -/
noncomputable def run : ℕ → State E
  | 0 => init
  | k + 1 => if 0 < level m β α (run k) then step f m β α (run k) else run k

open Classical in
/-- The number of steps: the first `k` with `λ = 0`, where the while loop stops (`0` if there is
none; `iters_spec` shows there is one, at most `2|Ê|`). -/
noncomputable def iters : ℕ :=
  if h : ∃ k, ¬ 0 < level m β α (run f m β α k) then Nat.find h else 0

/-- **`alg:waterfilling`** (Algorithm 1, `appB-quadratic.tex:186-199`): the output `x̄` of
water-filling, the point after the last step, which line 7 returns. Line 1 is `init` with `level`
and `active` (`eq:A-level`); the while loop of lines 2-6 is `run`, stopping after `iters` steps;
line 4 is `step` (`eq:A-step`); line 5 is `level` and `active` of the new state. `run` and `step`
take `d(x, S*)` (`dmax`) and, at a capacity event, `T(x⁺) = T(x + d(x, S*) v^{S*})` (`maxTight`) as
values; line 3 computes them by the ray computation of `lem:ray` (`rayStep`, `rayArg`), and that it
returns them in each pass of the loop is `alg_step` (lines 3-4). -/
noncomputable def waterFill : E → ℝ := (run f m β α (iters f m β α)).x

open Classical in
/-- The blocking level `λ̄_e` (`appB-quadratic.tex:81-83`): `λ − Δ` at the step at which `e` first
enters `Y`, and `0` if `e` never enters `Y`. -/
noncomputable def blockLevel (e : E) : ℝ :=
  if h : ∃ k, e ∈ (run f m β α (k + 1)).Y then
    level m β α (run f m β α (Nat.find h)) - stepSize f m β α (run f m β α (Nat.find h))
  else 0

variable {f m β α}

lemma run_succ (k : ℕ) : run f m β α (k + 1) =
    if 0 < level m β α (run f m β α k) then step f m β α (run f m β α k) else run f m β α k :=
  rfl

lemma run_succ_of_pos {k : ℕ} (h : 0 < level m β α (run f m β α k)) :
    run f m β α (k + 1) = step f m β α (run f m β α k) := by
  rw [run_succ, ite_eq_left h]

lemma run_succ_of_not_pos {k : ℕ} (h : ¬ 0 < level m β α (run f m β α k)) :
    run f m β α (k + 1) = run f m β α k := by
  rw [run_succ, ite_eq_right h]

lemma step_x (s : State E) :
    (step f m β α s).x = s.x + stepSize f m β α s • vS β (active m β α s) := rfl

lemma step_Y (s : State E) :
    (step f m β α s).Y = if stepSize f m β α s = dmax f β s.x (active m β α s) then
      maxTight f m α (step f m β α s).x else s.Y := rfl

lemma le_level {s : State E} {e : E} (he : e ∈ hatE m α \ s.Y) :
    marg m β α s.x e ≤ level m β α s :=
  le_max' _ _ (mem_insert_of_mem (mem_image_of_mem _ he))

lemma level_nonneg (s : State E) : 0 ≤ level m β α s :=
  le_max' _ _ (mem_insert_self _ _)

lemma level_le {s : State E} {c : ℝ} (h0 : 0 ≤ c)
    (h : ∀ e ∈ hatE m α \ s.Y, marg m β α s.x e ≤ c) : level m β α s ≤ c := by
  refine max'_le _ _ _ fun y hy => ?_
  rcases mem_insert.1 hy with rfl | hy
  · exact h0
  · obtain ⟨e, he, rfl⟩ := mem_image.1 hy
    exact h e he

lemma exists_level {s : State E} (hpos : 0 < level m β α s) :
    ∃ e ∈ hatE m α \ s.Y, marg m β α s.x e = level m β α s := by
  have hmem := max'_mem (insert 0 ((hatE m α \ s.Y).image (marg m β α s.x)))
    (insert_nonempty _ _)
  rcases mem_insert.1 hmem with h | h
  · exact absurd h hpos.ne'
  · obtain ⟨e, he, heq⟩ := mem_image.1 h
    exact ⟨e, he, heq⟩

lemma active_subset (s : State E) : active m β α s ⊆ hatE m α \ s.Y := filter_subset _ _

lemma active_nonempty {s : State E} (hpos : 0 < level m β α s) : (active m β α s).Nonempty := by
  obtain ⟨e, he, heq⟩ := exists_level hpos
  exact ⟨e, mem_filter.2 ⟨he, heq⟩⟩

lemma admLevel_nonneg (s : State E) : 0 ≤ admLevel m β α s :=
  le_max' _ _ (mem_insert_self _ _)

lemma le_admLevel {s : State E} {e : E} (he : e ∈ hatE m α \ (s.Y ∪ active m β α s)) :
    α * m e ≤ admLevel m β α s :=
  le_max' _ _ (mem_insert_of_mem (mem_image_of_mem (fun e => α * m e) he))

lemma exists_admLevel {s : State E} (hpos : 0 < admLevel m β α s) :
    ∃ e ∈ hatE m α \ (s.Y ∪ active m β α s), α * m e = admLevel m β α s := by
  have hmem := max'_mem (insert 0 ((hatE m α \ (s.Y ∪ active m β α s)).image fun e => α * m e))
    (insert_nonempty _ _)
  rcases mem_insert.1 hmem with h | h
  · exact absurd h hpos.ne'
  · obtain ⟨e, he, heq⟩ := mem_image.1 h
    exact ⟨e, he, heq⟩

/-- The saturated sets lie in `Ê`. (Not in the paper: the paper leaves implicit that `Y ⊆ Ê`, as
`T(x) ⊆ Ê` by definition; steps (4) and (5) of the proof of `lem:wfstructure` use it.) -/
lemma run_Y_subset (k : ℕ) : (run f m β α k).Y ⊆ hatE m α := by
  induction k with
  | zero => exact empty_subset _
  | succ k ih =>
    rw [run_succ]
    split_ifs
    · rw [step_Y]
      split_ifs
      · exact maxTight_subset _
      · exact ih
    · exact ih

/-- `x_e = 0` for `e ∉ Ê` at every state. (Not in the paper: the paper keeps `x_e = 0` outside `Ê`
by construction, "We keep `x_e = 0` for the unprofitable elements outside `Ê`".) -/
lemma run_x_eq_zero {e : E} (he : e ∉ hatE m α) (k : ℕ) : (run f m β α k).x e = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [run_succ]
    split_ifs
    · rw [step_x, add_smul_apply, ih,
        vS_of_notMem fun h => he (mem_sdiff.1 (active_subset _ h)).1, mul_zero, add_zero]
    · exact ih

/-- `ρ_e = 0` for `e ∉ Ê` at every state. (Not in the paper: the paper leaves the elements outside
`Ê` implicit, "We keep `x_e = 0` for the unprofitable elements outside `Ê`".) -/
lemma marg_eq_zero_of_notMem (H : Hyp f m β α) {e : E} (he : e ∉ hatE m α) (k : ℕ) :
    marg m β α (run f m β α k).x e = 0 := by
  rw [marg, run_x_eq_zero he k, H.am_eq_zero he, mul_zero, sub_zero]

/-- Nested steps `j → j + 1` for `j < k` give `Y_i ⊆ Y_k` for `i ≤ k`. (Not in the paper: the paper
leaves the induction over the steps implicit.) -/
lemma Y_subset_of_nested {k : ℕ}
    (hn : ∀ j < k, (run f m β α j).Y ⊆ (run f m β α (j + 1)).Y) {i : ℕ} (hi : i ≤ k) :
    (run f m β α i).Y ⊆ (run f m β α k).Y := by
  induction k with
  | zero =>
    obtain rfl : i = 0 := by omega
    exact Subset.rfl
  | succ k ih =>
    rcases Nat.lt_or_ge i (k + 1) with h | h
    · exact (ih (fun j hj => hn j (by omega)) (by omega)).trans (hn k (by omega))
    · obtain rfl : i = k + 1 := by omega
      exact Subset.rfl

/-- Steps that do not raise the level, `0 ≤ Δ_i` and `λ_{i+1} ≤ λ_i − Δ_i` for `i < k`, give
`λ_k ≤ λ_j` for `j ≤ k`. (Not in the paper: the paper leaves the induction over the steps
implicit.) -/
lemma level_le_of_le {k : ℕ}
    (hstep : ∀ i < k, 0 ≤ stepSize f m β α (run f m β α i) ∧
      level m β α (run f m β α (i + 1)) ≤
        level m β α (run f m β α i) - stepSize f m β α (run f m β α i))
    {j : ℕ} (hjk : j ≤ k) : level m β α (run f m β α k) ≤ level m β α (run f m β α j) := by
  induction k with
  | zero =>
    obtain rfl : j = 0 := by omega
    exact le_rfl
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · have h1 := hstep k (Nat.lt_succ_self k)
      have h2 := ih (fun i hi => hstep i (by omega)) (by omega)
      linarith [h1.1, h1.2]
    · obtain rfl : j = k + 1 := by omega
      exact le_rfl

/-- If `e` enters `Y` at step `k` (and the saturated sets are nested up to step `k`), then `k` is
the step at which `e` first enters `Y`, so `λ̄_e = λ − Δ` at step `k`. -/
lemma blockLevel_eq {k : ℕ} (hn : ∀ j < k, (run f m β α j).Y ⊆ (run f m β α (j + 1)).Y)
    {e : E} (he : e ∉ (run f m β α k).Y) (he' : e ∈ (run f m β α (k + 1)).Y) :
    blockLevel f m β α e = level m β α (run f m β α k) - stepSize f m β α (run f m β α k) := by
  have h : ∃ k, e ∈ (run f m β α (k + 1)).Y := ⟨k, he'⟩
  have hfind : Nat.find h = k := by
    refine le_antisymm (Nat.find_min' h he') ?_
    by_contra hlt
    push Not at hlt
    exact he (Y_subset_of_nested hn (Nat.succ_le_of_lt hlt) (Nat.find_spec h))
  rw [blockLevel, dite_eq_left h, hfind]

/-- An element that never enters `Y` has `λ̄_e = 0`. -/
lemma blockLevel_eq_zero {e : E} (h : ∀ k, e ∉ (run f m β α (k + 1)).Y) :
    blockLevel f m β α e = 0 := by
  rw [blockLevel, dite_eq_right]
  rintro ⟨k, hk⟩
  exact h k hk

/-! #### The structure of water-filling (`lem:wfstructure`) -/

variable (f m β α) in
/-- What the induction of the proof of `lem:wfstructure` maintains after `k` steps: the point is
feasible, the saturated sets so far are nested, `Y` is tight, `ρ_e(x) = min{α m_e, λ}` for the
unsaturated elements of `Ê`, `e ∈ Ê \ Y`, and `ρ_e(x) = min{α m_e, λ̄_e}` with `λ̄_e ≥ λ` for the
saturated elements. The unsaturated elements outside `Ê`, which the paper leaves implicit, have
`ρ_e = 0 = min{0, λ}` (`marg_eq_zero_of_notMem`, used in `wfstructure`). -/
structure Inv (k : ℕ) : Prop where
  mem : (run f m β α k).x ∈ indepPoly f
  nested : ∀ j < k, (run f m β α j).Y ⊆ (run f m β α (j + 1)).Y
  tight : IsTight f (run f m β α k).x (run f m β α k).Y
  unsat : ∀ e ∈ hatE m α \ (run f m β α k).Y,
    marg m β α (run f m β α k).x e = min (α * m e) (level m β α (run f m β α k))
  sat : ∀ e ∈ (run f m β α k).Y,
    marg m β α (run f m β α k).x e = min (α * m e) (blockLevel f m β α e) ∧
      level m β α (run f m β α k) ≤ blockLevel f m β α e

/-- `lem:wfstructure`, step (1): "Initially these identities hold, and `Y = ∅` is tight." -/
lemma inv_init (H : Hyp f m β α) : Inv f m β α 0 where
  mem := zero_mem_indepPoly H.rank
  nested := fun j hj => absurd hj (Nat.not_lt_zero j)
  tight := by
    show ∑ e ∈ (∅ : Finset E), (0 : E → ℝ) e = f ∅
    rw [sum_empty, H.rank.empty]
  unsat := fun e he => by
    have h := le_level (m := m) (β := β) (α := α) (s := run f m β α 0) he
    have h0 : marg m β α (run f m β α 0).x e = α * m e := by
      show α * m e - β e * (0 : E → ℝ) e = α * m e
      rw [Pi.zero_apply, mul_zero, sub_zero]
    rw [h0] at h ⊢
    exact (min_eq_left h).symm
  sat := fun e he => absurd he (notMem_empty e)

/-- `lem:wfstructure`, step (2) (`appB-quadratic.tex:101-102`): the identities "imply
`S* = {e ∈ Ê \ Y : α m_e ≥ λ}`. All remaining unsaturated elements have `x_e = 0` and
`α m_e ≤ λ' < λ`." -/
lemma Inv.active_waiting (H : Hyp f m β α) {k : ℕ} (hk : Inv f m β α k)
    (hpos : 0 < level m β α (run f m β α k)) :
    (∀ e, e ∈ active m β α (run f m β α k) ↔
      e ∈ hatE m α \ (run f m β α k).Y ∧ level m β α (run f m β α k) ≤ α * m e) ∧
    (∀ e ∈ hatE m α \ ((run f m β α k).Y ∪ active m β α (run f m β α k)),
      (run f m β α k).x e = 0 ∧ α * m e ≤ admLevel m β α (run f m β α k)) ∧
    admLevel m β α (run f m β α k) < level m β α (run f m β α k) := by
  set s := run f m β α k
  -- "They imply `S* = {e ∈ Ê \ Y : α m_e ≥ λ}`."
  have hact : ∀ e, e ∈ active m β α s ↔ e ∈ hatE m α \ s.Y ∧ level m β α s ≤ α * m e := by
    intro e
    simp only [active, mem_filter]
    constructor
    · rintro ⟨he, h⟩
      refine ⟨he, ?_⟩
      rw [← h, hk.unsat e he]
      exact min_le_left _ _
    · rintro ⟨he, h⟩
      exact ⟨he, by rw [hk.unsat e he, min_eq_right h]⟩
  -- "All remaining unsaturated elements have `x_e = 0` and `α m_e ≤ λ' < λ`": `α m_e < λ`, so
  -- `ρ_e(x) = α m_e` and `x_e = 0`, and `α m_e ≤ λ'`;
  have hwait : ∀ e ∈ hatE m α \ (s.Y ∪ active m β α s),
      α * m e < level m β α s ∧ s.x e = 0 ∧ α * m e ≤ admLevel m β α s := by
    intro e he
    obtain ⟨heE, heYS⟩ := mem_sdiff.1 he
    rw [mem_union, not_or] at heYS
    have hlt : α * m e < level m β α s := by
      by_contra h
      exact heYS.2 ((hact e).2 ⟨mem_sdiff.2 ⟨heE, heYS.1⟩, not_lt.1 h⟩)
    refine ⟨hlt, ?_, le_admLevel he⟩
    have hm := hk.unsat e (mem_sdiff.2 ⟨heE, heYS.1⟩)
    rw [min_eq_left hlt.le, marg] at hm
    have hb := (H.beta e).ne'
    have : β e * s.x e = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hb
  refine ⟨hact, fun e he => ⟨(hwait e he).2.1, (hwait e he).2.2⟩, ?_⟩
  -- and `λ' < λ`, as `λ'` is the maximum of `0 < λ` and of these `α m_e < λ`.
  refine (max'_lt_iff _ _).2 fun y hy => ?_
  rcases mem_insert.1 hy with rfl | hy
  · exact hpos
  · obtain ⟨e, he, rfl⟩ := mem_image.1 hy
    exact (hwait e he).1

/-- `lem:wfstructure`, the induction step (`appB-quadratic.tex:101-110`, steps (2)-(6)): if the
identities hold after `k` steps and `λ > 0`, they hold after step `k + 1`; moreover `Δ ≥ 0` and the
recomputed level is at most `λ − Δ` ("the monotonicity of the level"). -/
theorem inv_step (H : Hyp f m β α) {k : ℕ} (hk : Inv f m β α k)
    (hpos : 0 < level m β α (run f m β α k)) :
    Inv f m β α (k + 1) ∧ 0 ≤ stepSize f m β α (run f m β α k) ∧
      level m β α (run f m β α (k + 1)) ≤
        level m β α (run f m β α k) - stepSize f m β α (run f m β α k) := by
  set s := run f m β α k with hs
  set S := active m β α s with hS
  set lam := level m β α s with hlam
  set lam' := admLevel m β α s with hlam'
  set Δ := stepSize f m β α s with hΔ
  have hrun : run f m β α (k + 1) = step f m β α s := run_succ_of_pos hpos
  have hxE : ∀ e ∉ hatE m α, s.x e = 0 := fun e he => run_x_eq_zero he k
  have hSne : S.Nonempty := active_nonempty hpos
  have hSE : S ⊆ hatE m α := (active_subset s).trans sdiff_subset
  have hspec := dmax_spec H.rank H.beta hk.mem hxE hSne hSE
  -- (2) "They imply `S* = {e ∈ Ê \ Y : α m_e ≥ λ}`. All remaining unsaturated elements have
  -- `x_e = 0` and `α m_e ≤ λ' < λ`."
  obtain ⟨hact, hwait, hlt⟩ := hk.active_waiting H hpos
  -- (3) "Since `0 ≤ Δ ≤ d(x, S*)`, the new point is feasible."
  have hΔ0 : 0 ≤ Δ := le_min hspec.1.1.1 (by linarith)
  have hΔd : Δ ≤ dmax f β s.x S := min_le_left _ _
  have hmem : (step f m β α s).x ∈ indepPoly f := by
    refine mem_indepPoly_of_le hspec.1.1.2 (fun e => ?_) (fun e => ?_)
    · rw [step_x, add_smul_apply]
      exact add_nonneg (hk.mem.1 e) (mul_nonneg hΔ0 (vS_nonneg H.beta S e))
    · rw [step_x, add_smul_apply, add_smul_apply]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hΔd (vS_nonneg H.beta S e))
  -- (4) "The coordinates of `Y` do not change, so `Y` remains tight and, at a capacity event, is
  -- contained in `T(x⁺)`."
  have hYfix : ∀ e ∈ s.Y, (step f m β α s).x e = s.x e := by
    intro e he
    have heS : e ∉ S := fun h => (mem_sdiff.1 (active_subset s h)).2 he
    rw [step_x, add_smul_apply, vS_of_notMem heS, mul_zero, add_zero]
  have hYtight : IsTight f (step f m β α s).x s.Y := by
    unfold IsTight
    rw [sum_congr rfl hYfix]
    exact hk.tight
  have hnest : s.Y ⊆ (step f m β α s).Y := by
    rw [step_Y]
    split_ifs
    · exact subset_maxTight (run_Y_subset k) hYtight
    · exact Subset.rfl
  have htight : IsTight f (step f m β α s).x (step f m β α s).Y := by
    have hY := step_Y (f := f) (m := m) (β := β) (α := α) s
    split_ifs at hY
    · rw [hY]
      exact maxTight_tight H.rank hmem
    · rw [hY]
      exact hYtight
  -- (5) "Active marginals become `λ − Δ ≥ λ'`, while waiting elements stay at zero allocation."
  have hmact : ∀ e ∈ S, marg m β α (step f m β α s).x e = lam - Δ := by
    intro e he
    rw [step_x, marg_add_smul_vS H.beta, ite_eq_left he, (mem_filter.1 he).2]
  have hlam'Δ : lam' ≤ lam - Δ := by
    have : Δ ≤ lam - lam' := min_le_right _ _
    linarith
  have hxwait : ∀ e ∈ hatE m α \ (s.Y ∪ S), (step f m β α s).x e = 0 := by
    intro e he
    have heS : e ∉ S := fun h => (mem_sdiff.1 he).2 (mem_union_right _ h)
    rw [step_x, add_smul_apply, vS_of_notMem heS, mul_zero, add_zero]
    exact (hwait e he).1
  -- "Thus the identities hold at level `λ − Δ`, also for newly saturated elements."
  have hunsat5 : ∀ e ∈ hatE m α \ s.Y,
      marg m β α (step f m β α s).x e = min (α * m e) (lam - Δ) := by
    intro e he
    by_cases heS : e ∈ S
    · rw [hmact e heS, min_eq_right]
      linarith [((hact e).1 heS).2]
    · have hw : e ∈ hatE m α \ (s.Y ∪ S) := by
        rw [mem_sdiff, mem_union, not_or]
        exact ⟨(mem_sdiff.1 he).1, (mem_sdiff.1 he).2, heS⟩
      rw [marg, hxwait e hw, mul_zero, sub_zero, min_eq_left ((hwait e hw).2.trans hlam'Δ)]
  have hsat5 : ∀ e ∈ (step f m β α s).Y,
      marg m β α (step f m β α s).x e = min (α * m e) (blockLevel f m β α e) ∧
        lam - Δ ≤ blockLevel f m β α e := by
    intro e he
    by_cases hold : e ∈ s.Y
    · have heS : e ∉ S := fun h => (mem_sdiff.1 (active_subset s h)).2 hold
      rw [step_x, marg_add_smul_vS H.beta, ite_eq_right heS]
      exact ⟨(hk.sat e hold).1, by linarith [(hk.sat e hold).2]⟩
    · -- a newly saturated element: `λ̄_e = λ − Δ`
      have he' : e ∈ (run f m β α (k + 1)).Y := by rw [hrun]; exact he
      have hbl : blockLevel f m β α e = lam - Δ := blockLevel_eq hk.nested hold he'
      have heE : e ∈ hatE m α := run_Y_subset (k + 1) he'
      rw [hbl]
      exact ⟨hunsat5 e (mem_sdiff.2 ⟨heE, hold⟩), le_rfl⟩
  -- (6) "Recomputing the largest unsaturated marginal can only lower this level."
  have hunsat' : ∀ e ∈ hatE m α \ (step f m β α s).Y, e ∈ hatE m α \ s.Y := fun e he =>
    mem_sdiff.2 ⟨(mem_sdiff.1 he).1, fun h => (mem_sdiff.1 he).2 (hnest h)⟩
  have hlev : level m β α (step f m β α s) ≤ lam - Δ := by
    refine level_le (by linarith [admLevel_nonneg (m := m) (β := β) (α := α) s]) fun e he => ?_
    rw [hunsat5 e (hunsat' e he)]
    exact min_le_right _ _
  -- "If it does, all remaining unsaturated marginals equal their initial values, so the
  -- identities still hold."
  have hunsat6 : ∀ e ∈ hatE m α \ (step f m β α s).Y,
      marg m β α (step f m β α s).x e = min (α * m e) (level m β α (step f m β α s)) := by
    intro e he
    rcases hlev.lt_or_eq with hlow | heq
    · have h1 : marg m β α (step f m β α s).x e ≤ level m β α (step f m β α s) := le_level he
      have h2 : marg m β α (step f m β α s).x e = α * m e := by
        rw [hunsat5 e (hunsat' e he)] at h1 ⊢
        refine min_eq_left (le_of_not_gt fun h => ?_)
        rw [min_eq_right h.le] at h1
        linarith
      rw [h2, min_eq_left (h2 ▸ h1)]
    · rw [heq]
      exact hunsat5 e (hunsat' e he)
  -- "This proves the induction and the monotonicity of the level."
  refine ⟨⟨?_, fun j hj => ?_, ?_, ?_, fun e he => ?_⟩, hΔ0, by rw [hrun]; exact hlev⟩
  · rw [hrun]; exact hmem
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact hk.nested j hj
    · rw [hrun]; exact hnest
  · rw [hrun]; exact htight
  · rw [hrun]; exact hunsat6
  · rw [hrun] at he ⊢
    exact ⟨(hsat5 e he).1, hlev.trans (hsat5 e he).2⟩

/-- `lem:wfstructure`, the induction (`appB-quadratic.tex:98-110`): the identities hold after every
number of steps. -/
theorem inv_run (H : Hyp f m β α) (k : ℕ) : Inv f m β α k := by
  induction k with
  | zero => exact inv_init H
  | succ k ih =>
    by_cases hpos : 0 < level m β α (run f m β α k)
    · exact (inv_step H ih hpos).1
    · have h := run_succ_of_not_pos hpos
      refine ⟨by rw [h]; exact ih.mem, fun j hj => ?_, by rw [h]; exact ih.tight,
        by rw [h]; exact ih.unsat, by rw [h]; exact ih.sat⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact ih.nested j hj
      · rw [h]

/-- `lem:wfstructure`, step (7) (`appB-quadratic.tex:112-118`): if the level is positive before each
of the first `N` steps, then `N ≤ 2|Ê|`. The steps are counted by kind: capacity steps
(`Δ = d(x, S*)`), other steps with `λ' > 0`, and other steps with `λ' = 0`. -/
theorem steps_le (H : Hyp f m β α) {N : ℕ} (hN : ∀ k < N, 0 < level m β α (run f m β α k)) :
    N ≤ 2 * (hatE m α).card := by
  have hinv : ∀ k, Inv f m β α k := inv_run H
  have hstep : ∀ k < N, 0 ≤ stepSize f m β α (run f m β α k) ∧
      level m β α (run f m β α (k + 1)) ≤
        level m β α (run f m β α k) - stepSize f m β α (run f m β α k) :=
    fun k hk => (inv_step H (hinv k) (hN k hk)).2
  -- the capacity steps `C`, and the other steps with `λ' > 0` (`A`) and with `λ' = 0` (`Z`)
  set C := (range N).filter fun k =>
    stepSize f m β α (run f m β α k) = dmax f β (run f m β α k).x (active m β α (run f m β α k))
    with hC
  set R := (range N).filter fun k =>
    ¬ stepSize f m β α (run f m β α k) = dmax f β (run f m β α k).x (active m β α (run f m β α k))
    with hR
  set A := R.filter fun k => 0 < admLevel m β α (run f m β α k) with hA
  set Z := R.filter fun k => ¬ 0 < admLevel m β α (run f m β α k) with hZ
  have hcard : N = C.card + (A.card + Z.card) := by
    rw [hA, hZ, card_filter_add_card_filter_not, hC, hR, card_filter_add_card_filter_not,
      card_range]
  -- `Δ = λ − λ'` at a step that is not a capacity step
  have hΔ : ∀ k ∈ R, stepSize f m β α (run f m β α k) =
      level m β α (run f m β α k) - admLevel m β α (run f m β α k) := fun k hk =>
    (min_choice _ _).resolve_left (mem_filter.1 hk).2
  -- (7a) "Every capacity step saturates an active element by (`eq:A-dmax`), so there are at most
  -- `|Ê|` such steps."
  have hCcard : C.card ≤ (hatE m α).card := by
    refine card_le_card_of_forall_subsingleton
      (fun k e => e ∈ active m β α (run f m β α k) ∧ e ∈ (run f m β α (k + 1)).Y) ?_ ?_
    · intro k hk
      obtain ⟨hkN, hcap⟩ := mem_filter.1 hk
      have hpos := hN k (mem_range.1 hkN)
      have hSE : active m β α (run f m β α k) ⊆ hatE m α := (active_subset _).trans sdiff_subset
      obtain ⟨e, he⟩ := maxTight_dmax_meets H.rank H.beta (hinv k).mem
        (fun e he => run_x_eq_zero he k) (active_nonempty hpos) hSE
      refine ⟨e, hSE (mem_inter.1 he).2, (mem_inter.1 he).2, ?_⟩
      rw [run_succ_of_pos hpos, step_Y, ite_eq_left hcap, step_x, hcap]
      exact (mem_inter.1 he).1
    · intro e _ k₁ hk₁ k₂ hk₂
      -- an element enters `Y` at one step only
      have key : ∀ i j, i < j → e ∈ (run f m β α (i + 1)).Y →
          e ∈ active m β α (run f m β α j) → False := fun i j hij hi hj =>
        (mem_sdiff.1 (active_subset _ hj)).2
          (Y_subset_of_nested (hinv j).nested (Nat.succ_le_of_lt hij) hi)
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact key k₁ k₂ h hk₁.2.2 hk₂.2.1
      · exact key k₂ k₁ h hk₂.2.2 hk₁.2.1
  -- (7b) "Every other step with `λ' > 0` admits a previously inactive element: its initial
  -- marginal `λ'` is strictly below the current level and hence below every earlier active level.
  -- There are at most `|Ê| − 1` such steps when `Ê ≠ ∅`, since the first active set is nonempty."
  have hAcard : (hatE m α).Nonempty → A.card ≤ (hatE m α).card - 1 := by
    intro hE
    -- the first active set is nonempty: at `x = 0`, `λ ≥ ρ_e = α m_e > 0` for `e ∈ Ê`
    have hS0 : (active m β α (run f m β α 0)).Nonempty := by
      obtain ⟨e, he⟩ := hE
      refine active_nonempty ((mem_hatE.1 he).trans_le ?_)
      have h := le_level (m := m) (β := β) (α := α) (s := run f m β α 0)
        (mem_sdiff.2 ⟨he, notMem_empty e⟩)
      have h0 : marg m β α (run f m β α 0).x e = α * m e := by
        show α * m e - β e * (0 : E → ℝ) e = α * m e
        rw [Pi.zero_apply, mul_zero, sub_zero]
      rwa [h0] at h
    have ht : (hatE m α \ active m β α (run f m β α 0)).card ≤ (hatE m α).card - 1 := by
      rw [card_sdiff_of_subset ((active_subset _).trans sdiff_subset)]
      have := hS0.card_pos
      omega
    refine (card_le_card_of_forall_subsingleton (fun k e => e ∈ active m β α (run f m β α (k + 1)) ∧
      ∀ j ≤ k, e ∉ active m β α (run f m β α j)) ?_ ?_).trans ht
    · intro k hk
      obtain ⟨hkR, hadm⟩ := mem_filter.1 hk
      have hkN := mem_range.1 (mem_filter.1 hkR).1
      have hncap := (mem_filter.1 hkR).2
      have hpos := hN k hkN
      obtain ⟨-, hwait, hlt⟩ := (hinv k).active_waiting H hpos
      -- the element `e'` with initial marginal `α m_{e'} = λ'`
      obtain ⟨e', he', heq⟩ := exists_admLevel hadm
      have he'E : e' ∈ hatE m α := (mem_sdiff.1 he').1
      have he'S : e' ∉ active m β α (run f m β α k) :=
        fun h => (mem_sdiff.1 he').2 (mem_union_right _ h)
      have hY : (run f m β α (k + 1)).Y = (run f m β α k).Y := by
        rw [run_succ_of_pos hpos, step_Y, ite_eq_right hncap]
      have he'Y : e' ∉ (run f m β α (k + 1)).Y := by
        rw [hY]
        exact fun h => (mem_sdiff.1 he').2 (mem_union_left _ h)
      have hx : (run f m β α (k + 1)).x e' = 0 := by
        rw [run_succ_of_pos hpos, step_x, add_smul_apply, vS_of_notMem he'S, mul_zero, add_zero]
        exact (hwait e' he').1
      have hmarg : marg m β α (run f m β α (k + 1)).x e' = admLevel m β α (run f m β α k) := by
        rw [marg, hx, mul_zero, sub_zero, heq]
      -- after the step the level is `λ'`, so `e'` is active
      have hlev : level m β α (run f m β α (k + 1)) = admLevel m β α (run f m β α k) := by
        refine le_antisymm ?_ ?_
        · have := (hstep k hkN).2
          rw [hΔ k hkR] at this
          linarith
        · rw [← hmarg]
          exact le_level (mem_sdiff.2 ⟨he'E, he'Y⟩)
      -- `e'` was inactive at every earlier step: `α m_{e'} = λ' < λ ≤ λ_j`
      have hprev : ∀ j ≤ k, e' ∉ active m β α (run f m β α j) := by
        intro j hj hjact
        have hposj := hN j (by omega)
        have h1 := ((((hinv j).active_waiting H hposj).1 e').1 hjact).2
        have h2 := level_le_of_le (fun i hi => hstep i (by omega)) hj
        rw [heq] at h1
        linarith
      exact ⟨e', mem_sdiff.2 ⟨he'E, hprev 0 (Nat.zero_le k)⟩,
        mem_filter.2 ⟨mem_sdiff.2 ⟨he'E, he'Y⟩, hmarg.trans hlev.symm⟩, hprev⟩
    · intro e _ k₁ hk₁ k₂ hk₂
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact hk₂.2.2 (k₁ + 1) h hk₁.2.1
      · exact hk₁.2.2 (k₂ + 1) h hk₂.2.1
  -- (7c) "A remaining step has `λ' = 0` and terminates the construction."
  have hZcard : Z.card ≤ 1 := by
    have key : ∀ k ∈ Z, k + 1 = N := by
      intro k hk
      obtain ⟨hkR, hadm⟩ := mem_filter.1 hk
      have hkN := mem_range.1 (mem_filter.1 hkR).1
      have hadm0 : admLevel m β α (run f m β α k) = 0 :=
        le_antisymm (not_lt.1 hadm) (admLevel_nonneg _)
      have h1 := (hstep k hkN).2
      rw [hΔ k hkR, hadm0, sub_zero, sub_self] at h1
      by_contra hne
      have := hN (k + 1) (by omega)
      linarith
    exact card_le_one.2 fun k₁ hk₁ k₂ hk₂ => by
      have := key k₁ hk₁
      have := key k₂ hk₂
      omega
  -- "If `Ê = ∅`, no step is taken."
  rcases (hatE m α).eq_empty_or_nonempty with hE | hE
  · rcases Nat.eq_zero_or_pos N with h | h
    · omega
    · exfalso
      have h0 := hN 0 h
      have : level m β α (run f m β α 0) ≤ 0 := level_le le_rfl fun e he => by
        rw [hE] at he
        simp at he
      linarith
  -- Otherwise `N ≤ |Ê| + (|Ê| − 1) + 1 = 2|Ê|`.
  have := hAcard hE
  have := hE.card_pos
  omega

/-- `lem:wfstructure`, the number of steps: the construction stops after `iters ≤ 2|Ê|` steps;
the level is positive before each of them and zero after the last. -/
theorem iters_spec (H : Hyp f m β α) :
    iters f m β α ≤ 2 * (hatE m α).card ∧
      (∀ k < iters f m β α, 0 < level m β α (run f m β α k)) ∧
      level m β α (run f m β α (iters f m β α)) = 0 := by
  have hex : ∃ k, ¬ 0 < level m β α (run f m β α k) := by
    by_contra h
    push Not at h
    have := steps_le H (N := 2 * (hatE m α).card + 1) fun k _ => h k
    omega
  have hiters : iters f m β α = Nat.find hex := by rw [iters, dite_eq_left hex]
  have hmin : ∀ k < iters f m β α, 0 < level m β α (run f m β α k) := by
    intro k hk
    rw [hiters] at hk
    have := Nat.find_min hex hk
    push Not at this
    exact this
  refine ⟨steps_le H hmin, hmin, ?_⟩
  have := Nat.find_spec hex
  rw [← hiters] at this
  exact le_antisymm (not_lt.1 this) (level_nonneg _)

/-- After the last step the state does not change (the encoding of the while loop by `run`). -/
lemma run_eq_final (H : Hyp f m β α) {k : ℕ} (hk : iters f m β α ≤ k) :
    run f m β α k = run f m β α (iters f m β α) := by
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k _ ih =>
    have hnot : ¬ 0 < level m β α (run f m β α k) := by
      rw [ih, (iters_spec H).2.2]
      exact lt_irrefl 0
    rw [run_succ_of_not_pos hnot, ih]

/-- Every saturated set lies in the last one. (Not in the paper: the paper leaves the induction over
the steps implicit.) -/
lemma Y_subset_final (H : Hyp f m β α) (k : ℕ) :
    (run f m β α k).Y ⊆ (run f m β α (iters f m β α)).Y := by
  rcases le_total k (iters f m β α) with h | h
  · exact Y_subset_of_nested (inv_run H _).nested h
  · rw [run_eq_final H h]

/-- **`lem:wfstructure`** (Lemma B.2, statement
`appB-quadratic.tex:85-95`, proof `:97-120`). The construction remains feasible, its saturated sets
are nested and tight, and its water level, including the level `λ − Δ` reached at the end of each
step, never increases: in step `k` it goes from `λ_k` down to `λ_k − Δ_k` (`Δ_k ≥ 0`), and the
recomputed level is `λ_{k+1} ≤ λ_k − Δ_k`. Throughout, every unsaturated element `e ∉ Y` has
`ρ_e(x) = min{α m_e, λ}`, and every saturated element `e ∈ Y` has `ρ_e(x) = min{α m_e, λ̄_e}` with
`λ̄_e ≥ λ`. It stops after at most `2|Ê|` steps (the level is positive before each of the `iters`
steps and zero after the last) at a point `x̄` satisfying (`eq:A-terminal`)
`ρ_e(x̄) = min{α m_e, λ̄_e} ≥ 0` for every `e ∈ E`. "Throughout" is after every number `k` of steps
(`run f m β α k`); an unsaturated element outside `Ê`, which the construction keeps at `x_e = 0`,
has `ρ_e = 0 = min{0, λ}`.

The paper's steps: (1) the identities `ρ_e(x) = min{α m_e, λ}` for unsaturated and
`ρ_e(x) = min{α m_e, λ̄_e}`, `λ̄_e ≥ λ`, for saturated elements are maintained (`Inv`, for the
unsaturated elements of `Ê`; the paper leaves those outside `Ê` implicit,
`marg_eq_zero_of_notMem`), and hold initially (`inv_init`); (2) they give `S*` and the waiting
elements (`Inv.active_waiting`); (3) feasibility, (4) `Y` stays tight and lies in `T(x⁺)`, (5) the
identities at `λ − Δ`, (6) recomputing the level (`inv_step`, the induction `inv_run`); (7) the
count by kinds of steps (`steps_le`, `iters_spec`); (8) the terminal identities. -/
theorem wfstructure (H : Hyp f m β α) :
    (∀ k, (run f m β α k).x ∈ indepPoly f) ∧
      (∀ k, (run f m β α k).Y ⊆ (run f m β α (k + 1)).Y) ∧
      (∀ k, IsTight f (run f m β α k).x (run f m β α k).Y) ∧
      (∀ k < iters f m β α, 0 ≤ stepSize f m β α (run f m β α k) ∧
        level m β α (run f m β α (k + 1)) ≤
          level m β α (run f m β α k) - stepSize f m β α (run f m β α k)) ∧
      (∀ k, ∀ e ∉ (run f m β α k).Y,
        marg m β α (run f m β α k).x e = min (α * m e) (level m β α (run f m β α k))) ∧
      (∀ k, ∀ e ∈ (run f m β α k).Y,
        marg m β α (run f m β α k).x e = min (α * m e) (blockLevel f m β α e) ∧
          level m β α (run f m β α k) ≤ blockLevel f m β α e) ∧
      (iters f m β α ≤ 2 * (hatE m α).card ∧
        (∀ k < iters f m β α, 0 < level m β α (run f m β α k)) ∧
        level m β α (run f m β α (iters f m β α)) = 0) ∧
      ∀ e, marg m β α (waterFill f m β α) e = min (α * m e) (blockLevel f m β α e) ∧
        0 ≤ min (α * m e) (blockLevel f m β α e) := by
  -- (1)-(6) "We maintain `ρ_e(x) = min{α m_e, λ}` for unsaturated elements and
  -- `ρ_e(x) = min{α m_e, λ̄_e}` with `λ̄_e ≥ λ` for saturated elements. … This proves the
  -- induction and the monotonicity of the level."
  have hinv : ∀ k, Inv f m β α k := inv_run H
  have hmono : ∀ k, 0 < level m β α (run f m β α k) →
      0 ≤ stepSize f m β α (run f m β α k) ∧ level m β α (run f m β α (k + 1)) ≤
        level m β α (run f m β α k) - stepSize f m β α (run f m β α k) :=
    fun k hpos => (inv_step H (hinv k) hpos).2
  -- The identity for every unsaturated element `e ∉ Y`: the induction's for `e ∈ Ê`, and
  -- `ρ_e = 0 = min{0, λ}` for an element outside `Ê` (`marg_eq_zero_of_notMem`).
  have hunsat : ∀ k, ∀ e ∉ (run f m β α k).Y,
      marg m β α (run f m β α k).x e = min (α * m e) (level m β α (run f m β α k)) := by
    intro k e he
    by_cases hE : e ∈ hatE m α
    · exact (hinv k).unsat e (mem_sdiff.2 ⟨hE, he⟩)
    · rw [marg_eq_zero_of_notMem H hE k, H.am_eq_zero hE, min_eq_left (level_nonneg _)]
  -- (7) "Every capacity step saturates an active element … If `Ê = ∅`, no step is taken."
  have hiters := iters_spec H
  refine ⟨fun k => (hinv k).mem, fun k => (hinv (k + 1)).nested k (Nat.lt_succ_self k),
    fun k => (hinv k).tight, fun k hk => hmono k (hiters.2.1 k hk), hunsat,
    fun k e he => (hinv k).sat e he, hiters, fun e => ?_⟩
  -- (8) "At termination all unsaturated marginals are zero, giving (`eq:A-terminal`)."
  have hlev0 := hiters.2.2
  show marg m β α (run f m β α (iters f m β α)).x e = _ ∧ _
  by_cases hY : e ∈ (run f m β α (iters f m β α)).Y
  · obtain ⟨h1, h2⟩ := (hinv (iters f m β α)).sat e hY
    rw [hlev0] at h2
    exact ⟨h1, le_min (H.am_nonneg e) h2⟩
  · -- an unsaturated element never enters `Y`, so `λ̄_e = 0`; its marginal is
    -- `min{α m_e, 0} = 0`
    have hbl : blockLevel f m β α e = 0 :=
      blockLevel_eq_zero fun k hk => hY (Y_subset_final H (k + 1) hk)
    have hzero : marg m β α (run f m β α (iters f m β α)).x e = 0 := by
      rw [hunsat _ e hY, hlev0]
      exact min_eq_right (H.am_nonneg e)
    rw [hbl, min_eq_right (H.am_nonneg e)]
    exact ⟨hzero, le_rfl⟩

/-- `alg:waterfilling`, lines 3-4 (`appB-quadratic.tex:193-194`): in each pass of the while loop,
the ray computation of `lem:ray` at `(x, S*)` returns `d(x, S*)` and `T(x + d(x, S*) v^{S*})`, the
values that `step` takes, and the update is the step (`eq:A-step`). Step (6) of the proof of
`thm:waterfilling` uses this: each step uses one ray computation. -/
theorem alg_step (H : Hyp f m β α) {k : ℕ} (hk : k < iters f m β α) :
    rayStep f m β α (run f m β α k).x (active m β α (run f m β α k)) =
        dmax f β (run f m β α k).x (active m β α (run f m β α k)) ∧
      rayArg f m β α (run f m β α k).x (active m β α (run f m β α k)) =
        maxTight f m α ((run f m β α k).x + dmax f β (run f m β α k).x
          (active m β α (run f m β α k)) • vS β (active m β α (run f m β α k))) ∧
      run f m β α (k + 1) = step f m β α (run f m β α k) := by
  -- the point is feasible and the level positive before the step (`lem:wfstructure`), so `lem:ray`
  -- applies to `x` and `S*`
  obtain ⟨hmem, -, -, -, -, -, ⟨-, hpos, -⟩, -⟩ := wfstructure H
  obtain ⟨-, -, h1, h2, -, -⟩ := ray H (hmem k) (fun e he => run_x_eq_zero he k)
    (active_nonempty (hpos k hk)) ((active_subset _).trans sdiff_subset)
  exact ⟨h1, h2, run_succ_of_pos (hpos k hk)⟩

/-! #### The best response by water-filling (`thm:waterfilling`) -/

/-- "As the water level never increases" (`appB-quadratic.tex:163`): steps with `0 ≤ Δ_i` and
`λ_{i+1} ≤ λ_i − Δ_i` for `i < n` (the monotonicity of the level in `lem:wfstructure`) give
`λ_k − Δ_k ≤ λ_j − Δ_j` for `j ≤ k < n`: the levels `λ − Δ` at the ends of the steps decrease.
(Not in the paper: the paper leaves the induction over the steps implicit.) -/
lemma levelEnd_antitone {n : ℕ}
    (hstep : ∀ i < n, 0 ≤ stepSize f m β α (run f m β α i) ∧
      level m β α (run f m β α (i + 1)) ≤
        level m β α (run f m β α i) - stepSize f m β α (run f m β α i))
    {j k : ℕ} (hjk : j ≤ k) (hk : k < n) :
    level m β α (run f m β α k) - stepSize f m β α (run f m β α k) ≤
      level m β α (run f m β α j) - stepSize f m β α (run f m β α j) := by
  rcases hjk.eq_or_lt with rfl | hjk
  · exact le_rfl
  -- `λ_k − Δ_k ≤ λ_k ≤ λ_{j+1} ≤ λ_j − Δ_j`
  have h1 := (hstep k hk).1
  have h2 := level_le_of_le (fun i hi => hstep i (by omega)) (Nat.succ_le_of_lt hjk)
  have h3 := (hstep j (by omega)).2
  linarith

/-- "As its coordinates no longer change" (`appB-quadratic.tex:164-165`): for nested saturated sets
(`lem:wfstructure`), the coordinates of a saturated set do not change in later steps. (Not in the
paper: the paper leaves the induction over the later steps implicit; one step is step (4) of
`lem:wfstructure`, "The coordinates of `Y` do not change".) -/
lemma x_eq_of_mem_Y (hn : ∀ k, (run f m β α k).Y ⊆ (run f m β α (k + 1)).Y) {i j : ℕ}
    (hij : i ≤ j) {e : E} (he : e ∈ (run f m β α i).Y) :
    (run f m β α j).x e = (run f m β α i).x e := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hij ih =>
    by_cases hpos : 0 < level m β α (run f m β α j)
    · rw [run_succ_of_pos hpos, step_x, add_smul_apply, vS_of_notMem, mul_zero, add_zero, ih]
      exact fun h => (mem_sdiff.1 (active_subset _ h)).2
        (Y_subset_of_nested (fun l _ => hn l) hij he)
    · rw [run_succ_of_not_pos hpos, ih]

/-- The blocking level of an element: either `e` first enters `Y` at a step `k < iters` and
`λ̄_e = λ − Δ` at step `k`, or `e` never enters `Y` and `λ̄_e = 0` (the definition,
`appB-quadratic.tex:81-83`, with the nested saturated sets of `lem:wfstructure`). -/
lemma blockLevel_cases (H : Hyp f m β α) (e : E) :
    (∃ k < iters f m β α, e ∉ (run f m β α k).Y ∧ e ∈ (run f m β α (k + 1)).Y ∧
      blockLevel f m β α e = level m β α (run f m β α k) - stepSize f m β α (run f m β α k)) ∨
    ((∀ k, e ∉ (run f m β α k).Y) ∧ blockLevel f m β α e = 0) := by
  have hn := (wfstructure H).2.1
  by_cases h : ∃ k, e ∈ (run f m β α (k + 1)).Y
  · left
    set k := Nat.find h
    have hk1 : e ∈ (run f m β α (k + 1)).Y := Nat.find_spec h
    have hk0 : e ∉ (run f m β α k).Y := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · rw [hk]
        exact notMem_empty e
      · obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        have := Nat.find_min h (show j < Nat.find h by omega)
        rw [hj]
        exact this
    have hlt : k < iters f m β α := by
      by_contra hge
      push Not at hge
      have h1 : run f m β α (k + 1) = run f m β α k := by
        rw [run_eq_final H hge, run_eq_final H (by omega : iters f m β α ≤ k + 1)]
      rw [h1] at hk1
      exact hk0 hk1
    exact ⟨k, hlt, hk0, hk1, blockLevel_eq (fun j _ => hn j) hk0 hk1⟩
  · right
    push Not at h
    refine ⟨fun k => ?_, blockLevel_eq_zero h⟩
    cases k with
    | zero => exact notMem_empty e
    | succ k => exact h k

/-- The proof of `thm:waterfilling`, steps (1)-(4) of its first part, which shows that
water-filling ends at the best response (`appB-quadratic.tex:162-171`): every positive marginal
level set `A_θ(x̄)`, `θ > 0`, is tight. -/
theorem waterFill_levelSet_tight (H : Hyp f m β α) {θ : ℝ} (hθ : 0 < θ) :
    IsTight f (waterFill f m β α) (levelSet m β α (waterFill f m β α) θ) := by
  -- `lem:wfstructure`: the points are feasible, the saturated sets nested and tight, the level
  -- never increases (`0 ≤ Δ` and `λ⁺ ≤ λ − Δ` in every step), and (`eq:A-terminal`) holds at `x̄`
  obtain ⟨hmem, hnest, htight, hmono, -, -, -, hterm⟩ := wfstructure H
  -- (1) "Fix `θ > 0` and let `C_θ := {e : λ̄_e ≥ θ}`."
  set C := univ.filter fun e => θ ≤ blockLevel f m β α e with hCdef
  -- "As the water level never increases, elements saturated earlier have larger blocking levels,"
  have horder : ∀ e, ∀ k < iters f m β α, e ∈ (run f m β α (k + 1)).Y →
      level m β α (run f m β α k) - stepSize f m β α (run f m β α k) ≤ blockLevel f m β α e := by
    intro e k hk he
    rcases blockLevel_cases H e with ⟨k₀, -, he₀, -, hbl⟩ | ⟨hnever, -⟩
    · rw [hbl]
      refine levelEnd_antitone hmono ?_ hk
      by_contra hlt
      exact he₀ (Y_subset_of_nested (fun j _ => hnest j) (by omega : k + 1 ≤ k₀) he)
    · exact absurd he (hnever _)
  -- "so `C_θ` is the set saturated after the last step with `λ − Δ ≥ θ`, or empty."
  have hC : C = ∅ ∨ ∃ k < iters f m β α, C = (run f m β α (k + 1)).Y := by
    set L := (range (iters f m β α)).filter fun k =>
      θ ≤ level m β α (run f m β α k) - stepSize f m β α (run f m β α k)
    rcases L.eq_empty_or_nonempty with hL | hL
    · left
      refine filter_eq_empty_iff.2 fun e _ he => ?_
      rcases blockLevel_cases H e with ⟨k₀, hk₀, -, -, hbl⟩ | ⟨-, hbl⟩
      · rw [hbl] at he
        exact filter_eq_empty_iff.1 hL (mem_range.2 hk₀) he
      · rw [hbl] at he
        linarith
    · right
      -- the last step `k₁` with `λ − Δ ≥ θ`
      obtain ⟨k₁, hk₁, hmax⟩ := L.exists_max_image id hL
      obtain ⟨hk₁K, hk₁θ⟩ := mem_filter.1 hk₁
      refine ⟨k₁, mem_range.1 hk₁K, ?_⟩
      ext e
      simp only [hCdef, mem_filter, mem_univ, true_and]
      constructor
      · intro he
        rcases blockLevel_cases H e with ⟨k₀, hk₀, -, he₀, hbl⟩ | ⟨-, hbl⟩
        · rw [hbl] at he
          have : k₀ ≤ k₁ := hmax k₀ (mem_filter.2 ⟨mem_range.2 hk₀, he⟩)
          exact Y_subset_of_nested (fun j _ => hnest j) (by omega) he₀
        · rw [hbl] at he
          linarith
      · intro he
        exact hk₁θ.trans (horder e k₁ (mem_range.1 hk₁K) he)
  -- (2) "By `lem:wfstructure`, this is a cumulative saturated set, and as its coordinates no
  -- longer change, it stays tight at `x̄`."
  have hCt : ∑ e ∈ C, waterFill f m β α e = f C := by
    rcases hC with hC | ⟨k, hk, hC⟩
    · rw [hC, sum_empty, H.rank.empty]
    · rw [hC]
      show ∑ e ∈ (run f m β α (k + 1)).Y, (run f m β α (iters f m β α)).x e = _
      rw [sum_congr rfl fun e he => x_eq_of_mem_Y hnest (by omega : k + 1 ≤ iters f m β α) he]
      exact htight (k + 1)
  -- (3) "Equation (`eq:A-terminal`) gives `A_θ(x̄) ⊆ C_θ`, and every element of `C_θ \ A_θ(x̄)` has
  -- `ρ_e(x̄) = α m_e`, hence `x̄_e = 0`."
  set A := levelSet m β α (waterFill f m β α) θ
  have hAC : A ⊆ C := by
    intro e he
    have h1 : θ ≤ marg m β α (waterFill f m β α) e := (mem_filter.1 he).2
    rw [(hterm e).1] at h1
    exact mem_filter.2 ⟨mem_univ e, h1.trans (min_le_right _ _)⟩
  have hzero : ∀ e ∈ C, e ∉ A → waterFill f m β α e = 0 := by
    intro e he heA
    have h1 : marg m β α (waterFill f m β α) e < θ := by
      by_contra h
      exact heA (mem_filter.2 ⟨mem_univ e, not_lt.1 h⟩)
    have h2 : θ ≤ blockLevel f m β α e := (mem_filter.1 he).2
    have h3 : marg m β α (waterFill f m β α) e = α * m e := by
      rw [(hterm e).1] at h1 ⊢
      refine min_eq_left (le_of_not_gt fun h => ?_)
      rw [min_eq_right h.le] at h1
      linarith
    rw [marg] at h3
    have hb := (H.beta e).ne'
    have : β e * waterFill f m β α e = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hb
  -- (4) "Consequently, `x̄(A_θ(x̄)) = x̄(C_θ) = f(C_θ) ≥ f(A_θ(x̄)) ≥ x̄(A_θ(x̄))`."
  have h1 : ∑ e ∈ A, waterFill f m β α e = ∑ e ∈ C, waterFill f m β α e := sum_subset hAC hzero
  have h2 : f A ≤ f C := H.rank.mono hAC
  have h3 : ∑ e ∈ A, waterFill f m β α e ≤ f A := (hmem (iters f m β α)).2 A
  show ∑ e ∈ A, waterFill f m β α e = f A
  linarith

variable (f m β α) in
/-- The number of submodular minimizations of water-filling: those of the ray computation in each
step. -/
noncomputable def oracleCalls : ℕ :=
  ∑ k ∈ range (iters f m β α), rayCalls f m β α (run f m β α k).x (active m β α (run f m β α k))

variable (f m β α) in
/-- The number of further evaluations of `f` of water-filling: those of the ray computation in
each step, counted by `rayEvals` (`|S*|` singleton evaluations and one for each update in each ray
computation). The counted water-filling `waterFillC` makes exactly this many (`waterFillC_spec`).
-/
noncomputable def fEvals : ℕ :=
  ∑ k ∈ range (iters f m β α), rayEvals f m β α (run f m β α k).x (active m β α (run f m β α k))

/-! #### Water-filling with its operation counts

Step (6) of the proof of `thm:waterfilling`: "Each uses one ray computation and `O(n)` additional
work to determine the active set, the admission level, and the updates." The counted water-filling
`waterFillC` performs `alg:waterfilling` in the cost model of `Stoc.Counted`: `Ê`, and then, while
`λ > 0`, the level (`levelC`) and a step (`stepC`: the active set, the admission level, the counted
ray computation `rayC`, the step, the update and the test for a capacity event), in `runC`.
`waterFillC_spec` shows that it returns `waterFill`, makes `oracleCalls` minimizations and `fEvals`
further evaluations of `f`, and at most `6n³ + 56n² + 29n + 2` further arithmetic operations.
(Not in the paper: the paper counts in prose.) -/

open Counted

variable (f m β α)

/-- `x + Δ v^A`, coordinatewise on `A`: `β_e⁻¹`, one multiplication and one addition for each
`e ∈ A`. -/
noncomputable def updC (x : E → ℝ) (A : Finset E) (Δ : ℝ) : Counted (E → ℝ) :=
  ops (3 * A.card) (x + Δ • vS β A)

/-- The level `λ` of a state (`eq:A-level`): the set `Ê \ Y`, the margins
`ρ_e(x) = α m_e − β_e x_e` (three operations each), and their maximum with `0`. -/
noncomputable def levelC (s : State E) : Counted ℝ :=
  Counted.sdiff (hatE m α) s.Y >>=ᶜ fun U => max0 U fun e => ops 3 (marg m β α s.x e)

/-- One step (`eq:A-step`) from a state with level `lam`: the active set `S*`, the admission level
`λ'`, the ray computation of `lem:ray`, the step `Δ = min{d(x, S*), λ − λ'}`, the update of `x`,
and the test for a capacity event. -/
noncomputable def stepC (s : State E) (lam : ℝ) : Counted (State E) :=
  Counted.sdiff (hatE m α) s.Y >>=ᶜ fun U =>
  filterEq U (fun e => ops 3 (marg m β α s.x e)) lam >>=ᶜ fun A =>
  Counted.sdiff U A >>=ᶜ fun U' =>
  max0 U' (fun e => ops 1 (α * m e)) >>=ᶜ fun lam' =>
  rayC f m β α s.x A >>=ᶜ fun r =>
  ops 2 (min r.1 (lam - lam')) >>=ᶜ fun Δ =>
  updC β s.x A Δ >>=ᶜ fun x' =>
  ops 1 () >>=ᶜ fun _ =>
  ret ⟨x', if Δ = r.1 then r.2 else s.Y⟩

/-- The while loop of `alg:waterfilling`, at most `k` passes: each pass computes the level and
tests `λ > 0` (one comparison), and then takes a step. -/
noncomputable def runC : ℕ → State E → Counted (State E)
  | 0, s => ret s
  | k + 1, s =>
      levelC m β α s >>=ᶜ fun lam =>
      ops 1 () >>=ᶜ fun _ =>
      if 0 < lam then stepC f m β α s lam >>=ᶜ fun s' => runC k s' else ret s

/-- `alg:waterfilling` with its operation counts: `Ê` (one multiplication and one comparison for
each element), then at most `2|E| + 1` passes of the while loop. -/
noncomputable def waterFillC : Counted (E → ℝ) :=
  ops (2 * Fintype.card E) () >>=ᶜ fun _ =>
  runC f m β α (2 * Fintype.card E + 1) init >>=ᶜ fun s => ret s.x

variable {f m β α}

lemma levelC_val (s : State E) : (levelC m β α s).val = level m β α s := rfl

lemma stepC_val (H : Hyp f m β α) {k : ℕ} (hk : k < iters f m β α) :
    (stepC f m β α (run f m β α k) (level m β α (run f m β α k))).val =
      run f m β α (k + 1) := by
  obtain ⟨hmem, -, -, -, -, -, ⟨-, hpos, -⟩, -⟩ := wfstructure H
  have hray := (rayC_spec H (hmem k) (fun e he => run_x_eq_zero he k)
    (active_nonempty (hpos k hk)) ((active_subset _).trans sdiff_subset)).1
  obtain ⟨h1, h2, h3⟩ := alg_step H hk
  have hA : (filterEq ((hatE m α : Finset E) \ (run f m β α k).Y)
      (fun e => ops 3 (marg m β α (run f m β α k).x e)) (level m β α (run f m β α k))).val =
      active m β α (run f m β α k) := rfl
  have hU : ((hatE m α : Finset E) \ (run f m β α k).Y) \ active m β α (run f m β α k) =
      (hatE m α : Finset E) \ ((run f m β α k).Y ∪ active m β α (run f m β α k)) := by
    rw [sdiff_sdiff_left, sup_eq_union]
  have hL : (max0 (((hatE m α : Finset E) \ (run f m β α k).Y) \ active m β α (run f m β α k))
      (fun e => ops 1 (α * m e))).val = admLevel m β α (run f m β α k) := by
    simp only [val_max0, val_ops, hU, admLevel]
  rw [h3]
  simp only [stepC, val_bind, val_sdiff]
  rw [hA, hL, hray]
  simp only [val_ops, updC, val_ret, h1, h2, step, stepSize]
  split_ifs with h <;> simp [h]

/-- The while loop returns the terminal state. From step `j ≤ N` (`N = iters`), with more than
`N − j` passes left, the loop returns `run N` after the passes `j, …, N − 1`, each with its level,
test and step, and the last level and test. -/
lemma runC_spec (H : Hyp f m β α) :
    ∀ k j, j ≤ iters f m β α → iters f m β α < j + k →
      (runC f m β α k (run f m β α j)).val = run f m β α (iters f m β α) ∧
      (runC f m β α k (run f m β α j)).cost =
        ∑ i ∈ Finset.Ico j (iters f m β α),
          ((levelC m β α (run f m β α i)).cost + ((1, 0, 0) +
            (stepC f m β α (run f m β α i) (level m β α (run f m β α i))).cost)) +
        ((levelC m β α (run f m β α (iters f m β α))).cost + (1, 0, 0)) := by
  obtain ⟨-, hpos, hlev0⟩ := iters_spec H
  intro k
  induction k with
  | zero => intro j hj h; omega
  | succ k ih =>
    intro j hj hjk
    rcases hj.lt_or_eq with hlt | rfl
    · obtain ⟨h1, h2⟩ := ih (j + 1) hlt (by omega)
      have hs := stepC_val H hlt
      simp only [runC, val_bind, cost_bind, levelC_val, hpos j hlt, ite_true, cost_ops, hs, h1, h2,
        true_and]
      rw [Finset.sum_eq_sum_Ico_succ_bot hlt]
      simp only [add_assoc]
    · simp only [runC, val_bind, cost_bind, levelC_val, hlev0, lt_irrefl, ite_false, val_ret,
        cost_ret, cost_ops, Finset.Ico_self, Finset.sum_empty, zero_add, add_zero, true_and]

lemma levelC_cost (s : State E) :
    (levelC m β α s).cost = ((hatE m α).card + 4 * (hatE m α \ s.Y).card + 1, 0, 0) := by
  simp [levelC, Prod.ext_iff]
  ring

lemma stepC_cost (k : ℕ) :
    (stepC f m β α (run f m β α k) (level m β α (run f m β α k))).cost =
      ((hatE m α).card + 5 * ((hatE m α : Finset E) \ (run f m β α k).Y).card +
        2 * (((hatE m α : Finset E) \ (run f m β α k).Y) \ active m β α (run f m β α k)).card +
        3 * (active m β α (run f m β α k)).card + 4, 0, 0) +
      (rayC f m β α (run f m β α k).x (active m β α (run f m β α k))).cost := by
  have hA : (filterEq ((hatE m α : Finset E) \ (run f m β α k).Y)
      (fun e => ops 3 (marg m β α (run f m β α k).x e)) (level m β α (run f m β α k))).val =
      active m β α (run f m β α k) := rfl
  simp only [stepC, cost_bind, val_sdiff, cost_sdiff, cost_filterEq, cost_ops]
  rw [hA]
  simp only [cost_max0, cost_ops, val_ops, updC, cost_ret, sum_const, smul_eq_mul, Prod.ext_iff,
    Prod.fst_add, Prod.snd_add, Prod.smul_mk]
  refine ⟨?_, ?_, ?_⟩ <;> simp
  ring

/-- The counted water-filling (steps (6) and (7) of `thm:waterfilling`; not in the paper: the
paper counts in prose): `waterFillC` returns the terminal point `waterFill`, with exactly
`oracleCalls` minimizations and `fEvals` further evaluations of `f`, and at most
`6n³ + 56n² + 29n + 2` further arithmetic operations (comparisons included), `n = |E|`. -/
lemma waterFillC_spec (H : Hyp f m β α) :
    (waterFillC f m β α).val = waterFill f m β α ∧
      (waterFillC f m β α).cost.2.1 = oracleCalls f m β α ∧
      (waterFillC f m β α).cost.2.2 = fEvals f m β α ∧
      (waterFillC f m β α).cost.1 ≤
        6 * Fintype.card E ^ 3 + 56 * Fintype.card E ^ 2 + 29 * Fintype.card E + 2 := by
  obtain ⟨hmem, -, -, -, -, -, ⟨hiters, hpos, -⟩, -⟩ := wfstructure H
  set n := Fintype.card E
  set N := iters f m β α
  have hE : (hatE m α).card ≤ n := card_le_univ _
  obtain ⟨hv, hc⟩ := runC_spec H (2 * n + 1) 0 (Nat.zero_le _) (by omega)
  have hray : ∀ i < N, (rayC f m β α (run f m β α i).x (active m β α (run f m β α i))).cost.2.1 =
        rayCalls f m β α (run f m β α i).x (active m β α (run f m β α i)) ∧
      (rayC f m β α (run f m β α i).x (active m β α (run f m β α i))).cost.2.2 =
        rayEvals f m β α (run f m β α i).x (active m β α (run f m β α i)) ∧
      (rayC f m β α (run f m β α i).x (active m β α (run f m β α i))).cost.1 ≤
        4 * (active m β α (run f m β α i)).card +
          ((active m β α (run f m β α i)).card + 1) * (3 * (hatE m α).card + 5) := fun i hi =>
    (rayC_spec H (hmem i) (fun e he => run_x_eq_zero he i) (active_nonempty (hpos i hi))
      ((active_subset _).trans sdiff_subset)).2
  have hcost : (waterFillC f m β α).cost = (2 * n, 0, 0) +
      (∑ i ∈ Finset.Ico 0 N, ((levelC m β α (run f m β α i)).cost + ((1, 0, 0) +
          (stepC f m β α (run f m β α i) (level m β α (run f m β α i))).cost)) +
        ((levelC m β α (run f m β α N)).cost + (1, 0, 0))) := by
    simp only [waterFillC, cost_bind, cost_ops, cost_ret, add_zero]
    rw [show (init : State E) = run f m β α 0 from rfl, hc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [waterFillC, val_bind, val_ret]
    rw [show (init : State E) = run f m β α 0 from rfl, hv]
    rfl
  · rw [hcost, oracleCalls]
    simp only [Prod.snd_add, Prod.snd_sum, Prod.fst_sum, levelC_cost, stepC_cost,
      Prod.mk_zero_zero, zero_add, add_zero, Nat.Ico_zero_eq_range]
    exact Finset.sum_congr rfl fun i hi => (hray i (Finset.mem_range.1 hi)).1
  · rw [hcost, fEvals]
    simp only [Prod.snd_add, Prod.snd_sum, levelC_cost, stepC_cost, Prod.mk_zero_zero, zero_add,
      add_zero, Nat.Ico_zero_eq_range]
    exact Finset.sum_congr rfl fun i hi => (hray i (Finset.mem_range.1 hi)).2.1
  · rw [hcost]
    simp only [Prod.fst_add, Prod.fst_sum, levelC_cost, stepC_cost]
    set e := (hatE m α).card
    have hpass : ∀ i ∈ Finset.Ico 0 N,
        e + 4 * ((hatE m α : Finset E) \ (run f m β α i).Y).card + 1 + (1 +
          (e + 5 * ((hatE m α : Finset E) \ (run f m β α i).Y).card +
            2 * (((hatE m α : Finset E) \ (run f m β α i).Y) \
              active m β α (run f m β α i)).card +
            3 * (active m β α (run f m β α i)).card + 4 +
            (rayC f m β α (run f m β α i).x (active m β α (run f m β α i))).cost.1)) ≤
        20 * e + 6 + (e + 1) * (3 * e + 5) := fun i hi => by
      have hU : ((hatE m α : Finset E) \ (run f m β α i).Y).card ≤ e := card_le_card sdiff_subset
      have hU' : (((hatE m α : Finset E) \ (run f m β α i).Y) \
          active m β α (run f m β α i)).card ≤ e :=
        (card_le_card sdiff_subset).trans hU
      have hA : (active m β α (run f m β α i)).card ≤ e :=
        (card_le_card (active_subset _)).trans hU
      have hr := (hray i (Finset.mem_Ico.1 hi).2).2.2
      have hmul : ((active m β α (run f m β α i)).card + 1) * (3 * e + 5) ≤ (e + 1) * (3 * e + 5) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    have hsum := Finset.sum_le_sum hpass
    simp only [Finset.sum_const, Nat.card_Ico, smul_eq_mul, Nat.sub_zero] at hsum
    have hfin : e + 4 * ((hatE m α : Finset E) \ (run f m β α N).Y).card + 1 + 1 ≤ 5 * e + 2 := by
      have : ((hatE m α : Finset E) \ (run f m β α N).Y).card ≤ e := card_le_card sdiff_subset
      omega
    have hN : N ≤ 2 * n := hiters.trans (by omega)
    have hP : 20 * e + 6 + (e + 1) * (3 * e + 5) ≤ 20 * n + 6 + (n + 1) * (3 * n + 5) := by
      have : (e + 1) * (3 * e + 5) ≤ (n + 1) * (3 * n + 5) := Nat.mul_le_mul (by omega) (by omega)
      omega
    have hNP : N * (20 * e + 6 + (e + 1) * (3 * e + 5)) ≤
        (2 * n) * (20 * n + 6 + (n + 1) * (3 * n + 5)) := Nat.mul_le_mul hN hP
    have hpoly : 2 * n * (20 * n + 6 + (n + 1) * (3 * n + 5)) =
        6 * n ^ 3 + 56 * n ^ 2 + 22 * n := by ring
    omega

/-- The counts of steps (6) and (7) of the proof of `thm:waterfilling`, as a lemma of their own for
`waterFillC_time` (not in the paper; the argument of `waterfilling`): at most `2n(n + 1)`
submodular minimizations and `2n(2n + 1)` further evaluations of `f`, `n = |E|`. -/
lemma oracleCalls_fEvals_le (H : Hyp f m β α) :
    oracleCalls f m β α ≤ 2 * Fintype.card E * (Fintype.card E + 1) ∧
      fEvals f m β α ≤ 2 * Fintype.card E * (2 * Fintype.card E + 1) := by
  obtain ⟨hmem, -, -, -, -, -, ⟨hiters, hpos, -⟩, -⟩ := wfstructure H
  -- (6) at most `2|Ê| ≤ 2n` steps
  have hsteps : iters f m β α ≤ 2 * Fintype.card E := by
    have := card_le_univ (hatE m α)
    omega
  -- (7) by `lem:ray`, as `|S*| ≤ n`, at most `n + 1` minimizations and `2n + 1` evaluations in
  -- each step
  have hcount : ∀ k ∈ range (iters f m β α),
      rayCalls f m β α (run f m β α k).x (active m β α (run f m β α k)) ≤ Fintype.card E + 1 ∧
        rayEvals f m β α (run f m β α k).x (active m β α (run f m β α k)) ≤
          2 * Fintype.card E + 1 := by
    intro k hk
    obtain ⟨-, -, -, -, hcalls, hevals, -⟩ := ray H (hmem k) (fun e he => run_x_eq_zero he k)
      (active_nonempty (hpos k (mem_range.1 hk))) ((active_subset _).trans sdiff_subset)
    have := card_le_univ (active m β α (run f m β α k))
    omega
  constructor
  · calc oracleCalls f m β α ≤ ∑ _k ∈ range (iters f m β α), (Fintype.card E + 1) :=
          sum_le_sum fun k hk => (hcount k hk).1
      _ = iters f m β α * (Fintype.card E + 1) := by rw [sum_const, card_range, smul_eq_mul]
      _ ≤ 2 * Fintype.card E * (Fintype.card E + 1) := Nat.mul_le_mul_right _ hsteps
  · calc fEvals f m β α ≤ ∑ _k ∈ range (iters f m β α), (2 * Fintype.card E + 1) :=
          sum_le_sum fun k hk => (hcount k hk).2
      _ = iters f m β α * (2 * Fintype.card E + 1) := by rw [sum_const, card_range, smul_eq_mul]
      _ ≤ 2 * Fintype.card E * (2 * Fintype.card E + 1) := Nat.mul_le_mul_right _ hsteps

/-- The running time of the counted water-filling, step (8) of the proof of `thm:waterfilling`
(`stoc-sections/appB-quadratic.tex:181`; not in the paper: the paper counts in prose), for
`n = |E| ≥ 1`: "The strongly polynomial algorithm of Iwata and Orlin [IO09] finds it in time
`O(n⁵ log n)·EO + O(n⁶ log n)` … so `EO = FO + O(n)`. Multiplying by the `O(n²)` minimizations
gives the stated bound." If an evaluation of `f` takes time `FO ≥ 0` and a submodular minimization
time `TS ≤ sfmTime C₁ C₂ n FO`, the cited bound of Iwata and Orlin with constants `C₁, C₂ ≥ 0`
(cited, [IO09]), then `waterFillC` takes time at most
`(6 + 4C₁) n⁷ lg n · FO + (93 + 4C₁(C₂ + 1)) n⁸ lg n`, the `O(n⁷ log n)·FO + O(n⁸ log n)` of the
theorem (`lg n = ⌈log₂ n⌉ + 1`): at most `6n³ + 56n² + 29n + 2` arithmetic operations, `2n(2n + 1)`
evaluations of `f` and `2n(n + 1)` minimizations (`waterFillC_spec`, `oracleCalls_fEvals_le`). -/
lemma waterFillC_time (H : Hyp f m β α) (hn : 0 < Fintype.card E) {FO TS C₁ C₂ : ℝ}
    (hFO : 0 ≤ FO) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hTS : TS ≤ sfmTime C₁ C₂ (Fintype.card E) FO) :
    time FO TS (waterFillC f m β α).cost ≤
      (6 + 4 * C₁) * (Fintype.card E : ℝ) ^ 7 * lg (Fintype.card E) * FO +
        (93 + 4 * C₁ * (C₂ + 1)) * (Fintype.card E : ℝ) ^ 8 * lg (Fintype.card E) := by
  obtain ⟨-, h1, h2, h3⟩ := waterFillC_spec H
  obtain ⟨hc, he⟩ := oracleCalls_fEvals_le H
  have key := time_le hFO (sfmTime_nonneg (Fintype.card E) hC₁ hC₂ hFO) hTS h3 (h2 ▸ he)
    (h1 ▸ hc)
  refine key.trans ?_
  have hx : (1 : ℝ) ≤ Fintype.card E := by exact_mod_cast hn
  have hL : (1 : ℝ) ≤ (lg (Fintype.card E) : ℝ) := by exact_mod_cast one_le_lg _
  unfold sfmTime
  push_cast
  set x : ℝ := (Fintype.card E : ℝ)
  set L : ℝ := (lg (Fintype.card E) : ℝ)
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hL0 : (0 : ℝ) ≤ L := by linarith
  have e1 : x ≤ x ^ 7 := by simpa using pow_le_pow_right₀ hx (show 1 ≤ 7 by norm_num)
  have e2 : x ^ 2 ≤ x ^ 7 := pow_le_pow_right₀ hx (by norm_num)
  have e6 : x ^ 6 ≤ x ^ 7 := pow_le_pow_right₀ hx (by norm_num)
  have e7 : x ^ 7 ≤ x ^ 8 := pow_le_pow_right₀ hx (by norm_num)
  have e3 : x ^ 3 ≤ x ^ 8 := pow_le_pow_right₀ hx (by norm_num)
  have e28 : x ^ 2 ≤ x ^ 8 := pow_le_pow_right₀ hx (by norm_num)
  have e18 : x ≤ x ^ 8 := by simpa using pow_le_pow_right₀ hx (show 1 ≤ 8 by norm_num)
  have e08 : 1 ≤ x ^ 8 := one_le_pow₀ hx
  have hx8 : 0 ≤ x ^ 8 := by positivity
  have hx7 : 0 ≤ x ^ 7 := by positivity
  -- (i) the arithmetic operations: `6x³ + 56x² + 29x + 2 ≤ 93x⁸ ≤ 93x⁸L`
  have i1 : 6 * x ^ 3 + 56 * x ^ 2 + 29 * x + 2 ≤ 93 * x ^ 8 * L := by
    have : x ^ 8 ≤ x ^ 8 * L := le_mul_of_one_le_right hx8 hL
    linarith
  -- (ii) the evaluations of `f`: `2x(2x + 1) ≤ 6x⁷ ≤ 6x⁷L`
  have i2 : FO * (2 * x * (2 * x + 1)) ≤ 6 * x ^ 7 * L * FO := by
    have h7 : x ^ 7 ≤ x ^ 7 * L := le_mul_of_one_le_right hx7 hL
    have : 2 * x * (2 * x + 1) ≤ 6 * x ^ 7 * L := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hFO]
  -- (iii) the minimizations: `C₁L(x⁵FO + C₂x⁶ + x⁶)(2x² + 2x) ≤ C₁L(4x⁷FO + 4C₂x⁸ + 4x⁸)`
  have i3 : C₁ * (x ^ 5 * L * (FO + C₂ * x) + x ^ 6 * L) * (2 * x * (x + 1)) ≤
      4 * C₁ * x ^ 7 * L * FO + 4 * C₁ * (C₂ + 1) * x ^ 8 * L := by
    have a1 : x ^ 6 * FO ≤ x ^ 7 * FO := mul_le_mul_of_nonneg_right e6 hFO
    have a2 : C₂ * x ^ 7 ≤ C₂ * x ^ 8 := mul_le_mul_of_nonneg_left e7 hC₂
    have hCL : 0 ≤ C₁ * L := mul_nonneg hC₁ hL0
    have hin : 2 * x ^ 7 * FO + 2 * x ^ 6 * FO + 2 * C₂ * x ^ 8 + 2 * C₂ * x ^ 7 + 2 * x ^ 8 +
        2 * x ^ 7 ≤ 4 * x ^ 7 * FO + 4 * C₂ * x ^ 8 + 4 * x ^ 8 := by linarith
    have := mul_le_mul_of_nonneg_left hin hCL
    calc C₁ * (x ^ 5 * L * (FO + C₂ * x) + x ^ 6 * L) * (2 * x * (x + 1))
        = C₁ * L * (2 * x ^ 7 * FO + 2 * x ^ 6 * FO + 2 * C₂ * x ^ 8 + 2 * C₂ * x ^ 7 +
            2 * x ^ 8 + 2 * x ^ 7) := by ring
      _ ≤ C₁ * L * (4 * x ^ 7 * FO + 4 * C₂ * x ^ 8 + 4 * x ^ 8) := this
      _ = 4 * C₁ * x ^ 7 * L * FO + 4 * C₁ * (C₂ + 1) * x ^ 8 * L := by ring
  nlinarith [i1, i2, i3]

/-- **`thm:waterfilling`** (Theorem 3.2, statement `05-best-response.tex:26-28`, proof
`appB-quadratic.tex:161-182`): the best response `x*(α)` can be computed in time
`𝒪(n⁷ log n)·FO + 𝒪(n⁸ log n)`. The Lean has the running time from what the proof derives it
from, with the time of a minimization cited: water-filling computes the best response, the output
`x̄` of `alg:waterfilling` is `x*(α)`, with at most `2n(n + 1)` submodular minimizations
(`oracleCalls`), `n = |E|`. The `𝒪(n²)` further evaluations of `f` appear as
`fEvals ≤ 2n(2n + 1)`, where `fEvals` sums `rayEvals = |S*| + K + 1` over the steps. The counted
water-filling `waterFillC`, which performs `alg:waterfilling` in the cost model of
`Stoc.Counted`, with the `𝒪(n)` work per step (for the
active set, the admission level, and the updates) and the counted ray computations, returns `x̄`
with exactly `oracleCalls` minimizations and `fEvals` evaluations of `f`, and at most
`6n³ + 56n² + 29n + 2` further arithmetic operations, comparisons included: the `𝒪(n³)` of the
proof (`waterFillC_spec`; not in the paper: the paper counts in prose). The time of a minimization
(step (8)) is cited: the Lean takes the bound of Iwata and Orlin as a hypothesis and proves the
running time from the counts (`waterFillC_time`, below).

The paper's steps. "We first show that water-filling ends at the best response": (1)
`C_θ := {e : λ̄_e ≥ θ}` is the set saturated after the last step with `λ − Δ ≥ θ`, or empty, as
elements saturated earlier have larger blocking levels (the water level, including the level
`λ − Δ` at the end of each step, never increases by `lem:wfstructure`; `levelEnd_antitone`);
(2) by `lem:wfstructure` it is a cumulative saturated set, tight at `x̄` as its coordinates no
longer change (`x_eq_of_mem_Y`); (3) `eq:A-terminal` gives `A_θ(x̄) ⊆ C_θ` and `x̄_e = 0` on
`C_θ \ A_θ(x̄)`; (4) the chain `x̄(A_θ) = x̄(C_θ) = f(C_θ) ≥ f(A_θ) ≥ x̄(A_θ)` (steps (1)-(4):
`waterFill_levelSet_tight`); (5) `ρ(x̄) ≥ 0` by `eq:A-terminal`, and `prop:optchar` (`optchar`).
"It remains to count the operations": (6) at most `2|Ê| ≤ 2n` steps (`lem:wfstructure`), each with
one ray computation, which returns the step's `d(x, S*)` and `T(x + d(x, S*) v^{S*})`
(`alg_step`), with at most `|S*| + 1` minimizations and `2|S*| + 1` evaluations (`lem:ray`); (7) by
`lem:ray`, as `|S*| ≤ n`, at most `n + 1` minimizations and `2n + 1` evaluations per step, so at
most `2n(n + 1)` and `2n(2n + 1)` in all; (8) a minimization returns the unique maximal minimizer
(`sfmArg`, `sfmArg_min`), which the algorithm of Iwata and Orlin [IO09] finds in time
`𝒪(n⁵ log n)·EO + 𝒪(n⁶ log n)` with `EO = FO + 𝒪(n)`, and multiplying by the `𝒪(n²)`
minimizations gives the stated bound: for `n ≥ 1`, if an evaluation of `f` takes time `FO ≥ 0` and a
minimization time at most `sfmTime C₁ C₂ n FO = C₁(n⁵ lg n (FO + C₂ n) + n⁶ lg n)`, the bound of
Iwata and Orlin (cited, a hypothesis), then `waterFillC` takes time at most
`(6 + 4C₁) n⁷ lg n · FO + (93 + 4C₁(C₂ + 1)) n⁸ lg n`, `lg n = ⌈log₂ n⌉ + 1` (`waterFillC_time`;
not in the paper: the paper counts in prose). -/
theorem waterfilling (H : Hyp f m β α) :
    waterFill f m β α = bestResponse f m β α ∧
      oracleCalls f m β α ≤ 2 * Fintype.card E * (Fintype.card E + 1) ∧
      fEvals f m β α ≤ 2 * Fintype.card E * (2 * Fintype.card E + 1) ∧
      ((waterFillC f m β α).val = waterFill f m β α ∧
        (waterFillC f m β α).cost.2.1 = oracleCalls f m β α ∧
        (waterFillC f m β α).cost.2.2 = fEvals f m β α ∧
        (waterFillC f m β α).cost.1 ≤
          6 * Fintype.card E ^ 3 + 56 * Fintype.card E ^ 2 + 29 * Fintype.card E + 2) ∧
      (0 < Fintype.card E → ∀ FO TS C₁ C₂ : ℝ, 0 ≤ FO → 0 ≤ C₁ → 0 ≤ C₂ →
        TS ≤ Counted.sfmTime C₁ C₂ (Fintype.card E) FO →
        Counted.time FO TS (waterFillC f m β α).cost ≤
          (6 + 4 * C₁) * (Fintype.card E : ℝ) ^ 7 * Counted.lg (Fintype.card E) * FO +
            (93 + 4 * C₁ * (C₂ + 1)) * (Fintype.card E : ℝ) ^ 8 *
              Counted.lg (Fintype.card E)) := by
  obtain ⟨hmem, -, -, -, -, -, ⟨hiters, hpos, -⟩, hterm⟩ := wfstructure H
  refine ⟨?_, ?_⟩
  · -- "We first show that water-filling ends at the best response." (1)-(4)
    -- (`waterFill_levelSet_tight`).
    -- (5) "Thus every positive marginal level set is tight,
    have htight : ∀ θ > 0, IsTight f (waterFill f m β α) (levelSet m β α (waterFill f m β α) θ) :=
      fun θ hθ => waterFill_levelSet_tight H hθ
    -- `ρ(x̄) ≥ 0` by (`eq:A-terminal`),
    have hρ : ∀ e, 0 ≤ marg m β α (waterFill f m β α) e := fun e => by
      rw [(hterm e).1]
      exact (hterm e).2
    -- and `prop:optchar` shows that `x̄` is the unique best response `x*(α)`."
    have hbr : IsBestResponse (indepPoly f) m β α (waterFill f m β α) :=
      (optchar (x := waterFill f m β α) H.rank H.beta H.reward H.share (hmem _)).1.2 ⟨hρ, htight⟩
    exact hbr.eq_bestResponse H.beta H.rank
  -- (6) "It remains to count the operations. There are at most `2|Ê| ≤ 2n` steps by
  -- `lem:wfstructure`.
  have hsteps : iters f m β α ≤ 2 * Fintype.card E := by
    have := card_le_univ (hatE m α)
    omega
  -- Each uses one ray computation and `O(n)` additional work to determine the active set, the
  -- admission level, and the updates": step `k` is the update (`eq:A-step`), and the ray
  -- computation of `lem:ray` at `(x, S*)` returns its `d(x, S*)` and `T(x + d(x, S*) v^{S*})`
  -- (`alg_step`, lines 3-4 of `alg:waterfilling`), next to its count from `lem:ray`: at most
  -- `|S*| + 1` minimizations and `2|S*| + 1` evaluations. `oracleCalls` and `fEvals` add up these
  -- counts, one ray computation per step; the additional work is counted in `waterFillC` (below).
  have hray : ∀ k ∈ range (iters f m β α),
      (rayStep f m β α (run f m β α k).x (active m β α (run f m β α k)) =
          dmax f β (run f m β α k).x (active m β α (run f m β α k)) ∧
        rayArg f m β α (run f m β α k).x (active m β α (run f m β α k)) =
          maxTight f m α ((run f m β α k).x + dmax f β (run f m β α k).x
            (active m β α (run f m β α k)) • vS β (active m β α (run f m β α k))) ∧
        run f m β α (k + 1) = step f m β α (run f m β α k)) ∧
      rayCalls f m β α (run f m β α k).x (active m β α (run f m β α k)) ≤
          (active m β α (run f m β α k)).card + 1 ∧
        rayEvals f m β α (run f m β α k).x (active m β α (run f m β α k)) ≤
          2 * (active m β α (run f m β α k)).card + 1 := by
    intro k hk
    obtain ⟨-, -, -, -, hcalls, hevals, -⟩ := ray H (hmem k) (fun e he => run_x_eq_zero he k)
      (active_nonempty (hpos k (mem_range.1 hk))) ((active_subset _).trans sdiff_subset)
    exact ⟨alg_step H (mem_range.1 hk), hcalls, hevals⟩
  -- (7) "By `lem:ray`, this gives at most `2n(n + 1)` submodular minimizations, `𝒪(n²)` further
  -- evaluations of `f`, and `𝒪(n³)` further arithmetic operations": as `|S*| ≤ n`, at most
  -- `n + 1` minimizations and `2n + 1` evaluations in each step, and at most `2n` steps.
  have hcount : ∀ k ∈ range (iters f m β α),
      rayCalls f m β α (run f m β α k).x (active m β α (run f m β α k)) ≤ Fintype.card E + 1 ∧
        rayEvals f m β α (run f m β α k).x (active m β α (run f m β α k)) ≤
          2 * Fintype.card E + 1 := by
    intro k hk
    have := (hray k hk).2
    have := card_le_univ (active m β α (run f m β α k))
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc oracleCalls f m β α ≤ ∑ _k ∈ range (iters f m β α), (Fintype.card E + 1) :=
          sum_le_sum fun k hk => (hcount k hk).1
      _ = iters f m β α * (Fintype.card E + 1) := by rw [sum_const, card_range, smul_eq_mul]
      _ ≤ 2 * Fintype.card E * (Fintype.card E + 1) := Nat.mul_le_mul_right _ hsteps
  · calc fEvals f m β α ≤ ∑ _k ∈ range (iters f m β α), (2 * Fintype.card E + 1) :=
          sum_le_sum fun k hk => (hcount k hk).2
      _ = iters f m β α * (2 * Fintype.card E + 1) := by rw [sum_const, card_range, smul_eq_mul]
      _ ≤ 2 * Fintype.card E * (2 * Fintype.card E + 1) := Nat.mul_le_mul_right _ hsteps
  · -- the `𝒪(n³)` further arithmetic operations: the counted water-filling `waterFillC` returns
    -- `x̄` with these minimizations and evaluations, and the `𝒪(n²)` operations of `lem:ray` and
    -- the `𝒪(n)` additional work in each of the at most `2n` steps make at most
    -- `6n³ + 56n² + 29n + 2` (`waterFillC_spec`)
    exact waterFillC_spec H
  · -- (8) "Throughout our operation counts, a submodular minimization returns the unique maximal
    -- minimizer" (`sfmArg`, `sfmArg_min`). "The strongly polynomial algorithm of Iwata and Orlin
    -- [IO09] finds it in time `𝒪(n⁵ log n)·EO + 𝒪(n⁶ log n)`, where `EO` is the cost of evaluating
    -- the function being minimized. Here each such function is `f` minus a modular function, so
    -- `EO = FO + 𝒪(n)`. Multiplying by the `𝒪(n²)` minimizations gives the stated bound."
    -- (`waterFillC_time`, with the time of a minimization by [IO09] as a hypothesis, cited)
    exact fun hn _ _ _ _ hFO hC₁ hC₂ hTS => waterFillC_time H hn hFO hC₁ hC₂ hTS

end Loop

end WaterFilling

end Stoc
