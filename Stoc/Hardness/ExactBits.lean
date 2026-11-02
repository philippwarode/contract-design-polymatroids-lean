-- stamp r6 2026-11-02
import Stoc.Hardness.Encoding
import Stoc.Hardness.ExactResponse

/-!
# Exact best responses in the bit model: `lem:exactbr`

The bit model of the STOC version's `lem:exactbr` (Appendix C.8, `sec:D-npcomplete`, "Exact best
responses and NP-completeness", `stoc-sections/appD-hardness.tex:1799-1807`, proof lines 1809-1881),
for an instance `I` of `𝒞_cut` given by its rational data (`RatInst`, `Stoc/Hardness/Encoding.lean`)
and a rational share `α ≥ 0`. `Stoc/Hardness/ExactResponse.lean` proves the mathematics of the three
parts (`exactbr_a`, `exactbr_b`, `exactbr_c`); this file adds the encoding lengths, the test of (b)
and the search of (c):

* (a) `exactbr_a_enc`: "The best response `x*(α)` is a rational vector, and each of its coordinates
  has encoding length at most `6⟨α⟩ + 31⟨I⟩`", by `eq:D-explicit` and the rules at the start of the
  proof; `enc_varrho_le`: `⟨ϱ_i⟩ ≤ Ω := 2⟨α⟩ + 14⟨I⟩`.
* The maximum flows. The paper cites them: "After multiplication by the product of their
  denominators, the capacities are integers of polynomial encoding length, and the algorithm of
  Edmonds and Karp computes a maximum flow in polynomial time [Sch03, Thm. 10.5]. This gives the
  minimum of `cut_D + y` and its largest minimizer" (with the criterion for minimum cuts by
  residual networks of [GGT89, §2.1–2.2]). The minimum `RatInst.minCut` and the largest minimizer
  `RatInst.largestMin` are defined as such, the procedures below count how often they use them (one
  maximum flow each), and `exists_common_den` is the first sentence: the capacities, multiplied by
  the product of their denominators, are integers of encoding length at most the sum of the
  encoding lengths of the capacities.
* (b) `RatInst.TestB` and `exactbr_b_enc`: "Given a rational vector `x ∈ ℚ^E`, one can decide in
  polynomial time whether `x = x*(α)`": the test of `2|E|` comparisons, `|E|` evaluations of `f`
  and one maximum flow in `G_{ω−x}` holds if and only if `x = x*(α)`, with the encoding lengths of
  the numbers it uses.
* (c) `bsearch`, `searchRound`, `chainSearch`, `RatInst.xOfChain` and `exactbr_c_enc`: "The best
  response `x*(α)` can be computed in polynomial time": the search finds `A_1, …, A_k` with at most
  `(|E| + 1)(3Ω + 1)` maximum flows, every `θ = jh` it uses has encoding length at most `5Ω + 3`,
  so all capacities of these flows have polynomial encoding length, and `eq:D-explicit` gives
  `x*(α)` from the chain; `varrho_bounds`: `ϱ_k > 2^{−Ω}`, `ϱ_1 < 2^Ω` and
  `ϱ_i − ϱ_{i+1} > 2^{−2Ω}`; `searchRound_spec`: one round of the search, the proof's steps with
  the step `h = 2^{−2Ω}` and the shares `jh`, `j ∈ {1, …, 2^{3Ω}}`.
* `exactbr`: the statement of `lem:exactbr` in the bit model, the conjunction of (a)–(c)
  (`exactbr_a_enc`, `exactbr_b_enc`, `exactbr_c_enc`) for one instance and one share.

Not formalised: the running time of Edmonds and Karp's algorithm and the criterion of [GGT89]
(both cited), and the arithmetic operations of (b) and (c), which the paper bounds as
"polynomially many further operations on numbers whose encoding lengths are bounded as in the proof
of (a)"; this library does not count arithmetic operations.
-/

namespace Stoc

namespace Hardness

open Finset

noncomputable section

/-! ### The cited maximum flows -/

/-- The first sentence on the maximum flows in the proof of `lem:exactbr`(b) (`stoc-sections/
appD-hardness.tex:1852`): "After multiplication by the product of their denominators, the
capacities are integers of polynomial encoding length". For rationals `q_i`, `i ∈ s`, the product
`P` of their denominators is at most `2^{∑⟨q_i⟩}`, and every `P q_i` is an integer of absolute
value less than `2^{∑⟨q_i⟩}`. -/
theorem exists_common_den {ι : Type*} [DecidableEq ι] (s : Finset ι) (q : ι → ℚ) :
    ∃ P : ℕ, 0 < P ∧ P ≤ 2 ^ (∑ i ∈ s, enc (q i)) ∧
      ∀ i ∈ s, ∃ z : ℤ, (P : ℚ) * q i = z ∧ z.natAbs < 2 ^ (∑ i ∈ s, enc (q i)) := by
  have hden : ∀ t : Finset ι, ∏ j ∈ t, (q j).den ≤ 2 ^ (∑ j ∈ t, enc (q j)) := fun t => by
    rw [← prod_pow_eq_pow_sum]
    exact prod_le_prod fun j _ => (den_lt (q j)).le
  refine ⟨∏ i ∈ s, (q i).den, prod_pos fun i _ => (q i).den_pos, hden s, fun i hi => ?_⟩
  refine ⟨(q i).num * ∏ j ∈ s.erase i, ((q j).den : ℤ), ?_, ?_⟩
  · rw [← mul_prod_erase s (fun j => (q j).den) hi]
    push_cast
    linear_combination (∏ j ∈ s.erase i, ((q j).den : ℚ)) * Rat.mul_den_eq_num (q i)
  · rw [Int.natAbs_mul, ← Nat.cast_prod, Int.natAbs_natCast]
    rw [← add_sum_erase s (fun j => enc (q j)) hi, pow_add]
    calc (q i).num.natAbs * ∏ j ∈ s.erase i, (q j).den
        < 2 ^ enc (q i) * ∏ j ∈ s.erase i, (q j).den :=
          Nat.mul_lt_mul_of_pos_right (natAbs_num_lt (q i))
            (prod_pos fun j _ => (q j).den_pos)
      _ ≤ 2 ^ enc (q i) * 2 ^ ∑ j ∈ s.erase i, enc (q j) :=
          Nat.mul_le_mul_left _ (hden (s.erase i))

namespace RatInst

variable {E : Type*} [Fintype E] [DecidableEq E] (I : RatInst E)

/-- `cut_D(S)` in `ℚ`. -/
def cutQ (S : Finset E) : ℚ := ∑ a ∈ I.D with a.1 ∈ S ∧ a.2 ∉ S, I.cap a

/-- The value `cut_D(S) + y(S)` of the function `cut_D + y` (`lem:exactbr`(b)). -/
def cutVal (y : E → ℚ) (S : Finset E) : ℚ := I.cutQ S + ∑ e ∈ S, y e

/-- The minimum of `cut_D + y` over the subsets of `E`, which one maximum flow in `G_y` gives
(`lem:exactbr`(b): "This gives the minimum of `cut_D + y` …", cited). -/
def minCut (y : E → ℚ) : ℚ :=
  (univ : Finset (Finset E)).inf' ⟨∅, mem_univ _⟩ (I.cutVal y)

/-- The largest minimizer of `cut_D + y`, the union of all minimizers, which the same maximum flow
gives (`lem:exactbr`(b): "… and its largest minimizer.", by the criterion of [GGT89], cited). -/
def largestMin (y : E → ℚ) : Finset E :=
  ((univ : Finset (Finset E)).filter fun S => I.cutVal y S = I.minCut y).sup id

lemma minCut_le (y : E → ℚ) (S : Finset E) : I.minCut y ≤ I.cutVal y S :=
  inf'_le _ (mem_univ S)

/-- A minimizer of `cut_D + y` that contains every minimizer is the largest minimizer (not in the
paper). -/
lemma largestMin_eq {y : E → ℚ} {L : Finset E} (hmin : ∀ S, I.cutVal y L ≤ I.cutVal y S)
    (hmax : ∀ S, I.cutVal y S ≤ I.cutVal y L → S ⊆ L) : I.largestMin y = L := by
  have hL : I.cutVal y L = I.minCut y :=
    le_antisymm (le_inf' _ _ fun S _ => hmin S) (I.minCut_le y L)
  apply le_antisymm
  · refine Finset.sup_le fun S hS => hmax S ?_
    rw [(mem_filter.1 hS).2, hL]
  · exact le_sup (f := id) (mem_filter.2 ⟨mem_univ _, hL⟩)

omit [Fintype E] in
lemma cutQ_cast (h : I.IsCutForm) (S : Finset E) : (I.cutQ S : ℝ) = (I.form h).cut S := by
  show ((∑ a ∈ I.D with a.1 ∈ S ∧ a.2 ∉ S, I.cap a : ℚ) : ℝ) =
    ∑ a ∈ I.D with a.1 ∈ S ∧ a.2 ∉ S, (I.cap a : ℝ)
  push_cast
  rfl

end RatInst

/-! ### (a): the encoding length of `x*(α)` -/

section PartA

variable {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E] (I : RatInst E)

/-- The proof of `lem:exactbr`(a) (`stoc-sections/appD-hardness.tex:1835-1838`): "The numerator of
`ϱ_i` is a sum of three terms of encoding lengths at most `⟨α⟩ + 2⟨I⟩`, `2⟨I⟩` and `2⟨I⟩`. So, by
the rules above, `⟨ϱ_i⟩ ≤ 2(⟨α⟩ + 6⟨I⟩) + 2⟨I⟩ = Ω` for `Ω := 2⟨α⟩ + 14⟨I⟩`" (indices from `0`:
`theta ρ 0 i` is `ϱ_{i+1}`). -/
theorem enc_varrho_le (hI : I.InCcut) {α : ℚ} (hα : 0 ≤ α) {i : ℕ}
    (hi : i < numVals (marg I.mR I.βR α (bestResponse I.f I.mR I.βR α)) 0) :
    ∃ ϱ : ℚ, (ϱ : ℝ) = theta (marg I.mR I.βR α (bestResponse I.f I.mR I.βR α)) 0 i ∧
      enc ϱ ≤ 2 * enc α + 14 * I.encI := by
  set x := bestResponse I.f I.mR I.βR (α : ℝ) with hxdef
  have hα' : (0 : ℝ) ≤ α := by exact_mod_cast hα
  obtain ⟨h5a, -, -, -⟩ := exactbr_a hI.2 hα' hxdef
  set Di := blockD I.mR I.βR α x i
  set A1 := chainA I.mR I.βR α x (i + 1)
  set A0 := chainA I.mR I.βR α x i
  refine ⟨(α * I.tQ Di - I.fQ A1 + I.fQ A0) / I.binvQ Di, ?_, ?_⟩
  · rw [h5a i hi]
    push_cast
    rw [I.tQ_cast, I.fQ_cast, I.fQ_cast, I.binvQ_cast]
  · -- `⟨ϱ_i⟩ ≤ ⟨numerator⟩ + ⟨β⁻¹(D_i)⟩` and the rule for a sum of three terms
    have e1 := enc_div (α * I.tQ Di - I.fQ A1 + I.fQ A0) (I.binvQ Di)
    have e2 := enc_add₃ (α * I.tQ Di) (-I.fQ A1) (I.fQ A0)
    rw [← sub_eq_add_neg, enc_neg] at e2
    have e3 := enc_mul α (I.tQ Di)
    have e4 := I.enc_tQ_le Di
    have e5 := I.enc_fQ_le A1
    have e6 := I.enc_fQ_le A0
    have e7 := I.enc_binvQ_le Di
    omega

/-- **`lem:exactbr`(a)** (Lemma C.25) in the bit model (`stoc-sections/appD-hardness.tex:1802`,
proof lines 1814-1841): for an instance `I` of `𝒞_cut` and a rational share `α ≥ 0`, "the best
response `x*(α)` is a rational vector, and each of its coordinates has encoding length at most
`6⟨α⟩ + 31⟨I⟩`".

The proof's steps (after `eq:D-explicit`, `exactbr_a`): (1) "In particular, `x` is rational"; (2)
`⟨ϱ_i⟩ ≤ Ω` (`enc_varrho_le`); (3) "`⟨x_e⟩ ≤ 2(⟨α⟩ + ⟨I⟩ + Ω) + ⟨I⟩ = 6⟨α⟩ + 31⟨I⟩` for
`e ∈ A_k`"; (4) "For `e ∈ E ∖ A_k`, we have `⟨x_e⟩ ≤ ⟨α⟩ + ⟨t_e⟩ ≤ ⟨α⟩ + ⟨I⟩`". -/
theorem exactbr_a_enc (hI : I.InCcut) {α : ℚ} (hα : 0 ≤ α) :
    ∃ x : E → ℚ, (∀ e, (x e : ℝ) = bestResponse I.f I.mR I.βR α e) ∧
      ∀ e, enc (x e) ≤ 6 * enc α + 31 * I.encI := by
  set xs := bestResponse I.f I.mR I.βR (α : ℝ) with hxdef
  have hα' : (0 : ℝ) ≤ α := by exact_mod_cast hα
  obtain ⟨-, h5b, h5c, -⟩ := exactbr_a hI.2 hα' hxdef
  have key : ∀ e, ∃ q : ℚ, (q : ℝ) = xs e ∧ enc q ≤ 6 * enc α + 31 * I.encI := by
    intro e
    by_cases he : e ∈ chainA I.mR I.βR α xs (numVals (marg I.mR I.βR α xs) 0)
    · -- (3) "… and `⟨x_e⟩ ≤ 2(⟨α⟩ + ⟨I⟩ + Ω) + ⟨I⟩ = 6⟨α⟩ + 31⟨I⟩` for `e ∈ A_k`." (`e ∈ D_j`
      -- for some `j`, and `x_e = (αm_e − ϱ_j)/β_e`)
      obtain ⟨j, hj, heD⟩ := exists_mem_blockD he
      obtain ⟨ϱ, hϱ, hϱe⟩ := enc_varrho_le I hI hα hj
      refine ⟨(α * I.m e - ϱ) / I.β e, ?_, ?_⟩
      · rw [h5b j hj e heD, ← hϱ]
        push_cast
        rfl
      · have e1 := enc_div (α * I.m e - ϱ) (I.β e)
        have e2 := enc_sub (α * I.m e) ϱ
        have e3 := enc_mul α (I.m e)
        have e4 := I.enc_m_le e
        have e5 := I.enc_β_le e
        omega
    · -- (4) "For `e ∈ E ∖ A_k`, we have `⟨x_e⟩ ≤ ⟨α⟩ + ⟨t_e⟩ ≤ ⟨α⟩ + ⟨I⟩`." (`x_e = αt_e`)
      refine ⟨α * (I.m e / I.β e), ?_, ?_⟩
      · rw [h5c e he]
        push_cast
        rfl
      · have e1 := enc_mul α (I.m e / I.β e)
        have e2 := I.enc_t_le e
        omega
  choose q hq hqe using key
  exact ⟨q, hq, hqe⟩

end PartA

/-! ### (b): the test -/

section PartB

variable {E : Type*} [Fintype E] [DecidableEq E] (I : RatInst E)

namespace RatInst

/-- The marginal `ρ_e(x) = αm_e − β_e x_e` in `ℚ` (`eq:marg`). -/
def margQ (α : ℚ) (x : E → ℚ) (e : E) : ℚ := α * I.m e - I.β e * x e

/-- The level set `A_θ(x) = {e : ρ_e(x) ≥ θ}` in `ℚ`. -/
def levelQ (α : ℚ) (x : E → ℚ) (θ : ℚ) : Finset E := univ.filter fun e => θ ≤ I.margQ α x e

/-- The test of `lem:exactbr`(b) for `x ∈ ℚ^E` (`stoc-sections/appD-hardness.tex:1856-1860`): the
signs `x ≥ 0` and `ρ(x) ≥ 0` (`2|E|` comparisons), the tightness of the at most `|E|` sets
`A_θ(x)` for the positive values `θ = ρ_e(x)` of `ρ(x)` (`|E|` evaluations of `f`), and that
`cut_D + (ω − x)` has minimum `0` (one maximum flow in `G_{ω−x}`). -/
def TestB (α : ℚ) (x : E → ℚ) : Prop :=
  (∀ e, 0 ≤ x e) ∧ (∀ e, 0 ≤ I.margQ α x e) ∧
    (∀ e, 0 < I.margQ α x e →
      ∑ e' ∈ I.levelQ α x (I.margQ α x e), x e' = I.fQ (I.levelQ α x (I.margQ α x e))) ∧
    I.minCut (fun e => I.ω e - x e) = 0

instance (α : ℚ) (x : E → ℚ) : Decidable (I.TestB α x) := by
  unfold TestB
  infer_instance

end RatInst

/-- **`lem:exactbr`(b)** in the bit model (`stoc-sections/appD-hardness.tex:1803`, proof lines
1843-1860): "Given a rational vector `x ∈ ℚ^E`, one can decide in polynomial time whether
`x = x*(α)`". The test `RatInst.TestB` (`2|E|` comparisons, `|E|` evaluations of `f` and one
maximum flow) holds if and only if `x = x*(α)`; every value of `f` it uses has encoding length at
most `2⟨I⟩`, and the capacities `ω_e − x_e` of `G_{ω−x}` at most `2(⟨I⟩ + ⟨x_e⟩)`, besides the
capacities of `D`.

The proof's steps: (1) "By `prop:optchar`, `x = x*(α)` if and only if `x ≥ 0`, `ρ(x) ≥ 0`,
`x(S) ≤ f(S)` for every `S ⊆ E`, and the at most `|E|` sets `A_θ(x)`, for the positive values `θ`
of `ρ(x)`, are tight for `x`" (`exactbr_b`); (2) "The sign conditions take `2|E|` comparisons, and
the tightness takes `|E|` evaluations of `f`, each a sum of input numbers"; (3) "The third
condition says that `cut_D + (ω − x)`, which vanishes at `∅`, has minimum `0`, and one maximum flow
in `G_{ω−x}` decides it". -/
theorem exactbr_b_enc [Nonempty E] (hI : I.InCcut) {α : ℚ} (hα : 0 ≤ α) (x : E → ℚ) :
    (I.TestB α x ↔ (fun e => (x e : ℝ)) = bestResponse I.f I.mR I.βR α) ∧
    (∀ S, enc (I.fQ S) ≤ 2 * I.encI) ∧ (∀ e, enc (I.ω e - x e) ≤ 2 * (I.encI + enc (x e))) := by
  refine ⟨?_, fun S => I.enc_fQ_le S,
    fun e => (enc_sub _ _).trans (by have := I.enc_ω_le e; omega)⟩
  set xr : E → ℝ := fun e => x e with hxr
  have hα' : (0 : ℝ) ≤ α := by exact_mod_cast hα
  -- (1) "By `prop:optchar`, `x = x*(α)` if and only if `x ≥ 0`, `ρ(x) ≥ 0`, `x(S) ≤ f(S)` for
  -- every `S ⊆ E`, and the at most `|E|` sets `A_θ(x)`, for the positive values `θ` of `ρ(x)`,
  -- are tight for `x`." (`exactbr_b`)
  obtain ⟨h1, -⟩ := exactbr_b hI.2 hα' (F := I.form hI.1) (fun S => rfl) xr
  rw [h1]
  have hmarg : ∀ e, (I.margQ α x e : ℝ) = marg I.mR I.βR α xr e := fun e => by
    simp [RatInst.margQ, marg, RatInst.mR, RatInst.βR, xr]
  have hlevel : ∀ θ : ℚ, I.levelQ α x θ = levelSet I.mR I.βR α xr θ := fun θ => by
    ext e
    simp only [RatInst.levelQ, levelSet, mem_filter, mem_univ, true_and, ← hmarg]
    exact_mod_cast Iff.rfl
  have hsum : ∀ S : Finset E, ((∑ e ∈ S, x e : ℚ) : ℝ) = ∑ e ∈ S, xr e := fun S => by
    push_cast
    rfl
  -- (3) "The third condition says that `cut_D + (ω − x)`, which vanishes at `∅`, has minimum
  -- `0`, and one maximum flow in `G_{ω−x}` decides it." (`minCut`, the cited maximum flow; the
  -- Lean takes (3) before (2))
  have hcv : ∀ S, ((I.cutVal (fun e => I.ω e - x e) S : ℚ) : ℝ) = I.f S - ∑ e ∈ S, xr e :=
    fun S => by
      rw [← I.fQ_cast]
      simp only [RatInst.cutVal, RatInst.fQ, RatInst.cutQ, sum_sub_distrib]
      push_cast
      ring
  have hmin : I.minCut (fun e => I.ω e - x e) = 0 ↔ ∀ S, ∑ e ∈ S, xr e ≤ I.f S := by
    constructor
    · intro h S
      have h0 := I.minCut_le (fun e => I.ω e - x e) S
      rw [h] at h0
      have h0' : (0 : ℝ) ≤ (I.cutVal (fun e => I.ω e - x e) S : ℝ) := by exact_mod_cast h0
      linarith [hcv S]
    · intro h
      apply le_antisymm
      · have h0 := I.minCut_le (fun e => I.ω e - x e) ∅
        simpa [RatInst.cutVal, RatInst.cutQ] using h0
      · refine le_inf' _ _ fun S _ => ?_
        have h2 : (0 : ℝ) ≤ (I.cutVal (fun e => I.ω e - x e) S : ℝ) := by
          linarith [hcv S, h S]
        exact_mod_cast h2
  -- (2) "The sign conditions take `2|E|` comparisons, and the tightness takes `|E|` evaluations
  -- of `f`, each a sum of input numbers." (`TestB`: the tightness of the sets `A_θ(x)` at the
  -- positive values `θ` of `ρ(x)`, at most one per element)
  have htight : (∀ e, 0 < I.margQ α x e →
      ∑ e' ∈ I.levelQ α x (I.margQ α x e), x e' = I.fQ (I.levelQ α x (I.margQ α x e))) ↔
      ∀ i < numVals (marg I.mR I.βR α xr) 0,
        IsTight I.f xr (levelSet I.mR I.βR α xr (theta (marg I.mR I.βR α xr) 0 i)) := by
    constructor
    · intro h i hi
      obtain ⟨hval, hpos⟩ := mem_filter.1 (theta_mem hi)
      obtain ⟨e, -, he⟩ := mem_image.1 hval
      have hq : 0 < I.margQ α x e := by
        have : (0 : ℝ) < I.margQ α x e := by rw [hmarg]; rwa [he]
        exact_mod_cast this
      have := h e hq
      unfold IsTight
      rw [← he, ← hmarg, ← hlevel, ← hsum, ← I.fQ_cast, this]
    · intro h e he
      have he' : (0 : ℝ) < marg I.mR I.βR α xr e := by rw [← hmarg]; exact_mod_cast he
      obtain ⟨j, hj, hθj⟩ := exists_theta_eq he'
      have := h j hj
      unfold IsTight at this
      rw [hθj, ← hmarg, ← hlevel, ← hsum, ← I.fQ_cast] at this
      exact_mod_cast this
  constructor
  · rintro ⟨hx, hρ, ht, hm⟩
    refine ⟨fun e => (show (0 : ℝ) ≤ (x e : ℝ) by exact_mod_cast hx e), fun e => ?_,
      hmin.1 hm, htight.1 ht⟩
    rw [← hmarg]
    exact_mod_cast hρ e
  · rintro ⟨hx, hρ, hf, ht⟩
    refine ⟨fun e => by exact_mod_cast (show (0 : ℝ) ≤ (x e : ℝ) from hx e), fun e => ?_,
      htight.2 ht, hmin.2 hf⟩
    have := hρ e
    rw [← hmarg] at this
    exact_mod_cast this

end PartB

/-! ### (c): the search -/

section Search

/-- The binary search of `lem:exactbr`(c) (`stoc-sections/appD-hardness.tex:1876-1877`): from `lo`,
with the known value `v = q lo`, `m` halvings of `[lo, lo + 2^m)`. It returns the largest `j` found,
the value `q j`, and the list of the `j` it queried (one query each). -/
def bsearch {β : Type*} (q : ℕ → β) (P : β → Prop) [DecidablePred P] :
    ℕ → β → ℕ → ℕ × β × List ℕ
  | lo, v, 0 => (lo, v, [])
  | lo, v, m + 1 =>
    if P (q (lo + 2 ^ m)) then
      let r := bsearch q P (lo + 2 ^ m) (q (lo + 2 ^ m)) m
      (r.1, r.2.1, (lo + 2 ^ m) :: r.2.2)
    else
      let r := bsearch q P lo v m
      (r.1, r.2.1, (lo + 2 ^ m) :: r.2.2)

/-- The binary search finds the largest `j` with `P (q j)`, for `P (q j) ↔ j ≤ J` on
`lo ≤ j < lo + 2^m`, with `lo ≤ J < lo + 2^m`, after `m` queries in `(lo, lo + 2^m)` (not in the
paper: "a binary search over `j` … finds the largest such `j`"). -/
theorem bsearch_spec {β : Type*} (q : ℕ → β) (P : β → Prop) [DecidablePred P] {J : ℕ} :
    ∀ (m lo : ℕ) (v : β), (∀ j, lo ≤ j → j < lo + 2 ^ m → (P (q j) ↔ j ≤ J)) → v = q lo →
      lo ≤ J → J < lo + 2 ^ m →
      (bsearch q P lo v m).1 = J ∧ (bsearch q P lo v m).2.1 = q J ∧
      (bsearch q P lo v m).2.2.length = m ∧
      ∀ j ∈ (bsearch q P lo v m).2.2, lo < j ∧ j < lo + 2 ^ m := by
  intro m
  induction m with
  | zero =>
    intro lo v _ hv hlo hJ
    obtain rfl : J = lo := by rw [pow_zero] at hJ; omega
    simp [bsearch, hv]
  | succ m ih =>
    intro lo v hP hv hlo hJ
    have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
    have hpos : 0 < 2 ^ m := by positivity
    by_cases hc : P (q (lo + 2 ^ m))
    · have hJ' : lo + 2 ^ m ≤ J := (hP _ (by omega) (by omega)).1 hc
      obtain ⟨r1, r2, r3, r4⟩ := ih (lo + 2 ^ m) (q (lo + 2 ^ m))
        (fun j hj hj' => hP j (by omega) (by omega)) rfl hJ' (by omega)
      simp only [bsearch, hc, ↓reduceIte, List.length_cons, List.mem_cons]
      refine ⟨r1, r2, by rw [r3], fun j hj => ?_⟩
      rcases hj with rfl | hj
      · omega
      · have := r4 j hj
        omega
    · have hJ' : J < lo + 2 ^ m := by
        by_contra h
        exact hc ((hP _ (by omega) (by omega)).2 (by omega))
      obtain ⟨r1, r2, r3, r4⟩ := ih lo v (fun j hj hj' => hP j hj (by omega)) hv hlo hJ'
      simp only [bsearch, hc, ↓reduceIte, List.length_cons, List.mem_cons]
      refine ⟨r1, r2, by rw [r3], fun j hj => ?_⟩
      rcases hj with rfl | hj
      · omega
      · have := r4 j hj
        omega

variable {E : Type*} [DecidableEq E]

/-- One round of the search of `lem:exactbr`(c) (`stoc-sections/appD-hardness.tex:1873-1878`), from
the known set `A = A_i`, where `q j` is `A_{jh}(α)` (one maximum flow): "if `A_h(α) = A_i`, then
`i = k` and we stop. Otherwise `i < k`", and the binary search over `j ∈ {1, …, 2^{3Ω}}` for the
largest `j` with `A_{jh}(α) ⊋ A_i` gives `A_{i+1} = A_{jh}(α)`. It returns the new set (`none` to
stop) and the list of the `j` it queried. -/
def searchRound (q : ℕ → Finset E) (Ω : ℕ) (A : Finset E) : Option (Finset E) × List ℕ :=
  if q 1 = A then (none, [1])
  else
    let r := bsearch q (A ⊂ ·) 1 (q 1) (3 * Ω)
    (some r.2.1, 1 :: r.2.2)

/-- The search of `lem:exactbr`(c): "We compute `A_1, …, A_k` in turn", at most `n` rounds from
`A`. It returns the sets found and all the queries. -/
def chainSearch (q : ℕ → Finset E) (Ω : ℕ) : ℕ → Finset E → List (Finset E) × List ℕ
  | 0, _ => ([], [])
  | n + 1, A =>
    match searchRound q Ω A with
    | (none, qs) => ([], qs)
    | (some A', qs) =>
      let r := chainSearch q Ω n A'
      (A' :: r.1, qs ++ r.2)

end Search

/-- A positive rational of encoding length at most `Ω` lies in `(2^{−Ω}, 2^Ω)` (the proof of
`lem:exactbr`(c), lines 1870-1871: "the numerators and denominators of `ϱ_1, …, ϱ_k` have absolute
value less than `2^Ω`. So `ϱ_k > 2^{−Ω}` and `ϱ_1 < 2^Ω`"). -/
lemma pos_rat_bounds {q : ℚ} {Ω : ℕ} (hq : 0 < q) (he : enc q ≤ Ω) :
    (1 : ℚ) / 2 ^ Ω < q ∧ q < 2 ^ Ω := by
  have hpow : (2 : ℚ) ^ enc q ≤ 2 ^ Ω := pow_le_pow_right₀ (by norm_num) he
  have hden : (q.den : ℚ) < 2 ^ enc q := by exact_mod_cast den_lt q
  have hnum : (q.num.natAbs : ℚ) < 2 ^ enc q := by exact_mod_cast natAbs_num_lt q
  have hn : 0 < q.num := Rat.num_pos.2 hq
  have hd : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have hq' : q = q.num / q.den := (Rat.num_div_den q).symm
  have hnn : (q.num : ℚ) = (q.num.natAbs : ℚ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hn)]
  constructor
  · rw [hq', hnn]
    have h1 : (1 : ℚ) ≤ (q.num.natAbs : ℚ) := by exact_mod_cast Int.natAbs_pos.2 hn.ne'
    calc (1 : ℚ) / 2 ^ Ω < 1 / q.den :=
          one_div_lt_one_div_of_lt hd (hden.trans_le hpow)
      _ ≤ (q.num.natAbs : ℚ) / q.den := div_le_div_of_nonneg_right h1 hd.le
  · rw [hq', hnn]
    have h1 : (1 : ℚ) ≤ q.den := by exact_mod_cast q.den_pos
    calc (q.num.natAbs : ℚ) / q.den ≤ q.num.natAbs := div_le_self (Nat.cast_nonneg _) h1
      _ < 2 ^ Ω := hnum.trans_le hpow

/-- Two rationals `q' < q` of encoding lengths at most `Ω` differ by more than `2^{−2Ω}` (the proof
of `lem:exactbr`(c), line 1871: "`ϱ_i − ϱ_{i+1} > 2^{−2Ω}` for `1 ≤ i ≤ k`, as `ϱ_i − ϱ_{i+1}` is a
positive rational with a denominator less than `2^{2Ω}`"). -/
lemma rat_gap {q q' : ℚ} {Ω : ℕ} (hlt : q' < q) (he : enc q ≤ Ω) (he' : enc q' ≤ Ω) :
    (1 : ℚ) / 2 ^ (2 * Ω) < q - q' := by
  have hd : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have hd' : (0 : ℚ) < q'.den := by exact_mod_cast q'.den_pos
  have key : q - q' = ((q.num * q'.den - q'.num * q.den : ℤ) : ℚ) / ((q.den : ℚ) * q'.den) := by
    conv_lhs => rw [← Rat.num_div_den q, ← Rat.num_div_den q']
    push_cast
    field_simp
  set N : ℤ := q.num * q'.den - q'.num * q.den
  have hDpos : (0 : ℚ) < (q.den : ℚ) * q'.den := mul_pos hd hd'
  have hN : 0 < N := by
    have h0 : (0 : ℚ) < q - q' := sub_pos.2 hlt
    rw [key] at h0
    exact_mod_cast (div_pos_iff_of_pos_right hDpos).1 h0
  have hN1 : (1 : ℚ) ≤ N := by exact_mod_cast hN
  have hpow : (2 : ℚ) ^ enc q ≤ 2 ^ Ω := pow_le_pow_right₀ (by norm_num) he
  have hpow' : (2 : ℚ) ^ enc q' ≤ 2 ^ Ω := pow_le_pow_right₀ (by norm_num) he'
  have hden : (q.den : ℚ) < 2 ^ Ω := (by exact_mod_cast den_lt q : (q.den : ℚ) < _).trans_le hpow
  have hden' : (q'.den : ℚ) < 2 ^ Ω :=
    (by exact_mod_cast den_lt q' : (q'.den : ℚ) < _).trans_le hpow'
  have hD : (q.den : ℚ) * q'.den < 2 ^ (2 * Ω) := by
    rw [two_mul, pow_add]
    exact mul_lt_mul'' hden hden' hd.le hd'.le
  rw [key]
  calc (1 : ℚ) / 2 ^ (2 * Ω) < 1 / ((q.den : ℚ) * q'.den) := one_div_lt_one_div_of_lt hDpos hD
    _ ≤ N / ((q.den : ℚ) * q'.den) := div_le_div_of_nonneg_right hN1 hDpos.le

/-- The set `A_i` read off a chain `L = [A_1, …, A_k]`, with `A_0 := ∅`. -/
def chainAt {E : Type*} (L : List (Finset E)) (i : ℕ) : Finset E :=
  if i = 0 then ∅ else L.getD (i - 1) ∅

section PartC

variable {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E] (I : RatInst E)

namespace RatInst

/-- The vector `y = ω − αt + θβ⁻¹` of `F_{α,θ} = cut_D + y` (`lem:exactbr`(c)), whose largest
minimizer is computed by one maximum flow in `G_y`. -/
def yθ (α θ : ℚ) (e : E) : ℚ := I.ω e - α * (I.m e / I.β e) + θ * (1 / I.β e)

/-- `Ω := 2⟨α⟩ + 14⟨I⟩` (the proof of `lem:exactbr`(a), line 1838). -/
def Ωα (α : ℚ) : ℕ := 2 * enc α + 14 * I.encI

end RatInst

/-- The step `h := 2^{−2Ω}` of the search (the proof of `lem:exactbr`(c), line 1872). -/
def hstep (Ω : ℕ) : ℚ := 1 / 2 ^ (2 * Ω)

namespace RatInst

/-- The query `A_{jh}(α)` of the search, one maximum flow in `G_{ω−αt+jhβ⁻¹}`. -/
def query (α : ℚ) (j : ℕ) : Finset E := I.largestMin (I.yθ α (j * hstep (I.Ωα α)))

/-- The search of `lem:exactbr`(c) for the share `α`, with at most `|E| + 1` rounds from
`A_0 = ∅`: the sets `A_1, …, A_k` and the queries. -/
def search (α : ℚ) : List (Finset E) × List ℕ :=
  chainSearch (I.query α) (I.Ωα α) (Fintype.card E + 1) ∅

/-- `eq:D-explicit` from a chain `L = [A_1, …, A_k]` (the last sentence of the proof of
`lem:exactbr`(c)): with `A_0 := ∅` and `D_i := A_i ∖ A_{i−1}`,
`ϱ_i = (αt(D_i) − f(A_i) + f(A_{i−1}))/β⁻¹(D_i)`, `x_e = (αm_e − ϱ_i)/β_e` for `e ∈ D_i`, and
`x_e = αt_e` for `e ∉ A_k`; the block of `e` is found as the first `i` with `e ∈ A_{i+1}`. -/
def xOfChain (α : ℚ) (L : List (Finset E)) (e : E) : ℚ :=
  if h : ∃ i, i < L.length ∧ e ∈ chainAt L (i + 1) then
    (α * I.m e - (α * I.tQ (chainAt L (Nat.find h + 1) \ chainAt L (Nat.find h)) -
      I.fQ (chainAt L (Nat.find h + 1)) + I.fQ (chainAt L (Nat.find h))) /
      I.binvQ (chainAt L (Nat.find h + 1) \ chainAt L (Nat.find h))) / I.β e
  else α * (I.m e / I.β e)

/-- The output of the procedure of `lem:exactbr`(c): `x*(α)` from the chain the search finds. -/
def exactResponse (α : ℚ) (e : E) : ℚ := I.xOfChain α (I.search α).1 e

end RatInst

omit [Nonempty E] in
/-- For `θ > 0`, the largest minimizer of `F_{α,θ} = cut_D + (ω − αt + θβ⁻¹)` is `A_θ(α)` (the
proof of `lem:exactbr`(c), line 1864: "By `thm:levelsets`, `A_θ(α)` is the largest minimizer of
`F_{α,θ}`", by `exactbr_c`). -/
theorem largestMin_yθ (hI : I.InCcut) {α θ : ℚ} (hα : 0 ≤ α) (hθ : 0 < θ) :
    I.largestMin (I.yθ α θ) =
      levelSet I.mR I.βR α (bestResponse I.f I.mR I.βR α) θ := by
  have hα' : (0 : ℝ) ≤ α := by exact_mod_cast hα
  obtain ⟨-, -, h2⟩ := exactbr_c hI.2 hα' (F := I.form hI.1) (fun S => rfl) rfl
  obtain ⟨hF', hmin, hmax, -⟩ := h2 θ (by exact_mod_cast hθ)
  have hcast : ∀ S, ((I.cutVal (I.yθ α θ) S : ℚ) : ℝ) =
      levelFun I.f I.mR I.βR α θ S := fun S => by
    rw [hF' S]
    simp only [RatInst.cutVal, RatInst.yθ]
    push_cast
    rw [I.cutQ_cast hI.1]
    rfl
  apply I.largestMin_eq
  · intro S
    have h := hmin S
    rw [← hcast, ← hcast] at h
    exact_mod_cast h
  · intro S hS
    apply hmax S
    rw [← hcast, ← hcast]
    exact_mod_cast hS

end PartC

/-! ### (c): the search finds `x*(α)` -/

section PartC2

variable {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E] (I : RatInst E)

namespace RatInst

/-- `x*(α)` of `I`. -/
def xs (α : ℚ) : E → ℝ := bestResponse I.f I.mR I.βR α

/-- The marginals `ρ(α) = αm − βx*(α)`. -/
def ρα (α : ℚ) : E → ℝ := marg I.mR I.βR α (I.xs α)

/-- `k`, the number of distinct positive values `ϱ_1 > ⋯ > ϱ_k` of `ρ(α)`. -/
def kα (α : ℚ) : ℕ := numVals (I.ρα α) 0

/-- The chain `A_0 = ∅ ⊂ A_1 ⊂ ⋯ ⊂ A_k` of the proof of `lem:exactbr`(a). -/
def Aα (α : ℚ) (i : ℕ) : Finset E := chainA I.mR I.βR α (I.xs α) i

end RatInst

/-- The bounds of the proof of `lem:exactbr`(c) (`stoc-sections/appD-hardness.tex:1870-1871`): "By
(a), the numerators and denominators of `ϱ_1, …, ϱ_k` have absolute value less than `2^Ω`. So
`ϱ_k > 2^{−Ω}` and `ϱ_1 < 2^Ω`, and `ϱ_i − ϱ_{i+1} > 2^{−2Ω}` for `1 ≤ i ≤ k`, as `ϱ_i − ϱ_{i+1}` is
a positive rational with a denominator less than `2^{2Ω}`", with `ϱ_{k+1} := 0` (line 1864)
(indices from `0`; `rat_gap`, for `i = k` with `ϱ_{k+1} = 0`). -/
theorem varrho_bounds (hI : I.InCcut) {α : ℚ} (hα : 0 ≤ α) {i : ℕ} (hi : i < I.kα α) :
    (((1 : ℚ) / 2 ^ I.Ωα α : ℚ) : ℝ) < theta (I.ρα α) 0 i ∧
    theta (I.ρα α) 0 i < 2 ^ I.Ωα α ∧
    (hstep (I.Ωα α) : ℝ) < theta (I.ρα α) 0 i - theta (I.ρα α) 0 (i + 1) := by
  obtain ⟨ϱ, hϱ, hϱe⟩ := enc_varrho_le I hI hα hi
  have hϱe' : enc ϱ ≤ I.Ωα α := hϱe
  have hpos : 0 < ϱ := by
    have h := c_lt_theta hi
    change (0 : ℝ) < theta (I.ρα α) 0 i at h
    rw [show theta (I.ρα α) 0 i = (ϱ : ℝ) from hϱ.symm] at h
    exact_mod_cast h
  obtain ⟨b1, b2⟩ := pos_rat_bounds hpos hϱe'
  have hϱ' : theta (I.ρα α) 0 i = (ϱ : ℝ) := hϱ.symm
  refine ⟨by rw [hϱ']; exact_mod_cast b1, by rw [hϱ']; exact_mod_cast b2, ?_⟩
  rcases lt_or_ge (i + 1) (I.kα α) with hi' | hi'
  · obtain ⟨ϱ', hϱ'', hϱe''⟩ := enc_varrho_le I hI hα hi'
    have h1 : theta (I.ρα α) 0 (i + 1) = (ϱ' : ℝ) := hϱ''.symm
    have hlt : ϱ' < ϱ := by
      have h := theta_lt_theta (ρ := I.ρα α) (c := 0) (Nat.lt_succ_self i) hi'.le
      rw [h1, hϱ'] at h
      exact_mod_cast h
    have h := rat_gap hlt hϱe' hϱe''
    rw [hϱ', h1]
    unfold hstep
    exact_mod_cast h
  · -- `i = k`: `ϱ_k − ϱ_{k+1} = ϱ_k − 0` is a positive rational with a denominator less than
    -- `2^{2Ω}` (`rat_gap` with `0`, whose encoding length `2` is at most that of `ϱ_k`)
    rw [theta_of_le hi', sub_zero, hϱ']
    have h0 : enc (0 : ℚ) ≤ I.Ωα α :=
      (show enc (0 : ℚ) = 2 by rfl).le.trans ((two_le_enc ϱ).trans hϱe')
    have h := rat_gap hpos hϱe' h0
    rw [sub_zero] at h
    unfold hstep
    exact_mod_cast h

omit [Nonempty E] in
/-- The queries: for `j ≥ 1`, `q j = A_{jh}(α)` (not in the paper: the queries of the search are
the largest minimizers of `F_{α,jh}`, by `largestMin_yθ`). -/
lemma query_eq (hI : I.InCcut) {α : ℚ} (hα : 0 ≤ α) {j : ℕ} (hj : 1 ≤ j) :
    I.query α j = levelSet I.mR I.βR α (I.xs α) (((j : ℚ) * hstep (I.Ωα α) : ℚ) : ℝ) := by
  have hh : 0 < hstep (I.Ωα α) := by unfold hstep; positivity
  have hj' : (0 : ℚ) < j := by exact_mod_cast hj
  exact largestMin_yθ I hI hα (mul_pos hj' hh)

/-- One round of the search on `A_i` (the proof of `lem:exactbr`(c), lines 1872-1878: "Let
`h := 2^{−2Ω}`. … Let `0 ≤ i ≤ k`, and suppose that `A_i` is known."), with the paper's step `h`
and the shares `jh`, `j ∈ {1, …, 2^{3Ω}}`, from (1) of `exactbr_c` and the bounds `varrho_bounds`
(indices from `0`: `ϱ_{i+1}` is `theta ρ 0 i`). The round's steps: (3)
"As `0 < h < ϱ_k`, we have `A_h(α) = A_k`, so if `A_h(α) = A_i`, then `i = k` and we stop."; (4)
"Otherwise `i < k`, and for `j ∈ {1, …, 2^{3Ω}}` we have `A_{jh}(α) ⊋ A_i` if and only if
`jh ≤ ϱ_{i+1}`."; (5) "As `h < ϱ_{i+1} < 2^Ω = 2^{3Ω}h`, a binary search over `j` with at most
`3Ω + 1` maximum flows finds the largest such `j`, namely `j = ⌊ϱ_{i+1}/h⌋`. It satisfies
`ϱ_{i+2} < ϱ_{i+1} − h < jh ≤ ϱ_{i+1}`, so `A_{jh}(α) = A_{i+1}`." (`bsearch_spec`; the first query
`j = 1` is the test of (3), the other `3Ω` are the binary search). -/
theorem searchRound_spec (hI : I.InCcut) {α : ℚ} (hα : 0 ≤ α) {i : ℕ} (hi : i ≤ I.kα α) :
    (i = I.kα α → searchRound (I.query α) (I.Ωα α) (I.Aα α i) = (none, [1])) ∧
    (i < I.kα α → ∃ qs : List ℕ,
      searchRound (I.query α) (I.Ωα α) (I.Aα α i) = (some (I.Aα α (i + 1)), qs) ∧
      qs.length = 3 * I.Ωα α + 1 ∧ ∀ j ∈ qs, 1 ≤ j ∧ j ≤ 2 ^ (3 * I.Ωα α)) := by
  have hα' : (0 : ℝ) ≤ α := by exact_mod_cast hα
  -- (1) "Then `A_θ(α) = A_i` for `ϱ_{i+1} < θ ≤ ϱ_i` and `i = 0, …, k`." (`exactbr_c`)
  obtain ⟨h1a, h1b, -⟩ := exactbr_c hI.2 hα' (F := I.form hI.1) (fun S => rfl) (rfl : I.xs α = _)
  -- "Let `h := 2^{−2Ω}`." (`hstep`)
  have hhq : (0 : ℚ) < hstep (I.Ωα α) := by unfold hstep; positivity
  have hh : (0 : ℝ) < (hstep (I.Ωα α) : ℝ) := by exact_mod_cast hhq
  -- `h ≤ 2^{−Ω}`
  have hhle : ((hstep (I.Ωα α) : ℚ) : ℝ) ≤ (((1 : ℚ) / 2 ^ I.Ωα α : ℚ) : ℝ) := by
    have : hstep (I.Ωα α) ≤ (1 : ℚ) / 2 ^ I.Ωα α :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
    exact_mod_cast this
  have hq1 : I.query α 1 = levelSet I.mR I.βR α (I.xs α) (hstep (I.Ωα α) : ℝ) := by
    rw [query_eq I hI hα le_rfl, Nat.cast_one, one_mul]
  -- (3) "As `0 < h < ϱ_k`, we have `A_h(α) = A_k`, …" (by (1), with `ϱ_{k+1} = 0`)
  have hAk : I.query α 1 = I.Aα α (I.kα α) := by
    rw [hq1]
    rcases Nat.eq_zero_or_pos (I.kα α) with hk | hk
    · rw [hk]
      refine h1a _ ?_
      change theta (I.ρα α) 0 0 < _
      rw [theta_of_le (by unfold RatInst.kα at hk; omega)]
      exact hh
    · obtain ⟨k', hk'⟩ : ∃ k', I.kα α = k' + 1 := ⟨I.kα α - 1, by omega⟩
      obtain ⟨b1, -, -⟩ := varrho_bounds I hI hα (show k' < I.kα α by omega)
      rw [hk']
      refine h1b k' (show k' < I.kα α by omega) _ ?_ (hhle.trans b1.le)
      change theta (I.ρα α) 0 (k' + 1) < _
      rw [theta_of_le (show I.kα α ≤ k' + 1 by omega)]
      exact hh
  refine ⟨fun hik => ?_, fun hik => ?_⟩
  · -- "… so if `A_h(α) = A_i`, then `i = k` and we stop."
    subst hik
    simp only [searchRound, hAk, ↓reduceIte]
  -- (4) "Otherwise `i < k`, and for `j ∈ {1, …, 2^{3Ω}}` we have `A_{jh}(α) ⊋ A_i` if and only if
  -- `jh ≤ ϱ_{i+1}`." (by (1): for `jh > ϱ_{i+1}`, `A_{jh}(α) ⊆ A_i`; for `jh ≤ ϱ_{i+1}`,
  -- `A_i ⊊ A_{i+1} ⊆ A_{jh}(α)`)
  have h4 : ∀ j : ℕ, 1 ≤ j → j ≤ 2 ^ (3 * I.Ωα α) →
      (I.Aα α i ⊂ I.query α j ↔ (j : ℝ) * (hstep (I.Ωα α) : ℝ) ≤ theta (I.ρα α) 0 i) := by
    intro j hj _
    rw [query_eq I hI hα hj]
    push_cast
    constructor
    · intro hss
      by_contra hc
      push Not at hc
      rcases i with _ | i
      · rw [h1a _ hc] at hss
        exact (ssubset_irrefl _) hss
      · apply not_subset_of_ssubset hss
        intro e he
        simp only [levelSet, mem_filter, mem_univ, true_and] at he
        simp only [RatInst.Aα, chainA, levelSet, mem_filter, mem_univ, true_and]
        exact theta_le_of_lt (Nat.lt_of_succ_lt hik) (hc.trans_le he)
    · intro hθi
      have hss : I.Aα α i ⊂ I.Aα α (i + 1) :=
        Finset.ssubset_iff_subset_ne.2 ⟨chainA_subset hik, fun heq => by
          obtain ⟨e, he⟩ := blockD_nonempty (m := I.mR) (β := I.βR) (α := α) (x := I.xs α) hik
          exact (mem_sdiff.1 he).2 (by rw [← RatInst.Aα, heq]; exact (mem_sdiff.1 he).1)⟩
      refine Finset.ssubset_of_ssubset_of_subset hss fun e he => ?_
      simp only [RatInst.Aα, chainA, levelSet, mem_filter, mem_univ, true_and] at he ⊢
      exact hθi.trans he
  -- (5) "As `h < ϱ_{i+1} < 2^Ω = 2^{3Ω}h`, a binary search over `j` with at most `3Ω + 1` maximum
  -- flows finds the largest such `j`, namely `j = ⌊ϱ_{i+1}/h⌋`." (`varrho_bounds`, `bsearch_spec`)
  obtain ⟨b1, b2, b3⟩ := varrho_bounds I hI hα hik
  have hhi : (hstep (I.Ωα α) : ℝ) < theta (I.ρα α) 0 i := hhle.trans_lt b1
  have h2Ω : (2 : ℝ) ^ I.Ωα α = 2 ^ (3 * I.Ωα α) * (hstep (I.Ωα α) : ℝ) := by
    have : (2 : ℚ) ^ I.Ωα α = 2 ^ (3 * I.Ωα α) * hstep (I.Ωα α) := by
      unfold hstep
      rw [show 3 * I.Ωα α = I.Ωα α + 2 * I.Ωα α by ring, pow_add]
      field_simp
    exact_mod_cast this
  have hdiv : 0 ≤ theta (I.ρα α) 0 i / (hstep (I.Ωα α) : ℝ) := div_nonneg (by linarith) hh.le
  have hP : ∀ j, 1 ≤ j → j < 1 + 2 ^ (3 * I.Ωα α) → (I.Aα α i ⊂ I.query α j ↔
      j ≤ ⌊theta (I.ρα α) 0 i / (hstep (I.Ωα α) : ℝ)⌋₊) := fun j hj hj' => by
    rw [h4 j hj (by omega), Nat.le_floor_iff hdiv, le_div_iff₀ hh]
  have hJ1 : 1 ≤ ⌊theta (I.ρα α) 0 i / (hstep (I.Ωα α) : ℝ)⌋₊ := by
    rw [Nat.le_floor_iff hdiv, le_div_iff₀ hh]
    simpa using hhi.le
  have hJ2 : ⌊theta (I.ρα α) 0 i / (hstep (I.Ωα α) : ℝ)⌋₊ < 1 + 2 ^ (3 * I.Ωα α) := by
    have hlt : theta (I.ρα α) 0 i / (hstep (I.Ωα α) : ℝ) < 2 ^ (3 * I.Ωα α) := by
      rw [div_lt_iff₀ hh, ← h2Ω]
      exact b2
    have := (Nat.floor_lt hdiv).2
      (by exact_mod_cast hlt : _ < ((2 ^ (3 * I.Ωα α) : ℕ) : ℝ))
    omega
  obtain ⟨r1, r2, r3, r4⟩ := bsearch_spec (I.query α) (I.Aα α i ⊂ ·) (3 * I.Ωα α) 1
    (I.query α 1) hP rfl hJ1 hJ2
  -- "It satisfies `ϱ_{i+2} < ϱ_{i+1} − h < jh ≤ ϱ_{i+1}`, so `A_{jh}(α) = A_{i+1}`." (by (1))
  set J := ⌊theta (I.ρα α) 0 i / (hstep (I.Ωα α) : ℝ)⌋₊ with hJ
  have i1 : theta (I.ρα α) 0 (i + 1) < theta (I.ρα α) 0 i - hstep (I.Ωα α) := by linarith
  have i2 : theta (I.ρα α) 0 i - hstep (I.Ωα α) < (J : ℝ) * hstep (I.Ωα α) := by
    have hlt := Nat.lt_floor_add_one (theta (I.ρα α) 0 i / (hstep (I.Ωα α) : ℝ))
    rw [div_lt_iff₀ hh] at hlt
    linarith
  have i3 : (J : ℝ) * hstep (I.Ωα α) ≤ theta (I.ρα α) 0 i := by
    have hle := Nat.floor_le hdiv
    rw [le_div_iff₀ hh] at hle
    exact hle
  have hqJ : I.query α J = I.Aα α (i + 1) := by
    rw [query_eq I hI hα hJ1]
    push_cast
    exact h1b i hik _ (i1.trans i2) i3
  -- the round: the test of (3) fails, as `A_h(α) ⊋ A_i` by (4) with `j = 1`, and the binary
  -- search of (5) returns `A_{i+1}`
  have hne : I.query α 1 ≠ I.Aα α i := by
    intro heq
    have := (h4 1 le_rfl Nat.one_le_two_pow).2 (by simpa using hhi.le)
    rw [heq] at this
    exact (ssubset_irrefl _) this
  refine ⟨1 :: (bsearch (I.query α) (I.Aα α i ⊂ ·) 1 (I.query α 1) (3 * I.Ωα α)).2.2,
    ?_, ?_, ?_⟩
  · simp only [searchRound, hne, ↓reduceIte, r2, hqJ]
  · simp [r3]
  · intro j hj
    rcases List.mem_cons.1 hj with rfl | hj
    · exact ⟨le_rfl, Nat.one_le_two_pow⟩
    · have := r4 j hj
      omega

/-- The search finds the chain (the proof of `lem:exactbr`(c), lines 1873-1880): from `A_i`, with at
least `k − i + 1` rounds, it returns `A_{i+1}, …, A_k` after at most `(k − i + 1)(3Ω + 1)` queries,
each with `1 ≤ j ≤ 2^{3Ω}` (not in the paper: the induction over the rounds). -/
theorem chainSearch_spec (hI : I.InCcut) {α : ℚ} (hα : 0 ≤ α) :
    ∀ n i, i ≤ I.kα α → I.kα α - i < n →
      (chainSearch (I.query α) (I.Ωα α) n (I.Aα α i)).1 =
        (List.range (I.kα α - i)).map (fun l => I.Aα α (i + 1 + l)) ∧
      (chainSearch (I.query α) (I.Ωα α) n (I.Aα α i)).2.length ≤
        (I.kα α - i + 1) * (3 * I.Ωα α + 1) ∧
      ∀ j ∈ (chainSearch (I.query α) (I.Ωα α) n (I.Aα α i)).2, 1 ≤ j ∧ j ≤ 2 ^ (3 * I.Ωα α) := by
  intro n
  induction n with
  | zero => intro i _ h; omega
  | succ n ih =>
    intro i hi hn
    obtain ⟨hstop, hgo⟩ := searchRound_spec I hI hα hi
    rcases hi.lt_or_eq with hik | hik
    · have hn' : I.kα α - (i + 1) < n := by clear hstop hgo ih; omega
      have hsub : I.kα α - i = I.kα α - (i + 1) + 1 := by clear hstop hgo ih; omega
      obtain ⟨qs, hqs, hlen, hmem⟩ := hgo hik
      obtain ⟨r1, r2, r3⟩ := ih (i + 1) hik hn'
      simp only [chainSearch, hqs]
      refine ⟨?_, ?_, ?_⟩
      · rw [r1, hsub, List.range_succ_eq_map, List.map_cons, List.map_map]
        congr 1
        refine List.map_congr_left fun l _ => ?_
        simp only [Function.comp_apply]
        congr 1
        simp only [Nat.succ_eq_add_one]
        ring
      · rw [List.length_append, hlen]
        calc 3 * I.Ωα α + 1 + (chainSearch (I.query α) (I.Ωα α) n (I.Aα α (i + 1))).2.length
            ≤ 3 * I.Ωα α + 1 + (I.kα α - (i + 1) + 1) * (3 * I.Ωα α + 1) :=
              Nat.add_le_add_left r2 _
          _ = (I.kα α - i + 1) * (3 * I.Ωα α + 1) := by rw [hsub]; ring
      · intro j hj
        rcases List.mem_append.1 hj with hj | hj
        · exact hmem j hj
        · exact r3 j hj
    · subst hik
      simp only [chainSearch, hstop (rfl)]
      refine ⟨by simp, by simp, ?_⟩
      intro j hj
      simp only [List.mem_singleton] at hj
      subst hj
      exact ⟨le_rfl, Nat.one_le_two_pow⟩

omit [Nonempty E] in
/-- "`eq:D-explicit` gives `x*(α)` from `A_1, …, A_k`" (the proof of `lem:exactbr`(c), line 1880):
`xOfChain` on the chain `A_1, …, A_k` is `x*(α)` (with `exactbr_a`). -/
theorem xOfChain_eq (hI : I.InCcut) {α : ℚ} (hα : 0 ≤ α) (e : E) :
    (I.xOfChain α ((List.range (I.kα α)).map (fun l => I.Aα α (0 + 1 + l))) e : ℝ) =
      I.xs α e := by
  have hα' : (0 : ℝ) ≤ α := by exact_mod_cast hα
  obtain ⟨h5a, h5b, h5c, -⟩ := exactbr_a hI.2 hα' (rfl : I.xs α = _)
  set L := (List.range (I.kα α)).map (fun l => I.Aα α (0 + 1 + l)) with hL
  have hlen : L.length = I.kα α := by simp [hL]
  -- the sets `A_i` read off the list
  have hA : ∀ i, i ≤ I.kα α → chainAt L i = I.Aα α i := by
    intro i hi
    unfold chainAt
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp [RatInst.Aα, chainA]
    · rw [ite_eq_right hi0.ne', List.getD_eq_getElem _ _ (by rw [hlen]; omega)]
      simp only [hL, List.getElem_map, List.getElem_range]
      congr 1
      omega
  unfold RatInst.xOfChain
  by_cases hex : ∃ i, i < L.length ∧ e ∈ chainAt L (i + 1)
  · -- `e` lies in a block: the first `i` with `e ∈ A_{i+1}`
    rw [dite_eq_left hex]
    obtain ⟨hi₀k, hei₀⟩ := Nat.find_spec hex
    set i₀ := Nat.find hex with hi₀
    rw [hlen] at hi₀k
    rw [hA (i₀ + 1) (by omega)] at hei₀ ⊢
    rw [hA i₀ (by omega)]
    have hnot : e ∉ I.Aα α i₀ := by
      rcases Nat.eq_zero_or_pos i₀ with h0 | h0
      · rw [h0]
        simp [RatInst.Aα, chainA]
      · intro he
        have hmin := Nat.find_min hex (show i₀ - 1 < i₀ by omega)
        apply hmin
        refine ⟨by rw [hlen]; omega, ?_⟩
        rw [hA (i₀ - 1 + 1) (by omega), show i₀ - 1 + 1 = i₀ by omega]
        exact he
    have heD : e ∈ blockD I.mR I.βR α (I.xs α) i₀ := mem_sdiff.2 ⟨hei₀, hnot⟩
    change (_ : ℝ) = I.xs α e
    rw [h5b i₀ hi₀k e heD, h5a i₀ hi₀k]
    push_cast
    rw [I.tQ_cast, I.fQ_cast, I.fQ_cast, I.binvQ_cast]
    rfl
  · -- `e ∉ A_k`, and `x_e = αt_e`
    rw [dite_eq_right hex]
    have hnot : e ∉ chainA I.mR I.βR α (I.xs α) (numVals (marg I.mR I.βR α (I.xs α)) 0) := by
      intro he
      change e ∈ I.Aα α (I.kα α) at he
      rcases Nat.eq_zero_or_pos (I.kα α) with h0 | h0
      · rw [h0] at he
        simp [RatInst.Aα, chainA] at he
      · apply hex
        refine ⟨I.kα α - 1, by rw [hlen]; omega, ?_⟩
        rw [hA (I.kα α - 1 + 1) (by omega), show I.kα α - 1 + 1 = I.kα α by omega]
        exact he
    change (_ : ℝ) = I.xs α e
    rw [h5c e hnot]
    push_cast
    rfl

/-- **`lem:exactbr`(c)** in the bit model (`stoc-sections/appD-hardness.tex:1804`, proof lines
1862-1880): "The best response `x*(α)` can be computed in polynomial time". The procedure
`RatInst.exactResponse` (the search `RatInst.search` and `eq:D-explicit`) returns `x*(α)`; it uses
at most `(|E| + 1)(3Ω + 1)` maximum flows, each for some `θ = jh` with `1 ≤ j ≤ 2^{3Ω}`; every such
`θ` has encoding length at most `5Ω + 3`, so every capacity `ω_e − αt_e + θ/β_e` of these flows has
encoding length at most `2(⟨α⟩ + 3⟨I⟩ + 5Ω + 3)` ("all capacities in these flows have polynomial
encoding length"), besides the capacities of `D`.

The proof's steps: (1) `A_θ(α) = A_i` for `ϱ_{i+1} < θ ≤ ϱ_i`, and `A_θ(α)` is the largest
minimizer of `F_{α,θ}` (`exactbr_c`, `largestMin_yθ`); (2) the bounds on the `ϱ_i` and their gaps
(`varrho_bounds`); (3) the rounds, with `h = 2^{−2Ω}` and the shares `jh`, `j ∈ {1, …, 2^{3Ω}}`
(`searchRound_spec`, with `bsearch_spec`); (4) "After at most `|E| + 1` rounds"
(`chainSearch_spec`, with `k ≤ |E|`); (5) "Every `θ = jh` has encoding length at most `5Ω + 3`";
(6) `eq:D-explicit` gives `x*(α)` from `A_1, …, A_k` (`xOfChain_eq`). -/
theorem exactbr_c_enc (hI : I.InCcut) {α : ℚ} (hα : 0 ≤ α) :
    (∀ e, (I.exactResponse α e : ℝ) = bestResponse I.f I.mR I.βR α e) ∧
    (I.search α).2.length ≤ (Fintype.card E + 1) * (3 * I.Ωα α + 1) ∧
    ∀ j ∈ (I.search α).2, enc (j * hstep (I.Ωα α)) ≤ 5 * I.Ωα α + 3 ∧
      ∀ e, enc (I.yθ α (j * hstep (I.Ωα α)) e) ≤ 2 * (enc α + 3 * I.encI + 5 * I.Ωα α + 3) := by
  have hk : I.kα α ≤ Fintype.card E := by
    unfold RatInst.kα numVals valsAbove
    exact (card_filter_le _ _).trans (card_image_le.trans (by simp))
  -- (4) "After at most `|E| + 1` rounds, …" (the search from `A_0 = ∅`, with
  -- `|E| + 1 ≥ k + 1` rounds)
  have hA0 : (∅ : Finset E) = I.Aα α 0 := by simp [RatInst.Aα, chainA]
  obtain ⟨r1, r2, r3⟩ := chainSearch_spec I hI hα (Fintype.card E + 1) 0 (Nat.zero_le _)
    (by omega)
  rw [← hA0] at r1 r2 r3
  rw [Nat.sub_zero] at r1 r2
  refine ⟨fun e => ?_, ?_, fun j hj => ?_⟩
  · -- (6) "… `eq:D-explicit` gives `x*(α)` from `A_1, …, A_k` with polynomially many further
    -- operations on numbers whose encoding lengths are bounded as in the proof of (a)."
    -- The Lean: `xOfChain_eq`; the operations are not counted.
    unfold RatInst.exactResponse RatInst.search
    rw [r1]
    exact xOfChain_eq I hI hα e
  · unfold RatInst.search
    exact r2.trans (Nat.mul_le_mul_right _ (show I.kα α + 1 ≤ Fintype.card E + 1 by omega))
  · -- (5) "Every `θ = jh` has encoding length at most `5Ω + 3`, so all capacities in these flows
    -- have polynomial encoding length." (`θ = jh = j/2^{2Ω}` with `j ≤ 2^{3Ω}`)
    obtain ⟨hj1, hj2⟩ := r3 j hj
    have hθ : enc (j * hstep (I.Ωα α)) ≤ 5 * (I.Ωα α) + 3 := by
      have heq : (j : ℚ) * hstep (I.Ωα α) = ((j : ℤ) : ℚ) / ((2 ^ (2 * (I.Ωα α)) : ℕ) : ℚ) := by
        simp only [hstep]
        push_cast
        ring
      refine (enc_le_of_eq_div (by positivity) heq).trans ?_
      have c1 : Nat.clog 2 ((j : ℤ).natAbs + 1) ≤ 3 * (I.Ωα α) + 1 := by
        rw [Int.natAbs_natCast]
        exact (Nat.clog_mono_right 2 (by omega)).trans (clog_two_pow_add_one_le (3 * (I.Ωα α)))
      have c2 := clog_two_pow_add_one_le (2 * (I.Ωα α))
      omega
    refine ⟨hθ, fun e => ?_⟩
    -- the capacities `ω_e − αt_e + θ/β_e`
    have e1 := enc_add₃ (I.ω e) (-(α * (I.m e / I.β e))) (j * hstep (I.Ωα α) * (1 / I.β e))
    rw [enc_neg, ← sub_eq_add_neg] at e1
    have e2 := enc_mul α (I.m e / I.β e)
    have e3 := enc_mul (j * hstep (I.Ωα α)) (1 / I.β e)
    rw [one_div, enc_inv] at e3
    have e4 := I.enc_ω_le e
    have e5 := I.enc_t_le e
    have e6 := I.enc_β_le e
    unfold RatInst.yθ
    rw [one_div] at e1 ⊢
    omega

/-- **`lem:exactbr`** (Lemma C.25, `stoc-sections/appD-hardness.tex:1799-1807`) in the bit model:
let `I = (f, m, β)` be an instance of `𝒞_cut` with the cut form `(D, cap, ω)`, and let `α ≥ 0` be
rational. (a) The best response `x*(α)` is a rational vector, and each of its coordinates has
encoding length at most `6⟨α⟩ + 31⟨I⟩`. (b) Given a rational vector `x ∈ ℚ^E`, one can decide in
polynomial time whether `x = x*(α)`. (c) The best response `x*(α)` can be computed in polynomial
time. Here polynomial time means polynomial in the encoding lengths of `I` and `α`, and in (b) also
of `x`.

Polynomial time is formalised as encoding lengths and counts. (b): the test `RatInst.TestB` (`2|E|`
comparisons, `|E|` evaluations of `f` and one maximum flow) holds if and only if `x = x*(α)`, every
value of `f` has encoding length at most `2⟨I⟩`, and the capacities `ω_e − x_e` of its maximum flow
at most `2(⟨I⟩ + ⟨x_e⟩)`. (c): the procedure `RatInst.exactResponse` returns `x*(α)` with at most
`(|E| + 1)(3Ω + 1)` maximum flows, `Ω = 2⟨α⟩ + 14⟨I⟩`, each for a `θ = jh` of encoding length at
most `5Ω + 3`, whose capacities `ω_e − αt_e + θ/β_e` have encoding length at most
`2(⟨α⟩ + 3⟨I⟩ + 5Ω + 3)`. The maximum flows are cited, and arithmetic operations and running times
are not counted (the header of this file). Its parts are `exactbr_a_enc`, `exactbr_b_enc` and
`exactbr_c_enc`; their docstrings give the paper's steps, whose mathematics is `exactbr_a`,
`exactbr_b` and `exactbr_c`. -/
theorem exactbr (hI : I.InCcut) {α : ℚ} (hα : 0 ≤ α) :
    -- (a)
    (∃ x : E → ℚ, (∀ e, (x e : ℝ) = bestResponse I.f I.mR I.βR α e) ∧
      ∀ e, enc (x e) ≤ 6 * enc α + 31 * I.encI) ∧
    -- (b)
    (∀ x : E → ℚ, (I.TestB α x ↔ (fun e => (x e : ℝ)) = bestResponse I.f I.mR I.βR α) ∧
      (∀ S, enc (I.fQ S) ≤ 2 * I.encI) ∧ (∀ e, enc (I.ω e - x e) ≤ 2 * (I.encI + enc (x e)))) ∧
    -- (c)
    ((∀ e, (I.exactResponse α e : ℝ) = bestResponse I.f I.mR I.βR α e) ∧
      (I.search α).2.length ≤ (Fintype.card E + 1) * (3 * I.Ωα α + 1) ∧
      ∀ j ∈ (I.search α).2, enc (j * hstep (I.Ωα α)) ≤ 5 * I.Ωα α + 3 ∧
        ∀ e, enc (I.yθ α (j * hstep (I.Ωα α)) e) ≤ 2 * (enc α + 3 * I.encI + 5 * I.Ωα α + 3)) :=
  ⟨exactbr_a_enc I hI hα, exactbr_b_enc I hI hα, exactbr_c_enc I hI hα⟩

end PartC2

end

end Hardness

end Stoc
