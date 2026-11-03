-- stamp r11 2026-11-03
import ContractDesignPolymatroids.Convex.Welfare
import ContractDesignPolymatroids.Convex.Ellipsoid

/-!
# Convex costs: the approximation scheme

The STOC version's `alg:convex`, `prop:convexscheme` and `prop:approxresponses`
(`stoc-sections/appF-convex.tex`:56-115, statement of `prop:approxresponses` 08c-convex.tex:7-9), in
the setting of `prop:convexscheme` (`Setting`: a compact action set `K ⊆ ℝ^E_{≥0}` containing zero,
here `P`, a continuous cost `c ≥ 0` on it with `c(0) = 0`, `r(x) = mᵀx` with `m ≥ 0` and a known
bound `r ≤ r̄` on `K`, where `r̄ > 0`), with an oracle `orc` that returns, for a share `α ∈ [0, 1]`
and a precision `δ > 0`, a `δ`-optimal response `orc α δ` at `α` (appF-convex.tex:56); "An
approximate best-response oracle obtains `δ` as input and returns such an action, together with its
exact reward and cost" (08c-convex.tex:4): here `r` and `c` are functions of the response. And
`thm:convexfptas` on `P₊(f)` (08c-convex.tex:16-18, proof appF-convex.tex:143-145).

* `alg:convex` (appF-convex.tex:58-79), line by line (TeX lines): the precisions `d_k = 2^{−k} r̄`
  of the rounds `k = 0, 1, …` of the welfare loop (`loopD`, appF:63 and 68), the estimates
  `W̃_k = r(x̃) − c(x̃)` of the responses `x̃ = orc 1 d_k` (`loopW`, appF:65), the break test
  `W̃ ≥ 2d` (`Brk`, appF:66), the test "`w` is given and `d < w/3`" (`WTest`, appF:67), the loop
  ending with a break in round `K` (`LoopBreaks`) or with "`W = 0`" (`LoopZero`); `LB`, `ᾱ`, `δ`
  (`cLB`, `cᾱ`, `cδ`, appF:70); `J` and `s` (`schemeJ (ε/2) ᾱ`, `schemeS (ε/2) ᾱ`, appF:71) and the
  shares `α̂_j` (`cHat`, appF:73), those of the proof of `thm:fptas` for the accuracy `ε/2`; `h_j`,
  `α̌_j`, `x̃_j` (`cH`, `cChk`, `cResp`, appF:74); `Ũ_j` (`cU`, appF:75); the output (`Returns`,
  appF:77, and `ReturnsZero`, appF:67). The loop does not both break and return "`W = 0`"
  (`not_loopBreaks_and_loopZero`), and it returns "`W = 0`" in at most one round
  (`loopZero_unique`).
* `prop:convexscheme` (`convexscheme`), with the four paragraphs of its proof, which we number (1)
  to (4): (1) "We first analyze the welfare loop" (`step1_pos`, `step1_zero`), (2) "Next we show
  that `LB < OPT`, so that `ᾱ` is a share bound, and we bound `δ` and `J`" (`step2`), (3) "Next we
  show that every `Ũ_j` is a valid bound" (`one_sub_cHat_pos`, `step3`) and (4) "Finally, we show
  that some `Ũ_j` is large" (`step4`). The names `step1_pos`, …, `step4` refer to this numbering.
* `prop:approxresponses` (`approxresponses`): with an approximate best-response oracle, `alg:convex`
  with `w` determines whether `W = 0` and otherwise returns a `(1 − ε)`-optimal contract, with at
  most `14 ε⁻¹ ln(3r̄/w)` oracle calls (`O(ε⁻¹ log(3r̄/w))`, `calls_le`; `O(log(3r̄/w))` if `W = 0`,
  `calls_zero_le`), by `prop:convexscheme`.
* `thm:convexfptas` (`convexfptas`), on `P₊(f)` (`PolySetting.toSetting`), with the steps
  (T1)–(T6) of its proof in order: (T1) and (T3) cite `prop:convexscheme` (`convexscheme`), (T1)
  also `lem:welfare`, and (T5) bounds the iteration number of `lem:ellipsoid` for every precision
  `δ ≥ δ₀` by `⌈32 n² ln(2nM/(εw))⌉` (`log_div_delta0_le`, `ellipsoidIters_le`). Its counts are
  those of the counted scheme `convexC` (section "`alg:convex` with its operation counts"), with
  the counted ellipsoid method of `lem:ellipsoid` as the oracle, in the cost model of
  `Stoc.CountedQ` (`ContractDesignPolymatroids/Preliminaries/CountedOracle.lean`).

What is not formalised: the computational model of 08c-convex.tex:13 (exact real arithmetic, exact
oracle answers) enters in that `c`, `g` and the oracle are exact functions of real points, and in
the cost model of `Stoc.CountedQ`, which counts arithmetic operations and comparisons, submodular
minimizations, evaluations of `f` and queries of the cost oracle; that the ellipsoid method
(`lem:ellipsoid`) computes each response within its iteration bound is not formalised
(`ContractDesignPolymatroids/Convex/Ellipsoid.lean`): the counts of `thm:convexfptas` are proved for the counted scheme,
with the ellipsoid method as a parameter whose `O(n²)` cost of an update is the paper's count
(appF-convex.tex:136), not cited. The
paragraph after the theorem (08c-convex.tex:20-26: for rational piecewise linear costs, a suitable
`w` from the denominators of the optimal value of a linear program, by Cramer's rule and determinant
bounds [GLS88]) is not formalised, and neither is the relation to the conversion of approximately
incentive-compatible contracts in [DRT21] (08c-convex.tex:11).

The bound `r̄ > 0` of the setting ("`r̄ > 0` a known reward bound", 08c-convex.tex:5; on `P₊(f)` the
given reward of success `r̄ > 0` of the model, 02-preliminaries.tex:12) is part of `Setting`
(`Setting.rbar_pos`). The analysis of the welfare loop uses it: the precisions `d = 2^{−k} r̄` are
positive, as the oracle requires (appF-convex.tex:56), and so "If `W = 0`, the loop does not end
without `w`" (`step1_zero`).
-/

namespace Stoc.Convex

open Set Finset

noncomputable section

/-! ### Real-number facts -/

/-- `⌈log₂ z⌉ ≤ z` for `z ≥ 1` (not in the paper: (2) of the proof of `prop:convexscheme` uses
this without proof). -/
lemma ceil_logb_le {z : ℝ} (hz : 1 ≤ z) : (⌈Real.logb 2 z⌉₊ : ℝ) ≤ z := by
  set n := ⌈Real.logb 2 z⌉₊
  have h0 : 0 ≤ Real.logb 2 z := Real.logb_nonneg (by norm_num) hz
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [hn]; push_cast; linarith
  · have hlt : (n : ℝ) < Real.logb 2 z + 1 := Nat.ceil_lt_add_one h0
    -- `2^{n−1} < z` and `n ≤ 2^{n−1}`
    have h1 : (2 : ℝ) ^ ((n : ℝ) - 1) < z := by
      have := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
        (show (n : ℝ) - 1 < Real.logb 2 z by linarith)
      rwa [Real.rpow_logb (by norm_num) (by norm_num) (by linarith)] at this
    have h2 : (n : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) - 1) := by
      have e : ((n : ℝ) - 1) = ((n - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [e, Real.rpow_natCast]
      have : n - 1 < 2 ^ (n - 1) := Nat.lt_two_pow_self
      have : n ≤ 2 ^ (n - 1) := by omega
      exact_mod_cast this
    linarith

/-- `ln z < log₂ z` for `z > 1` (not in the paper: (2) of the proof of `prop:convexscheme` uses
this without proof). -/
lemma log_lt_logb {z : ℝ} (hz : 1 < z) : Real.log z < Real.logb 2 z := by
  have hl : 0 < Real.log z := Real.log_pos hz
  have h2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  have h20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Real.logb, lt_div_iff₀ h20]
  nlinarith

/-- `u ↦ u/(2 ln(2r̄/u))` is nondecreasing on `(0, r̄]` (not in the paper: (2) of the proof of
`prop:convexscheme` asserts that it is increasing). -/
lemma div_log_mono {R w w' : ℝ} (hw : 0 < w) (hww' : w ≤ w') (hw' : w' ≤ R) :
    w / (2 * Real.log (2 * R / w)) ≤ w' / (2 * Real.log (2 * R / w')) := by
  have hw'0 : 0 < w' := hw.trans_le hww'
  have hl' : 0 < Real.log (2 * R / w') := Real.log_pos (by rw [lt_div_iff₀ hw'0]; linarith)
  have hll : Real.log (2 * R / w') ≤ Real.log (2 * R / w) :=
    Real.log_le_log (div_pos (by linarith) hw'0) (div_le_div_of_nonneg_left (by linarith) hw hww')
  exact div_le_div₀ hw'0.le hww' (by linarith) (by linarith)

/-- `u ↦ u/⌈log₂(3r̄/u)⌉` is nondecreasing on `(0, r̄]` (not in the paper: the proof of
`thm:convexfptas` asserts this). -/
lemma div_ceil_mono {R x x' : ℝ} (hx : 0 < x) (hxx' : x ≤ x') (hx' : x' ≤ R) :
    x / (⌈Real.logb 2 (3 * R / x)⌉₊ : ℝ) ≤ x' / (⌈Real.logb 2 (3 * R / x')⌉₊ : ℝ) := by
  have hx'0 : 0 < x' := hx.trans_le hxx'
  have hR : 0 < R := hx'0.trans_le hx'
  have h1 : (1 : ℝ) ≤ ⌈Real.logb 2 (3 * R / x')⌉₊ := by
    have : 1 ≤ Real.logb 2 (3 * R / x') := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
      rw [le_div_iff₀ hx'0]
      norm_num
      linarith
    exact_mod_cast Nat.one_le_iff_ne_zero.2 fun h0 => by
      have := Nat.le_ceil (Real.logb 2 (3 * R / x'))
      rw [h0] at this
      push_cast at this
      linarith
  have hle : (⌈Real.logb 2 (3 * R / x')⌉₊ : ℝ) ≤ ⌈Real.logb 2 (3 * R / x)⌉₊ := by
    exact_mod_cast Nat.ceil_mono (Real.logb_le_logb_of_le (by norm_num) (by positivity)
      (div_le_div_of_nonneg_left (by linarith) hx hxx'))
  exact div_le_div₀ hx'0.le hxx' (by linarith) hle

/-! ### `alg:convex` -/

section Alg

variable {E : Type*} [Fintype E] (rb : ℝ) (m : E → ℝ) (c : (E → ℝ) → ℝ)
  (orc : ℝ → ℝ → (E → ℝ))

/-- `alg:convex` (appF-convex.tex:63, 68): the precision `d_k = 2^{−k} r̄` of round `k` of the
welfare loop (`d ← r̄`, then `d ← d/2` in every round). -/
def loopD (k : ℕ) : ℝ := rb / 2 ^ k

/-- `alg:convex` (appF-convex.tex:65): `x̃ ←` a `d_k`-optimal response at the share `1`
(`orc 1 d_k`), and `W̃_k ← r(x̃) − c(x̃)`. -/
def loopW (k : ℕ) : ℝ := reward m (orc 1 (loopD rb k)) - c (orc 1 (loopD rb k))

/-- `alg:convex` (appF-convex.tex:66): the test `W̃ ≥ 2d` (then the loop breaks). -/
def Brk (k : ℕ) : Prop := 2 * loopD rb k ≤ loopW rb m c orc k

/-- `alg:convex` (appF-convex.tex:67): "`w` is given and `d < w/3`" (then the algorithm returns
"`W = 0`"); `w = none` when `w` is not given. -/
def WTest (w : Option ℝ) (k : ℕ) : Prop := ∃ w₀ ∈ w, loopD rb k < w₀ / 3

/-- `alg:convex` (appF-convex.tex:64-69): the loop breaks in round `K` (the test of appF:66), and
no earlier round broke or returned. -/
def LoopBreaks (w : Option ℝ) (K : ℕ) : Prop :=
  Brk rb m c orc K ∧ ∀ k < K, ¬ Brk rb m c orc k ∧ ¬ WTest rb w k

/-- `alg:convex` (appF-convex.tex:64-69): the loop returns "`W = 0`" in round `K` (the test of
appF:67; the test of appF:66, which comes first, fails there), and no earlier round broke or
returned. -/
def LoopZero (w : Option ℝ) (K : ℕ) : Prop :=
  ¬ Brk rb m c orc K ∧ WTest rb w K ∧ ∀ k < K, ¬ Brk rb m c orc k ∧ ¬ WTest rb w k

/-- `alg:convex` (appF-convex.tex:70): `LB = W̃/(2⌈log₂(2r̄/W̃)⌉)`. -/
def cLB (Wt : ℝ) : ℝ := Wt / (2 * ⌈Real.logb 2 (2 * rb / Wt)⌉₊)

/-- `alg:convex` (appF-convex.tex:70): `ᾱ = 1 − LB/r̄`. -/
def cᾱ (Wt : ℝ) : ℝ := 1 - cLB rb Wt / rb

/-- `alg:convex` (appF-convex.tex:70): `δ = ε² LB/64`. -/
def cδ (ε Wt : ℝ) : ℝ := ε ^ 2 * cLB rb Wt / 64

/-- `alg:convex` (appF-convex.tex:71, 73): "`J ← min{j ∈ ℤ_{≥0} : (1 − ε/4)^j ≤ 1 − ᾱ}`,
`s ← ⌈log₂(8/(ε(1 − ᾱ)))⌉`" and, for `j = 0, …, J`, "`α̂_j ← 1 − 2^{−s} ⌊2^s (1 − ε/4)^j⌋`".
These are exactly the shares of the proof of `thm:fptas` for the accuracy `ε/2` and the share bound
`ᾱ` (`schemeShare (ε/2) ᾱ j`, with `J = schemeJ (ε/2) ᾱ` and `s = schemeS (ε/2) ᾱ`), the shares
that the algorithm bridges ("every share `α̂_j` constructed in the proof of `thm:fptas`",
appF-convex.tex:56): with `ε/2` in place of `ε`, that proof has `ε' = ε/4`,
`J = min{j ≥ 0 : (1 − ε/4)^j ≤ 1 − ᾱ}` and `s = ⌈log₂(4/((ε/2)(1 − ᾱ)))⌉ = ⌈log₂(8/(ε(1 − ᾱ)))⌉`.
-/
def cHat (ε Wt : ℝ) (j : ℕ) : ℝ := schemeShare (ε / 2) (cᾱ rb Wt) j

/-- `alg:convex` (appF-convex.tex:74): `h_j = (ε/8)(1 − α̂_j)`. -/
def cH (ε Wt : ℝ) (j : ℕ) : ℝ := ε / 8 * (1 - cHat rb ε Wt j)

/-- `alg:convex` (appF-convex.tex:74): `α̌_j = α̂_j + 2h_j`. -/
def cChk (ε Wt : ℝ) (j : ℕ) : ℝ := cHat rb ε Wt j + 2 * cH rb ε Wt j

/-- `alg:convex` (appF-convex.tex:74): `x̃_j ←` a `δ`-optimal response at the share `α̂_j + h_j`. -/
def cResp (ε Wt : ℝ) (j : ℕ) : E → ℝ := orc (cHat rb ε Wt j + cH rb ε Wt j) (cδ rb ε Wt)

/-- `alg:convex` (appF-convex.tex:75): `Ũ_j = (1 − α̌_j)(r(x̃_j) − δ/h_j)`. -/
def cU (ε Wt : ℝ) (j : ℕ) : ℝ :=
  (1 - cChk rb ε Wt j) * (reward m (cResp rb orc ε Wt j) - cδ rb ε Wt / cH rb ε Wt j)

/-- **`alg:convex`** (Algorithm 3, appF-convex.tex:58-79): the algorithm, with or without `w`
(`w = none`), returns the share `b = α̌_ĵ` and the number `Ũ = Ũ_ĵ` (`Ut`, appF:77): the loop breaks
in a round `K`, `W̃ = W̃_K`, and `ĵ ≤ J` is chosen with `Ũ_ĵ = max_{j ≤ J} Ũ_j`. The lines of the
algorithm (appF:63-77): `d ← r̄` and `d ← d/2` (appF:63, 68) are `loopD`, appF:65 is `loopW`, the
tests of appF:66 and 67 are `Brk` and `WTest`, the loop ends in `LoopBreaks` (or in `LoopZero`, when
the algorithm returns "`W = 0`" in appF:67, `ReturnsZero`), appF:70 is `cLB`, `cᾱ`, `cδ`, appF:71 is
`J = schemeJ (ε/2) ᾱ` and `s = schemeS (ε/2) ᾱ`, appF:73 is `cHat` (the shares of the proof of
`thm:fptas` for the accuracy `ε/2`, see `cHat`), appF:74 is `cH`, `cChk`, `cResp`, and appF:75 is
`cU`. -/
def Returns (ε : ℝ) (w : Option ℝ) (b Ut : ℝ) : Prop :=
  ∃ K, LoopBreaks rb m c orc w K ∧
    ∃ jh ≤ schemeJ (ε / 2) (cᾱ rb (loopW rb m c orc K)),
      (∀ j ≤ schemeJ (ε / 2) (cᾱ rb (loopW rb m c orc K)),
        cU rb m orc ε (loopW rb m c orc K) j ≤ cU rb m orc ε (loopW rb m c orc K) jh) ∧
      b = cChk rb ε (loopW rb m c orc K) jh ∧ Ut = cU rb m orc ε (loopW rb m c orc K) jh

/-- `alg:convex` (appF-convex.tex:67): the algorithm returns "`W = 0`". -/
def ReturnsZero (w : Option ℝ) : Prop := ∃ K, LoopZero rb m c orc w K

variable {rb m c orc}

/-- The loop does not both break and return "`W = 0`" (not in the paper, which takes the run
of `alg:convex` as determined by the oracle). -/
lemma not_loopBreaks_and_loopZero {w : Option ℝ} {K K' : ℕ} (hK : LoopBreaks rb m c orc w K)
    (hK' : LoopZero rb m c orc w K') : False := by
  rcases lt_trichotomy K K' with hlt | heq | hgt
  · exact (hK'.2.2 K hlt).1 hK.1
  · exact hK'.1 (heq ▸ hK.1)
  · exact (hK.2 K' hgt).2 hK'.2.1

/-- The loop returns "`W = 0`" in at most one round (not in the paper, as above). -/
lemma loopZero_unique {w : Option ℝ} {K K' : ℕ} (hK : LoopZero rb m c orc w K)
    (hK' : LoopZero rb m c orc w K') : K = K' := by
  rcases lt_trichotomy K K' with hlt | heq | hgt
  · exact absurd hK.2.1 (hK'.2.2 K hlt).2
  · exact heq
  · exact absurd hK'.2.1 (hK.2.2 K' hgt).2

end Alg

/-! ### (1) The welfare loop -/

section Loop

variable {E : Type*} [Fintype E] {P : Set (E → ℝ)} {m : E → ℝ} {c : (E → ℝ) → ℝ} {rb : ℝ}
  {orc : ℝ → ℝ → (E → ℝ)}

lemma loopD_pos (hrb : 0 < rb) (k : ℕ) : 0 < loopD rb k := by
  unfold loopD
  positivity

lemma loopD_succ (k : ℕ) : loopD rb (k + 1) = loopD rb k / 2 := by
  unfold loopD
  rw [pow_succ]
  field_simp

/-- (1b) of the proof of `prop:convexscheme`: `d_k ≤ W/3` for `k ≥ ⌈log₂(3r̄/W)⌉`, so the least `k`
with `2^{−k} r̄ ≤ W/3` "is at most `⌈log₂(3r̄/W)⌉`" (not in the paper: it asserts this). -/
lemma loopD_le {W : ℝ} (hrb : 0 < rb) (hW : 0 < W) {k : ℕ}
    (hk : ⌈Real.logb 2 (3 * rb / W)⌉₊ ≤ k) : loopD rb k ≤ W / 3 := by
  have hpos : 0 < 3 * rb / W := by positivity
  have h1 : Real.logb 2 (3 * rb / W) ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk)
  have h2 : 3 * rb / W ≤ (2 : ℝ) ^ k := by
    calc 3 * rb / W = (2 : ℝ) ^ Real.logb 2 (3 * rb / W) :=
          (Real.rpow_logb (by norm_num) (by norm_num) hpos).symm
      _ ≤ (2 : ℝ) ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
      _ = 2 ^ k := Real.rpow_natCast 2 k
  unfold loopD
  rw [div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ hW] at h2
  linarith

/-- (1c) of the proof of `prop:convexscheme`, the last precision (not in the paper: "every
precision used, including the last one, is larger than `W/6`" leaves implicit that the last one is
`d_{k₀} = d_{k₀−1}/2 > W/6` if `k₀ ≥ 1`, and `d_0 = r̄ ≥ W` if `k₀ = 0`): if every precision before
round `k₀` is larger than `W/3`, then `d_{k₀} > W/6`. -/
lemma loopD_last {W : ℝ} (hW : 0 < W) (hWrb : W ≤ rb) {k₀ : ℕ}
    (hbefore : ∀ k < k₀, W / 3 < loopD rb k) : W / 6 < loopD rb k₀ := by
  rcases Nat.eq_zero_or_pos k₀ with h0 | hpos
  · rw [h0]
    unfold loopD
    simp only [pow_zero, div_one]
    linarith
  · have := hbefore (k₀ - 1) (by omega)
    have e : loopD rb k₀ = loopD rb (k₀ - 1) / 2 := by
      rw [← loopD_succ]
      congr 1
      omega
    rw [e]
    linarith

variable (h : Setting P m c rb)
  (horc : ∀ α ∈ Icc (0 : ℝ) 1, ∀ δ, 0 < δ → IsDeltaOpt P m c α δ (orc α δ))
include h horc

/-- (1a) of the proof of `prop:convexscheme` (appF-convex.tex:90): "A `d`-optimal response at the
share `1` gives `W − d ≤ W̃ ≤ W`, and the calls have the precisions `d = 2^{−k} r̄` for
`k = 0, 1, …`" (`loopD`; `d > 0` is a precision of the oracle, as `r̄ > 0`). -/
lemma loopW_bounds (k : ℕ) :
    welfare P m c - loopD rb k ≤ loopW rb m c orc k ∧ loopW rb m c orc k ≤ welfare P m c := by
  have hx := horc 1 ⟨zero_le_one, le_rfl⟩ _ (loopD_pos h.rbar_pos k)
  have hW := V_one (P := P) (m := m) (c := c)
  have hu : util m c 1 (orc 1 (loopD rb k)) = loopW rb m c orc k := by
    simp only [util, loopW, one_mul]
  refine ⟨?_, ?_⟩
  · rw [← hW, ← hu]
    exact hx.2
  · rw [← hW, ← hu]
    exact h.util_le_V hx.1

/-- **(1) of the proof of `prop:convexscheme`**, "We first analyze the welfare loop", the case
`W > 0` (appF-convex.tex:90): with or without `w` (given with `w ∈ (0, r̄]` and `W = 0` or `W ≥ w`),
"Let first `W > 0`. We show that the loop ends after at most `⌈log₂(3r̄/W)⌉ + 1` calls, all with
`d > W/6`, that it does not return "`W = 0`", and that then `(2/3)W ≤ W̃ ≤ W`".

(1a) `loopW_bounds`; (1b) "Whenever `d ≤ W/3`, we get `W̃ ≥ W − d ≥ 2d`, so the loop breaks at the
latest at the least `k` with `2^{−k} r̄ ≤ W/3`, and this `k` is at most `⌈log₂(3r̄/W)⌉`"
(`loopD_le`); (1c) "Every earlier precision is larger than `W/3`, so every precision used, including
the last one, is larger than `W/6`" (`loopD_last`); (1d) "If `w` is given, then `W ≥ w`, so at every
`d < w/3` the test `W̃ ≥ 2d`, which comes first, succeeds, and "`W = 0`" is not returned"; (1e)
"When the loop breaks, `W̃ ≥ 2d`, so `W ≤ W̃ + d ≤ (3/2)W̃`". -/
theorem step1_pos (hW : 0 < welfare P m c) {w : Option ℝ}
    (hw : ∀ w₀ ∈ w, w₀ ∈ Ioc 0 rb ∧ (welfare P m c = 0 ∨ w₀ ≤ welfare P m c)) :
    (∃ K, LoopBreaks rb m c orc w K) ∧ (¬ ∃ K, LoopZero rb m c orc w K) ∧
      ∀ K, LoopBreaks rb m c orc w K →
        K + 1 ≤ ⌈Real.logb 2 (3 * rb / welfare P m c)⌉₊ + 1 ∧
        (∀ k ≤ K, welfare P m c / 6 < loopD rb k) ∧
        2 / 3 * welfare P m c ≤ loopW rb m c orc K ∧ loopW rb m c orc K ≤ welfare P m c := by
  classical
  set W := welfare P m c with hWdef
  have hWrb := (welfare_lemma h).2.1
  have hrb := h.rbar_pos
  -- (1a) "A `d`-optimal response at the share `1` gives `W − d ≤ W̃ ≤ W`."
  have h1a := loopW_bounds h horc
  -- (1b) "Whenever `d ≤ W/3`, we get `W̃ ≥ W − d ≥ 2d`"
  have h1b : ∀ k, loopD rb k ≤ W / 3 → Brk rb m c orc k := fun k hk => by
    have := (h1a k).1
    unfold Brk
    linarith
  -- "so the loop breaks at the latest at the least `k` with `2^{−k} r̄ ≤ W/3`, and this `k` is at
  -- most `⌈log₂(3r̄/W)⌉`"
  have hex0 : ∃ k, loopD rb k ≤ W / 3 := ⟨_, loopD_le hrb hW le_rfl⟩
  set k₀ := Nat.find hex0 with hk₀
  have hk₀le : k₀ ≤ ⌈Real.logb 2 (3 * rb / W)⌉₊ :=
    Nat.find_min' hex0 (loopD_le hrb hW le_rfl)
  -- (1c) "Every earlier precision is larger than `W/3`, so every precision used, including the last
  -- one, is larger than `W/6`."
  have h1c : ∀ k < k₀, W / 3 < loopD rb k := fun k hk => not_le.1 (Nat.find_min hex0 hk)
  have hlast : W / 6 < loopD rb k₀ := loopD_last hW hWrb h1c
  -- (1d) "If `w` is given, then `W ≥ w`, so at every `d < w/3` the test `W̃ ≥ 2d`, which comes
  -- first, succeeds, and "`W = 0`" is not returned."
  have h1d : ∀ k, WTest rb w k → Brk rb m c orc k := by
    rintro k ⟨w₀, hw₀, hlt⟩
    obtain ⟨-, hW0 | hww⟩ := hw w₀ hw₀
    · exact absurd hW0 hW.ne'
    · exact h1b k (by linarith)
  -- the loop breaks at the least `K` with `W̃_K ≥ 2 d_K`, which is at most `k₀`
  have hexK : ∃ k, Brk rb m c orc k := ⟨k₀, h1b k₀ (Nat.find_spec hex0)⟩
  have hKmin : ∀ K, LoopBreaks rb m c orc w K → K ≤ k₀ := fun K hK => by
    by_contra hlt
    exact (hK.2 k₀ (not_le.1 hlt)).1 (h1b k₀ (Nat.find_spec hex0))
  refine ⟨⟨Nat.find hexK, Nat.find_spec hexK, fun k hk =>
      ⟨Nat.find_min hexK hk, fun ht => Nat.find_min hexK hk (h1d k ht)⟩⟩,
    fun ⟨K, hK⟩ => hK.1 (h1d K hK.2.1), fun K hK => ⟨?_, fun k hk => ?_, ?_, (h1a K).2⟩⟩
  · -- the count: `K + 1 ≤ k₀ + 1 ≤ ⌈log₂(3r̄/W)⌉ + 1`
    have := hKmin K hK
    omega
  · -- every precision used is larger than `W/6`
    have hkk₀ : k ≤ k₀ := hk.trans (hKmin K hK)
    rcases hkk₀.lt_or_eq with hlt | rfl
    · linarith [h1c k hlt]
    · exact hlast
  · -- (1e) "When the loop breaks, `W̃ ≥ 2d`, so `W ≤ W̃ + d ≤ (3/2)W̃`."
    have hbrk := hK.1
    have := (h1a K).1
    unfold Brk at hbrk
    linarith

/-- **(1) of the proof of `prop:convexscheme`**, the case `W = 0` (appF-convex.tex:90): "Let now
`W = 0`. Then `W̃ ≤ 0 < 2d` in every round, so the loop does not end without `w`"
(`d = 2^{−k} r̄ > 0`, as `r̄ > 0`). "With `w`, it returns "`W = 0`" at the least `k` with
`2^{−k} r̄ < w/3`, which is `⌊log₂(3r̄/w)⌋ + 1 ≥ 1` as `w ≤ r̄`, and `2^{−k} r̄ ≥ w/6` by the
minimality of `k`. This proves the claims on the loop." -/
theorem step1_zero (hW : welfare P m c = 0) :
    (∀ k, ¬ Brk rb m c orc k) ∧
      ∀ w ∈ Ioc 0 rb, ∃ K, LoopZero rb m c orc (some w) K ∧
        K = ⌊Real.logb 2 (3 * rb / w)⌋₊ + 1 ∧ ∀ k ≤ K, w / 6 ≤ loopD rb k := by
  have hrb := h.rbar_pos
  -- "Then `W̃ ≤ 0 < 2d` in every round, so the loop does not end without `w`."
  have hno : ∀ k, ¬ Brk rb m c orc k := fun k hk => by
    have h1 := (loopW_bounds h horc k).2
    have h2 := loopD_pos hrb k
    unfold Brk at hk
    rw [hW] at h1
    linarith
  refine ⟨hno, fun w hw => ?_⟩
  set L := Real.logb 2 (3 * rb / w)
  have hpos : 0 < 3 * rb / w := by have := hw.1; positivity
  have hL0 : 0 ≤ L := Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ hw.1]; linarith [hw.2])
  -- "it returns "`W = 0`" at the least `k` with `2^{−k} r̄ < w/3`": `d_k < w/3` if and only if
  -- `log₂(3r̄/w) < k`
  have key : ∀ k : ℕ, (loopD rb k < w / 3 ↔ L < k) := by
    intro k
    unfold loopD
    rw [div_lt_iff₀ (by positivity), show w / 3 * 2 ^ k = 2 ^ k * w / 3 by ring,
      lt_div_iff₀ (by norm_num : (0 : ℝ) < 3), ← div_lt_iff₀ hw.1,
      show rb * 3 / w = 3 * rb / w by ring]
    constructor
    · intro h'
      have := Real.logb_lt_logb (b := 2) (by norm_num) hpos
        (show 3 * rb / w < (2 : ℝ) ^ (k : ℝ) by rwa [Real.rpow_natCast])
      rwa [Real.logb_rpow (by norm_num) (by norm_num)] at this
    · intro h'
      have := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) h'
      rwa [Real.rpow_logb (by norm_num) (by norm_num) hpos, Real.rpow_natCast] at this
  -- "which is `⌊log₂(3r̄/w)⌋ + 1 ≥ 1` as `w ≤ r̄`"
  have hstop : loopD rb (⌊L⌋₊ + 1) < w / 3 :=
    (key _).2 (by push_cast; exact Nat.lt_floor_add_one L)
  have hbefore : ∀ k < ⌊L⌋₊ + 1, w / 3 ≤ loopD rb k := fun k hk => by
    by_contra hlt
    have := (key k).1 (not_le.1 hlt)
    have : (k : ℝ) ≤ ⌊L⌋₊ := by exact_mod_cast Nat.lt_succ_iff.1 hk
    linarith [Nat.floor_le hL0]
  refine ⟨⌊L⌋₊ + 1, ⟨hno _, ⟨w, rfl, hstop⟩, fun k hk => ⟨hno k, ?_⟩⟩, rfl, fun k hk => ?_⟩
  · rintro ⟨w₀, hw₀, hlt⟩
    cases hw₀
    exact absurd hlt (not_lt.2 (hbefore k hk))
  · -- "and `2^{−k} r̄ ≥ w/6` by the minimality of `k`"
    rcases hk.lt_or_eq with hk | rfl
    · linarith [hbefore k hk, hw.1]
    · rw [loopD_succ]
      linarith [hbefore ⌊L⌋₊ (Nat.lt_succ_self _)]

end Loop

/-! ### (2) to (4): the share bound, the valid bounds and a large bound -/

section Bounds

variable {E : Type*} [Fintype E] {P : Set (E → ℝ)} {m : E → ℝ} {c : (E → ℝ) → ℝ} {rb : ℝ}
  {orc : ℝ → ℝ → (E → ℝ)}

/-- **(2) of the proof of `prop:convexscheme`** (appF-convex.tex:92-96): let `W > 0` and let `W̃`
be the estimate with which the loop breaks, `(2/3) W ≤ W̃ ≤ W` (by (1)). "Next we show that
`LB < OPT`, so that `ᾱ` is a share bound, and we bound `δ` and `J`": `LB < OPT`; `ᾱ` is a share
bound; `δ ≥ ε² W/(192 ⌈log₂(3r̄/W)⌉)`; `1/(1 − ᾱ) ≤ (3r̄/W)²`; `J + 1 ≤ ⌈8ε⁻¹ ln(3r̄/W)⌉ + 1`.

(2a) `2r̄/W̃ ≥ 2`, so `⌈log₂(2r̄/W̃)⌉ ≥ log₂(2r̄/W̃) > ln(2r̄/W̃)` (`log_lt_logb`); (2b) the
function `u ↦ u/(2 ln(2r̄/u))` is increasing on `(0, r̄]` (`div_log_mono`), so with `lem:welfare`,
`LB < W̃/(2 ln(2r̄/W̃)) ≤ W/(2 ln(2r̄/W)) ≤ OPT`; (2c) `0 < ᾱ < 1`, and for `α ∈ (ᾱ, 1]`,
`U_P(α) ≤ (1 − α) r̄ ≤ (1 − ᾱ) r̄ = LB < OPT`, hence `sup_{α ∈ [0, ᾱ]} U_P(α) = OPT`; (2d) "As
`W̃ ≥ (2/3)W` by the analysis of the loop, `2r̄/W̃ ≤ 3r̄/W`, so `LB ≥ W/(3⌈log₂(3r̄/W)⌉)`, which
gives the bound on `δ = ε² LB/64`"; (2e) `⌈log₂ z⌉ ≤ z` for `z ≥ 1` (`ceil_logb_le`), so
`1/(1 − ᾱ) = r̄/LB = (2r̄/W̃)⌈log₂(2r̄/W̃)⌉ ≤ (3r̄/W)²`; (2f) by `thm:fptas` with the accuracy
`ε/2`, `J + 1 ≤ ⌈4ε⁻¹ ln(1/(1 − ᾱ))⌉ + 1 ≤ ⌈8ε⁻¹ ln(3r̄/W)⌉ + 1`: the count
`J + 1 ≤ ⌈2ε'⁻¹ ln(1/(1 − ᾱ))⌉ + 1` for `ε' = ε/2` of the shares constructed in the proof of
`thm:fptas` (`fptas_aux`). -/
theorem step2 (h : Setting P m c rb) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1)
    (hW : 0 < welfare P m c) {Wt : ℝ} (hWt1 : 2 / 3 * welfare P m c ≤ Wt)
    (hWt2 : Wt ≤ welfare P m c) :
    cLB rb Wt < OPT (profit P m c) ∧ IsShareBound (profit P m c) (cᾱ rb Wt) ∧
      ε ^ 2 * welfare P m c / (192 * ⌈Real.logb 2 (3 * rb / welfare P m c)⌉₊) ≤
        cδ rb ε Wt ∧
      1 / (1 - cᾱ rb Wt) ≤ (3 * rb / welfare P m c) ^ 2 ∧
      schemeJ (ε / 2) (cᾱ rb Wt) + 1 ≤
        ⌈8 / ε * Real.log (3 * rb / welfare P m c)⌉₊ + 1 := by
  set W := welfare P m c with hWdef
  obtain ⟨hOPTW, hWrb, hwel⟩ := welfare_lemma h
  have hWt : 0 < Wt := by linarith
  have hrb : 0 < rb := hW.trans_le hWrb
  have hε0 := hε.1
  have hε1 := hε.2
  -- (2a) "As `0 < W̃ ≤ W ≤ r̄`, we have `2r̄/W̃ ≥ 2`, so
  -- `⌈log₂(2r̄/W̃)⌉ ≥ log₂(2r̄/W̃) > ln(2r̄/W̃)`."
  have h2 : 2 ≤ 2 * rb / Wt := by rw [le_div_iff₀ hWt]; linarith
  have hlog : 0 < Real.log (2 * rb / Wt) := Real.log_pos (by linarith)
  have h2a : Real.log (2 * rb / Wt) < ⌈Real.logb 2 (2 * rb / Wt)⌉₊ :=
    (log_lt_logb (by linarith)).trans_le (Nat.le_ceil _)
  have hceil0 : (0 : ℝ) < ⌈Real.logb 2 (2 * rb / Wt)⌉₊ := hlog.trans h2a
  -- (2b) "The function `u ↦ u/(2 ln(2r̄/u))` is increasing on `(0, r̄]`. With `W̃ ≤ W` and
  -- `lem:welfare`, `LB < W̃/(2 ln(2r̄/W̃)) ≤ W/(2 ln(2r̄/W)) ≤ OPT`."
  have hLB : cLB rb Wt < OPT (profit P m c) :=
    calc cLB rb Wt < Wt / (2 * Real.log (2 * rb / Wt)) := by
          unfold cLB
          exact div_lt_div_of_pos_left hWt (by positivity) (by linarith)
      _ ≤ W / (2 * Real.log (2 * rb / W)) := div_log_mono hWt hWt2 hWrb
      _ ≤ OPT (profit P m c) := hwel hW
  -- (2c) "So `0 < ᾱ < 1`,"
  have hLB0 : 0 < cLB rb Wt := by unfold cLB; positivity
  have hᾱ0 : 0 < cᾱ rb Wt := by
    unfold cᾱ
    rw [sub_pos, div_lt_one hrb]
    linarith
  have hᾱ1 : cᾱ rb Wt < 1 := by
    unfold cᾱ
    have := div_pos hLB0 hrb
    linarith
  have hᾱrb : (1 - cᾱ rb Wt) * rb = cLB rb Wt := by
    unfold cᾱ
    field_simp
    ring
  -- "and for `α ∈ (ᾱ, 1]` we have `U_P(α) ≤ (1 − α) r̄ ≤ (1 − ᾱ) r̄ = LB < OPT`."
  have hright : ∀ α ∈ Icc (0 : ℝ) 1, cᾱ rb Wt < α → profit P m c α ≤ cLB rb Wt := by
    intro α hα hlt
    calc profit P m c α = (1 - α) * S P m c α := rfl
      _ ≤ (1 - α) * rb := mul_le_mul_of_nonneg_left (h.S_le_rbar α) (by linarith [hα.2])
      _ ≤ (1 - cᾱ rb Wt) * rb := mul_le_mul_of_nonneg_right (by linarith) hrb.le
      _ = cLB rb Wt := hᾱrb
  -- "Hence `sup_{α ∈ [0, ᾱ]} U_P(α) = OPT`, and `ᾱ` is a share bound."
  have hsub : Icc (0 : ℝ) (cᾱ rb Wt) ⊆ Icc 0 1 := Icc_subset_Icc le_rfl hᾱ1.le
  have hbdd : BddAbove (profit P m c '' Icc 0 (cᾱ rb Wt)) :=
    h.bddAbove_profit.mono (image_mono hsub)
  have hne : (profit P m c '' Icc 0 (cᾱ rb Wt)).Nonempty :=
    ⟨_, mem_image_of_mem _ (show (0 : ℝ) ∈ Icc (0 : ℝ) (cᾱ rb Wt) from ⟨le_rfl, hᾱ0.le⟩)⟩
  have hsb : IsShareBound (profit P m c) (cᾱ rb Wt) := by
    refine ⟨hᾱ0.le, hᾱ1, le_antisymm (csSup_le_csSup h.bddAbove_profit hne (image_mono hsub)) ?_⟩
    have hmax : OPT (profit P m c) ≤
        max (sSup (profit P m c '' Icc 0 (cᾱ rb Wt))) (cLB rb Wt) := by
      refine csSup_le ⟨_, mem_image_of_mem _ (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from
        ⟨le_rfl, zero_le_one⟩)⟩ ?_
      rintro _ ⟨α, hα, rfl⟩
      rcases le_or_gt α (cᾱ rb Wt) with hle | hlt
      · exact le_max_of_le_left (le_csSup hbdd (mem_image_of_mem _ ⟨hα.1, hle⟩))
      · exact le_max_of_le_right (hright α hα hlt)
    rcases le_total (sSup (profit P m c '' Icc 0 (cᾱ rb Wt))) (cLB rb Wt) with hle | hle
    · rw [max_eq_right hle] at hmax
      linarith
    · rwa [max_eq_left hle] at hmax
  -- (2d) "As `W̃ ≥ (2/3)W` by the analysis of the loop, `2r̄/W̃ ≤ 3r̄/W`, so
  -- `LB ≥ W/(3⌈log₂(3r̄/W)⌉)`, which gives the bound on `δ = ε² LB/64`."
  have hz : 2 * rb / Wt ≤ 3 * rb / W := by
    rw [div_le_div_iff₀ hWt hW]
    nlinarith
  have hceil : (⌈Real.logb 2 (2 * rb / Wt)⌉₊ : ℝ) ≤ ⌈Real.logb 2 (3 * rb / W)⌉₊ := by
    exact_mod_cast Nat.ceil_mono (Real.logb_le_logb_of_le (by norm_num) (by positivity) hz)
  have hLBge : W / (3 * ⌈Real.logb 2 (3 * rb / W)⌉₊) ≤ cLB rb Wt := by
    unfold cLB
    rw [div_le_div_iff₀ (mul_pos (by norm_num) (hceil0.trans_le hceil))
      (mul_pos (by norm_num) hceil0)]
    nlinarith
  have hδ : ε ^ 2 * W / (192 * ⌈Real.logb 2 (3 * rb / W)⌉₊) ≤ cδ rb ε Wt := by
    have e : ε ^ 2 * W / (192 * ⌈Real.logb 2 (3 * rb / W)⌉₊) =
        ε ^ 2 * (W / (3 * ⌈Real.logb 2 (3 * rb / W)⌉₊)) / 64 := by
      rw [mul_div_assoc', div_div]
      ring_nf
    rw [e]
    unfold cδ
    gcongr
  -- (2e) "Moreover `⌈log₂ z⌉ ≤ z` for `z ≥ 1`, so
  -- `1/(1 − ᾱ) = r̄/LB = (2r̄/W̃)⌈log₂(2r̄/W̃)⌉ ≤ (3r̄/W)²`."
  have hinv : 1 / (1 - cᾱ rb Wt) ≤ (3 * rb / W) ^ 2 := by
    have e : 1 / (1 - cᾱ rb Wt) = 2 * rb / Wt * ⌈Real.logb 2 (2 * rb / Wt)⌉₊ := by
      have h1 := hWt.ne'
      have h2 := hrb.ne'
      have h3 := hceil0.ne'
      unfold cᾱ cLB
      rw [sub_sub_cancel]
      field_simp
    have hc := ceil_logb_le (show 1 ≤ 2 * rb / Wt by linarith)
    rw [e, sq]
    calc 2 * rb / Wt * ⌈Real.logb 2 (2 * rb / Wt)⌉₊ ≤
          3 * rb / W * ⌈Real.logb 2 (2 * rb / Wt)⌉₊ :=
          mul_le_mul_of_nonneg_right hz hceil0.le
      _ ≤ 3 * rb / W * (3 * rb / W) :=
          mul_le_mul_of_nonneg_left (hc.trans hz) (by positivity)
  -- (2f) "By `thm:fptas` with the accuracy `ε/2`, the number of shares is
  -- `J + 1 ≤ ⌈4ε⁻¹ ln(1/(1 − ᾱ))⌉ + 1 ≤ ⌈8ε⁻¹ ln(3r̄/W)⌉ + 1`." The count of the shares
  -- constructed in the proof of `thm:fptas` (`fptas_aux`).
  have hε2 : ε / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  obtain ⟨hcount, -, -, -⟩ := fptas_aux hε2 ⟨hsb.1, hsb.2.1⟩
  refine ⟨hLB, hsb, hδ, hinv, hcount.trans (Nat.add_le_add_right (Nat.ceil_mono ?_) 1)⟩
  have hlog1 : Real.log (1 / (1 - cᾱ rb Wt)) ≤ 2 * Real.log (3 * rb / W) := by
    rw [← Real.log_rpow (by positivity) 2]
    apply Real.log_le_log (one_div_pos.2 (sub_pos.2 hᾱ1))
    rw [show (3 * rb / W) ^ (2 : ℝ) = (3 * rb / W) ^ 2 by norm_cast]
    exact hinv
  calc 2 / (ε / 2) * Real.log (1 / (1 - cᾱ rb Wt)) =
        4 / ε * Real.log (1 / (1 - cᾱ rb Wt)) := by
        field_simp
        ring
    _ ≤ 4 / ε * (2 * Real.log (3 * rb / W)) := mul_le_mul_of_nonneg_left hlog1 (by positivity)
    _ = 8 / ε * Real.log (3 * rb / W) := by ring

/-- **(3) of the proof of `prop:convexscheme`**, (3a)–(3c) (appF-convex.tex:98): for `0 ≤ ᾱ < 1`
and every `j ≤ J`, `1 − α̂_j > 0`. (3a) "With `ε/2` in place of `ε`, the grid in the proof of
`thm:fptas` uses `(1 − ε/4)^j` and `2^{−s} ≤ ε(1 − ᾱ)/8`"; (3b) "If `J ≥ 1`, the minimality of `J`
gives `(1 − ε/4)^{J−1} > 1 − ᾱ`, so `(1 − ε/4)^J > (3/4)(1 − ᾱ) > 2^{−s}`, and if `J = 0`, then
`(1 − ε/4)^J = 1 > 2^{−s}`"; (3c) "So
`1 − α̂_j = 2^{−s}⌊2^s(1 − ε/4)^j⌋ > (1 − ε/4)^j − 2^{−s} ≥ (1 − ε/4)^J − 2^{−s} > 0` for every
`j ≤ J`". -/
lemma one_sub_cHat_pos {ε Wt : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) (hᾱ0 : 0 ≤ cᾱ rb Wt)
    (hᾱ1 : cᾱ rb Wt < 1) {j : ℕ} (hj : j ≤ schemeJ (ε / 2) (cᾱ rb Wt)) :
    0 < 1 - cHat rb ε Wt j := by
  set ᾱ := cᾱ rb Wt with hᾱdef
  set J := schemeJ (ε / 2) ᾱ with hJdef
  set s := schemeS (ε / 2) ᾱ with hsdef
  have hε0 := hε.1
  have hε1 := hε.2
  have hε2 : ε / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hᾱ' : 0 < 1 - ᾱ := sub_pos.2 hᾱ1
  -- (3a) "With `ε/2` in place of `ε`, the grid in the proof of `thm:fptas` uses `(1 − ε/4)^j` and
  -- `2^{−s} ≤ ε(1 − ᾱ)/8`": `ε' = (ε/2)/2`, and the bound `2^{−s} ≤ ε(1 − ᾱ)/4` of step (6) of
  -- its proof (`one_div_two_pow_schemeS_le`), with `ε/2` in place of `ε`.
  have hq : 1 - ε / 2 / 2 = 1 - ε / 4 := by ring
  have h2s : 1 / (2 : ℝ) ^ s ≤ ε * (1 - ᾱ) / 8 := by
    have := one_div_two_pow_schemeS_le hε2 hᾱ1
    rw [← hsdef] at this
    linarith
  -- (3b) "If `J ≥ 1`, the minimality of `J` gives `(1 − ε/4)^{J−1} > 1 − ᾱ`, so
  -- `(1 − ε/4)^J > (3/4)(1 − ᾱ) > 2^{−s}`, and if `J = 0`, then `(1 − ε/4)^J = 1 > 2^{−s}`."
  have h3b : 1 / (2 : ℝ) ^ s < (1 - ε / 4) ^ J := by
    rcases Nat.eq_zero_or_pos J with h0 | hpos
    · rw [h0, pow_zero]
      have : ε * (1 - ᾱ) < 8 := by nlinarith
      linarith
    · have hlt := lt_of_lt_schemeJ (ε := ε / 2) (ᾱ := ᾱ) (show J - 1 < J by omega)
      rw [hq] at hlt
      have e : (1 - ε / 4) ^ J = (1 - ε / 4) * (1 - ε / 4) ^ (J - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have h34 : 3 / 4 * (1 - ᾱ) < (1 - ε / 4) ^ J := by
        rw [e]
        have : (3 : ℝ) / 4 ≤ 1 - ε / 4 := by linarith
        nlinarith
      have : ε * (1 - ᾱ) / 8 < 3 / 4 * (1 - ᾱ) := by nlinarith
      linarith
  -- (3c) "So `1 − α̂_j = 2^{−s}⌊2^s(1 − ε/4)^j⌋ > (1 − ε/4)^j − 2^{−s} ≥ (1 − ε/4)^J − 2^{−s} > 0`
  -- for every `j ≤ J`."
  have hgt := schemeB_gt (ε := ε / 2) (ᾱ := ᾱ) j
  rw [hq] at hgt
  have hpow : (1 - ε / 4) ^ J ≤ (1 - ε / 4) ^ j :=
    pow_le_pow_of_le_one (by linarith) (by linarith) hj
  have e1 : 1 - cHat rb ε Wt j = schemeB (ε / 2) ᾱ j := by
    unfold cHat schemeShare
    ring
  rw [e1]
  linarith

/-- **(3) of the proof of `prop:convexscheme`** (appF-convex.tex:98), "Next we show that every
`Ũ_j` is a valid bound, that is, `α̌_j ∈ (0, 1)` and `(1 − α̌_j) r(y) ≥ Ũ_j` for every
`y ∈ X*(α̌_j)`": for `W > 0`, the estimate `W̃` of (1) and every `j ≤ J`.

(3a)–(3c) `1 − α̂_j > 0` (`one_sub_cHat_pos`, with `0 ≤ ᾱ < 1` from (2)); (3d) "Hence `h_j > 0`
and `1 − α̌_j = (1 − ε/4)(1 − α̂_j) ∈ (0, 1)`"; (3e) "Let `y ∈ X*(α̌_j)`. The right-hand inequality
of `lem:shift` with `α = α̂_j + h_j` and `α' = α̌_j` gives `r(y) ≥ r(x̃_j) − δ/h_j`, so
`(1 − α̌_j) r(y) ≥ Ũ_j`" (`lem:shift` is applied with `α'' = α̂_j`, which its right-hand inequality
does not involve). -/
theorem step3 (h : Setting P m c rb)
    (horc : ∀ α ∈ Icc (0 : ℝ) 1, ∀ δ, 0 < δ → IsDeltaOpt P m c α δ (orc α δ)) {ε : ℝ}
    (hε : ε ∈ Ioo (0 : ℝ) 1) (hW : 0 < welfare P m c) {Wt : ℝ}
    (hWt1 : 2 / 3 * welfare P m c ≤ Wt) (hWt2 : Wt ≤ welfare P m c) {j : ℕ}
    (hj : j ≤ schemeJ (ε / 2) (cᾱ rb Wt)) :
    cChk rb ε Wt j ∈ Ioo (0 : ℝ) 1 ∧ ∀ y ∈ bestResponses P m c (cChk rb ε Wt j),
      cU rb m orc ε Wt j ≤ (1 - cChk rb ε Wt j) * reward m y := by
  obtain ⟨-, ⟨hᾱ0, hᾱ1, -⟩, -⟩ := step2 h hε hW hWt1 hWt2
  have hε0 := hε.1
  have hε1 := hε.2
  have hrb := h.rbar_pos
  -- (3a)–(3c)
  have hpos := one_sub_cHat_pos hε hᾱ0 hᾱ1 hj
  have hmem := schemeShare_mem (ᾱ := cᾱ rb Wt)
    (show ε / 2 ∈ Ioo (0 : ℝ) 1 from ⟨by linarith, by linarith⟩) j
  set a := cHat rb ε Wt j with ha
  have ha0 : 0 ≤ a := hmem.1
  have hH : cH rb ε Wt j = ε / 8 * (1 - a) := rfl
  have hC : cChk rb ε Wt j = a + 2 * cH rb ε Wt j := rfl
  -- (3d) "Hence `h_j > 0` and `1 − α̌_j = (1 − ε/4)(1 − α̂_j) ∈ (0, 1)`."
  have hHpos : 0 < cH rb ε Wt j := by rw [hH]; positivity
  have hchk : 1 - cChk rb ε Wt j = (1 - ε / 4) * (1 - a) := by rw [hC, hH]; ring
  have hchk0 : 0 < 1 - cChk rb ε Wt j := by
    rw [hchk]
    exact mul_pos (by linarith) hpos
  have hchk1 : 1 - cChk rb ε Wt j < 1 := by
    rw [hchk]
    nlinarith
  refine ⟨⟨by linarith, by linarith⟩, fun y hy => ?_⟩
  -- (3e) "Let `y ∈ X*(α̌_j)`. The right-hand inequality of `lem:shift` with `α = α̂_j + h_j` and
  -- `α' = α̌_j` gives `r(y) ≥ r(x̃_j) − δ/h_j`, so `(1 − α̌_j) r(y) ≥ Ũ_j`."
  have hLB0 : 0 < cLB rb Wt := by
    have h1 : 0 < cLB rb Wt / rb := by unfold cᾱ at hᾱ1; linarith
    exact (div_pos_iff_of_pos_right hrb).1 h1
  have hδ : 0 < cδ rb ε Wt := by unfold cδ; positivity
  have hx : IsDeltaOpt P m c (a + cH rb ε Wt j) (cδ rb ε Wt) (cResp rb orc ε Wt j) :=
    horc _ ⟨by linarith, by rw [hH]; nlinarith⟩ _ hδ
  have hsh := (shift h ha0 (by linarith : a < a + cH rb ε Wt j)
    (by rw [hC]; linarith : a + cH rb ε Wt j < cChk rb ε Wt j) hδ.le hx).2 y hy
  have e : cChk rb ε Wt j - (a + cH rb ε Wt j) = cH rb ε Wt j := by rw [hC]; ring
  rw [e] at hsh
  unfold cU
  exact mul_le_mul_of_nonneg_left (by linarith) hchk0.le

/-- **(4) of the proof of `prop:convexscheme`** (appF-convex.tex:100-107), "Finally, we show that
some `Ũ_j` is large, namely `Ũ_j ≥ (1 − ε) OPT` for some `j`": for `W > 0` and the estimate `W̃`
of (1), some `j ≤ J` has `Ũ_j ≥ (1 − ε) OPT`.

(4a) "The proof of `thm:fptas` uses only `lem:monreward`, which holds for all maximizers, so the
theorem applies to the best responses `x*(α)` and the share bound `ᾱ` shown above. It gives a
`j ≤ J` with `U_P(α̂_j) ≥ (1 − ε/2) OPT`" (`fptas_aux`, `thm:fptas` for the shares constructed in
its proof and any reward curve that satisfies the conclusion of `lem:monreward`, applied to the
reward `r(x*(α))` of the best responses `x*(α)` of the largest reward, which is nondecreasing by
`lem:monreward`, `Setting.monotoneOn_S`); (4b) "The left-hand inequality of `lem:shift` with
`α'' = α̂_j`, `α = α̂_j + h_j`, and `y'' = x*(α̂_j)` gives `r(x̃_j) ≥ r(x*(α̂_j)) − δ/h_j`" (with
`α' = α̌_j`, which its left-hand inequality does not involve); (4c) "As
`1 − α̌_j = (1 − ε/4)(1 − α̂_j)`, `h_j = (ε/8)(1 − α̂_j)`, and `δ = ε² LB/64`,
`Ũ_j ≥ (1 − α̌_j)(r(x*(α̂_j)) − 2δ/h_j) = (1 − ε/4)(U_P(α̂_j) − ε LB/4)`
`≥ (1 − ε/4)(1 − ε/2) OPT − (ε/4) OPT ≥ (1 − ε) OPT`, using `LB < OPT`" (from (2)). -/
theorem step4 (h : Setting P m c rb)
    (horc : ∀ α ∈ Icc (0 : ℝ) 1, ∀ δ, 0 < δ → IsDeltaOpt P m c α δ (orc α δ)) {ε : ℝ}
    (hε : ε ∈ Ioo (0 : ℝ) 1) (hW : 0 < welfare P m c) {Wt : ℝ}
    (hWt1 : 2 / 3 * welfare P m c ≤ Wt) (hWt2 : Wt ≤ welfare P m c) :
    ∃ j ≤ schemeJ (ε / 2) (cᾱ rb Wt), (1 - ε) * OPT (profit P m c) ≤ cU rb m orc ε Wt j := by
  obtain ⟨hLB, hsb, -⟩ := step2 h hε hW hWt1 hWt2
  have hε0 := hε.1
  have hε1 := hε.2
  have hε2 : ε / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hrb := h.rbar_pos
  -- (4a) "The proof of `thm:fptas` uses only `lem:monreward`, which holds for all maximizers, so
  -- the theorem applies to the best responses `x*(α)` and the share bound `ᾱ` shown above. It
  -- gives a `j ≤ J` with `U_P(α̂_j) ≥ (1 − ε/2) OPT`."
  obtain ⟨-, -, -, hguar⟩ := fptas_aux hε2 ⟨hsb.1, hsb.2.1⟩
  obtain ⟨⟨j, hj, hmax⟩, -⟩ := hguar (S P m c) h.monotoneOn_S (fun α _ => h.S_nonneg α) hsb
  change (1 - ε / 2) * OPT (profit P m c) ≤ profit P m c (schemeShare (ε / 2) (cᾱ rb Wt) j)
    at hmax
  refine ⟨j, hj, ?_⟩
  -- the facts of (3) for this `j`: `1 − α̂_j > 0`, `h_j > 0`, `1 − α̌_j = (1 − ε/4)(1 − α̂_j)`
  have hpos := one_sub_cHat_pos hε hsb.1 hsb.2.1 hj
  have hmem := schemeShare_mem (ᾱ := cᾱ rb Wt) hε2 j
  set a := cHat rb ε Wt j with ha
  have ha0 : 0 ≤ a := hmem.1
  have hH : cH rb ε Wt j = ε / 8 * (1 - a) := rfl
  have hC : cChk rb ε Wt j = a + 2 * cH rb ε Wt j := rfl
  have hHpos : 0 < cH rb ε Wt j := by rw [hH]; positivity
  have hchk : 1 - cChk rb ε Wt j = (1 - ε / 4) * (1 - a) := by rw [hC, hH]; ring
  have hLB0 : 0 < cLB rb Wt := by
    have h1 : 0 < cLB rb Wt / rb := by have := hsb.2.1; unfold cᾱ at this; linarith
    exact (div_pos_iff_of_pos_right hrb).1 h1
  have hδ : 0 < cδ rb ε Wt := by unfold cδ; positivity
  have hx : IsDeltaOpt P m c (a + cH rb ε Wt j) (cδ rb ε Wt) (cResp rb orc ε Wt j) :=
    horc _ ⟨by linarith, by rw [hH]; nlinarith⟩ _ hδ
  -- (4b) "The left-hand inequality of `lem:shift` with `α'' = α̂_j`, `α = α̂_j + h_j`, and
  -- `y'' = x*(α̂_j)` gives `r(x̃_j) ≥ r(x*(α̂_j)) − δ/h_j`."
  obtain ⟨y, hy, hyS⟩ := h.exists_favourable a
  have hsh := (shift h ha0 (by linarith : a < a + cH rb ε Wt j)
    (by rw [hC]; linarith : a + cH rb ε Wt j < cChk rb ε Wt j) hδ.le hx).1 y hy
  rw [add_sub_cancel_left, hyS] at hsh
  -- (4c) "As `1 − α̌_j = (1 − ε/4)(1 − α̂_j)`, `h_j = (ε/8)(1 − α̂_j)`, and `δ = ε² LB/64`,
  -- `Ũ_j ≥ (1 − α̌_j)(r(x*(α̂_j)) − 2δ/h_j) = (1 − ε/4)(U_P(α̂_j) − ε LB/4)
  -- ≥ (1 − ε/4)(1 − ε/2) OPT − (ε/4) OPT ≥ (1 − ε) OPT`, using `LB < OPT`" (from (2)).
  have hOPT0 : 0 ≤ OPT (profit P m c) := h.OPT_nonneg
  have hprofa : profit P m c a = (1 - a) * S P m c a := rfl
  calc (1 - ε) * OPT (profit P m c)
      ≤ (1 - ε / 4) * (1 - ε / 2) * OPT (profit P m c) - ε / 4 * OPT (profit P m c) := by
        nlinarith [sq_nonneg ε]
    _ ≤ (1 - ε / 4) * (profit P m c a - ε * cLB rb Wt / 4) := by
        have k1 : (1 - ε / 4) * (1 - ε / 2) * OPT (profit P m c) ≤
            (1 - ε / 4) * profit P m c a := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hmax (by linarith)
        have k2 : (1 - ε / 4) * (ε * cLB rb Wt / 4) ≤ ε / 4 * OPT (profit P m c) := by
          have : ε * cLB rb Wt / 4 ≤ ε / 4 * OPT (profit P m c) := by nlinarith
          have hX : 0 ≤ ε * cLB rb Wt / 4 := by positivity
          nlinarith [mul_nonneg hε0.le hX]
        nlinarith
    _ = (1 - cChk rb ε Wt j) * (S P m c a - 2 * (cδ rb ε Wt / cH rb ε Wt j)) := by
        rw [hchk, hprofa, hH]
        unfold cδ
        have h1a : 1 - a ≠ 0 := hpos.ne'
        field_simp
        ring
    _ ≤ cU rb m orc ε Wt j := by
        unfold cU
        exact mul_le_mul_of_nonneg_left (by linarith)
          (by rw [hchk]; exact mul_nonneg (by linarith) hpos.le)

end Bounds

/-! ### `prop:convexscheme` -/

section Main

variable {E : Type*} [Fintype E] {P : Set (E → ℝ)} {m : E → ℝ} {c : (E → ℝ) → ℝ} {rb : ℝ}
  {orc : ℝ → ℝ → (E → ℝ)}

/-- **`prop:convexscheme`** (Proposition D.7, appF-convex.tex:81-87, proof 89-108): "Under the
assumptions on `K`, `c`, `r`, and the response oracle at the start of `app:convex`" (`Setting`,
appF-convex.tex:9, with the action set `P`; an oracle for `δ`-optimal responses), let
`ε ∈ (0, 1)`.
(a) If `W > 0`, then `alg:convex`, with or without `w` (`w = some w₀` with `w₀ ∈ (0, r̄]` and
`W = 0` or `W ≥ w₀`, or `w = none`), returns a share `b ∈ (0, 1)` and a number `Ũ` (`Ut`; and not
"`W = 0`") with `(1 − b) r(y) ≥ Ũ ≥ (1 − ε) OPT` for every `y ∈ X*(b)`. It calls the oracle at
most `⌈log₂(3r̄/W)⌉ + 1` times at the share `1` (the rounds `k = 0, …, K` of the loop), with
precisions `d > W/6`, and at most `⌈8ε⁻¹ ln(3r̄/W)⌉ + 1` times (`j = 0, …, J`) with the precision
`δ ≥ ε² W/(192 ⌈log₂(3r̄/W)⌉)`.
(b) If `W = 0`, the loop does not end without `w`, and with `w ∈ (0, r̄]` the algorithm returns
"`W = 0`" after at most `⌊log₂(3r̄/w)⌋ + 2` calls (the rounds `k = 0, …, K`), all with precisions
`d ≥ w/6`.

The proof has four paragraphs, which we number (1) to (4): (1) "We first analyze the welfare
loop" (`step1_pos`, `step1_zero`), (2) "Next we show that `LB < OPT`, so that `ᾱ` is a share bound,
and we bound `δ` and `J`" (`step2`), (3) "Next we show that every `Ũ_j` is a valid bound"
(`step3`), which ends with "For `j = ĵ`, this is the left-hand inequality of the claim", and (4)
"Finally, we show that some `Ũ_j` is large" (`step4`), which ends with "As `Ũ ≥ Ũ_j`, this proves
the right-hand inequality of the claim". -/
theorem convexscheme (h : Setting P m c rb)
    (horc : ∀ α ∈ Icc (0 : ℝ) 1, ∀ δ, 0 < δ → IsDeltaOpt P m c α δ (orc α δ)) {ε : ℝ}
    (hε : ε ∈ Ioo (0 : ℝ) 1) :
    (0 < welfare P m c → ∀ w : Option ℝ,
      (∀ w₀ ∈ w, w₀ ∈ Ioc 0 rb ∧ (welfare P m c = 0 ∨ w₀ ≤ welfare P m c)) →
      (∃ b Ut, Returns rb m c orc ε w b Ut) ∧ ¬ ReturnsZero rb m c orc w ∧
      (∀ b Ut, Returns rb m c orc ε w b Ut → b ∈ Ioo (0 : ℝ) 1 ∧
        (∀ y ∈ bestResponses P m c b, Ut ≤ (1 - b) * reward m y) ∧
        (1 - ε) * OPT (profit P m c) ≤ Ut) ∧
      ∀ K, LoopBreaks rb m c orc w K →
        K + 1 ≤ ⌈Real.logb 2 (3 * rb / welfare P m c)⌉₊ + 1 ∧
        (∀ k ≤ K, welfare P m c / 6 < loopD rb k) ∧
        schemeJ (ε / 2) (cᾱ rb (loopW rb m c orc K)) + 1 ≤
          ⌈8 / ε * Real.log (3 * rb / welfare P m c)⌉₊ + 1 ∧
        ε ^ 2 * welfare P m c / (192 * ⌈Real.logb 2 (3 * rb / welfare P m c)⌉₊) ≤
          cδ rb ε (loopW rb m c orc K)) ∧
    (welfare P m c = 0 →
      (∀ K, ¬ LoopBreaks rb m c orc none K ∧ ¬ LoopZero rb m c orc none K) ∧
      ∀ w ∈ Ioc 0 rb, ∃ K, LoopZero rb m c orc (some w) K ∧
        K + 1 ≤ ⌊Real.logb 2 (3 * rb / w)⌋₊ + 2 ∧ ∀ k ≤ K, w / 6 ≤ loopD rb k) := by
  refine ⟨fun hW w hw => ?_, fun hW => ?_⟩
  · -- (1): the loop breaks in a round `K`, with `(2/3) W ≤ W̃_K ≤ W`
    obtain ⟨⟨K₀, hK₀⟩, hnz, hloop⟩ := step1_pos h horc hW hw
    refine ⟨?_, fun ⟨K, hK⟩ => hnz ⟨K, hK⟩, ?_, fun K hK => ?_⟩
    · -- the algorithm returns: `ĵ` with the largest `Ũ_ĵ`
      obtain ⟨-, -, hW1, hW2⟩ := hloop K₀ hK₀
      obtain ⟨jh, hjh, hmax⟩ := exists_max_image
        (range (schemeJ (ε / 2) (cᾱ rb (loopW rb m c orc K₀)) + 1))
        (fun j => cU rb m orc ε (loopW rb m c orc K₀) j) nonempty_range_add_one
      exact ⟨_, _, K₀, hK₀, jh, by have := mem_range.1 hjh; omega,
        fun j hj => hmax j (mem_range.2 (by omega)), rfl, rfl⟩
    · rintro b Ut ⟨K, hK, jh, hjh, hmax, rfl, rfl⟩
      obtain ⟨-, -, hW1, hW2⟩ := hloop K hK
      -- (3) for `j = ĵ`: "For `j = ĵ`, this is the left-hand inequality of the claim."
      obtain ⟨hb, hval⟩ := step3 h horc hε hW hW1 hW2 hjh
      -- (4): "As `Ũ ≥ Ũ_j`, this proves the right-hand inequality of the claim."
      obtain ⟨j, hj, hjU⟩ := step4 h horc hε hW hW1 hW2
      exact ⟨hb, hval, hjU.trans (hmax j hj)⟩
    · -- the counts: (1) and (2)
      obtain ⟨hcalls, hprec, hW1, hW2⟩ := hloop K hK
      obtain ⟨-, -, hδ, -, hJ⟩ := step2 h hε hW hW1 hW2
      exact ⟨hcalls, hprec, hJ, hδ⟩
  · -- (1), the case `W = 0`
    obtain ⟨hno, hzero⟩ := step1_zero h horc hW
    refine ⟨fun K => ⟨fun hK => hno K hK.1, fun hK => ?_⟩, fun w hw => ?_⟩
    · obtain ⟨w₀, hw₀, -⟩ := hK.2.1
      cases hw₀
    · obtain ⟨K, hK, hKeq, hprec⟩ := hzero w hw
      exact ⟨K, hK, by omega, hprec⟩

end Main

/-! ### `prop:approxresponses` -/

section Approx

/-- `⌈log₂(3r̄/u)⌉ ≥ 1` for `u ∈ (0, r̄]` (not in the paper: it uses this tacitly). -/
lemma one_le_ceil_logb {R u : ℝ} (hu : 0 < u) (huR : u ≤ R) :
    (1 : ℝ) ≤ ⌈Real.logb 2 (3 * R / u)⌉₊ := by
  have : 1 ≤ Real.logb 2 (3 * R / u) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (div_pos (by linarith) hu), le_div_iff₀ hu]
    norm_num
    linarith
  exact_mod_cast Nat.one_le_iff_ne_zero.2 fun h0 => by
    have := Nat.le_ceil (Real.logb 2 (3 * R / u))
    rw [h0] at this
    push_cast at this
    linarith

/-- The `O(ε⁻¹ log(3r̄/w))` oracle calls of `prop:approxresponses`, and the
"`O(ε⁻¹ log(3r̄/w))` responses" of (T4) of the proof of `thm:convexfptas`, with the constant `14`
(not in the paper: it states the `O`): for `ε ∈ (0, 1)` and `w ∈ (0, r̄]`,
`(⌈log₂(3r̄/w)⌉ + 1) + (⌈8ε⁻¹ ln(3r̄/w)⌉ + 1) ≤ 14 ε⁻¹ ln(3r̄/w)` and
`⌊log₂(3r̄/w)⌋ + 2 ≤ 14 ε⁻¹ ln(3r̄/w)`. -/
lemma calls_le {R w ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) (hw : 0 < w) (hwR : w ≤ R) :
    ((⌈Real.logb 2 (3 * R / w)⌉₊ + 1 + (⌈8 / ε * Real.log (3 * R / w)⌉₊ + 1) : ℕ) : ℝ) ≤
        14 / ε * Real.log (3 * R / w) ∧
      ((⌊Real.logb 2 (3 * R / w)⌋₊ + 2 : ℕ) : ℝ) ≤ 14 / ε * Real.log (3 * R / w) := by
  have hε0 := hε.1
  have hε1 := hε.2
  set L := Real.log (3 * R / w) with hLdef
  have h3 : 3 ≤ 3 * R / w := by rw [le_div_iff₀ hw]; linarith
  -- `ln(3r̄/w) ≥ ln 3 > 1`
  have hL1 : 1 < L := by
    have : (1 : ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9
      linarith
    exact this.trans_le (Real.log_le_log (by norm_num) h3)
  -- `log₂(3r̄/w) = L/ln 2 ≤ (3/2) L`
  have hl2 := Real.log_two_gt_d9
  have hlogb : Real.logb 2 (3 * R / w) ≤ 3 / 2 * L := by
    rw [Real.logb, div_le_iff₀ (Real.log_pos one_lt_two)]
    nlinarith
  have hlogb0 : 0 ≤ Real.logb 2 (3 * R / w) := Real.logb_nonneg one_lt_two (by linarith)
  have hc1 : (⌈Real.logb 2 (3 * R / w)⌉₊ : ℝ) ≤ 3 / 2 * L + 1 :=
    (Nat.ceil_lt_add_one hlogb0).le.trans (by linarith)
  have h8 : 0 ≤ 8 / ε * L := mul_nonneg (div_nonneg (by norm_num) hε0.le) (by linarith)
  have hc2 : (⌈8 / ε * L⌉₊ : ℝ) ≤ 8 / ε * L + 1 := (Nat.ceil_lt_add_one h8).le
  have hfl : (⌊Real.logb 2 (3 * R / w)⌋₊ : ℝ) ≤ 3 / 2 * L := (Nat.floor_le hlogb0).trans hlogb
  -- `L ≤ L/ε`
  have hLε : L ≤ L / ε := by rw [le_div_iff₀ hε0]; nlinarith
  have e14 : 14 / ε * L = 14 * (L / ε) := by ring
  have e8 : 8 / ε * L = 8 * (L / ε) := by ring
  constructor
  · push_cast
    linarith
  · push_cast
    linarith

/-- The proof of `prop:approxresponses`, "If `W = 0`, it detects this with `O(log(3r̄/w))` calls",
with the constant `4` (not in the paper: it states the `O`): for `w ∈ (0, r̄]`,
`⌊log₂(3r̄/w)⌋ + 2 ≤ 4 ln(3r̄/w)`, as `ln(3r̄/w) ≥ ln 3 > 1` and `log₂(3r̄/w) ≤ (3/2) ln(3r̄/w)`. -/
lemma calls_zero_le {R w : ℝ} (hw : 0 < w) (hwR : w ≤ R) :
    ((⌊Real.logb 2 (3 * R / w)⌋₊ + 2 : ℕ) : ℝ) ≤ 4 * Real.log (3 * R / w) := by
  set L := Real.log (3 * R / w) with hLdef
  have h3 : 3 ≤ 3 * R / w := by rw [le_div_iff₀ hw]; linarith
  -- `ln(3r̄/w) ≥ ln 3 > 1`
  have hL1 : 1 < L := by
    have : (1 : ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9
      linarith
    exact this.trans_le (Real.log_le_log (by norm_num) h3)
  -- `log₂(3r̄/w) = L/ln 2 ≤ (3/2) L`
  have hl2 := Real.log_two_gt_d9
  have hlogb : Real.logb 2 (3 * R / w) ≤ 3 / 2 * L := by
    rw [Real.logb, div_le_iff₀ (Real.log_pos one_lt_two)]
    nlinarith
  have hlogb0 : 0 ≤ Real.logb 2 (3 * R / w) := Real.logb_nonneg one_lt_two (by linarith)
  have hfl : (⌊Real.logb 2 (3 * R / w)⌋₊ : ℝ) ≤ 3 / 2 * L := (Nat.floor_le hlogb0).trans hlogb
  push_cast
  linarith

variable {E : Type*} [Fintype E] {P : Set (E → ℝ)} {m : E → ℝ} {c : (E → ℝ) → ℝ} {rb : ℝ}
  {orc : ℝ → ℝ → (E → ℝ)}

/-- **`prop:approxresponses`** (Proposition 5.6; 08c-convex.tex:7-9, proof appF-convex.tex:113-115):
"Given an approximate best-response oracle, `ε ∈ (0, 1)`, and `w ∈ (0, r̄]` such that `W = 0` or
`W ≥ w`, one can determine whether `W = 0` and otherwise compute a `(1 − ε)`-optimal contract using
`O(ε⁻¹ log(3r̄/w))` oracle calls."

Here, in the setting of `prop:convexscheme` (`Setting`: a compact action set `K ⊆ ℝ^E_{≥0}` with
`0 ∈ K`, here `P`, a continuous cost `c ≥ 0` on it with `c(0) = 0`, `r(x) = mᵀx` with `m ≥ 0` and a
known bound `r ≤ r̄` on `K`, where `r̄ > 0`) and with an approximate best-response oracle `orc` (for
`α ∈ [0, 1]` and `δ > 0`, `orc α δ` is a `δ`-optimal response at `α`, 08c-convex.tex:3-4, whose
reward and cost are known exactly), `alg:convex` with `w`:
(a) returns "`W = 0`" if and only if `W = 0` ("determine whether `W = 0`");
(b) if `W ≠ 0`, returns a share `b` (with a number `Ũ`), and every share it returns is a
`(1 − ε)`-optimal contract (`IsApproxOptimal`);
(c) makes at most `14 ε⁻¹ ln(3r̄/w)` oracle calls (`O(ε⁻¹ log(3r̄/w))`; the constant `14` is ours):
if the loop breaks in round `K`, the `K + 1` calls of the loop and the `J + 1` calls at the shares
`α̂_j + h_j`, and if it returns "`W = 0`" in round `K`, the `K + 1` calls of the loop.
The proposition takes the setting of `prop:convexscheme`, which its proof applies, stated at the
start of `app:convex` (appF-convex.tex:9); the introduction states it so: "The underlying scheme
applies to any compact action set containing zero, with continuous nonnegative costs vanishing at
zero, given approximate responses and their reward and cost values (`prop:approxresponses`)"
(01-introduction.tex:26). Section 5.2 introduces its costs as convex (08c-convex.tex:3), which the
proof does not use.

The proof (appF-convex.tex:114), sentence by sentence: (1) "Apply `prop:convexscheme` with the
supplied `w`" (`convexscheme`); (2) "If `W > 0`, then `W ≥ w`, so its call bound is
`O(ε⁻¹ log(3r̄/w))`, and the returned contract is `(1 − ε)`-optimal" (`calls_le`; the share `b`
has `(1 − b) r(y) ≥ (1 − ε) OPT` for every `y ∈ X*(b)`, so for `x*(b)`); (3) "If `W = 0`, it detects
this with `O(log(3r̄/w))` calls" (`calls_zero_le`); (4) "The required oracle precisions and the
guarantee without a supplied `w` are given in `prop:convexscheme`" (a reference to `convexscheme`;
nothing is left to prove). That "`W = 0`" is returned only if `W = 0`, and the loop breaks only if
`W ≠ 0`, is (2) and (3) together. -/
theorem approxresponses (h : Setting P m c rb)
    (horc : ∀ α ∈ Icc (0 : ℝ) 1, ∀ δ, 0 < δ → IsDeltaOpt P m c α δ (orc α δ)) {ε w : ℝ}
    (hε : ε ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioc 0 rb)
    (hwW : welfare P m c = 0 ∨ w ≤ welfare P m c) :
    (ReturnsZero rb m c orc (some w) ↔ welfare P m c = 0) ∧
    (welfare P m c ≠ 0 → (∃ b Ut, Returns rb m c orc ε (some w) b Ut) ∧
      ∀ b Ut, Returns rb m c orc ε (some w) b Ut → IsApproxOptimal (profit P m c) ε b) ∧
    (∀ K, LoopBreaks rb m c orc (some w) K →
      ((K + 1 + (schemeJ (ε / 2) (cᾱ rb (loopW rb m c orc K)) + 1) : ℕ) : ℝ) ≤
        14 / ε * Real.log (3 * rb / w)) ∧
    (∀ K, LoopZero rb m c orc (some w) K →
      ((K + 1 : ℕ) : ℝ) ≤ 14 / ε * Real.log (3 * rb / w)) := by
  obtain ⟨hw0, hwrb⟩ := hw
  have hrb := h.rbar_pos
  have hwsome : ∀ w₀ ∈ some w, w₀ ∈ Ioc 0 rb ∧ (welfare P m c = 0 ∨ w₀ ≤ welfare P m c) :=
    fun w₀ hw₀ => by
      cases hw₀
      exact ⟨⟨hw0, hwrb⟩, hwW⟩
  -- (1) "Apply `prop:convexscheme` with the supplied `w`."
  obtain ⟨hpos, hzero⟩ := convexscheme h horc hε
  -- (2) "If `W > 0`, then `W ≥ w`, so its call bound is `O(ε⁻¹ log(3r̄/w))`, and the returned
  -- contract is `(1 − ε)`-optimal."
  have h2 : 0 < welfare P m c →
      (∃ b Ut, Returns rb m c orc ε (some w) b Ut) ∧ ¬ ReturnsZero rb m c orc (some w) ∧
      (∀ b Ut, Returns rb m c orc ε (some w) b Ut → IsApproxOptimal (profit P m c) ε b) ∧
      ∀ K, LoopBreaks rb m c orc (some w) K →
        ((K + 1 + (schemeJ (ε / 2) (cᾱ rb (loopW rb m c orc K)) + 1) : ℕ) : ℝ) ≤
          14 / ε * Real.log (3 * rb / w) := by
    intro hW
    have hwW' : w ≤ welfare P m c := hwW.resolve_left hW.ne'
    obtain ⟨hex, hnz, hval, hcount⟩ := hpos hW (some w) hwsome
    refine ⟨hex, hnz, fun b Ut hbU => ?_, fun K hK => ?_⟩
    · -- "the returned contract is `(1 − ε)`-optimal": `(1 − b) r(x*(b)) ≥ Ũ ≥ (1 − ε) OPT`
      obtain ⟨hb, hy, hU⟩ := hval b Ut hbU
      obtain ⟨y, hyBR, hyS⟩ := h.exists_favourable b
      refine ⟨⟨hb.1.le, hb.2.le⟩, ?_⟩
      calc (1 - ε) * OPT (profit P m c) ≤ Ut := hU
        _ ≤ (1 - b) * reward m y := hy y hyBR
        _ = profit P m c b := by rw [profit, hyS]
    · -- "so its call bound is `O(ε⁻¹ log(3r̄/w))`": the bounds of `prop:convexscheme` with
      -- `3r̄/W ≤ 3r̄/w`
      obtain ⟨hK1, -, hJ, -⟩ := hcount K hK
      have h3 : 3 * rb / welfare P m c ≤ 3 * rb / w :=
        div_le_div_of_nonneg_left (by positivity) hw0 hwW'
      have hKw : K + 1 ≤ ⌈Real.logb 2 (3 * rb / w)⌉₊ + 1 := by
        have := Nat.ceil_mono (Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h3)
        omega
      have hJw : schemeJ (ε / 2) (cᾱ rb (loopW rb m c orc K)) + 1 ≤
          ⌈8 / ε * Real.log (3 * rb / w)⌉₊ + 1 :=
        hJ.trans (Nat.add_le_add_right (Nat.ceil_mono (mul_le_mul_of_nonneg_left
          (Real.log_le_log (by positivity) h3) (div_nonneg (by norm_num) hε.1.le))) 1)
      obtain ⟨hcalls, -⟩ := calls_le hε hw0 hwrb
      have : ((K + 1 + (schemeJ (ε / 2) (cᾱ rb (loopW rb m c orc K)) + 1) : ℕ) : ℝ) ≤
          ((⌈Real.logb 2 (3 * rb / w)⌉₊ + 1 + (⌈8 / ε * Real.log (3 * rb / w)⌉₊ + 1) : ℕ) :
            ℝ) := by
        exact_mod_cast Nat.add_le_add hKw hJw
      exact this.trans hcalls
  -- (3) "If `W = 0`, it detects this with `O(log(3r̄/w))` calls."
  have h3 : welfare P m c = 0 → (∃ K, LoopZero rb m c orc (some w) K) ∧
      ∀ K, LoopZero rb m c orc (some w) K → ((K + 1 : ℕ) : ℝ) ≤ 4 * Real.log (3 * rb / w) := by
    intro h0
    obtain ⟨-, hz⟩ := hzero h0
    obtain ⟨K', hK', hK'1, -⟩ := hz w ⟨hw0, hwrb⟩
    refine ⟨⟨K', hK'⟩, fun K hK => ?_⟩
    obtain rfl := loopZero_unique hK hK'
    have : ((K + 1 : ℕ) : ℝ) ≤ ((⌊Real.logb 2 (3 * rb / w)⌋₊ + 2 : ℕ) : ℝ) := by
      exact_mod_cast hK'1
    exact this.trans (calls_zero_le hw0 hwrb)
  -- (4) "The required oracle precisions and the guarantee without a supplied `w` are given in
  -- `prop:convexscheme`." (a reference to `convexscheme`)
  -- "`W = 0`" is returned exactly if `W = 0`, by (2) and (3)
  have hW : welfare P m c ≠ 0 → 0 < welfare P m c := fun hne => hw0.trans_le (hwW.resolve_left hne)
  refine ⟨⟨fun hz => ?_, fun h0 => ?_⟩, fun hne => ?_, fun K hK => ?_, fun K hK => ?_⟩
  · by_contra hne
    exact (h2 (hW hne)).2.1 hz
  · obtain ⟨⟨K, hK⟩, -⟩ := h3 h0
    exact ⟨K, hK⟩
  · obtain ⟨hex, -, hopt, -⟩ := h2 (hW hne)
    exact ⟨hex, hopt⟩
  · -- the loop breaks, so `W ≠ 0`, by (3)
    have hne : welfare P m c ≠ 0 := fun h0 => by
      obtain ⟨⟨K', hK'⟩, -⟩ := h3 h0
      exact not_loopBreaks_and_loopZero hK hK'
    exact (h2 (hW hne)).2.2.2 K hK
  · -- "`W = 0`" is returned, so `W = 0`, by (2); and `4 ≤ 14/ε`
    have h0 : welfare P m c = 0 := by
      by_contra hne
      exact (h2 (hW hne)).2.1 ⟨K, hK⟩
    have hle := (h3 h0).2 K hK
    have hL : 0 < Real.log (3 * rb / w) := Real.log_pos (by rw [lt_div_iff₀ hw0]; linarith)
    have h14 : 4 ≤ 14 / ε := by rw [le_div_iff₀ hε.1]; linarith [hε.2]
    nlinarith

end Approx

/-! ### `alg:convex` with its operation counts

The proof of `thm:convexfptas` counts the work of `alg:convex` with `lem:ellipsoid` as the oracle
(appF-convex.tex:144): "`O(ε⁻¹ log(3r̄/w))` responses are computed", "each response takes
`O(n² log(2nM/(εw)))` iterations by `lem:ellipsoid`", and "The remaining work, the `n + 1`
evaluations of `f` for the coordinate bounds `f({e})` used by the ellipsoid method and for `f(E)`,
the values of `r` at the responses (those of `c` come with them), the number `⌈log₂(2r̄/W̃)⌉`, and
the `J + 1` shares constructed in the proof of `thm:fptas` with `s = O(log(1/(ε(1 − ᾱ))))` bits
each, takes a number of operations polynomial in `n`, `1/ε`, and `log(3r̄/w)`". The counted scheme
`convexC` performs `alg:convex` with `w` in the cost model of `Stoc.CountedQ`, with the responses of
the counted ellipsoid method `respC` after its preparation `prepC` (`ContractDesignPolymatroids/Convex/Ellipsoid.lean`):
the welfare loop (`loopC`), and after it `postC`: `LB` (`lbC`, with the number `⌈log₂(2r̄/W̃)⌉` by
repeated doubling, `powSearchC`), `ᾱ` and `δ`, `J` (`jC`, by repeated multiplication), `s` (`sC`),
and the shares (`sharesC`, with `⌊2^s (1 − ε/4)^j⌋` bit by bit, `floorBitsC`, and the record of the
largest `Ũ_j`, `maxUpd`). The searches and the floor are computed step by step, as the model of
08c-convex.tex:13 has neither logarithms nor a floor. The fuel of the searches (`powSearchC`) and of
the welfare loop (`loopC`) only makes Lean's recursion terminate: it is computed outside the model
(with `log`, `⌊·⌋` and `⌈·⌉`, for `J` from `schemeJ` itself), is not counted and is not part of
`alg:convex`; the searches and the loop end before it runs out (`powSearchC_spec`,
`loopRound_le`), so the values and the counts do not depend on it. The iteration number
`t(δ) = ellipsoidIters n M δ` of each response is taken by `respC` from its definition at no cost:
computing it needs `ln` and `⌈·⌉`, which the model lacks, and the paper does not count it.
`convexC_breaks` and `convexC_zero` give its
value (the share and the number of `Returns`, or "`W = 0`") and its counts in the numbers of
rounds, shares and iterations; `totals_le` and `totals_le_zero`, with `iters_poly`, `bits_poly` and
`ceil_logb_poly`, turn them into the polynomials of `convexfptas`. (Not in the paper: the paper
counts in prose.) -/

section Counts

open Counted

section CountedSearch

open Classical in
/-- The least `k` with `P(b^k)`, from the counter `k` and the power `p = b^k`, by computing
`b^0 = 1, b^1, b^2, …` (one multiplication and one increment for each step) and testing `P` on each
(one comparison). It computes the numbers `⌈log₂(2r̄/W̃)⌉`, `J` and `s` of `alg:convex`
(appF-convex.tex:70-71), as the model of 08c-convex.tex:13 has no logarithms (not in the paper).
The fuel (at most `fuel` tests) only makes Lean's recursion terminate: the callers compute it
outside the model and do not count it, and once it exceeds the answer the value and the count do
not depend on it (`powSearchC_spec`). -/
def powSearchC (b : ℝ) (P : ℝ → Prop) : ℕ → ℕ → ℝ → Counted (ℕ × ℝ)
  | 0, k, p => Counted.ret (k, p)
  | fuel + 1, k, p =>
      ops 1 () >>=ᶜ fun _ =>
      if P p then Counted.ret (k, p)
      else ops 2 (b * p) >>=ᶜ fun p' => powSearchC b P fuel (k + 1) p'

/-- From `k ≤ K`, with more than `K − k` tests left, the search returns the least `K` with `P(b^K)`
and `b^K`, with `3(K − k) + 1` operations (not in the paper). -/
lemma powSearchC_spec (b : ℝ) (P : ℝ → Prop) {K : ℕ} (hK : P (b ^ K))
    (hlt : ∀ i < K, ¬ P (b ^ i)) :
    ∀ fuel k, k ≤ K → K < k + fuel →
      (powSearchC b P fuel k (b ^ k)).val = (K, b ^ K) ∧
        (powSearchC b P fuel k (b ^ k)).cost = (3 * (K - k) + 1, 0, 0) := by
  intro fuel
  induction fuel with
  | zero => intro k hk h; omega
  | succ fuel ih =>
    intro k hk hfuel
    rcases hk.lt_or_eq with hlt' | rfl
    · have hP : ¬ P (b ^ k) := hlt k hlt'
      obtain ⟨h1, h2⟩ := ih (k + 1) hlt' (by omega)
      have hp : b * b ^ k = b ^ (k + 1) := (pow_succ' b k).symm
      simp only [powSearchC, Counted.val_bind, Counted.cost_bind, cost_ops, val_ops, hP,
        ite_false, hp, h1, h2, true_and]
      simp only [Prod.mk_add_mk, add_zero, Prod.mk.injEq, and_true]
      omega
    · simp [powSearchC, hK]

/-- `⌊x⌋` for `N ≤ x < N + 2^i`, bit by bit (the shares "with `s` bits each" of the proof of
`thm:convexfptas`, appF-convex.tex:144, as the model of 08c-convex.tex:13 has no floor): for the
bits `i − 1, …, 0`, with `pw = 2^{bit}`, one addition, one comparison and one halving each (not in
the paper). -/
def floorBitsC (x : ℝ) : ℕ → ℝ → ℝ → Counted ℝ
  | 0, a, _ => Counted.ret a
  | i + 1, a, pw =>
      ops 2 (a + pw) >>=ᶜ fun a' =>
      ops 1 (pw / 2) >>=ᶜ fun pw' =>
      if a' ≤ x then floorBitsC x i a' pw' else floorBitsC x i a pw'

/-- The bits give `⌊x⌋`, with `3i` operations (not in the paper). -/
lemma floorBitsC_spec (x : ℝ) :
    ∀ (i N : ℕ), (N : ℝ) ≤ x → x < N + 2 ^ i →
      (floorBitsC x i N (2 ^ i / 2)).val = (⌊x⌋₊ : ℝ) ∧
        (floorBitsC x i N (2 ^ i / 2)).cost = (3 * i, 0, 0) := by
  intro i
  induction i with
  | zero =>
    intro N h1 h2
    have hx : 0 ≤ x := (Nat.cast_nonneg N).trans h1
    have : ⌊x⌋₊ = N := (Nat.floor_eq_iff hx).2 ⟨h1, by simpa using h2⟩
    exact ⟨by simp [floorBitsC, this], rfl⟩
  | succ i ih =>
    intro N h1 h2
    have hpw : (2 : ℝ) ^ (i + 1) / 2 = 2 ^ i := by rw [pow_succ]; ring
    by_cases hle : (N : ℝ) + 2 ^ i ≤ x
    · obtain ⟨k1, k2⟩ := ih (N + 2 ^ i) (by push_cast; exact hle)
        (by push_cast; rw [pow_succ] at h2; linarith)
      have e : ((N + 2 ^ i : ℕ) : ℝ) = (N : ℝ) + 2 ^ i := by push_cast; ring
      rw [e] at k1 k2
      simp only [floorBitsC, Counted.val_bind, Counted.cost_bind, cost_ops, val_ops, hpw, hle,
        ite_true, k1, k2, true_and]
      simp only [Prod.mk_add_mk, add_zero, Prod.mk.injEq, and_true]
      ring
    · obtain ⟨k1, k2⟩ := ih N h1 (lt_of_not_ge hle)
      simp only [floorBitsC, Counted.val_bind, Counted.cost_bind, cost_ops, val_ops, hpw, hle,
        ite_false, k1, k2, true_and]
      simp only [Prod.mk_add_mk, add_zero, Prod.mk.injEq, and_true]
      ring

end CountedSearch

section CountedLoop

variable {E : Type*} [Fintype E]

/-- The welfare loop of `alg:convex` (appF-convex.tex:63-69), counted, from the precision `d`, at
most `fuel` rounds, with a counted oracle `resp` that returns a response and its cost: in each
round "`x̃ ←` a `d`-optimal response at the share `1`, `W̃ ← r(x̃) − c(x̃)`" (the response, `r(x̃)`
with one multiplication and one addition for each `e`, "those of `c` come with them", appF:144,
and one subtraction), "if `W̃ ≥ 2d` then break" (two operations), "if `w` is given and `d < w/3`
then return "`W = 0`"" (two operations) and "`d ← d/2`" (one). It returns `inl W̃` when the loop
breaks and `inr ()` when it returns "`W = 0`". -/
def loopC (m : E → ℝ) (resp : ℝ → ℝ → CountedQ ((E → ℝ) × ℝ)) (w : ℝ) :
    ℕ → ℝ → CountedQ (ℝ ⊕ Unit)
  | 0, _ => CountedQ.ret (Sum.inr ())
  | fuel + 1, d =>
      resp 1 d >>=ᵠ fun p =>
      CountedQ.lift (Counted.sum univ fun e => ops 1 (m e * p.1 e)) >>=ᵠ fun r =>
      CountedQ.lift (ops 1 (r - p.2)) >>=ᵠ fun Wt =>
      CountedQ.lift (ops 2 ()) >>=ᵠ fun _ =>
      if 2 * d ≤ Wt then CountedQ.ret (Sum.inl Wt) else
      CountedQ.lift (ops 2 ()) >>=ᵠ fun _ =>
      if d < w / 3 then CountedQ.ret (Sum.inr ()) else
      CountedQ.lift (ops 1 (d / 2)) >>=ᵠ fun d' => loopC m resp w fuel d'

variable {rb : ℝ} {m : E → ℝ} {c : (E → ℝ) → ℝ} {orc : ℝ → ℝ → (E → ℝ)}

/-- The counted loop is the loop of `alg:convex` (`LoopBreaks`, `LoopZero`): if the rounds before
`K` neither break nor return and round `K` does one of them, then from round `j ≤ K`, with more than
`K − j` rounds left, it returns `W̃_K` (`loopW`) if it breaks and "`W = 0`" otherwise, with at most
`K − j + 1` responses and `2n + 6` further operations in each round (not in the paper). -/
lemma loopC_spec {resp : ℝ → ℝ → CountedQ ((E → ℝ) × ℝ)}
    (hval : ∀ d, (resp 1 d).val = (orc 1 d, c (orc 1 d))) {w : ℝ} {K : ℕ}
    (hbefore : ∀ k < K, ¬ Brk rb m c orc k ∧ ¬ WTest rb (some w) k)
    (hend : Brk rb m c orc K ∨ WTest rb (some w) K) {A B : ℕ}
    (hA : ∀ k ≤ K, (resp 1 (loopD rb k)).cost.1 ≤ A ∧ (resp 1 (loopD rb k)).cost.2.1 ≤ B ∧
      (resp 1 (loopD rb k)).cost.2.2 ≤ B ∧ (resp 1 (loopD rb k)).queries ≤ B) :
    ∀ fuel j, j ≤ K → K < j + fuel →
      (Brk rb m c orc K → (loopC m resp w fuel (loopD rb j)).val = Sum.inl (loopW rb m c orc K)) ∧
        (¬ Brk rb m c orc K → (loopC m resp w fuel (loopD rb j)).val = Sum.inr ()) ∧
        (loopC m resp w fuel (loopD rb j)).cost.1 ≤
          (K - j + 1) * (A + 2 * Fintype.card E + 6) ∧
        (loopC m resp w fuel (loopD rb j)).cost.2.1 ≤ (K - j + 1) * B ∧
        (loopC m resp w fuel (loopD rb j)).cost.2.2 ≤ (K - j + 1) * B ∧
        (loopC m resp w fuel (loopD rb j)).queries ≤ (K - j + 1) * B := by
  intro fuel
  induction fuel with
  | zero => intro j hj h; omega
  | succ fuel ih =>
    intro j hj hfuel
    obtain ⟨a1, a2, a3, a4⟩ := hA j hj
    -- the estimate `W̃` of round `j`
    have hW : reward m (resp 1 (loopD rb j)).val.1 - (resp 1 (loopD rb j)).val.2 =
        loopW rb m c orc j := by
      rw [hval]
      rfl
    have hsum : (∑ e, m e * (resp 1 (loopD rb j)).val.1 e) =
        reward m (resp 1 (loopD rb j)).val.1 := rfl
    have hwt : WTest rb (some w) j ↔ loopD rb j < w / 3 :=
      ⟨fun ⟨w₀, hw₀, h⟩ => by cases hw₀; exact h, fun h => ⟨w, rfl, h⟩⟩
    have hcard : ∑ _e : E, ((1, 0, 0) : Cost) = (Fintype.card E, 0, 0) := by
      simp [sum_const, Prod.smul_mk]
    rcases hj.lt_or_eq with hlt | rfl
    · -- an earlier round: no break, no return, and `d ← d/2`
      obtain ⟨hnb, hnw⟩ := hbefore j hlt
      have hnb' : ¬ 2 * loopD rb j ≤ reward m (resp 1 (loopD rb j)).val.1 -
          (resp 1 (loopD rb j)).val.2 := by rw [hW]; exact hnb
      have hnw' : ¬ loopD rb j < w / 3 := fun h => hnw (hwt.2 h)
      obtain ⟨k0, k1, k2, k3, k4, k5⟩ := ih (j + 1) hlt (by omega)
      rw [loopD_succ] at k0 k1 k2 k3 k4 k5
      have e : K - j + 1 = (K - (j + 1) + 1) + 1 := by omega
      have hX : ∀ X : ℕ, (K - j + 1) * X = (K - (j + 1) + 1) * X + X := fun X => by
        rw [e]; ring
      simp only [loopC, CountedQ.val_bind, CountedQ.cost_bind, CountedQ.queries_bind,
        CountedQ.val_lift, CountedQ.cost_lift, CountedQ.queries_lift, val_sum, val_ops,
        cost_sum, cost_ops, hsum, hnb', hnw', ite_false]
      refine ⟨k0, k1, ?_⟩
      simp only [hcard, card_univ, Prod.fst_add, Prod.snd_add, hX]
      omega
    · -- round `K`: the break, or the return of "`W = 0`"
      by_cases hb : Brk rb m c orc j
      · have hb' : 2 * loopD rb j ≤ reward m (resp 1 (loopD rb j)).val.1 -
            (resp 1 (loopD rb j)).val.2 := by rw [hW]; exact hb
        have hb'' : 2 * loopD rb j ≤ loopW rb m c orc j := hb
        refine ⟨fun _ => ?_, fun h => absurd hb h, ?_⟩
        · simp only [loopC, CountedQ.val_bind, CountedQ.val_lift, val_sum, val_ops, hsum, hW,
            hb'', ite_true, CountedQ.val_ret]
        · simp only [loopC, CountedQ.cost_bind, CountedQ.queries_bind, CountedQ.val_lift,
            CountedQ.cost_lift, CountedQ.queries_lift, val_sum, val_ops, cost_sum, cost_ops, hsum,
            hb', ite_true, CountedQ.cost_ret, CountedQ.queries_ret, hcard, card_univ,
            Prod.fst_add, Prod.snd_add, Nat.sub_self, zero_add, one_mul, Prod.fst_zero,
            Prod.snd_zero]
          omega
      · have hz : loopD rb j < w / 3 := hwt.1 (hend.resolve_left hb)
        have hb' : ¬ 2 * loopD rb j ≤ reward m (resp 1 (loopD rb j)).val.1 -
            (resp 1 (loopD rb j)).val.2 := by rw [hW]; exact hb
        refine ⟨fun h => absurd h hb, fun _ => ?_, ?_⟩
        · simp only [loopC, CountedQ.val_bind, CountedQ.val_lift, val_sum, val_ops, hsum, hb',
            hz, ite_false, ite_true, CountedQ.val_ret]
        · simp only [loopC, CountedQ.cost_bind, CountedQ.queries_bind, CountedQ.val_lift,
            CountedQ.cost_lift, CountedQ.queries_lift, val_sum, val_ops, cost_sum, cost_ops, hsum,
            hb', hz, ite_false, ite_true, CountedQ.cost_ret, CountedQ.queries_ret, hcard,
            card_univ, Prod.fst_add, Prod.snd_add, Nat.sub_self, zero_add, one_mul,
            Prod.fst_zero, Prod.snd_zero]
          omega

end CountedLoop

section CountedShares

variable {E : Type*} [Fintype E]

/-- The record of the largest `Ũ_j` so far, with its share `α̌_j` ("choose `ĵ` with
`Ũ_ĵ = max_{j ≤ J} Ũ_j`", appF-convex.tex:77, one comparison for each `j`); the first largest is
kept. -/
def maxUpd : Option (ℝ × ℝ) → ℝ × ℝ → Option (ℝ × ℝ)
  | none, p => some p
  | some q, p => if q.1 < p.1 then some p else some q

/-- The loop over the shares of `alg:convex` (appF-convex.tex:72-77), counted, `k` passes from the
power `qj = (1 − ε/4)^j` with the record `best`, for `q = 1 − ε/4` and `ps = 2^s`:
"`α̂_j ← 1 − 2^{−s}⌊2^s(1 − ε/4)^j⌋`" (one multiplication, the `s + 1` bits of the floor,
`floorBitsC`, and two operations), "`h_j ← (ε/8)(1 − α̂_j)`, `α̌_j ← α̂_j + 2h_j`, `x̃_j ←` a
`δ`-optimal response at the share `α̂_j + h_j`" (six operations and the response),
"`Ũ_j ← (1 − α̌_j)(r(x̃_j) − δ/h_j)`" (`r(x̃_j)` and four operations), one comparison for the
record, and one multiplication for the next power. -/
def sharesC (m : E → ℝ) (resp : ℝ → ℝ → CountedQ ((E → ℝ) × ℝ)) (ε δ q ps : ℝ) (s : ℕ) :
    ℕ → ℝ → Option (ℝ × ℝ) → CountedQ (Option (ℝ × ℝ))
  | 0, _, best => CountedQ.ret best
  | k + 1, qj, best =>
      CountedQ.lift (ops 1 (ps * qj)) >>=ᵠ fun x =>
      CountedQ.lift (floorBitsC x (s + 1) 0 ps) >>=ᵠ fun N =>
      CountedQ.lift (ops 2 (1 - N / ps)) >>=ᵠ fun ah =>
      CountedQ.lift (ops 3 (ε / 8 * (1 - ah))) >>=ᵠ fun hj =>
      CountedQ.lift (ops 2 (ah + 2 * hj)) >>=ᵠ fun ac =>
      CountedQ.lift (ops 1 (ah + hj)) >>=ᵠ fun a =>
      resp a δ >>=ᵠ fun p =>
      CountedQ.lift (Counted.sum univ fun e => ops 1 (m e * p.1 e)) >>=ᵠ fun r =>
      CountedQ.lift (ops 4 ((1 - ac) * (r - δ / hj))) >>=ᵠ fun U =>
      CountedQ.lift (ops 1 (maxUpd best (U, ac))) >>=ᵠ fun best' =>
      CountedQ.lift (ops 1 (qj * q)) >>=ᵠ fun qj' =>
      sharesC m resp ε δ q ps s k qj' best'

variable {rb : ℝ} {m : E → ℝ} {orc : ℝ → ℝ → (E → ℝ)}

/-- The record after the shares `0, …, j − 1`: `none` for `j = 0`, and otherwise `Ũ_ĵ` and `α̌_ĵ`
for a `ĵ < j` with the largest `Ũ` (not in the paper). -/
def ShInv (rb : ℝ) (m : E → ℝ) (orc : ℝ → ℝ → (E → ℝ)) (ε Wt : ℝ) (best : Option (ℝ × ℝ))
    (j : ℕ) : Prop :=
  (j = 0 ∧ best = none) ∨ ∃ jh < j, best = some (cU rb m orc ε Wt jh, cChk rb ε Wt jh) ∧
    ∀ i < j, cU rb m orc ε Wt i ≤ cU rb m orc ε Wt jh

/-- One comparison updates the record (not in the paper). -/
lemma shInv_upd {ε Wt : ℝ} {best : Option (ℝ × ℝ)} {j : ℕ} (h : ShInv rb m orc ε Wt best j) :
    ShInv rb m orc ε Wt (maxUpd best (cU rb m orc ε Wt j, cChk rb ε Wt j)) (j + 1) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨jh, hjh, rfl, hmax⟩
  · exact Or.inr ⟨0, by omega, rfl, fun i hi => by rw [show i = 0 by omega]⟩
  · simp only [maxUpd]
    split_ifs with hlt
    · refine Or.inr ⟨j, by omega, rfl, fun i hi => ?_⟩
      rcases (Nat.lt_succ_iff.1 hi).lt_or_eq with hi' | rfl
      · exact (hmax i hi').trans hlt.le
      · exact le_rfl
    · refine Or.inr ⟨jh, by omega, rfl, fun i hi => ?_⟩
      rcases (Nat.lt_succ_iff.1 hi).lt_or_eq with hi' | rfl
      · exact hmax i hi'
      · exact not_lt.1 hlt

/-- The counted shares are those of `alg:convex` (`cHat`, `cH`, `cChk`, `cResp`, `cU`): `k` passes
from `j` extend the record of the shares before `j` to the shares before `j + k`, with at most `k`
responses and `2n + 3s + 18` further operations in each pass (not in the paper). -/
lemma sharesC_spec {resp : ℝ → ℝ → CountedQ ((E → ℝ) × ℝ)}
    (hresp : ∀ a d, (resp a d).val.1 = orc a d) {ε Wt : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) {A B : ℕ}
    (hA : ∀ a, (resp a (cδ rb ε Wt)).cost.1 ≤ A ∧ (resp a (cδ rb ε Wt)).cost.2.1 ≤ B ∧
      (resp a (cδ rb ε Wt)).cost.2.2 ≤ B ∧ (resp a (cδ rb ε Wt)).queries ≤ B) :
    ∀ k j best, ShInv rb m orc ε Wt best j →
      ShInv rb m orc ε Wt (sharesC m resp ε (cδ rb ε Wt) (1 - ε / 4)
          (2 ^ schemeS (ε / 2) (cᾱ rb Wt)) (schemeS (ε / 2) (cᾱ rb Wt)) k
          ((1 - ε / 4) ^ j) best).val (j + k) ∧
        (sharesC m resp ε (cδ rb ε Wt) (1 - ε / 4) (2 ^ schemeS (ε / 2) (cᾱ rb Wt))
          (schemeS (ε / 2) (cᾱ rb Wt)) k ((1 - ε / 4) ^ j) best).cost.1 ≤
          k * (A + 2 * Fintype.card E + 3 * schemeS (ε / 2) (cᾱ rb Wt) + 18) ∧
        (sharesC m resp ε (cδ rb ε Wt) (1 - ε / 4) (2 ^ schemeS (ε / 2) (cᾱ rb Wt))
          (schemeS (ε / 2) (cᾱ rb Wt)) k ((1 - ε / 4) ^ j) best).cost.2.1 ≤ k * B ∧
        (sharesC m resp ε (cδ rb ε Wt) (1 - ε / 4) (2 ^ schemeS (ε / 2) (cᾱ rb Wt))
          (schemeS (ε / 2) (cᾱ rb Wt)) k ((1 - ε / 4) ^ j) best).cost.2.2 ≤ k * B ∧
        (sharesC m resp ε (cδ rb ε Wt) (1 - ε / 4) (2 ^ schemeS (ε / 2) (cᾱ rb Wt))
          (schemeS (ε / 2) (cᾱ rb Wt)) k ((1 - ε / 4) ^ j) best).queries ≤ k * B := by
  set s := schemeS (ε / 2) (cᾱ rb Wt) with hs
  intro k
  induction k with
  | zero => intro j best hb; simpa [sharesC] using hb
  | succ k ih =>
    intro j best hb
    have hq0 : 0 ≤ 1 - ε / 4 := by linarith [hε.2]
    have hq1 : 1 - ε / 4 ≤ 1 := by linarith [hε.1]
    have hpow0 : 0 ≤ (1 - ε / 4) ^ j := pow_nonneg hq0 j
    have hpow1 : (1 - ε / 4) ^ j ≤ 1 := pow_le_one₀ hq0 hq1
    have h2s : (0 : ℝ) < 2 ^ s := by positivity
    -- `α̂_j`: `⌊2^s (1 − ε/4)^j⌋`, bit by bit
    obtain ⟨f1, f2⟩ := floorBitsC_spec (2 ^ s * (1 - ε / 4) ^ j) (s + 1) 0
      (by simpa using mul_nonneg h2s.le hpow0)
      (by
        have : 2 ^ s * (1 - ε / 4) ^ j ≤ 2 ^ s * 1 := mul_le_mul_of_nonneg_left hpow1 h2s.le
        rw [pow_succ]
        push_cast
        linarith)
    have hps : (2 : ℝ) ^ (s + 1) / 2 = 2 ^ s := by rw [pow_succ]; ring
    rw [hps, Nat.cast_zero] at f1 f2
    have hah : 1 - (⌊2 ^ s * (1 - ε / 4) ^ j⌋₊ : ℝ) / 2 ^ s = cHat rb ε Wt j := by
      simp only [cHat, schemeShare, schemeEps, hs]
      rw [show (1 : ℝ) - ε / 2 / 2 = 1 - ε / 4 by ring]
    obtain ⟨a1, a2, a3, a4⟩ := hA (cHat rb ε Wt j + ε / 8 * (1 - cHat rb ε Wt j))
    obtain ⟨k0, k1, k2, k3, k4⟩ := ih (j + 1) _ (shInv_upd (j := j) hb)
    rw [pow_succ] at k0 k1 k2 k3 k4
    have hcard : ∑ _e : E, ((1, 0, 0) : Cost) = (Fintype.card E, 0, 0) := by
      simp [sum_const, Prod.smul_mk]
    have hp' : (resp (cHat rb ε Wt j + ε / 8 * (1 - cHat rb ε Wt j)) (cδ rb ε Wt)).val.1 =
        orc (cHat rb ε Wt j + cH rb ε Wt j) (cδ rb ε Wt) := hresp _ _
    simp only [sharesC, CountedQ.val_bind, CountedQ.cost_bind, CountedQ.queries_bind,
      CountedQ.val_lift, CountedQ.cost_lift, CountedQ.queries_lift, val_ops, cost_ops, f1, f2,
      hah, val_sum, cost_sum, hp']
    have hU : ((1 - (cHat rb ε Wt j + 2 * (ε / 8 * (1 - cHat rb ε Wt j)))) *
        (∑ e, m e * orc (cHat rb ε Wt j + cH rb ε Wt j) (cδ rb ε Wt) e -
          cδ rb ε Wt / (ε / 8 * (1 - cHat rb ε Wt j))),
        cHat rb ε Wt j + 2 * (ε / 8 * (1 - cHat rb ε Wt j))) =
        (cU rb m orc ε Wt j, cChk rb ε Wt j) := rfl
    rw [hU]
    refine ⟨by rw [show j + (k + 1) = j + 1 + k by omega]; exact k0, ?_⟩
    simp only [hcard, card_univ, Prod.fst_add, Prod.snd_add, add_one_mul]
    omega

end CountedShares

section CountedPost

variable {E : Type*} [Fintype E]

/-- `z ≤ 2^k` if and only if `⌈log₂ z⌉ ≤ k`, for `z > 0` (not in the paper). -/
lemma le_two_pow_iff {z : ℝ} (hz : 0 < z) (k : ℕ) : z ≤ 2 ^ k ↔ ⌈Real.logb 2 z⌉₊ ≤ k := by
  rw [Nat.ceil_le, Real.logb_le_iff_le_rpow (by norm_num) hz, Real.rpow_natCast]

/-- The counted search for `⌈log₂ z⌉`, `z > 0`, returns it with `2^{⌈log₂ z⌉}`, with
`3⌈log₂ z⌉ + 1` operations (not in the paper). -/
lemma ceilLogC_spec {z : ℝ} (hz : 0 < z) :
    (powSearchC 2 (fun p => z ≤ p) (⌈Real.logb 2 z⌉₊ + 1) 0 1).val =
        (⌈Real.logb 2 z⌉₊, 2 ^ ⌈Real.logb 2 z⌉₊) ∧
      (powSearchC 2 (fun p => z ≤ p) (⌈Real.logb 2 z⌉₊ + 1) 0 1).cost =
        (3 * ⌈Real.logb 2 z⌉₊ + 1, 0, 0) := by
  have h := powSearchC_spec 2 (fun p => z ≤ p) (K := ⌈Real.logb 2 z⌉₊)
    ((le_two_pow_iff hz _).2 le_rfl) (fun i hi h => absurd ((le_two_pow_iff hz i).1 h) (by omega))
    (⌈Real.logb 2 z⌉₊ + 1) 0 (Nat.zero_le _) (by omega)
  obtain ⟨h1, h2⟩ := h
  rw [pow_zero] at h1 h2
  rw [h2, Nat.sub_zero]
  exact ⟨h1, rfl⟩

/-- "`LB ← W̃/(2⌈log₂(2r̄/W̃)⌉)`" (appF-convex.tex:70), counted: `2r̄/W̃` (two operations), "the
number `⌈log₂(2r̄/W̃)⌉`" (appF:144) by repeated doubling, and the quotient (two operations). The
fuel `⌈log₂(2r̄/W̃)⌉ + 1` of the search only makes the recursion terminate: it is computed outside
the model, not counted, and the value and the count do not depend on it (`powSearchC`). -/
def lbC (rb Wt : ℝ) : Counted ℝ :=
  ops 2 (2 * rb / Wt) >>=ᶜ fun z =>
  powSearchC 2 (fun p => z ≤ p) (⌈Real.logb 2 z⌉₊ + 1) 0 1 >>=ᶜ fun L =>
  ops 2 (Wt / (2 * (L.1 : ℝ)))

/-- `lbC` computes `LB` (`cLB`), with `3⌈log₂(2r̄/W̃)⌉ + 5` operations (not in the paper). -/
lemma lbC_spec {rb Wt : ℝ} (hz : 0 < 2 * rb / Wt) :
    (lbC rb Wt).val = cLB rb Wt ∧
      (lbC rb Wt).cost = (3 * ⌈Real.logb 2 (2 * rb / Wt)⌉₊ + 5, 0, 0) := by
  obtain ⟨l1, l2⟩ := ceilLogC_spec hz
  refine ⟨?_, ?_⟩
  · simp only [lbC, Counted.val_bind, val_ops, l1]
    rfl
  · simp only [lbC, Counted.cost_bind, val_ops, cost_ops, l1, l2,
      Prod.mk_add_mk, add_zero, Prod.mk.injEq, and_true]
    ring

/-- "`J ← min{j ∈ ℤ_{≥0} : (1 − ε/4)^j ≤ 1 − ᾱ}`" (appF-convex.tex:71), counted, with
`q = 1 − ε/4`: `1 − ᾱ` (one operation), then repeated multiplication by `q`. The fuel `J + 1` of
the search (`schemeJ`, the parameter `ε` serves only for it) only makes the recursion terminate: it
is computed outside the model, not counted, and the value and the count do not depend on it
(`powSearchC`). -/
def jC (q ε ab : ℝ) : Counted ℕ :=
  ops 1 (1 - ab) >>=ᶜ fun oma =>
  powSearchC q (fun p => p ≤ oma) (schemeJ (ε / 2) ab + 1) 0 1 >>=ᶜ fun J =>
  Counted.ret J.1

/-- `jC` computes `J` (`schemeJ (ε/2) ᾱ`), with `3J + 2` operations (not in the paper). -/
lemma jC_spec {ε ab : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) (hab : ab < 1) :
    (jC (1 - ε / 4) ε ab).val = schemeJ (ε / 2) ab ∧
      (jC (1 - ε / 4) ε ab).cost = (3 * schemeJ (ε / 2) ab + 2, 0, 0) := by
  have hε2 : ε / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hε.1], by linarith [hε.2]⟩
  have hq : 1 - schemeEps (ε / 2) = 1 - ε / 4 := by unfold schemeEps; ring
  obtain ⟨j1, j2⟩ := powSearchC_spec (1 - ε / 4) (fun p => p ≤ 1 - ab)
    (K := schemeJ (ε / 2) ab) (by rw [← hq]; exact schemeJ_mem hε2 hab)
    (fun i hi h => absurd h (not_le.2 (by rw [← hq]; exact lt_of_lt_schemeJ hi)))
    (schemeJ (ε / 2) ab + 1) 0 (Nat.zero_le _) (by omega)
  rw [pow_zero] at j1 j2
  refine ⟨?_, ?_⟩
  · simp only [jC, Counted.val_bind, val_ops, j1, Counted.val_ret]
  · simp only [jC, Counted.cost_bind, val_ops, cost_ops, j1, j2, Counted.cost_ret, Nat.sub_zero]
    ext <;> simp
    ring

/-- "`s ← ⌈log₂(8/(ε(1 − ᾱ)))⌉`" (appF-convex.tex:71), counted, with `2^s`: the argument (three
operations), then repeated doubling. The fuel `s + 1` of the search only makes the recursion
terminate: it is computed outside the model, not counted, and the value and the count do not
depend on it (`powSearchC`). -/
def sC (ε ab : ℝ) : Counted (ℕ × ℝ) :=
  ops 3 (8 / (ε * (1 - ab))) >>=ᶜ fun z =>
  powSearchC 2 (fun p => z ≤ p) (⌈Real.logb 2 z⌉₊ + 1) 0 1

/-- `sC` computes `s` (`schemeS (ε/2) ᾱ`) and `2^s`, with `3s + 4` operations (not in the
paper). -/
lemma sC_spec {ε ab : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) (hab : ab < 1) :
    (sC ε ab).val = (schemeS (ε / 2) ab, 2 ^ schemeS (ε / 2) ab) ∧
      (sC ε ab).cost = (3 * schemeS (ε / 2) ab + 4, 0, 0) := by
  have hz : 0 < 8 / (ε * (1 - ab)) := div_pos (by norm_num) (mul_pos hε.1 (sub_pos.2 hab))
  obtain ⟨s1, s2⟩ := ceilLogC_spec hz
  have hs : ⌈Real.logb 2 (8 / (ε * (1 - ab)))⌉₊ = schemeS (ε / 2) ab := by
    unfold schemeS
    congr 2
    field_simp
    ring
  rw [hs] at s1 s2
  refine ⟨?_, ?_⟩
  · simp only [sC, Counted.val_bind, val_ops, hs, s1]
  · simp only [sC, Counted.cost_bind, val_ops, cost_ops, hs, s2,
      Prod.mk_add_mk, add_zero, Prod.mk.injEq, and_true]
    ring

/-- `alg:convex` after the loop broke with the estimate `W̃` (appF-convex.tex:70-77), counted:
`LB` (`lbC`), "`ᾱ ← 1 − LB/r̄`, `δ ← ε² LB/64`" (five operations), `1 − ε/4` (two operations),
`J` (`jC`), `s` (`sC`), and the shares `j = 0, …, J` (`sharesC`). It returns the record of the
largest `Ũ_j` with its share `α̌_j`. -/
def postC (rb : ℝ) (m : E → ℝ) (resp : ℝ → ℝ → CountedQ ((E → ℝ) × ℝ)) (ε Wt : ℝ) :
    CountedQ (Option (ℝ × ℝ)) :=
  CountedQ.lift (lbC rb Wt) >>=ᵠ fun LB =>
  CountedQ.lift (ops 2 (1 - LB / rb)) >>=ᵠ fun ab =>
  CountedQ.lift (ops 3 (ε ^ 2 * LB / 64)) >>=ᵠ fun δ =>
  CountedQ.lift (ops 2 (1 - ε / 4)) >>=ᵠ fun q =>
  CountedQ.lift (jC q ε ab) >>=ᵠ fun J =>
  CountedQ.lift (sC ε ab) >>=ᵠ fun S =>
  sharesC m resp ε δ q S.2 S.1 (J + 1) 1 none

variable {rb : ℝ} {m : E → ℝ} {orc : ℝ → ℝ → (E → ℝ)}

/-- `postC` returns `Ũ_ĵ` and `α̌_ĵ` for a `ĵ ≤ J` with the largest `Ũ`, with at most `J + 1`
responses and `3⌈log₂(2r̄/W̃)⌉ + 3J + 3s + 18 + (J + 1)(2n + 3s + 18)` further operations (not in
the paper). Its value is computed by rewriting step by step, which keeps the kernel from unfolding
the loop over the shares. -/
lemma postC_spec {resp : ℝ → ℝ → CountedQ ((E → ℝ) × ℝ)}
    (hresp : ∀ a d, (resp a d).val.1 = orc a d) {ε Wt : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1)
    (hrb : 0 < rb) (hWt : 0 < Wt) (hᾱ : cᾱ rb Wt < 1) {A B : ℕ}
    (hA : ∀ a, (resp a (cδ rb ε Wt)).cost.1 ≤ A ∧ (resp a (cδ rb ε Wt)).cost.2.1 ≤ B ∧
      (resp a (cδ rb ε Wt)).cost.2.2 ≤ B ∧ (resp a (cδ rb ε Wt)).queries ≤ B) :
    (∃ jh ≤ schemeJ (ε / 2) (cᾱ rb Wt), (∀ j ≤ schemeJ (ε / 2) (cᾱ rb Wt),
        cU rb m orc ε Wt j ≤ cU rb m orc ε Wt jh) ∧
      (postC rb m resp ε Wt).val = some (cU rb m orc ε Wt jh, cChk rb ε Wt jh)) ∧
    (postC rb m resp ε Wt).cost.1 ≤ 3 * ⌈Real.logb 2 (2 * rb / Wt)⌉₊ +
        3 * schemeJ (ε / 2) (cᾱ rb Wt) + 3 * schemeS (ε / 2) (cᾱ rb Wt) + 18 +
        (schemeJ (ε / 2) (cᾱ rb Wt) + 1) *
          (A + 2 * Fintype.card E + 3 * schemeS (ε / 2) (cᾱ rb Wt) + 18) ∧
    (postC rb m resp ε Wt).cost.2.1 ≤ (schemeJ (ε / 2) (cᾱ rb Wt) + 1) * B ∧
    (postC rb m resp ε Wt).cost.2.2 ≤ (schemeJ (ε / 2) (cᾱ rb Wt) + 1) * B ∧
    (postC rb m resp ε Wt).queries ≤ (schemeJ (ε / 2) (cᾱ rb Wt) + 1) * B := by
  obtain ⟨b1, b2⟩ := lbC_spec (rb := rb) (Wt := Wt) (by positivity)
  obtain ⟨j1, j2⟩ := jC_spec hε hᾱ
  obtain ⟨s1, s2⟩ := sC_spec hε hᾱ
  obtain ⟨sh0, sh1, sh2, sh3, sh4⟩ := sharesC_spec (m := m) hresp hε hA
    (schemeJ (ε / 2) (cᾱ rb Wt) + 1) 0 none (Or.inl ⟨rfl, rfl⟩)
  simp only [pow_zero, zero_add] at sh0 sh1 sh2 sh3 sh4
  have ha : 1 - cLB rb Wt / rb = cᾱ rb Wt := rfl
  have hd : ε ^ 2 * cLB rb Wt / 64 = cδ rb ε Wt := rfl
  -- the value, by rewriting step by step
  have hval : (postC rb m resp ε Wt).val = (sharesC m resp ε (ε ^ 2 * (lbC rb Wt).val / 64)
      (1 - ε / 4) (sC ε (1 - (lbC rb Wt).val / rb)).val.2 (sC ε (1 - (lbC rb Wt).val / rb)).val.1
      ((jC (1 - ε / 4) ε (1 - (lbC rb Wt).val / rb)).val + 1) 1 none).val := by
    rw [postC, CountedQ.val_bind, CountedQ.val_lift]
    rw [CountedQ.val_bind, CountedQ.val_lift, val_ops]
    rw [CountedQ.val_bind, CountedQ.val_lift, val_ops]
    rw [CountedQ.val_bind, CountedQ.val_lift, val_ops]
    rw [CountedQ.val_bind, CountedQ.val_lift]
    rw [CountedQ.val_bind, CountedQ.val_lift]
  rw [b1, ha, hd, j1, s1] at hval
  dsimp only at hval
  rw [← hval] at sh0
  refine ⟨?_, ?_⟩
  · rcases sh0 with ⟨h0, -⟩ | ⟨jh, hjh, hb, hmax⟩
    · omega
    · exact ⟨jh, by omega, fun j hj => hmax j (by omega), hb⟩
  -- the costs
  have hcost : (postC rb m resp ε Wt).cost = (lbC rb Wt).cost + ((2, 0, 0) + ((3, 0, 0) +
      ((2, 0, 0) + ((jC (1 - ε / 4) ε (cᾱ rb Wt)).cost + ((sC ε (cᾱ rb Wt)).cost +
        (sharesC m resp ε (cδ rb ε Wt) (1 - ε / 4) (2 ^ schemeS (ε / 2) (cᾱ rb Wt))
          (schemeS (ε / 2) (cᾱ rb Wt)) (schemeJ (ε / 2) (cᾱ rb Wt) + 1) 1 none).cost))))) := by
    simp only [postC, CountedQ.cost_bind, CountedQ.val_lift, CountedQ.cost_lift, val_ops,
      cost_ops, b1, ha, hd, j1, s1]
  have hq : (postC rb m resp ε Wt).queries = (sharesC m resp ε (cδ rb ε Wt) (1 - ε / 4)
      (2 ^ schemeS (ε / 2) (cᾱ rb Wt)) (schemeS (ε / 2) (cᾱ rb Wt))
      (schemeJ (ε / 2) (cᾱ rb Wt) + 1) 1 none).queries := by
    simp only [postC, CountedQ.queries_bind, CountedQ.val_lift, CountedQ.queries_lift, val_ops,
      b1, ha, hd, j1, s1, zero_add]
  rw [hcost, hq, b2, j2, s2]
  simp only [Prod.fst_add, Prod.snd_add]
  refine ⟨?_, ?_, ?_, sh4⟩ <;> omega

end CountedPost

section CountedScheme

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- With `w`, the welfare loop ends by the round `⌊log₂(3r̄/w)⌋ + 1`, where `d < w/3` (not in the
paper: it bounds the rounds of the counted loop). -/
lemma loopD_floor_lt {rb w : ℝ} (hrb : 0 < rb) (hw : 0 < w) :
    loopD rb (⌊Real.logb 2 (3 * rb / w)⌋₊ + 1) < w / 3 := by
  set L := Real.logb 2 (3 * rb / w)
  have hpos : 0 < 3 * rb / w := by positivity
  have h1 : (3 * rb / w) < 2 ^ (⌊L⌋₊ + 1) := by
    have := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
      (show L < ((⌊L⌋₊ + 1 : ℕ) : ℝ) by push_cast; exact Nat.lt_floor_add_one L)
    rwa [Real.rpow_logb (by norm_num) (by norm_num) hpos, Real.rpow_natCast] at this
  unfold loopD
  rw [div_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ hw] at h1
  linarith

omit [DecidableEq E] in
/-- The round in which the loop with `w` ends is at most `⌊log₂(3r̄/w)⌋ + 1` (not in the paper). -/
lemma loopRound_le {rb : ℝ} {m : E → ℝ} {c : (E → ℝ) → ℝ} {orc : ℝ → ℝ → (E → ℝ)} {w : ℝ}
    (hrb : 0 < rb) (hw : 0 < w) {K : ℕ}
    (hK : ∀ k < K, ¬ Brk rb m c orc k ∧ ¬ WTest rb (some w) k) :
    K ≤ ⌊Real.logb 2 (3 * rb / w)⌋₊ + 1 := by
  by_contra hlt
  exact (hK _ (not_le.1 hlt)).2 ⟨w, rfl, loopD_floor_lt hrb hw⟩

/-- `alg:convex` with `w` (appF-convex.tex:58-79), counted, with `lem:ellipsoid` as the oracle
("Run `alg:convex` with `w` and with `lem:ellipsoid` as the oracle", appF:144): the preparation of
the ellipsoid method (`prepC`: "the `n + 1` evaluations of `f` for the coordinate bounds `f({e})`
used by the ellipsoid method and for `f(E)`"), the welfare loop (`loopC`) with the responses of the
counted ellipsoid method (`respC`), and after a break `postC`. It returns `none` for "`W = 0`"
and `some (b, Ũ)` otherwise. The fuel `⌊log₂(3r̄/w)⌋ + 2` of the loop only makes Lean's recursion
terminate: it is computed outside the model, is not counted and is not part of `alg:convex`; the
loop ends before it runs out (`loopRound_le`), so the value and the counts do not depend on it.
`respC` takes the iteration number `t(δ) = ellipsoidIters n M δ` of each response from its
definition at no cost (computing it needs `ln` and `⌈·⌉`, which the model lacks, and the paper
does not count it). -/
def convexC (f : Finset E → ℝ) (m : E → ℝ) (c : (E → ℝ) → ℝ) (g : (E → ℝ) → E → ℝ) (G rb : ℝ)
    {σ : Type*} (Ell : EllMethod {e // e ∈ posElems f} σ) (ε w : ℝ) :
    CountedQ (Option (ℝ × ℝ)) :=
  CountedQ.lift (prepC f G rb) >>=ᵠ fun P =>
  loopC m (respC f m c g Ell P) w (⌊Real.logb 2 (3 * rb / w)⌋₊ + 2) rb >>=ᵠ fun r =>
  match r with
  | Sum.inl Wt => postC rb m (respC f m c g Ell P) ε Wt >>=ᵠ fun best =>
      CountedQ.ret (best.map fun p => (p.2, p.1))
  | Sum.inr _ => CountedQ.ret none

variable {f : Finset E → ℝ} {m : E → ℝ} {c : (E → ℝ) → ℝ} {g : (E → ℝ) → E → ℝ} {G rb : ℝ}
  {orc : ℝ → ℝ → (E → ℝ)} {σ : Type*} {Ell : EllMethod {e // e ∈ posElems f} σ}

/-- The responses of the counted ellipsoid method as the oracle of the scheme (not in the paper):
if they are the responses `orc α δ`, they come with their costs `c(orc α δ)` (`respC_spec`), and
with `t ≤ T` iterations they make at most `T` minimizations, queries and evaluations of `f` and at
most `cE n² + 2 + T (cE n² + 9n + 4)` operations (`respC_cost`). -/
lemma resp_facts (h : PolySetting f m c g G rb) {cE : ℕ} (hU : Ell.Cited cE)
    (horcC : ∀ α δ, orc α δ = (respC f m c g Ell (posElems f, rb + G * f univ) α δ).val.1) :
    (∀ α δ, (respC f m c g Ell (posElems f, rb + G * f univ) α δ).val = (orc α δ, c (orc α δ))) ∧
    ∀ {T : ℕ} α δ, ellipsoidIters (Fintype.card E) (rb + G * f univ) δ ≤ T →
      (respC f m c g Ell (posElems f, rb + G * f univ) α δ).cost.1 ≤
          cE * Fintype.card E ^ 2 + 2 + T * (cE * Fintype.card E ^ 2 + 9 * Fintype.card E + 4) ∧
        (respC f m c g Ell (posElems f, rb + G * f univ) α δ).cost.2.1 ≤ T ∧
        (respC f m c g Ell (posElems f, rb + G * f univ) α δ).cost.2.2 ≤ T ∧
        (respC f m c g Ell (posElems f, rb + G * f univ) α δ).queries ≤ T := by
  refine ⟨fun α δ => ?_, fun α δ hT => ?_⟩
  · obtain ⟨-, h2, -⟩ := respC_spec h Ell (rb + G * f univ) α δ
    have h1 := (horcC α δ).symm
    exact Prod.ext h1 (h2.trans (congrArg c h1))
  · obtain ⟨k1, k2, k3, k4⟩ := respC_cost (m := m) (c := c) (g := g) hU
      (posElems f, rb + G * f univ) α δ
    have := Nat.mul_le_mul_right (cE * Fintype.card E ^ 2 + 9 * Fintype.card E + 4) hT
    exact ⟨by dsimp only at k1; omega, k2.trans hT, k3.trans hT, k4.trans hT⟩

/-- If the loop breaks in round `K`, `convexC` returns the share `b = α̌_ĵ` and `Ũ = Ũ_ĵ` of
`Returns`, with the `K + 1` responses of the loop and the `J + 1` responses at the shares: if each
response takes at most `T` iterations, at most `T` minimizations, queries and evaluations of `f`
each, and the operations of `prepC`, `loopC_spec` and `postC_spec` (not in the paper). -/
lemma convexC_breaks (h : PolySetting f m c g G rb) {cE : ℕ} (hU : Ell.Cited cE)
    (horcC : ∀ α δ, orc α δ = (respC f m c g Ell (posElems f, rb + G * f univ) α δ).val.1)
    {ε w : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) (hw : 0 < w) {K : ℕ}
    (hK : LoopBreaks rb m c orc (some w) K) (hWt : 0 < loopW rb m c orc K)
    (hᾱ : cᾱ rb (loopW rb m c orc K) < 1) {T : ℕ}
    (hT : ∀ k ≤ K, ellipsoidIters (Fintype.card E) (rb + G * f univ) (loopD rb k) ≤ T)
    (hTδ : ellipsoidIters (Fintype.card E) (rb + G * f univ) (cδ rb ε (loopW rb m c orc K)) ≤ T) :
    (∃ jh ≤ schemeJ (ε / 2) (cᾱ rb (loopW rb m c orc K)),
      (∀ j ≤ schemeJ (ε / 2) (cᾱ rb (loopW rb m c orc K)),
        cU rb m orc ε (loopW rb m c orc K) j ≤ cU rb m orc ε (loopW rb m c orc K) jh) ∧
      (convexC f m c g G rb Ell ε w).val =
        some (cChk rb ε (loopW rb m c orc K) jh, cU rb m orc ε (loopW rb m c orc K) jh)) ∧
    (convexC f m c g G rb Ell ε w).cost.1 ≤ Fintype.card E + 2 +
        (K + 1) * (cE * Fintype.card E ^ 2 + 2 +
          T * (cE * Fintype.card E ^ 2 + 9 * Fintype.card E + 4) + 2 * Fintype.card E + 6) +
        (3 * ⌈Real.logb 2 (2 * rb / loopW rb m c orc K)⌉₊ +
          3 * schemeJ (ε / 2) (cᾱ rb (loopW rb m c orc K)) +
          3 * schemeS (ε / 2) (cᾱ rb (loopW rb m c orc K)) + 18 +
          (schemeJ (ε / 2) (cᾱ rb (loopW rb m c orc K)) + 1) *
            (cE * Fintype.card E ^ 2 + 2 +
              T * (cE * Fintype.card E ^ 2 + 9 * Fintype.card E + 4) + 2 * Fintype.card E +
              3 * schemeS (ε / 2) (cᾱ rb (loopW rb m c orc K)) + 18)) ∧
    (convexC f m c g G rb Ell ε w).cost.2.1 ≤
      (K + 1) * T + (schemeJ (ε / 2) (cᾱ rb (loopW rb m c orc K)) + 1) * T ∧
    (convexC f m c g G rb Ell ε w).cost.2.2 ≤ Fintype.card E + 1 +
      ((K + 1) * T + (schemeJ (ε / 2) (cᾱ rb (loopW rb m c orc K)) + 1) * T) ∧
    (convexC f m c g G rb Ell ε w).queries ≤
      (K + 1) * T + (schemeJ (ε / 2) (cᾱ rb (loopW rb m c orc K)) + 1) * T := by
  have hrb := h.rbar_pos
  obtain ⟨hval, hcost⟩ := resp_facts h hU horcC
  set resp := respC f m c g Ell (posElems f, rb + G * f univ) with hresp
  set Wt := loopW rb m c orc K with hWtdef
  -- the loop breaks in round `K`, within the rounds of the counted loop
  have hKle := loopRound_le hrb hw hK.2
  obtain ⟨l0, -, l2, l3, l4, l5⟩ := loopC_spec (resp := resp) (fun d => hval 1 d) hK.2
    (Or.inl hK.1) (fun k hk => hcost 1 (loopD rb k) (hT k hk))
    (⌊Real.logb 2 (3 * rb / w)⌋₊ + 2) 0 (Nat.zero_le _) (by omega)
  have h0 : loopD rb 0 = rb := by simp [loopD]
  rw [h0] at l0 l2 l3 l4 l5
  have hloop := l0 hK.1
  -- the part after the loop
  obtain ⟨⟨jh, hjh, hmax, hpost⟩, p1, p2, p3, p4⟩ := postC_spec (m := m) (resp := resp)
    (fun a d => (congrArg Prod.fst (hval a d)).trans rfl) hε hrb hWt hᾱ
    (fun a => hcost a (cδ rb ε Wt) hTδ)
  -- the value
  have hv : (convexC f m c g G rb Ell ε w).val = some (cChk rb ε Wt jh, cU rb m orc ε Wt jh) := by
    rw [convexC, CountedQ.val_bind, CountedQ.val_lift, prepC_val]
    rw [CountedQ.val_bind, hloop]
    dsimp only
    rw [CountedQ.val_bind, hpost]
    rfl
  refine ⟨⟨jh, hjh, hmax, hv⟩, ?_⟩
  -- the costs
  have hc : (convexC f m c g G rb Ell ε w).cost = (prepC f G rb).cost +
      ((loopC m resp w (⌊Real.logb 2 (3 * rb / w)⌋₊ + 2) rb).cost +
        ((postC rb m resp ε Wt).cost + 0)) := by
    rw [convexC, CountedQ.cost_bind, CountedQ.cost_lift, CountedQ.val_lift, prepC_val]
    rw [CountedQ.cost_bind, hloop]
    dsimp only
    rw [CountedQ.cost_bind]
    rfl
  have hq : (convexC f m c g G rb Ell ε w).queries =
      (loopC m resp w (⌊Real.logb 2 (3 * rb / w)⌋₊ + 2) rb).queries +
        ((postC rb m resp ε Wt).queries + 0) := by
    rw [convexC, CountedQ.queries_bind, CountedQ.queries_lift, CountedQ.val_lift, prepC_val,
      zero_add]
    rw [CountedQ.queries_bind, hloop]
    dsimp only
    rw [CountedQ.queries_bind]
    rfl
  rw [hc, hq, prepC_cost]
  simp only [Prod.fst_add, Prod.snd_add, add_zero, Nat.sub_zero] at l2 l3 l4 l5 ⊢
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- If the loop returns "`W = 0`" in round `K`, `convexC` returns `none`, with the `K + 1`
responses of the loop (not in the paper). -/
lemma convexC_zero (h : PolySetting f m c g G rb) {cE : ℕ} (hU : Ell.Cited cE)
    (horcC : ∀ α δ, orc α δ = (respC f m c g Ell (posElems f, rb + G * f univ) α δ).val.1)
    {ε w : ℝ} (hw : 0 < w) {K : ℕ} (hK : LoopZero rb m c orc (some w) K) {T : ℕ}
    (hT : ∀ k ≤ K, ellipsoidIters (Fintype.card E) (rb + G * f univ) (loopD rb k) ≤ T) :
    (convexC f m c g G rb Ell ε w).val = none ∧
    (convexC f m c g G rb Ell ε w).cost.1 ≤ Fintype.card E + 2 +
        (K + 1) * (cE * Fintype.card E ^ 2 + 2 +
          T * (cE * Fintype.card E ^ 2 + 9 * Fintype.card E + 4) + 2 * Fintype.card E + 6) ∧
    (convexC f m c g G rb Ell ε w).cost.2.1 ≤ (K + 1) * T ∧
    (convexC f m c g G rb Ell ε w).cost.2.2 ≤ Fintype.card E + 1 + (K + 1) * T ∧
    (convexC f m c g G rb Ell ε w).queries ≤ (K + 1) * T := by
  have hrb := h.rbar_pos
  obtain ⟨hval, hcost⟩ := resp_facts h hU horcC
  set resp := respC f m c g Ell (posElems f, rb + G * f univ) with hresp
  -- the loop returns "`W = 0`" in round `K`, within the rounds of the counted loop
  have hKle := loopRound_le hrb hw hK.2.2
  obtain ⟨-, l1, l2, l3, l4, l5⟩ := loopC_spec (resp := resp) (fun d => hval 1 d) hK.2.2
    (Or.inr hK.2.1) (fun k hk => hcost 1 (loopD rb k) (hT k hk))
    (⌊Real.logb 2 (3 * rb / w)⌋₊ + 2) 0 (Nat.zero_le _) (by omega)
  have h0 : loopD rb 0 = rb := by simp [loopD]
  rw [h0] at l1 l2 l3 l4 l5
  have hloop := l1 hK.1
  have hv : (convexC f m c g G rb Ell ε w).val = none := by
    rw [convexC, CountedQ.val_bind, CountedQ.val_lift, prepC_val]
    rw [CountedQ.val_bind, hloop]
    rfl
  have hc : (convexC f m c g G rb Ell ε w).cost = (prepC f G rb).cost +
      ((loopC m resp w (⌊Real.logb 2 (3 * rb / w)⌋₊ + 2) rb).cost + 0) := by
    rw [convexC, CountedQ.cost_bind, CountedQ.cost_lift, CountedQ.val_lift, prepC_val]
    rw [CountedQ.cost_bind, hloop]
    rfl
  have hq : (convexC f m c g G rb Ell ε w).queries =
      (loopC m resp w (⌊Real.logb 2 (3 * rb / w)⌋₊ + 2) rb).queries + 0 := by
    rw [convexC, CountedQ.queries_bind, CountedQ.queries_lift, CountedQ.val_lift, prepC_val,
      zero_add]
    rw [CountedQ.queries_bind, hloop]
    rfl
  refine ⟨hv, ?_⟩
  rw [hc, hq, prepC_cost]
  simp only [Prod.fst_add, Prod.snd_add, add_zero, Nat.sub_zero] at l2 l3 l4 l5 ⊢
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

end CountedScheme

section CountBounds

/-- `ln(3r̄/w) ≤ ln(M/w) + 2` for `0 < w ≤ r̄ ≤ M` (not in the paper). -/
lemma log_three_le {R M w : ℝ} (hw : 0 < w) (hwR : w ≤ R) (hRM : R ≤ M) :
    Real.log (3 * R / w) ≤ Real.log (M / w) + 2 := by
  have hR : 0 < R := hw.trans_le hwR
  have h3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    linarith
  rw [mul_div_assoc, Real.log_mul (by norm_num) (by positivity)]
  have := Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hRM hw.le)
  linarith

/-- `ln(M/w) ≥ 0` for `0 < w ≤ M` (not in the paper). -/
lemma log_div_nonneg {M w : ℝ} (hw : 0 < w) (hwM : w ≤ M) : 0 ≤ Real.log (M / w) :=
  Real.log_nonneg (by rw [le_div_iff₀ hw]; linarith)

/-- `1/ln 2 ≤ 3/2` (not in the paper). -/
lemma inv_log_two_le : 1 / Real.log 2 ≤ 3 / 2 := by
  have := Real.log_two_gt_d9
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-- The iteration bound of (T5) as a polynomial,
`⌈32 n² ln(2nM/(εw))⌉ ≤ 32 n² (2n + 1/ε + ln(M/w)) + 1` (not in the paper: `ln(2n) ≤ 2n` and
`ln(1/ε) ≤ 1/ε`). -/
lemma iters_poly {n : ℕ} {M w ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) (hw : 0 < w) (hwM : w ≤ M) :
    (⌈32 * (n : ℝ) ^ 2 * Real.log (2 * n * M / (ε * w))⌉₊ : ℝ) ≤
      32 * (n : ℝ) ^ 2 * (2 * n + 1 / ε + Real.log (M / w)) + 1 := by
  have hX := log_div_nonneg hw hwM
  have hε0 := hε.1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hM : 0 < M := hw.trans_le hwM
  -- `ln(2nM/(εw)) = ln(2n) + ln(1/ε) + ln(M/w) ≤ 2n + 1/ε + ln(M/w)`
  have e : 2 * (n : ℝ) * M / (ε * w) = (2 * n) * (1 / ε) * (M / w) := by field_simp
  have hlog : Real.log (2 * n * M / (ε * w)) ≤ 2 * n + 1 / ε + Real.log (M / w) := by
    rw [e, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity)]
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * n by positivity)
    have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / ε by positivity)
    linarith
  have hY : 0 ≤ 32 * (n : ℝ) ^ 2 * (2 * n + 1 / ε + Real.log (M / w)) := by positivity
  calc (⌈32 * (n : ℝ) ^ 2 * Real.log (2 * n * M / (ε * w))⌉₊ : ℝ)
      ≤ ⌈32 * (n : ℝ) ^ 2 * (2 * n + 1 / ε + Real.log (M / w))⌉₊ := by
        exact_mod_cast Nat.ceil_mono (mul_le_mul_of_nonneg_left hlog (by positivity))
    _ ≤ _ := (Nat.ceil_lt_add_one hY).le

/-- The bits `s` of the shares as a polynomial (not in the paper, which states
`s = O(log(1/(ε(1 − ᾱ))))` and `ln(1/(1 − ᾱ)) ≤ 2 ln(3r̄/w)`, appF-convex.tex:144): from
`s ≤ 3 + log₂(2/ε) + log₂(1/(1 − ᾱ))` (`fptas_aux` for the accuracy `ε/2`) and
`ln(3r̄/w) ≤ ln(M/w) + 2`, `s ≤ 2/ε + 3 ln(M/w) + 10`. -/
lemma bits_poly {ε ᾱ R M w : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) (hᾱ : ᾱ ∈ Ico (0 : ℝ) 1)
    (hw : 0 < w) (hwR : w ≤ R) (hRM : R ≤ M)
    (hlog : Real.log (1 / (1 - ᾱ)) ≤ 2 * Real.log (3 * R / w)) :
    (schemeS (ε / 2) ᾱ : ℝ) ≤ 2 / ε + 3 * Real.log (M / w) + 10 := by
  have hε2 : ε / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hε.1], by linarith [hε.2]⟩
  obtain ⟨-, -, hs, -⟩ := fptas_aux hε2 hᾱ
  have hε0 := hε.1
  have hl2 := Real.log_two_gt_d9
  have hl2' : 0 < Real.log 2 := by linarith
  have hinv := inv_log_two_le
  have h3 := log_three_le hw hwR hRM
  -- `log₂(2/ε) = 1 + ln(1/ε)/ln 2 ≤ 1 + (3/2)(1/ε)`
  have hA : Real.logb 2 (1 / (ε / 2)) ≤ 1 + 3 / 2 * (1 / ε) := by
    have e : 1 / (ε / 2) = 2 * (1 / ε) := by field_simp
    rw [e, Real.logb, Real.log_mul (by norm_num) (by positivity), add_div,
      div_self hl2'.ne']
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / ε by positivity)
    have h0 : 0 ≤ Real.log (1 / ε) := Real.log_nonneg (by rw [le_div_iff₀ hε0]; linarith [hε.2])
    have : Real.log (1 / ε) / Real.log 2 ≤ 3 / 2 * Real.log (1 / ε) := by
      rw [div_le_iff₀ hl2']
      nlinarith
    linarith
  -- `log₂(1/(1 − ᾱ)) = ln(1/(1 − ᾱ))/ln 2 ≤ (3/2) · 2 (ln(M/w) + 2)`
  have hB : Real.logb 2 (1 / (1 - ᾱ)) ≤ 3 * (Real.log (M / w) + 2) := by
    have h0 : 0 ≤ Real.log (1 / (1 - ᾱ)) :=
      Real.log_nonneg (by rw [le_div_iff₀ (by linarith [hᾱ.2])]; linarith [hᾱ.1])
    rw [Real.logb, div_le_iff₀ hl2']
    nlinarith
  have hε1 : 3 / 2 * (1 / ε) ≤ 2 / ε := by
    rw [show 2 / ε = 2 * (1 / ε) by ring]
    have : 0 < 1 / ε := by positivity
    linarith
  linarith

/-- The arithmetic of the totals (not in the paper): the counts of a run with `K + 1 + (J + 1)`
responses of at most `T'` iterations each, with `s` bits for the shares, `L = ⌈log₂(2r̄/W̃)⌉` and
`J` the index of the last share, below the bounds `R`, `T`, `S`, `L'`, `J'` of `K + 1 + (J + 1)`,
`T'`, `s`, `L`, `J`. -/
lemma totals_le {n cE K J s L T' mins qs evs ops : ℕ} {R T S L' J' : ℝ}
    (hmins : mins ≤ (K + 1) * T' + (J + 1) * T') (hqs : qs ≤ (K + 1) * T' + (J + 1) * T')
    (hevs : evs ≤ n + 1 + ((K + 1) * T' + (J + 1) * T'))
    (hops : ops ≤ n + 2 + (K + 1) * (cE * n ^ 2 + 2 + T' * (cE * n ^ 2 + 9 * n + 4) + 2 * n + 6) +
      (3 * L + 3 * J + 3 * s + 18 +
        (J + 1) * (cE * n ^ 2 + 2 + T' * (cE * n ^ 2 + 9 * n + 4) + 2 * n + 3 * s + 18)))
    (hR : ((K + 1 + (J + 1) : ℕ) : ℝ) ≤ R) (hT : (T' : ℝ) ≤ T) (hS : (s : ℝ) ≤ S)
    (hL : (L : ℝ) ≤ L') (hJ : (J : ℝ) ≤ J') :
    (mins : ℝ) ≤ R * T ∧ (qs : ℝ) ≤ R * T ∧ (evs : ℝ) ≤ n + 1 + R * T ∧
      (ops : ℝ) ≤ n + 2 + R * (cE * n ^ 2 + 2 + T * (cE * n ^ 2 + 9 * n + 4) + 2 * n + 3 * S + 18) +
        3 * L' + 3 * J' + 3 * S + 18 := by
  have hR0 : (0 : ℝ) ≤ R := (Nat.cast_nonneg _).trans hR
  have hN : ((K + 1) * T' + (J + 1) * T' : ℕ) = (K + 1 + (J + 1)) * T' := by ring
  have hRT : (((K + 1 + (J + 1)) * T' : ℕ) : ℝ) ≤ R * T := by
    push_cast
    exact mul_le_mul (by exact_mod_cast hR) hT (Nat.cast_nonneg _) hR0
  rw [hN] at hmins hqs hevs
  refine ⟨(by exact_mod_cast hmins : (mins : ℝ) ≤ _).trans hRT,
    (by exact_mod_cast hqs : (qs : ℝ) ≤ _).trans hRT, ?_, ?_⟩
  · have : (evs : ℝ) ≤ n + 1 + (((K + 1 + (J + 1)) * T' : ℕ) : ℝ) := by exact_mod_cast hevs
    linarith
  · -- the `K + 1` rounds of the loop cost at most as much as a share
    have hops' : ops ≤ n + 2 + (K + 1 + (J + 1)) *
        (cE * n ^ 2 + 2 + T' * (cE * n ^ 2 + 9 * n + 4) + 2 * n + 3 * s + 18) +
        (3 * L + 3 * J + 3 * s + 18) := by
      have := Nat.mul_le_mul_left (K + 1) (show cE * n ^ 2 + 2 + T' * (cE * n ^ 2 + 9 * n + 4) +
        2 * n + 6 ≤ cE * n ^ 2 + 2 + T' * (cE * n ^ 2 + 9 * n + 4) + 2 * n + 3 * s + 18 by omega)
      nlinarith
    have hc : (ops : ℝ) ≤ n + 2 + ((K + 1 + (J + 1) : ℕ) : ℝ) *
        (cE * n ^ 2 + 2 + T' * (cE * n ^ 2 + 9 * n + 4) + 2 * n + 3 * s + 18) +
        (3 * L + 3 * J + 3 * s + 18) := by exact_mod_cast hops'
    refine hc.trans ?_
    have hA : (cE : ℝ) * n ^ 2 + 2 + T' * (cE * n ^ 2 + 9 * n + 4) + 2 * n + 3 * s + 18 ≤
        cE * n ^ 2 + 2 + T * (cE * n ^ 2 + 9 * n + 4) + 2 * n + 3 * S + 18 := by
      gcongr
    have hA0 : (0 : ℝ) ≤ cE * n ^ 2 + 2 + T' * (cE * n ^ 2 + 9 * n + 4) + 2 * n + 3 * s + 18 := by
      positivity
    have := mul_le_mul hR hA hA0 hR0
    linarith

/-- `⌈log₂ z⌉ ≤ (3/2) ln(M/w) + 4` for `0 < z ≤ 3r̄/w` and `0 < w ≤ r̄ ≤ M` (not in the paper). -/
lemma ceil_logb_poly {R M w z : ℝ} (hw : 0 < w) (hwR : w ≤ R) (hRM : R ≤ M) (hz : 0 < z)
    (hzle : z ≤ 3 * R / w) : (⌈Real.logb 2 z⌉₊ : ℝ) ≤ 3 / 2 * Real.log (M / w) + 4 := by
  have h3 : 1 ≤ 3 * R / w := by rw [le_div_iff₀ hw]; linarith
  have hl0 : 0 ≤ Real.logb 2 (3 * R / w) := Real.logb_nonneg one_lt_two h3
  have hl : (⌈Real.logb 2 z⌉₊ : ℝ) ≤ ⌈Real.logb 2 (3 * R / w)⌉₊ := by
    exact_mod_cast Nat.ceil_mono (Real.logb_le_logb_of_le (by norm_num) hz hzle)
  have hc := Nat.ceil_lt_add_one hl0
  have hlog0 : 0 ≤ Real.log (3 * R / w) := Real.log_nonneg h3
  have hb : Real.logb 2 (3 * R / w) ≤ 3 / 2 * Real.log (3 * R / w) := by
    have hl2 := Real.log_two_gt_d9
    rw [Real.logb, div_le_iff₀ (by linarith)]
    nlinarith
  have := log_three_le hw hwR hRM
  linarith

/-- The arithmetic of the totals when the algorithm returns "`W = 0`" (not in the paper). -/
lemma totals_le_zero {n cE K T' mins qs evs ops : ℕ} {R T S L' J' : ℝ}
    (hmins : mins ≤ (K + 1) * T') (hqs : qs ≤ (K + 1) * T') (hevs : evs ≤ n + 1 + (K + 1) * T')
    (hops : ops ≤ n + 2 + (K + 1) * (cE * n ^ 2 + 2 + T' * (cE * n ^ 2 + 9 * n + 4) + 2 * n + 6))
    (hR : ((K + 1 : ℕ) : ℝ) ≤ R) (hT : (T' : ℝ) ≤ T) (hS : 0 ≤ S) (hL : 0 ≤ L') (hJ : 0 ≤ J') :
    (mins : ℝ) ≤ R * T ∧ (qs : ℝ) ≤ R * T ∧ (evs : ℝ) ≤ n + 1 + R * T ∧
      (ops : ℝ) ≤ n + 2 + R * (cE * n ^ 2 + 2 + T * (cE * n ^ 2 + 9 * n + 4) + 2 * n + 3 * S + 18) +
        3 * L' + 3 * J' + 3 * S + 18 := by
  have hR0 : (0 : ℝ) ≤ R := (Nat.cast_nonneg _).trans hR
  have hRT : (((K + 1) * T' : ℕ) : ℝ) ≤ R * T := by
    push_cast
    exact mul_le_mul (by exact_mod_cast hR) hT (Nat.cast_nonneg _) hR0
  refine ⟨(by exact_mod_cast hmins : (mins : ℝ) ≤ _).trans hRT,
    (by exact_mod_cast hqs : (qs : ℝ) ≤ _).trans hRT, ?_, ?_⟩
  · have : (evs : ℝ) ≤ n + 1 + (((K + 1) * T' : ℕ) : ℝ) := by exact_mod_cast hevs
    linarith
  · have hc : (ops : ℝ) ≤ n + 2 + ((K + 1 : ℕ) : ℝ) *
        (cE * n ^ 2 + 2 + T' * (cE * n ^ 2 + 9 * n + 4) + 2 * n + 6) := by exact_mod_cast hops
    refine hc.trans ?_
    have hA : (cE : ℝ) * n ^ 2 + 2 + T' * (cE * n ^ 2 + 9 * n + 4) + 2 * n + 6 ≤
        cE * n ^ 2 + 2 + T * (cE * n ^ 2 + 9 * n + 4) + 2 * n + 3 * S + 18 := by
      have : (cE : ℝ) * n ^ 2 + 2 + T' * (cE * n ^ 2 + 9 * n + 4) ≤
          cE * n ^ 2 + 2 + T * (cE * n ^ 2 + 9 * n + 4) := by gcongr
      linarith
    have hA0 : (0 : ℝ) ≤ cE * n ^ 2 + 2 + T' * (cE * n ^ 2 + 9 * n + 4) + 2 * n + 6 := by
      positivity
    have := mul_le_mul hR hA hA0 hR0
    linarith

end CountBounds

end Counts

/-! ### `thm:convexfptas` -/

section Fptas

/-- The proof of `thm:convexfptas`, (T4) (appF-convex.tex:144): "`w/6 ≥ δ₀`" for
`δ₀ = ε² w/(192 ⌈log₂(3r̄/w)⌉)`. -/
lemma delta0_le {R w ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) (hw : 0 < w) (hwR : w ≤ R) :
    ε ^ 2 * w / (192 * ⌈Real.logb 2 (3 * R / w)⌉₊) ≤ w / 6 := by
  have hc := one_le_ceil_logb hw hwR
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith [hε.1, hε.2]
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [sq_nonneg ε]

/-- The proof of `thm:convexfptas`, (T5) (appF-convex.tex:144): "With `M := r̄ + G f(E) ≥ w` and
`⌈log₂(3r̄/w)⌉ ≤ 3M/w`, we get `ln(M/δ₀) ≤ ln(576/ε²) + 2 ln(M/w)`", for
`δ₀ = ε² w/(192 ⌈log₂(3r̄/w)⌉)` (here for any `M ≥ r̄`). -/
lemma log_div_delta0_le {R M w ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) (hw : 0 < w) (hwR : w ≤ R)
    (hRM : R ≤ M) :
    Real.log (M / (ε ^ 2 * w / (192 * ⌈Real.logb 2 (3 * R / w)⌉₊))) ≤
      Real.log (576 / ε ^ 2) + 2 * Real.log (M / w) := by
  have hM : 0 < M := by linarith
  have hε0 := hε.1
  set C : ℝ := (⌈Real.logb 2 (3 * R / w)⌉₊ : ℝ) with hCdef
  have hC1 : 1 ≤ C := one_le_ceil_logb hw hwR
  -- "`M ≥ w` and `⌈log₂(3r̄/w)⌉ ≤ 3M/w`"
  have hMw : w ≤ M := by linarith
  have hC : C ≤ 3 * M / w :=
    (ceil_logb_le (by rw [le_div_iff₀ hw]; linarith)).trans
      (div_le_div_of_nonneg_right (by linarith) hw.le)
  have hCw : C * w ≤ 3 * M := by rwa [le_div_iff₀ hw] at hC
  rw [← Real.log_rpow (div_pos hM hw), ← Real.log_mul (by positivity) (by positivity)]
  apply Real.log_le_log (by positivity)
  rw [show (M / w) ^ (2 : ℝ) = (M / w) ^ 2 by norm_cast]
  have e1 : M / (ε ^ 2 * w / (192 * C)) = 192 * C * M / (ε ^ 2 * w) := by field_simp
  have e2 : 576 / ε ^ 2 * (M / w) ^ 2 = 576 * M ^ 2 / (ε ^ 2 * w ^ 2) := by field_simp
  rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
  have hk : 0 ≤ 192 * M * ε ^ 2 * w := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hCw hk]

/-- The proof of `thm:convexfptas`, (T5) (appF-convex.tex:144): "so each response takes
`O(n² log(2nM/(εw)))` iterations by `lem:ellipsoid`". For the iteration number
`t(δ) = ⌈2n² ln(2n^{3/2} M/δ)⌉` of `lem:ellipsoid` (`ellipsoidIters`) and every precision `δ ≥ δ₀`,
`t(δ) ≤ ⌈32 n² ln(2nM/(εw))⌉` (not in the paper: it states the `O`; the constant `32` is ours).
This bounds the formula `t(δ)` only: that the ellipsoid method computes a `δ`-optimal response in
`t(δ)` iterations is the claim of `lem:ellipsoid`, which is not formalised. -/
lemma ellipsoidIters_le {n : ℕ} (hn : 1 ≤ n) {R M w ε δ : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1)
    (hw : 0 < w) (hwR : w ≤ R) (hRM : R ≤ M)
    (hδ : ε ^ 2 * w / (192 * ⌈Real.logb 2 (3 * R / w)⌉₊) ≤ δ) :
    ellipsoidIters n M δ ≤ ⌈32 * (n : ℝ) ^ 2 * Real.log (2 * n * M / (ε * w))⌉₊ := by
  have hε0 := hε.1
  have hε1 := hε.2
  have hM : 0 < M := by linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hC1 := one_le_ceil_logb hw hwR
  set δ₀ := ε ^ 2 * w / (192 * ⌈Real.logb 2 (3 * R / w)⌉₊) with hδ₀def
  have hδ₀ : 0 < δ₀ := div_pos (by positivity) (by linarith)
  have hnp : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hδpos : 0 < δ := hδ₀.trans_le hδ
  unfold ellipsoidIters
  apply Nat.ceil_mono
  -- `ln(2n^{3/2} M/δ) ≤ ln(2n^{3/2} M/δ₀) = ln(2n^{3/2}) + ln(M/δ₀)`
  have s1 : Real.log (2 * (n : ℝ) ^ (3 / 2 : ℝ) * M / δ) ≤
      Real.log (2 * (n : ℝ) ^ (3 / 2 : ℝ)) + Real.log (M / δ₀) := by
    rw [← Real.log_mul (by positivity) (by positivity), ← mul_div_assoc]
    exact Real.log_le_log (by positivity)
      (div_le_div_of_nonneg_left (by positivity) hδ₀ hδ)
  -- (T5)
  have s2 := log_div_delta0_le hε hw hwR hRM
  rw [← hδ₀def] at s2
  -- the constant, with `x = 2nM/(εw) ≥ 2`
  set x := 2 * (n : ℝ) * M / (ε * w) with hxdef
  have hMw : 1 ≤ M / w := by rw [le_div_iff₀ hw]; linarith
  have hx1 : 2 * (n : ℝ) ≤ x := by
    rw [hxdef, mul_div_assoc]
    have : 1 ≤ M / (ε * w) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    nlinarith
  have hw2 : w ≤ 2 * n * M := by nlinarith
  have hxε : 1 / ε ≤ x := by
    rw [hxdef, div_le_div_iff₀ hε0 (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hw2 hε0.le]
  have hxM : M / w ≤ x := by
    rw [hxdef, div_le_div_iff₀ hw (by positivity)]
    have h2n : ε ≤ 2 * n := by linarith
    nlinarith [mul_le_mul_of_nonneg_right h2n (mul_nonneg hM.le hw.le)]
  have hl2 := Real.log_two_gt_d9
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
  -- `ln(2n^{3/2}) ≤ (3/2) ln(2n) ≤ (3/2) ln x`
  have t1 : Real.log (2 * (n : ℝ) ^ (3 / 2 : ℝ)) ≤ 3 / 2 * Real.log x := by
    rw [Real.log_mul (by norm_num) hnp.ne', Real.log_rpow (by linarith)]
    have : Real.log (2 * n) ≤ Real.log x := Real.log_le_log (by positivity) hx1
    rw [Real.log_mul (by norm_num) (by positivity)] at this
    nlinarith
  -- `ln(576/ε²) = ln 576 + 2 ln(1/ε) ≤ 10 ln 2 + 2 ln x ≤ 12 ln x`
  have t2 : Real.log (576 / ε ^ 2) ≤ 12 * Real.log x := by
    have e : Real.log (576 / ε ^ 2) = Real.log 576 + 2 * Real.log (1 / ε) := by
      rw [div_eq_mul_inv, Real.log_mul (by norm_num) (by positivity), one_div,
        Real.log_inv, Real.log_inv, Real.log_pow]
      push_cast
      ring
    have h576 : Real.log 576 ≤ 10 * Real.log 2 := by
      rw [← Real.log_rpow (by norm_num)]
      exact Real.log_le_log (by norm_num) (by norm_num)
    have hε' : Real.log (1 / ε) ≤ Real.log x := Real.log_le_log (by positivity) hxε
    rw [e]
    linarith
  -- `2 ln(M/w) ≤ 2 ln x`
  have t3 : Real.log (M / w) ≤ Real.log x := Real.log_le_log (by positivity) hxM
  have hlx0 : 0 ≤ Real.log x := by linarith [Real.log_pos one_lt_two]
  have hn2 : 0 ≤ 2 * (n : ℝ) ^ 2 := by positivity
  calc 2 * (n : ℝ) ^ 2 * Real.log (2 * (n : ℝ) ^ (3 / 2 : ℝ) * M / δ)
      ≤ 2 * (n : ℝ) ^ 2 * (16 * Real.log x) := by
        apply mul_le_mul_of_nonneg_left _ hn2
        linarith
    _ = 32 * (n : ℝ) ^ 2 * Real.log x := by ring

variable {E : Type*} [Fintype E] {P : Set (E → ℝ)} {m : E → ℝ} {c : (E → ℝ) → ℝ} {rb : ℝ}
  {orc : ℝ → ℝ → (E → ℝ)}

/-- The proof of `thm:convexfptas`, (T6) (appF-convex.tex:144): "as
`ln(1/(1 − ᾱ)) ≤ 2 ln(3r̄/W) ≤ 2 ln(3r̄/w)`", for the share bound `ᾱ` of the run with `w ∈ (0, W]`,
whose loop breaks in round `K` (from `1/(1 − ᾱ) ≤ (3r̄/W)²`, (2e) of the proof of
`prop:convexscheme`). -/
lemma log_inv_one_sub_le (h : Setting P m c rb)
    (horc : ∀ α ∈ Icc (0 : ℝ) 1, ∀ δ, 0 < δ → IsDeltaOpt P m c α δ (orc α δ)) {ε : ℝ}
    (hε : ε ∈ Ioo (0 : ℝ) 1) {w : ℝ} (hw : 0 < w) (hwW : w ≤ welfare P m c) {K : ℕ}
    (hK : LoopBreaks rb m c orc (some w) K) :
    Real.log (1 / (1 - cᾱ rb (loopW rb m c orc K))) ≤ 2 * Real.log (3 * rb / welfare P m c) ∧
      2 * Real.log (3 * rb / welfare P m c) ≤ 2 * Real.log (3 * rb / w) := by
  have hW : 0 < welfare P m c := hw.trans_le hwW
  have hWrb := (welfare_lemma h).2.1
  obtain ⟨-, -, hloop⟩ := step1_pos h horc hW (w := some w) fun w₀ hw₀ => by
    cases hw₀
    exact ⟨⟨hw, hwW.trans hWrb⟩, Or.inr hwW⟩
  obtain ⟨-, -, hW1, hW2⟩ := hloop K hK
  obtain ⟨-, hsb, -, hinv, -⟩ := step2 h hε hW hW1 hW2
  have hrb := h.rbar_pos
  refine ⟨?_, ?_⟩
  · rw [← Real.log_rpow (by positivity) 2]
    apply Real.log_le_log (one_div_pos.2 (sub_pos.2 hsb.2.1))
    rw [show (3 * rb / welfare P m c) ^ (2 : ℝ) = (3 * rb / welfare P m c) ^ 2 by
      norm_cast]
    exact hinv
  · exact mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity)
      (div_le_div_of_nonneg_left (by positivity) hw hwW)) (by norm_num)

/-- **`thm:convexfptas`** (Theorem 5.7; 08c-convex.tex:16-18, restated at appF-convex.tex:142, proof
appF-convex.tex:143-145): "For convex costs on `P₊(f)`, given `ε ∈ (0, 1)` and `w ∈ (0, r̄]` with
`W = 0` or `W ≥ w`, one can detect `W = 0` or compute a `(1 − ε)`-optimal contract with numbers of
submodular minimizations, cost-oracle queries, and arithmetic operations polynomial in `n`, `1/ε`,
and `log((r̄ + Gf(E))/w)`."

The part that is formalised: for convex costs on `P₊(f)` with the bounded-subgradient cost oracle
(`PolySetting`, 08c-convex.tex:13; the computational model of 08c-convex.tex:13 enters in the cost
model of `Stoc.CountedQ` in (d)), the proof runs `alg:convex` with `w` and an oracle for
`δ`-optimal responses (in the STOC version, the ellipsoid method of `lem:ellipsoid`), and then:
(a) "one can detect `W = 0`": the algorithm returns "`W = 0`" if and only if `W = 0`;
(b) "or compute a `(1 − ε)`-optimal contract": otherwise it returns a share, and every share `b` it
returns is a `(1 − ε)`-optimal contract (`IsApproxOptimal`);
(c) "with numbers of submodular minimizations, cost-oracle queries, and arithmetic operations
polynomial in `n`, `1/ε`, and `log((r̄ + Gf(E))/w)`", as far as the counts of its proof go that do
not concern the operations themselves: (T4) in both cases at most `14 ε⁻¹ ln(3r̄/w)` responses are
computed (the proof's `O(ε⁻¹ log(3r̄/w))`), each with a precision at least
`δ₀ = ε² w/(192 ⌈log₂(3r̄/w)⌉)`: if `W ≥ w`, those of the rounds `k = 0, …, K` of the loop, with
`K + 1 ≤ ⌈log₂(3r̄/w)⌉ + 1`, and the `J + 1 ≤ ⌈8ε⁻¹ ln(3r̄/w)⌉ + 1` responses at the shares; if
`W = 0`, those of the rounds `k = 0, …, K` of the loop, with `K + 1 ≤ ⌊log₂(3r̄/w)⌋ + 2`; (T5) for
every precision `δ ≥ δ₀`, the number `t(δ) = ⌈2n² ln(2n^{3/2} M/δ)⌉` of `lem:ellipsoid`
(`ellipsoidIters`), with `M = r̄ + G f(E)`, is at most `⌈32 n² ln(2nM/(εw))⌉` (the proof's
`O(n² log(2nM/(εw)))`; the constant `32` is ours); (T6) if the loop breaks, the share bound `ᾱ` of
the run has `ln(1/(1 − ᾱ)) ≤ 2 ln(3r̄/w)`, the bound by which the proof counts the
`s = O(log(1/(ε(1 − ᾱ))))` bits of each of the `J + 1` shares of `thm:fptas`;
(d) the counts themselves, in the cost model of `Stoc.CountedQ` (arithmetic operations and
comparisons, submodular minimizations, evaluations of `f`, queries of the cost oracle), with
`lem:ellipsoid` as the oracle: for the ellipsoid method as a parameter (`EllMethod`, cited) with at
most `cE n²` operations for the initial ellipsoid and for each update (`EllMethod.Cited`), if the
oracle `orc` is the counted ellipsoid method `respC` after its preparation `prepC`, the counted
scheme `convexC` returns the share `b` and the number `Ũ` of `Returns` when the loop breaks and
"`W = 0`" when the loop returns it, and, with `X = ln((r̄ + G f(E))/w)`, the bound
`R = 14ε⁻¹(X + 2)` on the number of responses (from (T4)), the bound `T = 32n²(2n + 1/ε + X) + 1`
on the iterations of each (from (T5)) and the bound `S = 2/ε + 3X + 10` on the bits `s` (from (T6)),
it makes at most `RT` submodular minimizations, at most `RT` queries of the cost oracle, at most
`n + 1 + RT` further evaluations of `f` (the `n + 1` of `f({e})` and `f(E)`, and one in each
iteration; 08c-convex.tex:13 counts them as arithmetic operations), and at most
`n + 2 + R(cE n² + 2 + T(cE n² + 9n + 4) + 2n + 3S + 18) + 3((3/2)X + 4) + 3(8ε⁻¹(X + 2) + 1) +
3S + 18` further arithmetic operations: polynomials in `n`, `1/ε` and `log((r̄ + G f(E))/w)`, the
claim of the theorem (not in the paper: the explicit polynomials; the paper states them as
polynomial).

Not formalised: that the ellipsoid method computes a `δ`-optimal response within `t(δ)` iterations
(the cited bound of `lem:ellipsoid`, here the hypothesis `horc` on the oracle), and the method
itself, a parameter whose cost of an update is cited (`ContractDesignPolymatroids/Convex/Ellipsoid.lean`); `respC`
takes the number `t(δ) = ellipsoidIters n M δ` from its definition at no cost, as computing it
needs `ln` and `⌈·⌉`, which are not operations of the model of 08c-convex.tex:13, and the paper
does not count it; likewise the fuel of the counted searches and loop, which only makes Lean's
recursion terminate and on which the values and counts do not depend.

The proof (appF-convex.tex:144) takes its steps (T1)–(T6) in order. `prop:convexscheme` and
`lem:welfare` are stated in the setting of `app:convex` (`Setting`), and `P₊(f)` lies in it
(`PolySetting.toSetting`, not in the paper: the final version argues the continuity of the costs
only in a comment, appF-convex.tex:119). (T1) "Run `alg:convex` with `w` and with `lem:ellipsoid`
as the oracle" (here the oracle `orc`, as above). "By `prop:convexscheme`, it returns "`W = 0`" if
and only if `W = 0`, and then `OPT = 0` by `lem:welfare`, so every share is optimal"
(`convexscheme`, `welfare_lemma`; that every share is optimal is not part of the statement, and the
proof records it in a `have`). (T2) "Otherwise `W ≥ w`, and the share `b` has the claimed guarantee"
(`prop:convexscheme` gives `(1 − b) r(y) ≥ (1 − ε) OPT` for every `y ∈ X*(b)`, so for `x*(b)`). (T3)
"As `u ↦ u/⌈log₂(3r̄/u)⌉` is nondecreasing on `(0, r̄]`, the bounds of `prop:convexscheme` hold with
`w` in place of `W`" (`div_ceil_mono`). (T4) "So, in both cases, `O(ε⁻¹ log(3r̄/w))` responses are
computed, each with a precision at least `δ₀ := ε² w/(192 ⌈log₂(3r̄/w)⌉)`, as `w/6 ≥ δ₀`"
(`calls_le`, `delta0_le`). (T5) "With `M := r̄ + G f(E) ≥ w` and `⌈log₂(3r̄/w)⌉ ≤ 3M/w`, we get
`ln(M/δ₀) ≤ ln(576/ε²) + 2 ln(M/w)`, so each response takes `O(n² log(2nM/(εw)))` iterations by
`lem:ellipsoid`" (`log_div_delta0_le`, `ellipsoidIters_le`). (T6) "The remaining work, … takes a
number of operations polynomial in `n`, `1/ε`, and `log(3r̄/w)`, as
`ln(1/(1 − ᾱ)) ≤ 2 ln(3r̄/W) ≤ 2 ln(3r̄/w)`" (`log_inv_one_sub_le`, with `1/(1 − ᾱ) ≤ (3r̄/W)²`
from (2) of the proof of `prop:convexscheme`); for (d), the counted scheme `convexC` with these
bounds (`convexC_breaks`, `convexC_zero`, and `totals_le`, `totals_le_zero` with `iters_poly`,
`bits_poly`, `ceil_logb_poly`). -/
theorem convexfptas [DecidableEq E] {f : Finset E → ℝ} {g : (E → ℝ) → E → ℝ} {G : ℝ}
    (h : PolySetting f m c g G rb)
    (horc : ∀ α ∈ Icc (0 : ℝ) 1, ∀ δ, 0 < δ → IsDeltaOpt (indepPoly f) m c α δ (orc α δ))
    {ε w : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioc 0 rb)
    (hwW : welfare (indepPoly f) m c = 0 ∨ w ≤ welfare (indepPoly f) m c) :
    (ReturnsZero rb m c orc (some w) ↔ welfare (indepPoly f) m c = 0) ∧
    (welfare (indepPoly f) m c ≠ 0 → (∃ b Ut, Returns rb m c orc ε (some w) b Ut) ∧
      ∀ b Ut, Returns rb m c orc ε (some w) b Ut →
        IsApproxOptimal (profit (indepPoly f) m c) ε b) ∧
    (∀ K, LoopBreaks rb m c orc (some w) K →
      K + 1 ≤ ⌈Real.logb 2 (3 * rb / w)⌉₊ + 1 ∧
      schemeJ (ε / 2) (cᾱ rb (loopW rb m c orc K)) + 1 ≤
        ⌈8 / ε * Real.log (3 * rb / w)⌉₊ + 1 ∧
      ((K + 1 + (schemeJ (ε / 2) (cᾱ rb (loopW rb m c orc K)) + 1) : ℕ) : ℝ) ≤
        14 / ε * Real.log (3 * rb / w) ∧
      (∀ k ≤ K, ε ^ 2 * w / (192 * ⌈Real.logb 2 (3 * rb / w)⌉₊) ≤ loopD rb k) ∧
      ε ^ 2 * w / (192 * ⌈Real.logb 2 (3 * rb / w)⌉₊) ≤ cδ rb ε (loopW rb m c orc K) ∧
      Real.log (1 / (1 - cᾱ rb (loopW rb m c orc K))) ≤ 2 * Real.log (3 * rb / w)) ∧
    (∀ K, LoopZero rb m c orc (some w) K →
      K + 1 ≤ ⌊Real.logb 2 (3 * rb / w)⌋₊ + 2 ∧
      ((K + 1 : ℕ) : ℝ) ≤ 14 / ε * Real.log (3 * rb / w) ∧
      ∀ k ≤ K, ε ^ 2 * w / (192 * ⌈Real.logb 2 (3 * rb / w)⌉₊) ≤ loopD rb k) ∧
    (∀ δ, ε ^ 2 * w / (192 * ⌈Real.logb 2 (3 * rb / w)⌉₊) ≤ δ →
      ellipsoidIters (Fintype.card E) (rb + G * f univ) δ ≤
        ⌈32 * (Fintype.card E : ℝ) ^ 2 *
          Real.log (2 * Fintype.card E * (rb + G * f univ) / (ε * w))⌉₊) ∧
    (∀ {σ : Type*} (Ell : EllMethod {e // e ∈ posElems f} σ) (cE : ℕ), Ell.Cited cE →
      (∀ α δ, orc α δ = (respC f m c g Ell (posElems f, rb + G * f univ) α δ).val.1) →
      ((∀ K, LoopBreaks rb m c orc (some w) K → ∃ b Ut,
          (convexC f m c g G rb Ell ε w).val = some (b, Ut) ∧
            Returns rb m c orc ε (some w) b Ut) ∧
        ∀ K, LoopZero rb m c orc (some w) K → (convexC f m c g G rb Ell ε w).val = none) ∧
      let C := convexC f m c g G rb Ell ε w
      let n : ℝ := Fintype.card E
      let X := Real.log ((rb + G * f univ) / w)
      let R := 14 / ε * (X + 2)
      let T := 32 * n ^ 2 * (2 * n + 1 / ε + X) + 1
      let S := 2 / ε + 3 * X + 10
      (C.cost.2.1 : ℝ) ≤ R * T ∧ (C.queries : ℝ) ≤ R * T ∧ (C.cost.2.2 : ℝ) ≤ n + 1 + R * T ∧
        (C.cost.1 : ℝ) ≤ n + 2 +
          R * (cE * n ^ 2 + 2 + T * (cE * n ^ 2 + 9 * n + 4) + 2 * n + 3 * S + 18) +
          3 * (3 / 2 * X + 4) + 3 * (8 / ε * (X + 2) + 1) + 3 * S + 18) := by
  -- `P₊(f)` lies in the setting of `prop:convexscheme` and `lem:welfare`, as the costs are
  -- continuous on it (not in the paper)
  have hS := h.toSetting
  have hw0 := hw.1
  have hwrb := hw.2
  have hrb := h.rbar_pos
  set δ₀ := ε ^ 2 * w / (192 * ⌈Real.logb 2 (3 * rb / w)⌉₊) with hδ₀def
  -- the hypothesis on `w` of `prop:convexscheme`
  have hwsome : ∀ w₀ ∈ some w, w₀ ∈ Ioc 0 rb ∧
      (welfare (indepPoly f) m c = 0 ∨ w₀ ≤ welfare (indepPoly f) m c) := fun w₀ hw₀ => by
    cases hw₀
    exact ⟨hw, hwW⟩
  -- (T1) "Run `alg:convex` with `w` and with `lem:ellipsoid` as the oracle." The oracle is `orc`,
  -- for which `horc` is the guarantee of `lem:ellipsoid`.
  -- "By `prop:convexscheme`, it returns "`W = 0`" if and only if `W = 0`, …"
  obtain ⟨hpos, hzero⟩ := convexscheme hS horc hε
  have hT1 : ReturnsZero rb m c orc (some w) ↔ welfare (indepPoly f) m c = 0 := by
    constructor
    · intro hz
      by_contra hne
      exact (hpos (hw0.trans_le (hwW.resolve_left hne)) (some w) hwsome).2.1 hz
    · intro h0
      obtain ⟨K, hK, -⟩ := (hzero h0).2 w hw
      exact ⟨K, hK⟩
  -- "… and then `OPT = 0` by `lem:welfare`, so every share is optimal." (not part of the statement)
  have _hT1opt : welfare (indepPoly f) m c = 0 →
      ∀ α ∈ Icc (0 : ℝ) 1, IsMaxOn (profit (indepPoly f) m c) (Icc 0 1) α := by
    intro h0 α hα
    have hOPT : OPT (profit (indepPoly f) m c) = 0 :=
      le_antisymm (h0 ▸ (welfare_lemma hS).1) hS.OPT_nonneg
    refine isMaxOn_iff.2 fun β hβ => ?_
    have h1 := hS.profit_le_OPT hβ
    have h2 : 0 ≤ profit (indepPoly f) m c α := mul_nonneg (by linarith [hα.2]) (hS.S_nonneg α)
    linarith
  -- (T2) "Otherwise `W ≥ w`, and the share `b` has the claimed guarantee": by
  -- `prop:convexscheme`, `(1 − b) r(y) ≥ Ũ ≥ (1 − ε) OPT` for every `y ∈ X*(b)`, so for `x*(b)`
  have hT2 : welfare (indepPoly f) m c ≠ 0 → (∃ b Ut, Returns rb m c orc ε (some w) b Ut) ∧
      ∀ b Ut, Returns rb m c orc ε (some w) b Ut →
        IsApproxOptimal (profit (indepPoly f) m c) ε b := by
    intro hne
    obtain ⟨hex, -, hval, -⟩ := hpos (hw0.trans_le (hwW.resolve_left hne)) (some w) hwsome
    refine ⟨hex, fun b Ut hbU => ?_⟩
    obtain ⟨hb, hy, hU⟩ := hval b Ut hbU
    obtain ⟨y, hyBR, hyS⟩ := hS.exists_favourable b
    refine ⟨⟨hb.1.le, hb.2.le⟩, ?_⟩
    calc (1 - ε) * OPT (profit (indepPoly f) m c) ≤ Ut := hU
      _ ≤ (1 - b) * reward m y := hy y hyBR
      _ = profit (indepPoly f) m c b := by rw [profit, hyS]
  -- "Otherwise `W ≥ w`": when the loop breaks, the algorithm does not return "`W = 0`", so
  -- `W ≠ 0` by (T1).
  have hT2w : ∀ K, LoopBreaks rb m c orc (some w) K →
      0 < welfare (indepPoly f) m c ∧ w ≤ welfare (indepPoly f) m c := fun K hK => by
    have hne : welfare (indepPoly f) m c ≠ 0 := fun h0 => by
      obtain ⟨K', hK'⟩ := hT1.2 h0
      exact not_loopBreaks_and_loopZero hK hK'
    exact ⟨hw0.trans_le (hwW.resolve_left hne), hwW.resolve_left hne⟩
  -- (T3) "As `u ↦ u/⌈log₂(3r̄/u)⌉` is nondecreasing on `(0, r̄]`, the bounds of
  -- `prop:convexscheme` hold with `w` in place of `W`."
  have hT3 : ∀ K, LoopBreaks rb m c orc (some w) K →
      K + 1 ≤ ⌈Real.logb 2 (3 * rb / w)⌉₊ + 1 ∧ (∀ k ≤ K, w / 6 < loopD rb k) ∧
      schemeJ (ε / 2) (cᾱ rb (loopW rb m c orc K)) + 1 ≤
        ⌈8 / ε * Real.log (3 * rb / w)⌉₊ + 1 ∧
      δ₀ ≤ cδ rb ε (loopW rb m c orc K) := by
    intro K hK
    obtain ⟨hW, hwW'⟩ := hT2w K hK
    have hWrb := (welfare_lemma hS).2.1
    obtain ⟨hK1, hprec, hJ, hδ⟩ := (hpos hW (some w) hwsome).2.2.2 K hK
    have h3 : 3 * rb / welfare (indepPoly f) m c ≤ 3 * rb / w :=
      div_le_div_of_nonneg_left (by positivity) hw0 hwW'
    have hlogle : ⌈Real.logb 2 (3 * rb / welfare (indepPoly f) m c)⌉₊ ≤
        ⌈Real.logb 2 (3 * rb / w)⌉₊ :=
      Nat.ceil_mono (Real.logb_le_logb_of_le (by norm_num) (by positivity) h3)
    have hmono := div_ceil_mono (R := rb) hw0 hwW' hWrb
    have hδw : δ₀ ≤ ε ^ 2 * welfare (indepPoly f) m c /
        (192 * ⌈Real.logb 2 (3 * rb / welfare (indepPoly f) m c)⌉₊) := by
      have e : ∀ x : ℝ, ε ^ 2 * x / (192 * ⌈Real.logb 2 (3 * rb / x)⌉₊) =
          ε ^ 2 / 192 * (x / (⌈Real.logb 2 (3 * rb / x)⌉₊ : ℝ)) := fun x => by ring
      rw [hδ₀def, e, e]
      exact mul_le_mul_of_nonneg_left hmono (by positivity)
    refine ⟨by omega, fun k hk => by linarith [hprec k hk], hJ.trans (Nat.add_le_add_right
      (Nat.ceil_mono (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) h3)
        (div_nonneg (by norm_num) hε.1.le))) 1), hδw.trans hδ⟩
  -- (T4) "So, in both cases, `O(ε⁻¹ log(3r̄/w))` responses are computed, each with a precision at
  -- least `δ₀ := ε² w/(192 ⌈log₂(3r̄/w)⌉)`, as `w/6 ≥ δ₀`."
  have hδ₀ : δ₀ ≤ w / 6 := delta0_le hε hw0 hwrb
  obtain ⟨hcalls, hcalls0⟩ := calls_le hε hw0 hwrb
  have hT4 : ∀ K, LoopBreaks rb m c orc (some w) K →
      ((K + 1 + (schemeJ (ε / 2) (cᾱ rb (loopW rb m c orc K)) + 1) : ℕ) : ℝ) ≤
        14 / ε * Real.log (3 * rb / w) ∧ ∀ k ≤ K, δ₀ ≤ loopD rb k := by
    intro K hK
    obtain ⟨hKw, hprec, hJw, -⟩ := hT3 K hK
    refine ⟨?_, fun k hk => by linarith [hprec k hk]⟩
    have : ((K + 1 + (schemeJ (ε / 2) (cᾱ rb (loopW rb m c orc K)) + 1) : ℕ) : ℝ) ≤
        ((⌈Real.logb 2 (3 * rb / w)⌉₊ + 1 + (⌈8 / ε * Real.log (3 * rb / w)⌉₊ + 1) : ℕ) :
          ℝ) := by
      exact_mod_cast Nat.add_le_add hKw hJw
    exact this.trans hcalls
  -- the case `W = 0`, in which the bounds of `prop:convexscheme` are those with `w`
  have hT4zero : ∀ K, LoopZero rb m c orc (some w) K →
      K + 1 ≤ ⌊Real.logb 2 (3 * rb / w)⌋₊ + 2 ∧
      ((K + 1 : ℕ) : ℝ) ≤ 14 / ε * Real.log (3 * rb / w) ∧ ∀ k ≤ K, δ₀ ≤ loopD rb k := by
    intro K hK
    obtain ⟨K', hK', hK'1, hprec⟩ := (hzero (hT1.1 ⟨K, hK⟩)).2 w hw
    obtain rfl := loopZero_unique hK hK'
    refine ⟨hK'1, ?_, fun k hk => hδ₀.trans (hprec k hk)⟩
    have : ((K + 1 : ℕ) : ℝ) ≤ ((⌊Real.logb 2 (3 * rb / w)⌋₊ + 2 : ℕ) : ℝ) := by
      exact_mod_cast hK'1
    exact this.trans hcalls0
  -- (T5) "With `M := r̄ + G f(E) ≥ w` and `⌈log₂(3r̄/w)⌉ ≤ 3M/w`, we get
  -- `ln(M/δ₀) ≤ ln(576/ε²) + 2 ln(M/w)`, so each response takes `O(n² log(2nM/(εw)))`
  -- iterations by `lem:ellipsoid`" (`M ≥ r̄`, as `G f(E) ≥ 0`; for `n = 0`, `t(δ) = 0`)
  have hT5 : ∀ δ, δ₀ ≤ δ → ellipsoidIters (Fintype.card E) (rb + G * f univ) δ ≤
      ⌈32 * (Fintype.card E : ℝ) ^ 2 *
        Real.log (2 * Fintype.card E * (rb + G * f univ) / (ε * w))⌉₊ := by
    intro δ hδ
    have hGf := h.G_mul_nonneg
    rcases Nat.eq_zero_or_pos (Fintype.card E) with hn | hn
    · simp [ellipsoidIters, hn]
    · exact ellipsoidIters_le hn hε hw0 hwrb (by linarith) hδ
  -- (T6) "The remaining work, … takes a number of operations polynomial in `n`, `1/ε`, and
  -- `log(3r̄/w)`, as `ln(1/(1 − ᾱ)) ≤ 2 ln(3r̄/W) ≤ 2 ln(3r̄/w)`."
  have hT6 : ∀ K, LoopBreaks rb m c orc (some w) K →
      Real.log (1 / (1 - cᾱ rb (loopW rb m c orc K))) ≤ 2 * Real.log (3 * rb / w) := by
    intro K hK
    obtain ⟨h1, h2⟩ := log_inv_one_sub_le hS horc hε hw0 (hT2w K hK).2 hK
    exact h1.trans h2
  refine ⟨hT1, hT2, fun K hK => ⟨(hT3 K hK).1, (hT3 K hK).2.2.1, (hT4 K hK).1,
    (hT4 K hK).2, (hT3 K hK).2.2.2, hT6 K hK⟩, hT4zero, hT5, ?_⟩
  -- (d) the counts of (T4)-(T6) for the counted scheme `convexC` with `lem:ellipsoid` as the
  -- oracle (the counted ellipsoid method `respC`; the method is a parameter, with the cited cost
  -- of an update): "The remaining work, … takes a number of operations polynomial in `n`, `1/ε`,
  -- and `log(3r̄/w)`" (not in the paper: the explicit polynomials)
  intro σ Ell cE hU horcC
  have hRM : rb ≤ rb + G * f univ := by linarith [h.G_mul_nonneg]
  have hwM : w ≤ rb + G * f univ := hw.2.trans hRM
  -- a run that breaks: `W̃ > 0`, `0 ≤ ᾱ < 1` and `2r̄/W̃ ≤ 3r̄/w`, by (1) and (2) of the proof of
  -- `prop:convexscheme`
  have hbrk : ∀ K, LoopBreaks rb m c orc (some w) K → 0 < loopW rb m c orc K ∧
      cᾱ rb (loopW rb m c orc K) ∈ Set.Ico 0 1 ∧ 2 * rb / loopW rb m c orc K ≤ 3 * rb / w := by
    intro K hK
    obtain ⟨hW, hwW'⟩ := hT2w K hK
    obtain ⟨-, -, hloop⟩ := step1_pos h.toSetting horc hW (w := some w) fun w₀ hw₀ => by
      cases hw₀
      exact ⟨hw, Or.inr hwW'⟩
    obtain ⟨-, -, hW1, hW2⟩ := hloop K hK
    obtain ⟨-, hsb, -⟩ := step2 h.toSetting hε hW hW1 hW2
    have hWt : 0 < loopW rb m c orc K := by linarith
    refine ⟨hWt, ⟨hsb.1, hsb.2.1⟩, ?_⟩
    rw [div_le_div_iff₀ hWt hw.1]
    nlinarith
  -- the iterations of each response, (T5)
  have hiter := iters_poly (n := Fintype.card E) hε hw.1 hwM
  have hX := log_div_nonneg hw.1 hwM
  have hlog3 := log_three_le hw.1 hw.2 hRM
  have hR : 14 / ε * Real.log (3 * rb / w) ≤ 14 / ε * (Real.log ((rb + G * f univ) / w) + 2) :=
    mul_le_mul_of_nonneg_left hlog3 (by have := hε.1; positivity)
  refine ⟨⟨fun K hK => ?_, fun K hK => ?_⟩, ?_⟩
  · -- the value when the loop breaks: the share `b = α̌_ĵ` and `Ũ = Ũ_ĵ` of `Returns`
    obtain ⟨hWt, hᾱ, -⟩ := hbrk K hK
    obtain ⟨⟨jh, hjh, hmax, hv⟩, -⟩ := convexC_breaks h hU horcC hε hw.1 hK hWt hᾱ.2
      (fun k hk => hT5 _ ((hT4 K hK).2 k hk)) (hT5 _ (hT3 K hK).2.2.2)
    exact ⟨_, _, hv, K, hK, jh, hjh, hmax, rfl, rfl⟩
  · -- the value when it returns "`W = 0`"
    exact (convexC_zero h hU horcC (ε := ε) hw.1 hK
      (fun k hk => hT5 _ ((hT4zero K hK).2.2 k hk))).1
  · -- the counts
    intro C n X R T S
    have hS0 : 0 ≤ S := by have := hε.1; positivity
    have hL0 : (0 : ℝ) ≤ 3 / 2 * X + 4 := by positivity
    have hJ0 : (0 : ℝ) ≤ 8 / ε * (X + 2) + 1 := by have := hε.1; positivity
    by_cases hW0 : welfare (indepPoly f) m c = 0
    · obtain ⟨K, hK⟩ := hT1.2 hW0
      obtain ⟨-, c1, c2, c3, c4⟩ := convexC_zero h hU horcC (ε := ε) hw.1 hK
        (fun k hk => hT5 _ ((hT4zero K hK).2.2 k hk))
      exact totals_le_zero c2 c4 c3 c1 ((hT4zero K hK).2.1.trans hR) hiter hS0 hL0 hJ0
    · obtain ⟨⟨b, Ut, K, hK, -⟩, -⟩ := hT2 hW0
      obtain ⟨hWt, hᾱ, hz⟩ := hbrk K hK
      obtain ⟨-, c1, c2, c3, c4⟩ := convexC_breaks h hU horcC hε hw.1 hK hWt hᾱ.2
        (fun k hk => hT5 _ ((hT4 K hK).2 k hk)) (hT5 _ (hT3 K hK).2.2.2)
      -- `J ≤ ⌈8ε⁻¹ ln(3r̄/w)⌉ ≤ 8ε⁻¹ (ln(M/w) + 2) + 1`
      have hJ : (schemeJ (ε / 2) (cᾱ rb (loopW rb m c orc K)) : ℝ) ≤ 8 / ε * (X + 2) + 1 := by
        have h1 := (hT3 K hK).2.2.1
        have h0 : 0 ≤ 8 / ε * Real.log (3 * rb / w) :=
          mul_nonneg (by have := hε.1; positivity)
            (Real.log_nonneg (by rw [le_div_iff₀ hw.1]; linarith [hw.2]))
        have h2 : (schemeJ (ε / 2) (cᾱ rb (loopW rb m c orc K)) : ℝ) ≤
            ⌈8 / ε * Real.log (3 * rb / w)⌉₊ := by exact_mod_cast (by omega :
              schemeJ (ε / 2) (cᾱ rb (loopW rb m c orc K)) ≤ ⌈8 / ε * Real.log (3 * rb / w)⌉₊)
        have h3 := Nat.ceil_lt_add_one h0
        have h4 : 8 / ε * Real.log (3 * rb / w) ≤ 8 / ε * (X + 2) :=
          mul_le_mul_of_nonneg_left hlog3 (by have := hε.1; positivity)
        linarith
      exact totals_le c2 c4 c3 c1 ((hT4 K hK).1.trans hR) hiter
        (bits_poly hε hᾱ hw.1 hw.2 hRM (hT6 K hK))
        (ceil_logb_poly hw.1 hw.2 hRM (by have := hWt; positivity) hz) hJ

end Fptas

end

end Stoc.Convex
