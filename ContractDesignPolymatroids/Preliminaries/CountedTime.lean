-- stamp r1 2026-11-03
import ContractDesignPolymatroids.Preliminaries.Counted

/-!
# Operation counts: running times

Several results of the STOC version state a running time, not only counts:
* `thm:waterfilling`: "The best response `x*(α)` can be computed in time
  `O(n⁷ log n)·FO + O(n⁸ log n)`" (`stoc-sections/05-best-response.tex:27`);
* `thm:pieces`: "… can be computed in time `O(n⁹(B+1) log n)·FO + O(n¹⁰(B+1) log n + n⁴(B+1)²)`"
  (`stoc-sections/06-optimal-share.tex:48`);
* `lem:A-lineartime` and `thm:linear`: "in time `O(n³)·FO + O(n³ log n)`".

Their proofs count arithmetic operations, evaluations of `f` (`FO` is "the cost of one
evaluation", `stoc-sections/02-preliminaries.tex:8`) and submodular minimizations, and multiply the
minimizations by the time of one minimization, which they cite: "The strongly polynomial algorithm
of Iwata and Orlin [IO09] finds it in time `O(n⁵ log n)·EO + O(n⁶ log n)`, where `EO` is the cost of
evaluating the function being minimized. Here each such function is `f` minus a modular function,
so `EO = FO + O(n)`. Multiplying by the `O(n²)` minimizations gives the stated bound"
(`stoc-sections/appB-quadratic.tex:181`). This file turns the counts of `Stoc.Counted` into times
(not in the paper: the paper counts in prose):

* `Counted.time FO TS c`: the time of the cost `c` when an arithmetic operation takes time `1`, an
  evaluation of `f` time `FO` and a submodular minimization time `TS`;
* `Counted.lg n = ⌈log₂ n⌉ + 1`: the factor `log n` of the time bounds, at least `1`, so that the
  bounds hold for `n = 1` as well (not in the paper);
* `Counted.sfmTime C₁ C₂ n FO = C₁(n⁵ lg n (FO + C₂ n) + n⁶ lg n)`: the cited bound of Iwata and
  Orlin with `EO = FO + C₂ n`, for constants `C₁` and `C₂` (cited, [IO09]). The results take
  `TS ≤ sfmTime C₁ C₂ n FO` as a hypothesis;
* `Counted.time_le`: the time from bounds on the three counts; `Counted.time_le_sfm`: the time of
  `L` water-fillings, or of anything with their counts, with the cited bound (for `cor:fptasquad`).
-/

namespace Stoc

namespace Counted

/-- The time of a cost (not in the paper): one unit for each arithmetic operation, `FO` for each
evaluation of `f`, and `TS` for each submodular minimization. -/
def time (FO TS : ℝ) (c : Cost) : ℝ := c.1 + FO * c.2.2 + TS * c.2.1

/-- `lg n = ⌈log₂ n⌉ + 1`, the factor `log n` of the time bounds, at least `1` (not in the paper: it
is `Θ(log n)` for `n ≥ 2` and makes the bounds hold for `n = 1` as well). -/
def lg (n : ℕ) : ℕ := Nat.clog 2 n + 1

/-- `lg n ≥ 1` (not in the paper). -/
lemma one_le_lg (n : ℕ) : 1 ≤ lg n := Nat.le_add_left 1 _

/-- The time of one submodular minimization on a ground set of `n` elements by the algorithm of
Iwata and Orlin (cited, [IO09]), as the proof of `thm:waterfilling` uses it
(`stoc-sections/appB-quadratic.tex:181`): "The strongly polynomial algorithm of Iwata and Orlin
[IO09] finds it in time `O(n⁵ log n)·EO + O(n⁶ log n)`, where `EO` is the cost of evaluating the
function being minimized. Here each such function is `f` minus a modular function, so
`EO = FO + O(n)`." With the constant `C₁` of [IO09] and the constant `C₂` of `EO = FO + O(n)`:
`C₁(n⁵ lg n (FO + C₂ n) + n⁶ lg n)`. -/
def sfmTime (C₁ C₂ : ℝ) (n : ℕ) (FO : ℝ) : ℝ :=
  C₁ * ((n : ℝ) ^ 5 * lg n * (FO + C₂ * n) + (n : ℝ) ^ 6 * lg n)

/-- The cited time of a minimization is nonnegative for nonnegative constants and `FO ≥ 0` (not in
the paper). -/
lemma sfmTime_nonneg {C₁ C₂ FO : ℝ} (n : ℕ) (h₁ : 0 ≤ C₁) (h₂ : 0 ≤ C₂) (hFO : 0 ≤ FO) :
    0 ≤ sfmTime C₁ C₂ n FO := by
  unfold sfmTime
  positivity

/-- The time from bounds on the counts (not in the paper): at most `a` arithmetic operations, `e`
evaluations of `f` and `s` minimizations, each of time at most `T`, take time at most
`a + FO e + T s`. -/
lemma time_le {FO TS T : ℝ} {c : Cost} {a e s : ℕ} (hFO : 0 ≤ FO) (hT : 0 ≤ T) (hTS : TS ≤ T)
    (ha : c.1 ≤ a) (he : c.2.2 ≤ e) (hs : c.2.1 ≤ s) :
    time FO TS c ≤ a + FO * e + T * s := by
  unfold time
  have ha' : (c.1 : ℝ) ≤ a := by exact_mod_cast ha
  have he' : (c.2.2 : ℝ) ≤ e := by exact_mod_cast he
  have hs' : (c.2.1 : ℝ) ≤ s := by exact_mod_cast hs
  have h0 : (0 : ℝ) ≤ c.2.1 := Nat.cast_nonneg _
  have h1 := mul_le_mul_of_nonneg_left he' hFO
  have h2 := mul_le_mul_of_nonneg_right hTS h0
  have h3 := mul_le_mul_of_nonneg_left hs' hT
  linarith

/-- The time of `L` water-fillings, or of anything with their counts (not in the paper; used for
`cor:fptasquad`): for `n ≥ 1`, at most `L·k n³` arithmetic operations, `L·6n²` evaluations of `f`
and `L·4n²` submodular minimizations, each of time at most `sfmTime C₁ C₂ n FO` (cited, [IO09]),
take time at most `L((6 + 4C₁) n⁷ lg n · FO + (k + 4C₁(C₂ + 1)) n⁸ lg n)`. -/
lemma time_le_sfm {FO TS C₁ C₂ : ℝ} {c : Cost} {n k L : ℕ} (hn : 0 < n) (hFO : 0 ≤ FO)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hTS : TS ≤ sfmTime C₁ C₂ n FO)
    (ha : c.1 ≤ L * (k * n ^ 3)) (he : c.2.2 ≤ L * (6 * n ^ 2)) (hs : c.2.1 ≤ L * (4 * n ^ 2)) :
    time FO TS c ≤
      L * ((6 + 4 * C₁) * (n : ℝ) ^ 7 * lg n * FO +
        (k + 4 * C₁ * (C₂ + 1)) * (n : ℝ) ^ 8 * lg n) := by
  refine (time_le hFO (sfmTime_nonneg n hC₁ hC₂ hFO) hTS ha he hs).trans ?_
  have hx : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL1 : (1 : ℝ) ≤ (lg n : ℝ) := by exact_mod_cast one_le_lg n
  unfold sfmTime
  push_cast
  set x : ℝ := (n : ℝ)
  set g : ℝ := (lg n : ℝ)
  set l : ℝ := (L : ℝ)
  have hl : 0 ≤ l := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have e3 : x ^ 3 ≤ x ^ 8 := pow_le_pow_right₀ hx (by norm_num)
  have e2 : x ^ 2 ≤ x ^ 7 := pow_le_pow_right₀ hx (by norm_num)
  have h8 : x ^ 8 ≤ x ^ 8 * g := le_mul_of_one_le_right (by positivity) hL1
  have h7 : x ^ 7 ≤ x ^ 7 * g := le_mul_of_one_le_right (by positivity) hL1
  -- the arithmetic operations: `l k x³ ≤ l k x⁸ g`
  have i1 : l * (k * x ^ 3) ≤ l * k * x ^ 8 * g := by
    have := mul_le_mul_of_nonneg_left (e3.trans h8) (mul_nonneg hl hk)
    nlinarith
  -- the evaluations of `f`: `FO l 6x² ≤ 6 l x⁷ g FO`
  have i2 : FO * (l * (6 * x ^ 2)) ≤ 6 * l * x ^ 7 * g * FO := by
    have := mul_le_mul_of_nonneg_left (e2.trans h7) (mul_nonneg hl hFO)
    nlinarith
  -- the minimizations: an identity
  have i3 : C₁ * (x ^ 5 * g * (FO + C₂ * x) + x ^ 6 * g) * (l * (4 * x ^ 2)) =
      4 * l * C₁ * x ^ 7 * g * FO + 4 * l * C₁ * (C₂ + 1) * x ^ 8 * g := by ring
  nlinarith [i1, i2, i3]

end Counted

end Stoc
