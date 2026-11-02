-- stamp r8 2026-11-02
import Stoc.Approximation.Agent

/-!
# The approximation scheme for an exact best-response oracle

The STOC version's Section 5 before its subsections (`sec:fptas`,
`stoc-sections/08-approximation.tex`:1-23) with the proofs in Appendix D (`app:halfrule`,
`stoc-sections/appE-halfrule.tex`:3-25): `thm:fptas` and `cor:probe`, and `lem:monreward`
(06-optimal-share.tex:29-31, proof appB-quadratic.tex:276-287) on any action set, which both proofs
cite.

* The setting. Section 5 gives "approximation schemes for the principal's utility that apply beyond
  polymatroids", and "Their running time is measured in best-response oracle calls"
  (08-approximation.tex:4); the argument of `thm:fptas` "applies to any action set" (08:8). An
  exact best-response oracle on an action set `K ⊆ ℝ^E_{≥0}` (`IsExactOracle`) answers every share
  `α ∈ [0, 1]` with the best response `x*(α)` of the model, which breaks ties in favor of the
  principal (02-preliminaries.tex:17), and `U_P(α) = (1 − α) r(x*(α))` is
  `profit fun α => reward m (xs α)`.
* `OPT = sup_{α ∈ [0, 1]} U_P(α)` (`OPT`) and `(1 − ε)`-optimal contracts (`IsApproxOptimal`,
  08-approximation.tex:6), share bounds (`IsShareBound`, 08-approximation.tex:8).
* `lem:monreward` for a choice of maximizers on any action set (`monotoneOn_reward`,
  `monotoneOn_reward_of_isBR`), by `Stoc.monreward_aux`, the proof of `lem:monreward` for any action
  set (the exact statement `Stoc.monreward` is in `Stoc/OptimalShare/Reward.lean`).
* `thm:fptas` (`fptas`). Its proof puts `ε' = ε/2` (`schemeEps`),
  `J = min{j ≥ 0 : (1 − ε')^j ≤ 1 − ᾱ}` (`schemeJ`) and `s = ⌈log₂(4/(ε(1 − ᾱ)))⌉` (`schemeS`); the
  scheme evaluates the dyadic shares `α̂_j = 1 − 2^{−s} ⌊2^s (1 − ε')^j⌋`, `j = 0, …, J`
  (`schemeShare`, the list `schemeShares`, `IsDyadic`), and returns the one with largest utility;
  then `b_j = 1 − α̂_j` (`schemeB`; `b_j = 2^{−s} ⌊2^s (1 − ε')^j⌋` is `schemeB_eq`). The steps of
  the proof are in `fptas_aux`, the theorem for the shares `α̂_j` and any reward curve that is
  nonnegative and nondecreasing on `[0, 1]` in place of `α ↦ r(x*(α))`, as the proof uses of the
  best responses only `lem:monreward`. `fptas` follows from it by `lem:monreward` on any action set,
  and the proof of `prop:convexscheme` cites it for the best responses of `app:convex` ("The proof
  of `thm:fptas` uses only `lem:monreward`, which holds for all maximizers, so the theorem applies
  to the best responses `x*(α)`", appF-convex.tex:103), and for the shares `α̂_j` themselves ("the
  shares constructed in the proof of `thm:fptas`", appF-convex.tex:75).
* `cor:probe` (`probe`), with `ᾱ_a = 1 − (1 − a) r(x*(a))/r(x*(1))` (`probeAlpha`). The paragraph
  before it (08-approximation.tex:17) outlines its proof.

How the schemes are formalised. The scheme of `thm:fptas` does not adapt its queries: it calls the
oracle at the shares of a list `Q` that depends only on `ε` and `ᾱ`, which gives `x*(q)` and so
`U_P(q) = (1 − q) r(x*(q))` for every `q ∈ Q`, and it returns a share of `Q` with the largest
utility. So `fptas` states that there is a list `Q` (it is `schemeShares ε ᾱ`) of at most
`⌈2ε⁻¹ ln(1/(1 − ᾱ))⌉ + 1` dyadic shares such that, on every instance for which `ᾱ` is a share
bound, every share of `Q` with the largest utility is `(1 − ε)`-optimal. The scheme of `cor:probe`
first calls the oracle at `a` and at `1`, which gives `ᾱ_a`, and then at the shares of a list that
depends only on `ε` and `ᾱ_a`, those of `thm:fptas`.

The model's reward of success `r̄` (02-preliminaries.tex:12) is a field of `IsExactOracle` that no
proof uses.
-/

open Finset Stoc.Convex

namespace Stoc

noncomputable section

/-! ### `lem:monreward` on any action set -/

section Monreward

variable {E : Type*} [Fintype E]

/-- `lem:monreward` for a choice `xs` of maximizers on any action set `C`: `α ↦ r(xs(α))` is
nondecreasing, by `Stoc.monreward_aux`, the proof of `lem:monreward` for any action set (not in the
paper as a result: `lem:monreward` is stated for `P₊(f)`, 06-optimal-share.tex:29-31; the proofs of
`thm:fptas` and `cor:probe` cite it on the action set of the oracle, as its argument "uses only the
optimality of `x` and `x'`" (appB-quadratic.tex:277), so that the argument of `thm:fptas` "applies
to any action set" (08-approximation.tex:8), and `prop:convexscheme` cites it as "`lem:monreward`,
which holds for all maximizers" (appF-convex.tex:103)). -/
theorem monotoneOn_reward {C : Set (E → ℝ)} (m : E → ℝ) (c : (E → ℝ) → ℝ) {I : Set ℝ}
    {xs : ℝ → E → ℝ} (hC : ∀ α ∈ I, xs α ∈ C)
    (hmax : ∀ α ∈ I, ∀ y ∈ C, α * reward m y - c y ≤ α * reward m (xs α) - c (xs α)) :
    MonotoneOn (fun α => reward m (xs α)) I := by
  intro α hα α' hα' h
  rcases h.lt_or_eq with h | h
  · exact monreward_aux m c h (hC α hα) (hC α' hα') (hmax α hα) (hmax α' hα')
  · simp only [h, le_refl]

/-- `lem:monreward` for best responses (`Convex.IsBR`) on any action set `C`, as
`monotoneOn_reward`. -/
theorem monotoneOn_reward_of_isBR {C : Set (E → ℝ)} {m : E → ℝ} {c : (E → ℝ) → ℝ} {I : Set ℝ}
    {xs : ℝ → E → ℝ} (hxs : ∀ α ∈ I, IsBR C m c α (xs α)) :
    MonotoneOn (fun α => reward m (xs α)) I :=
  monotoneOn_reward m c (fun α hα => (hxs α hα).1) fun α hα y hy => (hxs α hα).2 y hy

end Monreward

/-! ### `OPT` and share bounds -/

/-- `OPT = sup_{α ∈ [0, 1]} U(α)` for the principal's utility `U` (08-approximation.tex:6, "Let
`OPT := sup_{α ∈ [0, 1]} U_P(α)`"). -/
def OPT (U : ℝ → ℝ) : ℝ := sSup (U '' Set.Icc 0 1)

/-- A contract, that is, a share `α ∈ [0, 1]` (02-preliminaries.tex:13: "We identify a linear
contract with its share `α`"), is **`(1 − ε)`-optimal** for the principal's utility `U` if "its
utility is at least `(1 − ε) OPT`" (08-approximation.tex:6). -/
def IsApproxOptimal (U : ℝ → ℝ) (ε α : ℝ) : Prop :=
  α ∈ Set.Icc (0 : ℝ) 1 ∧ (1 - ε) * OPT U ≤ U α

/-- `ᾱ` is a **share bound** for the principal's utility `U` (08-approximation.tex:8, "a number
`ᾱ ∈ [0, 1)` such that `sup_{α ∈ [0, ᾱ]} U_P(α) = OPT`"). -/
def IsShareBound (U : ℝ → ℝ) (ᾱ : ℝ) : Prop :=
  0 ≤ ᾱ ∧ ᾱ < 1 ∧ sSup (U '' Set.Icc 0 ᾱ) = OPT U

/-- `α` is **dyadic** with `s` bits: it has the form `k/2^s` for an integer `k`. The proof of
`thm:fptas` evaluates "the dyadic shares" `α̂_j = 1 − 2^{−s} ⌊2^s (1 − ε')^j⌋`
(appE-halfrule.tex:5-7), and the theorem states that "The queried shares are rationals with
`O(1 + log(1/ε) + log(1/(1 − ᾱ)))` bits" (08-approximation.tex:13): a dyadic share `k/2^s` in
`[0, 1]` has `0 ≤ k ≤ 2^s`. -/
def IsDyadic (s : ℕ) (α : ℝ) : Prop :=
  ∃ k : ℤ, α = k / 2 ^ s

section Bounded

variable {S : ℝ → ℝ}

/-- `U_P = (1 − α) S(α)` is nonnegative on `[0, 1]` if `S` is (not in the paper: the proof of
`thm:fptas` uses `U_P(0) ≥ 0` without saying so). -/
lemma profit_nonneg (hnn : ∀ α ∈ Set.Icc (0 : ℝ) 1, 0 ≤ S α) {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ profit S α :=
  mul_nonneg (by linarith [hα.2]) (hnn α hα)

variable (hmono : MonotoneOn S (Set.Icc 0 1)) (hnn : ∀ α ∈ Set.Icc (0 : ℝ) 1, 0 ≤ S α)
include hmono hnn

/-- `U_P ≤ S(1)` on `[0, 1]`. -/
lemma profit_le_one {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) : profit S α ≤ S 1 := by
  have h1 : S α ≤ S 1 := hmono hα ⟨by norm_num, le_rfl⟩ hα.2
  have h2 := hnn α hα
  unfold profit
  nlinarith [hα.1, hα.2]

/-- `U_P` is bounded above on `[0, 1]` (not in the paper: it takes the suprema of `U_P` as
given). -/
lemma bddAbove_profit (A : Set ℝ) (hA : A ⊆ Set.Icc 0 1) : BddAbove (profit S '' A) :=
  ⟨S 1, by
    rintro _ ⟨α, hα, rfl⟩
    exact profit_le_one hmono hnn (hA hα)⟩

end Bounded

/-! ### The exact best-response oracle -/

section Oracle

variable {E : Type*} [Fintype E]

/-- An **exact best-response oracle** on the action set `K` (08-approximation.tex:13, `thm:fptas`:
"Given an exact best-response oracle"; Section 5 measures the running time of its schemes "in
best-response oracle calls", 08-approximation.tex:4), with its answers `xs`. The model of
`sec:model` (02-preliminaries.tex:12, 17) with an action set `K` in place of `P₊(f)`, as the schemes
"apply beyond polymatroids" (08-approximation.tex:4) and the argument of `thm:fptas` "applies to any
action set" (08-approximation.tex:8): a nonempty `K ⊆ ℝ^E_{≥0}`, rewards `m ≥ 0`, a cost
`c : ℝ^E_{≥0} → ℝ_{≥0}` with `c(0) = 0` (`IsCost`), a reward of success `r̄ > 0` with `r ≤ r̄` on
`K` (`bounded`; no proof uses it), and at every share `α ∈ [0, 1]` the oracle's answer
`xs α = x*(α)`, the best response of the model, which breaks ties in favor of the principal
(`IsPBR`, 02-preliminaries.tex:17). So `U_P(α) = (1 − α) r(x*(α))` is
`profit fun α => reward m (xs α)`. -/
structure IsExactOracle (K : Set (E → ℝ)) (m : E → ℝ) (c : (E → ℝ) → ℝ) (xs : ℝ → E → ℝ) :
    Prop where
  nonempty : K.Nonempty
  nonneg : ∀ x ∈ K, 0 ≤ x
  m_nonneg : ∀ e, 0 ≤ m e
  cost : IsCost c
  bounded : ∃ rb > 0, ∀ x ∈ K, reward m x ≤ rb
  isPBR : ∀ α ∈ Set.Icc (0 : ℝ) 1, IsPBR K m c α (xs α)

end Oracle

/-! ### The shares of the scheme -/

/-- `ε' = ε/2` (appE-halfrule.tex:5). An abbreviation: it unfolds to `ε / 2` for `rw`, `ring` and
`linarith`. -/
abbrev schemeEps (ε : ℝ) : ℝ := ε / 2

/-- `J = min{j ≥ 0 : (1 − ε')^j ≤ 1 − ᾱ}` (appE-halfrule.tex:5). -/
def schemeJ (ε ᾱ : ℝ) : ℕ := sInf {j : ℕ | (1 - schemeEps ε) ^ j ≤ 1 - ᾱ}

/-- `s = ⌈log₂(4/(ε(1 − ᾱ)))⌉` (appE-halfrule.tex:5). -/
def schemeS (ε ᾱ : ℝ) : ℕ := ⌈Real.logb 2 (4 / (ε * (1 - ᾱ)))⌉₊

/-- The dyadic shares `α̂_j = 1 − 2^{−s} ⌊2^s (1 − ε')^j⌋` that the scheme of `thm:fptas` evaluates
(appE-halfrule.tex:5-7); the floor of the nonnegative number `2^s (1 − ε')^j` is taken in `ℕ`. An
abbreviation, like `schemeB`. -/
abbrev schemeShare (ε ᾱ : ℝ) (j : ℕ) : ℝ :=
  1 - (⌊(2 : ℝ) ^ schemeS ε ᾱ * (1 - schemeEps ε) ^ j⌋₊ : ℝ) / 2 ^ schemeS ε ᾱ

/-- The list `α̂_0, …, α̂_J` of the shares that the scheme of `thm:fptas` evaluates: "The scheme
evaluates the dyadic shares `α̂_j`, `j = 0, …, J`, and returns the one with largest utility"
(appE-halfrule.tex:5-9). -/
def schemeShares (ε ᾱ : ℝ) : List ℝ := (List.range (schemeJ ε ᾱ + 1)).map (schemeShare ε ᾱ)

lemma mem_schemeShares {ε ᾱ q : ℝ} :
    q ∈ schemeShares ε ᾱ ↔ ∃ j ≤ schemeJ ε ᾱ, schemeShare ε ᾱ j = q := by
  simp only [schemeShares, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, by omega, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, by omega, rfl⟩

lemma length_schemeShares (ε ᾱ : ℝ) : (schemeShares ε ᾱ).length = schemeJ ε ᾱ + 1 := by
  simp [schemeShares]

lemma schemeShares_ne_nil (ε ᾱ : ℝ) : schemeShares ε ᾱ ≠ [] := by
  rw [← List.length_pos_iff, length_schemeShares]
  omega

/-- `b_j = 1 − α̂_j`, defined in the proof of `thm:fptas` (appE-halfrule.tex:11). An abbreviation,
so that it unfolds to `1 − α̂_j` and further to `2^{−s} ⌊2^s (1 − ε')^j⌋` for `ring`. -/
abbrev schemeB (ε ᾱ : ℝ) (j : ℕ) : ℝ := 1 - schemeShare ε ᾱ j

/-- `b_j = 2^{−s} ⌊2^s (1 − ε')^j⌋`, by the definitions of `b_j` and `α̂_j`. -/
lemma schemeB_eq (ε ᾱ : ℝ) (j : ℕ) :
    schemeB ε ᾱ j = (⌊(2 : ℝ) ^ schemeS ε ᾱ * (1 - schemeEps ε) ^ j⌋₊ : ℝ) / 2 ^ schemeS ε ᾱ :=
  sub_sub_cancel _ _

/-- `α̂_j = 1 − b_j`. -/
lemma schemeShare_eq (ε ᾱ : ℝ) (j : ℕ) : schemeShare ε ᾱ j = 1 - schemeB ε ᾱ j :=
  (sub_sub_cancel _ _).symm

section Shares

variable {ε ᾱ : ℝ}

/-- `1 − ε' > 0`. -/
lemma q_pos (hε : ε ∈ Set.Ioo (0 : ℝ) 1) : 0 < 1 - schemeEps ε := by
  unfold schemeEps
  linarith [hε.2]

/-- `1 − ε' < 1`. -/
lemma q_lt_one (hε : ε ∈ Set.Ioo (0 : ℝ) 1) : 1 - schemeEps ε < 1 := by
  unfold schemeEps
  linarith [hε.1]

/-- `J` exists: some power of `1 − ε'` is at most `1 − ᾱ` (not in the paper: it leaves this
implicit). -/
lemma schemeJ_mem (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hᾱ : ᾱ < 1) :
    (1 - schemeEps ε) ^ schemeJ ε ᾱ ≤ 1 - ᾱ := by
  have hne : {j : ℕ | (1 - schemeEps ε) ^ j ≤ 1 - ᾱ}.Nonempty := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (sub_pos.2 hᾱ) (q_lt_one hε)
    exact ⟨n, hn.le⟩
  exact Nat.sInf_mem hne

/-- The minimality of `J`: `(1 − ε')^j > 1 − ᾱ` for `j < J`. -/
lemma lt_of_lt_schemeJ {j : ℕ} (hj : j < schemeJ ε ᾱ) : 1 - ᾱ < (1 - schemeEps ε) ^ j := by
  have := Nat.notMem_of_lt_sInf hj
  simp only [Set.mem_ofPred_eq, not_le] at this
  exact this

/-- `2^{−s} ≤ ε(1 − ᾱ)/4`, as `2^s ≥ 4/(ε(1 − ᾱ))` by the definition of `s`: the bound with
which step (6) of the proof of `thm:fptas` begins, and which (3) of the proof of
`prop:convexscheme` recalls for the accuracy `ε/2` ("the grid in the proof of `thm:fptas` uses …
`2^{−s} ≤ ε(1 − ᾱ)/8`", appF-convex.tex:101). -/
lemma one_div_two_pow_schemeS_le (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hᾱ : ᾱ < 1) :
    1 / (2 : ℝ) ^ schemeS ε ᾱ ≤ ε * (1 - ᾱ) / 4 := by
  have hεᾱ : 0 < ε * (1 - ᾱ) := mul_pos hε.1 (sub_pos.2 hᾱ)
  have hpos : 0 < 4 / (ε * (1 - ᾱ)) := by positivity
  have h1 : Real.logb 2 (4 / (ε * (1 - ᾱ))) ≤ (schemeS ε ᾱ : ℝ) := Nat.le_ceil _
  have h2 : 4 / (ε * (1 - ᾱ)) ≤ (2 : ℝ) ^ schemeS ε ᾱ :=
    calc 4 / (ε * (1 - ᾱ)) = (2 : ℝ) ^ Real.logb 2 (4 / (ε * (1 - ᾱ))) :=
          (Real.rpow_logb (by norm_num) (by norm_num) hpos).symm
      _ ≤ (2 : ℝ) ^ (schemeS ε ᾱ : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
      _ = (2 : ℝ) ^ schemeS ε ᾱ := Real.rpow_natCast 2 _
  rw [div_le_iff₀ hεᾱ] at h2
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- `b_j ≤ (1 − ε')^j`. -/
lemma schemeB_le (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (j : ℕ) :
    schemeB ε ᾱ j ≤ (1 - schemeEps ε) ^ j := by
  have h2 : (0 : ℝ) < 2 ^ schemeS ε ᾱ := by positivity
  have hq := q_pos hε
  rw [schemeB_eq, div_le_iff₀ h2]
  have := Nat.floor_le (a := (2 : ℝ) ^ schemeS ε ᾱ * (1 - schemeEps ε) ^ j) (by positivity)
  linarith

/-- `(1 − ε')^j − 2^{−s} < b_j`. -/
lemma schemeB_gt (j : ℕ) : (1 - schemeEps ε) ^ j - 1 / 2 ^ schemeS ε ᾱ < schemeB ε ᾱ j := by
  have h2 : (0 : ℝ) < 2 ^ schemeS ε ᾱ := by positivity
  rw [schemeB_eq]
  have := Nat.lt_floor_add_one ((2 : ℝ) ^ schemeS ε ᾱ * (1 - schemeEps ε) ^ j)
  have e : (1 - schemeEps ε) ^ j - 1 / 2 ^ schemeS ε ᾱ =
      (2 ^ schemeS ε ᾱ * (1 - schemeEps ε) ^ j - 1) / 2 ^ schemeS ε ᾱ := by
    field_simp
  rw [e]
  exact div_lt_div_of_pos_right (by linarith) h2

lemma schemeB_nonneg (j : ℕ) : 0 ≤ schemeB ε ᾱ j := by
  rw [schemeB_eq]
  positivity

lemma floor_two_pow : ⌊(2 : ℝ) ^ schemeS ε ᾱ⌋₊ = 2 ^ schemeS ε ᾱ := by
  rw [show (2 : ℝ) ^ schemeS ε ᾱ = ((2 ^ schemeS ε ᾱ : ℕ) : ℝ) by push_cast; ring]
  exact Nat.floor_natCast _

/-- `b_0 = 1`. -/
lemma schemeB_zero : schemeB ε ᾱ 0 = 1 := by
  have h2 : (0 : ℝ) < 2 ^ schemeS ε ᾱ := by positivity
  rw [schemeB_eq, pow_zero, mul_one, floor_two_pow]
  push_cast
  exact div_self h2.ne'

/-- `b_j` is nonincreasing in `j`. -/
lemma schemeB_antitone (hε : ε ∈ Set.Ioo (0 : ℝ) 1) : Antitone (schemeB ε ᾱ) := by
  intro i j hij
  have h2 : (0 : ℝ) < 2 ^ schemeS ε ᾱ := by positivity
  rw [schemeB_eq, schemeB_eq]
  refine div_le_div_of_nonneg_right ?_ h2.le
  exact_mod_cast Nat.floor_le_floor (mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one (q_pos hε).le (q_lt_one hε).le hij) h2.le)

/-- Every `α̂_j` lies in `[0, 1]` (not in the paper: it leaves this implicit):
`α̂_j = 1 − b_j` with `0 ≤ b_j ≤ (1 − ε')^j ≤ 1`. -/
lemma schemeShare_mem (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (j : ℕ) :
    schemeShare ε ᾱ j ∈ Set.Icc (0 : ℝ) 1 := by
  have h1 := schemeB_le (ᾱ := ᾱ) hε j
  have h2 := schemeB_nonneg (ε := ε) (ᾱ := ᾱ) j
  have h3 : (1 - schemeEps ε) ^ j ≤ 1 := pow_le_one₀ (q_pos hε).le (q_lt_one hε).le
  rw [schemeShare_eq]
  constructor <;> linarith

/-- Every `α̂_j` is a dyadic rational with `s` bits (`IsDyadic s`): `α̂_j = k/2^s` for the integer
`k = 2^s − ⌊2^s (1 − ε')^j⌋` (not in the paper: the proof calls the shares dyadic,
appE-halfrule.tex:5, by their form). -/
lemma schemeShare_dyadic (j : ℕ) : IsDyadic (schemeS ε ᾱ) (schemeShare ε ᾱ j) := by
  refine ⟨2 ^ schemeS ε ᾱ - ⌊(2 : ℝ) ^ schemeS ε ᾱ * (1 - schemeEps ε) ^ j⌋₊, ?_⟩
  have h2 : (0 : ℝ) < 2 ^ schemeS ε ᾱ := by positivity
  push_cast
  rw [sub_div, div_self h2.ne']

/-- The proof of `thm:fptas`, "Finally": `J ≤ ⌈ln(1/(1 − ᾱ))/ln(1/(1 − ε'))⌉`, by the minimality
of `J`. -/
lemma schemeJ_le_log (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hᾱ : ᾱ < 1) :
    schemeJ ε ᾱ ≤ ⌈Real.log (1 / (1 - ᾱ)) / Real.log (1 / (1 - schemeEps ε))⌉₊ := by
  set N := ⌈Real.log (1 / (1 - ᾱ)) / Real.log (1 / (1 - schemeEps ε))⌉₊
  have hq := q_pos hε
  have hᾱ0 : 0 < 1 - ᾱ := sub_pos.2 hᾱ
  have hL : 0 < Real.log (1 / (1 - schemeEps ε)) :=
    Real.log_pos (by rw [lt_div_iff₀ hq]; linarith [q_lt_one hε])
  have hN : Real.log (1 / (1 - ᾱ)) / Real.log (1 / (1 - schemeEps ε)) ≤ N := Nat.le_ceil _
  rw [div_le_iff₀ hL] at hN
  -- `ln((1 − ε')^N) = −N ln(1/(1 − ε')) ≤ −ln(1/(1 − ᾱ)) = ln(1 − ᾱ)`
  have hlog : Real.log ((1 - schemeEps ε) ^ N) ≤ Real.log (1 - ᾱ) := by
    rw [Real.log_pow, show Real.log (1 - schemeEps ε) = -Real.log (1 / (1 - schemeEps ε)) by
      rw [one_div, Real.log_inv, neg_neg], show Real.log (1 - ᾱ) = -Real.log (1 / (1 - ᾱ)) by
      rw [one_div, Real.log_inv, neg_neg]]
    linarith
  exact Nat.sInf_le (show (1 - schemeEps ε) ^ N ≤ 1 - ᾱ from
    (Real.log_le_log_iff (by positivity) hᾱ0).1 hlog)

/-- The proof of `thm:fptas`, "Finally":
`⌈ln(1/(1 − ᾱ))/ln(1/(1 − ε'))⌉ ≤ ⌈ln(1/(1 − ᾱ))/ε'⌉`, as `ln(1/(1 − ε')) ≥ ε'`. -/
lemma ceil_log_div_le (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hᾱ0 : 0 ≤ ᾱ) (hᾱ : ᾱ < 1) :
    ⌈Real.log (1 / (1 - ᾱ)) / Real.log (1 / (1 - schemeEps ε))⌉₊ ≤
      ⌈Real.log (1 / (1 - ᾱ)) / schemeEps ε⌉₊ := by
  have hq := q_pos hε
  have hε2 : 0 < schemeEps ε := by linarith [q_lt_one hε]
  have hlog0 : 0 ≤ Real.log (1 / (1 - ᾱ)) :=
    Real.log_nonneg (by rw [le_div_iff₀ (sub_pos.2 hᾱ)]; linarith)
  -- `ln(1/(1 − ε')) = −ln(1 − ε') ≥ ε'`
  have hge : schemeEps ε ≤ Real.log (1 / (1 - schemeEps ε)) := by
    have := Real.log_le_sub_one_of_pos hq
    rw [one_div, Real.log_inv]
    linarith
  exact Nat.ceil_mono (div_le_div_of_nonneg_left hlog0 hε2 hge)

/-- `J ≤ ⌈2ε⁻¹ ln(1/(1 − ᾱ))⌉`, so `J + 1 ≤ ⌈2ε⁻¹ ln(1/(1 − ᾱ))⌉ + 1`: the chain of
`schemeJ_le_log` and `ceil_log_div_le`, with `ln(1/(1 − ᾱ))/ε' = 2ε⁻¹ ln(1/(1 − ᾱ))`. -/
lemma schemeJ_le (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hᾱ0 : 0 ≤ ᾱ) (hᾱ : ᾱ < 1) :
    schemeJ ε ᾱ ≤ ⌈2 / ε * Real.log (1 / (1 - ᾱ))⌉₊ := by
  have e : Real.log (1 / (1 - ᾱ)) / schemeEps ε = 2 / ε * Real.log (1 / (1 - ᾱ)) := by
    unfold schemeEps
    field_simp [hε.1.ne']
  exact (schemeJ_le_log hε hᾱ).trans ((ceil_log_div_le hε hᾱ0 hᾱ).trans (by rw [e]))

/-- The proof of `thm:fptas`, "Finally": `s ≤ log₂(4/(ε(1 − ᾱ))) + 1`. -/
lemma schemeS_le (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hᾱ0 : 0 ≤ ᾱ) (hᾱ : ᾱ < 1) :
    (schemeS ε ᾱ : ℝ) ≤ Real.logb 2 (4 / (ε * (1 - ᾱ))) + 1 := by
  have hεᾱ : 0 < ε * (1 - ᾱ) := mul_pos hε.1 (sub_pos.2 hᾱ)
  have hεᾱ1 : ε * (1 - ᾱ) ≤ 1 := by nlinarith [hε.2]
  have h0 : 0 ≤ Real.logb 2 (4 / (ε * (1 - ᾱ))) :=
    Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ hεᾱ]; linarith)
  exact (Nat.ceil_lt_add_one h0).le

/-- `s = O(1 + log(1/ε) + log(1/(1 − ᾱ)))`:
`log₂(4/(ε(1 − ᾱ))) + 1 = 3 + log₂(1/ε) + log₂(1/(1 − ᾱ))`. -/
lemma logb_four_div (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hᾱ : ᾱ < 1) :
    Real.logb 2 (4 / (ε * (1 - ᾱ))) + 1 =
      3 + Real.logb 2 (1 / ε) + Real.logb 2 (1 / (1 - ᾱ)) := by
  have hε0 := hε.1
  have hᾱ0 : 0 < 1 - ᾱ := sub_pos.2 hᾱ
  have e : 4 / (ε * (1 - ᾱ)) = 4 * ((1 / ε) * (1 / (1 - ᾱ))) := by field_simp
  rw [e, Real.logb_mul (by norm_num) (by positivity), Real.logb_mul (by positivity) (by positivity),
    show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)]
  ring

end Shares

/-! ### `thm:fptas` -/

section Fptas

variable {E : Type*} [Fintype E]

/-- **`thm:fptas`** for the shares `α̂_j` of its proof and any reward curve `S` that is nonnegative
and nondecreasing on `[0, 1]`, with `U_P(α) = (1 − α) S(α)` (`profit S`): the scheme evaluates the
`J + 1 ≤ ⌈2ε⁻¹ ln(1/(1 − ᾱ))⌉ + 1` shares `α̂_j` (`schemeShares`), each in `[0, 1]` and dyadic with
`s ≤ 3 + log₂(1/ε) + log₂(1/(1 − ᾱ))` bits, and for every such curve for which `ᾱ` is a share
bound, some `α̂_j` has `U_P(α̂_j) ≥ (1 − ε) OPT`, and so has every `α̂_j` with the largest utility.
The proof of `thm:fptas` uses of the best responses only that their reward `S(α) = r(x*(α))` is
nondecreasing, by `lem:monreward` ("By `lem:monreward`, `r(x*(α̂_j)) ≥ r(x*(α))`",
appE-halfrule.tex:15), which is the hypothesis on `S` here; it uses tacitly that the reward is
nonnegative. The exact statement `fptas` follows with `lem:monreward` on any action set, and the
proof of `prop:convexscheme` takes this form for the shares `α̂_j` and the best responses `x*(α)` of
`app:convex`: "the shares constructed in the proof of `thm:fptas`" (appF-convex.tex:75), and "The
proof of `thm:fptas` uses only `lem:monreward`, which holds for all maximizers, so the theorem
applies to the best responses `x*(α)` and the share bound `ᾱ` shown above" (appF-convex.tex:103).

The proof is that of appE-halfrule.tex:5-19: (0) the definitions of `ε'`, `J`, `s` and the shares
`α̂_j` (`schemeEps`, `schemeJ`, `schemeS`, `schemeShare`, `schemeShares`), and "There are at most
`⌈2ε⁻¹ ln(1/(1 − ᾱ))⌉ + 1` shares", which (8) shows;
(1) `b_j = 1 − α̂_j`: `b_0 = 1`, `b_j` is nonincreasing and
`(1 − ε')^j − 2^{−s} < b_j ≤ (1 − ε')^j`;
(2) for `α ∈ [0, ᾱ]` some `j` has `U_P(α̂_j) ≥ (1 − ε) U_P(α)`, which proves the claim as `ᾱ` is a
share bound; (3) there is a smallest `j` with `b_j ≤ 1 − α`; (4) the case `j = 0`; (5) otherwise
`b_{j−1} > 1 − α` and `(1 − ε')^{j−1} > 1 − ᾱ`; (6) with `2^{−s} ≤ ε(1 − ᾱ)/4`
(`one_div_two_pow_schemeS_le`), the displayed chain `b_j > … ≥ (1 − ε) b_{j−1}`; (7) by
`lem:monreward` (here the hypothesis on `S`), `r(x*(α̂_j)) ≥ r(x*(α))`, and the displayed chain
`U_P(α̂_j) = b_j r(x*(α̂_j)) ≥ … = (1 − ε) U_P(α)`; (8) "Finally,
`J ≤ ⌈ln(1/(1 − ᾱ))/ln(1/(1 − ε'))⌉ ≤ ⌈ln(1/(1 − ᾱ))/ε'⌉`, and `s ≤ log₂(4/(ε(1 − ᾱ))) + 1`"
(`schemeJ_le_log` and `ceil_log_div_le`, chained in `schemeJ_le`, and `schemeS_le`, with
`logb_four_div` for the `O`). That `α̂_j ∈ [0, 1]` is `schemeShare_mem`, and the dyadic form is
`schemeShare_dyadic` (both not in the proof). -/
theorem fptas_aux {ε ᾱ : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hᾱ : ᾱ ∈ Set.Ico (0 : ℝ) 1) :
    schemeJ ε ᾱ + 1 ≤ ⌈2 / ε * Real.log (1 / (1 - ᾱ))⌉₊ + 1 ∧
    (∀ j ≤ schemeJ ε ᾱ, schemeShare ε ᾱ j ∈ Set.Icc (0 : ℝ) 1 ∧
      IsDyadic (schemeS ε ᾱ) (schemeShare ε ᾱ j)) ∧
    (schemeS ε ᾱ : ℝ) ≤ 3 + Real.logb 2 (1 / ε) + Real.logb 2 (1 / (1 - ᾱ)) ∧
    ∀ S : ℝ → ℝ, MonotoneOn S (Set.Icc 0 1) → (∀ α ∈ Set.Icc (0 : ℝ) 1, 0 ≤ S α) →
      IsShareBound (profit S) ᾱ →
      (∃ j ≤ schemeJ ε ᾱ, (1 - ε) * OPT (profit S) ≤ profit S (schemeShare ε ᾱ j)) ∧
      ∀ q ∈ schemeShares ε ᾱ, (∀ q' ∈ schemeShares ε ᾱ, profit S q' ≤ profit S q) →
        IsApproxOptimal (profit S) ε q := by
  -- (0) "Put `ε' := ε/2`, `J := min{j ≥ 0 : (1 − ε')^j ≤ 1 − ᾱ}` and
  -- `s := ⌈log₂(4/(ε(1 − ᾱ)))⌉`. The scheme evaluates the dyadic shares
  -- `α̂_j := 1 − 2^{−s} ⌊2^s (1 − ε')^j⌋`, `j = 0, …, J`, and returns the one with largest
  -- utility." (`schemeEps`, `schemeJ`, `schemeS`, `schemeShare`, `schemeShares`) "There are at most
  -- `⌈2ε⁻¹ ln(1/(1 − ᾱ))⌉ + 1` shares." (shown in (8))
  set J := schemeJ ε ᾱ with hJ
  set ε' := schemeEps ε with hε'
  have hε'2 : ε' = ε / 2 := rfl
  obtain ⟨hᾱ0, hᾱ1⟩ := hᾱ
  have hguar : ∀ S : ℝ → ℝ, MonotoneOn S (Set.Icc 0 1) → (∀ α ∈ Set.Icc (0 : ℝ) 1, 0 ≤ S α) →
      IsShareBound (profit S) ᾱ →
      (∃ j ≤ J, (1 - ε) * OPT (profit S) ≤ profit S (schemeShare ε ᾱ j)) ∧
      ∀ q ∈ schemeShares ε ᾱ, (∀ q' ∈ schemeShares ε ᾱ, profit S q' ≤ profit S q) →
        IsApproxOptimal (profit S) ε q := by
    intro S hmono hnn hsb
    set U := profit S with hU
    -- (1) "Let `b_j := 1 − α̂_j`. Then `b_0 = 1`, `b_j` is nonincreasing in `j`, and
    -- `(1 − ε')^j − 2^{−s} < b_j ≤ (1 − ε')^j`."
    have hb0 : schemeB ε ᾱ 0 = 1 := schemeB_zero
    have _hbanti : Antitone (schemeB ε ᾱ) := schemeB_antitone hε
    have hbgt : ∀ j, (1 - ε') ^ j - 1 / 2 ^ schemeS ε ᾱ < schemeB ε ᾱ j := schemeB_gt
    have hble : ∀ j, schemeB ε ᾱ j ≤ (1 - ε') ^ j := schemeB_le hε
    -- (2) "Let `α ∈ [0, ᾱ]`. We show that `U_P(α̂_j) ≥ (1 − ε) U_P(α)` for some `j`, …"
    have key : ∀ α ∈ Set.Icc (0 : ℝ) ᾱ, ∃ j ≤ J, (1 - ε) * U α ≤ U (schemeShare ε ᾱ j) := by
      intro α hα
      have hα01 : α ∈ Set.Icc (0 : ℝ) 1 := ⟨hα.1, by linarith [hα.2]⟩
      -- (3) "As `b_J ≤ (1 − ε')^J ≤ 1 − ᾱ ≤ 1 − α`, there is a smallest `j` with `b_j ≤ 1 − α`,
      -- that is, `α̂_j ≥ α`."
      have hbJ : schemeB ε ᾱ J ≤ 1 - α :=
        (hble J).trans ((schemeJ_mem hε hᾱ1).trans (by linarith [hα.2]))
      classical
      have hex : ∃ j, schemeB ε ᾱ j ≤ 1 - α := ⟨J, hbJ⟩
      set j := Nat.find hex with hjdef
      have hj : schemeB ε ᾱ j ≤ 1 - α := Nat.find_spec hex
      have hjJ : j ≤ J := Nat.find_min' hex hbJ
      have hge : α ≤ schemeShare ε ᾱ j := by rw [schemeShare_eq]; linarith
      refine ⟨j, hjJ, ?_⟩
      have hmem := schemeShare_mem (ᾱ := ᾱ) hε j
      have hε1 : 0 ≤ 1 - ε := by linarith [hε.2]
      rcases Nat.eq_zero_or_eq_succ_pred j with h0 | hsucc
      · -- (4) "If `j = 0`, then `α = 0 = α̂_0`." (`U_P(0) ≥ 0` is left implicit.)
        rw [h0, hb0] at hj
        have hα0 : α = 0 := le_antisymm (by linarith) hα.1
        have hs0 : schemeShare ε ᾱ j = 0 := by rw [h0, schemeShare_eq, hb0, sub_self]
        rw [hs0, ← hα0]
        have := profit_nonneg (S := S) hnn hα01
        rw [← hα0] at this
        nlinarith [hε.1]
      · -- (5) "Otherwise `b_{j−1} > 1 − α`, and `(1 − ε')^{j−1} > 1 − ᾱ` by the minimality of
        -- `J`."
        obtain ⟨i, hi⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        have hprev : 1 - α < schemeB ε ᾱ i := by
          have := Nat.find_min hex (show i < j by omega)
          exact not_le.1 this
        have hqi : 1 - ᾱ < (1 - ε') ^ i := lt_of_lt_schemeJ (by omega)
        -- (6) "With `2^{−s} ≤ ε(1 − ᾱ)/4 < ε'(1 − ᾱ)`,
        -- `b_j > (1 − ε')^j − ε'(1 − ᾱ) > (1 − ε')^j − ε'(1 − ε')^{j−1}`
        -- `= (1 − ε)(1 − ε')^{j−1} ≥ (1 − ε) b_{j−1}`."
        have h2s : 1 / 2 ^ schemeS ε ᾱ ≤ ε * (1 - ᾱ) / 4 := one_div_two_pow_schemeS_le hε hᾱ1
        have h2s' : ε * (1 - ᾱ) / 4 < ε' * (1 - ᾱ) := by
          have : 0 < ε * (1 - ᾱ) := mul_pos hε.1 (sub_pos.2 hᾱ1)
          rw [hε'2]
          linarith
        have hε'0 : 0 < ε' := by rw [hε'2]; linarith [hε.1]
        have hstep : schemeB ε ᾱ j > (1 - ε) * schemeB ε ᾱ i := by
          rw [hi]
          calc schemeB ε ᾱ (i + 1) > (1 - ε') ^ (i + 1) - ε' * (1 - ᾱ) := by
                linarith [hbgt (i + 1)]
            _ > (1 - ε') ^ (i + 1) - ε' * (1 - ε') ^ i := by
                have := mul_lt_mul_of_pos_left hqi hε'0
                linarith
            _ = (1 - ε) * (1 - ε') ^ i := by rw [hε'2]; ring
            _ ≥ (1 - ε) * schemeB ε ᾱ i := mul_le_mul_of_nonneg_left (hble i) hε1
        -- (7) "By `lem:monreward`, `r(x*(α̂_j)) ≥ r(x*(α))`, so
        -- `U_P(α̂_j) = b_j r(x*(α̂_j)) ≥ (1 − ε) b_{j−1} r(x*(α))`
        -- `≥ (1 − ε)(1 − α) r(x*(α)) = (1 − ε) U_P(α)`." Here `r(x*(α)) = S(α)`, and the
        -- conclusion of `lem:monreward` is `hmono`.
        have hmon : S α ≤ S (schemeShare ε ᾱ j) := hmono hα01 hmem hge
        have hrα := hnn α hα01
        calc U (schemeShare ε ᾱ j) = schemeB ε ᾱ j * S (schemeShare ε ᾱ j) := by
              rw [hU]; unfold profit schemeShare; ring
          _ ≥ (1 - ε) * schemeB ε ᾱ i * S α :=
              mul_le_mul hstep.le hmon hrα (schemeB_nonneg j)
          _ ≥ (1 - ε) * (1 - α) * S α :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprev.le hε1) hrα
          _ = (1 - ε) * U α := by rw [hU]; unfold profit; ring
    -- (2), continued: "… which proves the claim as `ᾱ` is a share bound": the largest of the
    -- utilities `U_P(α̂_j)` is at least `(1 − ε) sup_{α ∈ [0, ᾱ]} U_P(α) = (1 − ε) OPT`, and so is
    -- the utility of the share that the scheme returns.
    have hclaim : (1 - ε) * OPT U ≤
        (range (J + 1)).sup' nonempty_range_add_one fun j => U (schemeShare ε ᾱ j) := by
      have hε1 : 0 < 1 - ε := by linarith [hε.2]
      have hne : (U '' Set.Icc 0 ᾱ).Nonempty :=
        ⟨_, Set.mem_image_of_mem _ (show (0 : ℝ) ∈ Set.Icc 0 ᾱ from ⟨le_rfl, hᾱ0⟩)⟩
      rw [← hsb.2.2, ← le_div_iff₀' hε1]
      refine csSup_le hne ?_
      rintro _ ⟨α, hα, rfl⟩
      obtain ⟨j, hj, hjα⟩ := key α hα
      rw [le_div_iff₀' hε1]
      exact hjα.trans (le_sup' (fun j => U (schemeShare ε ᾱ j)) (mem_range.2 (by omega)))
    obtain ⟨j₀, hj₀, hj₀eq⟩ :=
      exists_mem_eq_sup' nonempty_range_add_one fun j => U (schemeShare ε ᾱ j)
    rw [hj₀eq] at hclaim
    have hj₀J : j₀ ≤ J := by have := mem_range.1 hj₀; omega
    refine ⟨⟨j₀, hj₀J, hclaim⟩, fun q hq hmax => ?_⟩
    obtain ⟨j, -, rfl⟩ := mem_schemeShares.1 hq
    exact ⟨schemeShare_mem hε j, hclaim.trans (hmax _ (mem_schemeShares.2 ⟨j₀, hj₀J, rfl⟩))⟩
  -- (8) "Finally, `J ≤ ⌈ln(1/(1 − ᾱ))/ln(1/(1 − ε'))⌉ ≤ ⌈ln(1/(1 − ᾱ))/ε'⌉`, …"
  have h8J : J + 1 ≤ ⌈2 / ε * Real.log (1 / (1 - ᾱ))⌉₊ + 1 := by
    have := schemeJ_le hε hᾱ0 hᾱ1
    omega
  -- "… and `s ≤ log₂(4/(ε(1 − ᾱ))) + 1`."
  have h8s : (schemeS ε ᾱ : ℝ) ≤ 3 + Real.logb 2 (1 / ε) + Real.logb 2 (1 / (1 - ᾱ)) := by
    rw [← logb_four_div hε hᾱ1]
    exact schemeS_le hε hᾱ0 hᾱ1
  -- Every `α̂_j` is a share in `[0, 1]` and a dyadic rational with `s` bits (not in the proof).
  exact ⟨h8J, fun j _ => ⟨schemeShare_mem hε j, schemeShare_dyadic j⟩, h8s, hguar⟩

/-- **`thm:fptas`** (Theorem 5.1, 08-approximation.tex:12-14, proof appE-halfrule.tex:4-20): "Given
an exact best-response oracle, a share bound `ᾱ ∈ [0, 1)` and `ε ∈ (0, 1)`, a `(1 − ε)`-optimal
contract can be found with at most `⌈2ε⁻¹ ln(1/(1 − ᾱ))⌉ + 1` oracle calls. The queried shares are
rationals with `O(1 + log(1/ε) + log(1/(1 − ᾱ)))` bits."

Here: for `ε ∈ (0, 1)` and `ᾱ ∈ [0, 1)` there is a list `Q` of at most `⌈2ε⁻¹ ln(1/(1 − ᾱ))⌉ + 1`
shares, each a dyadic rational `k/2^s` in `[0, 1]` (`IsDyadic s`) with
`s ≤ 3 + log₂(1/ε) + log₂(1/(1 − ᾱ))` bits, such that on every instance with an exact best-response
oracle (`IsExactOracle`: an action set `K`, rewards `m`, a cost `c` and the answers `x*(α)`) for
which `ᾱ` is a share bound, every share of `Q` with the largest utility `U_P(q) = (1 − q) r(x*(q))`
is `(1 − ε)`-optimal (`IsApproxOptimal`). The scheme calls the oracle at the shares of `Q`, which do
not depend on the instance, and returns one of them with the largest utility (see the module
docstring).

The proof is that of `fptas_aux` (appE-halfrule.tex:5-19), for the shares `α̂_j` of the proof
(`schemeShares`) and the reward `S(α) = r(x*(α))` of the oracle's answers, which is nondecreasing by
`lem:monreward` on the action set of the oracle (`monotoneOn_reward_of_isBR`), as step (7) cites it,
and nonnegative, as `m ≥ 0` and `K ⊆ ℝ^E_{≥0}`. -/
theorem fptas {ε ᾱ : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hᾱ : ᾱ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Q : List ℝ, Q ≠ [] ∧ Q.length ≤ ⌈2 / ε * Real.log (1 / (1 - ᾱ))⌉₊ + 1 ∧
      (∃ s : ℕ, (s : ℝ) ≤ 3 + Real.logb 2 (1 / ε) + Real.logb 2 (1 / (1 - ᾱ)) ∧
        ∀ q ∈ Q, q ∈ Set.Icc (0 : ℝ) 1 ∧ IsDyadic s q) ∧
      ∀ (K : Set (E → ℝ)) (m : E → ℝ) (c : (E → ℝ) → ℝ) (xs : ℝ → E → ℝ),
        IsExactOracle K m c xs → IsShareBound (profit fun α => reward m (xs α)) ᾱ →
        ∀ q ∈ Q, (∀ q' ∈ Q, profit (fun α => reward m (xs α)) q' ≤
            profit (fun α => reward m (xs α)) q) →
          IsApproxOptimal (profit fun α => reward m (xs α)) ε q := by
  -- the scheme of the proof of `thm:fptas`: the shares `α̂_0, …, α̂_J`
  obtain ⟨hcount, hbits, hs, hguar⟩ := fptas_aux hε hᾱ
  refine ⟨schemeShares ε ᾱ, schemeShares_ne_nil ε ᾱ, by rwa [length_schemeShares],
    ⟨schemeS ε ᾱ, hs, fun q hq => ?_⟩, fun K m c xs h hsb => ?_⟩
  · obtain ⟨j, hj, rfl⟩ := mem_schemeShares.1 hq
    exact hbits j hj
  -- "By `lem:monreward`, `r(x*(α̂_j)) ≥ r(x*(α))`": `lem:monreward` on the action set of the
  -- oracle; the rewards are nonnegative, as `m ≥ 0` and `K ⊆ ℝ^E_{≥0}`
  exact (hguar _ (monotoneOn_reward_of_isBR fun α hα => (h.isPBR α hα).isBR)
    (fun α hα => reward_nonneg_of_nonneg h.m_nonneg (h.nonneg _ (h.isPBR α hα).isBR.1)) hsb).2

end Fptas

/-! ### `cor:probe` -/

section Probe

variable {E : Type*} [Fintype E]

/-- `ᾱ_a = 1 − (1 − a) r(x*(a))/r(x*(1))` of `cor:probe`. -/
def probeAlpha (m : E → ℝ) (xs : ℝ → E → ℝ) (a : ℝ) : ℝ :=
  1 - (1 - a) * reward m (xs a) / reward m (xs 1)

/-- **`cor:probe`** (Corollary 5.2, 08-approximation.tex:19-21, proof appE-halfrule.tex:23-25): "Let
`ε ∈ (0, 1)`. For every `a ∈ [0, 1)` with `r(x*(a)) > 0`, the number
`ᾱ_a := 1 − (1 − a) r(x*(a))/r(x*(1))` is a share bound. So a `(1 − ε)`-optimal contract is found
with at most `⌈2ε⁻¹ ln(1/(1 − ᾱ_a))⌉ + 3` best-response calls."

Here: for `ε ∈ (0, 1)` there are lists `Q(ᾱ)` of shares, one for every number `ᾱ`, such that on
every instance with an exact best-response oracle (`IsExactOracle`) and for every `a ∈ [0, 1)` with
`r(x*(a)) > 0`, `ᾱ_a` (`probeAlpha`) is a share bound, `Q(ᾱ_a)` has at most
`⌈2ε⁻¹ ln(1/(1 − ᾱ_a))⌉ + 1` shares in `[0, 1]`, so that with the calls at `a` and `1`, which give
`ᾱ_a`, there are at most `⌈2ε⁻¹ ln(1/(1 − ᾱ_a))⌉ + 3` calls, and every share of `Q(ᾱ_a)` with the
largest utility is `(1 − ε)`-optimal (`IsApproxOptimal`). `Q(ᾱ)` is the list of `thm:fptas` for `ε`
and `ᾱ`.

The proof: (1) by `lem:monreward`, `0 < r(x*(a)) ≤ r(x*(1))`, so `a ≤ ᾱ_a < 1`; (2) for
`α > ᾱ_a`, again by `lem:monreward`,
`U_P(α) = (1 − α) r(x*(α)) ≤ (1 − α) r(x*(1)) < (1 − ᾱ_a) r(x*(1)) = U_P(a)`; (3) so
`sup_{α ∈ [0, ᾱ_a]} U_P(α) = OPT`; (4) by `thm:fptas` with `ᾱ = ᾱ_a`, at most
`⌈2ε⁻¹ ln(1/(1 − ᾱ_a))⌉ + 1` shares need to be tried, and the best responses at `a` and at `1` add
two more. `lem:monreward` is cited on the action set of the oracle (`monotoneOn_reward_of_isBR`). -/
theorem probe {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ Q : ℝ → List ℝ, ∀ (K : Set (E → ℝ)) (m : E → ℝ) (c : (E → ℝ) → ℝ) (xs : ℝ → E → ℝ),
      IsExactOracle K m c xs → ∀ a ∈ Set.Ico (0 : ℝ) 1, 0 < reward m (xs a) →
        IsShareBound (profit fun α => reward m (xs α)) (probeAlpha m xs a) ∧
        Q (probeAlpha m xs a) ≠ [] ∧
        (Q (probeAlpha m xs a)).length + 2 ≤
          ⌈2 / ε * Real.log (1 / (1 - probeAlpha m xs a))⌉₊ + 3 ∧
        (∀ q ∈ Q (probeAlpha m xs a), q ∈ Set.Icc (0 : ℝ) 1) ∧
        ∀ q ∈ Q (probeAlpha m xs a), (∀ q' ∈ Q (probeAlpha m xs a),
            profit (fun α => reward m (xs α)) q' ≤ profit (fun α => reward m (xs α)) q) →
          IsApproxOptimal (profit fun α => reward m (xs α)) ε q := by
  classical
  -- the lists of `thm:fptas` for `ε` and the share bounds `ᾱ ∈ [0, 1)` (for (4))
  refine ⟨fun ᾱ => if hᾱ : ᾱ ∈ Set.Ico (0 : ℝ) 1 then (fptas (E := E) hε hᾱ).choose else [],
    fun K m c xs h a ha hra => ?_⟩
  set U := profit fun α => reward m (xs α) with hU
  set ᾱ := probeAlpha m xs a with hᾱdef
  have hmono := monotoneOn_reward_of_isBR fun α hα => (h.isPBR α hα).isBR
  have hnn : ∀ α ∈ Set.Icc (0 : ℝ) 1, 0 ≤ reward m (xs α) := fun α hα =>
    reward_nonneg_of_nonneg h.m_nonneg (h.nonneg _ (h.isPBR α hα).isBR.1)
  have ha01 : a ∈ Set.Icc (0 : ℝ) 1 := ⟨ha.1, ha.2.le⟩
  have h1mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have h1a : 0 < 1 - a := by linarith [ha.2]
  -- (1) "By `lem:monreward`, `0 < r(x*(a)) ≤ r(x*(1))`, so `a ≤ ᾱ_a < 1`."
  have hS1 : reward m (xs a) ≤ reward m (xs 1) := hmono ha01 h1mem ha.2.le
  have hS1pos : 0 < reward m (xs 1) := lt_of_lt_of_le hra hS1
  have h1ᾱ : 1 - ᾱ = (1 - a) * reward m (xs a) / reward m (xs 1) := by
    rw [hᾱdef, probeAlpha]; ring
  have haᾱ : a ≤ ᾱ := by
    have : (1 - a) * reward m (xs a) / reward m (xs 1) ≤ 1 - a := by
      rw [div_le_iff₀ hS1pos]
      exact mul_le_mul_of_nonneg_left hS1 h1a.le
    linarith
  have hᾱ1 : ᾱ < 1 := by
    have : 0 < (1 - a) * reward m (xs a) / reward m (xs 1) := by positivity
    linarith
  -- (2) "For `α > ᾱ_a`, again by `lem:monreward`,
  -- `U_P(α) = (1 − α) r(x*(α)) ≤ (1 − α) r(x*(1)) < (1 − ᾱ_a) r(x*(1)) = U_P(a)`."
  have hUa : U a = (1 - ᾱ) * reward m (xs 1) := by
    rw [hU, h1ᾱ]
    unfold profit
    field_simp
  have hbig : ∀ α ∈ Set.Icc (0 : ℝ) 1, ᾱ < α → U α < U a := by
    intro α hα hlt
    have hSα : reward m (xs α) ≤ reward m (xs 1) := hmono hα h1mem hα.2
    calc U α = (1 - α) * reward m (xs α) := rfl
      _ ≤ (1 - α) * reward m (xs 1) := mul_le_mul_of_nonneg_left hSα (by linarith [hα.2])
      _ < (1 - ᾱ) * reward m (xs 1) := mul_lt_mul_of_pos_right (by linarith) hS1pos
      _ = U a := hUa.symm
  -- (3) "So `sup_{α ∈ [0, ᾱ_a]} U_P(α) = OPT`."
  have hsub : Set.Icc (0 : ℝ) ᾱ ⊆ Set.Icc 0 1 := Set.Icc_subset_Icc le_rfl hᾱ1.le
  have hamem : a ∈ Set.Icc (0 : ℝ) ᾱ := ⟨ha.1, haᾱ⟩
  have hbdd := bddAbove_profit hmono hnn _ hsub
  have hsb : IsShareBound U ᾱ := by
    refine ⟨ha.1.trans haᾱ, hᾱ1, le_antisymm ?_ ?_⟩
    · exact csSup_le_csSup (bddAbove_profit hmono hnn _ le_rfl) ⟨_, Set.mem_image_of_mem _ hamem⟩
        (Set.image_mono hsub)
    · refine csSup_le ⟨_, Set.mem_image_of_mem _ h1mem⟩ ?_
      rintro _ ⟨α, hα, rfl⟩
      rcases le_or_gt α ᾱ with hle | hlt
      · exact le_csSup hbdd (Set.mem_image_of_mem _ ⟨hα.1, hle⟩)
      · exact (hbig α hα hlt).le.trans (le_csSup hbdd (Set.mem_image_of_mem _ hamem))
  -- (4) "By `thm:fptas` with `ᾱ = ᾱ_a`, at most `⌈2ε⁻¹ ln(1/(1 − ᾱ_a))⌉ + 1` shares need to be
  -- tried, and the best responses at `a` and at `1` add two more."
  have hᾱmem : ᾱ ∈ Set.Ico (0 : ℝ) 1 := ⟨ha.1.trans haᾱ, hᾱ1⟩
  obtain ⟨hne, hlen, ⟨s, -, hQ⟩, hguar⟩ := (fptas (E := E) hε hᾱmem).choose_spec
  simp only [hᾱmem, ↓reduceDIte]
  exact ⟨hsb, hne, by omega, fun q hq => (hQ q hq).1, hguar K m c xs h hsb⟩

end Probe

end

end Stoc
