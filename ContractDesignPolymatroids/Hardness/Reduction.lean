-- stamp r10 2026-11-03
import ContractDesignPolymatroids.Hardness.Gadget

/-!
# The reduction from Subset Sum: `lem:coincidence`, `def:reduction`, `prop:correct`

The reduction of the STOC version's Appendix C.3 (`sec:D-correct`, "The gadget",
`stoc-sections/appD-hardness.tex:201-349`): `lem:coincidence` (lines 203-220; `fig:coincidence` at
lines 222-251 and the sentence "Both `μ` and `μ'` lie in `𝔉`" at line 253), `def:reduction` (lines
255-264, the sentence after it at line 266) and `prop:correct` (lines 268-270, proof lines 273-347,
and the sentence after the proof at line 349).

* `SubsetSum`: an instance `(a, T)` of Subset Sum; `SubsetSum.Yes`, `sumA` (`∑_i a_i`), `H`, `μ`,
  `μ'`, `Γ₁`, `Γ₂` (the notation of `lem:coincidence`);
* `coincidence`: `lem:coincidence`; `inF_μ`: `μ, μ' ∈ 𝔉`;
* `def:reduction`: `step1` (step (1)), `N₀`, `N₂`, `δ₁`, `δ₂`, `κ₁`, `κ₂`, `p₁`, `q₁`, `p₂`,
  `q₂` (step (2)), `fStar`, `mStar`, `βStar`, `p`, `q`, `κStar`, `c`, `ℓ` (step (3)), `Cond4`,
  `σ`, `αknob` (the share `α_∘` of the centering summand), `C`, `fHat`, `mHat`, `βHat` (step (4))
  and `ϑ` (step (5)); `rhsMin` (the smallest positive right-hand side of the conditions of
  step (4)) and `σ_spec`: `σ` exists and is at least `rhsMin/2` (the sentence after the
  definition);
* `prop:correct`: its proof has six parts, which open with "We first show that step (1) of
  `def:reduction` does not change the answer", "Next we show that `I*` is a comb …", "Then we show
  that the reward of `Î`, … stays below a line and touches it at the contacts", "We now show that
  `(1 − α)L̃(α)` is a parabola …", "With this, we prove the claim for yes-instances" and
  "Finally, we prove the claim for no-instances"; we number them (1)-(6). The parts (1)-(4) are
  `correct_step1` to `correct_step4` (with `Γstar`, `Γ* := Γ_1 ∩ Γ_2`, and `eq:D-parabola` in
  `correct_step4`), and (5) and (6) are in `correct`.

What is not formalised: the running time of the reduction. The bit lengths and the rational data
(the proof of NP-hardness in `thm:nphard`) are in `ReductionSizes.lean` (`reduction_sizes`).

Taken over on 2026-10-20 from `Paper/Hardness/Reduction.lean` (the paper at Overleaf f035b19) for
the STOC version (`stoc.tex`); from then on this copy follows the STOC version.
-/

namespace Stoc

namespace Hardness

open Finset

noncomputable section

/-! ### Subset Sum -/

/-- An instance `(a, T)` of Subset Sum (`stoc-sections/appD-hardness.tex:201`: "Let `(a, T)` be an
instance of Subset Sum with `k ≥ 1` and `a ∈ ℤ^k_{>0}`"): `k ≥ 1` items `a ∈ ℤ^k_{>0}` and a target
`T ∈ ℤ` (any integer: step (1) of `def:reduction` replaces `T < 0`). The items are
`a 0, …, a (k − 1)` (indices from `0`), natural numbers with `a i > 0`. -/
structure SubsetSum where
  /-- the number of items -/
  k : ℕ
  one_le_k : 1 ≤ k
  /-- the items -/
  a : ℕ → ℕ
  a_pos : ∀ i < k, 0 < a i
  /-- the target -/
  T : ℤ

namespace SubsetSum

variable (P : SubsetSum)

/-- `(a, T)` is a yes-instance: `a^⊤χ = T` for some `χ ∈ {0, 1}^k` (`χ` the indicator of
`Q ⊆ {0, …, k − 1}`). -/
def Yes : Prop := ∃ Q ⊆ range P.k, ∑ i ∈ Q, (P.a i : ℤ) = P.T

/-- The sum `∑_i a_i` of the items. -/
def sumA : ℕ := ∑ i ∈ range P.k, P.a i

/-- `H = 10∑_i a_i + 1` (`lem:coincidence`). -/
def H : ℕ := 10 * P.sumA + 1

/-- `μ_i = H 8^{i−1} + a_i` (`lem:coincidence`; indices from `0`, so `μ i = H 8^i + a i`). -/
def μ (i : ℕ) : ℕ := P.H * 8 ^ i + P.a i

/-- `μ'_i = H 8^{i−1}` (`lem:coincidence`; indices from `0`). -/
def μ' (i : ℕ) : ℕ := P.H * 8 ^ i

/-- `Γ_1 = {δ_1(N_0 + μ^⊤χ) : χ ∈ {0, 1}^k}` (`lem:coincidence`). -/
def Γ₁ (N₀ : ℤ) (δ₁ : ℝ) : Finset ℝ :=
  (range P.k).powerset.image fun Q => δ₁ * ((N₀ : ℝ) + ∑ i ∈ Q, (P.μ i : ℝ))

/-- `Γ_2 = {δ_1(N_0 + T + μ'^⊤χ') : χ' ∈ {0, 1}^k}` (`lem:coincidence`). -/
def Γ₂ (N₀ : ℤ) (δ₁ : ℝ) : Finset ℝ :=
  (range P.k).powerset.image fun Q => δ₁ * ((N₀ : ℝ) + P.T + ∑ i ∈ Q, (P.μ' i : ℝ))

end SubsetSum

/-! ### `lem:coincidence` -/

/-- **`lem:coincidence`** (Lemma C.7, `stoc-sections/appD-hardness.tex:203-214`, proof lines
218-220): let `0 ≤ T ≤ ∑_i a_i`, let `N_0 ∈ ℤ` and `δ_1 > 0`, and let `H := 10∑_i a_i + 1`. Define
`μ, μ' ∈ ℤ^k_{>0}` by `μ_i := H 8^{i−1} + a_i` and `μ'_i := H 8^{i−1}` for `i ∈ [k]` (`SubsetSum.μ`,
`SubsetSum.μ'`), and the sets `Γ_1 := {δ_1(N_0 + μ^⊤χ) : χ ∈ {0, 1}^k}` and
`Γ_2 := {δ_1(N_0 + T + μ'^⊤χ') : χ' ∈ {0, 1}^k}` (`SubsetSum.Γ₁`, `SubsetSum.Γ₂`). Then the common
points of `Γ_1` and `Γ_2` are the points `δ_1(N_0 + μ^⊤χ)` with `a^⊤χ = T` (the first conjunct:
`Γ_1 ∩ Γ_2` is the set of these points). In particular, `Γ_1` and `Γ_2` meet if and only if
`(a, T)` is a yes-instance (the second conjunct).

The proof's steps: (1) as `μ^⊤χ = H∑_iχ_i8^{i−1} + a^⊤χ` and `μ'^⊤χ' = H∑_iχ'_i8^{i−1}`, two points
coincide if and only if `H∑_i(χ_i − χ'_i)8^{i−1} = T − a^⊤χ`; (2) the right-hand side has absolute
value less than `H`, as `T, a^⊤χ ∈ [0, ∑_i a_i]`, and the left-hand side is a multiple of `H`, so
both vanish, and `a^⊤χ = T`; (3) conversely, `χ' := χ` gives a common point if `a^⊤χ = T`. -/
theorem coincidence (P : SubsetSum) (hT : 0 ≤ P.T) (hTA : P.T ≤ P.sumA) (N₀ : ℤ) {δ₁ : ℝ}
    (hδ : 0 < δ₁) :
    P.Γ₁ N₀ δ₁ ∩ P.Γ₂ N₀ δ₁ =
      ((range P.k).powerset.filter fun Q => ∑ i ∈ Q, (P.a i : ℤ) = P.T).image
        (fun Q => δ₁ * ((N₀ : ℝ) + ∑ i ∈ Q, (P.μ i : ℝ))) ∧
    ((P.Γ₁ N₀ δ₁ ∩ P.Γ₂ N₀ δ₁).Nonempty ↔ P.Yes) := by
  -- the indicator `χ` of `Q`, and `∑_{i∈Q} 8^i = ∑_i χ_i 8^i`
  set χ : Finset ℕ → ℕ → ℤ := fun Q i => if i ∈ Q then 1 else 0 with hχ
  have hχsum : ∀ Q ⊆ range P.k, ∑ i ∈ Q, (8 : ℤ) ^ i = ∑ i ∈ range P.k, χ Q i * 8 ^ i := by
    intro Q hQ
    simp only [hχ, ite_mul, one_mul, zero_mul]
    rw [sum_ite_mem, inter_eq_right.2 hQ]
  have hH : (0 : ℤ) < P.H := by unfold SubsetSum.H; positivity
  have hA : ∀ Q ⊆ range P.k, 0 ≤ ∑ i ∈ Q, (P.a i : ℤ) ∧ ∑ i ∈ Q, (P.a i : ℤ) ≤ P.sumA :=
    fun Q hQ => ⟨sum_nonneg fun i _ => by positivity, by
      unfold SubsetSum.sumA
      push_cast
      exact sum_le_sum_of_subset_of_nonneg hQ fun i _ _ => by positivity⟩
  -- (1) "As `μ^⊤χ = H∑_iχ_i8^{i−1} + a^⊤χ` and `μ'^⊤χ' = H∑_iχ'_i8^{i−1}`, two points coincide if
  -- and only if `H∑_i(χ_i − χ'_i)8^{i−1} = T − a^⊤χ`."
  have key : ∀ Q ⊆ range P.k, ∀ Q' ⊆ range P.k,
      (δ₁ * ((N₀ : ℝ) + ∑ i ∈ Q, (P.μ i : ℝ)) = δ₁ * ((N₀ : ℝ) + P.T + ∑ i ∈ Q', (P.μ' i : ℝ)) ↔
        (P.H : ℤ) * ∑ i ∈ range P.k, (χ Q i - χ Q' i) * 8 ^ i = P.T - ∑ i ∈ Q, (P.a i : ℤ)) := by
    intro Q hQ Q' hQ'
    have e1 : ∑ i ∈ Q, (P.μ i : ℤ) = P.H * ∑ i ∈ range P.k, χ Q i * 8 ^ i +
        ∑ i ∈ Q, (P.a i : ℤ) := by
      rw [← hχsum Q hQ, mul_sum, ← sum_add_distrib]
      simp [SubsetSum.μ]
    have e2 : ∑ i ∈ Q', (P.μ' i : ℤ) = P.H * ∑ i ∈ range P.k, χ Q' i * 8 ^ i := by
      rw [← hχsum Q' hQ', mul_sum]
      simp [SubsetSum.μ']
    have e3 : ∑ i ∈ range P.k, (χ Q i - χ Q' i) * 8 ^ i =
        ∑ i ∈ range P.k, χ Q i * 8 ^ i - ∑ i ∈ range P.k, χ Q' i * 8 ^ i := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun i _ => by ring
    rw [mul_right_inj' hδ.ne', add_assoc, add_right_inj, e3]
    constructor
    · intro h
      have h' : ((∑ i ∈ Q, (P.μ i : ℤ) : ℤ) : ℝ) = ((P.T + ∑ i ∈ Q', (P.μ' i : ℤ) : ℤ) : ℝ) := by
        push_cast
        exact h
      have h'' := Int.cast_injective h'
      rw [e1, e2] at h''
      linarith
    · intro h
      have h' : ∑ i ∈ Q, (P.μ i : ℤ) = P.T + ∑ i ∈ Q', (P.μ' i : ℤ) := by
        rw [e1, e2]
        linarith
      exact_mod_cast h'
  -- (2) "The right-hand side has absolute value less than `H`, as `T, a^⊤χ ∈ [0, ∑_i a_i]`, and the
  -- left-hand side is a multiple of `H`, so both vanish, and `a^⊤χ = T`."
  have hvanish : ∀ Q ⊆ range P.k, ∀ Q' ⊆ range P.k,
      (P.H : ℤ) * ∑ i ∈ range P.k, (χ Q i - χ Q' i) * 8 ^ i = P.T - ∑ i ∈ Q, (P.a i : ℤ) →
        ∑ i ∈ range P.k, (χ Q i - χ Q' i) * 8 ^ i = 0 ∧ P.T - ∑ i ∈ Q, (P.a i : ℤ) = 0 := by
    intro Q hQ Q' _ h
    obtain ⟨a1, a2⟩ := hA Q hQ
    have hlt : |P.T - ∑ i ∈ Q, (P.a i : ℤ)| < P.H := by
      rw [abs_lt]
      unfold SubsetSum.H
      push_cast
      constructor <;> linarith
    have hD : ∑ i ∈ range P.k, (χ Q i - χ Q' i) * 8 ^ i = 0 := by
      by_contra hne
      have h1 : 1 ≤ |∑ i ∈ range P.k, (χ Q i - χ Q' i) * 8 ^ i| := Int.one_le_abs hne
      have h2 : |(P.H : ℤ) * ∑ i ∈ range P.k, (χ Q i - χ Q' i) * 8 ^ i| =
          P.H * |∑ i ∈ range P.k, (χ Q i - χ Q' i) * 8 ^ i| := by
        rw [abs_mul, abs_of_pos hH]
      rw [h] at h2
      nlinarith
    refine ⟨hD, ?_⟩
    rw [hD, mul_zero] at h
    exact h.symm
  -- (3) "Conversely, `χ' := χ` gives a common point if `a^⊤χ = T`."
  have hconv : ∀ Q ⊆ range P.k, ∑ i ∈ Q, (P.a i : ℤ) = P.T →
      δ₁ * ((N₀ : ℝ) + ∑ i ∈ Q, (P.μ i : ℝ)) = δ₁ * ((N₀ : ℝ) + P.T + ∑ i ∈ Q, (P.μ' i : ℝ)) := by
    intro Q hQ h
    rw [key Q hQ Q hQ]
    simp only [sub_self, zero_mul, sum_const_zero, mul_zero]
    rw [h, sub_self]
  have hset : P.Γ₁ N₀ δ₁ ∩ P.Γ₂ N₀ δ₁ =
      ((range P.k).powerset.filter fun Q => ∑ i ∈ Q, (P.a i : ℤ) = P.T).image
        (fun Q => δ₁ * ((N₀ : ℝ) + ∑ i ∈ Q, (P.μ i : ℝ))) := by
    ext x
    simp only [mem_inter, SubsetSum.Γ₁, SubsetSum.Γ₂, mem_image, mem_filter, mem_powerset]
    constructor
    · rintro ⟨⟨Q, hQ, rfl⟩, ⟨Q', hQ', hx⟩⟩
      obtain ⟨hD, hT'⟩ := hvanish Q hQ Q' hQ' ((key Q hQ Q' hQ').1 hx.symm)
      exact ⟨Q, ⟨hQ, by linarith⟩, rfl⟩
    · rintro ⟨Q, ⟨hQ, hsum⟩, rfl⟩
      exact ⟨⟨Q, hQ, rfl⟩, ⟨Q, hQ, (hconv Q hQ hsum).symm⟩⟩
  refine ⟨hset, ?_⟩
  -- "In particular, `Γ_1` and `Γ_2` meet if and only if `(a, T)` is a yes-instance."
  rw [hset, image_nonempty, filter_nonempty_iff]
  constructor
  · rintro ⟨Q, hQ, h⟩
    exact ⟨Q, mem_powerset.1 hQ, h⟩
  · rintro ⟨Q, hQ, h⟩
    exact ⟨Q, mem_powerset.2 hQ, h⟩

/-- "Both `μ` and `μ'` lie in `𝔉`, as `a_i ≤ ∑_j a_j < H/10`" (after `lem:coincidence`,
`stoc-sections/appD-hardness.tex:253`). -/
theorem inF_μ (P : SubsetSum) : InF P.μ P.k ∧ InF P.μ' P.k := by
  have hH : (1 : ℝ) ≤ P.H := by
    have : 1 ≤ P.H := by unfold SubsetSum.H; omega
    exact_mod_cast this
  have hai : ∀ i < P.k, (P.a i : ℝ) < P.H / 10 := by
    intro i hi
    have h1 : P.a i ≤ P.sumA := single_le_sum (fun j _ => Nat.zero_le _) (mem_range.2 hi)
    have h2 : (P.a i : ℝ) ≤ P.sumA := by exact_mod_cast h1
    have h3 : (P.H : ℝ) = 10 * P.sumA + 1 := by unfold SubsetSum.H; push_cast; ring
    rw [h3]
    linarith
  refine ⟨⟨P.one_le_k, fun i _ => by unfold SubsetSum.μ SubsetSum.H; positivity,
    P.H, by unfold SubsetSum.H; omega, fun i hi => ⟨?_, ?_⟩⟩,
    ⟨P.one_le_k, fun i _ => by unfold SubsetSum.μ' SubsetSum.H; positivity,
    P.H, by unfold SubsetSum.H; omega, fun i _ => ⟨?_, ?_⟩⟩⟩
  · unfold SubsetSum.μ
    push_cast
    have : (0 : ℝ) ≤ P.a i := Nat.cast_nonneg _
    linarith
  · unfold SubsetSum.μ
    push_cast
    have h8 : (1 : ℝ) ≤ 8 ^ i := one_le_pow₀ (by norm_num)
    have := hai i hi
    nlinarith
  · unfold SubsetSum.μ'
    push_cast
    exact le_rfl
  · unfold SubsetSum.μ'
    push_cast
    have : (0 : ℝ) < 8 ^ i := by positivity
    nlinarith

/-! ### `def:reduction`

The steps (1)-(5) of `def:reduction` (`stoc-sections/appD-hardness.tex:255-264`); the sentence after
the definition (line 266) is `rhsMin` and `σ_spec` (`σ` exists), `C > 0` (in `correct_step3`) and
the vertex of the parabola (`correct_step4`). -/

namespace SubsetSum

variable (P : SubsetSum)

/-- **`def:reduction`** (Definition C.8, `stoc-sections/appD-hardness.tex:255-264`), step (1): if
`T < 0` or `T > ∑_i a_i`, replace `(a, T)` by the no-instance `a = (2)`, `T = 1`. The steps (2)-(5)
are the definitions that follow: (2) `N₀`, with `H`, `μ` and `μ'` of `lem:coincidence`; (3) `I_2'`
and `I* := I_1 ⊕ I_2'` (`N₂`, `δ₁`, `δ₂`, `fStar`, `mStar`, `βStar`, with `p`, `q`, `κStar`, `c`,
`ℓ`); (4) `σ` (`Cond4`, `σ`); (5) the output `Î` (`fHat`, `mHat`, `βHat`, with `αknob` and `C`) and
`ϑ`. -/
def step1 : SubsetSum :=
  if P.T < 0 ∨ (P.sumA : ℤ) < P.T then ⟨1, le_rfl, fun _ => 2, fun _ _ => two_pos, 1⟩ else P

/-- Step (2): `N_0 := max(N_min(μ), N_min(μ'))`, with `H, μ, μ'` as in `lem:coincidence`. -/
def N₀ : ℕ := max (gNmin P.μ P.k) (gNmin P.μ' P.k)

/-- `N_0 + T`, the offset of `I_2 := I(μ', N_0 + T)` (a natural number, as `T ≥ 0` after
step (1)). -/
def N₂ : ℕ := P.N₀ + P.T.toNat

/-- The width `δ_1` of `I_1 := I(μ, N_0)` (`thm:gadget`). -/
def δ₁ : ℝ := δT P.μ

/-- The width `δ_2` of `I_2`. -/
def δ₂ : ℝ := δT P.μ'

/-- The dip `κ_1` of `I_1`. -/
def κ₁ : ℝ := κT P.μ

/-- The dip `κ_2` of `I_2`. -/
def κ₂ : ℝ := κT P.μ'

/-- The line `p_1 + q_1α` of `I_1`: `p_1`. -/
def p₁ : ℝ := gp P.μ P.k P.N₀

/-- `q_1`. -/
def q₁ : ℝ := gq P.μ P.k

/-- The line `p_2 + q_2α` of `I_2`: `p_2`. -/
def p₂ : ℝ := gp P.μ' P.k P.N₂

/-- `q_2`. -/
def q₂ : ℝ := gq P.μ' P.k

/-- Step (3): the rank function of `I* := I_1 ⊕ I_2'`, where `I_2'` is `I_2` with `m` replaced
by `(δ_2/δ_1)m` (the rank function of `I_2` is unchanged). -/
def fStar : Finset ((Gr (P.k - 1) ⊕ Unit) ⊕ (Gr (P.k - 1) ⊕ Unit)) → ℝ :=
  dsum (gadgetF P.μ P.k P.N₀) (gadgetF P.μ' P.k P.N₂)

/-- The rewards of `I*`: those of `I_1`, and those of `I_2'`, which is `I_2` with `m` replaced by
`(δ_2/δ_1)m`. -/
def mStar : (Gr (P.k - 1) ⊕ Unit) ⊕ (Gr (P.k - 1) ⊕ Unit) → ℝ :=
  Sum.elim (gadgetM P.μ P.k) fun e => P.δ₂ / P.δ₁ * gadgetM P.μ' P.k e

/-- The curvatures of `I*`. -/
def βStar : (Gr (P.k - 1) ⊕ Unit) ⊕ (Gr (P.k - 1) ⊕ Unit) → ℝ :=
  Sum.elim (gadgetB P.μ P.k P.N₀) (gadgetB P.μ' P.k P.N₂)

/-- `p := p_1 + (δ_2/δ_1)p_2`. -/
def p : ℝ := P.p₁ + P.δ₂ / P.δ₁ * P.p₂

/-- `q := q_1 + (δ_2/δ_1)²q_2`. -/
def q : ℝ := P.q₁ + (P.δ₂ / P.δ₁) ^ 2 * P.q₂

/-- `κ* := min(κ_1, (δ_2/δ_1)²κ_2)`. -/
def κStar : ℝ := min P.κ₁ ((P.δ₂ / P.δ₁) ^ 2 * P.κ₂)

/-- Step (3): `c`, the center of `[δ_1N_0, δ_1(N_0 + ∑_iμ_i)]`. -/
def c : ℝ := (P.δ₁ * P.N₀ + P.δ₁ * (P.N₀ + ∑ i ∈ range P.k, (P.μ i : ℝ))) / 2

/-- Step (3): `ℓ`, the half-length of `[δ_1N_0, δ_1(N_0 + ∑_iμ_i)]`. -/
def ℓ : ℝ := (P.δ₁ * (P.N₀ + ∑ i ∈ range P.k, (P.μ i : ℝ)) - P.δ₁ * P.N₀) / 2

/-- The four conditions of step (4) on `σ`: `σ ≤ 1`, `σ ≤ κ*δ_1/(4qℓ²)`, `σ(c + ℓ) ≤ 1/4`, and
`σ(p + 2qc) < q`. -/
def Cond4 (σ : ℝ) : Prop :=
  σ ≤ 1 ∧ σ ≤ P.κStar * P.δ₁ / (4 * P.q * P.ℓ ^ 2) ∧ σ * (P.c + P.ℓ) ≤ 1 / 4 ∧
    σ * (P.p + 2 * P.q * P.c) < P.q

open Classical in
/-- Step (4): `σ`, the largest power of `2` with the four conditions `Cond4`. As `σ ≤ 1`, the
powers of `2` in question are the `2^{−j}`, `j ≥ 0`, and the largest is the one with the least `j`
(`σ_spec`; the value `1` in the other case is never used, as `σ` exists). -/
def σ : ℝ := if h : ∃ j : ℕ, P.Cond4 ((1 / 2) ^ j) then (1 / 2) ^ Nat.find h else 1

/-- Step (4): the share `α_∘ := σδ_1N_0` of the centering summand. -/
def αknob : ℝ := P.σ * P.δ₁ * P.N₀

/-- Step (4): the capacity `C := (q(1 − 2σc) − σp)/σ²` of the centering summand (by the last
condition of step (4), `C > 0`: `correct_step3`). -/
def C : ℝ := (P.q * (1 - 2 * P.σ * P.c) - P.σ * P.p) / P.σ ^ 2

/-- Step (4): the rank function of `Î`, which is `I*` with `m` replaced by `m/σ`, plus a capped
linear summand (`lem:ops`(c), `knob`), the centering summand, with `α_∘` and `C`. -/
def fHat : Finset (((Gr (P.k - 1) ⊕ Unit) ⊕ (Gr (P.k - 1) ⊕ Unit)) ⊕ Unit) → ℝ :=
  knob P.fStar P.C

/-- The rewards of `Î`: `m/σ` on `I*`, and `1` for the centering summand. -/
def mHat : ((Gr (P.k - 1) ⊕ Unit) ⊕ (Gr (P.k - 1) ⊕ Unit)) ⊕ Unit → ℝ :=
  Sum.elim (fun e => P.mStar e / P.σ) fun _ => 1

/-- The curvatures of `Î`: those of `I*`, and `α_∘/C` for the centering summand. -/
def βHat : ((Gr (P.k - 1) ⊕ Unit) ⊕ (Gr (P.k - 1) ⊕ Unit)) ⊕ Unit → ℝ :=
  Sum.elim P.βStar fun _ => P.αknob / P.C

/-- Step (5): `ϑ := (q/σ²)((1 − σc)² − σ²ℓ²)`. -/
def ϑ : ℝ := P.q / P.σ ^ 2 * ((1 - P.σ * P.c) ^ 2 - P.σ ^ 2 * P.ℓ ^ 2)

/-- The smallest of the positive right-hand sides of the conditions of step (4) (the sentence
after `def:reduction`, `stoc-sections/appD-hardness.tex:266`): of `σ ≤ 1`,
`σ ≤ κ*δ_1/(4qℓ²)`, `σ ≤ 1/(4(c + ℓ))` (that is, `σ(c + ℓ) ≤ 1/4`) and, if `p + 2qc > 0`,
`σ < q/(p + 2qc)` (that is, `σ(p + 2qc) < q`); for `p + 2qc ≤ 0` the last condition is vacuous
and has no right-hand side. -/
def rhsMin : ℝ :=
  if 0 < P.p + 2 * P.q * P.c then
    min (min 1 (P.κStar * P.δ₁ / (4 * P.q * P.ℓ ^ 2)))
      (min (1 / (4 * (P.c + P.ℓ))) (P.q / (P.p + 2 * P.q * P.c)))
  else min (min 1 (P.κStar * P.δ₁ / (4 * P.q * P.ℓ ^ 2))) (1 / (4 * (P.c + P.ℓ)))

/-- `Γ* := Γ_1 ∩ Γ_2`, the contact set of `I*` (part (2) of the proof of `prop:correct`). -/
def Γstar : Finset ℝ := P.Γ₁ P.N₀ P.δ₁ ∩ P.Γ₂ P.N₀ P.δ₁

/-- `L'(α) = p/σ + qα/σ²`, the line of `I'` (`I*` with `m` replaced by `m/σ`; part (3) of the
proof of `prop:correct`). -/
def L' (α : ℝ) : ℝ := P.p / P.σ + P.q / P.σ ^ 2 * α

/-- `L̃ := L' + C` (part (3) of the proof of `prop:correct`). -/
def Lt (α : ℝ) : ℝ := P.L' α + P.C

/-- `c' := σc` (part (3) of the proof of `prop:correct`), the center of the window of contacts
`[c' − ℓ', c' + ℓ']` of `Î`. -/
def c' : ℝ := P.σ * P.c

/-- `ℓ' := σℓ` (part (3) of the proof of `prop:correct`). -/
def ℓ' : ℝ := P.σ * P.ℓ

/-- `q' := q/σ²` (part (4) of the proof of `prop:correct`). -/
def q' : ℝ := P.q / P.σ ^ 2

end SubsetSum

/-! ### `prop:correct` -/

/-- **Part (1) of the proof of `prop:correct`** (our numbering of the six parts, see `correct`;
`stoc-sections/appD-hardness.tex:274-278`): "We first show that step (1) of `def:reduction` does
not change the answer." (1a) If it applies, then `(a, T)` is a no-instance, as `0 ≤ a^⊤χ ≤ ∑_i a_i`;
(1b) it is replaced by `a = (2)`, `T = 1`, which is a no-instance as well, as `2χ_1 ≠ 1`, and
which satisfies `0 ≤ T ≤ ∑_i a_i = 2`; (1c) so the steps (2) to (5) are applied to a pair with
`0 ≤ T ≤ ∑_i a_i` that is a yes-instance if and only if the given pair is one. -/
theorem correct_step1 (P : SubsetSum) :
    0 ≤ P.step1.T ∧ P.step1.T ≤ P.step1.sumA ∧ (P.step1.Yes ↔ P.Yes) := by
  unfold SubsetSum.step1
  split_ifs with h
  · -- (1a) "If it applies, then `(a, T)` is a no-instance, as `0 ≤ a^⊤χ ≤ ∑_i a_i` for every
    -- `χ ∈ {0, 1}^k`."
    have hno : ¬ P.Yes := by
      rintro ⟨Q, hQ, hsum⟩
      have h1 : 0 ≤ ∑ i ∈ Q, (P.a i : ℤ) := sum_nonneg fun i _ => by positivity
      have h2 : ∑ i ∈ Q, (P.a i : ℤ) ≤ P.sumA := by
        unfold SubsetSum.sumA
        push_cast
        exact sum_le_sum_of_subset_of_nonneg hQ fun i _ _ => by positivity
      rcases h with h | h <;> linarith
    -- (1b) "It is replaced by `a = (2)`, `T = 1`, which is a no-instance as well, as `2χ_1 ≠ 1`,
    -- and which satisfies `0 ≤ T ≤ ∑_i a_i = 2`."
    have hno' : ¬ SubsetSum.Yes ⟨1, le_rfl, fun _ => 2, fun _ _ => two_pos, 1⟩ := by
      rintro ⟨Q, hQ, hsum⟩
      simp only [sum_const, nsmul_eq_mul] at hsum
      have hc : Q.card ≤ 1 := by simpa using card_le_card hQ
      interval_cases h : Q.card <;> norm_num at hsum
    -- (1c) "So the steps (2) to (5) are applied to a pair `(a, T)` with `0 ≤ T ≤ ∑_i a_i` that is a
    -- yes-instance if and only if the given pair is one."
    refine ⟨by norm_num, ?_, ⟨fun h' => absurd h' hno', fun h' => absurd h' hno⟩⟩
    show (1 : ℤ) ≤ ((∑ i ∈ range 1, 2 : ℕ) : ℤ)
    simp
  · -- (1c) (step (1) does not apply, and the pair is unchanged)
    push Not at h
    exact ⟨h.1, h.2, Iff.rfl⟩

/-- `σ` exists (the sentence after `def:reduction`, Definition C.8,
`stoc-sections/appD-hardness.tex:266`): "Every condition in step (4) is an upper bound on `σ` with a
positive right-hand side, or vacuous, so `σ` exists and is at least half the smallest of these
right-hand sides", given `q, ℓ, κ*, δ_1 > 0` and `c + ℓ > 0` (which part (2) of the proof of
`prop:correct` shows). Here `σ = 2^{−j}` for the least `j ≥ 0` with the four conditions: `σ > 0`
satisfies them, every power `2^{−j}` that satisfies them is at most `σ`, and `σ ≥ rhsMin/2` for the
smallest right-hand side `rhsMin`.

The steps: (1) `σ ≤ 1` and `σ ≤ κ*δ_1/(4qℓ²)` are upper bounds with positive right-hand sides,
`σ(c + ℓ) ≤ 1/4` is the upper bound `σ ≤ 1/(4(c + ℓ))`, and `σ(p + 2qc) < q` is the upper
bound `σ < q/(p + 2qc)` if `p + 2qc > 0` and is vacuous otherwise (it holds for every `σ > 0`, as
`q > 0`); so every `s` with `0 < s < rhsMin` satisfies the four conditions; (2) so `σ` exists:
the power `2^{−(n+1)}` with `2^n ≤ 1/rhsMin < 2^{n+1}` lies in `[rhsMin/2, rhsMin)`, so it
satisfies the conditions, and `σ`, the largest such power, is at least `2^{−(n+1)} ≥ rhsMin/2`.
(The use of this bound, the running time of the reduction, is not formalised.) -/
theorem σ_spec (P : SubsetSum) (hq : 0 < P.q) (hl : 0 < P.ℓ) (hκ : 0 < P.κStar)
    (hδ : 0 < P.δ₁) (hcl : 0 < P.c + P.ℓ) :
    P.Cond4 P.σ ∧ 0 < P.σ ∧ (∀ j : ℕ, P.Cond4 ((1 / 2) ^ j) → (1 / 2 : ℝ) ^ j ≤ P.σ) ∧
      P.rhsMin / 2 ≤ P.σ := by
  classical
  -- (1) "Every condition in step (4) is an upper bound on `σ` with a positive right-hand side, or
  -- vacuous,": `σ ≤ 1`; `σ ≤ κ*δ_1/(4qℓ²)` with `κ*δ_1/(4qℓ²) > 0`;
  have h2 : 0 < P.κStar * P.δ₁ / (4 * P.q * P.ℓ ^ 2) := by positivity
  -- `σ(c + ℓ) ≤ 1/4` is `σ ≤ 1/(4(c + ℓ))`, with `1/(4(c + ℓ)) > 0`;
  have h3 : ∀ s, s * (P.c + P.ℓ) ≤ 1 / 4 ↔ s ≤ 1 / (4 * (P.c + P.ℓ)) := fun s => by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (P.c + P.ℓ))]
    constructor <;> intro h <;> linarith
  have h3pos : 0 < 1 / (4 * (P.c + P.ℓ)) := by positivity
  -- `σ(p + 2qc) < q` is `σ < q/(p + 2qc)`, with `q/(p + 2qc) > 0`, if `p + 2qc > 0`,
  have h4 : 0 < P.p + 2 * P.q * P.c → (∀ s, s * (P.p + 2 * P.q * P.c) < P.q ↔
      s < P.q / (P.p + 2 * P.q * P.c)) ∧ 0 < P.q / (P.p + 2 * P.q * P.c) :=
    fun h => ⟨fun s => (lt_div_iff₀ h).symm, by positivity⟩
  -- and it is vacuous, it holds for every `σ > 0` as `q > 0`, if `p + 2qc ≤ 0`.
  have h4vac : P.p + 2 * P.q * P.c ≤ 0 → ∀ s, 0 < s → s * (P.p + 2 * P.q * P.c) < P.q :=
    fun h s hs => by nlinarith
  -- So every `s` with `0 < s < rhsMin` satisfies the four conditions, and `0 < rhsMin ≤ 1`.
  have hbelow : ∀ s, 0 < s → s < P.rhsMin → P.Cond4 s := by
    intro s hs hsr
    unfold SubsetSum.rhsMin at hsr
    split_ifs at hsr with hp
    · simp only [lt_min_iff] at hsr
      exact ⟨hsr.1.1.le, hsr.1.2.le, (h3 s).2 hsr.2.1.le, ((h4 hp).1 s).2 hsr.2.2⟩
    · simp only [lt_min_iff] at hsr
      exact ⟨hsr.1.1.le, hsr.1.2.le, (h3 s).2 hsr.2.le, h4vac (not_lt.1 hp) s hs⟩
  have hpos : 0 < P.rhsMin := by
    unfold SubsetSum.rhsMin
    split_ifs with hp
    · exact lt_min (lt_min one_pos h2) (lt_min h3pos (h4 hp).2)
    · exact lt_min (lt_min one_pos h2) h3pos
  have hle1 : P.rhsMin ≤ 1 := by
    unfold SubsetSum.rhsMin
    split_ifs <;> exact (min_le_left _ _).trans (min_le_left _ _)
  -- (2) "so `σ` exists and is at least half the smallest of these right-hand sides": with
  -- `2^n ≤ 1/rhsMin < 2^{n+1}`, the power `2^{−(n+1)} ∈ [rhsMin/2, rhsMin)` satisfies the four
  -- conditions, and `σ`, the largest such power, is at least `2^{−(n+1)}`.
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (one_le_one_div hpos hle1) one_lt_two
  have hj1 : (1 / 2 : ℝ) ^ (n + 1) < P.rhsMin := by
    rw [one_div_pow, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hpos] at hn2
    linarith
  have hj2 : P.rhsMin / 2 ≤ (1 / 2 : ℝ) ^ (n + 1) := by
    rw [one_div_pow, le_div_iff₀ (by positivity), pow_succ]
    rw [le_div_iff₀ hpos] at hn1
    linarith
  have hex : ∃ j : ℕ, P.Cond4 ((1 / 2) ^ j) := ⟨n + 1, hbelow _ (by positivity) hj1⟩
  have hσ : P.σ = (1 / 2) ^ Nat.find hex := by
    unfold SubsetSum.σ
    exact dite_eq_left hex
  have hlargest : ∀ j : ℕ, P.Cond4 ((1 / 2) ^ j) → (1 / 2 : ℝ) ^ j ≤ P.σ := fun j hj => by
    rw [hσ]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.find_min' hex hj)
  exact ⟨hσ ▸ Nat.find_spec hex, by rw [hσ]; positivity, hlargest,
    hj2.trans (hlargest _ (hbelow _ (by positivity) hj1))⟩

/-- **Part (2) of the proof of `prop:correct`** (`stoc-sections/appD-hardness.tex:280-290`), for a
pair with `0 ≤ T ≤ ∑_i a_i`: "Next we show that `I*` is a comb whose contacts lie in the window
`[c − ℓ, c + ℓ]` and exist if and only if `(a, T)` is a yes-instance." That is, `I* = I_1 ⊕ I_2'`
is a comb with line `p + qα`, dip `κ*`, width `δ_1/2`, and contact set `Γ* := Γ_1 ∩ Γ_2`
(`Γstar`), which is nonempty exactly for yes-instances and lies in `[c − ℓ, c + ℓ]`; moreover
`q ≥ q_1 > 0`, `ℓ > 0` and `c − ℓ = δ_1N_0 > 0`.

The part's sentences: (2a) `μ, μ' ∈ 𝔉`, `N_0 ≥ N_min(μ)` and `N_0 + T ≥ N_0 ≥ N_min(μ')`, so
`thm:gadget` applies to both calls; (2b) so `I_1` is a comb with the contact set `Γ_1`, line
`p_1 + q_1α`, dip `κ_1`, and width `δ_1`, and `I_2` one with contact set
`{δ_2(N_0 + T + μ'^⊤χ')}`, line `p_2 + q_2α`, dip `κ_2`, and width `δ_2`, with `q_1, q_2 > 0`;
(2c) by `lem:combsum`(a) with `δ_1/δ_2` in place of `σ`, `I_2'` is a comb with contact set `Γ_2`,
line `(δ_2/δ_1)p_2 + (δ_2/δ_1)²q_2α`, dip `(δ_2/δ_1)²κ_2`, and width `δ_1`; (2d) both contact sets
lie in `δ_1ℤ`; (2e) so, by `lem:combsum`(b), `I*` is a comb with line `p + qα`, dip `κ*`, width
`δ_1/2`, and contact set `Γ*`; (2f) by `lem:coincidence`, `Γ* ≠ ∅` if and only if `(a, T)` is a
yes-instance, and `Γ* ⊆ Γ_1 ⊆ [δ_1N_0, δ_1(N_0 + ∑_iμ_i)] = [c − ℓ, c + ℓ]`; (2g) `q ≥ q_1 > 0`,
`ℓ = (1/2)δ_1∑_iμ_i > 0` and `c − ℓ = δ_1N_0 > 0`, as `N_0 ≥ 1`. -/
theorem correct_step2 (R : SubsetSum) (hT : 0 ≤ R.T) (hTA : R.T ≤ R.sumA) :
    IsRankFunction R.fStar ∧ (∀ e, 0 < R.βStar e) ∧
    IsComb R.fStar R.mStar R.βStar R.Γstar R.p R.q R.κStar (R.δ₁ / 2) ∧
    (R.Γstar.Nonempty ↔ R.Yes) ∧
    (∀ γ ∈ R.Γstar, R.c - R.ℓ ≤ γ ∧ γ ≤ R.c + R.ℓ) ∧
    R.q₁ ≤ R.q ∧ 0 < R.q₁ ∧ 0 < R.ℓ ∧ R.c - R.ℓ = R.δ₁ * R.N₀ ∧
    0 < R.δ₁ * R.N₀ := by
  -- (2a) "Both `μ` and `μ'` lie in `𝔉`, and `N_0 ≥ N_min(μ)` and `N_0 + T ≥ N_0 ≥ N_min(μ')`, so
  -- `thm:gadget` applies to both calls in step (2)."
  obtain ⟨hF₁, hF₂⟩ := inF_μ R
  have hN₁ : gNmin R.μ R.k ≤ R.N₀ := le_max_left _ _
  have hN₂ : gNmin R.μ' R.k ≤ R.N₂ := (le_max_right _ _).trans (Nat.le_add_right _ _)
  -- (2b) "So `I_1` is a comb with the contact set `Γ_1` of `lem:coincidence`, line `p_1 + q_1α`,
  -- dip `κ_1`, and width `δ_1`, and `I_2` is a comb with contact set
  -- `{δ_2(N_0 + T + μ'^⊤χ') : χ' ∈ {0, 1}^k}`, line `p_2 + q_2α`, dip `κ_2`, and width `δ_2`,
  -- where `q_1, q_2 > 0`."
  obtain ⟨hNmin, hg₁⟩ := gadget hF₁
  obtain ⟨hc₁, -, hq₁, h₁⟩ := hg₁ R.N₀ hN₁
  obtain ⟨hc₂, -, hq₂, h₂⟩ := (gadget hF₂).2 R.N₂ hN₂
  have hδ₁ : 0 < δT R.μ := (δT_κT_pos (μin0_pos hF₁)).1
  have hδ₂ : 0 < δT R.μ' := (δT_κT_pos (μin0_pos hF₂)).1
  have hN₂cast : (R.N₂ : ℝ) = R.N₀ + R.T := by
    have h : ((R.T.toNat : ℤ) : ℝ) = (R.T : ℝ) := by rw [Int.toNat_of_nonneg hT]
    unfold SubsetSum.N₂
    push_cast at h ⊢
    linarith
  have hΓ₁ : gΓ R.μ R.k R.N₀ = R.Γ₁ R.N₀ R.δ₁ := by
    simp only [gΓ, SubsetSum.Γ₁, SubsetSum.δ₁, Int.cast_natCast]
  have h₁' : IsComb (gadgetF R.μ R.k R.N₀) (gadgetM R.μ R.k) (gadgetB R.μ R.k R.N₀)
      (R.Γ₁ R.N₀ R.δ₁) R.p₁ R.q₁ R.κ₁ R.δ₁ := by
    rw [← hΓ₁]
    exact h₁
  -- (2c) "By `lem:combsum`(a), applied with `δ_1/δ_2` in place of `σ`, the instance `I_2'` is a
  -- comb with the contact set `Γ_2` of `lem:coincidence`, line
  -- `(δ_2/δ_1)p_2 + (δ_2/δ_1)²q_2α`, dip `(δ_2/δ_1)²κ_2`, and width `δ_1`."
  have h₂' : IsComb (gadgetF R.μ' R.k R.N₂) (fun e => R.δ₂ / R.δ₁ * gadgetM R.μ' R.k e)
      (gadgetB R.μ' R.k R.N₂) (R.Γ₂ R.N₀ R.δ₁) (R.δ₂ / R.δ₁ * R.p₂) ((R.δ₂ / R.δ₁) ^ 2 * R.q₂)
      ((R.δ₂ / R.δ₁) ^ 2 * R.κ₂) R.δ₁ := by
    have h := combsum_a h₂ (div_pos hδ₁ hδ₂)
    have eΓ : (gΓ R.μ' R.k R.N₂).image (δT R.μ / δT R.μ' * ·) = R.Γ₂ R.N₀ R.δ₁ := by
      rw [gΓ, image_image]
      unfold SubsetSum.Γ₂ SubsetSum.δ₁
      refine image_congr fun Q _ => ?_
      simp only [Function.comp_apply, Int.cast_natCast, hN₂cast]
      field_simp
    have em : (fun e => gadgetM R.μ' R.k e / (δT R.μ / δT R.μ')) =
        fun e => R.δ₂ / R.δ₁ * gadgetM R.μ' R.k e := by
      funext e
      unfold SubsetSum.δ₁ SubsetSum.δ₂
      field_simp
    have ep : gp R.μ' R.k R.N₂ / (δT R.μ / δT R.μ') = R.δ₂ / R.δ₁ * R.p₂ := by
      unfold SubsetSum.δ₁ SubsetSum.δ₂ SubsetSum.p₂
      field_simp
    have eq : gq R.μ' R.k / (δT R.μ / δT R.μ') ^ 2 = (R.δ₂ / R.δ₁) ^ 2 * R.q₂ := by
      unfold SubsetSum.δ₁ SubsetSum.δ₂ SubsetSum.q₂
      field_simp
    have eκ : κT R.μ' / (δT R.μ / δT R.μ') ^ 2 = (R.δ₂ / R.δ₁) ^ 2 * R.κ₂ := by
      unfold SubsetSum.δ₁ SubsetSum.δ₂ SubsetSum.κ₂
      field_simp
    have eδ : δT R.μ / δT R.μ' * δT R.μ' = R.δ₁ := by
      unfold SubsetSum.δ₁
      field_simp
    rw [eΓ, em, ep, eq, eκ, eδ] at h
    exact h
  -- (2d) "Both contact sets lie in `δ_1ℤ`, as `N_0`, `T`, `μ`, and `μ'` are integral."
  have hZ₁ : ∀ γ ∈ R.Γ₁ R.N₀ R.δ₁, ∃ n : ℤ, γ = R.δ₁ * n := by
    intro γ hγ
    obtain ⟨Q, -, rfl⟩ := mem_image.1 hγ
    exact ⟨R.N₀ + ∑ i ∈ Q, (R.μ i : ℤ), by push_cast; ring⟩
  have hZ₂ : ∀ γ ∈ R.Γ₂ R.N₀ R.δ₁, ∃ n : ℤ, γ = R.δ₁ * n := by
    intro γ hγ
    obtain ⟨Q, -, rfl⟩ := mem_image.1 hγ
    exact ⟨R.N₀ + R.T + ∑ i ∈ Q, (R.μ' i : ℤ), by push_cast; ring⟩
  -- (2e) "So, by `lem:combsum`(b), the instance `I* = I_1 ⊕ I_2'` is a comb with line `p + qα`,
  -- dip `κ*`, width `δ_1/2`, and contact set `Γ* := Γ_1 ∩ Γ_2`."
  have hcomb : IsComb R.fStar R.mStar R.βStar R.Γstar R.p R.q R.κStar (R.δ₁ / 2) :=
    combsum_b hc₁.rank hc₂.rank hc₁.β_pos hc₂.β_pos h₁' h₂' hZ₁ hZ₂
  -- (2f) "By `lem:coincidence`, `Γ* ≠ ∅` if and only if `(a, T)` is a yes-instance, and
  -- `Γ* ⊆ Γ_1 ⊆ [δ_1N_0, δ_1(N_0 + ∑_iμ_i)] = [c − ℓ, c + ℓ]`."
  have hcoin : R.Γstar.Nonempty ↔ R.Yes := (coincidence R hT hTA R.N₀ hδ₁).2
  have hsub : R.Γstar ⊆ R.Γ₁ R.N₀ R.δ₁ := inter_subset_left
  have hΓ₁ : ∀ γ ∈ R.Γ₁ R.N₀ R.δ₁, R.δ₁ * R.N₀ ≤ γ ∧
      γ ≤ R.δ₁ * (R.N₀ + ∑ i ∈ range R.k, (R.μ i : ℝ)) := by
    intro γ hγ
    obtain ⟨Q, hQ, rfl⟩ := mem_image.1 hγ
    have h1 : 0 ≤ ∑ i ∈ Q, (R.μ i : ℝ) := sum_nonneg fun i _ => Nat.cast_nonneg _
    have h2 : ∑ i ∈ Q, (R.μ i : ℝ) ≤ ∑ i ∈ range R.k, (R.μ i : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (mem_powerset.1 hQ) fun i _ _ => Nat.cast_nonneg _
    have hδ : 0 < R.δ₁ := hδ₁
    simp only [Int.cast_natCast]
    constructor <;> nlinarith
  have hends : R.c - R.ℓ = R.δ₁ * R.N₀ ∧
      R.c + R.ℓ = R.δ₁ * (R.N₀ + ∑ i ∈ range R.k, (R.μ i : ℝ)) := by
    unfold SubsetSum.c SubsetSum.ℓ
    constructor <;> ring
  have hint : ∀ γ ∈ R.Γstar, R.c - R.ℓ ≤ γ ∧ γ ≤ R.c + R.ℓ := by
    intro γ hγ
    rw [hends.1, hends.2]
    exact hΓ₁ γ (hsub hγ)
  -- (2g) "Moreover, `q ≥ q_1 > 0` and `ℓ = (1/2)δ_1∑_iμ_i > 0`, and `c − ℓ = δ_1N_0 > 0`, as
  -- `N_0 ≥ 1`."
  have hqq : R.q₁ ≤ R.q := by
    unfold SubsetSum.q
    have : 0 ≤ (R.δ₂ / R.δ₁) ^ 2 * R.q₂ := mul_nonneg (sq_nonneg _) hq₂.le
    linarith
  have hN₀ : (1 : ℝ) ≤ R.N₀ := by
    have : 1 ≤ R.N₀ := hNmin.trans hN₁
    exact_mod_cast this
  have hsum : 0 < ∑ i ∈ range R.k, (R.μ i : ℝ) :=
    sum_pos (fun i hi => by have := hF₁.2.1 i (mem_range.1 hi); positivity)
      ⟨0, mem_range.2 (by have := R.one_le_k; omega)⟩
  have hl : R.ℓ = 1 / 2 * R.δ₁ * ∑ i ∈ range R.k, (R.μ i : ℝ) := by
    unfold SubsetSum.ℓ
    ring
  have hδ : 0 < R.δ₁ := hδ₁
  refine ⟨isRankFunction_dsum hc₁.rank hc₂.rank, ?_, hcomb, hcoin, hint, hqq, hq₁,
    by rw [hl]; positivity, hends.1, by positivity⟩
  rintro (e | e)
  · exact hc₁.β_pos e
  · exact hc₂.β_pos e

/-- `σ` exists (`σ_spec`), for a pair with `0 ≤ T ≤ ∑_i a_i`, from the facts of part (2) of the
proof of `prop:correct` (`correct_step2`) that step (4) of `def:reduction` needs. -/
lemma σ_spec' (R : SubsetSum) (hT : 0 ≤ R.T) (hTA : R.T ≤ R.sumA) :
    R.Cond4 R.σ ∧ 0 < R.σ := by
  obtain ⟨-, -, hcomb, -, -, hqq, hq₁, hl, hcl, hδN⟩ := correct_step2 R hT hTA
  have hδ : 0 < R.δ₁ := by
    have : (0 : ℝ) < R.N₀ := by
      have h1 : 1 ≤ R.N₀ := (gadget (inF_μ R).1).1.trans (le_max_left _ _)
      exact_mod_cast (show 0 < R.N₀ by omega)
    exact pos_of_mul_pos_left hδN this.le
  have hκ : 0 < R.κStar := by
    have := hcomb.κ_pos
    exact this
  obtain ⟨h1, h2, -, -⟩ := σ_spec R (by linarith) hl hκ hδ (by linarith)
  exact ⟨h1, h2⟩

/-- **Part (3) of the proof of `prop:correct`** (`stoc-sections/appD-hardness.tex:292-303`), for a
pair with `0 ≤ T ≤ ∑_i a_i`: "Then we show that the reward of `Î`, the rescaled sum plus the
centering summand, stays below a line and touches it at the contacts." Here `I'` is `I*` with `m`
replaced by `m/σ`, `r'(x'*(α))` is the reward of `I'` under its best response, and `r̂(x̂*(α))` is
that of `Î`.

The part's sentences: (3a) by `lem:combsum`(a), `I'` is a comb with contact set `σΓ*`, line
`L'(α) = p/σ + qα/σ²`, dip `κ*/σ²`, and width `σδ_1/2`; (3b) the centering summand has
`α_∘ = σδ_1N_0 > 0` and `C > 0`, by the condition `σ(p + 2qc) < q` of step (4), so, by
`lem:ops`(c), `r̂(x̂*(α)) = r'(x'*(α)) + C min(α/α_∘, 1)` for `α ≥ 0`; (3c) with `L̃ := L' + C`,
`c' := σc`, and `ℓ' := σℓ`, as `C min(α/α_∘, 1) ≤ C`, `L̃(α) − r̂(x̂*(α)) ≥ L'(α) − r'(x'*(α))`
for all `α ≥ 0`; (3d) as `Γ* ⊆ [c − ℓ, c + ℓ]`, the contacts satisfy
`σΓ* ⊆ [c' − ℓ', c' + ℓ']`, and `c' − ℓ' = σδ_1N_0 = α_∘`; (3e) so the centering summand adds `C`
at every contact, and `L̃(γ) = L'(γ) + C = r̂(x̂*(γ))` for every `γ ∈ σΓ*`. -/
theorem correct_step3 (R : SubsetSum) (hT : 0 ≤ R.T) (hTA : R.T ≤ R.sumA) :
    IsComb R.fStar (fun e => R.mStar e / R.σ) R.βStar (R.Γstar.image (R.σ * ·)) (R.p / R.σ)
      (R.q / R.σ ^ 2) (R.κStar / R.σ ^ 2) (R.σ * (R.δ₁ / 2)) ∧
    0 < R.αknob ∧ 0 < R.C ∧
    (∀ α, 0 ≤ α → grossValue R.fHat R.mHat R.βHat α =
      grossValue R.fStar (fun e => R.mStar e / R.σ) R.βStar α + R.C * min (α / R.αknob) 1) ∧
    (∀ α, 0 ≤ α → R.L' α - grossValue R.fStar (fun e => R.mStar e / R.σ) R.βStar α ≤
      R.Lt α - grossValue R.fHat R.mHat R.βHat α) ∧
    (∀ γ ∈ R.Γstar.image (R.σ * ·), R.c' - R.ℓ' ≤ γ ∧ γ ≤ R.c' + R.ℓ') ∧
    R.c' - R.ℓ' = R.αknob ∧
    ∀ γ ∈ R.Γstar.image (R.σ * ·), R.Lt γ = grossValue R.fHat R.mHat R.βHat γ := by
  obtain ⟨hrank, hβ, hcomb, -, hint, -, -, -, hcl, hδN⟩ := correct_step2 R hT hTA
  obtain ⟨hcond, hσ⟩ := σ_spec' R hT hTA
  -- (3a) "Let `I'` be `I*` with `m` replaced by `m/σ`. We write `r'(x'*(α))` for the reward of
  -- `I'` under its best response, and `r̂(x̂*(α))` for that of `Î`. By `lem:combsum`(a), `I'` is a
  -- comb with contact set `σΓ*`, line `L'(α) := p/σ + qα/σ²`, dip `κ*/σ²`, and width `σδ_1/2`."
  have hcomb' := combsum_a hcomb hσ
  -- (3b) "The centering summand has `α_∘ = σδ_1N_0 > 0` and `C > 0`, by the condition
  -- `σ(p + 2qc) < q` in step (4), so, by `lem:ops`(c),
  -- `r̂(x̂*(α)) = r'(x'*(α)) + C min(α/α_∘, 1)` for `α ≥ 0`."
  have hαk : 0 < R.αknob := by
    unfold SubsetSum.αknob
    rw [mul_assoc]
    exact mul_pos hσ hδN
  have hC : 0 < R.C := by
    unfold SubsetSum.C
    have := hcond.2.2.2
    exact div_pos (by nlinarith) (by positivity)
  have hr : ∀ α, 0 ≤ α → grossValue R.fHat R.mHat R.βHat α =
      grossValue R.fStar (fun e => R.mStar e / R.σ) R.βStar α + R.C * min (α / R.αknob) 1 :=
    fun α hα => ops_c_aux hrank hβ hC hαk hα
  -- (3c) "Put `L̃ := L' + C`, `c' := σc`, and `ℓ' := σℓ`. As `C min(α/α_∘, 1) ≤ C`, we have
  -- `L̃(α) − r̂(x̂*(α)) ≥ L'(α) − r'(x'*(α))` for all `α ≥ 0`."
  have hle : ∀ α, 0 ≤ α → R.L' α - grossValue R.fStar (fun e => R.mStar e / R.σ) R.βStar α ≤
      R.Lt α - grossValue R.fHat R.mHat R.βHat α := by
    intro α hα
    rw [hr α hα]
    have : R.C * min (α / R.αknob) 1 ≤ R.C := by
      have := min_le_right (α / R.αknob) 1
      nlinarith
    unfold SubsetSum.Lt
    linarith
  -- (3d) "As `Γ* ⊆ [c − ℓ, c + ℓ]`, the contacts satisfy `σΓ* ⊆ [c' − ℓ', c' + ℓ']`, and
  -- `c' − ℓ' = σδ_1N_0 = α_∘`." (`Γ* ⊆ [c − ℓ, c + ℓ]` is from (2).)
  have hint' : ∀ γ ∈ R.Γstar.image (R.σ * ·), R.c' - R.ℓ' ≤ γ ∧ γ ≤ R.c' + R.ℓ' := by
    intro γ hγ
    obtain ⟨γ₀, hγ₀, rfl⟩ := mem_image.1 hγ
    obtain ⟨h1, h2⟩ := hint γ₀ hγ₀
    unfold SubsetSum.c' SubsetSum.ℓ'
    constructor <;> nlinarith
  have hck : R.c' - R.ℓ' = R.αknob := by
    unfold SubsetSum.c' SubsetSum.ℓ' SubsetSum.αknob
    rw [mul_assoc, ← hcl]
    ring
  -- (3e) "So the centering summand adds `C` at every contact, and `L̃(γ) = L'(γ) + C = r̂(x̂*(γ))`
  -- for every `γ ∈ σΓ*`."
  refine ⟨hcomb', hαk, hC, hr, hle, hint', hck, fun γ hγ => ?_⟩
  have hγk : R.αknob ≤ γ := hck ▸ (hint' γ hγ).1
  rw [hr γ (hαk.le.trans hγk), min_eq_right ((one_le_div hαk).2 hγk), mul_one,
    hcomb'.contact γ hγ]
  rfl

/-- **Part (4) of the proof of `prop:correct`** (`stoc-sections/appD-hardness.tex:305-316`), for a
pair with `0 ≤ T ≤ ∑_i a_i`: "We now show that `(1 − α)L̃(α)` is a parabola with its top at the
center `c'` of the window of contacts." (4a) With `q' := q/σ²`, by the choice of `C` in step (4),
`L̃(α) = p/σ + qα/σ² + q/σ² − 2qc/σ − p/σ = q'(1 − 2c' + α)`; (4b) so
`(1 − α)L̃(α) = q'((1 − c')² − (α − c')²) = ϑ + qℓ² − q'(α − c')²` (`eq:D-parabola`, the second
conjunct), as `ϑ = q'((1 − c')² − ℓ'²)` and `q'ℓ'² = qℓ²`; (4c) moreover, `c' + ℓ' ≤ 1/4` by step
(4). -/
theorem correct_step4 (R : SubsetSum) (hT : 0 ≤ R.T) (hTA : R.T ≤ R.sumA) :
    (∀ α, R.Lt α = R.q' * (1 - 2 * R.c' + α)) ∧
    (∀ α, (1 - α) * R.Lt α = R.ϑ + R.q * R.ℓ ^ 2 - R.q' * (α - R.c') ^ 2) ∧
    R.c' + R.ℓ' ≤ 1 / 4 := by
  obtain ⟨hcond, hσ⟩ := σ_spec' R hT hTA
  -- (4a) "Put `q' := q/σ²`. By the choice of `C` in step (4),
  -- `L̃(α) = p/σ + qα/σ² + q/σ² − 2qc/σ − p/σ = q'(1 − 2c' + α)`,"
  have hL : ∀ α, R.Lt α = R.q' * (1 - 2 * R.c' + α) := by
    intro α
    calc R.Lt α = R.p / R.σ + R.q * α / R.σ ^ 2 + R.q / R.σ ^ 2 - 2 * R.q * R.c / R.σ -
          R.p / R.σ := by
          simp only [SubsetSum.Lt, SubsetSum.L', SubsetSum.C]
          field_simp
          ring
      _ = R.q' * (1 - 2 * R.c' + α) := by
          simp only [SubsetSum.q', SubsetSum.c']
          field_simp
          ring
  -- (4b) "so `(1 − α)L̃(α) = q'((1 − c')² − (α − c')²) = ϑ + qℓ² − q'(α − c')²` (`eq:D-parabola`),
  -- as `ϑ = q'((1 − c')² − ℓ'²)` and `q'ℓ'² = qℓ²`."
  have hpar : ∀ α, (1 - α) * R.Lt α = R.q' * ((1 - R.c') ^ 2 - (α - R.c') ^ 2) := by
    intro α
    rw [hL]
    ring
  have hϑ : R.ϑ = R.q' * ((1 - R.c') ^ 2 - R.ℓ' ^ 2) := by
    simp only [SubsetSum.ϑ, SubsetSum.q', SubsetSum.c', SubsetSum.ℓ']
    ring
  have hql : R.q' * R.ℓ' ^ 2 = R.q * R.ℓ ^ 2 := by
    simp only [SubsetSum.q', SubsetSum.ℓ']
    field_simp
  refine ⟨hL, fun α => ?_, ?_⟩
  · rw [hpar, hϑ, ← hql]
    ring
  · -- (4c) "Moreover, `c' + ℓ' ≤ 1/4` by step (4)."
    have := hcond.2.2.1
    simp only [SubsetSum.c', SubsetSum.ℓ']
    linarith

/-- **`prop:correct`** (Proposition C.9, `stoc-sections/appD-hardness.tex:268-270`, proof lines
273-347): let `(Î, ϑ)` be the output of `def:reduction` for `(a, T)` (the steps (2)-(5) applied to
the pair `P.step1` of step (1)), and let `α*` be an optimal share of `Î` (a maximizer of
`U_P(α) = (1 − α)r̂(x̂*(α))` over `[0, 1]`). If `(a, T)` is a yes-instance, then `U_P(α*) ≥ ϑ`.
Otherwise `U_P(α*) ≤ ϑ − qℓ²/2 < ϑ`.

The proof has six parts, which open with sentences instead of labels; we number them (1)-(6):
(1) "We first show that step (1) of `def:reduction` does not change the answer"
(`correct_step1`); (2) "Next we show that `I*` is a comb whose contacts lie in the window
`[c − ℓ, c + ℓ]` and exist if and only if `(a, T)` is a yes-instance" (`correct_step2`);
(3) "Then we show that the reward of `Î`, the rescaled sum plus the centering summand, stays below
a line and touches it at the contacts" (`correct_step3`); (4) "We now show that `(1 − α)L̃(α)` is a
parabola with its top at the center `c'` of the window of contacts", `eq:D-parabola`
(`correct_step4`); (5) "With this, we prove the claim for yes-instances": (5a) `Γ* ≠ ∅` by
`lem:coincidence`, and we let `γ ∈ σΓ*`; (5b) then `|γ − c'| ≤ ℓ'` and
`0 ≤ γ ≤ c' + ℓ' ≤ 1/4`, so `L̃(γ) = r̂(x̂*(γ))` and `eq:D-parabola` give
`U_P(γ) = (1 − γ)L̃(γ) ≥ ϑ + qℓ² − q'ℓ'² = ϑ`; (5c) as `γ ∈ [0, 1]`, `U_P(α*) ≥ U_P(γ) ≥ ϑ`;
(6) "Finally, we prove the claim for no-instances": (6a) `Γ* = ∅`, so `dist(α, σΓ*) = ∞`, and
`def:comb` for `I'` gives `L'(α) − r'(x'*(α)) ≥ (κ*/σ²)(σδ_1/2) = κ*δ_1/(2σ)` for `α ≥ 0`;
(6b) as `L̃(α) − r̂(x̂*(α)) ≥ L'(α) − r'(x'*(α))`, and by `σ ≤ κ*δ_1/(4qℓ²)`,
`L̃(α) − r̂(x̂*(α)) ≥ κ*δ_1/(2σ) ≥ 2qℓ²` for `α ≥ 0`; (6c) for `α ∈ [0, 1]`,
`U_P(α) ≤ (1 − α)L̃(α) − (1 − α)2qℓ²`, and three cases, each with `eq:D-parabola`:
`|α − c'| < ℓ'`; `|α − c'| ≥ ℓ'` and `α ≤ 3/4`; `α > 3/4`; (6d) in all cases
`U_P(α) ≤ ϑ − qℓ²/2`, so `U_P(α*) ≤ ϑ − qℓ²/2 < ϑ`, as `q > 0` and `ℓ > 0`. -/
theorem correct (P : SubsetSum) {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hopt : IsMaxOn (profit (grossValue P.step1.fHat P.step1.mHat P.step1.βHat)) (Set.Icc 0 1)
      α) :
    (P.Yes → P.step1.ϑ ≤ profit (grossValue P.step1.fHat P.step1.mHat P.step1.βHat) α) ∧
    (¬ P.Yes → profit (grossValue P.step1.fHat P.step1.mHat P.step1.βHat) α ≤
        P.step1.ϑ - P.step1.q * P.step1.ℓ ^ 2 / 2 ∧
      P.step1.ϑ - P.step1.q * P.step1.ℓ ^ 2 / 2 < P.step1.ϑ) := by
  -- (1) "We first show that step (1) of `def:reduction` does not change the answer." … "From
  -- now on, `(a, T)` denotes this pair, and `0 ≤ T ≤ ∑_i a_i`." (`correct_step1`)
  obtain ⟨hT, hTA, hyes⟩ := correct_step1 P
  set R := P.step1 with hR
  -- (2), (3) and (4) (`correct_step2`, `correct_step3`, `correct_step4`)
  obtain ⟨-, -, -, hne, -, hqq, hq₁, hl, hcl, hδN⟩ := correct_step2 R hT hTA
  obtain ⟨hcomb', hαk, -, -, hle, hint', hck, hcont⟩ := correct_step3 R hT hTA
  obtain ⟨-, hpar, hcl4⟩ := correct_step4 R hT hTA
  obtain ⟨hcond, hσ⟩ := σ_spec' R hT hTA
  have hq : 0 < R.q := by linarith
  have hql : R.q' * R.ℓ' ^ 2 = R.q * R.ℓ ^ 2 := by
    simp only [SubsetSum.q', SubsetSum.ℓ']
    field_simp
  have hℓ' : 0 ≤ R.ℓ' := by unfold SubsetSum.ℓ'; positivity
  have hq' : 0 < R.q' := by unfold SubsetSum.q'; positivity
  refine ⟨fun hY => ?_, fun hN => ?_⟩
  · -- (5) "With this, we prove the claim for yes-instances. Let `(a, T)` be a yes-instance."
    -- (5a) "Then `Γ* ≠ ∅` by `lem:coincidence`, and we let `γ ∈ σΓ*`."
    have hδ₁ : 0 < R.δ₁ := (δT_κT_pos (μin0_pos (inF_μ R).1)).1
    obtain ⟨γ₀, hγ₀⟩ := (coincidence R hT hTA R.N₀ hδ₁).2.2 (hyes.2 hY)
    have hγ : R.σ * γ₀ ∈ R.Γstar.image (R.σ * ·) := mem_image_of_mem _ hγ₀
    -- (5b) "Then `|γ − c'| ≤ ℓ'` and `0 ≤ γ ≤ c' + ℓ' ≤ 1/4`, so `L̃(γ) = r̂(x̂*(γ))` and
    -- `eq:D-parabola` give `U_P(γ) = (1 − γ)r̂(x̂*(γ)) = (1 − γ)L̃(γ) ≥ ϑ + qℓ² − q'ℓ'² = ϑ`."
    obtain ⟨h1, h2⟩ := hint' _ hγ
    have habs : |R.σ * γ₀ - R.c'| ≤ R.ℓ' := abs_le.2 ⟨by linarith, by linarith⟩
    have hγ0 : 0 ≤ R.σ * γ₀ := by linarith
    have hγ4 : R.σ * γ₀ ≤ 1 / 4 := h2.trans hcl4
    have hU : R.ϑ ≤ profit (grossValue R.fHat R.mHat R.βHat) (R.σ * γ₀) := by
      have hsq : (R.σ * γ₀ - R.c') ^ 2 ≤ R.ℓ' ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) habs 2
      calc R.ϑ = R.ϑ + R.q * R.ℓ ^ 2 - R.q' * R.ℓ' ^ 2 := by rw [hql]; ring
        _ ≤ R.ϑ + R.q * R.ℓ ^ 2 - R.q' * (R.σ * γ₀ - R.c') ^ 2 := by
          have := mul_le_mul_of_nonneg_left hsq hq'.le
          linarith
        _ = (1 - R.σ * γ₀) * R.Lt (R.σ * γ₀) := (hpar _).symm
        _ = profit (grossValue R.fHat R.mHat R.βHat) (R.σ * γ₀) := by
          unfold profit
          rw [hcont _ hγ]
    -- (5c) "As `γ ∈ [0, 1]`, we get `U_P(α*) ≥ U_P(γ) ≥ ϑ`."
    exact hU.trans (hopt ⟨hγ0, by linarith⟩)
  · -- (6) "Finally, we prove the claim for no-instances. Let `(a, T)` be a no-instance."
    -- (6a) "Then `Γ* = ∅`" (by the equivalence of (2)), "so `dist(α, σΓ*) = ∞` for every `α`,
    -- and `def:comb` for `I'` gives `L'(α) − r'(x'*(α)) ≥ (κ*/σ²)(σδ_1/2) = κ*δ_1/(2σ)` for all
    -- `α ≥ 0`."
    have hempty : R.Γstar = ∅ :=
      not_nonempty_iff_eq_empty.1 fun h => hN (hyes.1 (hne.1 h))
    have hdist : ∀ β, distTo β (R.Γstar.image (R.σ * ·)) = ⊤ := fun β => by
      rw [hempty, image_empty, distTo_empty]
    have hg6a : ∀ β, 0 ≤ β → R.κStar * R.δ₁ / (2 * R.σ) ≤
        R.L' β - grossValue R.fStar (fun e => R.mStar e / R.σ) R.βStar β := by
      intro β hβ
      have hm : minDist β (R.Γstar.image (R.σ * ·)) (R.σ * (R.δ₁ / 2)) = R.σ * (R.δ₁ / 2) := by
        have h := minDist_coe (α := β) (Γ := R.Γstar.image (R.σ * ·)) (δ := R.σ * (R.δ₁ / 2))
        rw [hdist β, min_eq_right le_top] at h
        exact_mod_cast h
      have h := hcomb'.gap β hβ
      rw [hm] at h
      have e : R.κStar / R.σ ^ 2 * (R.σ * (R.δ₁ / 2)) = R.κStar * R.δ₁ / (2 * R.σ) := by
        field_simp
      rw [e] at h
      exact h
    -- (6b) "As `L̃(α) − r̂(x̂*(α)) ≥ L'(α) − r'(x'*(α))`" (from (3)), "and by the condition
    -- `σ ≤ κ*δ_1/(4qℓ²)` in step (4), we get `L̃(α) − r̂(x̂*(α)) ≥ κ*δ_1/(2σ) ≥ 2qℓ²` for all
    -- `α ≥ 0`."
    have h4 : 2 * R.q * R.ℓ ^ 2 ≤ R.κStar * R.δ₁ / (2 * R.σ) := by
      have h := hcond.2.1
      rw [le_div_iff₀ (by positivity)] at h
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have hg6b : ∀ β, 0 ≤ β → 2 * R.q * R.ℓ ^ 2 ≤ R.Lt β - grossValue R.fHat R.mHat R.βHat β :=
      fun β hβ => (h4.trans (hg6a β hβ)).trans (hle β hβ)
    -- (6c) "For `α ∈ [0, 1]`, therefore, `U_P(α) ≤ (1 − α)L̃(α) − (1 − α)2qℓ²`, and we
    -- distinguish three cases."
    have hc0 : 0 ≤ R.c' := by
      have : 0 ≤ R.c' - R.ℓ' := by rw [hck]; exact hαk.le
      linarith
    have hall : ∀ β ∈ Set.Icc (0 : ℝ) 1, profit (grossValue R.fHat R.mHat R.βHat) β ≤
        R.ϑ - R.q * R.ℓ ^ 2 / 2 := by
      intro β hβ
      have hU : profit (grossValue R.fHat R.mHat R.βHat) β ≤
          (1 - β) * R.Lt β - (1 - β) * (2 * R.q * R.ℓ ^ 2) := by
        unfold profit
        have := mul_le_mul_of_nonneg_left (hg6b β hβ.1) (sub_nonneg.2 hβ.2)
        linarith
      have hpb := hpar β
      have hqlb : 0 ≤ R.q * R.ℓ ^ 2 := by positivity
      rcases lt_or_ge |β - R.c'| R.ℓ' with h | h
      · -- "If `|α − c'| < ℓ'`, then `α < c' + ℓ' ≤ 1/4`, and `eq:D-parabola` gives
        -- `U_P(α) ≤ ϑ + qℓ² − (3/4)·2qℓ²`."
        have hb : β < 1 / 4 := by
          have := (abs_lt.1 h).2
          linarith
        have hcase : profit (grossValue R.fHat R.mHat R.βHat) β ≤
            R.ϑ + R.q * R.ℓ ^ 2 - 3 / 4 * (2 * R.q * R.ℓ ^ 2) := by
          have h1 : 3 / 4 * (2 * R.q * R.ℓ ^ 2) ≤ (1 - β) * (2 * R.q * R.ℓ ^ 2) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          have h2 : 0 ≤ R.q' * (β - R.c') ^ 2 := by positivity
          linarith
        -- (6d) "In all cases `U_P(α) ≤ ϑ − qℓ²/2`"
        linarith
      · rcases le_or_gt β (3 / 4) with h' | h'
        · -- "If `|α − c'| ≥ ℓ'` and `α ≤ 3/4`, then `(1 − α)L̃(α) ≤ ϑ + qℓ² − q'ℓ'² = ϑ` by
          -- `eq:D-parabola`, and `U_P(α) ≤ ϑ − (1/4)·2qℓ²`."
          have hLt : (1 - β) * R.Lt β ≤ R.ϑ := by
            have h1 : R.ℓ' ^ 2 ≤ (β - R.c') ^ 2 := by
              rw [← sq_abs (β - R.c')]
              exact pow_le_pow_left₀ hℓ' h 2
            have h2 : R.q' * R.ℓ' ^ 2 ≤ R.q' * (β - R.c') ^ 2 :=
              mul_le_mul_of_nonneg_left h1 hq'.le
            linarith
          have hcase : profit (grossValue R.fHat R.mHat R.βHat) β ≤
              R.ϑ - 1 / 4 * (2 * R.q * R.ℓ ^ 2) := by
            have h3 : 1 / 4 * (2 * R.q * R.ℓ ^ 2) ≤ (1 - β) * (2 * R.q * R.ℓ ^ 2) :=
              mul_le_mul_of_nonneg_right (by linarith) (by positivity)
            linarith
          -- (6d) "In all cases `U_P(α) ≤ ϑ − qℓ²/2`"
          linarith
        · -- "If `α > 3/4`, then `α − c' ≥ 1/2`, as `c' ≤ 1/4`, so `eq:D-parabola` gives
          -- `U_P(α) ≤ (1 − α)L̃(α) ≤ ϑ + qℓ² − q'/4 ≤ ϑ − 3qℓ²`, as
          -- `q'/4 = q/(4σ²) ≥ 4qℓ²` by `σℓ ≤ σ(c + ℓ) ≤ 1/4`."
          have hc4 : R.c' ≤ 1 / 4 := by linarith
          have hac : 1 / 2 ≤ β - R.c' := by linarith
          have hσl : R.σ * R.ℓ ≤ 1 / 4 := by
            have h1 : R.σ * R.ℓ ≤ R.σ * (R.c + R.ℓ) := by
              have : 0 ≤ R.σ * R.c := hc0
              linarith [mul_add R.σ R.c R.ℓ]
            exact h1.trans hcond.2.2.1
          have hq'4 : 4 * (R.q * R.ℓ ^ 2) ≤ R.q' / 4 := by
            have e : R.q' / 4 = R.q / (4 * R.σ ^ 2) := by
              simp only [SubsetSum.q']
              ring
            have h5 : (R.σ * R.ℓ) ^ 2 ≤ 1 / 16 := by
              have : 0 ≤ R.σ * R.ℓ := by positivity
              nlinarith
            rw [e, le_div_iff₀ (by positivity)]
            nlinarith
          have hcase : profit (grossValue R.fHat R.mHat R.βHat) β ≤
              R.ϑ - 3 * (R.q * R.ℓ ^ 2) :=
            calc profit (grossValue R.fHat R.mHat R.βHat) β ≤ (1 - β) * R.Lt β := by
                  have : 0 ≤ (1 - β) * (2 * R.q * R.ℓ ^ 2) := by
                    have : 0 ≤ 1 - β := by linarith [hβ.2]
                    positivity
                  linarith
              _ ≤ R.ϑ + R.q * R.ℓ ^ 2 - R.q' / 4 := by
                  have h1 : 1 / 4 ≤ (β - R.c') ^ 2 := by nlinarith
                  have h2 : R.q' * (1 / 4) ≤ R.q' * (β - R.c') ^ 2 :=
                    mul_le_mul_of_nonneg_left h1 hq'.le
                  linarith
              _ ≤ R.ϑ - 3 * (R.q * R.ℓ ^ 2) := by linarith
          -- (6d) "In all cases `U_P(α) ≤ ϑ − qℓ²/2`"
          linarith
    -- (6d) "… so `U_P(α*) ≤ ϑ − qℓ²/2 < ϑ`, as `q > 0` and `ℓ > 0`."
    exact ⟨hall α hα, by have := mul_pos hq (pow_pos hl 2); linarith⟩

end

end Hardness

end Stoc
