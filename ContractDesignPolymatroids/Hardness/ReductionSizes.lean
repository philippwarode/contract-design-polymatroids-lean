-- stamp r5 2026-11-02
import ContractDesignPolymatroids.Hardness.GadgetSizes
import ContractDesignPolymatroids.Hardness.Reduction

/-!
# The reduction runs in polynomial time: the sizes in the proof of NP-hardness in `thm:nphard`

The STOC version's proof of `thm:nphard` (Appendix C.8, `stoc-sections/appD-hardness.tex:1886-1906`)
first establishes NP-hardness (lines 1887-1892): "The reduction of `def:reduction` runs in time
polynomial in the encoding length of `(a, T)`. Indeed, the algorithm of `thm:gadget` computes `N_0`
and both combs in polynomial time, as its inputs have `log μ_k, log μ'_k = O(k + log(2 + ∑_i a_i))`
and the integers `N_0` and `N_0 + T` have bit lengths bounded in the same way (`lem:sizes`, the
proof of `thm:gadget`, and `T ≤ ∑_i a_i`). Apart from the choice of `σ`, the steps (3) to (5) take
`O(k)` arithmetic operations, and `σ` is a power of `2` that is at least half the smallest
right-hand side in step (4), so `log(1/σ)` is polynomial and `σ` is found by as many comparisons."

This file proves these sizes in the bit model of `ContractDesignPolymatroids/Hardness/Encoding.lean`, in the paper's
order:

* `SubsetSum.encLen`: the encoding length `∑_i ⟨a_i⟩ + ⟨T⟩` of `(a, T)`, with `k ≤ ⟨(a, T)⟩` and
  `⌊log₂ ∑_i a_i⌋ < ⟨(a, T)⟩` (`k_le_encLen`, `log_sumA_lt`);
* "its inputs have `log μ_k, log μ'_k = O(k + log(2 + ∑_i a_i))`" (`μ_last_lt`), "the integers `N_0`
  and `N_0 + T` have bit lengths bounded in the same way" (`N₀_le`, `N₂_le`), and the gadgets'
  numbers then have `O(k + log ∑_i a_i)` bits (`gadget_sizes`, here `gadget1_bits`, `gadget2_bits`
  with the common bound `Bg`);
* the numbers of the steps (3)-(5) (`steps_bits`, `out_bits`): each is obtained from these by
  `O(1)` arithmetic operations (`Bits.add3`, `Bits.mul3`, `Bits.div`), and `σ = 2^{−J}`;
* "`σ` is a power of `2` that is at least half the smallest right-hand side in step (4), so
  `log(1/σ)` is polynomial and `σ` is found by as many comparisons" (`σ_search`: the search tests
  the conditions of step (4) for `σ = 1, 1/2, …, 2^{−J}`, `J + 1` tests, and `J ≤ 6561Bg + 1`);
* `reduction_sizes`: the output `(Î, ϑ)` is a rational instance, the cut form of `Î` the disjoint
  union of the two gadgets' forms and an isolated node of weight `C` (`outForm`), with
  `⟨Î⟩ + ⟨ϑ⟩ ≤ 2^{58}⟨(a, T)⟩³`.

Not formalised: the running time itself, as Turing machines are not formalised and arithmetic
operations are not counted (the `O(k)` arithmetic operations of the steps (3)-(5)); the
evaluations of `g` that each gadget needs are counted in `gadget_evals`. That the output lies in
`𝒞_cut` is the first conjunct of `nphard_core`, and `nphard_hardness` combines both.
-/

namespace Stoc

namespace Hardness

open Finset

noncomputable section

/-! ### Arithmetic on numbers of bounded size (not in the paper) -/

namespace Bits

variable {B : ℕ} {x y : ℝ}

/-- A sum of two numbers of at most `B ≥ 1` bits has at most `3B` bits. -/
lemma add3 (hx : Bits B x) (hy : Bits B y) (hB : 1 ≤ B) : Bits (3 * B) (x + y) :=
  (hx.add hy).mono (by omega)

/-- A difference of two numbers of at most `B ≥ 1` bits has at most `3B` bits. -/
lemma sub3 (hx : Bits B x) (hy : Bits B y) (hB : 1 ≤ B) : Bits (3 * B) (x - y) :=
  (hx.sub hy).mono (by omega)

/-- A product of two numbers of at most `B` bits has at most `3B` bits. -/
lemma mul3 (hx : Bits B x) (hy : Bits B y) : Bits (3 * B) (x * y) :=
  (hx.mul hy).mono (by omega)

/-- A natural number at most `2^B` has at most `B` bits. -/
lemma natCast {n : ℕ} (h : (n : ℝ) ≤ 2 ^ B) : Bits B n :=
  bits_of 1 (by norm_num) one_pos (InZ.nat n) (by push_cast; exact one_le_pow₀ (by norm_num))
    (by rw [Nat.abs_cast]; exact h)

/-- The minimum of two numbers of at most `B` bits has at most `B` bits. -/
lemma min' (hx : Bits B x) (hy : Bits B y) : Bits B (min x y) := by
  rcases min_choice x y with h | h <;> rw [h]
  · exact hx
  · exact hy

/-- A positive number of at most `B` bits is at least `2^{−B}`. -/
lemma one_le_two_pow_mul (hx : Bits B x) (hpos : 0 < x) : 1 ≤ 2 ^ B * x := by
  obtain ⟨-, n, hn, hnB, z, hz⟩ := hx
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hz0 : (0 : ℝ) < z := by rw [← hz]; positivity
  have hz1 : (1 : ℝ) ≤ z := by
    have : (0 : ℤ) < z := Int.cast_pos.1 hz0
    exact_mod_cast (show (1 : ℤ) ≤ z by omega)
  calc (1 : ℝ) ≤ z := hz1
    _ = n * x := hz.symm
    _ ≤ 2 ^ B * x := mul_le_mul_of_nonneg_right hnB hpos.le

/-- `2^{−J}` has at most `J` bits. -/
lemma half_pow (J : ℕ) : Bits J ((1 / 2 : ℝ) ^ J) := by
  refine bits_of (N := (2 : ℝ) ^ J) (2 ^ J) (by push_cast; ring) (by positivity)
    ⟨1, by rw [← mul_pow]; norm_num⟩ (by push_cast; exact le_rfl) ?_
  rw [abs_of_pos (by positivity)]
  calc (1 / 2 : ℝ) ^ J ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    _ ≤ 2 ^ J := one_le_pow₀ (by norm_num)

end Bits

/-! ### The encoding length of an instance of Subset Sum -/

/-- `∑_{i<k} 2^{x_i} ≤ 2^{∑_{i<k} x_i}` for `x_i ≥ 1` (not in the paper). -/
lemma sum_two_pow_le (x : ℕ → ℕ) : ∀ k : ℕ, (∀ i < k, 1 ≤ x i) →
    ∑ i ∈ range k, 2 ^ x i ≤ 2 ^ (∑ i ∈ range k, x i)
  | 0, _ => by simp
  | k + 1, hx => by
    rw [sum_range_succ, sum_range_succ, pow_add]
    have ih := sum_two_pow_le x k fun i hi => hx i (by omega)
    have h2 : 2 ≤ 2 ^ x k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ x k := Nat.pow_le_pow_right (by norm_num) (hx k (by omega))
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have h1 : 2 ≤ 2 ^ (∑ i ∈ range k, x i) := by
        have : 1 ≤ ∑ i ∈ range k, x i :=
          (hx 0 (by omega)).trans (single_le_sum (fun i _ => Nat.zero_le _) (mem_range.2 hk))
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ _ := Nat.pow_le_pow_right (by norm_num) this
      nlinarith

namespace SubsetSum

/-- The encoding length `⟨(a, T)⟩ = ∑_i ⟨a_i⟩ + ⟨T⟩` of an instance of Subset Sum, with the encoding
length `⟨·⟩` of `lem:exactbr` (the proof of NP-hardness in `thm:nphard`: "polynomial in the
encoding length of `(a, T)`"; the items and the target are given in binary). -/
def encLen (P : SubsetSum) : ℕ := ∑ i ∈ range P.k, enc (P.a i) + enc P.T

/-- `k ≤ ⟨(a, T)⟩` and `⟨(a, T)⟩ ≥ 2` (not in the paper). -/
lemma k_le_encLen (P : SubsetSum) : P.k ≤ P.encLen ∧ 2 ≤ P.encLen := by
  have h : ∀ i ∈ range P.k, 1 ≤ enc (P.a i) := fun i _ => le_trans (by norm_num) (two_le_enc _)
  have h1 := card_nsmul_le_sum (range P.k) (fun i => enc (P.a i)) 1 h
  simp only [card_range, smul_eq_mul, mul_one] at h1
  have h2 := two_le_enc (P.T : ℚ)
  unfold encLen
  omega

/-- `∑_i a_i ≥ 1` (not in the paper: `k ≥ 1` and `a_i > 0`). -/
lemma sumA_pos (P : SubsetSum) : 0 < P.sumA :=
  (P.a_pos 0 P.one_le_k).trans_le
    (single_le_sum (fun _ _ => Nat.zero_le _) (mem_range.2 P.one_le_k))

/-- `⌊log₂ ∑_i a_i⌋ < ⟨(a, T)⟩`, as `∑_i a_i + k ≤ ∑_i 2^{⟨a_i⟩} ≤ 2^{∑_i ⟨a_i⟩}` (not in the
paper). -/
lemma log_sumA_lt (P : SubsetSum) : Nat.log 2 P.sumA < P.encLen := by
  have ha : ∀ i, P.a i + 1 ≤ 2 ^ enc (P.a i) := fun i => by
    have := natAbs_num_lt (P.a i : ℚ)
    rw [Rat.num_natCast, Int.natAbs_natCast] at this
    omega
  have h1 : P.sumA + P.k ≤ 2 ^ (∑ i ∈ range P.k, enc (P.a i)) := by
    have h2 := sum_two_pow_le (fun i => enc (P.a i)) P.k fun i _ =>
      le_trans (by norm_num) (two_le_enc _)
    have h3 : ∑ i ∈ range P.k, (P.a i + 1) ≤ ∑ i ∈ range P.k, 2 ^ enc (P.a i) :=
      sum_le_sum fun i _ => ha i
    rw [sum_add_distrib, sum_const, card_range, smul_eq_mul, mul_one] at h3
    unfold sumA
    omega
  have h4 : P.sumA < 2 ^ P.encLen := by
    have : 2 ^ (∑ i ∈ range P.k, enc (P.a i)) ≤ 2 ^ P.encLen :=
      Nat.pow_le_pow_right (by norm_num) (by unfold encLen; omega)
    have := P.one_le_k
    omega
  exact Nat.log_lt_of_lt_pow (sumA_pos P).ne' h4

/-- Step (1) of `def:reduction` does not increase the encoding length by more than the factor `7`:
the replacement `a = (2)`, `T = 1` has `⟨(a, T)⟩ = ⟨2⟩ + ⟨1⟩ ≤ 7` (not in the paper). -/
lemma encLen_step1 (P : SubsetSum) : P.step1.encLen ≤ 7 * P.encLen := by
  have hP := (k_le_encLen P).2
  unfold step1
  split_ifs
  · show ∑ i ∈ range 1, enc ((2 : ℕ) : ℚ) + enc ((1 : ℤ) : ℚ) ≤ 7 * P.encLen
    have e2 : enc ((2 : ℕ) : ℚ) ≤ 4 := by
      rw [show ((2 : ℕ) : ℚ) = ((2 : ℤ) : ℚ) by norm_num, enc_intCast]
      have : Nat.clog 2 ((2 : ℤ).natAbs + 1) ≤ 2 := Nat.clog_le_of_le_pow (by norm_num)
      omega
    have e1 : enc ((1 : ℤ) : ℚ) ≤ 3 := by
      rw [enc_intCast]
      have : Nat.clog 2 ((1 : ℤ).natAbs + 1) ≤ 1 := Nat.clog_le_of_le_pow (by norm_num)
      omega
    simp only [sum_range_one]
    omega
  · omega

end SubsetSum

/-! ### The inputs of the gadgets, `N_0` and `N_0 + T` -/

namespace SubsetSum

variable (R : SubsetSum)

/-- "its inputs have `log μ_k, log μ'_k = O(k + log(2 + ∑_i a_i))`":
`μ_k, μ'_k < 2^{3k+⌊log₂ ∑_i a_i⌋+2}`, as `μ_k ≤ H 8^{k−1} + ∑_i a_i ≤ 12(∑_i a_i)8^{k−1}` with
`H = 10∑_i a_i + 1`. -/
lemma μ_last_lt : R.μ (R.k - 1) < 2 ^ (3 * R.k + Nat.log 2 R.sumA + 2) ∧
    R.μ' (R.k - 1) < 2 ^ (3 * R.k + Nat.log 2 R.sumA + 2) := by
  have hs := sumA_pos R
  have hslt : R.sumA < 2 ^ (Nat.log 2 R.sumA + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  obtain ⟨k', hk'⟩ : ∃ k', R.k = k' + 1 := ⟨R.k - 1, by have := R.one_le_k; omega⟩
  have ha : R.a (R.k - 1) ≤ R.sumA :=
    single_le_sum (fun i _ => Nat.zero_le _) (mem_range.2 (by have := R.one_le_k; omega))
  have h8 : 1 ≤ 8 ^ (R.k - 1) := Nat.one_le_pow _ _ (by norm_num)
  have hpow : 2 ^ (3 * R.k + Nat.log 2 R.sumA + 2) =
      16 * 2 ^ (Nat.log 2 R.sumA + 1) * 8 ^ (R.k - 1) := by
    rw [hk', show k' + 1 - 1 = k' by omega, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul,
      show 3 * (k' + 1) + Nat.log 2 R.sumA + 2 = 4 + (Nat.log 2 R.sumA + 1) + 3 * k' by ring,
      pow_add, pow_add]
    norm_num
  have hH : R.H * 8 ^ (R.k - 1) + R.sumA ≤ 12 * R.sumA * 8 ^ (R.k - 1) := by
    unfold SubsetSum.H
    nlinarith
  have hlt : 12 * R.sumA * 8 ^ (R.k - 1) < 2 ^ (3 * R.k + Nat.log 2 R.sumA + 2) := by
    rw [hpow]
    have : 0 < 8 ^ (R.k - 1) := by positivity
    nlinarith
  constructor
  · unfold SubsetSum.μ
    omega
  · unfold SubsetSum.μ'
    omega

/-- `⌊log₂ μ_k⌋, ⌊log₂ μ'_k⌋ ≤ 3k + ⌊log₂ ∑_i a_i⌋ + 1` (from `μ_last_lt`). -/
lemma log_μ_le : Nat.log 2 (R.μ (R.k - 1)) ≤ 3 * R.k + Nat.log 2 R.sumA + 1 ∧
    Nat.log 2 (R.μ' (R.k - 1)) ≤ 3 * R.k + Nat.log 2 R.sumA + 1 := by
  obtain ⟨h1, h2⟩ := μ_last_lt R
  have hF := inF_μ R
  have p1 : R.μ (R.k - 1) ≠ 0 := (hF.1.2.1 _ (by have := R.one_le_k; omega)).ne'
  have p2 : R.μ' (R.k - 1) ≠ 0 := (hF.2.2.1 _ (by have := R.one_le_k; omega)).ne'
  exact ⟨Nat.le_of_lt_succ (Nat.log_lt_of_lt_pow p1 h1),
    Nat.le_of_lt_succ (Nat.log_lt_of_lt_pow p2 h2)⟩

/-- "the integers `N_0` and `N_0 + T` have bit lengths bounded in the same way": `1 ≤ N_0`,
`N_0 ≤ 2^{2(20k + ⌊log₂ μ_k⌋ + ⌊log₂ μ'_k⌋ + 20) + 3}` (`gNmin_le`) and `N_0 ≤ N_0 + T` (`T ≥ 0`
after step (1)). -/
lemma N₀_le : 1 ≤ R.N₀ ∧ R.N₀ ≤ R.N₂ ∧
    R.N₀ ≤ 2 ^ (2 * (20 * R.k + Nat.log 2 (R.μ (R.k - 1)) + Nat.log 2 (R.μ' (R.k - 1)) + 20) + 3)
    := by
  obtain ⟨hF₁, hF₂⟩ := inF_μ R
  obtain ⟨h1, -, h1'⟩ := gNmin_le hF₁
  obtain ⟨-, -, h2'⟩ := gNmin_le hF₂
  set X := 2 * (20 * R.k + Nat.log 2 (R.μ (R.k - 1)) + Nat.log 2 (R.μ' (R.k - 1)) + 20) + 3
  have e1 : (gNmin R.μ R.k : ℝ) ≤ 2 ^ X :=
    h1'.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have e2 : (gNmin R.μ' R.k : ℝ) ≤ 2 ^ X :=
    h2'.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  refine ⟨h1.trans (le_max_left _ _), Nat.le_add_right _ _, max_le ?_ ?_⟩
  · exact_mod_cast e1
  · exact_mod_cast e2

/-- `N_0 + T ≤ 2^{X + ⌊log₂ ∑_i a_i⌋ + 1}` with `2^X` the bound of `N₀_le`, as `T ≤ ∑_i a_i` (the
proof of NP-hardness in `thm:nphard`: "and `T ≤ ∑_i a_i`"). -/
lemma N₂_le (hTA : R.T ≤ R.sumA) :
    R.N₂ ≤ 2 ^ (2 * (20 * R.k + Nat.log 2 (R.μ (R.k - 1)) + Nat.log 2 (R.μ' (R.k - 1)) + 20) + 3 +
      Nat.log 2 R.sumA + 1) := by
  obtain ⟨-, -, h⟩ := N₀_le R
  set X := 2 * (20 * R.k + Nat.log 2 (R.μ (R.k - 1)) + Nat.log 2 (R.μ' (R.k - 1)) + 20) + 3
  have hT : R.T.toNat ≤ R.sumA := by omega
  have hslt : R.sumA < 2 ^ (Nat.log 2 R.sumA + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h2X : 2 ≤ 2 ^ X := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ X := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2L : 2 ≤ 2 ^ (Nat.log 2 R.sumA + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e : 2 ^ (X + Nat.log 2 R.sumA + 1) = 2 ^ X * 2 ^ (Nat.log 2 R.sumA + 1) := by
    rw [← pow_add]; ring_nf
  unfold SubsetSum.N₂
  rw [e]
  nlinarith

/-! ### The cut form of the output -/

/-- The cut form of the output `Î` (the proof of NP-hardness in `thm:nphard`: "its rank
function is a direct sum of polymatroid rank functions whose cut forms, together with an isolated
node of weight `C` for the centering summand, form a cut form of it (`lem:cutforms`)"): the disjoint
union of the forms of the two gadgets (`gadgetForm`) and the node of weight `C`. -/
def outForm : CutForm (((Gr (R.k - 1) ⊕ Unit) ⊕ (Gr (R.k - 1) ⊕ Unit)) ⊕ Unit) :=
  ((gadgetForm R.μ R.k R.N₀).dsumForm (gadgetForm R.μ' R.k R.N₂)).dsumForm (CutForm.node R.C)

/-- `outForm` is a cut form of the rank function of `Î` (`lem:cutforms`(c)). -/
theorem outForm_fn (T : Finset (((Gr (R.k - 1) ⊕ Unit) ⊕ (Gr (R.k - 1) ⊕ Unit)) ⊕ Unit)) :
    R.fHat T = (outForm R).fn T := by
  have h1 : ∀ S, R.fStar S =
      ((gadgetForm R.μ R.k R.N₀).dsumForm (gadgetForm R.μ' R.k R.N₂)).fn S := fun S =>
    (cutforms_c (gadgetForm_fn (μin := R.μ) R.k R.N₀)).2.2.2
      (gadgetForm_fn (μin := R.μ') R.k R.N₂) S
  have h2 : ∀ S, single R.C S = (CutForm.node R.C).fn S := by
    intro S
    rcases finset_unit S with rfl | rfl
    · simp [single, CutForm.fn, CutForm.cut, CutForm.node]
    · simp [single, CutForm.fn, CutForm.cut, CutForm.node]
  exact (cutforms_c h1).2.2.2 h2 T

/-- The arcs of `outForm` are those of the two gadgets' forms, with their capacities (not in the
paper). -/
lemma outForm_cap {a} (ha : a ∈ (outForm R).D) :
    (∃ a' ∈ (gadgetForm R.μ R.k R.N₀).D, (outForm R).cap a = (gadgetForm R.μ R.k R.N₀).cap a') ∨
    ∃ a' ∈ (gadgetForm R.μ' R.k R.N₂).D,
      (outForm R).cap a = (gadgetForm R.μ' R.k R.N₂).cap a' := by
  rcases mem_union.1 ha with ha | ha
  · obtain ⟨b, h, rfl⟩ := mem_map.1 ha
    rcases mem_union.1 h with h | h
    · obtain ⟨⟨u, v⟩, h', rfl⟩ := mem_map.1 h
      exact Or.inl ⟨(u, v), h', rfl⟩
    · obtain ⟨⟨u, v⟩, h', rfl⟩ := mem_map.1 h
      exact Or.inr ⟨(u, v), h', rfl⟩
  · obtain ⟨⟨u, v⟩, h, -⟩ := mem_map.1 ha
    exact absurd h (notMem_empty _)

/-- The output has `6k + 3` elements, and the arcs of its form are at most `(6k + 3)²` (not in the
paper). -/
lemma card_out :
    Fintype.card (((Gr (R.k - 1) ⊕ Unit) ⊕ (Gr (R.k - 1) ⊕ Unit)) ⊕ Unit) = 6 * R.k + 3 ∧
    (outForm R).D.card ≤ (6 * R.k + 3) * (6 * R.k + 3) := by
  have hc : Fintype.card (((Gr (R.k - 1) ⊕ Unit) ⊕ (Gr (R.k - 1) ⊕ Unit)) ⊕ Unit) =
      6 * R.k + 3 := by
    simp only [Fintype.card_sum, card_Gr, Fintype.card_unit]
    have := R.one_le_k
    omega
  refine ⟨hc, ?_⟩
  calc (outForm R).D.card ≤ Fintype.card ((((Gr (R.k - 1) ⊕ Unit) ⊕ (Gr (R.k - 1) ⊕ Unit)) ⊕
        Unit) × (((Gr (R.k - 1) ⊕ Unit) ⊕ (Gr (R.k - 1) ⊕ Unit)) ⊕ Unit)) := card_le_univ _
    _ = (6 * R.k + 3) * (6 * R.k + 3) := by rw [Fintype.card_prod, hc]

/-! ### The numbers of the gadgets and of the steps (3)-(5) -/

end SubsetSum

namespace GadgetNumber

variable {μin : ℕ → ℕ} {k N : ℕ}

/-- `δ` is a number of the gadget. -/
lemma of_δ : GadgetNumber μin k N (δT μin) := by
  unfold GadgetNumber
  iterate 8 right
  left
  rfl

/-- `κ` is a number of the gadget. -/
lemma of_κ : GadgetNumber μin k N (κT μin) := by
  unfold GadgetNumber
  iterate 9 right
  left
  rfl

/-- `p` is a number of the gadget. -/
lemma of_p : GadgetNumber μin k N (gp μin k N) := by
  unfold GadgetNumber
  iterate 6 right
  left
  rfl

/-- `q` is a number of the gadget. -/
lemma of_q : GadgetNumber μin k N (gq μin k) := by
  unfold GadgetNumber
  iterate 7 right
  left
  rfl

/-- `α_Γ = δN` is a number of the gadget. -/
lemma of_αΓ : GadgetNumber μin k N (gαΓ μin N) := by
  unfold GadgetNumber
  iterate 4 right
  left
  rfl

/-- The rewards are numbers of the gadget. -/
lemma of_m (e : Gr (k - 1) ⊕ Unit) : GadgetNumber μin k N (gadgetM μin k e) := by
  unfold GadgetNumber
  iterate 10 right
  left
  exact ⟨e, rfl⟩

/-- The curvatures are numbers of the gadget. -/
lemma of_β (e : Gr (k - 1) ⊕ Unit) : GadgetNumber μin k N (gadgetB μin k N e) := by
  unfold GadgetNumber
  iterate 11 right
  left
  exact ⟨e, rfl⟩

/-- The capacities of the gadget's form are numbers of the gadget. -/
lemma of_cap {a} (ha : a ∈ (gadgetForm μin k N).D) :
    GadgetNumber μin k N ((gadgetForm μin k N).cap a) := by
  unfold GadgetNumber
  iterate 14 right
  left
  exact ⟨a, ha, rfl⟩

/-- The weights of the gadget's form are numbers of the gadget. -/
lemma of_ω (e : Gr (k - 1) ⊕ Unit) : GadgetNumber μin k N ((gadgetForm μin k N).ω e) := by
  unfold GadgetNumber
  iterate 15 right
  exact ⟨e, rfl⟩

end GadgetNumber

namespace SubsetSum

variable (R : SubsetSum)

/-- The common bound `Bg = 300(k + ⌊log₂ μ_k⌋ + ⌊log₂ μ'_k⌋ + ⌊log₂(N_0 + T)⌋ + 1)` for the bits of
the numbers of the two gadgets `I_1 = I(μ, N_0)` and `I_2 = I(μ', N_0 + T)` (`gadget_sizes`). -/
def Bg : ℕ :=
  300 * (R.k + Nat.log 2 (R.μ (R.k - 1)) + Nat.log 2 (R.μ' (R.k - 1)) + Nat.log 2 R.N₂ + 1)

lemma one_le_Bg : 1 ≤ R.Bg := by unfold Bg; omega

/-- The numbers of `I_1` have at most `Bg` bits ("the algorithm of `thm:gadget` computes `N_0` and
both combs in polynomial time", `gadget_sizes`). -/
lemma gadget1_bits (x : ℝ) (hx : GadgetNumber R.μ R.k R.N₀ x) : Bits R.Bg x := by
  have hN : gNmin R.μ R.k ≤ R.N₀ := le_max_left _ _
  refine (gadget_sizes (inF_μ R).1 hN x hx).mono ?_
  have : Nat.log 2 R.N₀ ≤ Nat.log 2 R.N₂ := Nat.log_mono_right (N₀_le R).2.1
  unfold Bg
  omega

/-- The numbers of `I_2` have at most `Bg` bits (`gadget_sizes`). -/
lemma gadget2_bits (x : ℝ) (hx : GadgetNumber R.μ' R.k R.N₂ x) : Bits R.Bg x := by
  have hN : gNmin R.μ' R.k ≤ R.N₂ := (le_max_right _ _).trans (Nat.le_add_right _ _)
  refine (gadget_sizes (inF_μ R).2 hN x hx).mono ?_
  unfold Bg
  omega

/-- The numbers of the steps (3) and (4) that do not involve `σ`, `δ_1`, `N_0`, `δ_2/δ_1`, `p`, `q`,
`κ*`, `c` and `ℓ`, have at most `81Bg` bits: each is obtained from the numbers of the gadgets, `N_0`
and `∑_i μ_i` by at most four arithmetic operations (`Bits.add3`, `Bits.mul3`, `Bits.div`; the
proof of NP-hardness in `thm:nphard`: "the steps (3) to (5) take `O(k)` arithmetic
operations"; not in the paper, as `out_bits`: the paper bounds no bit length here). -/
lemma steps_bits :
    Bits (81 * R.Bg) R.δ₁ ∧ Bits (81 * R.Bg) (R.N₀ : ℝ) ∧ Bits (81 * R.Bg) (R.δ₂ / R.δ₁) ∧
    Bits (81 * R.Bg) R.p ∧ Bits (81 * R.Bg) R.q ∧ Bits (81 * R.Bg) R.κStar ∧
    Bits (81 * R.Bg) R.c ∧ Bits (81 * R.Bg) R.ℓ := by
  have hB := one_le_Bg R
  obtain ⟨hF₁, -⟩ := inF_μ R
  have two_pow : ∀ a b : ℕ, a ≤ b → (2 : ℝ) ^ a ≤ 2 ^ b := fun a b h =>
    pow_le_pow_right₀ (by norm_num) h
  -- the numbers of the gadgets
  have hδ₁ : Bits R.Bg R.δ₁ := gadget1_bits R _ GadgetNumber.of_δ
  have hδ₂ : Bits R.Bg R.δ₂ := gadget2_bits R _ GadgetNumber.of_δ
  have hκ₁ : Bits R.Bg R.κ₁ := gadget1_bits R _ GadgetNumber.of_κ
  have hκ₂ : Bits R.Bg R.κ₂ := gadget2_bits R _ GadgetNumber.of_κ
  have hp₁ : Bits R.Bg R.p₁ := gadget1_bits R _ GadgetNumber.of_p
  have hp₂ : Bits R.Bg R.p₂ := gadget2_bits R _ GadgetNumber.of_p
  have hq₁ : Bits R.Bg R.q₁ := gadget1_bits R _ GadgetNumber.of_q
  have hq₂ : Bits R.Bg R.q₂ := gadget2_bits R _ GadgetNumber.of_q
  have hδN : Bits R.Bg (R.δ₁ * R.N₀) := gadget1_bits R _ GadgetNumber.of_αΓ
  have hδ0 : R.δ₁ ≠ 0 := (δT_κT_pos (μin0_pos hF₁)).1.ne'
  -- `N_0` and `∑_i μ_i` are natural numbers below `2^{Bg}`
  have hN₀ : Bits R.Bg (R.N₀ : ℝ) := by
    refine Bits.natCast ?_
    have h1 : R.N₀ < 2 ^ (Nat.log 2 R.N₀ + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    have h2 : Nat.log 2 R.N₀ ≤ Nat.log 2 R.N₂ := Nat.log_mono_right (N₀_le R).2.1
    have h3 : (R.N₀ : ℝ) ≤ 2 ^ (Nat.log 2 R.N₀ + 1) := by exact_mod_cast h1.le
    exact h3.trans (two_pow _ _ (by unfold Bg; omega))
  have hsumμ : Bits R.Bg (∑ i ∈ range R.k, (R.μ i : ℝ)) := by
    have hle : ∑ i ∈ range R.k, R.μ i ≤ R.k * R.μ (R.k - 1) := by
      calc ∑ i ∈ range R.k, R.μ i ≤ ∑ _i ∈ range R.k, R.μ (R.k - 1) :=
            sum_le_sum fun i hi => μin_mono hF₁ (by have := mem_range.1 hi; omega)
              (by have := R.one_le_k; omega)
        _ = R.k * R.μ (R.k - 1) := by rw [sum_const, card_range, smul_eq_mul]
    have h1 : R.μ (R.k - 1) < 2 ^ (Nat.log 2 (R.μ (R.k - 1)) + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) _
    have h2 : R.k < 2 ^ R.k := Nat.lt_two_pow_self
    have h3 : R.k * R.μ (R.k - 1) ≤ 2 ^ (R.k + Nat.log 2 (R.μ (R.k - 1)) + 1) := by
      rw [show R.k + Nat.log 2 (R.μ (R.k - 1)) + 1 = R.k + (Nat.log 2 (R.μ (R.k - 1)) + 1) by
        ring, pow_add]
      exact Nat.mul_le_mul h2.le h1.le
    have h4 : ∑ i ∈ range R.k, R.μ i ≤ 2 ^ R.Bg :=
      hle.trans (h3.trans (Nat.pow_le_pow_right (by norm_num) (by unfold Bg; omega)))
    have h5 : ((∑ i ∈ range R.k, R.μ i : ℕ) : ℝ) ≤ 2 ^ R.Bg := by exact_mod_cast h4
    have := Bits.natCast h5
    simpa using this
  have h2 : Bits R.Bg (2 : ℝ) := by
    have h5 : ((2 : ℕ) : ℝ) ≤ 2 ^ R.Bg := by
      push_cast
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ R.Bg := two_pow _ _ hB
    have := Bits.natCast h5
    exact_mod_cast this
  -- `δ_2/δ_1`, `p`, `q`, `κ*`
  have hr : Bits (3 * R.Bg) (R.δ₂ / R.δ₁) := hδ₂.div hδ₁ hδ0
  have hp : Bits (27 * R.Bg) R.p := by
    have h1 : Bits (9 * R.Bg) (R.δ₂ / R.δ₁ * R.p₂) :=
      (hr.mul3 (hp₂.mono (by omega))).mono (by omega)
    exact ((hp₁.mono (by omega : R.Bg ≤ 9 * R.Bg)).add3 h1 (by omega)).mono (by omega)
  have hr2 : Bits (9 * R.Bg) ((R.δ₂ / R.δ₁) ^ 2) := by
    rw [sq]
    exact (hr.mul3 hr).mono (by omega)
  have hq : Bits (81 * R.Bg) R.q := by
    have h1 : Bits (27 * R.Bg) ((R.δ₂ / R.δ₁) ^ 2 * R.q₂) :=
      (hr2.mul3 (hq₂.mono (by omega))).mono (by omega)
    exact ((hq₁.mono (by omega : R.Bg ≤ 27 * R.Bg)).add3 h1 (by omega)).mono (by omega)
  have hκ : Bits (81 * R.Bg) R.κStar := by
    have h1 : Bits (27 * R.Bg) ((R.δ₂ / R.δ₁) ^ 2 * R.κ₂) :=
      (hr2.mul3 (hκ₂.mono (by omega))).mono (by omega)
    exact ((hκ₁.mono (by omega : R.Bg ≤ 27 * R.Bg)).min' h1).mono (by omega)
  -- `c` and `ℓ`
  have hs : Bits (9 * R.Bg) (R.δ₁ * (R.N₀ + ∑ i ∈ range R.k, (R.μ i : ℝ))) :=
    ((hδ₁.mono (by omega)).mul3 (hN₀.add3 hsumμ (by omega))).mono (by omega)
  have hδN9 : Bits (9 * R.Bg) (R.δ₁ * R.N₀) := hδN.mono (by omega)
  have h2' : Bits (27 * R.Bg) (2 : ℝ) := h2.mono (by omega)
  have hc : Bits (81 * R.Bg) R.c := by
    have h1 : Bits (27 * R.Bg) (R.δ₁ * R.N₀ + R.δ₁ * (R.N₀ + ∑ i ∈ range R.k, (R.μ i : ℝ))) :=
      (hδN9.add3 hs (by omega)).mono (by omega)
    exact (h1.div h2' two_ne_zero).mono (by omega)
  have hl : Bits (81 * R.Bg) R.ℓ := by
    have h1 : Bits (27 * R.Bg) (R.δ₁ * (R.N₀ + ∑ i ∈ range R.k, (R.μ i : ℝ)) - R.δ₁ * R.N₀) :=
      (hs.sub3 hδN9 (by omega)).mono (by omega)
    exact (h1.div h2' two_ne_zero).mono (by omega)
  exact ⟨hδ₁.mono (by omega), hN₀.mono (by omega), hr.mono (by omega), hp.mono (by omega), hq,
    hκ, hc, hl⟩

/-! ### `σ` -/

/-- `σ = 2^{−J}` for the least `J` with the conditions of step (4) (`σ_spec'`): the conditions fail
for `2^{−j}`, `j < J`, and hold for `2^{−J}` (not in the paper: the definition of `σ` as "the
largest power of `2`" with the conditions). -/
lemma σ_pow (hT : 0 ≤ R.T) (hTA : R.T ≤ R.sumA) :
    ∃ J : ℕ, R.σ = (1 / 2) ^ J ∧ R.Cond4 ((1 / 2) ^ J) ∧
      ∀ j < J, ¬ R.Cond4 ((1 / 2) ^ j) := by
  classical
  have hex : ∃ j : ℕ, R.Cond4 ((1 / 2) ^ j) := by
    by_contra hne
    have hσ1 : R.σ = 1 := by unfold SubsetSum.σ; exact dite_eq_right hne
    exact hne ⟨0, by rw [pow_zero, ← hσ1]; exact (σ_spec' R hT hTA).1⟩
  unfold SubsetSum.σ
  rw [dite_eq_left hex]
  exact ⟨_, rfl, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩

/-- The smallest right-hand side of step (4) is at least `2^{−6561Bg}`: each right-hand side is a
positive number with at most `6561Bg` bits (not in the paper, which says "`log(1/σ)` is
polynomial"). -/
lemma rhsMin_ge (hT : 0 ≤ R.T) (hTA : R.T ≤ R.sumA) : 1 ≤ 2 ^ (6561 * R.Bg) * R.rhsMin := by
  have hB := one_le_Bg R
  obtain ⟨hδ₁, -, -, hp, hq, hκ, hc, hl⟩ := steps_bits R
  obtain ⟨-, -, hcomb, -, -, hqq, hq₁, hl0, hcl, hδN⟩ := correct_step2 R hT hTA
  have hq0 : 0 < R.q := hq₁.trans_le hqq
  have hκ0 : 0 < R.κStar := hcomb.κ_pos
  have hδ0 : 0 < R.δ₁ := (δT_κT_pos (μin0_pos (inF_μ R).1)).1
  have hcl0 : 0 < R.c + R.ℓ := by linarith
  set B₁ := 81 * R.Bg with hB₁def
  have hB₁ : 1 ≤ B₁ := by omega
  have two_pow : ∀ a b : ℕ, a ≤ b → (2 : ℝ) ^ a ≤ 2 ^ b := fun a b h =>
    pow_le_pow_right₀ (by norm_num) h
  have h1 : Bits B₁ (1 : ℝ) := by
    have h5 : ((1 : ℕ) : ℝ) ≤ 2 ^ B₁ := by push_cast; exact one_le_pow₀ (by norm_num)
    have := Bits.natCast h5
    exact_mod_cast this
  have h4 : Bits B₁ (4 : ℝ) := by
    have h5 : ((4 : ℕ) : ℝ) ≤ 2 ^ B₁ := by
      push_cast
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ B₁ := two_pow _ _ (by omega)
    have := Bits.natCast h5
    exact_mod_cast this
  have h2 : Bits B₁ (2 : ℝ) := by
    have h5 : ((2 : ℕ) : ℝ) ≤ 2 ^ B₁ := by
      push_cast
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ B₁ := two_pow _ _ hB₁
    have := Bits.natCast h5
    exact_mod_cast this
  -- the right-hand sides
  have hA : Bits (27 * B₁) (R.κStar * R.δ₁ / (4 * R.q * R.ℓ ^ 2)) := by
    have e1 : Bits (9 * B₁) (4 * R.q * R.ℓ ^ 2) := by
      rw [sq]
      exact ((h4.mul3 hq).mul3 (hl.mul3 hl)).mono (by omega)
    have e2 : Bits (9 * B₁) (R.κStar * R.δ₁) := (hκ.mul3 hδ₁).mono (by omega)
    exact (e2.div e1 (by positivity)).mono (by omega)
  have hBt : Bits (27 * B₁) (1 / (4 * (R.c + R.ℓ))) := by
    have e1 : Bits (9 * B₁) (4 * (R.c + R.ℓ)) :=
      ((h4.mono (by omega : B₁ ≤ 3 * B₁)).mul3 (hc.add3 hl hB₁)).mono (by omega)
    exact ((h1.mono (by omega)).div e1 (by positivity)).mono (by omega)
  have hCt : 0 < R.p + 2 * R.q * R.c → Bits (81 * B₁) (R.q / (R.p + 2 * R.q * R.c)) := by
    intro hpos
    have e1 : Bits (9 * B₁) (2 * R.q * R.c) :=
      ((h2.mul3 hq).mul3 (hc.mono (by omega))).mono (by omega)
    have e2 : Bits (27 * B₁) (R.p + 2 * R.q * R.c) :=
      ((hp.mono (by omega : B₁ ≤ 9 * B₁)).add3 e1 (by omega)).mono (by omega)
    exact ((hq.mono (by omega)).div e2 hpos.ne').mono (by omega)
  -- each right-hand side `y` has `1 ≤ 2^{6561Bg} y`
  have key : ∀ {B : ℕ} {y : ℝ}, Bits B y → 0 < y → B ≤ 6561 * R.Bg →
      1 ≤ 2 ^ (6561 * R.Bg) * y := fun hy hy0 hBle =>
    (hy.one_le_two_pow_mul hy0).trans
      (mul_le_mul_of_nonneg_right (two_pow _ _ hBle) hy0.le)
  have hmin : ∀ a b : ℝ, 1 ≤ 2 ^ (6561 * R.Bg) * a → 1 ≤ 2 ^ (6561 * R.Bg) * b →
      1 ≤ 2 ^ (6561 * R.Bg) * min a b := fun a b ha hb => by
    rcases min_choice a b with h | h <;> rw [h]
    · exact ha
    · exact hb
  have k1 : 1 ≤ 2 ^ (6561 * R.Bg) * (1 : ℝ) := by
    rw [mul_one]; exact one_le_pow₀ (by norm_num)
  have kA := key hA (by positivity) (by omega)
  have kB := key hBt (by positivity) (by omega)
  unfold SubsetSum.rhsMin
  split_ifs with hpos
  · exact hmin _ _ (hmin _ _ k1 kA) (hmin _ _ kB (key (hCt hpos) (by positivity) (by omega)))
  · exact hmin _ _ (hmin _ _ k1 kA) kB

/-- The proof of NP-hardness in `thm:nphard`: "`σ` is a power of `2` that is at least half the
smallest right-hand side in step (4), so `log(1/σ)` is polynomial and `σ` is found by as many
comparisons": `σ = 2^{−J}`, the conditions of step (4) fail for `2^{−j}`, `j < J`, and hold for
`2^{−J}`, so the search through `σ = 1, 1/2, …` tests them `J + 1` times, and
`J = log₂(1/σ) ≤ 6561Bg + 1`, as `σ ≥ rhsMin/2` (`σ_spec`) and `rhsMin ≥ 2^{−6561Bg}`
(`rhsMin_ge`). -/
theorem σ_search (hT : 0 ≤ R.T) (hTA : R.T ≤ R.sumA) :
    ∃ J : ℕ, R.σ = (1 / 2) ^ J ∧ R.Cond4 ((1 / 2) ^ J) ∧ (∀ j < J, ¬ R.Cond4 ((1 / 2) ^ j)) ∧
      J ≤ 6561 * R.Bg + 1 := by
  obtain ⟨J, hσ, hJ, hmin⟩ := σ_pow R hT hTA
  refine ⟨J, hσ, hJ, hmin, ?_⟩
  obtain ⟨-, -, hcomb, -, -, hqq, hq₁, hl0, hcl, hδN⟩ := correct_step2 R hT hTA
  have hδ0 : 0 < R.δ₁ := (δT_κT_pos (μin0_pos (inF_μ R).1)).1
  obtain ⟨-, -, -, hσr⟩ := σ_spec R (hq₁.trans_le hqq) hl0 hcomb.κ_pos hδ0 (by linarith)
  have hr := rhsMin_ge R hT hTA
  rw [hσ] at hσr
  -- `2^J ≤ 2^{6561Bg + 1}`
  have h1 : (2 : ℝ) ^ J ≤ 2 ^ (6561 * R.Bg + 1) := by
    have e1 : (1 / 2 : ℝ) ^ J * 2 ^ J = 1 := by rw [← mul_pow]; norm_num
    have e2 : (2 : ℝ) ^ (6561 * R.Bg + 1) = 2 ^ (6561 * R.Bg) * 2 := by rw [pow_succ]
    have hpos : (0 : ℝ) < 2 ^ J := by positivity
    have h3 : 1 ≤ 2 ^ (6561 * R.Bg) * (2 * (1 / 2 : ℝ) ^ J) := by
      have : R.rhsMin ≤ 2 * (1 / 2 : ℝ) ^ J := by linarith
      exact hr.trans (mul_le_mul_of_nonneg_left this (by positivity))
    nlinarith
  exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 h1

/-! ### The numbers of the output -/

/-- The numbers of the output `(Î, ϑ)` have at most `2187(81Bg + J)` bits, `σ = 2^{−J}`: `C`, `α_∘`
and `ϑ` (step (4) and (5)), the rewards `m/σ`, `(δ_2/δ_1)m/σ` and `1`, the curvatures (those of the
gadgets and `α_∘/C`), and the capacities and weights of `outForm` (those of the gadgets' forms and
`C`) (not in the paper: each is obtained from the numbers above by at most seven arithmetic
operations, `Bits.add3`, `Bits.mul3`, `Bits.div`). -/
lemma out_bits (hT : 0 ≤ R.T) (hTA : R.T ≤ R.sumA) {J : ℕ} (hσ : R.σ = (1 / 2) ^ J) :
    Bits (2187 * (81 * R.Bg + J)) R.ϑ ∧
    (∀ e, Bits (2187 * (81 * R.Bg + J)) (R.mHat e)) ∧
    (∀ e, Bits (2187 * (81 * R.Bg + J)) (R.βHat e)) ∧
    (∀ a ∈ (outForm R).D, Bits (2187 * (81 * R.Bg + J)) ((outForm R).cap a)) ∧
    ∀ e, Bits (2187 * (81 * R.Bg + J)) ((outForm R).ω e) := by
  have hB := one_le_Bg R
  obtain ⟨hδ₁, hN₀, hr, hp, hq, -, hc, hl⟩ := steps_bits R
  obtain ⟨-, hσ0⟩ := σ_spec' R hT hTA
  obtain ⟨-, -, hC0, -⟩ := correct_step3 R hT hTA
  set B₂ := 81 * R.Bg + J with hB₂
  have hB₂1 : 1 ≤ B₂ := by omega
  have two_pow : ∀ a b : ℕ, a ≤ b → (2 : ℝ) ^ a ≤ 2 ^ b := fun a b h =>
    pow_le_pow_right₀ (by norm_num) h
  have up : ∀ {x : ℝ}, Bits (81 * R.Bg) x → Bits B₂ x := fun h => h.mono (by omega)
  have hσb : Bits B₂ R.σ := by rw [hσ]; exact (Bits.half_pow J).mono (by omega)
  have h1 : Bits B₂ (1 : ℝ) := by
    have h5 : ((1 : ℕ) : ℝ) ≤ 2 ^ B₂ := by push_cast; exact one_le_pow₀ (by norm_num)
    have := Bits.natCast h5
    exact_mod_cast this
  have h2 : Bits B₂ (2 : ℝ) := by
    have h5 : ((2 : ℕ) : ℝ) ≤ 2 ^ B₂ := by
      push_cast
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ B₂ := two_pow _ _ hB₂1
    have := Bits.natCast h5
    exact_mod_cast this
  -- `C = (q(1 − 2σc) − σp)/σ²`
  have hσ2 : Bits (3 * B₂) (R.σ ^ 2) := by rw [sq]; exact hσb.mul3 hσb
  have hC : Bits (729 * B₂) R.C := by
    have e1 : Bits (9 * B₂) (2 * R.σ * R.c) :=
      ((h2.mul3 hσb).mul3 ((up hc).mono (by omega))).mono (by omega)
    have e2 : Bits (27 * B₂) (1 - 2 * R.σ * R.c) :=
      ((h1.mono (by omega)).sub3 e1 (by omega)).mono (by omega)
    have e3 : Bits (81 * B₂) (R.q * (1 - 2 * R.σ * R.c)) :=
      (((up hq).mono (by omega)).mul3 e2).mono (by omega)
    have e4 : Bits (243 * B₂) (R.q * (1 - 2 * R.σ * R.c) - R.σ * R.p) :=
      (e3.sub3 ((hσb.mul3 (up hp)).mono (by omega)) (by omega)).mono (by omega)
    exact (e4.div (hσ2.mono (by omega)) (by positivity)).mono (by omega)
  -- `α_∘ = σδ_1N_0`
  have hαb : Bits (9 * B₂) R.αknob :=
    ((hσb.mul3 (up hδ₁)).mul3 ((up hN₀).mono (by omega))).mono (by omega)
  -- `ϑ = (q/σ²)((1 − σc)² − σ²ℓ²)`
  have hϑ : Bits (243 * B₂) R.ϑ := by
    have e0 : Bits (3 * B₂) (R.σ * R.c) := hσb.mul3 (up hc)
    have e1 : Bits (9 * B₂) (1 - R.σ * R.c) :=
      ((h1.mono (by omega : B₂ ≤ 3 * B₂)).sub3 e0 (by omega)).mono (by omega)
    have e2 : Bits (27 * B₂) ((1 - R.σ * R.c) ^ 2) := by
      rw [sq]
      exact (e1.mul3 e1).mono (by omega)
    have e3 : Bits (27 * B₂) (R.σ ^ 2 * R.ℓ ^ 2) := by
      have : Bits (3 * B₂) (R.ℓ ^ 2) := by rw [sq]; exact (up hl).mul3 (up hl)
      exact (hσ2.mul3 this).mono (by omega)
    have e4 : Bits (81 * B₂) ((1 - R.σ * R.c) ^ 2 - R.σ ^ 2 * R.ℓ ^ 2) :=
      (e2.sub3 e3 (by omega)).mono (by omega)
    have e5 : Bits (81 * B₂) (R.q / R.σ ^ 2) :=
      (((up hq).mono (by omega : B₂ ≤ 3 * B₂)).div hσ2 (by positivity)).mono (by omega)
    exact (e5.mul3 e4).mono (by omega)
  have hBo : ∀ {x : ℝ} {B : ℕ}, Bits B x → B ≤ 2187 * B₂ → Bits (2187 * B₂) x :=
    fun h hle => h.mono hle
  refine ⟨hBo hϑ (by omega), fun e => ?_, fun e => ?_, fun a ha => ?_, fun e => ?_⟩
  · -- the rewards `m/σ`, `(δ_2/δ_1)m/σ` and `1`
    rcases e with (e | e) | u
    · have hm : Bits R.Bg (gadgetM R.μ R.k e) := gadget1_bits R _ (GadgetNumber.of_m e)
      exact hBo ((hm.mono (by omega : R.Bg ≤ B₂)).div hσb hσ0.ne') (by omega)
    · have hm : Bits R.Bg (gadgetM R.μ' R.k e) := gadget2_bits R _ (GadgetNumber.of_m e)
      have e1 : Bits (3 * B₂) (R.δ₂ / R.δ₁ * gadgetM R.μ' R.k e) :=
        (up hr).mul3 (hm.mono (by omega))
      exact hBo (e1.div (hσb.mono (by omega)) hσ0.ne') (by omega)
    · exact hBo h1 (by omega)
  · -- the curvatures: those of the gadgets, and `α_∘/C`
    rcases e with (e | e) | u
    · exact hBo (gadget1_bits R _ (GadgetNumber.of_β e)) (by omega)
    · exact hBo (gadget2_bits R _ (GadgetNumber.of_β e)) (by omega)
    · exact ((hαb.mono (by omega : 9 * B₂ ≤ 729 * B₂)).div hC hC0.ne').mono (by omega)
  · -- the capacities: those of the gadgets' forms
    rcases outForm_cap R ha with ⟨a', ha', h⟩ | ⟨a', ha', h⟩ <;> rw [h]
    · exact hBo (gadget1_bits R _ (GadgetNumber.of_cap ha')) (by omega)
    · exact hBo (gadget2_bits R _ (GadgetNumber.of_cap ha')) (by omega)
  · -- the weights: those of the gadgets' forms, and `C`
    rcases e with (e | e) | u
    · exact hBo (gadget1_bits R _ (GadgetNumber.of_ω e)) (by omega)
    · exact hBo (gadget2_bits R _ (GadgetNumber.of_ω e)) (by omega)
    · exact hBo hC (by omega)

/-- `Bg ≤ 35100⟨(a, T)⟩` for a pair with `0 ≤ T ≤ ∑_i a_i` (from `log_μ_le`, `N₀_le`, `N₂_le`,
`k_le_encLen` and `log_sumA_lt`; not in the paper). -/
lemma Bg_le (hTA : R.T ≤ R.sumA) : R.Bg ≤ 35100 * R.encLen := by
  obtain ⟨h1, h2⟩ := log_μ_le R
  have hN := N₂_le R hTA
  have hL : Nat.log 2 R.N₂ ≤ 2 * (20 * R.k + Nat.log 2 (R.μ (R.k - 1)) +
      Nat.log 2 (R.μ' (R.k - 1)) + 20) + 3 + Nat.log 2 R.sumA + 1 :=
    (Nat.log_mono_right hN).trans (by rw [Nat.log_pow (by norm_num)])
  obtain ⟨hk, hE⟩ := k_le_encLen R
  have hs := log_sumA_lt R
  unfold Bg
  omega

end SubsetSum

/-! ### The reduction runs in polynomial time -/

/-- **The sizes in the proof of NP-hardness in `thm:nphard`**
(`stoc-sections/appD-hardness.tex:1888-1890`): "The reduction of `def:reduction` runs in time
polynomial in the encoding length of `(a, T)`". For every instance `(a, T)` of Subset Sum, the
output `(Î, ϑ)` of `def:reduction` is a rational instance whose data is a cut form (`RatInst`,
`RatInst.IsCutForm`; its real image the output `fHat`, `mHat`, `βHat`) and a rational `ϑ`, with
`⟨Î⟩ + ⟨ϑ⟩ ≤ 2^{58}⟨(a, T)⟩³`; and `σ = 2^{−J}`, found after `J + 1` tests of the conditions of step
(4), with `J ≤ 2^{31}⟨(a, T)⟩`.

The proof's steps: (1) "the algorithm of `thm:gadget` computes `N_0` and both combs in polynomial
time, as its inputs have `log μ_k, log μ'_k = O(k + log(2 + ∑_i a_i))` and the integers `N_0` and
`N_0 + T` have bit lengths bounded in the same way (`lem:sizes`, the proof of `thm:gadget`, and
`T ≤ ∑_i a_i`)" (`μ_last_lt`, `N₀_le`, `N₂_le`, `gadget1_bits`, `gadget2_bits`, `Bg_le`); (2) "Apart
from the choice of `σ`, the steps (3) to (5) take `O(k)` arithmetic operations" (`steps_bits`,
`out_bits`; the operations themselves are not counted); (3) "and `σ` is a power of `2` that is at
least half the smallest right-hand side in step (4), so `log(1/σ)` is polynomial and `σ` is found by
as many comparisons" (`σ_search`); (4) the output is given by its cut form `outForm` (the two
gadgets' forms and a node of weight `C`), its rewards and its curvatures, all of polynomial size, so
its encoding length is polynomial (`exists_ratInst_of_bits`, `card_out`). Step (1) of
`def:reduction` changes the encoding length by at most the factor `7` (`encLen_step1`). -/
theorem reduction_sizes (P : SubsetSum) :
    (∃ I : RatInst (((Gr (P.step1.k - 1) ⊕ Unit) ⊕ (Gr (P.step1.k - 1) ⊕ Unit)) ⊕ Unit),
      I.IsCutForm ∧ (∀ T, I.f T = P.step1.fHat T) ∧ I.mR = P.step1.mHat ∧ I.βR = P.step1.βHat ∧
      ∃ ϑq : ℚ, (ϑq : ℝ) = P.step1.ϑ ∧ I.encI + enc ϑq ≤ 2 ^ 58 * P.encLen ^ 3) ∧
    ∃ J : ℕ, P.step1.σ = (1 / 2) ^ J ∧ P.step1.Cond4 ((1 / 2) ^ J) ∧
      (∀ j < J, ¬ P.step1.Cond4 ((1 / 2) ^ j)) ∧ J ≤ 2 ^ 31 * P.encLen := by
  obtain ⟨hT, hTA, -⟩ := correct_step1 P
  obtain ⟨J, hσ, hJ, hmin, hJle⟩ := P.step1.σ_search hT hTA
  obtain ⟨hϑ, hm, hβ, hcap, hω⟩ := P.step1.out_bits hT hTA hσ
  have hBg := P.step1.Bg_le hTA
  have hE1 := SubsetSum.encLen_step1 P
  have hk := (SubsetSum.k_le_encLen P.step1).1
  have hE2 := (SubsetSum.k_le_encLen P.step1).2
  have hP2 := (SubsetSum.k_le_encLen P).2
  have hBg1 := SubsetSum.one_le_Bg P.step1
  refine ⟨?_, J, hσ, hJ, hmin, ?_⟩
  · obtain ⟨I, hcf, -, hf, hmI, hβI, henc⟩ := exists_ratInst_of_bits
      (SubsetSum.outForm P.step1) P.step1.mHat P.step1.βHat hcap hω hm hβ
    obtain ⟨ϑq, hϑq, hϑenc⟩ := exists_rat_of_bits hϑ
    refine ⟨I, hcf, fun T => by rw [hf, ← SubsetSum.outForm_fn], hmI, hβI, ϑq, hϑq, ?_⟩
    obtain ⟨hcard, hD'⟩ := SubsetSum.card_out P.step1
    rw [hcard] at henc
    -- `Bo = 2187(81Bg + J) ≤ 2^{39}⟨R⟩`, `R` the pair after step (1), and
    -- `⟨Î⟩ + ⟨ϑ⟩ ≤ ((6k + 3)² + 3(6k + 3))(3Bo + 3) + 3Bo + 3 ≤ 109·2^{41}⟨R⟩³ ≤ 2^{58}⟨(a, T)⟩³`
    set E₁ := P.step1.encLen with hE₁
    set E := P.encLen with hE
    set Bo := 2187 * (81 * P.step1.Bg + J) with hBodef
    have hk3 : 6 * P.step1.k + 3 ≤ 9 * E₁ := by omega
    have hEE : E₁ ≤ E₁ * E₁ := Nat.le_mul_self E₁
    have hsum : (SubsetSum.outForm P.step1).D.card + 3 * (6 * P.step1.k + 3) ≤
        108 * (E₁ * E₁) := by
      have h1 : (SubsetSum.outForm P.step1).D.card ≤ 81 * (E₁ * E₁) :=
        hD'.trans ((Nat.mul_le_mul hk3 hk3).trans (le_of_eq (by ring)))
      have h2 : 3 * (6 * P.step1.k + 3) ≤ 27 * (E₁ * E₁) := by
        have : 3 * (6 * P.step1.k + 3) ≤ 27 * E₁ := by omega
        exact this.trans (Nat.mul_le_mul_left 27 hEE)
      calc _ ≤ 81 * (E₁ * E₁) + 27 * (E₁ * E₁) := Nat.add_le_add h1 h2
        _ = 108 * (E₁ * E₁) := by ring
    have h3B : 3 * Bo + 3 ≤ 2199023255552 * E₁ := by omega
    have hI : I.encI ≤ 108 * (E₁ * E₁) * (2199023255552 * E₁) :=
      henc.trans (Nat.mul_le_mul hsum h3B)
    have hE13 : E₁ ≤ E₁ * E₁ * E₁ := by
      have h1 : 1 ≤ E₁ := by omega
      calc E₁ = 1 * 1 * E₁ := by ring
        _ ≤ E₁ * E₁ * E₁ := Nat.mul_le_mul (Nat.mul_le_mul h1 h1) le_rfl
    have hE7 : E₁ * E₁ * E₁ ≤ (7 * E) * (7 * E) * (7 * E) :=
      Nat.mul_le_mul (Nat.mul_le_mul hE1 hE1) hE1
    calc I.encI + enc ϑq ≤ 108 * (E₁ * E₁) * (2199023255552 * E₁) + 2199023255552 * E₁ :=
          Nat.add_le_add hI (hϑenc.trans h3B)
      _ = 108 * 2199023255552 * (E₁ * E₁ * E₁) + 2199023255552 * E₁ := by ring
      _ ≤ 108 * 2199023255552 * (E₁ * E₁ * E₁) + 2199023255552 * (E₁ * E₁ * E₁) :=
          Nat.add_le_add_left (Nat.mul_le_mul_left 2199023255552 hE13) _
      _ = 109 * 2199023255552 * (E₁ * E₁ * E₁) := by ring
      _ ≤ 109 * 2199023255552 * ((7 * E) * (7 * E) * (7 * E)) := Nat.mul_le_mul_left _ hE7
      _ = 109 * 2199023255552 * 343 * E ^ 3 := by ring
      _ ≤ 2 ^ 58 * E ^ 3 := Nat.mul_le_mul_right _ (by norm_num)
  · rw [show (2 : ℕ) ^ 31 = 2147483648 by norm_num]
    omega

end

end Hardness

end Stoc
