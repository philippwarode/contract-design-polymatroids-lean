-- stamp r9 2026-11-02
import Stoc.Hardness.ExactBits
import Stoc.Hardness.ReductionSizes
import Stoc.OptimalShare.BitLength

/-!
# NP-completeness: `thm:nphard`

The STOC version's `thm:nphard` (Section 4, `stoc-sections/07-hardness.tex:8-10`, restated before
its proof) with its proof (Appendix C.8, `sec:D-npcomplete`,
`stoc-sections/appD-hardness.tex:1885-1906`), which first establishes NP-hardness (lines
1887-1892) and next shows membership in NP (lines 1894-1905), and the claim after the proof that
computing an optimal contract is NP-hard under polynomial-time Turing reductions (line 1908), as far
as they are mathematics:

* `nphard_core`: for every instance `(a, T)` of Subset Sum, the output `(Î, ϑ)` of `def:reduction`
  lies in `𝒞_cut`, and for every optimal share `α*` of `Î`, `(a, T)` is a yes-instance if and only
  if `U_P(α*) ≥ ϑ` (`prop:correct`), which holds if and only if some `α ∈ [0, 1]` has
  `U_P(α) ≥ ϑ` (the first step of the proof of membership in NP); a step of the proof of
  `nphard_hardness`, the mathematical core of NP-hardness.
* `nphard_hardness`: NP-hardness in the bit model. The output of `def:reduction` (the statement
  names it: `fHat`, `mHat`, `βHat` and `ϑ`) is an instance of `𝒞_cut` with rational data and a
  rational `ϑ`, of encoding length at most `2^{58}⟨(a, T)⟩³` ("The reduction of
  `def:reduction` runs in time polynomial in the encoding length of `(a, T)`", by
  `reduction_sizes` in `Stoc/Hardness/ReductionSizes.lean`), and it is a yes-instance of the
  problem of `thm:nphard` if and only if `(a, T)` is one of Subset Sum.
* `nphard_np`: membership in NP. A certificate `(α, x)` is checked by `RatInst.Verify` (with the
  test of `lem:exactbr`(b)), and a yes-instance has one of polynomial encoding length, by
  `thm:bitlength` and `lem:exactbr`(a) (`nphard_np_aux`).
* `nphard`: the statement of `thm:nphard`, the conjunction of NP-hardness, `nphard_hardness`, and
  membership in NP, `nphard_np`.
* `nphard_optimal`: the claim after the proof, "Computing an optimal contract is NP-hard under
  polynomial-time Turing reductions". An optimal share `α*`, one exact best response by
  `lem:exactbr`(c) and one comparison decide the problem of `thm:nphard`
  (`RatInst.DecideByShare`).

What is not formalised is the machine model: Turing machines, polynomial time, the classes P and
NP, NP-completeness and polynomial-time Turing reductions as notions, and Subset Sum's
NP-completeness, which the paper cites [GJ79]. The paper's claims of polynomial time are formalised
as sizes, that is encoding lengths, and as counts of comparisons, evaluations of `f` and maximum
flows. The maximum flows are cited (Edmonds and Karp, [GGT89]), and arithmetic operations are not
counted.

Taken over on 2026-10-20 from `Paper/Hardness/Main.lean` (the paper at Overleaf f035b19) for the
STOC version (`stoc.tex`); from then on this copy follows the STOC version.
-/

namespace Stoc

namespace Hardness

open Finset

noncomputable section

/-- **NP-hardness in `thm:nphard`**, its mathematical part (`stoc-sections/07-hardness.tex:8-10`,
proof `stoc-sections/appD-hardness.tex:1887-1892`): for every instance `(a, T)` of Subset Sum, the
output `(Î, ϑ)` of `def:reduction` (the steps (2)-(5) applied to the pair `P.step1` of step (1))
lies in `𝒞_cut`, and for every optimal share `α*` of `Î`, `(a, T)` is a yes-instance if and only if
`U_P(α*) ≥ ϑ`; and `U_P(α*) ≥ ϑ` if and only if some `α ∈ [0, 1]` has `U_P(α) ≥ ϑ`.

The proof's steps: (1) the reduction runs in polynomial time: the algorithm of `thm:gadget`
computes `N_0` and both combs in polynomial time, as its inputs and the integers `N_0` and
`N_0 + T` have short bit lengths, and apart from the choice of `σ` the steps (3) to (5) take `O(k)`
arithmetic operations, while `σ` is a power of `2` at least half the smallest right-hand side of
step (4) (that bound is `σ_spec`; the sizes are `reduction_sizes` and `nphard_hardness`, the
running time is not formalised); (2) the output lies in
`𝒞_cut`, since its rank function is a direct sum of polymatroid rank functions whose cut forms,
together with an isolated node of weight `C` for the centering summand, form a cut form of it
(`lem:cutforms`), and its rewards and curvatures are positive (and rational: `nphard_hardness`);
(3) by `prop:correct`, and as Subset Sum is NP-complete
`[GJ79]`, deciding whether `U_P(α*) ≥ ϑ` is NP-hard on `𝒞_cut` (the equivalence is
`prop:correct`; the complexity statement is not formalised); (4) from the proof of membership in
NP (line 1896): as `U_P(α*) = max_{α∈[0,1]} U_P(α)`, `U_P(α*) ≥ ϑ` if and only if some
`α ∈ [0, 1]` has `U_P(α) ≥ ϑ`. This is a step of the proof of `nphard_hardness`, its mathematical
core; the statement of the theorem is `nphard`. -/
theorem nphard_core (P : SubsetSum) :
    Ccut P.step1.fHat P.step1.mHat P.step1.βHat ∧
    ∀ α ∈ Set.Icc (0 : ℝ) 1,
      IsMaxOn (profit (grossValue P.step1.fHat P.step1.mHat P.step1.βHat)) (Set.Icc 0 1) α →
      (P.Yes ↔ P.step1.ϑ ≤ profit (grossValue P.step1.fHat P.step1.mHat P.step1.βHat) α) ∧
      (P.step1.ϑ ≤ profit (grossValue P.step1.fHat P.step1.mHat P.step1.βHat) α ↔
        ∃ β ∈ Set.Icc (0 : ℝ) 1,
          P.step1.ϑ ≤ profit (grossValue P.step1.fHat P.step1.mHat P.step1.βHat) β) := by
  obtain ⟨hT, hTA, -⟩ := correct_step1 P
  set R := P.step1 with hR
  obtain ⟨hrank, hβ, -, -, -, -, -, -, -, -⟩ := correct_step2 R hT hTA
  obtain ⟨-, hαk, hC, -⟩ := correct_step3 R hT hTA
  obtain ⟨-, hσ⟩ := σ_spec' R hT hTA
  obtain ⟨hF₁, hF₂⟩ := inF_μ R
  have hN₁ : gNmin R.μ R.k ≤ R.N₀ := le_max_left _ _
  have hN₂ : gNmin R.μ' R.k ≤ R.N₂ := (le_max_right _ _).trans (Nat.le_add_right _ _)
  obtain ⟨hc₁, -⟩ := (gadget hF₁).2 R.N₀ hN₁
  obtain ⟨hc₂, -⟩ := (gadget hF₂).2 R.N₂ hN₂
  have hδ₁ : 0 < R.δ₁ := (δT_κT_pos (μin0_pos hF₁)).1
  have hδ₂ : 0 < R.δ₂ := (δT_κT_pos (μin0_pos hF₂)).1
  -- (2) "The output lies in `𝒞_cut`, since its rank function is a direct sum of polymatroid rank
  -- functions whose cut forms, together with an isolated node of weight `C` for the centering
  -- summand, form a cut form of it (`lem:cutforms`), and its rewards and curvatures are positive
  -- rationals."
  refine ⟨⟨fun e => ?_, fun e => ?_, isRankFunction_dsum hrank (isRankFunction_single hC.le),
    (hc₁.cutForm.dsum hc₂.cutForm).knob R.C⟩, fun α hα hopt => ?_⟩
  · rcases e with (e | e) | e
    · exact div_pos (hc₁.m_pos e) hσ
    · exact div_pos (mul_pos (div_pos hδ₂ hδ₁) (hc₂.m_pos e)) hσ
    · show (0 : ℝ) < 1
      norm_num
  · rcases e with e | e
    · exact hβ e
    · exact div_pos hαk hC
  -- (3) "By `prop:correct`, and as Subset Sum is NP-complete [GJ79], deciding whether
  -- `U_P(α*) ≥ ϑ` is NP-hard on `𝒞_cut`." (The equivalence; the complexity is not formalised.)
  obtain ⟨hyes, hno⟩ := correct P hα hopt
  refine ⟨⟨hyes, fun h => ?_⟩, ⟨fun h => ⟨α, hα, h⟩, fun ⟨β, hβ', h⟩ => h.trans (hopt hβ')⟩⟩
  · by_contra hN
    obtain ⟨h1, h2⟩ := hno hN
    linarith


/-- **NP-hardness in `thm:nphard`, in the bit model** (`stoc-sections/07-hardness.tex:8-10`,
proof `stoc-sections/appD-hardness.tex:1887-1892`): for every instance `(a, T)` of Subset Sum, the
reduction of `def:reduction` outputs an instance `Î` of `𝒞_cut` with rational data and a rational
`ϑ` (the rational instance `I` and `ϑ` of the statement are that output: their real images are
`fHat`, `mHat`, `βHat` and `ϑ` of `P.step1`, the instance after step (1)), with
`⟨Î⟩ + ⟨ϑ⟩ ≤ 2^{58}⟨(a, T)⟩³`, and `(a, T)` is a yes-instance if and only if some `α ∈ [0, 1]` has
`U_P(α) ≥ ϑ` for `Î`, that is, `U_P(α*) ≥ ϑ`. With `nphard_np`, deciding whether `U_P(α*) ≥ ϑ` on
`𝒞_cut` is NP-complete (`nphard`), up to the machine model and Subset Sum's NP-completeness [GJ79].

The proof's steps, after "We first establish NP-hardness." (quoted in `nphard`): (1) "The
reduction of `def:reduction` runs in time polynomial in the encoding length of `(a, T)`"
(`reduction_sizes`: the output's numbers and its encoding length, and `σ` found by `J + 1`
comparisons); (2) "The output lies in `𝒞_cut`" (`nphard_core`); (3) "By `prop:correct`, and as
Subset Sum is NP-complete [GJ79], deciding whether `U_P(α*) ≥ ϑ` is NP-hard on `𝒞_cut`"
(`nphard_core`, with an optimal share by `BitLength.exists_optimal_share`). -/
theorem nphard_hardness (P : SubsetSum) :
    ∃ (I : RatInst (((Gr (P.step1.k - 1) ⊕ Unit) ⊕ (Gr (P.step1.k - 1) ⊕ Unit)) ⊕ Unit))
      (ϑ : ℚ), I.f = P.step1.fHat ∧ I.mR = P.step1.mHat ∧ I.βR = P.step1.βHat ∧
      (ϑ : ℝ) = P.step1.ϑ ∧ I.InCcut ∧ I.encI + enc ϑ ≤ 2 ^ 58 * P.encLen ^ 3 ∧
      (P.Yes ↔ ∃ α ∈ Set.Icc (0 : ℝ) 1, (ϑ : ℝ) ≤ profit (grossValue I.f I.mR I.βR) α) := by
  -- (1) "The reduction of `def:reduction` runs in time polynomial in the encoding length of
  -- `(a, T)`."
  -- The Lean: the output's numbers and its encoding length, and `σ` found by `J + 1` comparisons
  -- (`reduction_sizes`); the running time is not formalised.
  obtain ⟨⟨I, hcf, hf, hm, hβ, ϑq, hϑ, henc⟩, -⟩ := reduction_sizes P
  -- (2) "The output lies in `𝒞_cut`, …" (`nphard_core`; its data is a cut form,
  -- `reduction_sizes`)
  obtain ⟨hC, hcorr⟩ := nphard_core P
  have hf' : I.f = P.step1.fHat := funext hf
  have hI : I.InCcut := by
    refine ⟨hcf, ?_⟩
    rw [hf', hm, hβ]
    exact hC
  refine ⟨I, ϑq, hf', hm, hβ, hϑ, hI, henc, ?_⟩
  -- (3) "By `prop:correct`, and as Subset Sum is NP-complete [GJ79], deciding whether
  -- `U_P(α*) ≥ ϑ` is NP-hard on `𝒞_cut`." (`nphard_core` at an optimal share,
  -- `BitLength.exists_optimal_share`; the complexity is not formalised)
  rw [hf', hm, hβ, hϑ]
  obtain ⟨αs, hαs, hopt⟩ := BitLength.exists_optimal_share
    (⟨hC.rank, hC.β_pos, fun e => (hC.m_pos e).le⟩ : Tracing.Hyp _ _ _)
  obtain ⟨h1, h2⟩ := hcorr αs hαs (isMaxOn_iff.2 hopt)
  exact h1.trans h2

/-! ### Membership in NP, in the bit model -/

section BitModel

variable {E : Type*} [Fintype E] [DecidableEq E] (I : RatInst E)

namespace RatInst

/-- The check of a certificate `(α, x)` in the proof of membership in NP
(`stoc-sections/appD-hardness.tex:1897-1898`): "check that `α ∈ [0, 1]`, that `x = x*(α)` by
`lem:exactbr`(b), and that `(1 − α) r(x) ≥ ϑ`, in exact arithmetic". -/
def Verify (ϑ α : ℚ) (x : E → ℚ) : Prop :=
  0 ≤ α ∧ α ≤ 1 ∧ I.TestB α x ∧ ϑ ≤ (1 - α) * ∑ e, I.m e * x e

instance (ϑ α : ℚ) (x : E → ℚ) : Decidable (I.Verify ϑ α x) := by
  unfold Verify
  infer_instance

end RatInst

/-- A real number that is a quotient of two integers of absolute value at most `2^L`, the
denominator nonzero, is a rational of encoding length at most `2L + 3` (not in the paper: the bit
length of `thm:bitlength` as an encoding length). -/
lemma exists_rat_enc_of_ratio {α : ℝ} {p q : ℤ} {L : ℕ} (hq : q ≠ 0) (hα : α = p / q)
    (hp : |p| ≤ 2 ^ L) (hqL : |q| ≤ 2 ^ L) : ∃ a : ℚ, (a : ℝ) = α ∧ enc a ≤ 2 * L + 3 := by
  refine ⟨(p * q.sign : ℤ) / (q.natAbs : ℚ), ?_, ?_⟩
  · rw [hα]
    push_cast
    rw [Nat.cast_natAbs, Int.cast_abs]
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq
    rcases lt_or_gt_of_ne hq with h | h
    · rw [Int.sign_eq_neg_one_of_neg h, abs_of_neg (by exact_mod_cast h)]
      push_cast
      field_simp
    · rw [Int.sign_eq_one_of_pos h, abs_of_pos (by exact_mod_cast h)]
      push_cast
      ring
  · refine (enc_le_of_eq_div (a := p * q.sign) (b := q.natAbs) (Int.natAbs_pos.2 hq) rfl).trans ?_
    have hp' : (p * q.sign).natAbs ≤ 2 ^ L := by
      rw [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hq, mul_one]
      have : ((p.natAbs : ℤ)) ≤ 2 ^ L := by rw [Int.natCast_natAbs]; exact hp
      exact_mod_cast this
    have hq' : q.natAbs ≤ 2 ^ L := by
      have : ((q.natAbs : ℤ)) ≤ 2 ^ L := by rw [Int.natCast_natAbs]; exact hqL
      exact_mod_cast this
    have c1 := (Nat.clog_mono_right 2 (Nat.add_le_add_right hp' 1)).trans
      (clog_two_pow_add_one_le L)
    have c2 := (Nat.clog_mono_right 2 (Nat.add_le_add_right hq' 1)).trans
      (clog_two_pow_add_one_le L)
    omega

/-- A rational of encoding length at most `ν` is a quotient of two integers of absolute value less
than `2^ν` (`IsSmall ν` of `thm:bitlength`; not in the paper: "so it is a quotient of two integers
of absolute value less than `2^{2⟨I⟩}`", the proof of membership in NP, line 1900). -/
lemma isSmall_of_enc {q : ℚ} {ν : ℕ} (h : enc q ≤ ν) : BitLength.IsSmall ν (q : ℝ) := by
  have hpow : (2 : ℝ) ^ enc q ≤ 2 ^ ν := pow_le_pow_right₀ (by norm_num) h
  refine ⟨q.num, q.den, by exact_mod_cast q.den_pos.ne', ?_, ?_, ?_⟩
  · calc |(q.num : ℝ)| = ((q.num.natAbs : ℕ) : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
      _ < 2 ^ enc q := by exact_mod_cast natAbs_num_lt q
      _ ≤ 2 ^ ν := hpow
  · rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
    exact (by exact_mod_cast den_lt q : (q.den : ℝ) < _).trans_le hpow
  · rw [Int.cast_natCast, ← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div,
      Rat.num_div_den]

/-- Steps (2)-(5) of the proof of membership in NP (`stoc-sections/appD-hardness.tex:1899-1905`): "A
yes-instance `I` has a certificate of polynomial encoding length", here
`⟨α*⟩ ≤ 48n⟨I⟩ + 3` and `⟨x*_e(α*)⟩ ≤ 6⟨α*⟩ + 31⟨I⟩`, by `thm:bitlength` with `ν := 2⟨I⟩` and
`lem:exactbr`(a). -/
theorem nphard_np_aux [Nonempty E] (hI : I.InCcut) (ϑ : ℚ)
    (hval : ∀ (α : ℚ) (x : E → ℚ), (fun e => (x e : ℝ)) = bestResponse I.f I.mR I.βR α →
      (((1 - α) * ∑ e, I.m e * x e : ℚ) : ℝ) = profit (grossValue I.f I.mR I.βR) α) :
    (∃ α ∈ Set.Icc (0 : ℝ) 1, (ϑ : ℝ) ≤ profit (grossValue I.f I.mR I.βR) α) →
      ∃ (α : ℚ) (x : E → ℚ), I.Verify ϑ α x ∧
        enc α ≤ 48 * Fintype.card E * I.encI + 3 ∧
        ∀ e, enc (x e) ≤ 6 * enc α + 31 * I.encI := by
  rintro ⟨β0, hβ0, hϑ⟩
  -- (2) "Indeed, by the rules at the start of the proof of `lem:exactbr`, every reward, every
  -- curvature and every value of `f` has encoding length at most `2⟨I⟩`, so it is a quotient of
  -- two integers of absolute value less than `2^{2⟨I⟩}`."
  have hHyp : Tracing.Hyp I.f I.mR I.βR := ⟨hI.2.rank, hI.2.β_pos, fun e => (hI.2.m_pos e).le⟩
  have hm : ∀ e, BitLength.IsSmall (2 * I.encI) (I.mR e) := fun e =>
    isSmall_of_enc (by have := I.enc_m_le e; omega)
  have hβs : ∀ e, BitLength.IsSmall (2 * I.encI) (I.βR e) := fun e =>
    isSmall_of_enc (by have := I.enc_β_le e; omega)
  have hfs : ∀ S, BitLength.IsSmall (2 * I.encI) (I.f S) := fun S => by
    rw [← I.fQ_cast]
    exact isSmall_of_enc (I.enc_fQ_le S)
  -- (3) "Moreover, `n ≤ ⟨I⟩`, as every reward has encoding length at least `1`."
  have hn : Fintype.card E ≤ 2 * I.encI := by have := I.card_le_encI; omega
  -- (4) "So the hypothesis of `thm:bitlength` holds with `ν := 2⟨I⟩`. By `thm:bitlength`, some
  -- optimal contract `α*` is a rational whose numerator and denominator have bit length
  -- `O(n⟨I⟩)`."
  -- (`BitLength.bitlength`: an optimal share `α* = p/q` with `|p|, |q| ≤ 2^{12nν}`)
  obtain ⟨-, hopt, hbig⟩ := BitLength.bitlength hHyp hm hβs hfs hn
  have hpos : 0 < Fintype.card E := Fintype.card_pos
  obtain ⟨αs, hαs, hmax, p, q, hq, hαpq, hp, hqb⟩ := hopt hpos
  obtain ⟨-, hQ'⟩ := hbig hpos
  have hQ'' : ((BitLength.bigQ' (Fintype.card E) (2 * I.encI) : ℕ) : ℤ) ≤
      2 ^ (12 * Fintype.card E * (2 * I.encI)) := by exact_mod_cast hQ'
  obtain ⟨a, ha, hae⟩ := exists_rat_enc_of_ratio hq hαpq (hp.trans hQ'') (hqb.trans hQ'')
  have ha0 : 0 ≤ a := by
    have := hαs.1
    rw [← ha] at this
    exact_mod_cast this
  have ha1 : a ≤ 1 := by
    have := hαs.2
    rw [← ha] at this
    exact_mod_cast this
  -- (5) "… and by `lem:exactbr`(a), each coordinate of `x*(α*)` has encoding length at most
  -- `6⟨α*⟩ + 31⟨I⟩ = O(n⟨I⟩)`."
  obtain ⟨x, hx, hxe⟩ := exactbr_a_enc I hI ha0
  have hxeq : (fun e => (x e : ℝ)) = bestResponse I.f I.mR I.βR a := funext hx
  refine ⟨a, x, ⟨ha0, ha1, ((exactbr_b_enc I hI ha0 x).1).2 hxeq, ?_⟩, ?_, hxe⟩
  · -- (5) "Then `U_P(α*) ≥ ϑ`, …"
    have h1 := hval a x hxeq
    rw [ha] at h1
    have h2 : (ϑ : ℝ) ≤ (((1 - a) * ∑ e, I.m e * x e : ℚ) : ℝ) := by
      rw [h1]
      exact hϑ.trans (hmax β0 hβ0)
    exact_mod_cast h2
  · calc enc a ≤ 2 * (12 * Fintype.card E * (2 * I.encI)) + 3 := hae
      _ = 48 * Fintype.card E * I.encI + 3 := by ring

/-- **Membership in NP in `thm:nphard`** (`stoc-sections/07-hardness.tex:8-10`, proof
`stoc-sections/appD-hardness.tex:1894-1905`), in the bit model: for an instance `I` of `𝒞_cut`
(rational data; `RatInst.inCcut_iff` recognizes the inputs, "The inputs are recognized in polynomial
time by `lem:cutforms`(b)") and a rational `ϑ`,
(1) the check `RatInst.Verify` accepts some certificate `(α, x)` if and only if some `α ∈ [0, 1]`
has `U_P(α) ≥ ϑ`, that is, `U_P(α*) ≥ ϑ`; and
(2) a yes-instance has a certificate `(α*, x*(α*))` of polynomial encoding length:
`⟨α*⟩ ≤ 48n⟨I⟩ + 3` and `⟨x*_e(α*)⟩ ≤ 6⟨α*⟩ + 31⟨I⟩`.
The check uses the test of `lem:exactbr`(b) (`2|E|` comparisons, `|E|` evaluations of `f`, one
maximum flow) and two comparisons and one evaluation of `(1 − α)r(x)` in exact arithmetic.

The proof's steps: (1) "As `U_P(α*) = max_{α∈[0,1]} U_P(α)`, we have `U_P(α*) ≥ ϑ` if and only if
some `α ∈ [0, 1]` has `U_P(α) ≥ ϑ`. A certificate is such a rational share `α` together with the
vector `x = x*(α)`. It is verified in polynomial time" (`exactbr_b_enc`); (2) "every reward, every
curvature and every value of `f` has encoding length at most `2⟨I⟩`, so it is a quotient of two
integers of absolute value less than `2^{2⟨I⟩}`" (`RatInst.enc_fQ_le`, `isSmall_of_enc`); (3)
"Moreover, `n ≤ ⟨I⟩`" (`RatInst.card_le_encI`); (4) "So the hypothesis of `thm:bitlength` holds
with `ν := 2⟨I⟩`. By `thm:bitlength`, some optimal contract `α*` is a rational whose numerator and
denominator have bit length `O(n⟨I⟩)`" (`BitLength.bitlength`, with `|p|, |q| ≤ 2^{12nν}`); (5)
"Then `U_P(α*) ≥ ϑ`, and by `lem:exactbr`(a), each coordinate of `x*(α*)` has encoding length at
most `6⟨α*⟩ + 31⟨I⟩ = O(n⟨I⟩)`" (`exactbr_a_enc`). -/
theorem nphard_np [Nonempty E] (hI : I.InCcut) (ϑ : ℚ) :
    ((∃ (α : ℚ) (x : E → ℚ), I.Verify ϑ α x) ↔
      ∃ α ∈ Set.Icc (0 : ℝ) 1, (ϑ : ℝ) ≤ profit (grossValue I.f I.mR I.βR) α) ∧
    ((∃ α ∈ Set.Icc (0 : ℝ) 1, (ϑ : ℝ) ≤ profit (grossValue I.f I.mR I.βR) α) →
      ∃ (α : ℚ) (x : E → ℚ), I.Verify ϑ α x ∧
        enc α ≤ 48 * Fintype.card E * I.encI + 3 ∧ ∀ e, enc (x e) ≤ 6 * enc α + 31 * I.encI) := by
  -- the value `(1 − α)r(x)` in `ℚ` is `U_P(α)` for `x = x*(α)`
  have hval : ∀ (α : ℚ) (x : E → ℚ), (fun e => (x e : ℝ)) = bestResponse I.f I.mR I.βR α →
      (((1 - α) * ∑ e, I.m e * x e : ℚ) : ℝ) = profit (grossValue I.f I.mR I.βR) α := by
    intro α x hx
    simp only [profit, grossValue, reward, ← hx]
    push_cast
    rfl
  constructor
  · -- (1) "As `U_P(α*) = max_{α∈[0,1]} U_P(α)`, we have `U_P(α*) ≥ ϑ` if and only if some
    -- `α ∈ [0, 1]` has `U_P(α) ≥ ϑ`. A certificate is such a rational share `α` together with the
    -- vector `x = x*(α)`. It is verified in polynomial time: check that `α ∈ [0, 1]`, that
    -- `x = x*(α)` by `lem:exactbr`(b), and that `(1 − α) r(x) ≥ ϑ`, in exact arithmetic."
    -- The Lean: the check `Verify` accepts exactly the yes-instances; the time is not counted.
    constructor
    · rintro ⟨α, x, h0, h1, hT, hϑ⟩
      have hx := ((exactbr_b_enc I hI h0 x).1).1 hT
      refine ⟨α, ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩, ?_⟩
      rw [← hval α x hx]
      exact_mod_cast hϑ
    · intro h
      -- a rational optimal share, by (2)-(4) below
      obtain ⟨α, x, hv, -⟩ := (nphard_np_aux I hI ϑ hval) h
      exact ⟨α, x, hv⟩
  · exact nphard_np_aux I hI ϑ hval

end BitModel

/-- **`thm:nphard`** (Theorem 4.1, `stoc-sections/07-hardness.tex:8-10`): Given an instance of
`𝒞_cut` and `ϑ ∈ ℚ`, it is NP-complete to decide whether `U_P(α*) ≥ ϑ`.

In the bit model, with polynomial time formalised as encoding lengths and counts (the header of this
file), the statement is the conjunction of NP-hardness, `nphard_hardness` (the reduction of
`def:reduction` from Subset Sum outputs an instance of `𝒞_cut` with rational data and a rational
`ϑ`, of encoding length at most `2^{58}⟨(a, T)⟩³`, that is a yes-instance if and only if `(a, T)` is
one), and membership in NP, `nphard_np` (the check `RatInst.Verify` accepts some certificate if and
only if `U_P(α*) ≥ ϑ`, and a yes-instance has a certificate `(α*, x*(α*))` with
`⟨α*⟩ ≤ 48n⟨I⟩ + 3` and `⟨x*_e(α*)⟩ ≤ 6⟨α*⟩ + 31⟨I⟩`). The machine model (Turing machines, P, NP
and NP-completeness as notions) and the NP-completeness of Subset Sum [GJ79] are not formalised.

The proof (`stoc-sections/appD-hardness.tex:1886-1906`) has two parts, (1) "We first establish
NP-hardness." (`nphard_hardness`, with the mathematical core in `nphard_core`) and (2) "We next show
membership in NP." (`nphard_np`); their docstrings give the paper's steps. -/
theorem nphard :
    -- NP-hardness
    (∀ P : SubsetSum,
      ∃ (I : RatInst (((Gr (P.step1.k - 1) ⊕ Unit) ⊕ (Gr (P.step1.k - 1) ⊕ Unit)) ⊕ Unit))
        (ϑ : ℚ), I.f = P.step1.fHat ∧ I.mR = P.step1.mHat ∧ I.βR = P.step1.βHat ∧
        (ϑ : ℝ) = P.step1.ϑ ∧ I.InCcut ∧ I.encI + enc ϑ ≤ 2 ^ 58 * P.encLen ^ 3 ∧
        (P.Yes ↔ ∃ α ∈ Set.Icc (0 : ℝ) 1, (ϑ : ℝ) ≤ profit (grossValue I.f I.mR I.βR) α)) ∧
    -- membership in NP
    ∀ {E : Type*} [Fintype E] [DecidableEq E] (I : RatInst E) [Nonempty E], I.InCcut →
      ∀ ϑ : ℚ,
      ((∃ (α : ℚ) (x : E → ℚ), I.Verify ϑ α x) ↔
        ∃ α ∈ Set.Icc (0 : ℝ) 1, (ϑ : ℝ) ≤ profit (grossValue I.f I.mR I.βR) α) ∧
      ((∃ α ∈ Set.Icc (0 : ℝ) 1, (ϑ : ℝ) ≤ profit (grossValue I.f I.mR I.βR) α) →
        ∃ (α : ℚ) (x : E → ℚ), I.Verify ϑ α x ∧
          enc α ≤ 48 * Fintype.card E * I.encI + 3 ∧
          ∀ e, enc (x e) ≤ 6 * enc α + 31 * I.encI) := by
  -- (1) "We first establish NP-hardness." (`nphard_hardness`)
  refine ⟨nphard_hardness, ?_⟩
  -- (2) "We next show membership in NP." (`nphard_np`)
  exact @nphard_np

/-! ### Computing an optimal contract, in the bit model

The claim after the proof of `thm:nphard` (`stoc-sections/appD-hardness.tex:1908`). -/

section Optimal

variable {E : Type*} [Fintype E] [DecidableEq E] (I : RatInst E)

namespace RatInst

/-- The decision in the claim after the proof of `thm:nphard`
(`stoc-sections/appD-hardness.tex:1908`): from a rational share `α`, compute `x*(α)` by
`lem:exactbr`(c) (`RatInst.exactResponse`) and compare `U_P(α) = (1 − α) r(x*(α))` with `ϑ`. -/
def DecideByShare (ϑ α : ℚ) : Prop :=
  ϑ ≤ (1 - α) * ∑ e, I.m e * I.exactResponse α e

instance (ϑ α : ℚ) : Decidable (I.DecideByShare ϑ α) := by
  unfold DecideByShare
  infer_instance

end RatInst

/-- **Computing an optimal contract is NP-hard**, in the bit model: the claim after the proof of
`thm:nphard` (`stoc-sections/appD-hardness.tex:1908`), "Computing an optimal contract is NP-hard
under polynomial-time Turing reductions". Given an instance `I` of `𝒞_cut`, a rational `ϑ` and a
rational optimal share `α*` (the answer of an algorithm that returns an optimal contract),
`RatInst.DecideByShare` computes `x*(α*)` by `lem:exactbr`(c) and compares
`U_P(α*) = (1 − α*) r(x*(α*))` with `ϑ`; it accepts if and only if `U_P(α*) ≥ ϑ`, the problem of
`thm:nphard`, and it uses at most `(|E| + 1)(3Ω + 1)` maximum flows on numbers of encoding length at
most `5Ω + 3` with `Ω = 2⟨α*⟩ + 14⟨I⟩`, polynomial in `⟨I⟩` and `⟨α*⟩` (`exactbr_c_enc`).

The claim's steps: (1) "a polynomial-time algorithm returning a rational optimal contract `α*`
would also allow us to compute `x*(α*)` and `U_P(α*)` exactly in polynomial time by
`lem:exactbr`(c)" (here `α*` is any rational optimal share, and the bounds are in terms of
`⟨α*⟩`); (2) "Comparing this value with `ϑ` would decide the NP-complete problem of `thm:nphard`"
(with `nphard`; NP-hardness under polynomial-time Turing reductions, a statement about Turing
machines, is not formalised). -/
theorem nphard_optimal [Nonempty E] (hI : I.InCcut) (ϑ αs : ℚ) (hαs : (αs : ℝ) ∈ Set.Icc 0 1)
    (hopt : ∀ α ∈ Set.Icc (0 : ℝ) 1,
      profit (grossValue I.f I.mR I.βR) α ≤ profit (grossValue I.f I.mR I.βR) αs) :
    (I.DecideByShare ϑ αs ↔
      ∃ α ∈ Set.Icc (0 : ℝ) 1, (ϑ : ℝ) ≤ profit (grossValue I.f I.mR I.βR) α) ∧
    (I.search αs).2.length ≤ (Fintype.card E + 1) * (3 * I.Ωα αs + 1) ∧
    ∀ j ∈ (I.search αs).2, enc (j * hstep (I.Ωα αs)) ≤ 5 * I.Ωα αs + 3 := by
  have h0 : 0 ≤ αs := by exact_mod_cast hαs.1
  -- (1) "a polynomial-time algorithm returning a rational optimal contract `α*` would also allow
  -- us to compute `x*(α*)` and `U_P(α*)` exactly in polynomial time by `lem:exactbr`(c)."
  -- (`exactbr_c_enc`, with its maximum flows)
  obtain ⟨hx, hcount, hθ⟩ := exactbr_c_enc I hI h0
  have hval : (((1 - αs) * ∑ e, I.m e * I.exactResponse αs e : ℚ) : ℝ) =
      profit (grossValue I.f I.mR I.βR) αs := by
    simp only [profit, grossValue, reward, ← hx]
    push_cast
    rfl
  refine ⟨?_, hcount, fun j hj => (hθ j hj).1⟩
  -- (2) "Comparing this value with `ϑ` would decide the NP-complete problem of `thm:nphard`."
  constructor
  · intro h
    refine ⟨αs, hαs, ?_⟩
    rw [← hval]
    exact_mod_cast h
  · rintro ⟨α, hα, h⟩
    have h2 : (ϑ : ℝ) ≤ (((1 - αs) * ∑ e, I.m e * I.exactResponse αs e : ℚ) : ℝ) := by
      rw [hval]
      exact h.trans (hopt α hα)
    unfold RatInst.DecideByShare
    exact_mod_cast h2

end Optimal

end

end Hardness

end Stoc
